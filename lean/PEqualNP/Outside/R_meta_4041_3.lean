import PEqualNP.Defs

/- Normalize the gates, trim after the output, and pad smaller circuits with copies.
The two remaining cases have 123 or 124 gates, with last wires 164 and 165.
The normalization adapts the project's Shannon, Support and Elim helpers. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4041_3 :
    (∀ C : Circuit, PEqualNP.TopForm.IsAO2 42 C → C.size = 123 → C.output = 164 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true) → False) →
    (∀ C : Circuit, PEqualNP.TopForm.IsAO2 42 C → C.size = 124 → C.output = 165 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true) →
      ∀ (Y : Finset (Fin 42)), Y.card ≤ 2 →
        (∀ v ∈ Y, v.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List ℕ)) →
        ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
          (C.wires (List.ofFn fun i : Fin 42 => decide (i ∈ Y))).getD (42+j) false = false) →
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) := by
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have length_wiresFrom (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]

  have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
    rw [ht, List.getD_append _ _ _ _ h]

  let Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

  have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  let Ref : Type := Sum Bool ℕ

  let valRef (w : List Bool) (s : Ref) : Bool :=
    Sum.casesOn s id (fun j => w.getD j false)

  let validRef (m : ℕ) (s : Ref) : Prop :=
    Sum.casesOn s (fun _ => True) (fun j => j < m)

  let binary (unit : Bool) (consume : Ref → Ref → Option Gate × Ref)
      (ins : List Ref) : Option Gate × Ref :=
    List.casesOn ins (none, Sum.inl unit) (fun a tail =>
      List.casesOn tail (none, a) (fun b extra =>
        List.casesOn extra (consume a b) (fun _ _ => (none, Sum.inl false))))

  let simpAnd (m : ℕ) (ins : List Ref) : Option Gate × Ref :=
    binary true (fun a b =>
      Sum.casesOn a
        (fun c => Sum.casesOn b
          (fun d => (none, Sum.inl (c && d)))
          (fun j => (none, bif c then Sum.inr j else Sum.inl false)))
        (fun j => Sum.casesOn b
          (fun c => (none, bif c then Sum.inr j else Sum.inl false))
          (fun k => (some ⟨.and,[j,k]⟩, Sum.inr m)))) ins

  let simpOr (m : ℕ) (ins : List Ref) : Option Gate × Ref :=
    binary false (fun a b =>
      Sum.casesOn a
        (fun c => Sum.casesOn b
          (fun d => (none, Sum.inl (c || d)))
          (fun j => (none, bif c then Sum.inl true else Sum.inr j)))
        (fun j => Sum.casesOn b
          (fun c => (none, bif c then Sum.inl true else Sum.inr j))
          (fun k => (some ⟨.or,[j,k]⟩, Sum.inr m)))) ins

  let simplify (op : GateOp) (m : ℕ) (ins : List Ref) : Option Gate × Ref :=
    GateOp.casesOn op (simpAnd m ins) (simpOr m ins) (none, Sum.inl false)
      (fun _ => (none, Sum.inl false)) (none, Sum.inl false)

  have evalAnd (ins : List Bool) : GateOp.and.eval ins = ins.all id := rfl
  have evalOr (ins : List Bool) : GateOp.or.eval ins = ins.any id := rfl
  have size_eq (C : Circuit) : C.size = C.gates.length := rfl

  have simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (w : List Bool) (ins : List Ref) (hlen : ins.length ≤ 2)
      (hv : ∀ s ∈ ins, validRef w.length s) :
      validRef (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      valRef (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (valRef w)) := by
    rcases hop with rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpAnd, binary, validRef, valRef, evalAnd]
      · cases a <;> simp_all [simplify, simpAnd, binary, validRef, valRef, wiresFrom]
      · rcases a with c | j <;> rcases b with d | k
        · cases c <;> cases d <;> simp_all [simplify, simpAnd, binary, validRef, valRef, wiresFrom]
        · cases c <;> simp_all [simplify, simpAnd, binary, validRef, valRef, wiresFrom]
        · cases d <;> simp_all [simplify, simpAnd, binary, validRef, valRef, wiresFrom]
        · simp_all [simplify, simpAnd, binary, validRef, valRef, wiresFrom]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [simplify, simpOr, binary, validRef, valRef, evalOr]
      · cases a <;> simp_all [simplify, simpOr, binary, validRef, valRef, wiresFrom]
      · rcases a with c | j <;> rcases b with d | k
        · cases c <;> cases d <;> simp_all [simplify, simpOr, binary, validRef, valRef, wiresFrom]
        · cases c <;> simp_all [simplify, simpOr, binary, validRef, valRef, wiresFrom]
        · cases d <;> simp_all [simplify, simpOr, binary, validRef, valRef, wiresFrom]
        · simp_all [simplify, simpOr, binary, validRef, valRef, wiresFrom]
      · simp at hlen

  let elimStep (n : ℕ) (acc : List Ref × List Gate) (g : Gate) : List Ref × List Gate :=
    let result := simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    (acc.1 ++ [result.2], acc.2 ++ result.1.toList)

  let elim (n : ℕ) (gs : List Gate) (acc : List Ref × List Gate) : List Ref × List Gate :=
    gs.foldl (elimStep n) acc

  have toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
    cases o <;> simp

  have elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Ref × List Gate,
      (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
    induction gs with
    | nil => intro acc; simp [elim]
    | cons g gs ih =>
      intro acc
      have h1 := ih (elimStep n acc g)
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
      rw [h3, List.length_cons]; omega

  have validMonotone {m m' : ℕ} (h : m ≤ m') (s : Ref) (hs : validRef m s) : validRef m' s := by
    cases s
    · trivial
    · exact lt_of_lt_of_le hs h

  have valueAppend (w t : List Bool) (s : Ref) (hs : validRef w.length s) :
      valRef (w ++ t) s = valRef w s := by
    cases s
    · rfl
    · exact List.getD_append _ _ _ _ hs

  let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Ref × List Gate) : Prop :=
    acc.1.length = w.length ∧ ∀ i : ℕ,
      validRef (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      valRef (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

  have inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
      ∀ (w : List Bool) (acc : List Ref × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
        Inv n y (wiresFrom gs w) (elim n gs acc) := by
    induction gs with
    | nil => intro w acc _ h; exact h
    | cons g gs ih =>
      intro w acc hok h
      apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨hl, hi⟩ := h
      set w' := wiresFrom acc.2 y with hw'
      have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          rw [lw']; exact (hi a).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hvals : ins.map (valRef w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro a _
        exact (hi a).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [wiresFrom_append]
      obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      show validRef (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
        valRef (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨validMonotone (by omega) _ (hi i).1, ?_⟩
        rw [ht, valueAppend _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2

  let initial (n : ℕ) : List Ref × List Gate :=
    (List.ofFn fun i : Fin n => Sum.inr i.val, [])

  have initialInv (n : ℕ) (y : Fin n → Bool) :
      Inv n (List.ofFn y) (List.ofFn y) (initial n) := by
    refine ⟨by simp [initial], ?_⟩
    intro i
    by_cases hi : i < n <;> simp [initial, hi, validRef, valRef, wiresFrom]

  let Proper (m : ℕ) (g : Gate) :=
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a < m ∧ b < m

  let Ordered (n : ℕ) (gs : List Gate) :=
    ∀ j g, gs[j]? = some g → Proper (n+j) g

  have orderedAO (C : Circuit) (n : ℕ) (legal : Ordered n C.gates) :
      PEqualNP.TopForm.IsAO2 n C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g mem
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp mem
      exact (legal j g hj).1
    · intro j hj i hi
      have found : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have eq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        delta PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, found]
      obtain ⟨a,b,hab,ha,hb⟩ := (legal j C.gates[j] found).2
      rw [eq,hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g mem
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp mem
      obtain ⟨a,b,l,_,_⟩ := (legal j g hj).2
      simp [l]

  have emitted (gop : GateOp) (hop : gop = .and ∨ gop = .or)
      (m : ℕ) (ins : List Ref) (g : Gate) (yes : (simplify gop m ins).1 = some g) :
      ∃ a b, ins = [Sum.inr a,Sum.inr b] ∧ g = ⟨gop,[a,b]⟩ := by
    rcases hop with rfl | rfl <;>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp only [simplify,simpAnd,simpOr,binary,Option.some.injEq,reduceCtorEq] at yes
    all_goals exact ⟨_, _, rfl, yes.symm⟩

  have orderedAppend (n : ℕ) (gs : List Gate) (g : Gate)
      (old : Ordered n gs) (new : Proper (n+gs.length) g) :
      Ordered n (gs ++ [g]) := by
    intro j h hj
    by_cases small : j < gs.length
    · exact old j h (by simpa only [List.getElem?_append_left small] using hj)
    · rw [List.getElem?_append_right (by omega : gs.length ≤ j)] at hj
      have hit : j-gs.length < ([g] : List Gate).length := by
        by_contra! no
        rw [List.getElem?_eq_none no] at hj
        contradiction
      have eq : j=gs.length := by simp at hit; omega
      subst j
      have same : g = h := by simpa using hj
      subst h
      exact new

  have preservesOrdered (n : ℕ) (y w : List Bool) (hy : y.length=n)
      (gs : List Gate) (s : List Ref × List Gate)
      (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      (inv : Inv n y w s) (ordered : Ordered n s.2) :
      Ordered n (elim n gs s).2 := by
    induction gs generalizing w s with
    | nil => exact ordered
    | cons g gs ih =>
      apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n s g)
        (fun g hg => legal g (List.mem_cons_of_mem _ hg))
      · exact inv_elim n y hy [g] w s
          (fun h mem => by
            have hg : h=g := List.mem_singleton.mp mem
            subst h
            exact legal g List.mem_cons_self) inv
      · let ins := g.inputs.map fun i => s.1.getD i (Sum.inl false)
        cases result : (simplify g.op (n+s.2.length) ins).1 with
        | none =>
          change Ordered n (s.2 ++ (simplify g.op (n+s.2.length) ins).1.toList)
          rw [result]
          simpa using ordered
        | some h =>
          obtain ⟨a,b,inputs,e⟩ := emitted g.op (legal g List.mem_cons_self).1 _ ins h result
          have bounds (r : ℕ) (member : Sum.inr r ∈ ins) : r<n+s.2.length := by
            obtain ⟨i,_,h⟩ := List.mem_map.mp member
            have v := (inv.2 i).1
            rw [h] at v
            exact v
          have good : Proper (n+s.2.length) h := by
            subst h
            exact ⟨(legal g List.mem_cons_self).1,a,b,rfl,bounds a (by simp [inputs]),bounds b (by simp [inputs])⟩
          have both := orderedAppend n s.2 h ordered good
          change Ordered n (s.2 ++ (simplify g.op (n+s.2.length) ins).1.toList)
          rw [result]
          simpa using both

  have badSkips (n : ℕ) (s : List Ref × List Gate) (gs : List Gate) (j : ℕ) (g : Gate)
      (tag : g.op = .and ∨ g.op = .or) (inList : gs[j]? = some g)
      (bad : ¬ Proper (s.1.length+j) g) : (elim n gs s).2.length+1 ≤ s.2.length+gs.length := by
    induction gs generalizing s j with
    | nil => simp at inList
    | cons h gs ih =>
      change (elim n gs (elimStep n s h)).2.length+1 ≤ s.2.length+(gs.length+1)
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at inList
        subst h
        let ins := g.inputs.map fun i => s.1.getD i (Sum.inl false)
        have none : (simplify g.op (n+s.2.length) ins).1 = none := by
          by_contra! no
          obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp no
          obtain ⟨l,r,us,_⟩ := emitted _ tag _ ins a ha
          have len : g.inputs.length = 2 := by
            have e := congrArg List.length us
            simpa [ins] using e
          obtain ⟨p,q,insEq⟩ := List.length_eq_two.mp len
          have bounded (i : ℕ) (hi : i ∈ g.inputs) : i<s.1.length := by
            by_contra! no
            have hc : Sum.inl false ∈ ins := List.mem_map.mpr
              ⟨i,hi,List.getD_eq_default _ _ no⟩
            simp [us] at hc
          exact bad ⟨tag,p,q,insEq,by simpa using bounded p (by simp [insEq]),
            by simpa using bounded q (by simp [insEq])⟩
        have paid := elim_len n gs (elimStep n s g)
        have same : (elimStep n s g).2.length = s.2.length := by
          change (s.2 ++ (simplify g.op (n+s.2.length) ins).1.toList).length = _
          rw [none]
          simp
        rw [same] at paid
        omega
      | succ j =>
        have prior : gs[j]? = some g := by simpa only [List.getElem?_cons_succ] using inList
        have newBad : ¬ Proper ((elimStep n s h).1.length+j) g := by
          simpa [elimStep,Nat.add_assoc,Nat.add_comm 1] using bad
        have mult := ih (elimStep n s h) j prior newBad
        have size : (elimStep n s h).2.length ≤ s.2.length+1 := by
          simp only [elimStep,List.length_append]
          have bound := toList_length_le (simplify h.op (n+s.2.length)
            (h.inputs.map fun i => s.1.getD i (Sum.inl false))).1
          omega
        omega

  have normalize (n : ℕ) (C : Circuit) (legal : Monotone2 C)
      (nonconstant : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
        (¬ PEqualNP.TopForm.IsAO2 n C → D.size+1 ≤ C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    let s := elim n C.gates (initial n)
    have mono (g : Gate) (mem : g ∈ C.gates) :
        (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
      exact legal g mem
    have simulates (x : Fin n → Bool) :
        valRef (wiresFrom s.2 (List.ofFn x)) (s.1.getD C.output (Sum.inl false))
          = C.eval (List.ofFn x) :=
      ((inv_elim n (List.ofFn x) (by simp) C.gates _ _
        mono (initialInv n x)).2 C.output).2
    cases out : s.1.getD C.output (Sum.inl false) with
    | inl b =>
      obtain ⟨x,y,ne⟩ := nonconstant
      have hx := simulates x
      have hy := simulates y
      rw [out] at hx hy
      exact False.elim (ne (hx.symm.trans hy))
    | inr o =>
      let D : Circuit := ⟨s.2,o⟩
      have ordered := preservesOrdered n (List.ofFn fun _ : Fin n => false)
        (List.ofFn fun _ : Fin n => false) (by simp) C.gates (initial n)
        mono (initialInv n _) (by simp [Ordered,initial])
      have small : D.size ≤ C.size := by simpa [D,size_eq,s,initial] using elim_len n C.gates (initial n)
      refine ⟨D,orderedAO D n ordered,small,?_,?_⟩
      · intro notAO
        have notOrdered : ¬ Ordered n C.gates := fun h => notAO (orderedAO C n h)
        unfold Ordered at notOrdered
        obtain ⟨j,hj⟩ := not_forall.mp notOrdered
        obtain ⟨g,hg⟩ := not_forall.mp hj
        obtain ⟨jg,fail⟩ := not_imp.mp hg
        have member := List.mem_iff_getElem?.mpr ⟨j,jg⟩
        have bad : ¬ Proper ((initial n).1.length+j) g := by simpa [initial] using fail
        simpa [D,size_eq,s,initial] using badSkips n (initial n) C.gates j g (mono g member).1 jg bad
      · intro x
        have h := simulates x
        rw [out] at h
        exact h

  have orderedOfAO (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
      Ordered n C.gates := by
    intro j g hj
    have ind := List.getElem?_eq_some_iff.mp hj
    have jm : j < C.gates.length := ind.1
    have inCircuit : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j,hj⟩
    have atGate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      delta PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD,hj]
    obtain ⟨a,b,wires⟩ := List.length_eq_two.mp (hAO.2.2 g inCircuit)
    refine ⟨hAO.1 g inCircuit,a,b,wires,?_,?_⟩
    · apply hAO.2.1 j jm
      simp [atGate,wires]
    · apply hAO.2.1 j jm
      simp [atGate,wires]

  let target (x : Fin 42 → Bool) : Prop :=
    ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧
      (v.val+21-u.val)%21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true

  let zeroes : Fin 42 → Bool := fun _ => false
  let edgeInput : Fin 42 → Bool := fun i => decide (i.val = 0 ∨ i.val = 21)

  have posTarget : target edgeInput := by
    refine ⟨0,21,?_,?_,?_⟩ <;> decide

  have nonconstant (C : Circuit)
      (eq : ∀ x, C.eval (List.ofFn x) = true ↔ target x) :
      ∃ x y : Fin 42 → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    refine ⟨edgeInput,zeroes,?_⟩
    rw [(eq edgeInput).mpr posTarget]
    intro h
    obtain ⟨_,_,_,bad,_⟩ := (eq zeroes).mp h.symm
    simp [zeroes] at bad

  have outputBounds (C : Circuit)
      (eq : ∀ x, C.eval (List.ofFn x) = true ↔ target x) :
      42 ≤ C.output ∧ C.output < 42+C.size := by
    constructor
    · by_contra! small
      let x : Fin 42 → Bool := fun i => decide (i.val=C.output)
      have wsize : C.output < (List.ofFn x).length := by simpa using small
      have evaluate : C.eval (List.ofFn x) = true := by
        change (wiresFrom C.gates (List.ofFn x)).getD C.output false = true
        rw [getD_wiresFrom C.gates _ _ wsize]
        rw [List.getD_eq_getElem _ _ wsize, List.getElem_ofFn]
        simp only [x, decide_true]
      obtain ⟨u,v,⟨low,high,_⟩,hu,hv⟩ := (eq x).mp evaluate
      simp [x] at hu hv
      omega
    · by_contra! past
      have evaluate : C.eval (List.ofFn edgeInput) = false := by
        change (wiresFrom C.gates (List.ofFn edgeInput)).getD C.output false = false
        apply List.getD_eq_default
        rw [length_wiresFrom,List.length_ofFn]
        exact past
      rw [(eq edgeInput).mpr posTarget] at evaluate
      contradiction

  have trim (C : Circuit) (legal : Ordered 42 C.gates)
      (lo : 42 ≤ C.output) (hi : C.output < 42+C.size) :
      ∃ D : Circuit, Ordered 42 D.gates ∧ D.output=C.output ∧
        D.size=C.output-42+1 ∧ ∀ x : Fin 42 → Bool, D.eval (List.ofFn x)=C.eval (List.ofFn x) := by
    let k := C.output-42+1
    let D : Circuit := ⟨C.gates.take k,C.output⟩
    have fit : k ≤ C.gates.length := by
      change C.output < 42 + C.gates.length at hi
      dsimp [k]
      omega
    have len : D.size = k := by
      simp [D,size_eq,Nat.min_eq_left fit]
    have valid : Ordered 42 D.gates := by
      intro j g hj
      have js : j < (C.gates.take k).length := by
        by_contra! past
        change (C.gates.take k)[j]? = some g at hj
        rw [List.getElem?_eq_none past] at hj
        contradiction
      have jk : j < k := by simpa [List.length_take,Nat.min_eq_left fit] using js
      apply legal j g
      simpa [D,List.getElem?_take,jk] using hj
    refine ⟨D,valid,rfl,len,?_⟩
    intro x
    change (wiresFrom (C.gates.take k) (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    have same : C.gates.take k ++ C.gates.drop k = C.gates := List.take_append_drop _ _
    have split : wiresFrom C.gates (List.ofFn x) =
        wiresFrom (C.gates.drop k) (wiresFrom (C.gates.take k) (List.ofFn x)) := by
      calc
        _ = wiresFrom (C.gates.take k ++ C.gates.drop k) (List.ofFn x) :=
          congrArg (fun gs => wiresFrom gs (List.ofFn x)) same.symm
        _ = _ := wiresFrom_append _ _ _
    have index : C.output < (wiresFrom (C.gates.take k) (List.ofFn x)).length := by
      rw [length_wiresFrom,List.length_ofFn,List.length_take,Nat.min_eq_left fit]
      dsimp [k]
      omega
    calc
      _ = (wiresFrom (C.gates.drop k) (wiresFrom (C.gates.take k) (List.ofFn x))).getD
          C.output false := (getD_wiresFrom (C.gates.drop k) _ _ index).symm
      _ = _ := congrArg (fun w : List Bool => w.getD C.output false) split.symm

  have appendCopy (C : Circuit) (ordered : Ordered 42 C.gates) (ending : C.output+1=42+C.size) :
      ∃ D : Circuit, Ordered 42 D.gates ∧ D.size=C.size+1 ∧ D.output+1=42+D.size ∧
        ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    let g : Gate := ⟨.or,[C.output,C.output]⟩
    let D : Circuit := ⟨C.gates ++ [g],42+C.size⟩
    refine ⟨D, orderedAppend 42 C.gates g ordered ⟨Or.inr rfl,C.output,C.output,rfl,?_,?_⟩,
      ?_,?_,?_⟩
    · change C.output < 42+C.size
      omega
    · change C.output < 42+C.size
      omega
    · simp [D,size_eq]
    · simp [D,size_eq,Nat.add_assoc]
    · intro x
      change (wiresFrom (C.gates ++ [g]) (List.ofFn x)).getD (42+C.size) false =
        (wiresFrom C.gates (List.ofFn x)).getD C.output false
      rw [wiresFrom_append]
      let w := wiresFrom C.gates (List.ofFn x)
      have len : w.length=42+C.size := by simp [w,length_wiresFrom,size_eq]
      rw [← len]
      change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD w.length false = _
      rw [getD_snoc_eq]
      change (w.getD C.output false || (w.getD C.output false || false)) = w.getD C.output false
      cases w.getD C.output false <;> rfl

  have pad (k : ℕ) : ∀ C : Circuit, Ordered 42 C.gates → C.output+1=42+C.size →
      ∃ D : Circuit, Ordered 42 D.gates ∧ D.size=C.size+k ∧ D.output+1=42+D.size ∧
        ∀ x : Fin 42 → Bool, D.eval (List.ofFn x)=C.eval (List.ofFn x) := by
    induction k with
    | zero =>
      intro C hq ho
      exact ⟨C,hq,by simp,ho,fun _=>rfl⟩
    | succ k ih =>
      intro C hq ho
      obtain ⟨D,hd,sz,last,same⟩ := appendCopy C hq ho
      obtain ⟨E,he,szE,lastE,sameE⟩ := ih D hd last
      exact ⟨E,he,by omega,lastE,fun x => (sameE x).trans (same x)⟩

  intro hShort hTight
  have shortFalse (C : Circuit) (hq : Ordered 42 C.gates) (sz : C.size≤123)
      (eq : ∀ x, C.eval (List.ofFn x)=true ↔ target x) : False := by
    obtain ⟨lower,upper⟩ := outputBounds C eq
    obtain ⟨D,hd,hout,hsize,same⟩ := trim C hq lower upper
    have small : D.size≤123 := by omega
    have last : D.output+1=42+D.size := by omega
    obtain ⟨E,he,hse,hlast,trans⟩ := pad (123-D.size) D hd last
    exact hShort E (orderedAO E 42 he) (by omega) (by omega) (fun x => by rw [trans x,same x]; exact eq x)

  intro C Y hMono hBound hCard hY hFire
  by_contra failed
  have spec : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x)=true ↔ target x := by
    intro x
    by_contra no
    exact failed ⟨x,no⟩
  by_cases hAO : PEqualNP.TopForm.IsAO2 42 C
  · have q := orderedOfAO 42 C hAO
    by_cases full : C.size=124
    · by_cases last : C.output=165
      · obtain ⟨j,g,hj,tag,fire⟩ := hFire
        have absent := hTight C hAO full last spec Y hCard hY j g hj tag
        rw [fire] at absent
        contradiction
      · obtain ⟨lo,hi⟩ := outputBounds C spec
        obtain ⟨D,hd,_,sz,ev⟩ := trim C q lo hi
        exact shortFalse D hd (by omega) (fun x => by rw [ev x]; exact spec x)
    · exact shortFalse C q (by omega) spec
  · obtain ⟨D,hd,_,smaller,ev⟩ := normalize 42 C hMono (nonconstant C spec)
    have size := smaller hAO
    exact shortFalse D (orderedOfAO 42 D hd) (by omega) (fun x => by rw [ev x]; exact spec x)
