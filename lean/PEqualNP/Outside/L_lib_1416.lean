import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1416
namespace M1228

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

abbrev Reach {n m : ℕ} (P N : (Fin n → Bool) → Fin m → Prop) :
    ℕ → (Fin n → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin n → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem no_packing_of_taps {n m r : ℕ} {P N : (Fin n → Bool) → Fin m → Prop}
    {C : Circuit} (tap : Fin m → ℕ) (basis : FanInTwo C) (budget : notCount C ≤ r)
    (fits : ∀ x j,
      let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j) false
      (P x j → w = true) ∧ (N x j → w = false)) :
    ∀ x, ¬ Reach P N (2^r) x := by
  have lower : ∀ k x, Reach P N k x → k ≤ grade C x := by
    intro k
    induction k with
    | zero => intro x _; exact Nat.zero_le _
    | succ k ih =>
      intro x reached
      obtain ⟨u,v,j,history,uv,vx,positive,negative⟩ := reached
      have old := ih u history
      have middle := grade_fall basis uv (tap j) ((fits u j).1 positive) ((fits v j).2 negative)
      have last := (grade_order basis vx).1
      omega
  intro x found
  have high := lower _ x found
  have low := (grade_bound C x).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) budget)
  omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendAnd (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.and, [a,b]⟩

def appendOr (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.or, [a,b]⟩

def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩

def withOutput (C : Circuit) (o : Nat) : Circuit := ⟨C.gates, o⟩

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (valid : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have available : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons,ih _ available]
    exact List.getD_append _ _ _ _ valid

@[local simp] theorem emptyCircuit_size : emptyCircuit.size = 0 := rfl

@[local simp] theorem emptyCircuit_notCount : notCount emptyCircuit = 0 := rfl

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

@[local simp] theorem withOutput_size (C : Circuit) (o : Nat) : (withOutput C o).size = C.size := rfl

@[local simp] theorem withOutput_output (C : Circuit) (o : Nat) : (withOutput C o).output = o := rfl

@[local simp] theorem withOutput_notCount (C : Circuit) (o : Nat) :
    notCount (withOutput C o) = notCount C := rfl

@[local simp] theorem withOutput_fanInTwo (C : Circuit) (o : Nat) :
    FanInTwo (withOutput C o) ↔ FanInTwo C := Iff.rfl

@[local simp] theorem withOutput_readsBack (n : Nat) (C : Circuit) (o : Nat) :
    ReadsBack n (withOutput C o) ↔ ReadsBack n C := Iff.rfl

@[local simp] theorem withOutput_value (C : Circuit) (o : Nat) (x : List Bool) (i : Nat) :
    value (withOutput C o) x i = value C x i := rfl

@[local simp] theorem withOutput_eval (C : Circuit) (o : Nat) (x : List Bool) :
    (withOutput C o).eval x = value C x o := rfl

theorem withOutput_valid {n : Nat} {C : Circuit} {o : Nat} (valid : o < nextWire n C) :
    (withOutput C o).output < n + (withOutput C o).size := valid

@[local simp] theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by
  simp [appendGate,Circuit.size]

@[local simp] theorem appendGate_output (C : Circuit) (g : Gate) :
    (appendGate C g).output = C.output := rfl

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

@[local simp] theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C + (@ite ℕ (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases inv : g.op = .not <;> simp [notCount,appendGate,inv]

@[local simp] theorem nextWire_appendGate (n : Nat) (C : Circuit) (g : Gate) :
    nextWire n (appendGate C g) = nextWire n C + 1 := by
  simp [nextWire,Nat.add_assoc]

theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op,arity⟩

theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

theorem value_input (C : Circuit) (x : List Bool) {i : Nat} (valid : i < x.length) :
    value C x i = x.getD i false := by
  rw [value,wires_eq]
  exact fold_value C.gates x valid

theorem nextWire_le_of_prefix {n : Nat} {C D : Circuit} (extension : C.gates <+: D.gates) :
    nextWire n C ≤ nextWire n D := Nat.add_le_add_left extension.length_le n

theorem value_of_prefix {C D : Circuit} (extension : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (valid : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest,appended⟩ := extension
  simp only [value,wires_eq,← appended,List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact valid

theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate,wires_eq,gateStep,value]

theorem appendGate_old {C : Circuit} {g : Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGate C g) x i = value C x i :=
  value_of_prefix (appendGate_prefix C g) valid

theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value,appendGate_wires,← wires_length]
  simp [List.getD_eq_getElem?_getD]

@[local simp] theorem appendAnd_size (C : Circuit) (a b : Nat) :
    (appendAnd C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendOr_size (C : Circuit) (a b : Nat) :
    (appendOr C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendAnd_notCount (C : Circuit) (a b : Nat) :
    notCount (appendAnd C a b) = notCount C := by simp [appendAnd]

@[local simp] theorem appendOr_notCount (C : Circuit) (a b : Nat) :
    notCount (appendOr C a b) = notCount C := by simp [appendOr]

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendAnd_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendAnd C a b) := appendGate_fanInTwo (g := ⟨.and,[a,b]⟩) basis (by simp) (by simp)

theorem appendOr_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendOr C a b) := appendGate_fanInTwo (g := ⟨.or,[a,b]⟩) basis (by simp) (by simp)

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendAnd_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendAnd C a b) := by
  apply appendGate_readsBack (g := ⟨.and,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendOr_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendOr C a b) := by
  apply appendGate_readsBack (g := ⟨.or,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendAnd_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendAnd C a b) x (nextWire x.length C) = (value C x a && value C x b) := by
  simpa [appendAnd,GateOp.eval] using appendGate_new C ⟨.and,[a,b]⟩ x

theorem appendOr_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendOr C a b) x (nextWire x.length C) = (value C x a || value C x b) := by
  simpa [appendOr,GateOp.eval] using appendGate_new C ⟨.or,[a,b]⟩ x

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x

abbrev Input (n : ℕ) := Fin n → Bool

variable {n m : ℕ} (P N : Input n → Fin m → Prop)

theorem reach_zero (x : Input n) : Reach P N 0 x := trivial

theorem reach_succ (k : ℕ) (x : Input n) : Reach P N (k+1) x ↔
    ∃ u v j, Reach P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem reach_mono (k : ℕ) : Monotone (Reach P N k) := by
  intro x y xy active
  cases k with
  | zero => exact reach_zero P N y
  | succ k =>
    obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
    exact (reach_succ P N k y).mpr ⟨u,v,j,prior,uv,vx.trans xy,pu,nv⟩

theorem reach_pred {k : ℕ} {x : Input n} (active : Reach P N (k+1) x) : Reach P N k x := by
  obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
  exact reach_mono P N k (uv.trans vx) prior

theorem reach_of_le {k l : ℕ} {x : Input n} (bound : k ≤ l) (active : Reach P N l x) :
    Reach P N k x := by
  induction bound with
  | refl => exact active
  | step _ ih => exact ih (reach_pred P N active)

noncomputable def support : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ j, P x j ∨ N x j)

theorem mem_support (x : Input n) : x ∈ support P N ↔ ∃ j, P x j ∨ N x j := by
  classical
  simp [support]

theorem cone_iff (u x : Input n) : u ≤ x ↔ ∀ i, u i = true → x i = true := by
  constructor
  · intro below i active
    exact Bool.le_iff_imp.mp (below i) active
  · intro on i
    exact Bool.le_iff_imp.mpr (on i)

theorem reach_support {k : ℕ} (positive : 0 < k) (x : Input n) : Reach P N k x ↔
    ∃ v ∈ support P N, v ≤ x ∧ Reach P N k v := by
  constructor
  · intro active
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
      refine ⟨v,(mem_support P N v).mpr ⟨j,Or.inr nv⟩,vx,?_⟩
      exact (reach_succ P N k v).mpr ⟨u,v,j,prior,uv,le_rfl,pu,nv⟩
  · rintro ⟨v,_,vx,active⟩
    exact reach_mono P N k vx active

private noncomputable def levels (d : ℕ) (x : Input n) : Finset ℕ := by
  classical
  exact (Finset.range (d+1)).filter (fun k => Reach P N k x)

private theorem mem_levels (d : ℕ) (x : Input n) (k : ℕ) :
    k ∈ levels P N d x ↔ k ≤ d ∧ Reach P N k x := by
  classical
  simp [levels,Nat.lt_succ_iff]

private theorem levels_nonempty (d : ℕ) (x : Input n) : (levels P N d x).Nonempty :=
  ⟨0,(mem_levels P N d x 0).mpr ⟨Nat.zero_le _,reach_zero P N x⟩⟩

noncomputable def rank (d : ℕ) (x : Input n) : ℕ :=
  (levels P N d x).max' (levels_nonempty P N d x)

theorem rank_bound (d : ℕ) (x : Input n) : rank P N d x ≤ d :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).1

theorem rank_reaches (d : ℕ) (x : Input n) : Reach P N (rank P N d x) x :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).2

theorem level_le_rank {d k : ℕ} {x : Input n} (small : k ≤ d) (active : Reach P N k x) :
    k ≤ rank P N d x :=
  Finset.le_max' (levels P N d x) k ((mem_levels P N d x k).mpr ⟨small,active⟩)

theorem rank_mono (d : ℕ) : Monotone (rank P N d) := by
  intro x y xy
  exact level_le_rank P N (rank_bound P N d x) (reach_mono P N _ xy (rank_reaches P N d x))

theorem rank_threshold_iff {d k : ℕ} {x : Input n} (small : k ≤ d) :
    k ≤ rank P N d x ↔ Reach P N k x :=
  ⟨fun below => reach_of_le P N below (rank_reaches P N d x), level_le_rank P N small⟩

theorem rank_grows {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {u v : Input n} {j : Fin m} (uv : u ≤ v) (pu : P u j) (nv : N v j) :
    rank P N d u < rank P N d v := by
  have next : Reach P N (rank P N d u + 1) v :=
    (reach_succ P N _ v).mpr ⟨u,v,j,rank_reaches P N d u,uv,le_rfl,pu,nv⟩
  have room : rank P N d u + 1 ≤ d := by
    by_contra notRoom
    exact bounded v (reach_of_le P N (by omega : d+1 ≤ rank P N d u+1) next)
  exact Nat.lt_of_succ_le (level_le_rank P N room next)

theorem threshold_support (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ v ∈ support P N, v ≤ x ∧ k ≤ rank P N d v := by
  constructor
  · intro high
    have small : k ≤ d := high.trans (rank_bound P N d x)
    obtain ⟨v,mem,vx,active⟩ := (reach_support P N positive x).mp
      ((rank_threshold_iff P N small).mp high)
    exact ⟨v,mem,vx,level_le_rank P N small active⟩
  · rintro ⟨v,_,vx,high⟩
    exact high.trans (rank_mono P N d vx)

noncomputable def rankBucket (d k : ℕ) : Finset (Input n) := by
  classical
  exact (support P N).filter (fun x => rank P N d x = k)

theorem mem_rankBucket (d k : ℕ) (x : Input n) :
    x ∈ rankBucket P N d k ↔ x ∈ support P N ∧ rank P N d x = k := by
  classical
  simp [rankBucket]

theorem rank_bucket_count (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), (rankBucket P N d k).card) = (support P N).card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (s := support P N) (t := Finset.range (d+1))
    (f := rank P N d) (by
      intro x _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (rank_bound P N d x)))).symm

theorem threshold_buckets (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ l, k ≤ l ∧ l ≤ d ∧ ∃ v ∈ rankBucket P N d l, v ≤ x := by
  constructor
  · intro on
    obtain ⟨v,mem,vx,below⟩ := (threshold_support P N d positive x).mp on
    exact ⟨rank P N d v,below,rank_bound P N d v,v,(mem_rankBucket P N d _ _).mpr ⟨mem,rfl⟩,vx⟩
  · rintro ⟨l,kl,_,v,mem,vx⟩
    obtain ⟨supportV,level⟩ := (mem_rankBucket P N d l v).mp mem
    exact (threshold_support P N d positive x).mpr ⟨v,supportV,vx,level.symm ▸ kl⟩

noncomputable def positiveInputs (j : Fin m) : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => P x j)

noncomputable def positivePairs : Finset (Input n × Fin m) := by
  classical
  exact Finset.univ.filter (fun z => P z.1 z.2)

theorem mem_positiveInputs (j : Fin m) (x : Input n) : x ∈ positiveInputs P j ↔ P x j := by
  classical
  simp [positiveInputs]

theorem mem_positivePairs (z : Input n × Fin m) : z ∈ positivePairs P ↔ P z.1 z.2 := by
  classical
  simp [positivePairs]

theorem positive_input_support {j : Fin m} {x : Input n} (positive : x ∈ positiveInputs P j) :
    x ∈ support P N :=
  (mem_support P N x).mpr ⟨j,Or.inl ((mem_positiveInputs P j x).mp positive)⟩

theorem positive_incidence_count :
    (∑ j : Fin m, (positiveInputs P j).card) = (positivePairs P).card := by
  classical
  calc
    _ = ∑ j : Fin m, ((positivePairs P).filter (fun z => z.2 = j)).card := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.card_nbij' (fun x : Input n => (x,j)) Prod.fst
      · intro x present
        exact Finset.mem_filter.mpr ⟨(mem_positivePairs P _).mpr ((mem_positiveInputs P _ _).mp present),rfl⟩
      · intro z present
        obtain ⟨member,eq⟩ := Finset.mem_filter.mp present
        exact (mem_positiveInputs P _ _).mpr (eq ▸ (mem_positivePairs P z).mp member)
      · intro x _
        rfl
      · intro z present
        exact Prod.ext rfl (Finset.mem_filter.mp present).2.symm
    _ = _ := (Finset.card_eq_sum_card_fiberwise (s := positivePairs P) (t := Finset.univ)
      (f := Prod.snd) (by
        intro j _
        exact Finset.mem_univ _)).symm

def guardedCone (d : ℕ) (u x : Input n) : Prop :=
  u ≤ x ∧ ¬ rank P N d u + 1 ≤ rank P N d x

def tapAccepts (d : ℕ) (x : Input n) (j : Fin m) : Prop :=
  ∃ u ∈ positiveInputs P j, guardedCone P N d u x

theorem tap_accepts_positive (d : ℕ) {x : Input n} {j : Fin m} (positive : P x j) :
    tapAccepts P N d x j := by
  refine ⟨x,(mem_positiveInputs P j x).mpr positive,le_rfl,?_⟩
  omega

theorem tap_rejects_negative {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {x : Input n} {j : Fin m} (negative : N x j) : ¬ tapAccepts P N d x j := by
  rintro ⟨u,mem,ux,below⟩
  have grows := rank_grows P N bounded ux ((mem_positiveInputs P j u).mp mem) negative
  exact below (Nat.succ_le_of_lt grows)

namespace Thermometer

abbrev Word (d : ℕ) := Fin d → Bool

def half (d : ℕ) : ℕ := d / 2

def middle (d : ℕ) : ℕ := (d - 1) / 2

theorem half_le (d : ℕ) : half d ≤ d := by
  unfold half
  omega

theorem middle_le_half (d : ℕ) : middle d ≤ half d := by
  unfold middle half
  omega

theorem split_length {d : ℕ} (positive : 0 < d) :
    middle d + 1 + half d = d := by
  unfold middle half
  omega

theorem half_lt_pow {r d : ℕ} (bound : d < 2^(r+1)) : half d < 2^r := by
  rw [Nat.pow_succ] at bound
  unfold half
  omega

def pivot {d : ℕ} (positive : 0 < d) : Fin d :=
  ⟨middle d,by have eq := split_length positive; omega⟩

def lowerSource {d : ℕ} (i : Fin (half d)) : Fin d :=
  ⟨i.val,i.isLt.trans_le (half_le d)⟩

def upperSource {d : ℕ} (positive : 0 < d) (i : Fin (half d)) : Fin d :=
  ⟨middle d + 1 + i.val,by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerSlot {d : ℕ} (i : Fin d) (before : i.val < middle d) : Fin (half d) :=
  ⟨i.val,before.trans_le (middle_le_half d)⟩

def upperSlot {d : ℕ} (positive : 0 < d) (i : Fin d) (after : middle d < i.val) : Fin (half d) :=
  ⟨i.val - (middle d + 1),by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerWord {d : ℕ} (w : Word d) : Word (half d) :=
  fun i => if i.val < middle d then w (lowerSource i) else false

def upperWord {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => w (upperSource positive i)

def folded {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => (!w (pivot positive) && lowerWord w i) || upperWord positive w i

private theorem lower_antitone {d : ℕ} {w : Word d} (ordered : Antitone w) :
    Antitone (lowerWord w) := by
  intro i j compare
  by_cases before : j.val < middle d
  · have earlier : i.val < middle d := lt_of_le_of_lt compare before
    simp only [lowerWord,ite_eq_left before,ite_eq_left earlier]
    exact ordered (show lowerSource i ≤ lowerSource j from compare)
  · simp only [lowerWord,ite_eq_right before]
    exact Bool.false_le _

private theorem upper_antitone {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w) :
    Antitone (upperWord positive w) := by
  intro i j compare
  apply ordered
  change middle d + 1 + i.val ≤ middle d + 1 + j.val
  exact Nat.add_le_add_left compare _

theorem folded_eq_lower {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    (off : w (pivot positive) = false) (i : Fin (half d)) :
    folded positive w i = lowerWord w i := by
  have after : pivot positive ≤ upperSource positive i := by
    change middle d ≤ middle d + 1 + i.val
    omega
  have upperOff : upperWord positive w i = false :=
    Bool.eq_false_of_le_false (by simpa only [off,upperWord] using ordered after)
  simp [folded,off,upperOff]

theorem folded_eq_upper {d : ℕ} (positive : 0 < d) {w : Word d}
    (on : w (pivot positive) = true) (i : Fin (half d)) :
    folded positive w i = upperWord positive w i := by
  simp [folded,on]

theorem folded_antitone {d : ℕ} (positive : 0 < d) {w : Word d}
    (ordered : Antitone w) : Antitone (folded positive w) := by
  cases bit : w (pivot positive)
  · rw [funext (folded_eq_lower positive ordered bit)]
    exact lower_antitone ordered
  · rw [funext (folded_eq_upper positive bit)]
    exact upper_antitone positive ordered

def decoded {d : ℕ} (positive : 0 < d) (notPivot : Bool)
    (notHalf : Word (half d)) (i : Fin d) : Bool :=
  if before : i.val < middle d then notPivot && notHalf (lowerSlot i before)
  else if atPivot : i.val = middle d then notPivot
  else notPivot || notHalf (upperSlot positive i (by omega))

theorem decoded_lower {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (before : i.val < middle d) :
    decoded positive b z i = (b && z (lowerSlot i before)) := by
  simp only [decoded,dite_eq_left before]

theorem decoded_pivot {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (atPivot : i.val = middle d) : decoded positive b z i = b := by
  have notBefore : ¬ i.val < middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_left atPivot]

theorem decoded_upper {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (after : middle d < i.val) :
    decoded positive b z i = (b || z (upperSlot positive i after)) := by
  have notBefore : ¬ i.val < middle d := by omega
  have notPivot : i.val ≠ middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_right notPivot]

private theorem lower_at_slot {d : ℕ} (w : Word d) (i : Fin d)
    (before : i.val < middle d) : lowerWord w (lowerSlot i before) = w i := by
  have same : lowerSource (lowerSlot i before) = i := Fin.ext rfl
  change (if i.val < middle d then w (lowerSource (lowerSlot i before)) else false) = w i
  rw [ite_eq_left before,same]

private theorem upper_at_slot {d : ℕ} (positive : 0 < d) (w : Word d) (i : Fin d)
    (after : middle d < i.val) : upperWord positive w (upperSlot positive i after) = w i := by
  apply congrArg w
  apply Fin.ext
  change middle d + 1 + (i.val - (middle d + 1)) = i.val
  omega

theorem decoded_correct {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    {z : Word (half d)} (tail : ∀ j, z j = !(folded positive w j)) (i : Fin d) :
    decoded positive (!w (pivot positive)) z i = !w i := by
  rcases lt_trichotomy i.val (middle d) with before | atPivot | after
  · rw [decoded_lower positive _ _ _ before]
    cases bit : w (pivot positive)
    · simp [bit,tail,folded_eq_lower positive ordered bit,lower_at_slot w i before]
    · have earlier : i ≤ pivot positive := by
        change i.val ≤ middle d
        omega
      have on : w i = true := Bool.eq_true_of_true_le (by simpa only [bit] using ordered earlier)
      simp [bit,on]
  · have same : pivot positive = i := Fin.ext atPivot.symm
    rw [decoded_pivot positive _ _ _ atPivot,same]
  · rw [decoded_upper positive _ _ _ after]
    cases bit : w (pivot positive)
    · have later : pivot positive ≤ i := by
        change middle d ≤ i.val
        omega
      have off : w i = false := Bool.eq_false_of_le_false (by simpa only [bit] using ordered later)
      simp [bit,off]
    · simp [bit,tail,folded_eq_upper positive bit,upper_at_slot positive w i after]

def inverted : (r d : ℕ) → Word d → Word d
  | 0, _, w => w
  | r+1, d, w =>
    if positive : 0 < d then
      decoded positive (!w (pivot positive)) (inverted r (half d) (folded positive w))
    else w

theorem inverted_correct {r d : ℕ} (bound : d < 2^r) (w : Word d) (ordered : Antitone w) :
    inverted r d w = fun i => !w i := by
  induction r generalizing d with
  | zero =>
    funext i
    have existsIndex := i.isLt
    simp at bound
    omega
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inverted,dite_eq_left positive]
      funext i
      have complement := ih (half_lt_pow bound) (folded positive w)
        (folded_antitone positive ordered)
      exact decoded_correct positive ordered (congrFun complement) i
    · funext i
      have existsIndex := i.isLt
      omega

def stepBinary (d : ℕ) : ℕ := 2 * half d + (d - 1)

theorem step_binary_bound (d : ℕ) : stepBinary d + 4 * half d ≤ 4*d := by
  unfold stepBinary half
  omega

def inversionBinary : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then stepBinary d + inversionBinary r (half d) else 0

def inversionNot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then 1 + inversionNot r (half d) else 0

theorem inversion_binary_bound (r d : ℕ) : inversionBinary r d ≤ 4*d := by
  induction r generalizing d with
  | zero => simp [inversionBinary]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionBinary,ite_eq_left positive]
      exact Nat.le_trans (Nat.add_le_add_left (ih (half d)) _) (step_binary_bound d)
    · simp [inversionBinary,positive]

theorem inversion_not_bound (r d : ℕ) : inversionNot r d ≤ r := by
  induction r generalizing d with
  | zero => simp [inversionNot]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionNot,ite_eq_left positive]
      have count := ih (half d)
      omega
    · simp [inversionNot,positive]

end Thermometer

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendBinary (conjunction : Bool) (C : Circuit) (left right : ℕ) : Circuit :=
  if conjunction then appendAnd C left right else appendOr C left right

def foldBinary (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) :
    List ℕ → Circuit × ℕ
  | [] => (C,base)
  | i :: rest => foldBinary n conjunction (appendBinary conjunction C base i) (nextWire n C) rest

private theorem fold_values (conjunction : Bool) (indices : List ℕ) (a b : ℕ → Bool)
    (same : ∀ i ∈ indices, a i = b i) (base : Bool) :
    indices.foldl (fun acc i => binaryValue conjunction acc (a i)) base =
      indices.foldl (fun acc i => binaryValue conjunction acc (b i)) base := by
  induction indices generalizing base with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons,same i (List.mem_cons_self ..)]
    exact ih (fun j hj => same j (List.mem_cons_of_mem _ hj)) _

theorem foldBinary_spec (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) (basis : FanInTwo C) (reads : ReadsBack n C)
    (baseValid : base < nextWire n C) (valid : ∀ i ∈ indices, i < nextWire n C) :
    let result := foldBinary n conjunction C base indices
    FanInTwo result.1 ∧ ReadsBack n result.1 ∧ result.2 < nextWire n result.1 ∧
      result.1.size = C.size + indices.length ∧ notCount result.1 = notCount C ∧
      ∀ (x : List Bool), x.length = n →
        (∀ i < nextWire n C, value result.1 x i = value C x i) ∧
        value result.1 x result.2 =
          indices.foldl (fun acc i => binaryValue conjunction acc (value C x i)) (value C x base) := by
  induction indices generalizing C base with
  | nil => exact ⟨basis,reads,baseValid,by simp [foldBinary],rfl,fun _ _ => ⟨fun _ _ => rfl,rfl⟩⟩
  | cons i rest ih =>
    let D := appendBinary conjunction C base i
    have iValid := valid i (List.mem_cons_self ..)
    have size : D.size = C.size+1 := by cases conjunction <;> simp [D,appendBinary]
    have nots : notCount D = notCount C := by cases conjunction <;> simp [D,appendBinary]
    have growth : nextWire n D = nextWire n C+1 := by simp [nextWire,size,Nat.add_assoc]
    have forms : FanInTwo D := by
      cases conjunction
      · exact appendOr_fanInTwo basis
      · exact appendAnd_fanInTwo basis
    have previous : ReadsBack n D := by
      cases conjunction
      · exact appendOr_readsBack reads baseValid iValid
      · exact appendAnd_readsBack reads baseValid iValid
    have persist (x : List Bool) (length : x.length = n) (j : ℕ) (earlier : j < nextWire n C) :
        value D x j = value C x j := by
      rw [← length] at earlier
      cases conjunction
      · exact appendGate_old (g := ⟨.or,[base,i]⟩) earlier
      · exact appendGate_old (g := ⟨.and,[base,i]⟩) earlier
    have evaluated (x : List Bool) (length : x.length = n) :
        value D x (nextWire n C) = binaryValue conjunction (value C x base) (value C x i) := by
      rw [← length]
      cases conjunction
      · exact appendOr_new C x base i
      · exact appendAnd_new C x base i
    obtain ⟨hasBasis,hasReads,output,finalSize,finalNot,wires⟩ :=
      ih D (nextWire n C) forms previous (by rw [growth]; omega)
        (fun j hj => (valid j (List.mem_cons_of_mem _ hj)).trans (by rw [growth]; omega))
    refine ⟨hasBasis,hasReads,output,?_,finalNot.trans nots,?_⟩
    · change (foldBinary n conjunction D (nextWire n C) rest).1.size = C.size + (i :: rest).length
      rw [finalSize,size,List.length_cons]
      omega
    · intro x length
      obtain ⟨old,current⟩ := wires x length
      refine ⟨fun j hj => (old j (hj.trans (by rw [growth]; omega))).trans (persist x length j hj),?_⟩
      change value (foldBinary n conjunction D (nextWire n C) rest).1 x
        (foldBinary n conjunction D (nextWire n C) rest).2 =
        (i :: rest).foldl (fun acc j => binaryValue conjunction acc (value C x j)) (value C x base)
      rw [List.foldl_cons,current,evaluated x length]
      exact fold_values conjunction rest (value D x) (value C x)
        (fun j hj => persist x length j (valid j (List.mem_cons_of_mem _ hj))) _

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def withConstants {n : ℕ} (x : Input n) : List Bool := List.ofFn x ++ [false,true]

@[local simp] theorem withConstants_length {n : ℕ} (x : Input n) :
    (withConstants x).length = n+2 := by simp [withConstants]

theorem input_value {n : ℕ} (C : Circuit) (x : Input n) (i : Fin n) :
    value C (withConstants x) i.val = x i := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have inside : i.val < (List.ofFn x).length := by simpa using i.isLt
  simp only [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_left inside]
  simp [List.getElem?_ofFn,i.isLt]

theorem false_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) n = false := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  simp [withConstants,List.getD_eq_getElem?_getD]

theorem true_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) (n+1) = true := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have outside : (List.ofFn x).length ≤ n+1 := by simp
  simp [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_right outside]

def coneIndices {n : ℕ} (u : Input n) : List ℕ :=
  ((List.finRange n).filter u).map (fun i => i.val)

theorem coneIndices_length {n : ℕ} (u : Input n) : (coneIndices u).length ≤ n := by
  simpa [coneIndices] using List.length_filter_le (p := u) (l := List.finRange n)

private theorem fold_and_true (inputs : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    inputs.foldl (fun b i => b && bits i) base = true ↔
      base = true ∧ ∀ i ∈ inputs, bits i = true := by
  induction inputs generalizing base with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons,ih,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp,and_assoc]

def emitCone {n : ℕ} (C : Circuit) (u : Input n) : Circuit × ℕ :=
  foldBinary (n+2) true C (n+1) (coneIndices u)

theorem emitCone_spec {n : ℕ} (C : Circuit) (u : Input n)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCone C u
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ result.2 < nextWire (n+2) result.1 ∧
      C.size ≤ result.1.size ∧ result.1.size ≤ C.size+n ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      ∀ x : Input n, value result.1 (withConstants x) result.2 = true ↔ u ≤ x := by
  have validBase : n+1 < nextWire (n+2) C := by unfold nextWire; omega
  have valid : ∀ i ∈ coneIndices u, i < nextWire (n+2) C := by
    intro i hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    unfold nextWire
    omega
  obtain ⟨newBasis,newReads,output,size,neg,sem⟩ :=
    foldBinary_spec (n+2) true C (n+1) (coneIndices u) basis reads validBase valid
  refine ⟨newBasis,newReads,output,(Nat.le_add_right _ _).trans size.ge,size.le.trans
    (Nat.add_le_add_left (coneIndices_length u) _),neg,?_,?_⟩
  · intro x i hi
    exact (sem (withConstants x) (withConstants_length x)).1 i hi
  · intro x
    have evaluated := (sem (withConstants x) (withConstants_length x)).2
    change value (foldBinary (n+2) true C (n+1) (coneIndices u)).1 (withConstants x)
        (foldBinary (n+2) true C (n+1) (coneIndices u)).2 = true ↔ u ≤ x
    rw [evaluated,true_value]
    simp only [binaryValue,ite_true,fold_and_true,true_and]
    rw [cone_iff]
    constructor
    · intro every i active
      have mem : i.val ∈ coneIndices u := List.mem_map.mpr
        ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,active⟩,rfl⟩
      exact (input_value C x i).symm.trans (every i.val mem)
    · intro above i mem
      obtain ⟨j,selected,rfl⟩ := List.mem_map.mp mem
      exact (input_value C x j).trans (above j (List.mem_filter.mp selected).2)

def emitCones {n : ℕ} (C : Circuit) : List (Input n) → Circuit × List ℕ
  | [] => (C,[])
  | u :: rest =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    (later.1,first.2 :: later.2)

theorem emitCones_spec {n : ℕ} (C : Circuit) (words : List (Input n))
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCones C words
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ C.size ≤ result.1.size ∧
      result.1.size ≤ C.size+n*words.length ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      List.Forall₂ (fun u i => i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u ≤ x) words result.2 := by
  induction words generalizing C with
  | nil => exact ⟨basis,reads,le_rfl,by simp [emitCones],rfl,fun _ _ _ => rfl,.nil⟩
  | cons u rest ih =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    obtain ⟨headBasis,headReads,headWire,growth,headCost,headNot,headOld,headValue⟩ :=
      emitCone_spec C u basis reads
    obtain ⟨tailBasis,tailReads,tailGrowth,tailCost,tailNot,tailOld,tailValues⟩ :=
      ih first.1 headBasis headReads
    have headValid : first.2 < nextWire (n+2) later.1 := by
      exact headWire.trans_le (Nat.add_le_add_left tailGrowth (n+2))
    refine ⟨tailBasis,tailReads,growth.trans tailGrowth,?_,tailNot.trans headNot,?_,?_⟩
    · change later.1.size ≤ C.size + n * (u :: rest).length
      rw [List.length_cons,Nat.mul_succ]
      change later.1.size ≤ first.1.size + n*rest.length at tailCost
      change first.1.size ≤ C.size+n at headCost
      omega
    · intro x i hi
      have through : i < nextWire (n+2) first.1 :=
        hi.trans_le (Nat.add_le_add_left growth (n+2))
      exact (tailOld x i through).trans (headOld x i hi)
    · refine .cons ⟨headValid,?_⟩ tailValues
      intro x
      change value later.1 (withConstants x) first.2 = true ↔ u ≤ x
      rw [tailOld x first.2 headWire]
      exact headValue x

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

@[local simp] theorem appendGates_size (C : Circuit) (gates : List Gate) :
    (appendGates C gates).size = C.size + gates.length := by
  simp [appendGates,Circuit.size]

@[local simp] theorem appendGates_nextWire (n : Nat) (C : Circuit) (gates : List Gate) :
    nextWire n (appendGates C gates) = nextWire n C + gates.length := by
  simp [nextWire,Nat.add_assoc]

@[local simp] theorem appendGates_output (C : Circuit) (gates : List Gate) :
    (appendGates C gates).output = C.output := rfl

theorem appendGates_notCount (C : Circuit) (gates : List Gate) :
    notCount (appendGates C gates) =
      notCount C + (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length := by
  simp [notCount,appendGates]

theorem appendGates_notCount_eq {C : Circuit} {gates : List Gate}
    (noNot : ∀ g ∈ gates, g.op ≠ .not) : notCount (appendGates C gates) = notCount C := by
  have empty : (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.filter_eq_nil_iff.mpr fun g member => by simp [noNot g member]
  simp [appendGates_notCount,empty]

private abbrev GateShape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem appendGates_fanInTwo {C : Circuit} {gates : List Gate} (basis : FanInTwo C)
    (shape : ∀ g ∈ gates, GateShape g) : FanInTwo (appendGates C gates) := by
  intro g member
  rcases List.mem_append.mp member with old | added
  · exact basis g old
  · exact shape g added

theorem appendGates_readsBack {n : Nat} {C : Circuit} {gates : List Gate} (valid : ReadsBack n C)
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGates C gates) := by
  induction gates generalizing C with
  | nil => simpa [appendGates] using valid
  | cons g rest ih =>
    rw [appendGates_cons]
    have fits : ∀ i ∈ g.inputs, i < nextWire n C := reads g (List.mem_cons_self ..)
    apply ih (appendGate_readsBack valid fits)
    intro h member i input
    exact Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
      (nextWire_le_of_prefix (appendGate_prefix C g))

theorem appendGates_old {C : Circuit} {gates : List Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGates C gates) x i = value C x i :=
  value_of_prefix (appendGates_prefix C gates) valid

private def readGate (C : Circuit) (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (value C x))

private theorem appendGates_wires {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) :
    (appendGates C gates).wires x = C.wires x ++ gates.map (readGate C x) := by
  induction gates generalizing C with
  | nil => simp [appendGates]
  | cons g rest ih =>
    have restReads : ∀ h ∈ rest, ∀ i ∈ h.inputs, i < nextWire x.length (appendGate C g) :=
      fun h member i input => Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
        (nextWire_le_of_prefix (appendGate_prefix C g))
    have tail : rest.map (readGate (appendGate C g) x) = rest.map (readGate C x) := by
      apply List.map_congr_left
      intro h member
      unfold readGate
      apply congrArg h.op.eval
      apply List.map_congr_left
      intro i input
      exact appendGate_old (g := g) (reads h (List.mem_cons_of_mem _ member) i input)
    rw [appendGates_cons,ih restReads,tail,appendGate_wires]
    simp [List.append_assoc,readGate]

theorem appendGates_new {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) (j : Fin gates.length) :
    value (appendGates C gates) x (nextWire x.length C + j.val) =
      gates[j].op.eval (gates[j].inputs.map (value C x)) := by
  change ((appendGates C gates).wires x).getD (nextWire x.length C + j.val) false = _
  rw [appendGates_wires (x := x) reads]
  have within : (C.wires x).length ≤ nextWire x.length C + j.val := by rw [wires_length]; omega
  have index : nextWire x.length C + j.val - nextWire x.length C = j.val := by omega
  rw [List.getD_append_right _ _ _ _ within,wires_length,index]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,readGate]

theorem appendFamily_prefix {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    C.gates <+: (appendFamily C gate).gates := appendGates_prefix C _

@[local simp] theorem appendFamily_size {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).size = C.size + k := by simp [appendFamily]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [appendFamily]

@[local simp] theorem appendFamily_output {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).output = C.output := rfl

theorem appendFamily_notCount {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    notCount (appendFamily C gate) = notCount C +
      ((List.ofFn gate).filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length :=
  appendGates_notCount C _

theorem appendFamily_notCount_eq {k : Nat} {C : Circuit} {gate : Fin k → Gate}
    (noNot : ∀ j, (gate j).op ≠ .not) : notCount (appendFamily C gate) = notCount C := by
  apply appendGates_notCount_eq
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact noNot j

theorem appendFamily_fanInTwo {k : Nat} {C : Circuit} {gate : Fin k → Gate} (basis : FanInTwo C)
    (shape : ∀ j, GateShape (gate j)) : FanInTwo (appendFamily C gate) := by
  apply appendGates_fanInTwo basis
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact shape j

theorem appendFamily_readsBack {k n : Nat} {C : Circuit} {gate : Fin k → Gate}
    (valid : ReadsBack n C) (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C) :
    ReadsBack n (appendFamily C gate) := by
  apply appendGates_readsBack valid
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact reads j

theorem appendFamily_old {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendFamily C gate) x i = value C x i :=
  appendGates_old valid

theorem appendFamily_new {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire x.length C) (j : Fin k) :
    value (appendFamily C gate) x (nextWire x.length C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have readsList : ∀ g ∈ List.ofFn gate, ∀ i ∈ g.inputs, i < nextWire x.length C := by
    intro g member
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp member
    exact reads t
  let t : Fin (List.ofFn gate).length := ⟨j.val,by simpa using j.isLt⟩
  simpa [appendFamily,t] using appendGates_new readsList t

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem appendBinary_prefix (conjunction : Bool) (C : Circuit) (a b : ℕ) :
    C.gates <+: (appendBinary conjunction C a b).gates := by
  cases conjunction
  · exact appendGate_prefix C ⟨.or,[a,b]⟩
  · exact appendGate_prefix C ⟨.and,[a,b]⟩

theorem foldBinary_prefix (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) (indices : List ℕ) :
    C.gates <+: (foldBinary n conjunction C base indices).1.gates := by
  induction indices generalizing C base with
  | nil => exact List.prefix_refl _
  | cons i rest ih =>
    exact (appendBinary_prefix conjunction C base i).trans (ih _ _)

theorem foldBinary_size_exact (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) : (foldBinary n conjunction C base indices).1.size = C.size + indices.length := by
  induction indices generalizing C base with
  | nil => simp [foldBinary]
  | cons i rest ih =>
    have step : (appendBinary conjunction C base i).size = C.size + 1 := by
      cases conjunction <;> simp [appendBinary]
    rw [foldBinary,ih,step,List.length_cons]
    omega

theorem emitCone_prefix {n : ℕ} (C : Circuit) (u : Input n) :
    C.gates <+: (emitCone C u).1.gates := foldBinary_prefix _ _ _ _ _

theorem emitCone_size_exact {n : ℕ} (C : Circuit) (u : Input n) :
    (emitCone C u).1.size = C.size + (coneIndices u).length := foldBinary_size_exact _ _ _ _ _

theorem emitCones_prefix {n : ℕ} (C : Circuit) (words : List (Input n)) :
    C.gates <+: (emitCones C words).1.gates := by
  induction words generalizing C with
  | nil => exact List.prefix_refl _
  | cons u rest ih => exact (emitCone_prefix C u).trans (ih (emitCone C u).1)

theorem emitCones_size_exact {n : ℕ} (C : Circuit) (words : List (Input n)) :
    (emitCones C words).1.size = C.size + (words.map (fun u => (coneIndices u).length)).sum := by
  induction words generalizing C with
  | nil => simp [emitCones]
  | cons u rest ih =>
    change (emitCones (emitCone C u).1 rest).1.size = C.size + _
    rw [ih,emitCone_size_exact,List.map_cons,List.sum_cons]
    omega

theorem supportConeTable {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : {u : Input n // u ∈ support P N} → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      ∀ u, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u.val ≤ x := by
  classical
  let words := (support P N).toList
  let result := emitCones C words
  obtain ⟨newBasis,newReads,_,cost,neg,_,paired⟩ := emitCones_spec C words basis reads
  have available (u : {u : Input n // u ∈ support P N}) :
      ∃ i, i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u.val ≤ x := by
    have member : u.val ∈ words := Finset.mem_toList.mpr u.property
    obtain ⟨j,point⟩ := List.mem_iff_get.mp member
    let k : Fin result.2.length := ⟨j.val,by rw [← paired.length_eq]; exact j.isLt⟩
    refine ⟨result.2.get k,?_⟩
    have atIndex := paired.get j.isLt k.isLt
    change result.2.get k < nextWire (n+2) result.1 ∧
      (∀ x : Input n, value result.1 (withConstants x) (result.2.get k) = true ↔ words.get j ≤ x) at atIndex
    simpa only [point] using atIndex
  refine ⟨result.1,fun u => (available u).choose,emitCones_prefix C words,newBasis,newReads,?_,neg,?_⟩
  · simpa only [words,Finset.length_toList] using cost
  · intro u
    exact (available u).choose_spec

theorem supportConeTable_total {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : Input n → ℕ), C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  classical
  obtain ⟨D,w,extension,newBasis,newReads,cost,neg,semantic⟩ := supportConeTable P N C basis reads
  let wire (u : Input n) : ℕ := if h : u ∈ support P N then w ⟨u,h⟩ else n
  refine ⟨D,wire,extension,newBasis,newReads,cost,neg,?_,?_⟩
  · intro u member
    simpa [wire,member] using semantic ⟨u,member⟩
  · intro u absent
    simp [wire,absent]

theorem supportConeTable_empty {n m : ℕ} (P N : Input n → Fin m → Prop) :
    ∃ (D : Circuit) (wire : Input n → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ n*(support P N).card ∧ notCount D = 0 ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  obtain ⟨D,w,_,basis,reads,cost,neg,semantic,defaultWire⟩ :=
    supportConeTable_total P N emptyCircuit emptyCircuit_fanInTwo (emptyCircuit_readsBack (n+2))
  exact ⟨D,w,basis,reads,by simpa using cost,by simpa using neg,semantic,defaultWire⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem fold_or_true (indices : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    indices.foldl (fun b i => b || bits i) base = true ↔
      base = true ∨ ∃ i ∈ indices, bits i = true := by
  induction indices generalizing base with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons,ih,Bool.or_eq_true_iff]
    constructor
    · rintro ((on | on) | ⟨j,mem,on⟩)
      · exact Or.inl on
      · exact Or.inr ⟨i,List.mem_cons_self ..,on⟩
      · exact Or.inr ⟨j,List.mem_cons_of_mem _ mem,on⟩
    · rintro (on | ⟨j,mem,on⟩)
      · exact Or.inl (Or.inl on)
      · rcases List.mem_cons.mp mem with rfl | restMem
        · exact Or.inl (Or.inr on)
        · exact Or.inr ⟨j,restMem,on⟩

theorem append_or_rows {n k : ℕ} (C : Circuit) (rows : Fin k → List ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (rowValid : ∀ i a, a ∈ rows i → a < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size + (∑ i : Fin k, (rows i).length) ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ a ∈ rows i, value C (withConstants x) a = true := by
  induction k generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    let first := foldBinary (n+2) false C n (rows 0)
    have zeroLive : n < nextWire (n+2) C := by unfold nextWire; omega
    obtain ⟨hBasis,hReads,hLive,hSize,hNot,hEval⟩ :=
      foldBinary_spec (n+2) false C n (rows 0) basis reads zeroLive (rowValid 0)
    have firstPrefix : C.gates <+: first.1.gates := by
      unfold first
      apply foldBinary_prefix
    have tailValid (i : Fin k) (a : ℕ) (ha : a ∈ rows i.succ) :
        a < nextWire (n+2) first.1 :=
      (rowValid i.succ a ha).trans_le (nextWire_le_of_prefix firstPrefix)
    obtain ⟨D,tail,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
      ih first.1 (fun i => rows i.succ) hBasis hReads tailValid
    let out : Fin (k+1) → ℕ := Fin.cases first.2 tail
    refine ⟨D,out,dBasis,dReads,firstPrefix.trans dPrefix,dNot.trans hNot,?_,?_,?_⟩
    · rw [dSize,Fin.sum_univ_succ]
      change first.1.size = C.size + (rows 0).length at hSize
      rw [hSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => dLive j) i
      exact hLive.trans_le (nextWire_le_of_prefix dPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) first.2 = true ↔ _
        have live : first.2 < nextWire (withConstants x).length first.1 := by
          simpa only [withConstants_length] using hLive
        rw [value_of_prefix dPrefix live]
        change value (foldBinary (n+2) false C n (rows 0)).1 (withConstants x)
          (foldBinary (n+2) false C n (rows 0)).2 = true ↔ _
        rw [(hEval (withConstants x) (withConstants_length x)).2,false_value]
        simp only [binaryValue,Bool.false_eq_true,ite_false,fold_or_true,false_or]
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [dEval x j]
        constructor <;> rintro ⟨a,mem,on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).symm.trans on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).trans on⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem value_prefix_input {n : ℕ} {C D : Circuit}
    (extension : C.gates <+: D.gates) (x : Input n) {i : ℕ} (live : i < nextWire (n+2) C) :
    value D (withConstants x) i = value C (withConstants x) i :=
  value_of_prefix extension (by simpa only [withConstants_length] using live)

theorem append_suffix_or {n k : ℕ} (C : Circuit) (bucket : Fin k → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) (live : ∀ i, bucket i < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+k ∧ (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ j : Fin k, i ≤ j ∧ value C (withConstants x) (bucket j) = true := by
  induction k generalizing C with
  | zero => exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B,tail,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
      ih C (fun j => bucket j.succ) basis reads (fun j => live j.succ)
    let lower := if reaches : 0 < k then tail ⟨0,reaches⟩ else n
    have lowerLive : lower < nextWire (n+2) B := by
      unfold lower
      split
      · exact bLive _
      · unfold nextWire
        omega
    have lowerEval (x : Input n) : value B (withConstants x) lower = true ↔
        ∃ j : Fin k, value C (withConstants x) (bucket j.succ) = true := by
      unfold lower
      split
      · rename_i positive
        rw [bEval x ⟨0,positive⟩]
        constructor
        · rintro ⟨j,_,on⟩
          exact ⟨j,on⟩
        · rintro ⟨j,on⟩
          exact ⟨j,show (0 : ℕ) ≤ j.val from Nat.zero_le _,on⟩
      · rename_i empty
        rw [false_value]
        constructor
        · intro impossible
          contradiction
        · rintro ⟨j,_⟩
          exact (empty (Nat.zero_lt_of_lt j.isLt)).elim
    let D := appendOr B (bucket 0) lower
    let out : Fin (k+1) → ℕ := Fin.cases (nextWire (n+2) B) tail
    have headLive := (live 0).trans_le (nextWire_le_of_prefix bPrefix)
    have lastPrefix : B.gates <+: D.gates := appendGate_prefix _ _
    have wireGrowth : nextWire (n+2) D = nextWire (n+2) B + 1 := nextWire_appendGate _ _ _
    refine ⟨D,out,appendOr_fanInTwo bBasis,appendOr_readsBack bReads headLive lowerLive,
      bPrefix.trans lastPrefix,(appendOr_notCount _ _ _).trans bNot,?_,?_,?_⟩
    · change (appendOr B (bucket 0) lower).size = C.size + (k+1)
      rw [appendOr_size,bSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change nextWire (n+2) B < nextWire (n+2) D
        omega
      · exact (bLive j).trans_le (nextWire_le_of_prefix lastPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) (nextWire (n+2) B) = true ↔
          ∃ j : Fin (k+1), 0 ≤ j ∧ value C (withConstants x) (bucket j) = true
        have evaluated := appendOr_new B (withConstants x) (bucket 0) lower
        simp only [withConstants_length] at evaluated
        rw [show value D (withConstants x) (nextWire (n+2) B) = _ from evaluated,
          Bool.or_eq_true_iff,value_prefix_input bPrefix x (live 0),lowerEval x]
        constructor
        · rintro (head | ⟨j,tailOn⟩)
          · exact ⟨0,le_rfl,head⟩
          · exact ⟨j.succ,show (0 : ℕ) ≤ j.succ.val from Nat.zero_le _,tailOn⟩
        · rintro ⟨j,_,on⟩
          refine Fin.cases ?_ (fun q => ?_) j on
          · exact Or.inl
          · intro tailOn
            exact Or.inr ⟨q,tailOn⟩
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [value_prefix_input lastPrefix x (bLive j),bEval x j]
        constructor
        · rintro ⟨i,order,on⟩
          exact ⟨i.succ,Fin.succ_le_succ_iff.mpr order,on⟩
        · rintro ⟨i,order,on⟩
          refine Fin.cases ?_ (fun q => ?_) i order on
          · intro incompatible _
            change j.val+1 ≤ 0 at incompatible
            omega
          · intro comparable active
            exact ⟨q,Fin.succ_le_succ_iff.mp comparable,active⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def bucketRows {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) (i : Fin d) : List ℕ :=
  (rankBucket P N d (i.val+1)).toList.map cone

private theorem positive_bucket_cost {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) :
    (∑ i : Fin d, (bucketRows P N d cone i).length) ≤ (support P N).card := by
  have total : (∑ i : Fin (d+1), (rankBucket P N d i.val).card) = (support P N).card :=
    (Fin.sum_univ_eq_sum_range (fun k => (rankBucket P N d k).card) (d+1)).trans (rank_bucket_count P N d)
  rw [Fin.sum_univ_succ] at total
  have bound : (∑ i : Fin d, (rankBucket P N d (i.val+1)).card) ≤ (support P N).card :=
    (Nat.le_add_left _ _).trans total.le
  simpa [bucketRows] using bound

theorem append_thresholds {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ) (C : Circuit)
    (cone : Input n → ℕ) (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneLive : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n,
      value C (withConstants x) (cone u) = true ↔ u ≤ x) :
    ∃ (D : Circuit) (out : Fin d → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+d ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x := by
  let rows := bucketRows P N d cone
  have liveRows (i : Fin d) (a : ℕ) (hm : a ∈ rows i) : a < nextWire (n+2) C := by
    obtain ⟨u,mem,rfl⟩ := List.mem_map.mp hm
    exact coneLive u ((mem_rankBucket P N d (i.val+1) u).mp (Finset.mem_toList.mp mem)).1
  obtain ⟨B,bucket,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
    append_or_rows C rows basis reads liveRows
  have bucketEval (x : Input n) (i : Fin d) :
      value B (withConstants x) (bucket i) = true ↔ ∃ u ∈ rankBucket P N d (i.val+1), u ≤ x := by
    rw [bEval x i]
    constructor
    · rintro ⟨a,found,on⟩
      obtain ⟨u,mem,rfl⟩ := List.mem_map.mp found
      have occurrence := Finset.mem_toList.mp mem
      have original := ((mem_rankBucket P N d (i.val+1) u).mp occurrence).1
      exact ⟨u,occurrence,(coneValue u original x).mp on⟩
    · rintro ⟨u,mem,ux⟩
      have original := ((mem_rankBucket P N d (i.val+1) u).mp mem).1
      exact ⟨cone u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr mem,rfl⟩,
        (coneValue u original x).mpr ux⟩
  obtain ⟨D,out,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
    append_suffix_or B bucket bBasis bReads bLive
  refine ⟨D,out,dBasis,dReads,bPrefix.trans dPrefix,dNot.trans bNot,?_,dLive,?_⟩
  · have budget : (∑ i : Fin d, (rows i).length) ≤ (support P N).card :=
      positive_bucket_cost P N d cone
    rw [dSize,bSize]
    omega
  · intro x i
    rw [dEval x i,threshold_buckets P N d (by omega : 0 < i.val+1) x]
    constructor
    · rintro ⟨j,ij,on⟩
      have below : i.val ≤ j.val := ij
      obtain ⟨u,mem,ux⟩ := (bucketEval x j).mp on
      exact ⟨j.val+1,by omega,by omega,u,mem,ux⟩
    · rintro ⟨k,ik,kd,u,mem,ux⟩
      let j : Fin d := ⟨k-1,by omega⟩
      have level : j.val+1 = k := by dsimp [j]; omega
      refine ⟨j,show i.val ≤ j.val from by omega,(bucketEval x j).mpr ?_⟩
      rw [level]
      exact ⟨u,mem,ux⟩

theorem threshold_antitone {n m d : ℕ} {P N : Input n → Fin m → Prop} {D : Circuit}
    {out : Fin d → ℕ}
    (sem : ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x)
    (x : Input n) : Antitone (fun i => value D (withConstants x) (out i)) := by
  intro i j ij
  change value D (withConstants x) (out j) ≤ value D (withConstants x) (out i)
  have below : i.val ≤ j.val := ij
  cases high : value D (withConstants x) (out j)
  · simp
  · have low : value D (withConstants x) (out i) = true :=
      (sem x i).mpr (by have reach := (sem x j).mp high; omega)
    rw [low]

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)
open Thermometer (half middle pivot lowerSource upperSource lowerSlot upperSlot
  lowerWord upperWord folded folded_antitone decoded decoded_lower decoded_pivot decoded_upper
  decoded_correct half_lt_pow)

private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem pair_reads {n : ℕ} {C : Circuit} {a b : ℕ}
    (la : a < nextWire n C) (lb : b < nextWire n C) :
    ∀ i ∈ [a,b], i < nextWire n C := by
  intro i member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact la
  · exact lb

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j

set_option maxHeartbeats 1700000 in
private theorem fold_taps {X : Type*} (input : X → List Bool) {n d : ℕ}
    (length : ∀ x, (input x).length = n) (positive : 0 < d) {C : Circuit}
    (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C) :
    ∃ (D : Circuit) (pivotWire : ℕ) (wires : Fin (half d) → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D ∧
      pivotWire < nextWire n D ∧ (∀ i, wires i < nextWire n D) ∧
      (∀ x, value D (input x) pivotWire = !value C (input x) (taps (pivot positive))) ∧
      (∀ x i, value D (input x) (wires i) =
        folded positive (fun j => value C (input x) (taps j)) i) ∧
      D.size = C.size + 1 + 2 * half d ∧ notCount D = notCount C + 1 := by
  let C0 := appendNot C (taps (pivot positive))
  let b := nextWire n C
  let low (i : Fin (half d)) := if i.val < middle d then taps (lowerSource i) else falseWire
  let ands (i : Fin (half d)) : Gate := ⟨.and,[b,low i]⟩
  let C1 := appendFamily C0 ands
  let mask (i : Fin (half d)) := nextWire n C0 + i.val
  let ors (i : Fin (half d)) : Gate := ⟨.or,[mask i,taps (upperSource positive i)]⟩
  let C2 := appendFamily C1 ors
  let output (i : Fin (half d)) := nextWire n C1 + i.val
  have e0 : C.gates <+: C0.gates := appendGate_prefix C _
  have e1 : C0.gates <+: C1.gates := appendFamily_prefix C0 ands
  have e2 : C1.gates <+: C2.gates := appendFamily_prefix C1 ors
  have e01 := e0.trans e1
  have e012 := e01.trans e2
  have bLive : b < nextWire n C0 := by
    simp [b,C0,appendNot]
  have lowLive (i : Fin (half d)) : low i < nextWire n C0 := by
    apply Nat.lt_of_lt_of_le _ (nextWire_le_of_prefix e0)
    unfold low
    split
    · exact live _
    · exact falseLive
  have andReads : ∀ j i, i ∈ (ands j).inputs → i < nextWire n C0 :=
    fun j => pair_reads bLive (lowLive j)
  have maskLive (i : Fin (half d)) : mask i < nextWire n C1 := by
    simpa only [mask,C1,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  have orReads : ∀ j i, i ∈ (ors j).inputs → i < nextWire n C1 :=
    fun j => pair_reads (maskLive j) ((live _).trans_le (nextWire_le_of_prefix e01))
  have f0 : FanInTwo C0 := appendNot_fanInTwo fan
  have f1 : FanInTwo C1 := appendFamily_fanInTwo (gate := ands) f0 (by
    intro j
    change GateOp.and ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([b,low j] : List ℕ).length ≤ 2
    simp)
  have f2 : FanInTwo C2 := appendFamily_fanInTwo (gate := ors) f1 (by
    intro j
    change GateOp.or ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([mask j,taps (upperSource positive j)] : List ℕ).length ≤ 2
    simp)
  have r0 : ReadsBack n C0 := appendNot_readsBack back (live (pivot positive))
  have r1 : ReadsBack n C1 := appendFamily_readsBack r0 andReads
  have r2 : ReadsBack n C2 := appendFamily_readsBack r1 orReads
  have atPivot (x : X) : value C0 (input x) b = !value C (input x) (taps (pivot positive)) := by
    simpa only [C0,b,length x] using appendNot_new C (input x) (taps (pivot positive))
  have foldOn (x : X) (i : Fin (half d)) : value C2 (input x) (output i) =
      folded positive (fun j => value C (input x) (taps j)) i := by
    let w : Fin d → Bool := fun j => value C (input x) (taps j)
    have lowOn : value C0 (input x) (low i) = lowerWord w i := by
      by_cases before : i.val < middle d
      · simp only [low,lowerWord,ite_eq_left before]
        exact old_value e0 (length x) (live (lowerSource i))
      · simp only [low,lowerWord,ite_eq_right before]
        exact (old_value e0 (length x) falseLive).trans (falseValue x)
    have maskOn : value C1 (input x) (mask i) = (!w (pivot positive) && lowerWord w i) := by
      have eq := family_value (gate := ands) andReads (input x) (length x) i
      simpa [C1,mask,ands,GateOp.eval,atPivot x,lowOn,w] using eq
    have upperOn : value C1 (input x) (taps (upperSource positive i)) = upperWord positive w i :=
      old_value e01 (length x) (live (upperSource positive i))
    have eq := family_value (gate := ors) orReads (input x) (length x) i
    simpa [C2,output,ors,GateOp.eval,maskOn,upperOn,folded,w] using eq
  refine ⟨C2,b,output,e012,f2,r2,bLive.trans_le (nextWire_le_of_prefix (e1.trans e2)),
    ?_,?_,foldOn,?_,?_⟩
  · intro i
    simpa only [output,C2,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  · intro x
    exact (old_value (e1.trans e2) (length x) bLive).trans (atPivot x)
  · dsimp only [C2,C1,C0]
    simp only [appendFamily_size,appendNot_size]
    omega
  · rw [show C2 = appendFamily C1 ors from rfl,
      appendFamily_notCount_eq (gate := ors) (by intro j; simp [ors]),
      show C1 = appendFamily C0 ands from rfl,
      appendFamily_notCount_eq (gate := ands) (by intro j; simp [ands])]
    simp [C0]

private def decoderGates {d : ℕ} (positive : 0 < d) (b falseWire : ℕ)
    (tail : Fin (half d) → ℕ) (i : Fin d) : Gate :=
  if before : i.val < middle d then ⟨.and,[b,tail (lowerSlot i before)]⟩
  else if eq : i.val = middle d then ⟨.or,[b,falseWire]⟩
  else ⟨.or,[b,tail (upperSlot positive i (by omega))]⟩

private theorem decoder_reads {n d : ℕ} (positive : 0 < d) {C : Circuit} {b f : ℕ}
    {tail : Fin (half d) → ℕ} (liveB : b < nextWire n C) (liveF : f < nextWire n C)
    (liveTail : ∀ j, tail j < nextWire n C) :
    ∀ j i, i ∈ (decoderGates positive b f tail j).inputs → i < nextWire n C := by
  intro j i member
  unfold decoderGates at member
  split at member
  · exact pair_reads liveB (liveTail _) i member
  · split at member
    · exact pair_reads liveB liveF i member
    · exact pair_reads liveB (liveTail _) i member

private theorem decoder_value {d : ℕ} (positive : 0 < d) (C : Circuit) (x : List Bool)
    (b f : ℕ) (tail : Fin (half d) → ℕ) (off : value C x f = false) (i : Fin d) :
    let g := decoderGates positive b f tail i
    g.op.eval (g.inputs.map (value C x)) =
      decoded positive (value C x b) (fun j => value C x (tail j)) i := by
  rcases lt_trichotomy i.val (middle d) with before | eq | after
  · rw [decoded_lower positive _ _ _ before]
    simp [decoderGates,before,GateOp.eval]
  · rw [decoded_pivot positive _ _ _ eq]
    simp [decoderGates,eq,off,GateOp.eval]
  · have lower : ¬ i.val < middle d := by omega
    have other : i.val ≠ middle d := by omega
    rw [decoded_upper positive _ _ _ after]
    simp [decoderGates,lower,other,GateOp.eval]

def InversionResult {X : Type*} (input : X → List Bool) (n r : ℕ)
    (C : Circuit) {d : ℕ} (taps : Fin d → ℕ) :=
  {data : Circuit × (Fin d → ℕ) × ℕ × ℕ //
    let D := data.1
    let output := data.2.1
    let binary := data.2.2.1
    let inversions := data.2.2.2
    (C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D) ∧
    (∀ i, output i < nextWire n D) ∧
    (binary ≤ 4*d ∧ inversions ≤ r) ∧
    (D.size = C.size + binary + inversions ∧ notCount D = notCount C + inversions) ∧
    ∀ x i, value D (input x) (output i) = !value C (input x) (taps i)}

namespace InversionResult

variable {X : Type*} {input : X → List Bool} {n r d : ℕ}
  {C : Circuit} {taps : Fin d → ℕ}

abbrev circuit (R : InversionResult input n r C taps) : Circuit := R.val.1

abbrev wires (R : InversionResult input n r C taps) : Fin d → ℕ := R.val.2.1

abbrev binary (R : InversionResult input n r C taps) : ℕ := R.val.2.2.1

abbrev inversions (R : InversionResult input n r C taps) : ℕ := R.val.2.2.2

theorem extension (R : InversionResult input n r C taps) : C.gates <+: R.circuit.gates :=
  R.property.1.1

theorem fanInTwo (R : InversionResult input n r C taps) : FanInTwo R.circuit :=
  R.property.1.2.1

theorem readsBack (R : InversionResult input n r C taps) : ReadsBack n R.circuit :=
  R.property.1.2.2

theorem valid (R : InversionResult input n r C taps) : ∀ i, R.wires i < nextWire n R.circuit :=
  R.property.2.1

theorem binaryBound (R : InversionResult input n r C taps) : R.binary ≤ 4*d :=
  R.property.2.2.1.1

theorem inversionsBound (R : InversionResult input n r C taps) : R.inversions ≤ r :=
  R.property.2.2.1.2

theorem size_eq (R : InversionResult input n r C taps) :
    R.circuit.size = C.size + R.binary + R.inversions := R.property.2.2.2.1.1

theorem count_eq (R : InversionResult input n r C taps) :
    notCount R.circuit = notCount C + R.inversions := R.property.2.2.2.1.2

theorem computes (R : InversionResult input n r C taps) :
    ∀ x i, value R.circuit (input x) (R.wires i) = !value C (input x) (taps i) :=
  R.property.2.2.2.2

end InversionResult

theorem InversionResult.nonnot_eq {X : Type*} {input : X → List Bool} {n r d : ℕ}
    {C : Circuit} {taps : Fin d → ℕ} (R : InversionResult input n r C taps) :
    R.circuit.size - notCount R.circuit = C.size - notCount C + R.binary := by
  have fits : notCount C ≤ C.size := List.length_filter_le _ _
  rw [R.size_eq,R.count_eq]
  omega

private theorem empty_inversion {X : Type*} (input : X → List Bool) {n r : ℕ}
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C) (taps : Fin 0 → ℕ) :
    Nonempty (InversionResult input n r C taps) := by
  exact ⟨⟨⟨C,taps,0,0⟩,⟨⟨List.prefix_rfl,fan,back⟩,fun i => Fin.elim0 i,
    ⟨by simp,by simp⟩,⟨rfl,rfl⟩,fun _ i => Fin.elim0 i⟩⟩⟩

set_option maxHeartbeats 2000000 in

theorem invert_taps {X : Type*} (input : X → List Bool) {n : ℕ}
    (length : ∀ x, (input x).length = n) {r d : ℕ} (bound : d < 2^r)
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C)
    (ordered : ∀ x, Antitone (fun i => value C (input x) (taps i))) :
    Nonempty (InversionResult input n r C taps) := by
  induction r generalizing d C with
  | zero =>
    have empty : d = 0 := by simpa using bound
    subst d
    exact empty_inversion input fan back taps
  | succ r ih =>
    by_cases positive : 0 < d
    · obtain ⟨F,pivotWire,foldWires,fExt,fFan,fBack,pivotValid,fValid,pivotValue,foldValue,fSize,fCount⟩ :=
        fold_taps input length positive fan back falseWire falseLive falseValue taps live
      have falseF := falseLive.trans_le (nextWire_le_of_prefix (n := n) fExt)
      have offF (x : X) : value F (input x) falseWire = false :=
        (old_value fExt (length x) falseLive).trans (falseValue x)
      have foldOrdered (x : X) : Antitone (fun i => value F (input x) (foldWires i)) := by
        rw [funext (foldValue x)]
        exact folded_antitone positive (ordered x)
      obtain ⟨R⟩ := ih (half_lt_pow bound) fFan fBack falseF offF foldWires fValid foldOrdered
      let gates := decoderGates positive pivotWire falseWire R.wires
      let D := appendFamily R.circuit gates
      let output (i : Fin d) := nextWire n R.circuit + i.val
      have step := appendFamily_prefix R.circuit gates
      have preserve := nextWire_le_of_prefix (n := n) R.extension
      have reads := decoder_reads positive (pivotValid.trans_le preserve)
        (falseF.trans_le preserve) R.valid
      have noNot : ∀ j, (gates j).op ≠ .not := by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ≠ .not
        unfold decoderGates
        split
        · simp
        · split <;> simp
      have basis : FanInTwo D := appendFamily_fanInTwo (gate := gates) R.fanInTwo (by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ∈
          ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
          (decoderGates positive pivotWire falseWire R.wires j).inputs.length ≤ 2
        unfold decoderGates
        split
        · simp
        · split <;> simp)
      refine ⟨⟨⟨D,output,2*half d+R.binary+d,1+R.inversions⟩,
        ⟨⟨fExt.trans (R.extension.trans step),basis,appendFamily_readsBack R.readsBack reads⟩,
          ?_,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩⟩⟩
      · intro i
        simpa only [D,output,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
      · change 2*half d + R.binary + d ≤ 4*d
        have rhs := R.binaryBound
        have halfBound : 2*half d ≤ d := by unfold half; omega
        omega
      · change 1 + R.inversions ≤ r + 1
        have rhs := R.inversionsBound
        omega
      · change D.size = C.size + (2*half d + R.binary + d) + (1 + R.inversions)
        rw [show D.size = R.circuit.size + d from appendFamily_size _ _, R.size_eq,fSize]
        omega
      · change notCount D = notCount C + (1 + R.inversions)
        rw [show notCount D = notCount R.circuit from appendFamily_notCount_eq noNot,R.count_eq,fCount]
        omega
      · intro x i
        have pivotOn : value R.circuit (input x) pivotWire =
            !value C (input x) (taps (pivot positive)) :=
          (old_value R.extension (length x) pivotValid).trans (pivotValue x)
        have off : value R.circuit (input x) falseWire = false :=
          (old_value R.extension (length x) falseF).trans (offF x)
        have tailOn (j : Fin (half d)) : value R.circuit (input x) (R.wires j) =
            !(folded positive (fun k => value C (input x) (taps k)) j) := by
          rw [R.computes,foldValue]
        have bits := family_value (gate := gates) reads (input x) (length x) i
        change value D (input x) (output i) = _ at bits
        rw [bits,decoder_value positive _ _ _ _ _ off,pivotOn]
        exact decoded_correct positive (ordered x) tailOn i
    · have empty : d = 0 := by omega
      subst d
      exact empty_inversion input fan back taps

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def ceilingWire {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (complement : Fin d → ℕ) (u : Input n) : ℕ :=
  if below : rank P N d u < d then complement ⟨rank P N d u,below⟩ else n+1

private theorem ceilingWire_valid {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ) (u : Input n)
    (valid : ∀ i, complement i < nextWire (n+2) C) :
    ceilingWire P N complement u < nextWire (n+2) C := by
  unfold ceilingWire
  split
  · exact valid _
  · unfold nextWire
    omega

private theorem ceilingWire_value {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ)
    (sem : ∀ (i : Fin d) (x : Input n), value C (withConstants x) (complement i) = true ↔
      ¬ i.val+1 ≤ rank P N d x) (u x : Input n) :
    value C (withConstants x) (ceilingWire P N complement u) = true ↔
      ¬ rank P N d u+1 ≤ rank P N d x := by
  unfold ceilingWire
  split
  · exact sem _ x
  · rename_i notBelow
    have atTop : rank P N d u = d := by
      have cap := rank_bound P N d u
      omega
    have noHigher : ¬ rank P N d u+1 ≤ rank P N d x := by
      rw [atTop]
      have cap := rank_bound P N d x
      omega
    exact ⟨fun _ => noHigher,fun _ => true_value C x⟩

set_option maxHeartbeats 1400000 in

theorem append_taps {n m d : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (cone : Input n → ℕ) (complement : Fin d → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneValid : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n, value C (withConstants x) (cone u) = true ↔ u ≤ x)
    (complementValid : ∀ i, complement i < nextWire (n+2) C)
    (complementValue : ∀ (i : Fin d) (x : Input n),
      value C (withConstants x) (complement i) = true ↔ ¬ i.val+1 ≤ rank P N d x)
    (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    ∃ (D : Circuit) (tap : Fin m → Fin (n+2+D.size)),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+(positivePairs P).card ∧
      ∀ (x : Input n) (j : Fin m),
        (P x j → value D (withConstants x) (tap j).val = true) ∧
        (N x j → value D (withConstants x) (tap j).val = false) := by
  classical
  let words := (support P N).toList
  let gate (i : Fin words.length) : Gate := ⟨.and,[cone words[i],ceilingWire P N complement words[i]]⟩
  let guarded := appendFamily C gate
  let term (u : Input n) : ℕ := nextWire (n+2) C + words.idxOf u
  have gateReads (i : Fin words.length) (wire : ℕ) (used : wire ∈ (gate i).inputs) :
      wire < nextWire (n+2) C := by
    have present : words[i] ∈ support P N := Finset.mem_toList.mp (List.getElem_mem i.isLt)
    change wire ∈ [cone words[i],ceilingWire P N complement words[i]] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl | rfl
    · exact coneValid _ present
    · exact ceilingWire_valid P N C complement _ complementValid
  have guardedBasis : FanInTwo guarded := by
    apply appendFamily_fanInTwo basis
    intro i
    change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (2 : ℕ) ≤ 2
    simp
  have guardedReads : ReadsBack (n+2) guarded := appendFamily_readsBack (gate := gate) reads gateReads
  have guardedCost : guarded.size = C.size+(support P N).card := by simp [guarded,words]
  have guardedNot : notCount guarded = notCount C := by
    apply appendFamily_notCount_eq
    intro i
    simp [gate]
  have termValid (u : Input n) (present : u ∈ support P N) : term u < nextWire (n+2) guarded := by
    have found : words.idxOf u < words.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)
    change nextWire (n+2) C + words.idxOf u < nextWire (n+2) (appendFamily C gate)
    rw [appendFamily_nextWire]
    exact Nat.add_lt_add_left found _
  have termValue (u : Input n) (present : u ∈ support P N) (x : Input n) :
      value guarded (withConstants x) (term u) = true ↔ guardedCone P N d u x := by
    let i : Fin words.length := ⟨words.idxOf u,List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)⟩
    have point : words[i] = u := List.getElem_idxOf i.isLt
    have evaluated := appendFamily_new (C := C) (gate := gate) (x := withConstants x)
      (by simpa only [withConstants_length] using gateReads) i
    rw [withConstants_length] at evaluated
    have equation : value guarded (withConstants x) (term u) =
      (value C (withConstants x) (cone words[i]) &&
        value C (withConstants x) (ceilingWire P N complement words[i])) := by
      simpa [guarded,term,i,gate,GateOp.eval] using evaluated
    rw [point] at equation
    change value guarded (withConstants x) (term u) = true ↔
      u ≤ x ∧ ¬ rank P N d u+1 ≤ rank P N d x
    rw [equation,Bool.and_eq_true,coneValue u present x,
      ceilingWire_value P N C complement complementValue u x]
  let rows (j : Fin m) : List ℕ := (positiveInputs P j).toList.map term
  have validRows : ∀ (j : Fin m) a, a ∈ rows j → a < nextWire (n+2) guarded := by
    intro j a member
    obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
    exact termValid u (positive_input_support P N (Finset.mem_toList.mp present))
  obtain ⟨D,out,finalBasis,finalReads,finalPrefix,finalNot,finalSize,outValid,outValue⟩ :=
    append_or_rows guarded rows guardedBasis guardedReads validRows
  have rowCost : (∑ j : Fin m, (rows j).length) = (positivePairs P).card := by
    simpa [rows] using positive_incidence_count P
  have realized (x : Input n) (j : Fin m) :
      value D (withConstants x) (out j) = true ↔ tapAccepts P N d x j := by
    rw [outValue]
    constructor
    · rintro ⟨a,member,active⟩
      obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
      have positive := Finset.mem_toList.mp present
      exact ⟨u,positive,(termValue u (positive_input_support P N positive) x).mp active⟩
    · rintro ⟨u,positive,active⟩
      exact ⟨term u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr positive,rfl⟩,
        (termValue u (positive_input_support P N positive) x).mpr active⟩
  let taps (j : Fin m) : Fin (n+2+(withOutput D 0).size) := ⟨out j,outValid j⟩
  refine ⟨withOutput D 0,taps,finalBasis,finalReads,?_,
    (appendFamily_prefix C gate).trans finalPrefix,finalNot.trans guardedNot,?_,?_⟩
  · simp only [withOutput_output,withOutput_size]
    omega
  · rw [withOutput_size,finalSize,guardedCost,rowCost]
  · intro x j
    change (P x j → value D (withConstants x) (out j) = true) ∧
      (N x j → value D (withConstants x) (out j) = false)
    refine ⟨fun positive => (realized x j).mpr (tap_accepts_positive P N d positive),?_⟩
    intro negative
    exact Bool.eq_false_iff.mpr fun active =>
      tap_rejects_negative P N bounded negative ((realized x j).mp active)

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def Fits {n m : ℕ} (P N : Input n → Fin m → Prop) (r : ℕ) (cost : ℕ → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
    FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ notCount C ≤ r ∧
    cost (C.size-notCount C) ∧ ∀ (x : Input n) (j : Fin m),
      (P x j → value C (withConstants x) (tap j).val = true) ∧
      (N x j → value C (withConstants x) (tap j).val = false)

theorem upper_fits {n m r d : ℕ} (P N : Input n → Fin m → Prop)
    (bound : d < 2^r) (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  obtain ⟨A,cone,aBasis,aReads,aSize,aNot,aSem,_⟩ := supportConeTable_empty P N
  obtain ⟨B,thresholds,bBasis,bReads,bExtends,bNot,bSize,bLive,bSem⟩ :=
    append_thresholds P N d A cone aBasis aReads
      (fun u hu => (aSem u hu).1) (fun u hu => (aSem u hu).2)
  have falseLive : n < nextWire (n+2) B := by unfold nextWire; omega
  obtain ⟨I⟩ := invert_taps (withConstants (n := n)) withConstants_length bound
    bBasis bReads n falseLive (false_value B) thresholds bLive (threshold_antitone bSem)
  have extension : A.gates <+: I.circuit.gates := bExtends.trans I.extension
  have coneLive (u : Input n) (hu : u ∈ support P N) :
      cone u < nextWire (n+2) I.circuit :=
    (aSem u hu).1.trans_le (nextWire_le_of_prefix extension)
  have coneValue (u : Input n) (hu : u ∈ support P N) (x : Input n) :
      value I.circuit (withConstants x) (cone u) = true ↔ u ≤ x := by
    have live : cone u < nextWire (withConstants x).length A := by
      rw [withConstants_length]
      exact (aSem u hu).1
    rw [value_of_prefix extension live]
    exact (aSem u hu).2 x
  have complementValue (i : Fin d) (x : Input n) :
      value I.circuit (withConstants x) (I.wires i) = true ↔ ¬ i.val+1 ≤ rank P N d x := by
    rw [I.computes, ← bSem x i]
    cases value B (withConstants x) (thresholds i) <;> decide
  obtain ⟨C,tap,cBasis,cReads,cOut,_,cNot,cSize,labels⟩ :=
    append_taps P N I.circuit cone I.wires I.fanInTwo I.readsBack
      coneLive coneValue I.valid complementValue bounded
  have bZero : notCount B = 0 := bNot.trans aNot
  have cInversions : notCount C = I.inversions := by
    rw [cNot,I.count_eq,bZero,Nat.zero_add]
  have cBinary : C.size-notCount C ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d := by
    have inversionSize := I.size_eq
    have binaryBudget := I.binaryBound
    rw [cInversions,Nat.add_mul]
    omega
  exact ⟨C,tap,cBasis,cReads,cOut,cInversions.le.trans I.inversionsBound,cBinary,labels⟩

theorem solve_fall_1228 (n m r : ℕ) (P N : Input n → Fin m → Prop) :
    (Fits P N r (fun _ => True) ↔ ∀ x, ¬ Reach P N (2^r) x) ∧
    ∀ d : ℕ, d < 2^r → (∀ x, ¬ Reach P N (d+1) x) →
      Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  constructor
  · constructor
    · rintro ⟨C,tap,basis,_,_,budget,_,labels⟩
      exact no_packing_of_taps (fun j => (tap j).val) basis budget labels
    · intro bounded
      have positive : 0 < (2:ℕ)^r := Nat.pow_pos (by decide)
      have below : (2:ℕ)^r-1 < 2^r := by omega
      have successor : (2:ℕ)^r-1+1 = 2^r := by omega
      have bounded' : ∀ x, ¬ Reach P N ((2:ℕ)^r-1+1) x := by simpa only [successor] using bounded
      obtain ⟨C,tap,basis,reads,output,budget,_,labels⟩ := upper_fits P N below bounded'
      exact ⟨C,tap,basis,reads,output,budget,True.intro,labels⟩
  · intro d bound bounded
    exact upper_fits P N bound bounded

end M1228
end PEqualNP.Outside.L_lib_1416

namespace PEqualNP.Outside.L_lib_1416
namespace Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.NotBracket
open PEqualNP.Outside.L_lib_1416.M1228 (Reach Fits solve_fall_1228 value withConstants reach_succ)

def Near (a f : ℕ) (W Y : Finset ℕ) : Prop := (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f

def ofX {r : ℕ} (x : Fin r → Bool) : Finset ℕ :=
  (Finset.range r).filter (fun j => ∃ h : j < r, x ⟨j, h⟩ = true)

def pt (r : ℕ) (Y : Finset ℕ) : Fin r → Bool := fun j => decide (j.val ∈ Y)

theorem mem_ofX {r : ℕ} (x : Fin r → Bool) (j : ℕ) :
    j ∈ ofX x ↔ ∃ h : j < r, x ⟨j, h⟩ = true := by
  simp only [ofX, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h, e⟩; exact ⟨h, h, e⟩

theorem ofX_sub_range {r : ℕ} (x : Fin r → Bool) : ofX x ⊆ Finset.range r := by
  intro j hj
  obtain ⟨h, _⟩ := (mem_ofX x j).1 hj
  exact Finset.mem_range.2 h

theorem ofX_mono {r : ℕ} {x y : Fin r → Bool} (h : x ≤ y) : ofX x ⊆ ofX y := by
  intro j hj
  obtain ⟨hr, e⟩ := (mem_ofX x j).1 hj
  refine (mem_ofX y j).2 ⟨hr, ?_⟩
  have := h ⟨j, hr⟩
  rw [e] at this
  exact Bool.eq_true_of_true_le this

theorem ofX_pt {r : ℕ} {Y : Finset ℕ} (h : Y ⊆ Finset.range r) : ofX (pt r Y) = Y := by
  ext j
  rw [mem_ofX]
  constructor
  · rintro ⟨_, e⟩
    simpa [pt] using e
  · intro hj
    exact ⟨Finset.mem_range.1 (h hj), by simpa [pt] using hj⟩

theorem pt_ofX {r : ℕ} (x : Fin r → Bool) : pt r (ofX x) = x := by
  funext j
  simp only [pt, mem_ofX]
  cases hx : x j
  · simp only [decide_eq_false_iff_not, not_exists]
    intro h e
    have : (⟨j.val, h⟩ : Fin r) = j := rfl
    rw [this, hx] at e
    exact Bool.false_ne_true e
  · simp only [decide_eq_true_eq]
    exact ⟨j.isLt, hx⟩

theorem pt_mono {r : ℕ} {Y Z : Finset ℕ} (h : Y ⊆ Z) : pt r Y ≤ pt r Z := by
  intro j
  simp only [pt]
  by_cases hy : j.val ∈ Y
  · have hz := h hy
    simp [hy, hz]
  · simp [hy]

section part1

variable {m : ℕ} (W : Fin m → Finset ℕ) (r a f : ℕ)

def PP : (Fin r → Bool) → Fin m → Prop := fun x j => Near a f (W j) (ofX x)
def NN : (Fin r → Bool) → Fin m → Prop := fun x j => ∃ i, i ≠ j ∧ Near a f (W i) (ofX x)

def Collide : Prop :=
  ∃ i j, i ≠ j ∧ ∃ Y ⊆ Finset.range r, Near a f (W i) Y ∧ Near a f (W j) Y

def FitD (b : ℕ) : Prop :=
  ∃ (D : Circuit) (out : Fin m → ℕ),
    FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output < r+2+D.size ∧ (∀ i, out i < r+2+D.size) ∧
    notCount D ≤ b ∧
    ∀ i Y, Y ⊆ Finset.range r → Near a f (W i) Y →
      ∀ j, (D.wires (List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true])).getD (out j)
        false = decide (i = j)

theorem fitD_iff (b : ℕ) : FitD W r a f b ↔ Fits (PP W r a f) (NN W r a f) b (fun _ => True) := by
  constructor
  · rintro ⟨D, out, h1, h2, h3, h4, h5, h6⟩
    refine ⟨D, fun j => ⟨out j, h4 j⟩, h1, h2, h3, h5, trivial, ?_⟩
    intro x j
    have hx : List.ofFn x = List.ofFn (fun k : Fin r => decide (k.val ∈ ofX x)) := by
      congr 1
      exact (pt_ofX x).symm
    constructor
    · intro hp
      have := h6 j (ofX x) (ofX_sub_range x) hp j
      simp only [value, withConstants, hx]
      simpa using this
    · rintro ⟨i, hij, hn⟩
      have := h6 i (ofX x) (ofX_sub_range x) hn j
      simp only [value, withConstants, hx]
      rw [this]
      simpa using hij
  · rintro ⟨C, tap, h1, h2, h3, h5, _, h6⟩
    refine ⟨C, fun j => (tap j).val, h1, h2, h3, fun j => (tap j).isLt, h5, ?_⟩
    intro i Y hY hn j
    have e1 := h6 (pt r Y) j
    have hpt : ofX (pt r Y) = Y := ofX_pt hY
    simp only [value, withConstants, PP, NN, hpt] at e1
    have hl : List.ofFn (pt r Y) = List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) := rfl
    rw [hl] at e1
    by_cases hij : i = j
    · subst hij
      rw [e1.1 hn]
      simp
    · rw [e1.2 ⟨i, hij, hn⟩]
      simp [hij]

theorem reach_of_collide (h : Collide W r a f) :
    ∀ k, ∃ x, Reach (PP W r a f) (NN W r a f) k x := by
  obtain ⟨i, j, hij, Y, hY, hi, hj⟩ := h
  have hpt : ofX (pt r Y) = Y := ofX_pt hY
  have base : ∀ k, Reach (PP W r a f) (NN W r a f) k (pt r Y) := by
    intro k
    induction k with
    | zero => trivial
    | succ k ih =>
      refine (reach_succ _ _ k _).2 ⟨pt r Y, pt r Y, i, ih, le_rfl, le_rfl, ?_, ?_⟩
      · simp only [PP, hpt]; exact hi
      · exact ⟨j, fun e => hij e.symm, by simp only [hpt]; exact hj⟩
  exact fun k => ⟨pt r Y, base k⟩

def TraceD (k : ℕ) : Prop :=
  ∃ (lab : Fin k → Fin m) (Y : Fin k → Finset ℕ), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
    (∀ i j : Fin k, i.val+1 = j.val → lab i ≠ lab j) ∧
    ∀ i, Y i ⊆ Finset.range r ∧ Near a f (W (lab i)) (Y i)

theorem reach_of_traceD {k : ℕ} (h : TraceD W r a f (k+1)) :
    ∃ x, Reach (PP W r a f) (NN W r a f) k x := by
  obtain ⟨lab, Y, inc, alt, mem⟩ := h
  have key : ∀ i (hi : i < k+1), Reach (PP W r a f) (NN W r a f) i (pt r (Y ⟨i, hi⟩)) := by
    intro i
    induction i with
    | zero => intro _; trivial
    | succ i ih =>
      intro hi
      have hi' : i < k+1 := by omega
      refine (reach_succ _ _ i _).2 ⟨pt r (Y ⟨i, hi'⟩), pt r (Y ⟨i+1, hi⟩), lab ⟨i, hi'⟩, ih hi',
        pt_mono (inc _ _ (by simp [Fin.le_def])), le_rfl, ?_, ?_⟩
      · simp only [PP, ofX_pt (mem _).1]; exact (mem _).2
      · refine ⟨lab ⟨i+1, hi⟩, fun e => alt ⟨i, hi'⟩ ⟨i+1, hi⟩ rfl e.symm, ?_⟩
        simp only [ofX_pt (mem _).1]; exact (mem _).2
  exact ⟨_, key k (by omega)⟩

def Good (L : List (Fin m × Finset ℕ)) : Prop :=
  L.Pairwise (fun p q => p.2 ⊆ q.2) ∧ List.IsChain (fun p q => p.1 ≠ q.1) L ∧
    ∀ p ∈ L, p.2 ⊆ Finset.range r ∧ Near a f (W p.1) p.2

theorem good_take {L : List (Fin m × Finset ℕ)} (h : Good W r a f L) (n : ℕ) :
    Good W r a f (L.take n) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.sublist (List.take_sublist _ _), List.IsChain.take h2 n, fun p hp => h3 p (List.mem_of_mem_take hp)⟩

theorem traceD_of_good {L : List (Fin m × Finset ℕ)} (h : Good W r a f L) :
    TraceD W r a f L.length := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => (L.get i).1, fun i => (L.get i).2, ?_, ?_, ?_⟩
  · intro i j hij
    rcases lt_or_eq_of_le hij with hlt | heq
    · exact List.pairwise_iff_get.1 h1 i j hlt
    · rw [heq]
  · intro i j hij
    have := List.isChain_iff_getElem.1 h2 i.val (by omega)
    have hj : j = ⟨i.val+1, by omega⟩ := Fin.ext hij.symm
    rw [hj]
    simpa using this
  · intro i
    exact h3 _ (List.get_mem _ _)

theorem good_of_reach {k : ℕ} {x : Fin r → Bool}
    (h : Reach (PP W r a f) (NN W r a f) (k+1) x) :
    ∃ L, Good W r a f L ∧ k+2 ≤ L.length ∧ ∀ p ∈ L, p.2 ⊆ ofX x := by
  induction k generalizing x with
  | zero =>
    obtain ⟨u, v, j, _, uv, vx, pu, ⟨i, hij, nv⟩⟩ := (reach_succ _ _ 0 x).1 h
    refine ⟨[(j, ofX u), (i, ofX v)], ⟨?_, ?_, ?_⟩, by simp, ?_⟩
    · simp [ofX_mono uv]
    · exact List.isChain_cons_cons.2 ⟨fun e => hij e.symm, List.isChain_singleton _⟩
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨ofX_sub_range u, pu⟩
      · exact ⟨ofX_sub_range v, nv⟩
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ofX_mono (uv.trans vx)
      · exact ofX_mono vx
  | succ k ih =>
    obtain ⟨u, v, j, pr, uv, vx, pu, ⟨i, hij, nv⟩⟩ := (reach_succ _ _ (k+1) x).1 h
    obtain ⟨L, ⟨g1, g2, g3⟩, hlen, hsub⟩ := ih pr
    have hne : L ≠ [] := by
      intro e; rw [e] at hlen; simp at hlen
    by_cases hlast : (L.getLast hne).1 = j
    · refine ⟨L ++ [(i, ofX v)], ⟨?_, ?_, ?_⟩, by simp; omega, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨g1, by simp, ?_⟩
        intro p hp q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact (hsub p hp).trans (ofX_mono uv)
      · rw [List.isChain_append]
        refine ⟨g2, List.isChain_singleton _, ?_⟩
        intro p hp q hq
        rw [List.getLast?_eq_some_getLast hne] at hp
        simp only [Option.mem_def, Option.some.injEq] at hp
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
        subst hp; subst hq
        rw [hlast]; exact fun e => hij e.symm
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact g3 p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact ⟨ofX_sub_range v, nv⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact (hsub p hp).trans (ofX_mono (uv.trans vx))
        · simp only [List.mem_singleton] at hp; subst hp; exact ofX_mono vx
    · refine ⟨L ++ [(j, ofX u), (i, ofX v)], ⟨?_, ?_, ?_⟩, by simp; omega, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨g1, by simp [ofX_mono uv], ?_⟩
        intro p hp q hq
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hsub p hp
        · exact (hsub p hp).trans (ofX_mono uv)
      · rw [List.isChain_append]
        refine ⟨g2, List.isChain_cons_cons.2 ⟨fun e => hij e.symm, List.isChain_singleton _⟩, ?_⟩
        intro p hp q hq
        rw [List.getLast?_eq_some_getLast hne] at hp
        simp only [Option.mem_def, Option.some.injEq] at hp
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
        subst hp; subst hq
        exact hlast
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact g3 p hp
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ⟨ofX_sub_range u, pu⟩
          · exact ⟨ofX_sub_range v, nv⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact (hsub p hp).trans (ofX_mono (uv.trans vx))
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ofX_mono (uv.trans vx)
          · exact ofX_mono vx

theorem good_length_le (hc : ¬ Collide W r a f) {L : List (Fin m × Finset ℕ)}
    (h : Good W r a f L) : L.length ≤ r+1 := by
  obtain ⟨h1, h2, h3⟩ := h

  have strict : List.IsChain (fun p q => p.2.card < q.2.card) L := by
    induction L with
    | nil => exact List.isChain_nil
    | cons p L ih =>
      cases L with
      | nil => exact List.isChain_singleton _
      | cons q L =>
        rw [List.isChain_cons_cons] at h2 ⊢
        have hpq : p.2 ⊆ q.2 := List.rel_of_pairwise_cons h1 (by simp)
        refine ⟨?_, ih (List.Pairwise.of_cons h1) h2.2 (fun t ht => h3 t (List.mem_cons_of_mem _ ht))⟩
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hpq, ?_⟩)
        intro e
        apply hc
        refine ⟨p.1, q.1, h2.1, p.2, (h3 p (by simp)).1, (h3 p (by simp)).2, ?_⟩
        rw [e]; exact (h3 q (by simp)).2
  have hp : (L.map (fun p => p.2.card)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.isChain_iff_pairwise.mp strict
  have hnd : (L.map (fun p => p.2.card)).Nodup := hp.imp (fun h => ne_of_lt h)
  have hsub : ∀ c ∈ L.map (fun p => p.2.card), c ∈ Finset.range (r+1) := by
    intro c hc'
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hc'
    have := Finset.card_le_card (h3 p hp').1
    simp only [Finset.card_range] at this
    exact Finset.mem_range.2 (by omega)
  have := List.Nodup.length_le_card (α := Fin (r+1)) (l := (L.map (fun p => p.2.card)).map
    (fun c => (⟨min c r, by omega⟩ : Fin (r+1)))) ?_
  · simpa using this
  · refine List.Nodup.map_on ?_ hnd
    intro c1 h1' c2 h2' e
    have b1 := Finset.mem_range.1 (hsub c1 h1')
    have b2 := Finset.mem_range.1 (hsub c2 h2')
    simp only [Fin.mk.injEq] at e
    omega

theorem part1 (b : ℕ) :
    ¬ FitD W r a f b ↔ Collide W r a f ∨ (2^b+1 ≤ r+1 ∧ TraceD W r a f (2^b+1)) := by
  rw [fitD_iff, (solve_fall_1228 r m b _ _).1]
  push Not
  constructor
  · rintro ⟨x, hx⟩
    by_cases hc : Collide W r a f
    · exact Or.inl hc
    · right
      have hpos : 2^b = (2^b-1)+1 := by have := Nat.one_le_two_pow (n := b); omega
      rw [hpos] at hx
      obtain ⟨L, hg, hlen, _⟩ := good_of_reach W r a f hx
      have hl := good_length_le W r a f hc hg
      refine ⟨by omega, ?_⟩
      have ht := traceD_of_good W r a f (good_take W r a f hg (2^b+1))
      rwa [List.length_take, min_eq_left (by omega)] at ht
  · rintro (hc | ⟨_, ht⟩)
    · exact reach_of_collide W r a f hc _
    · exact reach_of_traceD W r a f ht

end part1

end Aux
end PEqualNP.Outside.L_lib_1416

namespace PEqualNP.Outside.L_lib_1416
namespace Aux

def Tg (n j : ℕ) : Finset ℕ := Finset.Ico (3*n+1) (3*n+1+(2*n+1)*j)

def padF (n : ℕ) (C : Finset ℕ) : Finset ℕ := C ∪ Finset.Ico (2*n) (2*n+(n+1-C.card))

def litI {n : ℕ} (l : Fin n × Bool) : ℕ := 2*l.1.val + (if l.2 then 1 else 0)

def Aw (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z j : ℕ) : Finset ℕ :=
  if j < m+1+z then Finset.range (2*n)
  else if j-(m+1+z) < n*(m+1) then
    padF n {2*((j-(m+1+z))/(m+1)), 2*((j-(m+1+z))/(m+1))+1}
  else if h : j-(m+1+z)-n*(m+1) < m then
    padF n ((F ⟨j-(m+1+z)-n*(m+1), h⟩).image litI)
  else ∅

def sizeD (n m z : ℕ) : ℕ := (n+2)*(m+1)+m+z
def dimD (n m z : ℕ) : ℕ := 3*n+1+(2*n+1)*sizeD n m z

def Wd (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z : ℕ) (j : Fin (sizeD n m z)) : Finset ℕ :=
  Aw n m F z j.val ∪ Tg n j.val

def lo (n : ℕ) (Y : Finset ℕ) : Finset ℕ := Y.filter (· < 3*n+1)
def hi (n : ℕ) (Y : Finset ℕ) : Finset ℕ := Y.filter (3*n+1 ≤ ·)

theorem litI_lt {n : ℕ} (l : Fin n × Bool) : litI l < 2*n := by
  have := l.1.isLt
  unfold litI; split <;> omega

theorem padF_sub {n : ℕ} {C : Finset ℕ} (h : C ⊆ Finset.range (2*n)) :
    padF n C ⊆ Finset.range (3*n+1) := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · have := Finset.mem_range.1 (h hx); exact Finset.mem_range.2 (by omega)
  · have := Finset.mem_Ico.1 hx; exact Finset.mem_range.2 (by omega)

theorem Aw_sub (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z j : ℕ) :
    Aw n m F z j ⊆ Finset.range (3*n+1) := by
  unfold Aw
  split_ifs with h1 h2 h3
  · intro x hx; have := Finset.mem_range.1 hx; exact Finset.mem_range.2 (by omega)
  · apply padF_sub
    have hv : (j-(m+1+z))/(m+1) < n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.2 (by omega)
  · apply padF_sub
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (litI_lt l)
  · exact Finset.empty_subset _

theorem Tg_ge {n j x : ℕ} (h : x ∈ Tg n j) : 3*n+1 ≤ x := (Finset.mem_Ico.1 h).1

theorem Tg_mono {n j j' : ℕ} (h : j ≤ j') : Tg n j ⊆ Tg n j' := by
  intro x hx
  have := Finset.mem_Ico.1 hx
  have : (2*n+1)*j ≤ (2*n+1)*j' := Nat.mul_le_mul_left _ h
  exact Finset.mem_Ico.2 (by omega)

theorem Tg_card (n j : ℕ) : (Tg n j).card = (2*n+1)*j := by
  simp [Tg]

theorem Tg_sub_hi {n j : ℕ} {Y : Finset ℕ} : Tg n j ∩ Y ⊆ hi n Y := by
  intro x hx
  rw [Finset.mem_inter] at hx
  exact Finset.mem_filter.2 ⟨hx.2, Tg_ge hx.1⟩

theorem hi_sdiff_sub {n j : ℕ} {A Y : Finset ℕ} (hA : A ⊆ Finset.range (3*n+1)) :
    hi n Y \ Tg n j ⊆ Y \ (A ∪ Tg n j) := by
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  have hx1 := Finset.mem_filter.1 hx.1
  refine ⟨hx1.1, ?_⟩
  rw [Finset.mem_union]
  rintro (h | h)
  · have := Finset.mem_range.1 (hA h); omega
  · exact hx.2 h

theorem near_tags {n j : ℕ} {A Y : Finset ℕ} (hA : A ⊆ Finset.range (3*n+1))
    (h : Near n n (A ∪ Tg n j) Y) :
    (2*n+1)*j ≤ (hi n Y).card + n ∧ (hi n Y).card ≤ (2*n+1)*j + n := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have e := Finset.card_sdiff_add_card_inter (Tg n j) Y
    have s1 : Tg n j \ Y ⊆ (A ∪ Tg n j) \ Y := Finset.sdiff_subset_sdiff (Finset.subset_union_right) le_rfl
    have c1 := Finset.card_le_card s1
    have c2 := Finset.card_le_card (Tg_sub_hi (n := n) (j := j) (Y := Y))
    rw [Tg_card] at e
    omega
  · have e := Finset.card_sdiff_add_card_inter (hi n Y) (Tg n j)
    have c1 := Finset.card_le_card (hi_sdiff_sub (n := n) (j := j) (Y := Y) hA)
    have c2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := hi n Y) (s₂ := Tg n j))
    rw [Tg_card] at c2
    omega

theorem hi_mono {n : ℕ} {Y Z : Finset ℕ} (h : Y ⊆ Z) : hi n Y ⊆ hi n Z :=
  Finset.filter_subset_filter _ h

theorem lo_mono {n : ℕ} {Y Z : Finset ℕ} (h : Y ⊆ Z) : lo n Y ⊆ lo n Z :=
  Finset.filter_subset_filter _ h

theorem label_le {n j j' : ℕ} {A A' Y Y' : Finset ℕ} (hA : A ⊆ Finset.range (3*n+1))
    (hA' : A' ⊆ Finset.range (3*n+1)) (hY : Y ⊆ Y')
    (h : Near n n (A ∪ Tg n j) Y) (h' : Near n n (A' ∪ Tg n j') Y') : j ≤ j' := by
  have a := (near_tags hA h).1
  have b := (near_tags hA' h').2
  have c := Finset.card_le_card (hi_mono (n := n) hY)
  by_contra hlt
  push Not at hlt
  have : (2*n+1)*(j'+1) ≤ (2*n+1)*j := Nat.mul_le_mul_left _ hlt
  rw [Nat.mul_succ] at this
  omega

theorem near_lo {n j : ℕ} {A Y : Finset ℕ} (hA : A ⊆ Finset.range (3*n+1))
    (h : Near n n (A ∪ Tg n j) Y) : (A \ lo n Y).card ≤ n ∧ (lo n Y \ A).card ≤ n := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans (Finset.card_le_card ?_) h1
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    refine ⟨Finset.mem_union_left _ hx.1, fun hy => hx.2 ?_⟩
    exact Finset.mem_filter.2 ⟨hy, Finset.mem_range.1 (hA hx.1)⟩
  · refine le_trans (Finset.card_le_card ?_) h2
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    have hx1 := Finset.mem_filter.1 hx.1
    refine ⟨hx1.1, ?_⟩
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hx.2 h
    · have := Tg_ge h; omega

theorem near_of_lo {n j : ℕ} {A X : Finset ℕ} (hA : A ⊆ Finset.range (3*n+1))
    (hX : X ⊆ Finset.range (3*n+1)) (h1 : (A \ X).card ≤ n) (h2 : (X \ A).card ≤ n) :
    Near n n (A ∪ Tg n j) (X ∪ Tg n j) := by
  have disj : ∀ x ∈ Tg n j, x ∉ A ∧ x ∉ X := by
    intro x hx
    have := Tg_ge hx
    exact ⟨fun h => by have := Finset.mem_range.1 (hA h); omega,
      fun h => by have := Finset.mem_range.1 (hX h); omega⟩
  constructor
  · refine le_trans (Finset.card_le_card ?_) h1
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
    rcases hx.1 with h | h
    · exact ⟨h, hx.2.1⟩
    · exact absurd h hx.2.2
  · refine le_trans (Finset.card_le_card ?_) h2
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
    rcases hx.1 with h | h
    · exact ⟨h, hx.2.1⟩
    · exact absurd h hx.2.2

theorem Aw_anchor {n m : ℕ} {F : Fin m → Finset (Fin n × Bool)} {z j : ℕ} (h : j < m+1+z) :
    Aw n m F z j = Finset.range (2*n) := by
  unfold Aw; rw [if_pos h]

theorem Aw_var {n m : ℕ} {F : Fin m → Finset (Fin n × Bool)} {z j : ℕ} (h1 : m+1+z ≤ j)
    (h2 : j < m+1+z+n*(m+1)) :
    Aw n m F z j = padF n {2*((j-(m+1+z))/(m+1)), 2*((j-(m+1+z))/(m+1))+1} := by
  unfold Aw; rw [if_neg (by omega), if_pos (by omega)]

theorem Aw_clause {n m : ℕ} {F : Fin m → Finset (Fin n × Bool)} {z j : ℕ}
    (h1 : m+1+z+n*(m+1) ≤ j) (h2 : j < m+1+z+n*(m+1)+m) :
    Aw n m F z j = padF n ((F ⟨j-(m+1+z)-n*(m+1), by omega⟩).image litI) := by
  unfold Aw; rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]

theorem Aw_empty {n m : ℕ} {F : Fin m → Finset (Fin n × Bool)} {z j : ℕ}
    (h1 : m+1+z+n*(m+1)+m ≤ j) : Aw n m F z j = ∅ := by
  unfold Aw; rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem padF_card_le (n : ℕ) (C : Finset ℕ) : (padF n C).card ≤ C.card + (n+1-C.card) := by
  unfold padF
  refine le_trans (Finset.card_union_le _ _) ?_
  simp

theorem padF_sdiff_of_disj {n : ℕ} {C X : Finset ℕ} (hC : C ⊆ Finset.range (2*n))
    (hX : X ⊆ Finset.range (2*n)) (hd : Disjoint C X) : n+1 ≤ (padF n C \ X).card := by
  have e : padF n C \ X = padF n C := by
    apply Finset.sdiff_eq_self_of_disjoint
    rw [Finset.disjoint_left]
    intro x hx hxX
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.disjoint_left.1 hd h hxX
    · have := Finset.mem_Ico.1 h; have := Finset.mem_range.1 (hX hxX); omega
  rw [e]
  unfold padF
  rw [Finset.card_union_of_disjoint]
  · simp only [Nat.card_Ico]; omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    have := Finset.mem_range.1 (hC hx); have := Finset.mem_Ico.1 hx'; omega

theorem pair_sub {n v : ℕ} (hv : v < n) : ({2*v, 2*v+1} : Finset ℕ) ⊆ Finset.range (2*n) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact Finset.mem_range.2 (by omega)

theorem img_sub {n : ℕ} (C : Finset (Fin n × Bool)) : C.image litI ⊆ Finset.range (2*n) := by
  intro x hx
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_range.2 (litI_lt l)

theorem pair_unique {n : ℕ} {X : Finset ℕ} (hX : X ⊆ Finset.range (2*n)) (hc : X.card ≤ n)
    (hit : ∀ v < n, 2*v ∈ X ∨ 2*v+1 ∈ X) : ∀ v < n, ¬ (2*v ∈ X ∧ 2*v+1 ∈ X) := by
  have himg : X.image (· / 2) = Finset.range n := by
    ext v
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩; have := Finset.mem_range.1 (hX hx); omega
    · intro hv
      rcases hit v hv with h | h
      · exact ⟨_, h, by omega⟩
      · exact ⟨_, h, by omega⟩
  have hcard : (X.image (· / 2)).card = X.card := by
    have := Finset.card_image_le (s := X) (f := (· / 2))
    rw [himg, Finset.card_range] at this ⊢
    omega
  have inj := Finset.card_image_iff.1 hcard
  rintro v hv ⟨h1, h2⟩
  have := inj h1 h2 (by simp only; omega)
  omega

def scoreD {n m : ℕ} (F : Fin m → Finset (Fin n × Bool)) : ℕ :=
  Finset.univ.sup (fun v : Fin n → Bool =>
    (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)).card)

theorem split4 (S : Finset ℕ) (a1 a2 a3 : ℕ) :
    S.card ≤ (S.filter (· < a1)).card + (S.filter (fun j => a1 ≤ j ∧ j < a2)).card +
      (S.filter (fun j => a2 ≤ j ∧ j < a3)).card + (S.filter (a3 ≤ ·)).card := by
  have : S ⊆ S.filter (· < a1) ∪ S.filter (fun j => a1 ≤ j ∧ j < a2) ∪
      S.filter (fun j => a2 ≤ j ∧ j < a3) ∪ S.filter (a3 ≤ ·) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h1 : x < a1
    · exact Or.inl (Or.inl (Or.inl ⟨hx, h1⟩))
    by_cases h2 : x < a2
    · exact Or.inl (Or.inl (Or.inr ⟨hx, by omega, h2⟩))
    by_cases h3 : x < a3
    · exact Or.inl (Or.inr ⟨hx, by omega, h3⟩)
    · exact Or.inr ⟨hx, by omega⟩
  refine le_trans (Finset.card_le_card this) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine Nat.add_le_add_right (le_trans (Finset.card_union_le _ _) ?_) _
  exact Nat.add_le_add_right (Finset.card_union_le _ _) _

theorem filter_card_le_Ico (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (a b : ℕ)
    (h : ∀ x ∈ S, p x → a ≤ x ∧ x < b) : (S.filter p).card ≤ b - a := by
  have : S.filter p ⊆ Finset.Ico a b := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.2 (h x hx.1 hx.2)
  simpa using Finset.card_le_card this

end Aux
end PEqualNP.Outside.L_lib_1416

namespace PEqualNP.Outside.L_lib_1416
namespace Aux

theorem div_window (x d : ℕ) (hd : 0 < d) : x / d * d ≤ x ∧ x < x / d * d + d :=
  ⟨Nat.div_mul_le_self x d, Nat.lt_div_mul_add hd⟩

theorem upper (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z k : ℕ)
    (h : TraceD (Wd n m F z) (dimD n m z) n n k) :
    k ≤ (m+1+z) + n*(m+1) + scoreD F + (m+1) := by
  obtain ⟨lab, Y, inc, alt, mem⟩ := h
  have hW : ∀ i, Near n n (Aw n m F z (lab i).val ∪ Tg n (lab i).val) (Y i) := fun i => (mem i).2
  have mono : ∀ i j : Fin k, i ≤ j → (lab i).val ≤ (lab j).val := fun i j hij =>
    label_le (Aw_sub n m F z _) (Aw_sub n m F z _) (inc i j hij) (hW i) (hW j)
  have smono : ∀ i j : Fin k, i < j → (lab i).val < (lab j).val := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hi1 : i.val + 1 < k := by have := j.isLt; omega
    have a := mono i ⟨i.val+1, hi1⟩ (by rw [Fin.le_def]; simp)
    have b := mono ⟨i.val+1, hi1⟩ j (by rw [Fin.le_def]; simp only; omega)
    have c : (lab i).val ≠ (lab ⟨i.val+1, hi1⟩).val := fun e => alt i ⟨i.val+1, hi1⟩ rfl (Fin.ext e)
    omega
  have back : ∀ i j : Fin k, (lab i).val < (lab j).val → i < j := by
    intro i j hlt
    by_contra hc
    push Not at hc
    have := mono j i hc
    omega
  have inj : Function.Injective (fun i => (lab i).val) := by
    intro i j e
    simp only at e
    rcases lt_trichotomy i j with h | h | h
    · have := smono i j h; omega
    · exact h
    · have := smono j i h; omega
  have hS : (Finset.univ.image (fun i => (lab i).val)).card = k := by
    rw [Finset.card_image_of_injective _ inj]; simp
  have hmemS : ∀ x ∈ Finset.univ.image (fun i => (lab i).val), ∃ i, (lab i).val = x := by
    intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx; exact ⟨i, rfl⟩
  have hlt : ∀ x ∈ Finset.univ.image (fun i => (lab i).val), x < sizeD n m z := by
    intro x hx; obtain ⟨i, rfl⟩ := hmemS x hx; exact (lab i).isLt
  have hsize : sizeD n m z = m+1+z+n*(m+1)+m+(m+1) := by simp only [sizeD]; ring
  generalize hSg : Finset.univ.image (fun i => (lab i).val) = S at hS hmemS hlt
  have sp := split4 S (m+1+z) (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m)
  have b1 := filter_card_le_Ico S (· < m+1+z) 0 (m+1+z) (fun x _ h => ⟨Nat.zero_le _, h⟩)
  have b2 := filter_card_le_Ico S (fun j => m+1+z ≤ j ∧ j < m+1+z+n*(m+1)) (m+1+z)
    (m+1+z+n*(m+1)) (fun x _ h => h)
  have b3 := filter_card_le_Ico S (fun j => m+1+z+n*(m+1) ≤ j ∧ j < m+1+z+n*(m+1)+m)
    (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m) (fun x _ h => h)
  have b4 := filter_card_le_Ico S (m+1+z+n*(m+1)+m ≤ ·) (m+1+z+n*(m+1)+m) (sizeD n m z)
    (fun x hx h => ⟨h, hlt x hx⟩)
  by_cases hE : S.filter (m+1+z+n*(m+1)+m ≤ ·) = ∅
  · rw [hE, Finset.card_empty] at sp; omega
  by_cases hA : S.filter (· < m+1+z) = ∅
  · rw [hA, Finset.card_empty] at sp; omega
  obtain ⟨xq, hxq⟩ := Finset.nonempty_iff_ne_empty.2 hE
  obtain ⟨xp, hxp⟩ := Finset.nonempty_iff_ne_empty.2 hA
  rw [Finset.mem_filter] at hxq hxp
  obtain ⟨q, hq⟩ := hmemS xq hxq.1
  obtain ⟨p, hp⟩ := hmemS xp hxp.1
  have hpA : (lab p).val < m+1+z := hp ▸ hxp.2
  have hqE : m+1+z+n*(m+1)+m ≤ (lab q).val := hq ▸ hxq.2
  have anc := near_lo (Aw_sub n m F z _) (hW p)
  rw [Aw_anchor hpA] at anc
  have emp := near_lo (Aw_sub n m F z _) (hW q)
  rw [Aw_empty hqE] at emp
  have hpq : p ≤ q := le_of_lt (back p q (by omega))
  have cq : (lo n (Y q)).card ≤ n := by simpa using emp.2
  have cp : n ≤ (Finset.range (2*n) ∩ lo n (Y p)).card := by
    have e := Finset.card_sdiff_add_card_inter (Finset.range (2*n)) (lo n (Y p))
    simp only [Finset.card_range] at e
    omega
  have hXq : lo n (Y p) ⊆ lo n (Y q) := lo_mono (inc p q hpq)
  have cX : (lo n (Y p)).card ≤ n := le_trans (Finset.card_le_card hXq) cq
  have hinter : Finset.range (2*n) ∩ lo n (Y p) = lo n (Y p) :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hXr : lo n (Y p) ⊆ Finset.range (2*n) := by
    rw [← hinter]; exact Finset.inter_subset_left
  have cXn : (lo n (Y p)).card = n := by rw [← hinter] at cX ⊢; omega
  have loeq : ∀ i, p ≤ i → i ≤ q → lo n (Y i) = lo n (Y p) := by
    intro i h1 h2
    have u := lo_mono (n := n) (inc p i h1)
    have v := Finset.card_le_card (lo_mono (n := n) (inc i q h2))
    exact (Finset.eq_of_subset_of_card_le u (by omega)).symm
  generalize hXg : lo n (Y p) = X at hXr cXn loeq
  have between : ∀ i : Fin k, m+1+z ≤ (lab i).val → (lab i).val < m+1+z+n*(m+1)+m →
      p ≤ i ∧ i ≤ q := by
    intro i h1 h2
    exact ⟨le_of_lt (back p i (by omega)), le_of_lt (back i q (by omega))⟩
  have varhit : ∀ i : Fin k, m+1+z ≤ (lab i).val → (lab i).val < m+1+z+n*(m+1) →
      ((lab i).val - (m+1+z))/(m+1) < n ∧
      (2*(((lab i).val - (m+1+z))/(m+1)) ∈ X ∨ 2*(((lab i).val - (m+1+z))/(m+1))+1 ∈ X) := by
    intro i h1 h2
    have hv : ((lab i).val - (m+1+z))/(m+1) < n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    refine ⟨hv, ?_⟩
    obtain ⟨bp, bq⟩ := between i h1 (by omega)
    have nl := near_lo (Aw_sub n m F z _) (hW i)
    rw [Aw_var h1 h2, loeq i bp bq] at nl
    by_contra hc
    push Not at hc
    have hd : Disjoint ({2*(((lab i).val - (m+1+z))/(m+1)),
        2*(((lab i).val - (m+1+z))/(m+1))+1} : Finset ℕ) X := by
      rw [Finset.disjoint_left]; intro x hx hxX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hc.1 hxX
      · exact hc.2 hxX
    have := padF_sdiff_of_disj (pair_sub hv) hXr hd
    omega
  let V := Finset.univ.filter (fun v : Fin n => 2*v.val ∈ X ∨ 2*v.val+1 ∈ X)
  have bV : (S.filter (fun j => m+1+z ≤ j ∧ j < m+1+z+n*(m+1))).card ≤ V.card * (m+1) := by
    have hsub : S.filter (fun j => m+1+z ≤ j ∧ j < m+1+z+n*(m+1)) ⊆
        V.biUnion (fun v => Finset.Ico (m+1+z + v.val*(m+1)) (m+1+z + v.val*(m+1) + (m+1))) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨i, rfl⟩ := hmemS x hx.1
      obtain ⟨hv, hhit⟩ := varhit i hx.2.1 hx.2.2
      rw [Finset.mem_biUnion]
      refine ⟨⟨_, hv⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hhit⟩
      · rw [Finset.mem_Ico]
        have w := div_window ((lab i).val - (m+1+z)) (m+1) (by omega)
        simp only
        omega
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    simp
  by_cases hVall : V = Finset.univ
  · have hitall : ∀ v < n, 2*v ∈ X ∨ 2*v+1 ∈ X := by
      intro v hv
      have : (⟨v, hv⟩ : Fin n) ∈ V := by rw [hVall]; exact Finset.mem_univ _
      rw [Finset.mem_filter] at this; exact this.2
    have uniq := pair_unique hXr (by omega) hitall
    let σ : Fin n → Bool := fun v => decide (2*v.val+1 ∈ X)
    have sat : ∀ i : Fin k, (h1 : m+1+z+n*(m+1) ≤ (lab i).val) →
        (h2 : (lab i).val < m+1+z+n*(m+1)+m) →
        ∃ l ∈ F ⟨(lab i).val-(m+1+z)-n*(m+1), by omega⟩, σ l.1 = l.2 := by
      intro i h1 h2
      obtain ⟨bp, bq⟩ := between i (by omega) h2
      have nl := near_lo (Aw_sub n m F z _) (hW i)
      rw [Aw_clause h1 h2, loeq i bp bq] at nl
      by_contra hc
      push Not at hc
      have hd : Disjoint ((F ⟨(lab i).val-(m+1+z)-n*(m+1), by omega⟩).image litI) X := by
        rw [Finset.disjoint_left]
        intro x hx hxX
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
        apply hc l hl
        simp only [σ, litI] at hxX ⊢
        cases hb : l.2
        · rw [hb] at hxX
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hxX
          have := uniq l.1.val l.1.isLt
          simp only [decide_eq_false_iff_not]
          exact fun h => this ⟨hxX, h⟩
        · rw [hb] at hxX
          simp only [↓reduceIte] at hxX
          simpa using hxX
      have := padF_sdiff_of_disj (img_sub _) hXr hd
      omega
    have bC : (S.filter (fun j => m+1+z+n*(m+1) ≤ j ∧ j < m+1+z+n*(m+1)+m)).card ≤ scoreD F := by
      have hsub : S.filter (fun j => m+1+z+n*(m+1) ≤ j ∧ j < m+1+z+n*(m+1)+m) ⊆
          (Finset.univ.filter (fun c : Fin m => ∃ l ∈ F c, σ l.1 = l.2)).image
            (fun c => m+1+z+n*(m+1) + c.val) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨i, rfl⟩ := hmemS x hx.1
        rw [Finset.mem_image]
        refine ⟨⟨(lab i).val-(m+1+z)-n*(m+1), by omega⟩, ?_, by simp only; omega⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, sat i hx.2.1 hx.2.2⟩
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      exact Finset.le_sup (f := fun v : Fin n → Bool =>
        (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)).card) (Finset.mem_univ σ)
    omega
  · have hVc : V.card + 1 ≤ n := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ V, hVall⟩)
      simpa using this
    have hm : V.card * (m+1) + (m+1) ≤ n*(m+1) := by
      have := Nat.mul_le_mul_right (m+1) hVc
      rw [Nat.succ_mul] at this
      exact this
    omega

end Aux
end PEqualNP.Outside.L_lib_1416

namespace PEqualNP.Outside.L_lib_1416
namespace Aux

def Xs {n : ℕ} (σ : Fin n → Bool) : Finset ℕ :=
  Finset.univ.image (fun v : Fin n => 2*v.val + (if σ v then 1 else 0))

theorem Xs_sub {n : ℕ} (σ : Fin n → Bool) : Xs σ ⊆ Finset.range (2*n) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hx
  have := v.isLt
  exact Finset.mem_range.2 (by split <;> omega)

theorem Xs_card {n : ℕ} (σ : Fin n → Bool) : (Xs σ).card = n := by
  unfold Xs
  rw [Finset.card_image_of_injective]
  · simp
  · intro v w e
    simp only at e
    apply Fin.ext
    split at e <;> split at e <;> omega

theorem Xs_mem {n : ℕ} (σ : Fin n → Bool) (v : Fin n) :
    2*v.val + (if σ v then 1 else 0) ∈ Xs σ :=
  Finset.mem_image.2 ⟨v, Finset.mem_univ _, rfl⟩

theorem litI_mem_Xs {n : ℕ} (σ : Fin n → Bool) (l : Fin n × Bool) (h : σ l.1 = l.2) :
    litI l ∈ Xs σ := by
  unfold litI; rw [← h]; exact Xs_mem σ l.1

theorem anchor_sdiff {n : ℕ} (σ : Fin n → Bool) : (Finset.range (2*n) \ Xs σ).card ≤ n := by
  rw [Finset.card_sdiff_of_subset (Xs_sub σ), Xs_card, Finset.card_range]; omega

theorem sdiff_le_of_meet {n : ℕ} {A X : Finset ℕ} (hc : A.card ≤ n+1) (hm : (A ∩ X).Nonempty) :
    (A \ X).card ≤ n := by
  have e := Finset.card_sdiff_add_card_inter A X
  have := Finset.card_pos.2 hm
  omega

theorem traceD_mono {m : ℕ} {W : Fin m → Finset ℕ} {r a f L k : ℕ} (h : TraceD W r a f L)
    (hk : k ≤ L) : TraceD W r a f k := by
  obtain ⟨lab, Y, inc, alt, mem⟩ := h
  refine ⟨fun i => lab (Fin.castLE hk i), fun i => Y (Fin.castLE hk i), ?_, ?_, ?_⟩
  · intro i j hij; exact inc _ _ (Fin.le_def.2 (by simp only [Fin.coe_castLE]; exact hij))
  · intro i j hij; exact alt _ _ (by simpa using hij)
  · intro i; exact mem _

theorem lower (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z : ℕ) :
    TraceD (Wd n m F z) (dimD n m z) n n ((m+1+z) + n*(m+1) + scoreD F + (m+1)) := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Bool))
    Finset.univ_nonempty (fun v : Fin n → Bool =>
      (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)).card)
  have hscore : scoreD F = (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, σ l.1 = l.2)).card := hσ
  set sat := Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, σ l.1 = l.2) with hsat
  let U : Finset ℕ := Finset.range (m+1+z+n*(m+1)) ∪
    (sat.image (fun c => m+1+z+n*(m+1) + c.val)) ∪
    Finset.Ico (m+1+z+n*(m+1)+m) (m+1+z+n*(m+1)+m+(m+1))
  have hU : U.card = (m+1+z) + n*(m+1) + scoreD F + (m+1) := by
    have d1 : Disjoint (Finset.range (m+1+z+n*(m+1))) (sat.image (fun c => m+1+z+n*(m+1) + c.val)) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx'
      have := Finset.mem_range.1 hx; omega
    have d2 : Disjoint (Finset.range (m+1+z+n*(m+1)) ∪ (sat.image (fun c => m+1+z+n*(m+1) + c.val)))
        (Finset.Ico (m+1+z+n*(m+1)+m) (m+1+z+n*(m+1)+m+(m+1))) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      have := (Finset.mem_Ico.1 hx').1
      rcases Finset.mem_union.1 hx with hx | hx
      · have := Finset.mem_range.1 hx; omega
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx; have := c.isLt; omega
    simp only [U]
    rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
      Finset.card_image_of_injective _ (fun a b e => Fin.ext (by simpa using e)), hscore]
    simp
  have hsize : sizeD n m z = m+1+z+n*(m+1)+m+(m+1) := by simp only [sizeD]; ring
  let e := U.orderEmbOfFin hU
  have emem : ∀ i, e i ∈ U := fun i => Finset.orderEmbOfFin_mem U hU i
  have elt : ∀ i, e i < sizeD n m z := by
    intro i
    have := emem i
    simp only [U, Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_image] at this
    rcases this with (h | ⟨c, _, h⟩) | h
    · omega
    · have := c.isLt; omega
    · omega
  refine ⟨fun i => ⟨e i, elt i⟩, fun i => Xs σ ∪ Tg n (e i), ?_, ?_, ?_⟩
  · intro i j hij
    exact Finset.union_subset_union le_rfl (Tg_mono (e.monotone hij))
  · intro i j hij heq
    have : e i = e j := by simpa using congrArg Fin.val heq
    have := e.injective this
    rw [this] at hij; omega
  · intro i
    constructor
    · apply Finset.union_subset
      · intro x hx; have := Finset.mem_range.1 (Xs_sub σ hx)
        exact Finset.mem_range.2 (by simp only [dimD]; omega)
      · intro x hx
        have h1 := Finset.mem_Ico.1 hx
        have h2 : (2*n+1)*(e i) ≤ (2*n+1)*sizeD n m z := Nat.mul_le_mul_left _ (le_of_lt (elt i))
        exact Finset.mem_range.2 (by simp only [dimD]; omega)
    · simp only [Wd]
      have hXs : Xs σ ⊆ Finset.range (3*n+1) := fun x hx => by
        have := Finset.mem_range.1 (Xs_sub σ hx); exact Finset.mem_range.2 (by omega)
      refine near_of_lo (Aw_sub n m F z _) hXs ?_ ?_
      · have hm := emem i
        simp only [U, Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_image] at hm
        by_cases ha : e i < m+1+z
        · rw [Aw_anchor ha]; exact anchor_sdiff σ
        by_cases hv : e i < m+1+z+n*(m+1)
        · push Not at ha
          rw [Aw_var ha hv]
          set v := (e i - (m+1+z))/(m+1) with hvdef
          have hvn : v < n := by rw [hvdef, Nat.div_lt_iff_lt_mul (by omega)]; omega
          apply sdiff_le_of_meet
          · refine le_trans (padF_card_le _ _) ?_
            have hn1 : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le v) hvn
            rw [Finset.card_pair (show 2*v ≠ 2*v+1 by omega)]; omega
          · refine ⟨2*v + (if σ ⟨v, hvn⟩ then 1 else 0), Finset.mem_inter.2 ⟨?_, Xs_mem σ ⟨v, hvn⟩⟩⟩
            unfold padF
            apply Finset.mem_union_left
            split <;> simp
        by_cases hc : e i < m+1+z+n*(m+1)+m
        · push Not at ha hv
          rw [Aw_clause hv hc]
          obtain ⟨c, hcs, hce⟩ : ∃ c ∈ sat, m+1+z+n*(m+1) + c.val = e i := by
            rcases hm with (h | ⟨c, hcs, h⟩) | h
            · omega
            · exact ⟨c, hcs, h⟩
            · omega
          have hcv : (⟨e i-(m+1+z)-n*(m+1), by omega⟩ : Fin m) = c := Fin.ext (by simp only; omega)
          rw [hcv]
          obtain ⟨l, hl, hsl⟩ := (Finset.mem_filter.1 hcs).2
          have hmeet : litI l ∈ (F c).image litI ∩ Xs σ :=
            Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨l, hl, rfl⟩, litI_mem_Xs σ l hsl⟩

          have hsplit : padF n ((F c).image litI) \ Xs σ ⊆
              ((F c).image litI \ Xs σ) ∪ Finset.Ico (2*n) (2*n+(n+1-((F c).image litI).card)) := by
            intro x hx
            simp only [padF, Finset.mem_sdiff, Finset.mem_union] at hx ⊢
            rcases hx.1 with h | h
            · exact Or.inl ⟨h, hx.2⟩
            · exact Or.inr h
          refine le_trans (Finset.card_le_card hsplit) (le_trans (Finset.card_union_le _ _) ?_)
          have c1 := Finset.card_sdiff_add_card_inter ((F c).image litI) (Xs σ)
          have c2 := Finset.card_pos.2 ⟨_, hmeet⟩
          have c3 : ((F c).image litI \ Xs σ).card ≤ n := by
            refine le_trans (Finset.card_le_card (Finset.sdiff_subset_sdiff (img_sub (F c)) le_rfl))
              (anchor_sdiff σ)
          simp only [Nat.card_Ico]
          omega
        · push Not at ha hv hc
          rw [Aw_empty hc]; simp
      · exact le_trans (Finset.card_le_card Finset.sdiff_subset) (Xs_card σ).le

end Aux
end PEqualNP.Outside.L_lib_1416

namespace PEqualNP.Outside.L_lib_1416
namespace Aux

theorem no_collide (n m : ℕ) (F : Fin m → Finset (Fin n × Bool)) (z : ℕ) :
    ¬ Collide (Wd n m F z) (dimD n m z) n n := by
  rintro ⟨i, j, hij, Y, _, hi, hj⟩
  have a := label_le (Aw_sub n m F z _) (Aw_sub n m F z _) (le_refl Y) hi hj
  have b := label_le (Aw_sub n m F z _) (Aw_sub n m F z _) (le_refl Y) hj hi
  exact hij (Fin.ext (le_antisymm a b))

theorem score_le {n m : ℕ} (F : Fin m → Finset (Fin n × Bool)) : scoreD F ≤ m := by
  unfold scoreD
  refine Finset.sup_le (fun v _ => ?_)
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

theorem part2 (n m t : ℕ) (F : Fin m → Finset (Fin n × Bool)) (h1 : 1 ≤ t) (h2 : t ≤ m) :
    sizeD n m (2^(Nat.log2 (4*((n+2)*(m+1)+m+1)))+1-t-(n+2)*(m+1)) ≤ 6*((n+2)*(m+1)+m+1) ∧
    ∀ b, FitD (Wd n m F (2^(Nat.log2 (4*((n+2)*(m+1)+m+1)))+1-t-(n+2)*(m+1)))
      (dimD n m (2^(Nat.log2 (4*((n+2)*(m+1)+m+1)))+1-t-(n+2)*(m+1))) n n b ↔
      Nat.log2 (4*((n+2)*(m+1)+m+1)) + (if t ≤ scoreD F then 1 else 0) ≤ b := by
  generalize hA : (n+2)*(m+1) = A
  generalize hc : Nat.log2 (4*(A+m+1)) = c
  have hX : 4*(A+m+1) ≠ 0 := by omega
  have p1 := Nat.log2_self_le hX
  have p2 := @Nat.lt_log2_self (4*(A+m+1))
  rw [hc] at p1 p2
  have p3 : 2^(c+1) = 2*2^c := by rw [pow_succ]; ring
  have hc1 : 1 ≤ c := by
    by_contra h; push Not at h
    have : c = 0 := by omega
    rw [this] at p2; simp at p2; omega
  have p4 : 2^c = 2*2^(c-1) := by
    rw [← pow_succ']; congr 1; omega
  have hA' : A = n*(m+1) + 2*(m+1) := by rw [← hA]; ring
  generalize hz : 2^c+1-t-A = z
  have hzt : z + t + A = 2^c + 1 := by omega
  have hsc := score_le F
  refine ⟨?_, ?_⟩
  · simp only [sizeD]; rw [hA]; omega
  · intro b
    have key := part1 (Wd n m F z) (dimD n m z) n n b
    have tr : ∀ k, TraceD (Wd n m F z) (dimD n m z) n n k ↔
        k ≤ (m+1+z) + n*(m+1) + scoreD F + (m+1) :=
      fun k => ⟨upper n m F z k, fun h => traceD_mono (lower n m F z) h⟩
    rw [tr] at key
    have hdim : (m+1+z) + n*(m+1) + scoreD F + (m+1) ≤ dimD n m z := by
      simp only [dimD, sizeD]
      have : sizeD n m z ≤ (2*n+1)*sizeD n m z := Nat.le_mul_of_pos_left _ (by omega)
      simp only [sizeD] at this
      rw [hA]
      nlinarith [this]
    have hfit : FitD (Wd n m F z) (dimD n m z) n n b ↔
        ¬ ((m+1+z) + n*(m+1) + scoreD F + (m+1) ≥ 2^b+1) := by
      constructor
      · intro hf hge
        exact (key.2 (Or.inr ⟨by omega, hge⟩)) hf
      · intro hn
        by_contra hf
        rcases key.1 hf with hcol | ⟨_, hge⟩
        · exact no_collide n m F z hcol
        · exact hn hge
    rw [hfit]
    have mono : ∀ x y : ℕ, x ≤ y → 2^x ≤ 2^y := fun x y h => Nat.pow_le_pow_right (by norm_num) h
    split_ifs with hts
    · constructor
      · intro hn
        by_contra hb; push Not at hb
        have := mono b c (by omega)
        omega
      · intro hb
        have := mono (c+1) b hb
        omega
    · constructor
      · intro hn
        by_contra hb; push Not at hb
        have := mono b (c-1) (by omega)
        omega
      · intro hb
        have := mono c b (by omega)
        omega

end Aux
end PEqualNP.Outside.L_lib_1416

open PEqualNP.Outside.L_lib_1416.Aux in
theorem PEqualNP.Outside.L_lib_1416 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let tag := fun (s w j : Nat) => Finset.Ico s (s+w*j)
let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
let inc := fun {m : Nat} (Y : Fin m → Finset Nat) => ∀ i j, i ≤ j → Y i ⊆ Y j
let trace := fun {m : Nat} (W : Fin m → Finset Nat) (r a f k : Nat) =>
  ∃ (lab : Fin k → Fin m) (Y : Fin k → Finset Nat), inc Y ∧
    (∀ i j, i.val+1=j.val → lab i ≠ lab j) ∧ ∀ i, Y i ⊆ Finset.range r ∧ near a f (W (lab i)) (Y i)
let base := fun (n m : Nat) => (n+2)*(m+1)
let size := fun (n m z : Nat) => base n m + m + z
let dim := fun (n m z : Nat) => 3*n+1+(2*n+1)*size n m z
let words := fun {n m : Nat} (F : Fin m → Finset (Fin n × Bool)) (z : Nat) (j : Fin (size n m z)) =>
  let t := m+1
  let left := t+z
  let i := j.val-left
  let pad := fun (C : Finset Nat) => C ∪ Finset.Ico (2*n) (2*n+(n+1-C.card))
  let A := if j.val < left then Finset.range (2*n) else if i < n*t then
    pad {2*(i/t), 2*(i/t)+1}
    else if h : i-n*t < m then
      pad ((F ⟨i-n*t,h⟩).image (fun l => 2*l.1.val + (if l.2 then 1 else 0)))
    else ∅
  A ∪ tag (3*n+1) (2*n+1) j.val
let score := fun {n m : Nat} (F : Fin m → Finset (Fin n × Bool)) =>
  Finset.univ.sup (fun v : Fin n → Bool =>
    (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)).card)
let fit := fun {m : Nat} (W : Fin m → Finset Nat) (r a f b : Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
    D.output < r+2+D.size ∧ (∀ i, out i < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
    ∀ i Y, Y ⊆ Finset.range r → near a f (W i) Y →
      let v := D.wires (List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true])
      ∀ j, v.getD (out j) false = decide (i=j)
(∀ (r m a f b : Nat) (W : Fin m → Finset Nat), (∀ i, W i ⊆ Finset.range r) →
  (¬fit W r a f b ↔
    (∃ i j, i ≠ j ∧ ∃ Y ⊆ Finset.range r, near a f (W i) Y ∧ near a f (W j) Y) ∨
    (2^b+1 ≤ r+1 ∧ trace W r a f (2^b+1)))) ∧
∀ (n m t : Nat) (F : Fin m → Finset (Fin n × Bool)), 1 ≤ t → t ≤ m →
  let A := base n m
  let c := Nat.log2 (4*(A+m+1))
  let z := 2^c+1-t-A
  size n m z ≤ 6*(A+m+1) ∧
    ∀ b : Nat, fit (words F z) (dim n m z) n n b ↔
      c + (if t ≤ score F then 1 else 0) ≤ b := by
  intro tag near inc trace base size dim words score fit
  have hnear : ∀ a f W Y, near a f W Y ↔ Near a f W Y := by
    intro a f W Y
    simp only [near, Near]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Eq.trans_le (by congr 1; ext x; simp) h1, Eq.trans_le (by congr 1; ext x; simp) h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Eq.trans_le (by congr 1; ext x; simp) h1, Eq.trans_le (by congr 1; ext x; simp) h2⟩
  have htrace : ∀ {m : ℕ} (W : Fin m → Finset ℕ) r a f k, trace W r a f k ↔ TraceD W r a f k := by
    intro m W r a f k
    simp only [trace, inc, TraceD, hnear]
  have hfit : ∀ {m : ℕ} (W : Fin m → Finset ℕ) r a f b, fit W r a f b ↔ FitD W r a f b := by
    intro m W r a f b
    simp only [fit, FitD, hnear]
    constructor
    · rintro ⟨D, out, h1, h2, h3, h4, h5, h6⟩
      refine ⟨D, out, h1, h2, h3, h4, h5, ?_⟩
      intro i Y hY hn j
      have := h6 i Y hY hn j
      convert this
    · rintro ⟨D, out, h1, h2, h3, h4, h5, h6⟩
      refine ⟨D, out, h1, h2, h3, h4, h5, ?_⟩
      intro i Y hY hn j
      have := h6 i Y hY hn j
      convert this
  constructor
  · intro r m a f b W hW
    rw [hfit, htrace, part1 W r a f b]
    simp only [Collide, hnear]
  · intro n m t F h1 h2 A c z
    have hwords : words F z = Wd n m F z := by
      funext j
      ext x
      simp only [words, Wd, Aw, padF, litI, tag, Tg]
      split_ifs <;> congr! <;> (simp only [litI]; split_ifs <;> simp_all)
    have hscore : score F = scoreD F := by
      simp only [score, scoreD]
      congr!
    obtain ⟨hs, hb⟩ := part2 n m t F h1 h2
    refine ⟨hs, fun b => ?_⟩
    rw [hfit, hwords]
    refine Iff.trans (hb b) ?_
    rw [hscore]
    split_ifs <;> exact Iff.rfl
