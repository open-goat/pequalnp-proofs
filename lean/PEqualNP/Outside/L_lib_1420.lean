import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates
namespace PulseList
open CircuitLowerBounds
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

end PulseList

namespace FiniteGateBank

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PulseList (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

abbrev Net (n : Nat) := {gs : List Gate // FanInTwo ⟨gs,0⟩ ∧
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n+j}
abbrev Net.gates (p : Net n) := p.val
theorem gates_mk (gs : List Gate) (ok) : Net.gates (n:=n) ⟨gs,ok⟩=gs := rfl
theorem Net.fan (p : Net n) : FanInTwo ⟨p.gates,0⟩ := p.property.1
theorem Net.back (p : Net n) : ∀ j (hj : j < p.gates.length), ∀ i ∈ p.gates[j].inputs, i < n+j := p.property.2

def empty (n : Nat) : Net n := ⟨[],by simp [FanInTwo],by simp⟩

def Net.cost (p : Net n) := NotBracket.notCount ⟨p.gates,0⟩

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) :=
  ∃ i, i < n+p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size neg : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length+size ∧ q.cost=p.cost+neg

theorem start (raw : X → List Bool) (p : Net n) : Grow raw p p 0 0 := by simp [Grow]

theorem chain {raw : X → List Bool} {p q r : Net n} {a b c d : Nat}
    (pq : Grow raw p q a b) (qr : Grow raw q r c d) : Grow raw p r (a+c) (b+d) :=
  ⟨fun f h => qr.1 f (pq.1 f h),by have := pq.2.1; have := qr.2.1; omega,
    by rw [qr.2.2,pq.2.2,Nat.add_assoc]⟩

theorem allowance {raw : X → List Bool} {p q : Net n} {a b c : Nat}
    (grow : Grow raw p q a b) (le : a≤c) : Grow raw p q c b :=
  ⟨grow.1,grow.2.1.trans (Nat.add_le_add_left le _),grow.2.2⟩

private def extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n := by
  refine ⟨p.gates++[g],?_,?_⟩
  ·
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  · intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j=p.gates.length := by simp at hj; omega
      subst j
      simp at hi
      exact ok i hi

private theorem emit {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) :
    ∃ q, Grow raw p q 1 (if g.op=.not then 1 else 0) ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := extend p g ops ok
  have len (x : X) : (run p.gates (raw x)).length=n+p.gates.length := by rw [run_length,width]
  refine ⟨q,⟨?_,by simp [q,extend,gates_mk],?_⟩,n+p.gates.length,by simp [q,extend,gates_mk],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend,gates_mk]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,gates_mk,List.filter_append,List.length_append]
    split <;> simp_all
  · intro x
    change (run (p.gates++[g]) (raw x)).getD (n+p.gates.length) false = _
    rw [run_append,run_singleton,←len x]; simp

theorem binary {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a b : X → Bool) (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q, Grow raw p q 1 0 ∧ q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨i,hi,readI⟩ := ha
  obtain ⟨j,hj,readJ⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or,[i,j]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by cases isAnd <;> simp [g]) (by simp [g,hi,hj])
  refine ⟨q,by cases isAnd <;> simpa [g] using grow,?_⟩
  convert w using 2 with x
  cases isAnd <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    PulseList.eval_and2,PulseList.eval_or2, readI,readJ] <;> rfl

theorem invert {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a : X → Bool) (ha : p.has raw a) :
    ∃ q, Grow raw p q 1 1 ∧ q.has raw (fun x => !(a x)) := by
  obtain ⟨i,hi,readI⟩ := ha
  let g : Gate := ⟨.not,[i]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by simp [g]) (by simp [g,hi])
  refine ⟨q,by simpa [g] using grow,?_⟩
  convert w using 2 with x
  change (!(a x)) = (!((run p.gates (raw x)).getD i false))
  rw [readI]

theorem anyList {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,zero⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old false
    exact ⟨r,chain gq gr,by simpa [List.any_cons] using ans⟩

theorem batch {raw : X → List Bool} (p : Net n) (l : List J) (f : J → X → Bool) (s z : Nat)
    (build : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r, Grow raw q r s z ∧ r.has raw (f j)) :
    ∃ r, Grow raw p r (l.length*s) (l.length*z) ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p,by simpa using start raw p,by simp⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => build i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := build j (by simp) q gq.1
    refine ⟨r,by simpa [Nat.succ_mul] using chain gq gr,?_⟩
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact ans
    · exact gr.1 _ (old i h)

theorem Net.readsBack (p : Net n) : ReadsBack n ⟨p.gates,0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi)

end FiniteGateBank

namespace OrderedThresholdBank

open FiniteGateBank

variable {X : Type} {n : Nat}

def high (r : X → Nat) (i : Nat) (x : X) := decide (i ≤ r x)
def low (r : X → Nat) (i : Nat) (x : X) := decide (r x < i)

theorem decode (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (b k : Nat)
    (room : k < 2^b) (r : X → Nat) (bound : ∀ x, r x≤k) (p : Net n)
    (zero : p.has raw (fun _ => false)) (known : ∀ i : Nat, 0 < i → i ≤ k → p.has raw (high r i)) :
    ∃ q, Grow raw p q (4*k+b) b ∧ ∀ i : Nat, 0 < i → i ≤ k → q.has raw (low r i) := by
  induction b generalizing k r p with
  | zero =>
    have : k=0 := by simpa using room
    subst k
    exact ⟨p,by simpa using start raw p,by omega⟩
  | succ b ih =>
    let a := k/2
    let m := a+1
    let rem (x : X) := if r x < m then r x else r x-m
    have small : k < 2*m := by dsimp [m,a]; omega
    have rem_le (x) : rem x≤a := by
      have := bound x
      dsimp [rem,m,a] at *
      split <;> omega
    have limited : a < 2^b := by dsimp [a]; rw [pow_succ] at room; omega
    have avail (i) (pos : 0 < i) : p.has raw (high r i) := by
      by_cases le : i≤k
      · exact known i pos le
      · convert zero using 2 with x
        simp [high,show ¬i≤r x by have := bound x; omega]
    obtain ⟨p₁,g₁,hneg⟩ := invert width p (high r m) (avail m (by dsimp [m]; omega))
    let ids := List.range a
    obtain ⟨p₂,g₂,hrem⟩ := batch (raw:=raw) p₁ ids (fun j => high rem (j+1)) 2 0 (by
      intro j hj q keep
      have index : j < a := List.mem_range.mp hj
      obtain ⟨u,gu,band⟩ := binary width q _ _ (keep _ hneg) (keep _ (g₁.1 _ (avail (j+1) (by omega)))) true
      obtain ⟨v,gv,bor⟩ := binary width u _ _ band (gu.1 _ (keep _ (g₁.1 _ (avail (m+(j+1)) (by omega))))) false
      refine ⟨v,chain gu gv,?_⟩
      convert bor using 2 with x
      have := bound x
      apply Bool.eq_iff_iff.mpr
      simp only [high,rem,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
        decide_eq_false_iff_not,ite_true,ite_false,Bool.false_eq_true]
      dsimp [m] at *
      split <;> omega)
    have residual (i) (pos : 0 < i) (le : i≤a) : p₂.has raw (high rem i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact hrem j (List.mem_range.mpr (by omega))
    obtain ⟨p₃,g₃,remneg⟩ := ih a limited rem rem_le p₂ (g₂.1 _ (g₁.1 _ zero)) residual
    have g123 := chain (chain g₁ g₂) g₃
    have mid := g₃.1 _ (g₂.1 _ hneg)
    obtain ⟨q,g₄,outs⟩ := batch (raw:=raw) p₃ (List.range k) (fun j => low r (j+1)) 1 0 (by
      intro j hj u keep
      have jk : j < k := List.mem_range.mp hj
      by_cases below : j+1 < m
      · have le : j+1≤a := by dsimp [m] at below; omega
        obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1) (by omega) le)) true
        refine ⟨v,g,?_⟩
        convert h using 2 with x
        apply Bool.eq_iff_iff.mpr
        simp only [low,high,rem,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
        split <;> omega
      · by_cases eq : j+1=m
        · refine ⟨u,allowance (start raw u) (by decide : 0≤1),?_⟩
          convert keep _ mid using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [high,low,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          omega
        · have above : m < j+1 := by omega
          have ix : j+1-m≤a := by dsimp [m,a] at *; omega
          obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1-m) (by omega) ix)) false
          refine ⟨v,g,?_⟩
          convert h using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [low,high,rem,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          split <;> omega)
    have gr := chain g123 g₄
    simp only [ids,List.length_range,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at gr
    refine ⟨q,?_,?_⟩
    · have gr' := allowance gr (show 1 + a*2 + (4*a+b) + k ≤ 4*k+(b+1) by dsimp [a]; omega)
      simpa [Nat.add_comm 1 b] using gr'
    · intro i pos le
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact outs j (List.mem_range.mpr (by omega))

end OrderedThresholdBank

namespace MarkedInversionRank
open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

private def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

private def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
private def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

private theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

private theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

private theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem circuit_rank {n : Nat} (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ h : (Fin n → Bool) → Nat, Monotone h ∧ (∀ x, h x < 2^PEqualNP.NotBracket.notCount C) ∧
      ∀ x y, x ≤ y → h x = h y → ∀ w,
        (C.wires (List.ofFn x ++ [false,true])).getD w false=true →
        (C.wires (List.ofFn y ++ [false,true])).getD w false=true := by
  let raw (x : Fin n → Bool) := List.ofFn x ++ [false,true]
  let h (x : Fin n → Bool) := driverNumber (code C.gates (raw x))
  have ops (g : Gate) (mem : g ∈ C.gates) := (fan g mem).1
  have order {x y : Fin n → Bool} (xy : x ≤ y) : ordered (raw x) (raw y) := by
    apply input_order
    intro i hi
    have v := xy i
    rw [hi] at v
    exact le_antisymm (by cases y i <;> decide) v
  have size : (C.gates.filter mark).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [mark,eq]
  refine ⟨h,fun x y xy => driver_mono _ ops (order xy),?_,?_⟩
  · intro x
    simpa only [h,code_len,size] using driver_bound (code C.gates (raw x))
  · intro x y xy eq w
    have same : code C.gates (raw x)=code C.gates (raw y) := driver_injective (by simp [code_len]) eq
    exact (output_order ops (order xy) same).2 w

end MarkedInversionRank

end PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates
open FiniteGateBank
open scoped Classical
variable {X I : Type} {n : ℕ} {src : X → List Bool}
noncomputable abbrev bit (F : X → Prop) := fun x => @decide (F x) (Classical.propDecidable _)
def Has (p : Net n) (src : X → List Bool) (F : X → Prop) := p.has src (bit F)

theorem hasCong {p : Net n} {F G : X → Prop} (same : ∀ x, F x ↔ G x) (old : Has p src F) :
    Has p src G := by
  have eq : bit F = bit G := by funext x; simp [bit,same x]
  simpa only [Has,← eq] using old

theorem foldPred (width : ∀ x, (src x).length=n) (s : Finset I) (F : I → X → Prop)
    (p : Net n) (conjunction : Bool) (emptyBit : p.has src (fun _ => conjunction))
    (known : ∀ i∈s, Has p src (F i)) :
    ∃ q, Grow src p q s.card 0 ∧ Has q src
      (fun x => if conjunction then ∀ i∈s, F i x else ∃ i∈s, F i x) := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty =>
    refine ⟨p,start src p,?_⟩
    unfold Has
    convert emptyBit using 2
    cases conjunction <;> simp [bit]
  | @insert i s hi ih =>
    obtain ⟨q,g,acc⟩ := ih p emptyBit (fun j hj => known j (Finset.mem_insert_of_mem hj))
    obtain ⟨v,gv,out⟩ := binary width q _ _ (g.1 _ (known i (Finset.mem_insert_self ..))) acc conjunction
    refine ⟨v,by simpa [hi] using chain g gv,?_⟩
    unfold Has bit
    convert out using 2
    cases conjunction <;> simp [bit,Finset.exists_mem_insert]

theorem batchPred {p : Net n} (s : Finset I) (F : I → X → Prop) (k : ℕ)
    (build : ∀ i ∈ s, ∀ q : Net n, (∀ a, p.has src a → q.has src a) →
      ∃ v, Grow src q v k 0 ∧ Has v src (F i)) :
    ∃ v, Grow src p v (s.card*k) 0 ∧ ∀ i ∈ s, Has v src (F i) := by
  obtain ⟨v,g,haveAll⟩ := batch (raw:=src) p s.toList (fun i => bit (F i)) k 0
    (fun i hi => build i (Finset.mem_toList.mp hi))
  exact ⟨v,by simpa using g,fun i hi => haveAll i (Finset.mem_toList.mpr hi)⟩
end PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates
open scoped Classical
def Near (a f : ℕ) (W Y : Finset ℕ) := (W\Y).card≤a ∧ (Y\W).card≤f
def input (r : ℕ) (Y : Finset ℕ) := List.ofFn (fun j : Fin r => decide (j.val∈Y)) ++ [false,true]
def Valid (r : ℕ) (D : Circuit) := FanInTwo D ∧ NestedCover.ReadsBack (r+2) D ∧ D.output<r+2+D.size
def Fit (W : Fin (h+1) → Finset ℕ) (r a f b p : ℕ) (V : Finset ℕ) :=
  ∃ (D : Circuit) (out : Fin (h+1) → ℕ), Valid r D ∧ (∀i,out i<r+2+D.size) ∧
    PEqualNP.NotBracket.notCount D≤b ∧ D.size-PEqualNP.NotBracket.notCount D≤p ∧
    ∀ i Y,Y ⊆ Finset.range r → Near a f (W i) Y → ∀j,
      (D.wires (input r (Y∩V))).getD (out j) false = decide (i=j)
def block (W : Fin (h+1) → Finset ℕ) (V : Finset ℕ) (i : Fin h) := (W i.succ \ W i.castSucc) ∩ V

theorem necessity {W : Fin (h+1) → Finset ℕ} (inside : ∀i,W i⊆Finset.range r) (mon : Monotone W)
    (fit : Fit W r a f b p V) : h+1≤2^b ∧ ∀i, a+f+1≤(block W V i).card := by
  classical
  obtain ⟨D,out,valid,_,negs,_,eval⟩ := fit
  obtain ⟨rank,mono,room,stable⟩ := MarkedInversionRank.circuit_rank (n:=r) D valid.1
  let v (i : Fin (h+1)) (j : Fin r) := decide (j.val∈W i∩V)
  have vm : Monotone v := by
    intro i k hik j
    apply Bool.le_iff_imp.mpr
    simp only [v,decide_eq_true_eq,Finset.mem_inter]
    exact fun ⟨hw,hv⟩ => ⟨mon hik hw,hv⟩
  have step : StrictMono (fun i => rank (v i)) := by
    intro i k lt
    refine lt_of_le_of_ne (mono (vm lt.le)) ?_
    intro eq
    have left := eval i (W i) (inside i) (by simp [Near]) i
    have right := eval k (W k) (inside k) (by simp [Near]) i
    have falls := stable _ _ (vm lt.le) eq (out i) (by simpa [input,v] using left)
    change (D.wires (input r (W k∩V))).getD (out i) false=true at falls
    exact lt.ne.symm (of_decide_eq_true (right.symm.trans falls))
  constructor
  · let embed (i : Fin (h+1)) : Fin (2^b) := ⟨rank (v i),(room _).trans_le (Nat.pow_le_pow_right (by decide) negs)⟩
    simpa using Fintype.card_le_of_injective embed (fun i j eq => step.injective (congrArg Fin.val eq))
  · intro i
    by_contra! small
    let A := W i.castSucc
    let B := W i.succ
    let Δ := block W V i
    have ab : A⊆B := mon (Fin.castSucc_le_succ i)
    obtain ⟨E,sub,sz⟩ := Finset.exists_subset_card_eq (s:=Δ) (min_le_right f Δ.card)
    let Y := A∪E
    let Z := B\(Δ\E)
    have dB : Δ⊆B := by intro x hx; exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
    have yInside : Y⊆Finset.range r := Finset.union_subset (inside _) (sub.trans (dB.trans (inside _)))
    have zInside : Z⊆Finset.range r := Finset.sdiff_subset.trans (inside _)
    have yn : Near a f A Y := by
      constructor
      · rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_union_left (s₂:=E))]; simp
      · have subE : Y\A⊆E := by intro x hx; simp_all [Y,Finset.mem_sdiff,Finset.mem_union]
        exact (Finset.card_le_card subE).trans (sz ▸ min_le_left ..)
    have zn : Near a f B Z := by
      constructor
      · have subD : B\Z ⊆ Δ\E := by intro x hx; simp_all [Z,Finset.mem_sdiff]
        have bound := Finset.card_le_card subD
        rw [Finset.card_sdiff_of_subset sub,sz] at bound
        change Δ.card<a+f+1 at small
        omega
      · simp [Z]
    have same : Y∩V=Z∩V := by
      ext w
      have e : w∈E → w∈Δ := fun m => sub m
      have inc : w∈A → w∈B := fun m => ab m
      change w∈(A∪E)∩V ↔ w∈(B\(((B\A)∩V)\E))∩V
      change w∈E → w∈(B\A)∩V at e
      simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_union] at *
      grind
    have lhs := eval i.castSucc Y yInside yn i.castSucc
    have rhs := eval i.succ Z zInside zn i.castSucc
    rw [same] at lhs
    have sameIdx : i.succ=i.castSucc := of_decide_eq_true (rhs.symm.trans (by simpa using lhs))
    have bad := congrArg Fin.val sameIdx
    simp at bad
end PEqualNP.Outside.L_lib_1420_aux.Noisy

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy
open PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates FiniteGateBank
open scoped Classical
variable {X : Type} {src : X → List Bool} {n : ℕ}

theorem gate (width : ∀ x, (src x).length=n) (p : Net n) {F G : X → Prop}
    (f : Has p src F) (g : Has p src G) (op : Bool) :
    ∃ q, Grow src p q 1 0 ∧ Has q src (fun x => if op then F x ∧ G x else F x ∨ G x) := by
  obtain ⟨q,gq,hh⟩ := binary width p _ _ f g op
  refine ⟨q,gq,?_⟩
  unfold Has
  convert hh using 2
  apply Bool.eq_iff_iff.mpr
  cases op <;> simp [bit]

def test (mode : Bool) (s Y : Finset ℕ) (j : ℕ) : Prop :=
  if mode then (s\Y).card≤j else j<(s∩Y).card

theorem testStep (mode : Bool) {s : Finset ℕ} {a : ℕ} (fresh : a∉s) (Y : Finset ℕ) (j : ℕ) :
    test mode (insert a s) Y j ↔
      let first := if mode then a∈Y ∧ test mode s Y j else a∈Y ∨ test mode s Y j
      if j=0 then first else if !mode then first ∧ test mode s Y (j-1) else first ∨ test mode s Y (j-1) := by
  have f₁ : a∉s∩Y := fun h => fresh (Finset.mem_inter.mp h).1
  have f₂ : a∉s\Y := fun h => fresh (Finset.mem_sdiff.mp h).1
  by_cases y : a∈Y <;> by_cases z : j=0 <;> cases mode <;>
    simp [test,y,z,Finset.insert_sdiff_of_mem,Finset.insert_sdiff_of_notMem,
      Finset.insert_inter_of_mem,Finset.insert_inter_of_notMem,f₁,f₂] <;> omega

theorem countBank (width : ∀ x, (src x).length=n) (obs : X → Finset ℕ) (mode : Bool)
    (s : Finset ℕ) (t : ℕ) (p : Net n) (zero : p.has src (fun _ => false))
    (one : p.has src (fun _ => true)) (single : ∀ a∈s,Has p src (fun x => a∈obs x)) :
    ∃ q, Grow src p q (s.card*((t+1)*2)) 0 ∧
      ∀ j : Fin (t+1),Has q src (fun x => test mode s (obs x) j.val) := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty =>
    refine ⟨p,by simpa using start src p,?_⟩
    intro j
    cases mode
    · unfold Has
      convert zero using 2
      simp [test,bit]
    · unfold Has
      convert one using 2
      simp [test,bit]
  | @insert a s ha ih =>
    obtain ⟨q,g,counts⟩ := ih p zero one (fun a m => single a (Finset.mem_insert_of_mem m))
    let pred := fun (j : Fin (t+1)) (x : X) => test mode (insert a s) (obs x) j.val
    obtain ⟨v,gv,terms⟩ := batchPred (p:=q) Finset.univ pred 2 (by
      intro j _ v old
      have hit := old _ (g.1 _ (single a (Finset.mem_insert_self ..)))
      obtain ⟨u,gu,first⟩ := gate width v hit (old _ (counts j)) mode
      by_cases z : j.val=0
      · refine ⟨u,allowance gu (by decide),hasCong ?_ first⟩
        intro x
        simpa only [pred,testStep mode ha (obs x) j.val,z,ite_true]
      · let k : Fin (t+1) := ⟨j.val-1,by omega⟩
        obtain ⟨w,gw,both⟩ := gate width u first (gu.1 _ (old _ (counts k))) (!mode)
        refine ⟨w,by simpa using chain gu gw,hasCong ?_ both⟩
        intro x
        simp only [pred,testStep mode ha (obs x) j.val,z,ite_false,k])
    exact ⟨v,by simpa [ha,Nat.succ_mul] using chain g gv,fun j => terms j (Finset.mem_univ _)⟩
end PEqualNP.Outside.L_lib_1420_aux.Noisy

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy
open scoped Classical
theorem thin {W : Fin (h+1) → Finset ℕ} (mon : Monotone W)
    (bound : ∀i,w ≤ (block W V i).card) :
    ∃ B : Fin h → Finset ℕ, (∀i,B i⊆block W V i ∧ (B i).card=w) ∧
      Finset.univ.biUnion B ⊆ V ∧ (Finset.univ.biUnion B).card=h*w := by
  classical
  choose B sub sz using fun i => Finset.exists_subset_card_eq (bound i)
  have dis (i j : Fin h) (lt : i<j) : Disjoint (B i) (B j) := by
    apply Finset.disjoint_left.mpr
    intro x hi hj
    have left := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (sub i hi)).1).1
    have right := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (sub j hj)).1).2
    exact right (mon (show i.succ ≤ j.castSucc from lt) left)
  refine ⟨B,fun i => ⟨sub i,sz i⟩,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp (sub i hi)).2
  · rw [Finset.card_biUnion]
    · simp [sz]
    · intro i _ j _ ne
      rcases lt_or_gt_of_ne ne with le|le
      · exact dis _ _ le
      · exact (dis _ _ le).symm

theorem markSpec {W : Fin (h+1) → Finset ℕ} (mon : Monotone W) {i : Fin h}
    {B Z Y : Finset ℕ} (inBlock : B ⊆ W i.succ \ W i.castSucc) (seen : B ⊆ Z)
    (sz : B.card=a+f+1) (idx : Fin (h+1)) (near : Near a f (W idx) Y) :
    test (decide (a ≤ f)) B (Y∩Z) (min a f) ↔ i.val+1 ≤ idx.val := by
  have balance := Finset.card_sdiff_add_card_inter B (Y∩Z)
  obtain ⟨loss,gain⟩ := near
  by_cases after : i.val+1 ≤ idx.val
  · have sub : B\(Y∩Z) ⊆ W idx\Y := by
      intro x hx
      obtain ⟨inB,notObs⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨mon (show i.succ ≤ idx from after) (Finset.mem_sdiff.mp (inBlock inB)).1,
        fun hit => notObs (Finset.mem_inter.mpr ⟨hit,seen inB⟩)⟩
    have := (Finset.card_le_card sub).trans loss
    by_cases which : a ≤ f <;> simp [test,which,after,min_eq_left,min_eq_right] <;> omega
  · have sub : B∩(Y∩Z) ⊆ Y\W idx := by
      intro x hx
      obtain ⟨inB,obs⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp obs).1,fun hx =>
        (Finset.mem_sdiff.mp (inBlock inB)).2 (mon (show idx ≤ i.castSucc by change idx.val ≤ i.val; omega) hx)⟩
    have := (Finset.card_le_card sub).trans gain
    by_cases which : a ≤ f <;> simp [test,which,after,min_eq_left,min_eq_right] <;> omega
end PEqualNP.Outside.L_lib_1420_aux.Noisy

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates FiniteGateBank OrderedThresholdBank
open scoped Classical
abbrev Obs (W : Fin (h+1) → Finset ℕ) (r a f : ℕ) :=
  {x : Fin (h+1) × Finset ℕ // x.2⊆Finset.range r ∧ Near a f (W x.1) x.2}
def budget (h a f : ℕ) := 16*(h+1)*((a+f+1)*(min a f+1)+1)

theorem build {W : Fin (h+1) → Finset ℕ} (inside : ∀i,W i⊆Finset.range r) (mon : Monotone W)
    (room : h+1 ≤ 2^b) (B : Fin h → Finset ℕ)
    (sub : ∀i,B i⊆W i.succ\W i.castSucc) (visible : ∀i,B i⊆Z)
    (size : ∀i,(B i).card=a+f+1) : Fit W r a f b (budget h a f) Z := by
  classical
  let X := Obs W r a f
  let obs (x : X) := x.val.2∩Z
  let src (x : X) := input r (obs x)
  let index (x : X) := x.val.1.val
  let startNet := empty (r+2)
  have width (x : X) : (src x).length=r+2 := by simp [src,input]
  have zero : startNet.has src (fun _ => false) := ⟨r,by simp [startNet,empty,gates_mk],by
    intro x; simp [startNet,empty,gates_mk,PulseList.run,src,input,List.getD_eq_getElem?_getD]⟩
  have one : startNet.has src (fun _ => true) := ⟨r+1,by simp [startNet,empty,gates_mk],by
    intro x; simp [startNet,empty,gates_mk,PulseList.run,src,input,List.getD_eq_getElem?_getD]⟩
  have wire (k : ℕ) (small : k<r) : Has startNet src (fun x => k∈obs x) := by
    refine ⟨k,by simp [startNet,empty,gates_mk]; omega,?_⟩
    intro x
    simp [startNet,empty,gates_mk,PulseList.run,src,input,bit,List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show k < (List.ofFn (fun j : Fin r => decide (j.val∈obs x))).length by simpa using small),small]
  let unit := (a+f+1)*((min a f+1)*2)
  let pred := fun (i : Fin h) (x : X) => i.val+1 ≤ index x
  obtain ⟨q,g,marks⟩ := batchPred (p:=startNet) Finset.univ pred unit (by
    intro i _ v keep
    obtain ⟨w,gw,hits⟩ := countBank width obs (decide (a ≤ f)) (B i) (min a f) v (keep _ zero) (keep _ one)
      (fun j hj => keep _ (wire j (Finset.mem_range.mp (inside _ (Finset.mem_sdiff.mp (sub i hj)).1))))
    refine ⟨w,by simpa [size,unit] using gw,hasCong ?_ (hits ⟨min a f,by omega⟩)⟩
    intro x
    exact markSpec mon (sub i) (visible i) (size i) x.val.1 x.property.2)
  have eqH (i) : high index i=bit (fun x => i ≤ index x) := by funext x; apply Bool.eq_iff_iff.mpr; simp [high,bit]
  have eqL (i) : low index i=bit (fun x => index x < i) := by funext x; apply Bool.eq_iff_iff.mpr; simp [low,bit]
  have highWire (i : ℕ) (pos : 0 < i) (le : i ≤ h) : q.has src (high index i) := by
    let j : Fin h := ⟨i-1,by omega⟩
    have old := marks j (Finset.mem_univ _)
    have back : j.val+1=i := by dsimp [j]; omega
    simpa only [Has,pred,back,eqH] using old
  obtain ⟨v,gv,lows⟩ := decode src width b h room index (fun x => Nat.le_of_lt_succ x.val.1.isLt) q (g.1 _ zero) highWire
  let answer (j : Fin (h+1)) (x : X) := x.val.1=j
  obtain ⟨w,gw,outs⟩ := batchPred (p:=v) Finset.univ answer 1 (by
    intro j _ z keep
    have left : Has z src (fun x => j.val ≤ index x) := by
      by_cases pos : 0 < j.val
      · have old := keep _ (gv.1 _ (highWire j.val pos (by omega)))
        simpa only [Has,eqH] using old
      · have val : j.val=0 := by omega
        have old := keep _ (gv.1 _ (g.1 _ one))
        unfold Has
        convert old using 2
        simp [bit,val]
    have right : Has z src (fun x => index x<j.val+1) := by
      by_cases lt : j.val<h
      · have old := keep _ (lows (j.val+1) (by omega) (by omega))
        simpa only [Has,eqL] using old
      · have old := keep _ (gv.1 _ (g.1 _ one))
        unfold Has
        convert old using 2 with x
        have le : index x<j.val+1 := by have := x.val.1.isLt; dsimp [index]; omega
        simp [bit,le]
    obtain ⟨z',gz,both⟩ := gate width z left right true
    refine ⟨z',gz,hasCong ?_ both⟩
    intro x
    simp only [ite_true,answer,index,Fin.ext_iff]
    omega)
  have grow := chain (chain g gv) gw
  choose out bounds reads using fun j => outs j (Finset.mem_univ _)
  have cost : PEqualNP.NotBracket.notCount ⟨w.gates,0⟩=b := by
    simpa [Net.cost,startNet,empty,gates_mk,PEqualNP.NotBracket.notCount] using grow.2.2
  refine ⟨⟨w.gates,0⟩,out,⟨w.fan,w.readsBack,by simp [Circuit.size]⟩,bounds,cost.le,?_,?_⟩
  · change w.gates.length-_ ≤ _
    rw [cost]
    have n := grow.2.1
    simp only [startNet,empty,gates_mk,List.length_nil,zero_add,Finset.card_univ,Fintype.card_fin,Nat.mul_one] at n
    dsimp [budget,unit] at n ⊢
    apply Nat.sub_le_of_le_add
    exact n.trans (by ring_nf; omega)
  · intro i Y y hy j
    let x : X := ⟨(i,Y),y,hy⟩
    change (PulseList.run w.gates (src x)).getD (out j) false=decide (i=j)
    rw [reads j x]
    simp [bit,answer,x]
end PEqualNP.Outside.L_lib_1420_aux.Noisy

namespace PEqualNP.Outside.L_lib_1420_aux.Noisy
noncomputable def truth (P : Prop) := @decide P (Classical.propDecidable P)
theorem normTruth (P : Prop) (d : Decidable P) : @decide P d = truth P := by
  unfold truth
  congr 1
def difference (A B : Finset Nat) := A \ B
theorem normDiff (d : DecidableEq Nat) (A B : Finset Nat) :
    @SDiff.sdiff _ (@Finset.instSDiff Nat d) A B = difference A B := by
  rw [Subsingleton.elim d instDecidableEqNat]
  rfl
def common (A B : Finset Nat) := A ∩ B
theorem normInter (d : DecidableEq Nat) (A B : Finset Nat) :
    @Min.min _ (@Finset.instMin Nat d) A B = common A B := by
  rw [Subsingleton.elim d instDecidableEqNat]
  rfl
end PEqualNP.Outside.L_lib_1420_aux.Noisy

namespace PEqualNP.Outside.L_lib_1420_aux.Boxes

open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket (notCount)

noncomputable def conj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d && g d
noncomputable def disj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d || g d
noncomputable def inv {α : Type*} (f : α → Bool) : α → Bool := fun d => !(f d)

def WVal {α : Type*} (x : α → List Bool) (gs : List Gate) (p : Nat) : α → Bool :=
  fun d => ((Circuit.mk gs 0).wires (x d)).getD p false

noncomputable def Built {α : Type*} (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool)) : Prop :=
  (∀ d, (x d).length = N) ∧ ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack N ⟨gs,0⟩ ∧
    gs.length - notCount ⟨gs,0⟩ ≤ p ∧ notCount ⟨gs,0⟩ ≤ b ∧
    ∀ f ∈ S, ∃ i < N+gs.length, WVal x gs i = f

private theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

private theorem old {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) {i} (hi : i < N+gs.length) :
    WVal x (gs++[g]) i = WVal x gs i := by
  funext d
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD i false = _
  exact List.getD_append _ _ _ _ (by omega)

private theorem fresh {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) (d : α) :
    WVal x (gs++[g]) (N+gs.length) d = g.op.eval (g.inputs.map fun i => WVal x gs i d) := by
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD (N+gs.length) false = _
  rw [← len, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private theorem extendBack {N : Nat} (gs : List Gate) (g : Gate) (h : ReadsBack N ⟨gs,0⟩)
    (ok : ∀ i ∈ g.inputs, i < N+gs.length) : ReadsBack N ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

section Compiler
variable {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}

theorem Built.start (hlen : ∀ d, (x d).length = N) :
    Built x N 0 0 {f | ∃ i < N, f = fun d => (x d).getD i false} := by
  refine ⟨hlen, [], by simp [FanInTwo], by simp [ReadsBack], by simp, by simp [notCount], ?_⟩
  rintro f ⟨i, hi, rfl⟩
  exact ⟨i, by simpa using hi, rfl⟩

theorem Built.relax {P B : Nat} {T : Set (α → Bool)} (H : Built x N p b S)
    (hp : p ≤ P) (hb : b ≤ B) (hst : T ⊆ S) : Built x N P B T := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  exact ⟨hlen, gs, fan, back, pc.trans hp, nc.trans hb, fun u hu => sig u (hst hu)⟩

private theorem Built.push (H : Built x N p b S) (op : GateOp) (arity : Nat)
    (allowed : op = .and ∨ op = .or ∨ op = .not) (ha : arity ≤ 2)
    (fs : List (α → Bool)) (hfs : fs.length = arity) (hf : ∀ f ∈ fs, f ∈ S) :
    Built x N (p + if op = .not then 0 else 1) (b + if op = .not then 1 else 0)
      (insert (fun d => op.eval (fs.map fun f => f d)) S) := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  have choose (f : α → Bool) (h : f ∈ fs) := sig f (hf f h)
  let is := fs.attach.map (fun f => (choose f.val f.property).choose)
  let g : Gate := ⟨op, is⟩
  have hcount : notCount ⟨gs++[g],0⟩ = notCount ⟨gs,0⟩ + (if op = .not then 1 else 0) := by
    by_cases h : op = .not <;> simp [notCount, List.filter_append, g, h]
  have hnc : notCount ⟨gs,0⟩ ≤ gs.length := List.length_filter_le _ _
  refine ⟨hlen, gs++[g], ?_, ?_, ?_, by rw [hcount]; exact Nat.add_le_add_right nc _, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact fan j hj
    · obtain rfl := List.mem_singleton.mp hj
      exact ⟨allowed, by simpa [g, is, hfs] using ha⟩
  · apply extendBack _ _ back
    intro i hi
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hi
    exact (choose f.val f.property).choose_spec.1
  · rw [hcount]
    simp only [List.length_append, List.length_singleton]
    split <;> omega
  · intro f hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · refine ⟨N+gs.length, by simp, ?_⟩
      funext d
      rw [fresh _ hlen]
      congr 1
      change is.map (fun i => WVal x gs i d) = _
      simp only [is, List.map_map]
      calc
        _ = fs.attach.map (fun f => f.val d) := by
          apply List.map_congr_left
          intro f _
          exact congrFun (choose f.val f.property).choose_spec.2 d
        _ = _ := List.attach_map_val (f := fun f : α → Bool => f d)
    · obtain ⟨i, hi, he⟩ := sig f hm
      exact ⟨i, by simp; omega, (old x hlen gs g hi).trans he⟩

theorem Built.andGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (conj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d && g d) S)
  simpa [GateOp.eval] using H.push .and 2 (Or.inl rfl) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.orGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (disj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d || g d) S)
  simpa [GateOp.eval] using H.push .or 2 (Or.inr (Or.inl rfl)) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.notGate {f : α → Bool} (H : Built x N p b S) (hf : f ∈ S) :
    Built x N p (b+1) (insert (inv f) S) := by
  change Built x N p (b+1) (insert (fun d => !f d) S)
  simpa [GateOp.eval] using H.push .not 1 (Or.inr (Or.inr rfl)) (by decide) [f] rfl (by simpa)

theorem boolOfIff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  cases hP : decide P <;> cases hQ : decide Q <;> simp_all

noncomputable def Grow (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool))
    (c : Nat) (f : α → Bool) := ∃ T, Built x N (p+c) b T ∧ S ⊆ T ∧ f ∈ T

theorem batch {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (c : Nat) (H : Built x N p b S)
    (make : ∀ {P T}, Built x N P b T → S ⊆ T → ∀ a ∈ s, Grow x N P b T c (F a)) :
    ∃ T, Built x N (p+s.card*c) b T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fr ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fr,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

end Compiler

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not
private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1], ?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD, ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none noneX, List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases g.inputs with
  | nil => simp
  | cons i _ => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i, here, rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.any_eq_true] at on ⊢
  obtain ⟨v, hm, active⟩ := on
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact ⟨_, List.mem_map.mpr ⟨i, here, rfl⟩, (bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1], if inverting g then 2 * s.2 + (firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance, neg, ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance, neg] using strict
    exact ⟨increase.le, fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega, ?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit, op, GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gs : List Gate) : ℕ := (gs.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting, h]

private theorem run_consistent (gs : List Gate) (allowed : ∀ g ∈ gs, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gs.foldl advance s) (gs.foldl advance t) := by
  induction gs generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gs : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2 ^ d) :
    (gs.foldl advance s).2 < 2 ^ (d + negCount gs) := by
  induction gs generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2 ^ (d + 1) := by
        simp only [advance, neg, ite_true, Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d + 1) raises
      simpa [negCount, neg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2 ^ d := by simpa [advance, neg] using bound
      simpa [negCount, neg] using ih (advance s g) d same

private theorem run_wires (gs : List Gate) (s : List Bool × ℕ) :
    (gs.foldl advance s).1 = gs.foldl gateStep s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private def grade (C : Circuit) (x : List Bool) : ℕ := (C.gates.foldl advance (x, 0)).2

private theorem grade_bound (C : Circuit) (x : List Bool) : grade C x < 2 ^ (notCount C) := by
  simpa [grade, negCount_spec] using run_bounded C.gates (x, 0) 0 (by change 0 < (1 : ℕ); decide)
private theorem grade_order {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i, (C.wires x).getD i false ≤ (C.wires y).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (x, 0) (y, 0) := ⟨le_rfl, fun _ => xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1, ?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires, run_wires] at order
  exact order

noncomputable def bits {r : Nat} (X : Finset (Fin r)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun j : Fin r => decide (j ∈ X))

noncomputable def labelBit {m : Nat} (i j : Fin m) : Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  decide (i=j)

def Near {r : Nat} (a f : Nat) (C Y : Finset (Fin r)) : Prop :=
  (C \ Y).card ≤ a ∧ (Y \ C).card ≤ f

def Label {r m : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (Y : Finset (Fin r)) (i : Fin m) : Prop :=
  ∃ C : Finset (Fin r), (Finset.univ \ C) ⊆ Z i ∧ C ⊆ O i ∧ Near (a i) (f i) C Y

def Valid (n : Nat) (D : Circuit) : Prop :=
  FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size

noncomputable def Possible {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) : Prop :=
  ∃ (D : Circuit) (out : Fin m → Nat), Valid r D ∧
    (∀ j, out j < r+2+D.size) ∧ notCount D ≤ b ∧
    ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = labelBit i j

def Adj {m l : Nat} (w : Fin l → Fin m) : Prop :=
  ∀ i j : Fin l, i.val + 1 = j.val → w i ≠ w j

def WordTrace {r m l : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r))
    (w : Fin l → Fin m) : Prop :=
  ∃ Y : Fin l → Finset (Fin r), Monotone Y ∧ (∀ i, Y i ⊆ T) ∧ ∀ i, lab (Y i) (w i)

def Trace {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (l : Nat) : Prop :=
  ∃ w : Fin l → Fin m, Adj w ∧ WordTrace lab T w

def Bucket {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (k : Nat)
    (j : Fin m) : Prop :=
  ∃ w : Fin (k+1) → Fin m, Adj w ∧ WordTrace lab T w ∧ w (Fin.last k) = j

private theorem bits_getD {r : Nat} (Y : Finset (Fin r)) (j : Fin r) :
    (bits Y).getD j.val false = decide (j ∈ Y) := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  first | rfl | exact Bool.eq_iff_iff.mpr (by simp)

private theorem bits_order {r : Nat} {Y T : Finset (Fin r)} (h : Y ⊆ T) :
    bitOrder (bits Y ++ [false,true]) (bits T ++ [false,true]) := by
  refine ⟨by simp [bits], fun q => ?_⟩
  by_cases hq : q < r
  · rw [List.getD_append _ _ _ _ (by simpa [bits] using hq),
      List.getD_append _ _ _ _ (by simpa [bits] using hq)]
    change (bits Y).getD (⟨q,hq⟩ : Fin r).val false ≤ (bits T).getD (⟨q,hq⟩ : Fin r).val false
    rw [bits_getD, bits_getD, bool_order]
    simpa using (fun hm : (⟨q,hq⟩ : Fin r) ∈ Y => h hm)
  · rw [List.getD_append_right _ _ _ _ (by simpa [bits] using Nat.le_of_not_gt hq),
      List.getD_append_right _ _ _ _ (by simpa [bits] using Nat.le_of_not_gt hq)]
    simp [bits]

private theorem index_le_of_steps {l : Nat} (v : Fin l → Nat)
    (step : ∀ i j : Fin l, i.val + 1 = j.val → v i < v j) (i : Fin l) : i.val ≤ v i := by
  have aux (j : Nat) : ∀ h : j < l, j ≤ v ⟨j,h⟩ := by
    induction j with
    | zero => simp
    | succ j ih =>
      intro h
      have hj : j < l := by omega
      have sv := step ⟨j,hj⟩ ⟨j+1,h⟩ rfl
      have iv := ih hj
      change v ⟨j,hj⟩ < v ⟨j+1,h⟩ at sv
      omega
  exact aux i.val i.isLt

private theorem possible_no_trace {r m b : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    (h : Possible b lab) : ¬ Trace lab Finset.univ (min (2^b) (r+1)+1) := by
  obtain ⟨D,out,valid,_,budget,fit⟩ := h
  rintro ⟨w,adj,Y,mono,_,ok⟩
  let l := min (2^b) (r+1)+1
  have last : l-1 < l := by dsimp [l]; omega
  let lastI : Fin l := ⟨l-1,last⟩
  have step (i j : Fin l) (hj : i.val+1=j.val) :
      grade D (bits (Y i) ++ [false,true]) < grade D (bits (Y j) ++ [false,true]) := by
    have sub := mono (show i ≤ j by exact Fin.le_iff_val_le_val.mpr (by omega))
    have ord := grade_order valid.1 (bits_order sub)
    apply lt_of_le_of_ne ord.1
    intro eq
    have hn := adj i j hj
    have bad := ord.2 eq (out (w i))
    rw [fit _ _ (ok i) _, fit _ _ (ok j) _] at bad
    simp [labelBit, Ne.symm hn] at bad
    exact (by decide : ¬((true : Bool) ≤ false)) bad
  have hpow := index_le_of_steps (fun i => grade D (bits (Y i) ++ [false,true])) step lastI
  have hb := (grade_bound D (bits (Y lastI) ++ [false,true])).trans_le (Nat.pow_le_pow_right (by decide) budget)
  have szstep (i j : Fin l) (hj : i.val+1=j.val) : (Y i).card < (Y j).card := by
    apply Finset.card_lt_card
    have sub := mono (show i ≤ j by exact Fin.le_iff_val_le_val.mpr (by omega))
    apply lt_of_le_of_ne sub
    intro eq
    have hs := step i j hj
    rw [eq] at hs
    exact (Nat.lt_irrefl _ hs)
  have hsz := index_le_of_steps (fun i => (Y i).card) szstep lastI
  have hcard : (Y lastI).card ≤ r := by
    simpa using (Y lastI).card_le_univ
  change min (2^b) (r+1) ≤ _ at hpow hsz
  omega

private theorem trace_mono {r m l : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T U : Finset (Fin r)} (sub : T ⊆ U) : Trace lab T l → Trace lab U l := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  exact ⟨w,adj,Y,mono,fun i => (top i).trans sub,ok⟩

private theorem trace_prefix {r m i j : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T : Finset (Fin r)} (le : i ≤ j) : Trace lab T j → Trace lab T i := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  refine ⟨w ∘ Fin.castLE le, fun a b h => adj _ _ h,
    Y ∘ Fin.castLE le, fun a b h => mono h, fun a => top _, fun a => ok _⟩

private theorem trace_one {r m : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i : Fin m} (h : lab X i) : Trace lab X 1 := by
  refine ⟨fun _ => i, fun j k adj => ?_, fun _ => X, fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ => h⟩
  have hj := j.isLt
  have hk := k.isLt
  omega

private theorem trace_extend {r m k : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (diff : j ≠ i) (hi : lab X i) (h : Bucket lab X k j) :
    Trace lab X (k+2) := by
  obtain ⟨w,adj,⟨Y,mono,top,ok⟩,last⟩ := h
  let w' : Fin (k+2) → Fin m := Fin.lastCases i w
  let Y' : Fin (k+2) → Finset (Fin r) := Fin.lastCases X Y
  refine ⟨w', ?_, Y', ?_, ?_, ?_⟩
  · intro a b step
    revert step
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro step
      have hb := b.isLt
      change k+1+1 = b.val at step
      omega
    · refine Fin.lastCases ?_ (fun b step => ?_) b
      · intro step
        have ha : a = Fin.last k := Fin.ext (by change a.val+1 = k+1 at step; exact Nat.add_right_cancel step)
        simpa [w', ha, last] using diff
      · simpa [w'] using adj a b step
  · intro a b le
    revert le
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro le
      have hb : b = Fin.last (k+1) := le_antisymm (Fin.le_last b) le
      simp [hb]
    · refine Fin.lastCases ?_ (fun b le => ?_) b
      · intro _; simpa [Y'] using top a
      · simpa [Y'] using mono (show a ≤ b from le)
  · intro a; exact Fin.lastCases (by simp [Y']) (fun a => by simpa [Y'] using top a) a
  · intro a; exact Fin.lastCases (by simpa [Y',w'] using hi) (fun a => by simpa [Y',w'] using ok a) a

noncomputable def rank {r m : Nat} (K : Nat) (lab : Finset (Fin r) → Fin m → Prop)
    (X : Finset (Fin r)) : Nat := ((Finset.range K).filter (fun k => Trace lab X (k+1))).sup id

private theorem rank_lt {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hk : 0 < K) : rank K lab X < K := by
  have h : rank K lab X ≤ K-1 := Finset.sup_le (fun i hi => by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    dsimp; omega)
  omega

private theorem le_rank_iff {r m K i : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hi : i < K) : i ≤ rank K lab X ↔ i = 0 ∨ Trace lab X (i+1) := by
  by_cases iz : i = 0
  · simp [iz]
  constructor
  · intro h
    right
    by_contra no
    have small : rank K lab X ≤ i-1 := Finset.sup_le (fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).2
      change j ≤ i-1
      by_contra hn
      exact no (trace_prefix (by omega) hj'))
    omega
  · rintro (h | h)
    · exact (iz h).elim
    · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,h⟩)

private theorem correct_bucket {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (hK : 0 < K) (hi : lab X i)
    (good : ¬ Trace lab Finset.univ (K+1)) : Bucket lab X (rank K lab X) j ↔ i = j := by
  let u := rank K lab X
  have ltK : u < K := rank_lt hK
  constructor
  · intro buck
    by_contra diff
    have ext := trace_extend (Ne.symm diff) hi buck
    change Trace lab X (u+2) at ext
    by_cases top : u+1 = K
    · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
    · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
      change u+1 ≤ u at lev
      omega
  · rintro rfl
    have existsTrace : Trace lab X (u+1) := by
      rcases (le_rank_iff (lab := lab) (X := X) ltK).mp (le_refl u) with z | yes
      · simpa [z] using trace_one hi
      · exact yes
    obtain ⟨w,adj,tr⟩ := existsTrace
    let j := w (Fin.last u)
    have buck : Bucket lab X u j := ⟨w,adj,tr,rfl⟩
    have eq : i = j := by
      by_contra diff
      have ext := trace_extend (Ne.symm diff) hi buck
      change Trace lab X (u+2) at ext
      by_cases top : u+1 = K
      · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
      · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
        change u+1 ≤ u at lev
        omega
    exact eq ▸ buck

namespace RankDecoder

private theorem one {α : Type*} {x : α → List Bool} {N p nb b : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hR : ∀ d, R d < 1) :
    ∃ T, Built x N (p + 16 * (1 + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < 1 → (fun d => decide (R d = i)) ∈ T := by
  refine ⟨S, H.relax (by omega) (by omega) (fun _ h => h), fun _ h => h, ?_⟩
  intro i hi
  have eq : (fun d => decide (R d = i)) = (fun _ => true) := by
    funext d
    have : R d = i := by have := hR d; omega
    simp [this]
  rw [eq]
  exact ht

theorem decode {α : Type*} {x : α → List Bool} {N p nb b K : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (hR : ∀ d, R d < K) (hK : 0 < K) (hpow : K ≤ 2^b)
    (threshold : ∀ i : Nat, i < K → (fun d => decide (i ≤ R d)) ∈ S) :
    ∃ T, Built x N (p + 16 * (K + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < K → (fun d => decide (R d = i)) ∈ T := by
  classical
  induction b generalizing p nb K S R with
  | zero =>
    have : K = 1 := by simp at hpow; omega
    subst K
    exact one H ht hR
  | succ b ih =>
    by_cases small : K = 1
    · subst K
      exact one H ht hR
    let h := (K + 1) / 2
    have hh : 0 < h := by dsimp [h]; omega
    have hlt : h < K := by dsimp [h]; omega
    have hsplit : K ≤ 2 * h := by dsimp [h]; omega
    have hhpow : h ≤ 2^b := by rw [pow_succ] at hpow; dsimp [h]; omega
    let U : Nat → α → Bool := fun i d => decide (i ≤ R d)
    let Q : α → Nat := fun d => if R d < h then R d else R d - h
    have qbound (d : α) : Q d < h := by
      have hd := hR d
      dsimp [Q]
      split <;> omega
    have uget (i : Nat) : U i ∈ S := by
      by_cases hi : i < K
      · exact threshold i hi
      · have eq : U i = (fun _ => false) := by
          funext d
          have hn : ¬ i ≤ R d := by have := hR d; omega
          simp [U, hn]
        rw [eq]
        exact hf
    let S₀ := insert (inv (U h)) S
    have H₀ : Built x N p (nb + 1) S₀ := H.notGate (uget h)
    have s₀ : S ⊆ S₀ := Set.subset_insert _ _
    have lower₀ : inv (U h) ∈ S₀ := Set.mem_insert _ _
    have foldStep {P : Nat} {V : Set (α → Bool)} (HV : Built x N P (nb + 1) V)
        (sV : S₀ ⊆ V) (i : Nat) (_ : i ∈ Finset.range h) :
        Grow x N P (nb + 1) V 2 (fun d => decide (i ≤ Q d)) := by
      let g := disj (inv (U h)) (U (h + i))
      have Hg : Built x N (P + 1) (nb + 1) (insert g V) :=
        HV.orGate (sV lower₀) (sV (s₀ (uget (h + i))))
      have vsub : V ⊆ insert g V := Set.subset_insert _ _
      have Hf := Hg.andGate (vsub (sV (s₀ (uget i)))) (Set.mem_insert g V)
      have f_eq : conj (U i) g = (fun d => decide (i ≤ Q d)) := by
        funext d
        by_cases hd : R d < h
        · have hn : ¬ h ≤ R d := by omega
          simp [conj, g, disj, inv, U, Q, hd, hn]
        · have hu : h ≤ R d := by omega
          have ieq : (h + i ≤ R d) ↔ (i ≤ R d - h) := by omega
          by_cases hi : i ≤ R d
          · simp [conj, g, disj, inv, U, Q, hd, hu, hi, ieq]
          · have hnot : ¬ i ≤ R d - h := by omega
            simp [conj, U, Q, hd, hi, hnot]
      refine ⟨_, Hf, vsub.trans (Set.subset_insert _ _), ?_⟩
      rw [← f_eq]
      exact Set.mem_insert _ _
    obtain ⟨A, HA, sA, getA⟩ := batch (Finset.range h)
      (fun i d => decide (i ≤ Q d)) 2 H₀ foldStep
    obtain ⟨C, HC, sC, getC⟩ := ih HA (sA (s₀ ht)) (sA (s₀ hf)) qbound hh hhpow
      (fun i hi => getA i (Finset.mem_range.mpr hi))
    have exactStep {P : Nat} {V : Set (α → Bool)}
        (HV : Built x N P (nb + 1 + b) V) (sV : C ⊆ V)
        (i : Nat) (hi : i ∈ Finset.range K) :
        Grow x N P (nb + 1 + b) V 1 (fun d => decide (R d = i)) := by
      have hiK := Finset.mem_range.mp hi
      let j := if i < h then i else i - h
      let flag := if i < h then inv (U h) else U h
      have hj : j < h := by dsimp [j]; split <;> omega
      have hflag : flag ∈ V := by
        by_cases il : i < h
        · simpa only [flag, if_pos il] using sV (sC (sA lower₀))
        · simpa only [flag, if_neg il] using sV (sC (sA (s₀ (uget h))))
      have HM := HV.andGate (sV (getC j hj)) hflag
      have eq : conj (fun d => decide (Q d = j)) flag = (fun d => decide (R d = i)) := by
        funext d
        by_cases il : i < h <;> by_cases dl : R d < h
        · have dn : ¬ h ≤ R d := by omega
          simp [conj, flag, inv, U, Q, j, il, dl, dn]
        · have du : h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, inv, U, il, du, ne]
        · have dn : ¬ h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, U, il, dn, ne]
        · have du : h ≤ R d := by omega
          have eq' : (R d - h = i - h) ↔ R d = i := by omega
          simp [conj, flag, U, Q, j, il, dl, du, eq']
      refine ⟨_, HM, Set.subset_insert _ _, ?_⟩
      rw [← eq]
      exact Set.mem_insert _ _
    obtain ⟨T, HT, sT, getT⟩ := batch (Finset.range K)
      (fun i d => decide (R d = i)) 1 HC exactStep
    refine ⟨T, HT.relax ?_ (by omega) (fun _ m => m),
      s₀.trans (sA.trans (sC.trans sT)), fun i hi => getT i (Finset.mem_range.mpr hi)⟩
    simp only [Finset.card_range, Nat.mul_one]
    have hs : (h + 1)^2 ≤ K^2 := by
      have le : h + 1 ≤ K := by omega
      simpa only [pow_two] using Nat.mul_le_mul le le
    nlinarith

end RankDecoder

namespace Tables

open scoped Classical

private abbrev State (l A F : Nat) := (Fin l → Fin (A+1)) × (Fin l → Fin (F+1))
private abbrev Keys (l A F : Nat) := Fin (l+1) × State l A F
private abbrev Rows (α : Type*) (l r : Nat) := α → Fin l → Finset (Fin r)

private def bit {r : Nat} (U : Finset (Fin r)) (j : Fin r) : Bool := decide (j ∈ U)
private def yBit {l : Nat} (t : Fin (l+1)) (i : Fin l) : Bool := decide (t.val ≤ i.val)
private def charge (u v : Bool) : Nat := if u && !v then 1 else 0

private def lower {U : Nat} (q : Fin (U+1)) (c : Nat) : Fin (U+1) :=
  ⟨q.val - c, (Nat.sub_le _ _).trans_lt q.isLt⟩

private def debit {l A F : Nat} (q : State l A F) (i : Fin l) (y c : Bool) : State l A F :=
  (Function.update q.1 i (lower (q.1 i) (charge c y)),
   Function.update q.2 i (lower (q.2 i) (charge y c)))

private def Pay {l A F : Nat} (q : State l A F) (i : Fin l) (y c : Bool) : Prop :=
  charge c y ≤ (q.1 i).val ∧ charge y c ≤ (q.2 i).val

private def Allowed {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (j : Fin r) (i : Fin l) (y c : Bool) (d : α) : Prop :=
  (if c then j ∈ O d i else j ∈ Z d i) ∧ (y = true → j ∈ T d)

private noncomputable def edge {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y : Bool)
    (V : State l A F → α → Bool) (q : State l A F) (c : Bool) : α → Bool :=
  if Pay q i y c then
    conj (if c then fun d => bit (O d i) j else fun d => bit (Z d i) j)
      (if y then conj (fun d => bit (T d) j) (V (debit q i y c)) else V (debit q i y c))
  else fun _ => false

private theorem edge_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y : Bool)
    (V : State l A F → α → Bool) (q : State l A F) (c : Bool) (d : α) :
    edge Z O T j i y V q c d = true ↔
      Pay q i y c ∧ Allowed Z O T j i y c d ∧ V (debit q i y c) d = true := by
  unfold edge
  split <;> rename_i h <;> cases y <;> cases c <;>
    simp [h, Allowed, conj, bit, and_assoc]

private noncomputable def steps {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (t : Fin (l+1)) (V : State l A F → α → Bool) :
    (n : Nat) → n ≤ l → State l A F → α → Bool
  | 0, _, q => V q
  | n+1, h, q =>
      let i : Fin l := ⟨n, by omega⟩
      let W := fun v => steps Z O T j t V n (by omega) v
      disj (edge Z O T j i (yBit t i) W q false) (edge Z O T j i (yBit t i) W q true)

private def Balance {l A F : Nat} (n : Nat) (q v : State l A F) (t : Fin (l+1))
    (C : Fin l → Bool) : Prop :=
  ∀ i, (q.1 i).val = (v.1 i).val + (if i.val < n then charge (C i) (yBit t i) else 0) ∧
       (q.2 i).val = (v.2 i).val + (if i.val < n then charge (yBit t i) (C i) else 0)

private theorem steps_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (t : Fin (l+1)) (V : State l A F → α → Bool)
    (d : α) (n : Nat) (hn : n ≤ l) (q : State l A F) :
    steps Z O T j t V n hn q d = true ↔
      ∃ (C : Fin l → Bool) (v : State l A F),
        (∀ i, i.val < n → Allowed Z O T j i (yBit t i) (C i) d) ∧
        Balance n q v t C ∧ V v d = true := by
  induction n generalizing q with
  | zero =>
      rw [steps]
      constructor
      · intro h
        exact ⟨fun _ => false, q, by simp, by simp [Balance], h⟩
      · rintro ⟨C, v, _, hb, hv⟩
        have e : q = v := Prod.ext
          (funext fun i => Fin.ext (by simpa using (hb i).1))
          (funext fun i => Fin.ext (by simpa using (hb i).2))
        rwa [e]
  | succ n ih =>
      let i : Fin l := ⟨n, by omega⟩
      let W := fun v => steps Z O T j t V n (by omega) v
      have hi : ¬ i.val < n := by simp [i]
      have hi' : i.val < n+1 := by simp [i]
      have sep (s : Fin l) (hs : s ≠ i) : s.val < n+1 ↔ s.val < n := by
        have hne : s.val ≠ n := fun h => hs (Fin.ext h)
        omega
      change (edge Z O T j i (yBit t i) W q false d ||
        edge Z O T j i (yBit t i) W q true d) = true ↔ _
      rw [Bool.or_eq_true_iff]
      constructor
      · intro h
        have extend (c : Bool) (he : edge Z O T j i (yBit t i) W q c d = true) :
            ∃ (C : Fin l → Bool) (v : State l A F),
              (∀ s, s.val < n+1 → Allowed Z O T j s (yBit t s) (C s) d) ∧
              Balance (n+1) q v t C ∧ V v d = true := by
          obtain ⟨hp, hc, hw⟩ := (edge_true Z O T j i _ W q c d).1 he
          obtain ⟨C, v, hg, hb, hv⟩ := (ih (by omega) (debit q i (yBit t i) c)).1 hw
          refine ⟨Function.update C i c, v, ?_, ?_, hv⟩
          · intro s hs
            by_cases heq : s = i
            · subst s
              simpa using hc
            · simpa [Function.update_of_ne heq] using hg s ((sep s heq).1 hs)
          · intro s
            by_cases heq : s = i
            · subst s
              have hbi := hb i
              have ha := hp.1
              have hf := hp.2
              simp only [debit, Function.update_self, lower, hi, if_false, Nat.add_zero] at hbi
              simp only [Function.update_self, hi', if_true]
              constructor <;> omega
            · simpa [sep s heq, debit, Function.update_of_ne heq] using hb s
        exact h.elim (extend false) (extend true)
      · rintro ⟨C, v, hc, hb, hv⟩
        have hbi := hb i
        simp only [hi', if_true] at hbi
        have hp : Pay q i (yBit t i) (C i) := by
          constructor <;> omega
        have hrest : W (debit q i (yBit t i) (C i)) d = true := by
          apply (ih (by omega) _).2
          refine ⟨C, v, (fun s hs => hc s (by omega)), ?_, hv⟩
          intro s
          by_cases heq : s = i
          · subst s
            simp only [debit, Function.update_self, lower, hi, if_false, Nat.add_zero]
            constructor <;> omega
          · simpa [sep s heq, debit, Function.update_of_ne heq] using hb s
        have he := (edge_true Z O T j i _ W q (C i) d).2 ⟨hp, hc i hi', hrest⟩
        cases hC : C i with
        | false => exact Or.inl (by simpa only [hC] using he)
        | true => exact Or.inr (by simpa only [hC] using he)

private noncomputable def table {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) : (k : Nat) → k ≤ r → State l A F → α → Bool
  | 0, _, _ => fun _ => true
  | k+1, hk, q => fun d =>
      decide (∃ t ∈ (Finset.univ : Finset (Fin (l+1))),
        steps Z O T ⟨k, by omega⟩ t (fun v => table Z O T k (by omega) v) l le_rfl q d = true)

private def put {r : Nat} (j : Fin r) (v : Bool) (U : Finset (Fin r)) : Finset (Fin r) :=
  if v then insert j U else U

private theorem mem_put {r : Nat} {j z : Fin r} {v : Bool} {U : Finset (Fin r)} :
    z ∈ put j v U ↔ z ∈ U ∨ (z = j ∧ v = true) := by
  cases v <;> simp [put, or_comm]

private theorem put_erase {r : Nat} (j : Fin r) (U : Finset (Fin r)) :
    put j (bit U j) (U.erase j) = U := by
  ext z
  by_cases h : z = j
  · subst z
    simp [mem_put, bit]
  · simp [mem_put, Finset.mem_erase, h]

private theorem card_put_sdiff {r : Nat} {j : Fin r} {U V : Finset (Fin r)}
    (hU : j ∉ U) (hV : j ∉ V) (u v : Bool) :
    (put j u U \ put j v V).card = (U \ V).card + charge u v := by
  have he : put j u U \ put j v V = put j (u && !v) (U \ V) := by
    ext z
    by_cases h : z = j
    · subst z
      cases u <;> cases v <;> simp [mem_put, Finset.mem_sdiff, hU, hV]
    · simp [mem_put, Finset.mem_sdiff, h]
  rw [he]
  cases u <;> cases v <;> simp [put, charge, Finset.card_insert_of_notMem, Finset.mem_sdiff, hU]

private def Row {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (k : Nat) (d : α) (i : Fin l) (Y C : Finset (Fin r)) : Prop :=
  ∀ z : Fin r, if z.val < k then Allowed Z O T z i (bit Y z) (bit C z) d
    else z ∉ Y ∧ z ∉ C

private theorem row_step {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    {k : Nat} {j : Fin r} (hj : j.val = k) (d : α) (i : Fin l) {Y C : Finset (Fin r)}
    (hy : j ∉ Y) (hc : j ∉ C) (y c : Bool) :
    Row Z O T (k+1) d i (put j y Y) (put j c C) ↔
      Row Z O T k d i Y C ∧ Allowed Z O T j i y c d := by
  have hj₀ : ¬ j.val < k := by omega
  have hj₁ : j.val < k+1 := by omega
  have sep (z : Fin r) (h : z ≠ j) : z.val < k+1 ↔ z.val < k := by
    have hn : z.val ≠ j.val := fun e => h (Fin.ext e)
    omega
  have self (Ws : Finset (Fin r)) (hWs : j ∉ Ws) (v : Bool) : bit (put j v Ws) j = v := by
    cases v <;> simp [bit, mem_put, hWs]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro z
      by_cases he : z = j
      · subst z
        simp [hj₀, hy, hc]
      · simpa [sep z he, bit, mem_put, he] using h z
    · simpa [hj₁, self Y hy, self C hc] using h j
  · rintro ⟨h, ha⟩ z
    by_cases he : z = j
    · subst z
      simpa [hj₁, self Y hy, self C hc] using ha
    · simpa [sep z he, bit, mem_put, he] using h z

private theorem row_top {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (d : α) (i : Fin l) (Y C : Finset (Fin r)) :
    Row Z O T r d i Y C ↔ Y ⊆ T d ∧ (Finset.univ \ C) ⊆ Z d i ∧ C ⊆ O d i := by
  unfold Row
  simp only [Fin.isLt, if_true]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (h z).2 (by simp [bit, hz])
    · intro z hz
      have hn := (Finset.mem_sdiff.mp hz).2
      simpa [bit, hn] using (h z).1
    · intro z hz
      simpa [bit, hz] using (h z).1
  · rintro ⟨hY, hZ, hO⟩ z
    constructor
    · by_cases hz : z ∈ C
      · simpa [bit, hz] using hO hz
      · simpa [bit, hz] using hZ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩)
    · intro h
      exact hY (by simpa [bit] using h)

private theorem threshold {l r : Nat} {Y : Fin l → Finset (Fin r)} (hY : Monotone Y) (j : Fin r) :
    ∃ t : Fin (l+1), ∀ i, yBit t i = bit (Y i) j := by
  by_cases h : ∃ n : Nat, ∃ i : Fin l, i.val = n ∧ j ∈ Y i
  · obtain ⟨i₀, hi₀, hm⟩ := Nat.find_spec h
    refine ⟨⟨Nat.find h, by have := i₀.isLt; omega⟩, fun i => ?_⟩
    change decide (Nat.find h ≤ i.val) = decide (j ∈ Y i)
    apply decide_eq_decide.mpr
    constructor
    · intro hi
      exact hY (show i₀ ≤ i from by change i₀.val ≤ i.val; omega) hm
    · intro hi
      exact Nat.find_min' h ⟨i, rfl, hi⟩
  · refine ⟨⟨l, by omega⟩, fun i => ?_⟩
    have hm : j ∉ Y i := fun hi => h ⟨i.val, i, rfl, hi⟩
    have hn : ¬ l ≤ i.val := Nat.not_le_of_lt i.isLt
    simp [yBit, bit, hm, hn]

private def Feasible {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (k : Nat) (q : State l A F) (d : α) : Prop :=
  ∃ Y C : Fin l → Finset (Fin r), Monotone Y ∧
    ∀ i, Row Z O T k d i (Y i) (C i) ∧
      (C i \ Y i).card ≤ (q.1 i).val ∧ (Y i \ C i).card ≤ (q.2 i).val

private theorem table_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (d : α) (k : Nat) (hk : k ≤ r) (q : State l A F) :
    table Z O T k hk q d = true ↔ Feasible Z O T k q d := by
  induction k generalizing q with
  | zero =>
      rw [table]
      refine ⟨fun _ => ⟨fun _ => ∅, fun _ => ∅, fun _ _ _ => le_rfl, fun i => ?_⟩,
        fun _ => rfl⟩
      simp [Row]
  | succ k ih =>
      let j : Fin r := ⟨k, by omega⟩
      let V := fun v : State l A F => table Z O T k (by omega) v
      change decide (∃ t ∈ (Finset.univ : Finset (Fin (l+1))),
        steps Z O T j t V l le_rfl q d = true) = true ↔ _
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨t, _, ht⟩
        obtain ⟨c, v, hc, hb, hv⟩ := (steps_true Z O T j t V d l le_rfl q).1 ht
        obtain ⟨Y, C, hY, h⟩ := (ih (by omega) v).1 hv
        refine ⟨fun i => put j (yBit t i) (Y i), fun i => put j (c i) (C i), ?_, ?_⟩
        · intro i s his z hz
          rw [mem_put] at hz ⊢
          refine hz.elim (fun hmem => Or.inl (hY his hmem)) ?_
          rintro ⟨hmem, hbit⟩
          have ht' : t.val ≤ i.val := by simpa [yBit] using hbit
          exact Or.inr ⟨hmem, by simpa [yBit] using ht'.trans his⟩
        · intro i
          obtain ⟨hr, ha, hf⟩ := h i
          have fresh : j ∉ Y i ∧ j ∉ C i := by simpa [j] using hr j
          have hbi := hb i
          simp only [i.isLt, if_true] at hbi
          refine ⟨(row_step Z O T rfl d i fresh.1 fresh.2 _ _).2 ⟨hr, hc i i.isLt⟩, ?_, ?_⟩
          · rw [card_put_sdiff fresh.2 fresh.1, hbi.1]
            exact Nat.add_le_add_right ha _
          · rw [card_put_sdiff fresh.1 fresh.2, hbi.2]
            exact Nat.add_le_add_right hf _
      · rintro ⟨Y, C, hY, h⟩
        obtain ⟨t, ht⟩ := threshold hY j
        let c := fun i => bit (C i) j
        let U := fun i => (Y i).erase j
        let W := fun i => (C i).erase j
        let v : State l A F := (fun i => lower (q.1 i) (charge (c i) (yBit t i)),
                                 fun i => lower (q.2 i) (charge (yBit t i) (c i)))
        have split (i : Fin l) :
            (Row Z O T k d i (U i) (W i) ∧ Allowed Z O T j i (yBit t i) (c i) d) ∧
            (W i \ U i).card + charge (c i) (yBit t i) ≤ (q.1 i).val ∧
            (U i \ W i).card + charge (yBit t i) (c i) ≤ (q.2 i).val := by
          have h1 : put j (yBit t i) (U i) = Y i := by rw [ht i]; exact put_erase j (Y i)
          have h2 : put j (c i) (W i) = C i := put_erase j (C i)
          have hu : j ∉ U i := by simp [U]
          have hw : j ∉ W i := by simp [W]
          refine ⟨(row_step Z O T rfl d i hu hw _ _).1 ?_, ?_, ?_⟩
          · rw [h1, h2]
            exact (h i).1
          · rw [← card_put_sdiff hw hu, h1, h2]
            exact (h i).2.1
          · rw [← card_put_sdiff hu hw, h1, h2]
            exact (h i).2.2
        refine ⟨t, Finset.mem_univ _, (steps_true Z O T j t V d l le_rfl q).2
          ⟨c, v, (fun i _ => (split i).1.2), ?_, ?_⟩⟩
        · intro i
          have ha := (split i).2.1
          have hf := (split i).2.2
          simp only [i.isLt, if_true, v, lower]
          constructor <;> omega
        · apply (ih (by omega) v).2
          refine ⟨U, W, ?_, fun i => ⟨(split i).1.1, ?_, ?_⟩⟩
          · intro i s his z hz
            obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hz
            exact Finset.mem_erase.mpr ⟨hn, hY his hm⟩
          · have ha := (split i).2.1
            change (W i \ U i).card ≤ (q.1 i).val - charge (c i) (yBit t i)
            omega
          · have hf := (split i).2.2
            change (U i \ W i).card ≤ (q.2 i).val - charge (yBit t i) (c i)
            omega

private theorem already {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f : α → Bool} (hf : f ∈ S) (cost : Nat) : Grow x N p b S cost f :=
  ⟨S, H.relax (by omega) le_rfl (by intro g hg; exact hg), (by intro g hg; exact hg), hf⟩

private theorem appendAnd {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f g : α → Bool} (hf : f ∈ S) (hg : g ∈ S) :
    Grow x N p b S 1 (conj f g) :=
  ⟨_, H.andGate hf hg, Set.subset_insert _ _, Set.mem_insert _ _⟩

private theorem appendOr {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f g : α → Bool} (hf : f ∈ S) (hg : g ∈ S) :
    Grow x N p b S 1 (disj f g) :=
  ⟨_, H.orGate hf hg, Set.subset_insert _ _, Set.mem_insert _ _⟩

private theorem edge_grow {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y c : Bool)
    (V : State l A F → α → Bool) (q : State l A F)
    (hz : (fun d => bit (Z d i) j) ∈ S) (ho : (fun d => bit (O d i) j) ∈ S)
    (ht : (fun d => bit (T d) j) ∈ S) (hfalse : (fun _ => false) ∈ S)
    (hv : V (debit q i y c) ∈ S) : Grow x N p b S 2 (edge Z O T j i y V q c) := by
  by_cases hp : Pay q i y c
  · let B := if c then fun d => bit (O d i) j else fun d => bit (Z d i) j
    have hB : B ∈ S := by cases c <;> assumption
    let w := V (debit q i y c)
    have hw : w ∈ S := hv
    have hinner : Grow x N p b S 1 (if y then conj (fun d => bit (T d) j) w else w) := by
      cases y
      · exact already H hw 1
      · exact appendAnd H ht hw
    obtain ⟨U, hU, hSU, hinner⟩ := hinner
    obtain ⟨W, hW, hUW, hout⟩ := appendAnd hU (hSU hB) hinner
    exact ⟨W, hW, hSU.trans hUW, by simpa only [edge, hp, if_true, B, w] using hout⟩
  · simpa only [edge, hp, if_false] using already H hfalse 2

private noncomputable def layerCost (l A F : Nat) : Nat := Fintype.card (Keys l A F) * 5
private noncomputable def columnCost (l A F : Nat) : Nat :=
  l * layerCost l A F + Fintype.card (State l A F) * (l+1)

private theorem steps_built {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (V : State l A F → α → Bool)
    (hz : ∀ i, (fun d => bit (Z d i) j) ∈ S) (ho : ∀ i, (fun d => bit (O d i) j) ∈ S)
    (ht : (fun d => bit (T d) j) ∈ S) (hfalse : (fun _ => false) ∈ S) (hv : ∀ q, V q ∈ S)
    (n : Nat) (hn : n ≤ l) :
    ∃ U, Built x N (p+n*layerCost l A F) b U ∧ S ⊆ U ∧
      ∀ t q, steps Z O T j t V n hn q ∈ U := by
  induction n with
  | zero => exact ⟨S, by simpa using H, fun _ h => h, fun _ q => hv q⟩
  | succ n ih =>
      obtain ⟨R, hR, hSR, hprev⟩ := ih (by omega)
      let i : Fin l := ⟨n, by omega⟩
      obtain ⟨U, hU, hRU, hvalues⟩ := batch (Finset.univ : Finset (Keys l A F))
        (fun z => steps Z O T j z.1 V (n+1) hn z.2) 5 hR (by
          intro P M hM hRM z _
          let W := fun q => steps Z O T j z.1 V n (by omega) q
          have hSM := hSR.trans hRM
          let y := yBit z.1 i
          have make (c : Bool) := edge_grow hM Z O T j i y c W z.2
            (hSM (hz i)) (hSM (ho i)) (hSM ht) (hSM hfalse) (hRM (hprev _ _))
          obtain ⟨M₀, hM₀, hMM₀, he₀⟩ := make false
          obtain ⟨M₁, hM₁, hM₀M₁, he₁⟩ := edge_grow hM₀ Z O T j i y true W z.2
            (hMM₀ (hSM (hz i))) (hMM₀ (hSM (ho i))) (hMM₀ (hSM ht))
            (hMM₀ (hSM hfalse)) (hMM₀ (hRM (hprev _ _)))
          obtain ⟨M₂, hM₂, hM₁M₂, hdone⟩ := appendOr hM₁ (hM₀M₁ he₀) he₁
          exact ⟨M₂, hM₂, hMM₀.trans (hM₀M₁.trans hM₁M₂), hdone⟩)
      refine ⟨U, ?_, hSR.trans hRU, fun t q => hvalues (t,q) (Finset.mem_univ _)⟩
      simpa [layerCost, Nat.succ_mul, Nat.add_assoc] using hU

private theorem table_built {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r))
    (hz : ∀ i j, (fun d => bit (Z d i) j) ∈ S) (ho : ∀ i j, (fun d => bit (O d i) j) ∈ S)
    (ht : ∀ j, (fun d => bit (T d) j) ∈ S)
    (hfalse : (fun _ => false) ∈ S) (htrue : (fun _ => true) ∈ S) (k : Nat) (hk : k ≤ r) :
    ∃ U, Built x N (p+k*columnCost l A F) b U ∧ S ⊆ U ∧
      ∀ q : State l A F, table Z O T k hk q ∈ U := by
  induction k with
  | zero => exact ⟨S, by simpa using H, fun _ h => h, fun _ => htrue⟩
  | succ k ih =>
      obtain ⟨R, hR, hSR, hprev⟩ := ih (by omega)
      let j : Fin r := ⟨k, by omega⟩
      let V := fun v : State l A F => table Z O T k (by omega) v
      obtain ⟨U, hU, hRU, hstep⟩ := steps_built hR Z O T j V (fun i => hSR (hz i j))
        (fun i => hSR (ho i j)) (hSR (ht j)) (hSR hfalse) hprev l le_rfl
      obtain ⟨W, hW, hUW, hout⟩ := batch (Finset.univ : Finset (State l A F))
        (fun q => table Z O T (k+1) hk q) (l+1) hU (by
          intro P M hM hUM q _
          obtain ⟨Q, hQ, hMQ, hfQ⟩ := anyFold (Finset.univ : Finset (Fin (l+1)))
            (fun t => steps Z O T j t V l le_rfl q) hM (hUM (hRU (hSR hfalse)))
            (fun t _ => hUM (hstep t q))
          refine ⟨Q, by simpa only [Finset.card_univ, Fintype.card_fin] using hQ, hMQ, ?_⟩
          refine Eq.mpr (congrArg (fun g : α → Bool => g ∈ Q) ?_) hfQ
          funext d
          apply Bool.eq_iff_iff.mpr
          simp only [table, decide_eq_true_eq, j, V])
      refine ⟨W, ?_, hSR.trans (hRU.trans hUW), fun q => hout q (Finset.mem_univ _)⟩
      simpa [columnCost, Nat.succ_mul, Nat.add_assoc] using hW

private theorem columnCost_bound (l A F : Nat) :
    columnCost l A F ≤ 8 * (l+1)^2 * ((A+1)*(F+1))^l := by
  have hs : Fintype.card (State l A F) = ((A+1)*(F+1))^l := by
    simp [Fintype.card_prod, Fintype.card_fun, mul_pow]
  have hk : Fintype.card (Keys l A F) = (l+1) * ((A+1)*(F+1))^l := by
    rw [Fintype.card_prod, Fintype.card_fin, hs]
  rw [columnCost, layerCost, hs, hk]
  let c := ((A+1)*(F+1))^l
  change l * ((l+1) * c * 5) + c * (l+1) ≤ 8 * (l+1)^2 * c
  have h : l*5+1 ≤ 8*(l+1) := by omega
  calc
    l * ((l+1) * c * 5) + c * (l+1) = (l*5+1) * (l+1) * c := by ring
    _ ≤ (8*(l+1)) * (l+1) * c := Nat.mul_le_mul_right c (Nat.mul_le_mul_right (l+1) h)
    _ = 8 * (l+1)^2 * c := by ring

theorem grow {α : Type*} {x : α → List Bool} {N p b l r A F : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) (Z O : α → Fin l → Finset (Fin r)) (T : α → Finset (Fin r))
    (a f : Fin l → Nat) (ha : ∀ i, a i ≤ A) (hf : ∀ i, f i ≤ F)
    (hz : ∀ i j, (fun d => decide (j ∈ Z d i)) ∈ S)
    (ho : ∀ i j, (fun d => decide (j ∈ O d i)) ∈ S)
    (ht : ∀ j, (fun d => decide (j ∈ T d)) ∈ S)
    (hfalse : (fun _ => false) ∈ S) (htrue : (fun _ => true) ∈ S) :
    Grow x N p b S (8 * (r+2) * (l+1)^2 * ((A+1)*(F+1))^l)
      (fun d => decide (∃ Y C : Fin l → Finset (Fin r), Monotone Y ∧
        (∀ i, Y i ⊆ T d) ∧
        (∀ i, (Finset.univ \ C i) ⊆ Z d i ∧ C i ⊆ O d i ∧
          (C i \ Y i).card ≤ a i ∧ (Y i \ C i).card ≤ f i))) := by
  let q : State l A F := (fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩,
                          fun i => ⟨f i, Nat.lt_succ_of_le (hf i)⟩)
  obtain ⟨U, hU, hSU, hout⟩ := table_built H Z O T hz ho ht hfalse htrue r le_rfl
    (A := A) (F := F)
  have hcost : r * columnCost l A F ≤ 8 * (r+2) * (l+1)^2 * ((A+1)*(F+1))^l := by
    calc
      _ ≤ (r+2) * (8 * (l+1)^2 * ((A+1)*(F+1))^l) :=
        Nat.mul_le_mul (by omega) (columnCost_bound l A F)
      _ = _ := by ring
  refine ⟨U, hU.relax (Nat.add_le_add_left hcost p) le_rfl (fun _ h => h), hSU, ?_⟩
  refine Eq.mpr (congrArg (fun g : α → Bool => g ∈ U) ?_) (hout q)
  funext d
  apply Bool.eq_iff_iff.mpr
  rw [table_true, decide_eq_true_eq]
  constructor
  · rintro ⟨Y, C, hm, hy, h⟩
    refine ⟨Y, C, hm, fun i => ⟨(row_top Z O T d i (Y i) (C i)).2
      ⟨hy i, (h i).1, (h i).2.1⟩, (h i).2.2.1, (h i).2.2.2⟩⟩
  · rintro ⟨Y, C, hm, h⟩
    have hr := fun i => (row_top Z O T d i (Y i) (C i)).1 (h i).1
    exact ⟨Y, C, hm, fun i => (hr i).1, fun i => ⟨(hr i).2.1, (hr i).2.2, (h i).2⟩⟩

end Tables

private theorem flatten_ofFn_length {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) :
    (List.ofFn f).flatten.length = k * m := by
  rw [List.length_flatten, List.map_ofFn]
  have hconst : (List.length ∘ f) = fun _ => m := funext hlen
  rw [hconst, List.ofFn_const, List.sum_replicate, smul_eq_mul]

private theorem flatten_ofFn_getElem {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) (i : Fin k) (r : ℕ) (hr : r < m) :
    ((List.ofFn f).flatten)[i.val * m + r]'(by
      rw [flatten_ofFn_length f hlen]
      have : (i.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; omega) =
    (f i)[r]'(by rw [hlen i]; exact hr) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem_append_left (by rw [hlen 0]; exact hr)]
    | succ i' =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, Nat.add_mul, Nat.one_mul]
      have h1 : m ≤ i'.val * m + m + r := by omega
      rw [List.getElem_append_right (by rw [hlen 0]; exact h1)]
      have heq : i'.val * m + m + r - (f 0).length = i'.val * m + r := by rw [hlen 0]; omega
      simp only [heq]
      exact ih (fun j => f j.succ) (fun j => hlen j.succ) i'

private def wordCost (r l A F : Nat) : Nat := 8*(r+2)*(l+1)^2*((A+1)*(F+1))^l

private def familyCost (r m l A F : Nat) : Nat := (m+1)^l * (wordCost r l A F + 1)

private def sizeBound (r m K A F : Nat) : Nat :=
  128*(r+2)*(K+3)^3*((m+1)*(A+1)*(F+1))^(K+1)

private theorem grow_family {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    {r m l A F : Nat} {lab : α → Finset (Fin r) → Fin m → Prop} {U : α → Finset (Fin r)}
    (H : Built x N p b S) (hf : (fun _ => false) ∈ S) (P : (Fin l → Fin m) → Prop)
    (word : ∀ {P' T}, Built x N P' b T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x N P' b T (wordCost r l A F) (fun d => decide (WordTrace (lab d) (U d) w))) :
    Grow x N p b S (familyCost r m l A F)
      (fun d => decide (∃ w : Fin l → Fin m, P w ∧ WordTrace (lab d) (U d) w)) := by
  let ws : Finset (Fin l → Fin m) := Finset.univ.filter P
  let sig (w : Fin l → Fin m) (d : α) := decide (WordTrace (lab d) (U d) w)
  obtain ⟨T,hT,st,hw⟩ := batch ws sig (wordCost r l A F) H (fun h sub w _ => word h sub w)
  obtain ⟨Q,hQ,tq,hq⟩ := anyFold ws sig hT (st hf) hw
  have cw : ws.card ≤ (m+1)^l := by
    calc
      ws.card ≤ (Finset.univ : Finset (Fin l → Fin m)).card := Finset.card_filter_le _ _
      _ = m^l := by simp [Fintype.card_fun]
      _ ≤ (m+1)^l := Nat.pow_le_pow_left (by omega) _
  have cap : p + ws.card * wordCost r l A F + ws.card ≤ p + familyCost r m l A F := by
    rw [Nat.add_assoc, ← Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ cw) _
  refine ⟨Q,hQ.relax cap le_rfl (Set.Subset.rfl),st.trans tq,?_⟩
  have eq : (fun d => decide (∃ w ∈ ws, sig w d = true)) =
      (fun d => decide (∃ w : Fin l → Fin m, P w ∧ WordTrace (lab d) (U d) w)) := by
    funext d; simp [ws,sig]
  exact eq ▸ hq

private noncomputable def signal {r m : Nat} (K : Nat) (lab : Finset (Fin r) → Fin m → Prop)
    (X : Finset (Fin r)) (j : Fin m) : Bool := decide (Bucket lab X (rank K lab X) j)

private theorem aggregate {α : Type*} {x : α → List Bool} {N : Nat} {S : Set (α → Bool)}
    {r m b K A F : Nat} {lab : α → Finset (Fin r) → Fin m → Prop} {X : α → Finset (Fin r)}
    (H : Built x N 0 0 S) (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (hK : 0 < K) (pow : K ≤ 2^b)
    (word : ∀ {P T l} (U : α → Finset (Fin r)), (U = X ∨ U = fun _ => Finset.univ) →
      Built x N P 0 T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x N P 0 T (wordCost r l A F) (fun d => decide (WordTrace (lab d) (U d) w))) :
    ∃ T, Built x N (sizeBound r m K A F) b T ∧
      (fun d => decide (Trace (lab d) Finset.univ (K+1))) ∈ T ∧
      ∀ j, (fun d => signal K (lab d) (X d) j) ∈ T := by
  let M := (m+1)*(A+1)*(F+1)
  let H₀ := 9*(r+2)*(K+2)^2
  let p₀ := H₀*M^(K+1)
  let p₁ := H₀*M^K
  have hM : 1 ≤ M := by change 0 < M; dsimp [M]; positivity
  have cost (l : Nat) (hl : l ≤ K+1) : familyCost r m l A F ≤ H₀*M^l := by
    have hcoeff : 1 ≤ (r+2)*(l+1)^2*((A+1)*(F+1))^l := by
      change 0 < (r+2)*(l+1)^2*((A+1)*(F+1))^l
      positivity
    calc
      familyCost r m l A F = (m+1)^l * (8*((r+2)*(l+1)^2*((A+1)*(F+1))^l) + 1) := by
        unfold familyCost wordCost; ring
      _ ≤ (m+1)^l * (9*((r+2)*(l+1)^2*((A+1)*(F+1))^l)) := by gcongr; omega
      _ = 9*(r+2)*(l+1)^2*M^l := by dsimp [M]; rw [mul_pow,mul_pow,mul_pow]; ring
      _ ≤ H₀*M^l := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (show l+1 ≤ K+2 by omega) 2))
  obtain ⟨U,hU,su,bad⟩ := grow_family H hf (Adj (m := m) (l := K+1))
    (fun h st w => word (fun _ => Finset.univ) (Or.inr rfl) h st w)
  have hU' : Built x N p₀ 0 U := hU.relax (by simpa [p₀] using cost (K+1) le_rfl) le_rfl (Set.Subset.rfl)
  let L (v : Fin K × Option (Fin m)) (d : α) := decide
    (∃ w : Fin (v.1.val+1) → Fin m, (Adj w ∧ ∀ j, v.2 = some j → w (Fin.last v.1.val) = j) ∧
      WordTrace (lab d) (X d) w)
  obtain ⟨V,hV,uv,lh⟩ := batch (Finset.univ : Finset (Fin K × Option (Fin m))) L p₁ hU' (by
    intro P T h ut v _
    obtain ⟨Q,hQ,tq,out⟩ := grow_family h (ut (su hf))
      (fun w : Fin (v.1.val+1) → Fin m => Adj w ∧ ∀ j, v.2 = some j → w (Fin.last v.1.val) = j)
      (fun hh st w => word X (Or.inl rfl) hh (su.trans (ut.trans st)) w)
    have cv : familyCost r m (v.1.val+1) A F ≤ p₁ :=
      (cost _ (by have := v.1.isLt; omega)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM (by have := v.1.isLt; omega)))
    refine ⟨Q,hQ.relax (Nat.add_le_add_left cv _) le_rfl (Set.Subset.rfl),tq,?_⟩
    convert out using 1
    funext d; apply Bool.eq_iff_iff.mpr; simp [L])
  have tr (k : Fin K) : (fun d => decide (Trace (lab d) (X d) (k.val+1))) ∈ V := by
    convert lh (k,none) (Finset.mem_univ _) using 1
    funext d; apply boolOfIff; simp [L,Trace]
  have buck (k : Fin K) (j : Fin m) : (fun d => decide (Bucket (lab d) (X d) k.val j)) ∈ V := by
    convert lh (k,some j) (Finset.mem_univ _) using 1
    funext d; apply boolOfIff
    simp [L,Bucket,and_left_comm,and_assoc,and_comm]
  let R (d : α) := rank K (lab d) (X d)
  have threshold (i : Nat) (hi : i < K) : (fun d => decide (i ≤ R d)) ∈ V := by
    rcases eq_or_ne i 0 with rfl | nz
    · simpa using uv (su ht)
    · have he : (fun d => decide (i ≤ R d)) = (fun d => decide (Trace (lab d) (X d) (i+1))) := by
        funext d
        simp [R, le_rank_iff hi,nz]
      rw [he]; exact tr ⟨i,hi⟩
  obtain ⟨W,hW,vw,exactRank⟩ := RankDecoder.decode hV (uv (su ht)) (uv (su hf))
    (R := R) (fun _ => rank_lt hK) hK pow threshold
  obtain ⟨T,hT,wt,taps⟩ := batch (Finset.univ : Finset (Fin m))
    (fun j d => signal K (lab d) (X d) j) (2*K) hW (by
      intro P Q h wq j _
      let c (k : Fin K) := conj (fun d => decide (R d=k.val))
        (fun d => decide (Bucket (lab d) (X d) k.val j))
      obtain ⟨Q',hQ',qq,terms⟩ := batch (Finset.univ : Finset (Fin K)) c 1 h (by
        intro p' A hh qa k _
        have hh' := hh.andGate (qa (wq (exactRank k.val k.isLt))) (qa (wq (vw (buck k j))))
        exact ⟨_,hh',Set.subset_insert _ _,Set.mem_insert _ _⟩)
      obtain ⟨Q'',hQ'',q'q'',sum⟩ := anyFold (Finset.univ : Finset (Fin K)) c hQ'
        (qq (wq (vw (uv (su hf))))) terms
      refine ⟨Q'',hQ''.relax (by simp; omega) le_rfl (Set.Subset.rfl),qq.trans q'q'',?_⟩
      convert sum using 1
      funext d
      symm
      apply Bool.eq_iff_iff.mpr
      simp only [Finset.mem_univ,true_and,c,conj,Bool.and_eq_true,decide_eq_true_eq,signal]
      constructor
      · rintro ⟨k,hk,ok⟩; simpa only [← hk] using ok
      · intro yes; exact ⟨⟨R d,rank_lt hK⟩,rfl,yes⟩)
  have leM : m+1 ≤ M := by
    dsimp [M]
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hp01 : (m+1)*p₁ ≤ p₀ := by
    dsimp [p₀,p₁]
    rw [pow_succ]
    calc
      (m+1)*(H₀*M^K) ≤ M*(H₀*M^K) := Nat.mul_le_mul_right _ leM
      _ = H₀*(M^K*M) := by ring
  have hp : K*(m+1)*p₁ ≤ K*p₀ := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hp01
  have hdr : 16*(K+1)^2 ≤ p₀ := by
    have hz : 1 ≤ M^(K+1) := by change 0 < M^(K+1); positivity
    calc
      16*(K+1)^2 ≤ H₀ := by dsimp [H₀]; nlinarith
      _ ≤ p₀ := by dsimp [p₀]; exact Nat.le_mul_of_pos_right _ hz
  have hlast : m*(2*K) ≤ p₀ := by
    have leP : m ≤ M^(K+1) := by
      nlinarith [Nat.pow_le_pow_right hM (show 1 ≤ K+1 by omega), pow_one M]
    have coef : 2*K ≤ H₀ := by dsimp [H₀]; nlinarith
    simpa [p₀,Nat.mul_comm] using Nat.mul_le_mul coef leP
  have tot : p₀ + K*(m+1)*p₁ + 16*(K+1)^2 + m*(2*K) ≤ sizeBound r m K A F := by
    calc
      _ ≤ (K+3)*p₀ := by nlinarith
      _ = 9*(r+2)*(K+2)^2*(K+3)*M^(K+1) := by dsimp [p₀,H₀]; ring
      _ ≤ sizeBound r m K A F := by
        change _ ≤ 128*(r+2)*(K+3)^3*M^(K+1)
        have hs : (K+2)^2 ≤ (K+3)^2 := by gcongr; omega
        rw [show (K+3)^3 = (K+3)^2*(K+3) by ring]
        rw [← Nat.mul_assoc (128*(r+2)) ((K+3)^2) (K+3)]
        gcongr <;> omega
  have hfinal : Built x N (sizeBound r m K A F) b T := by
    apply hT.relax _ (by simp) (Set.Subset.rfl)
    simpa [Fintype.card_prod,Nat.add_comm] using tot
  refine ⟨T,hfinal,wt (vw (uv ?_)),fun j => taps j (Finset.mem_univ _)⟩
  convert bad using 1
  funext d; apply boolOfIff; rfl

noncomputable def rows {m r : Nat} (D : Fin m → Finset (Fin r)) : List Bool :=
  (List.ofFn (fun i => bits (D i))).flatten

private theorem rows_length {m r : Nat} (D : Fin m → Finset (Fin r)) : (rows D).length = m*r :=
  flatten_ofFn_length _ (fun _ => by simp [bits])

private theorem rows_getD {m r : Nat} (D : Fin m → Finset (Fin r)) (i : Fin m) (j : Fin r) :
    (rows D).getD (i.val*r+j.val) false = decide (j ∈ D i) := by
  have lb : i.val*r+j.val < (rows D).length := by
    rw [rows_length]
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  have rb : j.val < (bits (D i)).length := by simp [bits]
  calc
    _ = (rows D)[i.val*r+j.val] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lb]
    _ = (bits (D i))[j.val] := flatten_ofFn_getElem _ (fun _ => by simp [bits]) i j.val j.isLt
    _ = _ := by
      rw [← bits_getD (D i) j]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rb]

private def InputSet {α : Type*} (x : α → List Bool) (N : Nat) : Set (α → Bool) :=
  {f | ∃ i < N, f = fun d => (x d).getD i false}

private theorem input_mem {α : Type*} {x : α → List Bool} {N i : Nat} {f : α → Bool}
    (hi : i < N) (eq : ∀ d, (x d).getD i false = f d) : f ∈ InputSet x N :=
  ⟨i,hi,(funext eq).symm⟩

private theorem suffix_const {α : Type*} {w : α → List Bool} {n : Nat} (L : ∀ d, (w d).length = n) :
    (fun _ => false) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) ∧
    (fun _ => true) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) := by
  constructor
  · apply input_mem (i := n) (by omega)
    intro d; simp [List.getD_append_right _ _ _ _ (show (w d).length ≤ n by rw [L]),L]
  · apply input_mem (i := n+1) (by omega)
    intro d; simp [List.getD_append_right _ _ _ _ (show (w d).length ≤ n+1 by rw [L]; omega),L]

private theorem some_taps {α : Type*} {x : α → List Bool} {n m p b : Nat} {S : Set (α → Bool)}
    {bad : α → Bool} {tap : Fin m → α → Bool} (H : Built x (n+2) p b S)
    (hb : bad ∈ S) (ht : ∀ j, tap j ∈ S) :
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧ (∀ j, out j < n+2+D.size) ∧
      notCount D ≤ b ∧ D.size - notCount D ≤ p ∧
      (∀ d, D.eval (x d) = bad d) ∧ ∀ d j, (D.wires (x d)).getD (out j) false = tap j d := by
  obtain ⟨_,gs,fan,back,pc,nc,sigs⟩ := H
  obtain ⟨o,ho,eo⟩ := sigs _ hb
  choose out hout eout using (fun j => sigs (tap j) (ht j))
  exact ⟨⟨gs,o⟩,out,⟨fan,back,ho⟩,hout,nc,pc,congrFun eo,fun d j => congrFun (eout j) d⟩

private theorem word_table_equiv {r m l : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (U : Finset (Fin r)) (w : Fin l → Fin m) :
    WordTrace (Label a f Z O) U w ↔
      ∃ (Y C : Fin l → Finset (Fin r)), Monotone Y ∧ (∀ i, Y i ⊆ U) ∧
        ∀ i, (Finset.univ \ C i) ⊆ Z (w i) ∧ C i ⊆ O (w i) ∧
          ((C i) \ (Y i)).card ≤ min r (a (w i)) ∧ ((Y i) \ (C i)).card ≤ min r (f (w i)) := by
  constructor
  · rintro ⟨Y,mono,sub,lab⟩
    choose C hC using lab
    refine ⟨Y,C,mono,sub,fun i => ?_⟩
    obtain ⟨hZ,hO,ha,hf⟩ := hC i
    exact ⟨hZ,hO,le_min (by simpa using ((C i) \ (Y i)).card_le_univ) ha,
      le_min (by simpa using ((Y i) \ (C i)).card_le_univ) hf⟩
  · rintro ⟨Y,C,mono,sub,all⟩
    exact ⟨Y,mono,sub,fun i => ⟨C i,(all i).1,(all i).2.1,
      (all i).2.2.1.trans (min_le_right ..),(all i).2.2.2.trans (min_le_right ..)⟩⟩

private theorem realize {α : Type*} {x : α → List Bool} {n r m b : Nat} {S : Set (α → Bool)}
    (a f : Fin m → Nat) (Z O : α → Fin m → Finset (Fin r)) (X : α → Finset (Fin r))
    (H : Built x (n+2) 0 0 S) (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (word : ∀ {P T l} (U : α → Finset (Fin r)), (U = X ∨ U = fun _ => Finset.univ) →
      Built x (n+2) P 0 T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x (n+2) P 0 T (wordCost r l (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i)))
        (fun d => decide (WordTrace (Label a f (Z d) (O d)) (U d) w))) :
    let K := min (2^b) (r+1)
    let B := sizeBound r m K (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i))
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧ (∀ j, out j < n+2+D.size) ∧
      notCount D ≤ b ∧ D.size - notCount D ≤ B ∧
      (∀ d, D.eval (x d) = false ↔ ¬ Trace (Label a f (Z d) (O d)) Finset.univ (K+1)) ∧
      ∀ d, (¬ Trace (Label a f (Z d) (O d)) Finset.univ (K+1)) →
        ∀ i, Label a f (Z d) (O d) (X d) i → ∀ j,
        (D.wires (x d)).getD (out j) false = labelBit i j := by
  dsimp only
  let K := min (2^b) (r+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T,hT,bad,tap⟩ := aggregate (K := K) (b := b) H ht hf hK (min_le_left ..) word
  obtain ⟨D,out,v,lt,neg,pos,fail,hit⟩ := some_taps hT bad tap
  refine ⟨D,out,v,lt,neg,pos,fun d => by rw [fail]; simp [K],?_⟩
  intro d good i hi j
  rw [hit]
  exact Bool.eq_iff_iff.mpr (by simp [signal,labelBit,correct_bucket hK hi good])

private theorem val_or_const {α : Type*} {S : Set (α → Bool)}
    (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S) (v : Bool) : (fun _ => v) ∈ S := by
  cases v <;> assumption

private abbrev Data (r m : Nat) := (Fin m → Finset (Fin r)) × (Fin m → Finset (Fin r)) × Finset (Fin r)
private noncomputable def raw {r m : Nat} (d : Data r m) : List Bool :=
  rows d.1 ++ rows d.2.1 ++ bits d.2.2 ++ [false,true]

private theorem raw_len {r m : Nat} (d : Data r m) : (raw d).length = 2*m*r+r+2 := by
  simp [raw,rows_length,bits, Nat.add_mul, Nat.add_assoc, two_mul]

private theorem raw_Z {r m : Nat} (i : Fin m) (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.1 i)) ∈ InputSet raw (2*m*r+r+2) := by
  have base : i.val*r+j.val < m*r := by
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  apply input_mem (i := i.val*r+j.val) (by rw [two_mul, Nat.add_mul]; omega)
  intro d
  have h₁ : i.val*r+j.val < (rows d.1).length := by rw [rows_length]; exact base
  rw [raw,List.append_assoc,List.append_assoc,List.getD_append _ _ _ _ h₁]
  exact rows_getD d.1 i j

private theorem raw_O {r m : Nat} (i : Fin m) (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.2.1 i)) ∈ InputSet raw (2*m*r+r+2) := by
  have base : i.val*r+j.val < m*r := by
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  apply input_mem (i := m*r+(i.val*r+j.val)) (by rw [two_mul, Nat.add_mul]; omega)
  intro d
  have h₁ : (rows d.1).length ≤ m*r+(i.val*r+j.val) := by rw [rows_length]; omega
  have h₂ : i.val*r+j.val < (rows d.2.1).length := by rw [rows_length]; exact base
  rw [raw,List.append_assoc,List.append_assoc,List.getD_append_right _ _ _ _ h₁,rows_length]
  rw [Nat.add_sub_cancel_left, List.getD_append _ _ _ _ h₂]
  exact rows_getD d.2.1 i j

private theorem raw_X {r m : Nat} (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.2.2)) ∈ InputSet raw (2*m*r+r+2) := by
  have hj := j.isLt
  apply input_mem (i := 2*m*r+j.val) (by omega)
  intro d
  have hL : (rows d.1 ++ rows d.2.1).length = 2*m*r := by simp [rows_length, two_mul, Nat.add_mul]
  have hR : j.val < (bits d.2.2).length := by simp [bits]
  unfold raw
  rw [List.append_assoc (rows d.1 ++ rows d.2.1), List.getD_append_right _ _ _ _ (by omega),hL,
    Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hR]
  exact bits_getD _ _

private theorem raw_const {r m : Nat} :
    (fun _ : Data r m => false) ∈ InputSet raw (2*m*r+r+2) ∧
    (fun _ : Data r m => true) ∈ InputSet raw (2*m*r+r+2) :=
  suffix_const (w := fun d : Data r m => rows d.1 ++ rows d.2.1 ++ bits d.2.2)
    (fun d => by simp [rows_length,bits, two_mul,Nat.add_mul,Nat.add_assoc])

private theorem fixed_X {r : Nat} (j : Fin r) :
    (fun d : Finset (Fin r) => decide (j ∈ d)) ∈ InputSet (fun d => bits d ++ [false,true]) (r+2) := by
  apply input_mem (i := j.val) (by have := j.isLt; omega)
  intro d
  rw [List.getD_append _ _ _ _ (by simp [bits])]
  exact bits_getD _ _

private theorem grow_word {α : Type*} {x : α → List Bool} {N p b r m l : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) (a f : Fin m → Nat) (Z O : α → Fin m → Finset (Fin r))
    (U : α → Finset (Fin r)) (w : Fin l → Fin m)
    (hz : ∀ i j, (fun d => decide (j ∈ Z d i)) ∈ S)
    (ho : ∀ i j, (fun d => decide (j ∈ O d i)) ∈ S)
    (hu : ∀ j, (fun d => decide (j ∈ U d)) ∈ S)
    (hf : (fun _ => false) ∈ S) (ht : (fun _ => true) ∈ S) :
    Grow x N p b S (wordCost r l (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i)))
      (fun d => decide (WordTrace (Label a f (Z d) (O d)) (U d) w)) := by
  have ha (i : Fin l) : min r (a (w i)) ≤ Finset.univ.sup (fun j => min r (a j)) :=
    Finset.le_sup (f := fun j => min r (a j)) (Finset.mem_univ (w i))
  have hff (i : Fin l) : min r (f (w i)) ≤ Finset.univ.sup (fun j => min r (f j)) :=
    Finset.le_sup (f := fun j => min r (f j)) (Finset.mem_univ (w i))
  obtain ⟨T,build,st,word⟩ := Tables.grow H (fun d i => Z d (w i)) (fun d i => O d (w i)) U
    (fun i => min r (a (w i))) (fun i => min r (f (w i))) ha hff
    (fun i => hz (w i)) (fun i => ho (w i)) hu hf ht
  refine ⟨T,build,st,?_⟩
  convert word using 1
  funext d
  apply boolOfIff
  exact word_table_equiv a f (Z d) (O d) (U d) w

theorem no_trace_possible {r m b : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (h : ¬ Trace (Label a f Z O) Finset.univ (min (2^b) (r+1)+1)) : Possible b (Label a f Z O) := by
  let x : Finset (Fin r) → List Bool := fun d => bits d ++ [false,true]
  let S := InputSet x (r+2)
  have H : Built x (r+2) 0 0 S := Built.start (fun d => by simp [x,bits])
  obtain ⟨hf,ht⟩ := suffix_const (n := r) (w := bits (r := r)) (fun d => by simp [bits])
  obtain ⟨D,out,v,lt,neg,_,_,ok⟩ := realize (b := b) a f (fun _ => Z) (fun _ => O) id H ht hf (by
    intro p T l U eq hh st w
    apply grow_word hh a f (fun _ => Z) (fun _ => O) U w
    · intro i j; exact st (val_or_const ht hf _)
    · intro i j; exact st (val_or_const ht hf _)
    · intro j
      rcases eq with rfl | rfl
      · exact st (fixed_X j)
      · exact st (val_or_const ht hf _)
    · exact st hf
    · exact st ht)
  exact ⟨D,out,v,lt,neg,fun X => ok X h⟩

end PEqualNP.Outside.L_lib_1420_aux.Boxes

namespace PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem mark_count (C : Circuit) :
    (C.gates.filter mark).length = PEqualNP.NotBracket.notCount C := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases eq : g.op <;> simp [mark,eq]

theorem ordered_refl (x : List Bool) : ordered x x := ⟨rfl, fun _ h => h⟩

theorem ordered_append {a b c d : List Bool} (h1 : ordered a b) (h2 : ordered c d) :
    ordered (a++c) (b++d) := by
  refine ⟨by simp [h1.1,h2.1],?_⟩
  intro i
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (h1.1 ▸ h)]
    exact h1.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [←h1.1]; omega),←h1.1]
    exact h2.2 _

theorem ordered_ofFn {r : Nat} {f g : Fin r → Bool} (fg : ∀ j, f j = true → g j = true) :
    ordered (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i < r
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using fg ⟨i,h⟩
  · simp [List.getD_eq_getElem?_getD,h]

theorem dn_top (l : List Bool) (a : Nat) (h : driverNumber l < 2^a) :
    ∀ i, i + a < l.length → l.getD i false = true := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
    intro i hi
    simp only [List.length_cons] at hi
    have hb : driverNumber bs < 2^a := by
      simp only [driverNumber] at h
      omega
    cases i with
    | zero =>
      cases b
      · exfalso
        have : 2^a ≤ 2^bs.length := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp [driverNumber] at h
        omega
      · simp
    | succ i => simpa using ih hb i (by omega)

theorem dn_step (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) (t : Nat) (h1 : (run gs a).getD t false = true)
    (h2 : (run gs b).getD t false = false) :
    driverNumber (code gs a) + 1 ≤ driverNumber (code gs b) := by
  have mono := driver_mono gs ops ab
  by_contra hh
  have eq : driverNumber (code gs a) = driverNumber (code gs b) := by omega
  have same := driver_injective (by simp [code_len]) eq
  have := (output_order ops ab same).2 t h1
  rw [h2] at this
  exact Bool.noConfusion this

theorem head_true (C : Circuit) (ops : ∀ g∈C.gates, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    (a L : Nat) (z : Nat → List Bool) (ord : ∀ i, i < L → ordered (z i) (z (i+1)))
    (fall : ∀ i, i < L → ∃ t, (run C.gates (z i)).getD t false = true ∧
      (run C.gates (z (i+1))).getD t false = false)
    (hL : 2^PEqualNP.NotBracket.notCount C ≤ L + 2^a) (z' : List Bool) (o' : ordered z' (z 0)) :
    ∀ i, i + a < PEqualNP.NotBracket.notCount C → (code C.gates z').getD i false = true := by
  have key : ∀ i, i ≤ L →
      driverNumber (code C.gates (z 0)) + i ≤ driverNumber (code C.gates (z i)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨t,h1,h2⟩ := fall i (by omega)
      have s1 := dn_step _ ops (ord i (by omega)) t h1 h2
      have s2 := ih (by omega)
      omega
  have h1 := key L le_rfl
  have h2 := driver_bound (code C.gates (z L))
  rw [code_len,mark_count] at h2
  have h3 := driver_mono C.gates ops o'
  intro i hi
  apply dn_top _ a (by omega)
  rw [code_len,mark_count]
  exact hi

theorem run_append (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := by
  simp [run,List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    show (run gs (tick w g)).length = _
    rw [ih]
    simp [tick]
    omega

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem getD_run (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    show (run gs (tick w g)).getD i false = _
    rw [ih _ (by simp [tick]; omega)]
    simp only [tick]
    rw [List.getD_append _ _ _ _ h]

theorem getD_snoc_length (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem wire_gate (C : Circuit) (n : Nat) (back : ReadsBack n C) (xs : List Bool) (len : xs.length=n)
    (a : Nat) (ha : a < C.size) :
    (C.wires xs).getD (n+a) false =
      (gateAt C a).op.eval ((gateAt C a).inputs.map (fun i => (C.wires xs).getD i false)) := by
  let front := C.gates.take a
  let rest := C.gates.drop (a+1)
  let g := gateAt C a
  have geta : g=C.gates[a] := by simp [g,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  have split : C.gates=(front++[g])++rest := by
    rw [geta,←List.take_succ_eq_append_getElem ha,List.take_append_drop]
  have whole : C.wires xs=run rest (run [g] (run front xs)) := by
    change run C.gates xs=_
    conv_lhs => rw [split,run_append,run_append]
  have fw : (run front xs).length=n+a := by
    simp [run_length,front,len,List.length_take,Nat.min_eq_left (show a ≤ C.gates.length by exact ha.le)]
  have sw : (run [g] (run front xs)).length=n+a+1 := by rw [run_length,fw]; simp
  have old (i) (hi : i∈g.inputs) : (C.wires xs).getD i false=(run front xs).getD i false := by
    have good := back a ha i hi
    rw [whole,getD_run _ _ _ (sw ▸ (by omega)),getD_run _ _ _ (fw ▸ good)]
  change _=g.op.eval _
  rw [whole,getD_run _ _ _ (sw ▸ (by omega)),run_singleton,←fw,getD_snoc_length]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (old i hi).symm.trans (by rw [whole,run_singleton])

def remap (ρ : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem gateAt_map (gs : List Gate) (o : Nat) (ρ : Nat → Nat) (j : Nat) :
    gateAt ⟨gs.map (remap ρ), o⟩ j = remap ρ (gateAt ⟨gs, o⟩ j) := by
  simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases gs[j]? <;> simp [remap]

theorem notCount_map (gs : List Gate) (o o' : Nat) (ρ : Nat → Nat) :
    PEqualNP.NotBracket.notCount ⟨gs.map (remap ρ), o⟩ = PEqualNP.NotBracket.notCount ⟨gs, o'⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_map,List.length_map]
  rfl

def rho (n r t : Nat) : Nat := if t < n then t else if t < n+r+1 then n else t - r

theorem tail_getD (r k : Nat) :
    (List.replicate r false ++ [false,true]).getD k false = decide (k = r+1) := by
  induction r generalizing k with
  | zero => rcases k with _|_|k <;> simp
  | succ r ih =>
    cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ,List.getD_eq_getElem?_getD] using ih k

theorem inputs_agree (n r : Nat) (u : List Bool) (hu : u.length = n) (t : Nat) (ht : t < n+r+2) :
    (u ++ [false,true]).getD (rho n r t) false =
      (u ++ List.replicate r false ++ [false,true]).getD t false := by
  by_cases h1 : t < n
  · have : rho n r t = t := by unfold rho; simp [h1]
    rw [this,List.append_assoc,List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
  · have h0 := tail_getD 0 (rho n r t - n)
    simp only [List.replicate_zero,List.nil_append] at h0
    rw [List.append_assoc,List.getD_append_right _ _ _ _ (by unfold rho; split_ifs <;> omega),
      List.getD_append_right _ _ _ _ (by omega),hu,h0,tail_getD]
    congr 1
    simp only [eq_iff_iff]
    unfold rho
    split_ifs <;> omega

def valid (N : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C ∧ C.output < N + C.size

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (tick w g) := rfl

theorem code_append (a b : List Gate) (w : List Bool) :
    code (a++b) w = code a w ++ code b (run a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g a ih => cases h : g.op <;> simp [code,h,ih,run_cons]

theorem code_at' (a : List Gate) (g : Gate) (b : List Gate) (w : List Bool) (gop : g.op = .not) :
    (code (a ++ g :: b) w).getD (a.filter mark).length false =
      (run (a ++ g :: b) w).getD (w.length + a.length) false := by
  rw [code_append,List.getD_append_right _ _ _ _ (by rw [code_len]),code_len,Nat.sub_self,
    run_append,run_cons,getD_run _ _ _ (by simp [tick,run_length]),tick,←run_length,
    getD_snoc_length]
  simp [code,gop,tick]

end PEqualNP.Outside.L_lib_1420_aux.Drivers

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy
open scoped Classical

def tagRow (s e j : ℕ) := Finset.Ico s (s+(2*e+1)*j)

theorem tagsFit (s e h b : ℕ) (P : Fin (h+1) → Finset ℕ)
    (payload : ∀i,P i⊆Finset.range s) (room : h+1≤2^b) :
    let r := s+(2*e+1)*(h+1)
    Fit (fun i => P i∪tagRow s e i.val) r e e b (budget h e e) (Finset.Ico s r) := by
  classical
  let r := s+(2*e+1)*(h+1)
  let W (i : Fin (h+1)) := tagRow s e i.val
  let V := Finset.Ico s r
  let B (i : Fin h) := Finset.Ico (s+(2*e+1)*i.val) (s+(2*e+1)*(i.val+1))
  have bound (i : Fin (h+1)) : s+(2*e+1)*i.val ≤ r := Nat.add_le_add_left (Nat.mul_le_mul_left _ i.isLt.le) _
  have seen (i) : W i⊆V := by
    intro x hx
    have ⟨a,c⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_Ico.mpr ⟨a,c.trans_le (bound i)⟩
  have ins (i) : W i⊆Finset.range r := fun x hx => Finset.mem_range.mpr (Finset.mem_Ico.mp (seen i hx)).2
  have mono : Monotone W := by
    intro i j le x hx
    obtain ⟨a,c⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_Ico.mpr ⟨a,c.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left _ le) _)⟩
  have parts (i) : B i⊆ W i.succ\W i.castSucc := by
    intro x hx
    have ⟨l,u⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,u⟩,fun hh => (Finset.mem_Ico.mp hh).2.not_ge l⟩
  have sizes (i) : (B i).card=e+e+1 := by simp [B,Nat.mul_add]; omega
  obtain ⟨D,out,valid,indices,neg,cost,decode⟩ := build ins mono room B parts
    (fun i x hx => seen _ (Finset.mem_sdiff.mp (parts i hx)).1) sizes
  refine ⟨D,out,valid,indices,neg,cost,?_⟩
  intro i Y sub near j
  have silent : Disjoint (P i) V := by
    apply Finset.disjoint_left.mpr
    intro x px vx
    exact (Finset.mem_range.mp (payload i px)).not_ge (Finset.mem_Ico.mp vx).1
  have n : Near e e (W i) (Y∩V) := by
    obtain ⟨lost,gained⟩ := near
    constructor
    · apply le_trans (Finset.card_le_card (t:=(P i∪W i)\Y) _) lost
      intro x hx
      obtain ⟨wx,no⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ wx,fun y => no (Finset.mem_inter.mpr ⟨y,seen i wx⟩)⟩
    · apply le_trans (Finset.card_le_card (t:=Y\(P i∪W i)) _) gained
      intro x hx
      obtain ⟨obs,miss⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨y,v⟩ := Finset.mem_inter.mp obs
      exact Finset.mem_sdiff.mpr ⟨y,fun h => (Finset.mem_union.mp h).elim
        (fun px => Finset.disjoint_left.mp silent px v) miss⟩
  simpa [Finset.inter_assoc] using decode i (Y∩V) (Finset.inter_subset_left.trans sub) n j
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy PEqualNP.CircuitLowerBounds
open scoped Classical

def FitN (W : Fin m → Finset ℕ) (r a f b p : ℕ) (V : Finset ℕ) :=
  ∃ (D : Circuit) (out : Fin m → ℕ), Valid r D ∧ (∀i,out i<r+2+D.size) ∧
    PEqualNP.NotBracket.notCount D≤b ∧ D.size-PEqualNP.NotBracket.notCount D≤p ∧
    ∀ i Y,Y⊆Finset.range r → Near a f (W i) Y → ∀j,
      (D.wires (input r (Y∩V))).getD (out j) false=decide (i=j)

theorem tagGeneral (m s e b : ℕ) (pos : 0 < m) (room : m≤2^b) (P : Fin m → Finset ℕ)
    (sub : ∀i, P i⊆Finset.range s) :
    let r := s+(2*e+1)*m
    FitN (fun i => P i∪tagRow s e i.val) r e e b
      (16*m*((2*e+1)*(e+1)+1)) (Finset.Ico s r) := by
  cases m with
  | zero => omega
  | succ h =>
    have fits := tagsFit s e h b P sub room
    have eq : budget h e e=16*(h+1)*((2*e+1)*(e+1)+1) := by simp [budget,two_mul]
    rw [←eq]
    exact fits

def plain (C : Finset ℕ) (F : Fin l → Finset ℕ) (j : ℕ) :=
  if j<2 then C else if u : (j-2)/2 < l then F ⟨(j-2)/2,u⟩ else ∅
def payload (H s : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (j : Fin (2*(H+1))) :=
  if j.val≤H then plain C F j.val else Finset.range s\plain R G (H-(j.val-(H+1)))

theorem slackDecoder (a e s : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (c : C⊆Finset.range s) (rows : ∀i,F i⊆Finset.range s) :
    let H := 2^a
    let M := 2*(H+1)
    let r := s+(2*e+1)*M
    let W := fun j : Fin M => payload H s C R F G j ∪ tagRow s e j.val
    FitN W r e e (a+1+1) (16*M*((2*e+1)*(e+1)+1)) (Finset.Ico s r) := by
  dsimp only
  apply tagGeneral
  · positivity
  · have := Nat.two_pow_pos a
    rw [pow_succ,pow_succ]
    omega
  · intro i
    unfold payload
    split
    · unfold plain
      split
      · exact c
      · split
        · exact rows _
        · exact Finset.empty_subset _
    · exact Finset.sdiff_subset
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy
open PEqualNP.Outside.L_lib_1420_aux.Noisy.Gates
open scoped Classical

def Witness (A : Finset ℕ) (F : Fin l → Finset ℕ) (e : ℕ) (T : Finset ℕ) :=
  T⊆A ∧ T.card=e ∧ ∀i, Near e e (F i) T

theorem plainNear {A T : Finset ℕ} {F : Fin l → Finset ℕ} (h : Witness A F e T) (sz : A.card=2*e) (j : ℕ) :
    Near e e (plain A F j) T := by
  obtain ⟨sub,card,rows⟩ := h
  unfold plain
  split
  · constructor
    · rw [Finset.card_sdiff_of_subset sub,sz,card]; omega
    · simp [Finset.sdiff_eq_empty_iff_subset.mpr sub]
  · split
    · exact rows _
    · simp [Near,card]

theorem plainSub (a : A⊆V) (rows : ∀i,F i⊆V) (j : ℕ) : plain A F j⊆V := by
  unfold plain
  split
  · exact a
  · split
    · exact rows _
    · exact Finset.empty_subset _

theorem complementNear {A B T : Finset ℕ} (sa : A⊆T) (sb : B⊆T) (h : Near e e A B) :
    Near e e (T\A) (T\B) := by
  have ex (a b : Finset ℕ) (bs : b⊆T) : (T\a)\(T\b)=b\a := by
    ext x
    simp only [Finset.mem_sdiff]
    have : x∈b → x∈T := fun hx => bs hx
    tauto
  simpa [Near,ex _ _ sa,ex _ _ sb] using And.intro h.2 h.1

theorem tagNear {A B : Finset ℕ} (T : Finset ℕ) (h : Near e e A B) :
    Near e e (A∪T) (B∪T) := by
  have incl (a b : Finset ℕ) : (a∪T)\(b∪T) ⊆ a\b := by
    intro x hx
    simp only [Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  exact ⟨(Finset.card_le_card (incl _ _)).trans h.1,(Finset.card_le_card (incl _ _)).trans h.2⟩

theorem pathBound {W Y : Fin m → Finset ℕ} (fit : FitN W r e e b p (Finset.range r))
    (mono : Monotone Y) (within : ∀i,Y i⊆Finset.range r) (near : ∀i,Near e e (W i) (Y i)) :
    m≤2^b := by
  obtain ⟨D,out,valid,_,negs,_,ev⟩ := fit
  obtain ⟨rank,mon,bound,stable⟩ := MarkedInversionRank.circuit_rank (n:=r) D valid.1
  let v (i : Fin m) (j : Fin r) := decide (j.val∈Y i)
  have vm : Monotone v := by
    intro i k le j
    apply Bool.le_iff_imp.mpr
    simpa [v] using (fun h => mono le h : j.val∈Y i → j.val∈Y k)
  have en (i j) : (D.wires (input r (Y i))).getD (out j) false=decide (i=j) := by
    simpa only [Finset.inter_eq_left.mpr (within i)] using ev i _ (within i) (near i) j
  have inc : StrictMono (fun i => rank (v i)) := by
    intro i j lt
    apply lt_of_le_of_ne (mon (vm lt.le))
    intro eq
    have one := en i i
    have still := stable _ _ (vm lt.le) eq (out i) (by simpa [v,input] using one)
    change (D.wires (input r (Y j))).getD (out i) false=true at still
    exact lt.ne.symm (of_decide_eq_true ((en j i).symm.trans still))
  let f (i : Fin m) : Fin (2^b) := ⟨rank (v i),(bound _).trans_le (Nat.pow_le_pow_right (by decide) negs)⟩
  simpa using Fintype.card_le_of_injective f (fun _ _ eq => inc.injective (congrArg Fin.val eq))

theorem forbidDisjoint (a e s : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (csub : C⊆Finset.range s) (rsub : R⊆Finset.range s) (cs : C.card=2*e) (rs : R.card=2*e)
    (gs : ∀i,G i⊆Finset.range s) (T U : Finset ℕ) (wt : Witness C F e T) (wu : Witness R G e U) :
    let H := 2^a
    let M := 2*(H+1)
    let r := s+(2*e+1)*M
    let W := fun j : Fin M => payload H s C R F G j ∪ tagRow s e j.val
    FitN W r e e (a+1) p (Finset.range r) → ¬Disjoint T U := by
  classical
  intro H M r W fit dis
  let core (j : Fin M) := if j.val≤H then T else Finset.range s\U
  let Y (j : Fin M) := core j ∪ tagRow s e j.val
  have ts := wt.1.trans csub
  have us := wu.1.trans rsub
  have cross : T⊆Finset.range s\U := fun x hx =>
    Finset.mem_sdiff.mpr ⟨ts hx,Finset.disjoint_left.mp dis hx⟩
  have cm : Monotone core := by
    intro i j le
    by_cases hi : i.val≤H <;> by_cases hj : j.val≤H <;> simp [core,hi,hj,cross]
    omega
  have ym : Monotone Y := by
    intro i j le
    apply Finset.union_subset_union (cm le)
    intro x hx
    obtain ⟨low,high⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_Ico.mpr ⟨low,high.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left _ le) _)⟩
  have inside (i : Fin M) : Y i⊆Finset.range r := by
    apply Finset.union_subset
    · have small : core i⊆Finset.range s := by unfold core; split; exact ts; exact Finset.sdiff_subset
      exact small.trans (Finset.range_mono (by dsimp [r]; omega))
    · intro x hx
      exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hx).2.trans_le
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ i.isLt.le) _))
  have n (i : Fin M) : Near e e (W i) (Y i) := by
    apply tagNear
    change Near e e (payload H s C R F G i) (core i)
    by_cases hi : i.val≤H
    · simpa [payload,core,hi] using plainNear wt cs i.val
    · simp only [payload,core,hi,ite_false]
      exact complementNear (plainSub rsub gs _) us (plainNear wu rs _)
  have cap := pathBound fit ym inside n
  dsimp [M,H] at cap
  rw [pow_succ] at cap
  omega
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy

theorem rowOrder {s e i j : ℕ} {P Q X Y : Finset ℕ}
    (qs : Q⊆Finset.range s) (xy : X⊆Y)
    (ix : Near e e (P∪tagRow s e i) X) (jy : Near e e (Q∪tagRow s e j) Y) : i ≤ j := by
  by_contra! bad
  let B := Finset.Ico (s+(2*e+1)*j) (s+(2*e+1)*(j+1))
  have inc : B⊆((P∪tagRow s e i)\X)∪(Y\(Q∪tagRow s e j)) := by
    intro x hx
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hx
    have top := Nat.mul_le_mul_left (2*e+1) (show j + 1  ≤  i by omega)
    have q : x∉Q := fun h => (Finset.mem_range.mp (qs h)).not_ge (by omega)
    have t : x∉tagRow s e j := fun h => (Finset.mem_Ico.mp h).2.not_ge lo
    by_cases h : x∈X
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨xy h,fun z => (Finset.mem_union.mp z).elim q t⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩),h⟩)
  have card : B.card=2*e+1 := by simp [B,Nat.mul_add]; omega
  have h := (Finset.card_le_card inc).trans (Finset.card_union_le ..)
  have lose := ix.1
  have gain := jy.2
  omega

theorem projectNear {s e j : ℕ} {P Y : Finset ℕ} (ps : P⊆Finset.range s)
    (n : Near e e (P∪tagRow s e j) Y) : Near e e P (Y∩Finset.range s) := by
  constructor
  · apply le_trans (Finset.card_le_card (t:=(P∪tagRow s e j)\Y) _) n.1
    intro x hx
    obtain ⟨p,miss⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ p,fun y => miss (Finset.mem_inter.mpr ⟨y,ps p⟩)⟩
  · apply le_trans (Finset.card_le_card (t:=Y\(P∪tagRow s e j)) _) n.2
    intro x hx
    obtain ⟨y,miss⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨y,small⟩ := Finset.mem_inter.mp y
    exact Finset.mem_sdiff.mpr ⟨y,fun h => (Finset.mem_union.mp h).elim miss
      (fun z => (Finset.mem_range.mp small).not_ge (Finset.mem_Ico.mp z).1)⟩

theorem frozenPayload {C A B : Finset ℕ} (cs : C.card=2*e) (ab : A⊆B)
    (early : Near e e C A) (late : Near e e ∅ B) : A=B ∧ A⊆C ∧ A.card=e := by
  have ub : B.card ≤ e := by simpa using late.2
  have diff := early.1
  have union : C ⊆ (C\A)∪(C∩A) := by intro x hx; by_cases h : x∈A <;> simp [hx,h]
  have bound := (Finset.card_le_card union).trans (Finset.card_union_le ..)
  have ca := Finset.card_le_card (Finset.inter_subset_right (s₁:=C) (s₂:=A))
  have ac := Finset.card_le_card ab
  have eq : C∩A=A := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact ⟨Finset.eq_of_subset_of_card_le ab (by omega),fun x hx => Finset.mem_inter.mp (eq.symm ▸ hx) |>.1,by omega⟩

theorem halfWitness (C : Finset ℕ) (F : Fin l → Finset ℕ) (Y : ℕ → Finset ℕ)
    (cs : C.card=2*e) (a : ℕ → ℕ) (mono : ∀ i j, i ≤ j → j ≤ 2*l+2 → Y i⊆Y j)
    (slot : ∀i, i ≤ 2*l+2 → i ≤ a i ∧ a i ≤ i+1)
    (near : ∀i, i ≤ 2*l+2 → Near e e (plain C F (a i)) (Y i)) :
    Witness C F e (Y 0) := by
  have sb := slot 0 (by omega)
  have first : plain C F (a 0)=C := if_pos (by omega)
  have se := slot (2*l+2) (by omega)
  have last : plain C F (a (2*l+2))=∅ := by
    unfold plain
    rw [if_neg (by omega),dif_neg (by omega)]
  have early := first ▸ near 0 (by omega)
  have late := last ▸ near (2*l+2) (by omega)
  obtain ⟨eq,sub,sz⟩ := frozenPayload cs (mono 0 _ (by omega) (by omega)) early late
  refine ⟨sub,sz,?_⟩
  intro i
  let k := 2*i.val+2
  have kl : k ≤ 2*l+2 := by dsimp [k]; have := i.isLt; omega
  obtain ⟨lo,hi⟩ := slot k kl
  have mid : (a k-2)/2=i.val := by dsimp [k] at lo hi ⊢; omega
  have row : plain C F (a k)= F i := by
    unfold plain
    rw [if_neg (by dsimp [k] at lo ⊢; omega),dif_pos (mid ▸ i.isLt)]
    congr 1
    exact Fin.ext mid
  have same : Y k=Y 0 := le_antisymm (eq.symm ▸ mono k _ kl (by omega)) (mono 0 k (by omega) kl)
  simpa only [row,same] using near k kl

theorem almostFull {n : ℕ} (f : Fin n → Fin (n+1)) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ (f i).val ∧ (f i).val ≤ i.val+1 := by
  have grow (p q : Fin n) (h : p ≤ q) : (f p).val+(q.val-p.val) ≤ (f q).val := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show p.val ≤ q.val from h)
    have go : ∀k (hk : p.val+k < n), (f p).val+k ≤ (f ⟨p.val+k,hk⟩).val := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have hi := ih (by omega)
        have step := hf (show (⟨p.val+k,by omega⟩ : Fin n) < ⟨p.val+(k+1),hk⟩ from by apply Fin.mk_lt_mk.mpr; omega)
        change (f _).val < (f _).val at step
        omega
    have z := go d (hd ▸ q.isLt)
    have same : (⟨p.val+d,hd ▸ q.isLt⟩ : Fin n)=q := Fin.ext hd.symm
    rw [same] at z
    omega
  have pos := i.isLt
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have lo := grow first i (by apply Fin.mk_le_mk.mpr; omega)
  have hi := grow i last (by apply Fin.mk_le_mk.mpr; omega)
  have lastBound := (f last).isLt
  change (f first).val + (i.val-0)  ≤  (f i).val at lo
  change (f i).val + (n-1-i.val)  ≤  (f last).val at hi
  omega
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy
theorem traceWitness (H s e : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (csub : C ⊆ Finset.range s) (rsub : R ⊆ Finset.range s)
    (fs : ∀i,F i ⊆ Finset.range s) (gs : ∀i,G i ⊆ Finset.range s)
    (cs : C.card=2*e) (rs : R.card=2*e) (wide : 2*(l+2) ≤ H+1) (widg : 2*(m+2) ≤ H+1)
    (w : Fin (2*H+1) → Fin (2*(H+1))) (Y : Fin (2*H+1) → Finset ℕ)
    (ym : Monotone Y) (adj : ∀ i j : Fin (2*H+1),i.val+1=j.val → w i ≠ w j)
    (near : ∀ i,Near e e (payload H s C R F G (w i)∪tagRow s e (w i).val) (Y i)) :
    ∃T U, Witness C F e T ∧ Witness R G e U ∧ Disjoint T U := by
  let S := Finset.range s
  have sub (i) : payload H s C R F G (w i) ⊆ S := by
    unfold payload
    split
    · exact plainSub csub fs _
    · exact Finset.sdiff_subset
  have sm : StrictMono w := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact lt_of_le_of_ne (rowOrder (sub _) (ym (Fin.castSucc_le_succ i)) (near _) (near _)) (adj _ _ rfl)
  have room (i) : i.val ≤ (w i).val ∧ (w i).val ≤ i.val+1 := by
    let f (u : Fin (2*H+1)) : Fin ((2*H+1)+1) := ⟨(w u).val,by have := (w u).isLt; omega⟩
    exact almostFull f (fun _ _ lt => sm lt) i
  let P (i) := Y i∩S
  have pm : Monotone P := fun _ _ le => Finset.inter_subset_inter_right (ym le)
  have pn (i) : Near e e (payload H s C R F G (w i)) (P i) := projectNear (sub i) (near i)
  let iL (k : ℕ) : Fin (2*H+1) := ⟨min k (2*H),by omega⟩
  let iR (k : ℕ) : Fin (2*H+1) := ⟨2*H-k,by omega⟩
  let Q (k : ℕ) := S\P (iR k)
  have leftSlot (k : ℕ) (hk : k ≤ 2*l+2) :
      k ≤ (w (iL k)).val ∧ (w (iL k)).val ≤ k+1 := by
    have h := room (iL k)
    simpa [iL,Nat.min_eq_left (by omega : k ≤ 2*H)] using h
  have left := halfWitness C F (fun k => P (iL k)) cs (fun k => (w (iL k)).val)
    (fun i j h _ => pm (show iL i ≤ iL j from min_le_min_right _ h)) leftSlot (by
      intro k hk
      have z := leftSlot k hk
      simpa [payload,show (w (iL k)).val ≤ H by omega] using pn (iL k))
  let aR (k : ℕ) := H-((w (iR k)).val-(H+1))
  have ar (k : ℕ) (hk : k ≤ 2*m+2) : k ≤ aR k ∧ aR k ≤ k+1 := by
    have h := room (iR k)
    change 2*H-k ≤ _ ∧ _ ≤ (2*H-k)+1 at h
    dsimp [aR]; omega
  have right := halfWitness R G Q rs aR (by
    intro i j le _
    exact Finset.sdiff_subset_sdiff (fun _ h => h) (pm (show iR j ≤ iR i from Nat.sub_le_sub_left le _))) ar (by
    intro k hk
    have h := room (iR k)
    change 2*H-k ≤ _ ∧ _ ≤ (2*H-k)+1 at h
    have z : Near e e (S\plain R G (aR k)) (P (iR k)) := by
      simpa [payload,aR,show ¬ (w (iR k)).val ≤ H by omega,S] using pn (iR k)
    have c := complementNear (show S\plain R G (aR k) ⊆ S from Finset.sdiff_subset) (Finset.inter_subset_right (s₁:=Y (iR k)) (s₂:=S)) z
    have eq : S\(S\plain R G (aR k))=plain R G (aR k) := by
      have ss := plainSub rsub gs (aR k)
      ext x
      simp only [Finset.mem_sdiff]
      have h : x∈plain R G (aR k) → x∈S := fun hx => ss hx
      tauto
    simpa only [eq,Q] using c)
  refine ⟨_,_,left,right,Finset.disjoint_left.mpr ?_⟩
  intro x xt xu
  exact (Finset.mem_sdiff.mp xu).2 (pm (show iL 0 ≤ iR 0 from by change min 0 _ ≤ 2*H-0; omega) xt)
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy
open scoped Classical
namespace Box
abbrev coords (r : ℕ) (W : Finset ℕ) := Finset.univ.filter (fun i : Fin r => i.val∈W)
abbrev vals {r : ℕ} (X : Finset (Fin r)) := X.map Fin.valEmbedding
theorem roundTrip {W : Finset ℕ} (h : W ⊆ Finset.range r) : vals (coords r W)=W := by
  ext x
  simp only [vals,coords,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,Fin.valEmbedding_apply]
  constructor
  · rintro ⟨v,h,rfl⟩; exact h
  · intro hx; exact ⟨⟨x,Finset.mem_range.mp (h hx)⟩,hx,rfl⟩

open PEqualNP.Outside.L_lib_1420_aux.Boxes (Label Possible no_trace_possible Trace bits labelBit)

theorem nearVals {A B : Finset (Fin r)} :
    PEqualNP.Outside.L_lib_1420_aux.Boxes.Near e e A B ↔ Near e e (vals A) (vals B) := by
  simp [PEqualNP.Outside.L_lib_1420_aux.Boxes.Near,Near,vals,←Finset.map_sdiff]

theorem boxLabel (W : Fin m → Finset ℕ) (hr : ∀i,W i ⊆ Finset.range r) (X : Finset (Fin r)) (i) :
    Label (fun _ => e) (fun _ => e) (fun j => Finset.univ\coords r (W j)) (fun j => coords r (W j)) X i ↔
      Near e e (W i) (vals X) := by
  let O := coords r (W i)
  have same := roundTrip (hr i)
  constructor
  · rintro ⟨C,h₁,h₂,h⟩
    have eq : C=O := Finset.Subset.antisymm h₂ (by
      intro x hx; by_contra miss
      exact (Finset.mem_sdiff.mp (h₁ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,miss⟩))).2 hx)
    simpa only [eq,O,same] using nearVals.mp h
  · intro h
    exact ⟨O,fun _ z => z,fun _ z => z,nearVals.mpr (by simpa only [O,same] using h)⟩

theorem abstractFit (W : Fin m → Finset ℕ) (hr : ∀i,W i ⊆ Finset.range r) (le : 2^b ≤ r+1)
    (bad : ∀ (w : Fin (2^b+1) → Fin m) (Y : Fin (2^b+1) → Finset ℕ), Monotone Y →
      (∀ i j : Fin (2^b+1), i.val+1=j.val → w i ≠ w j) → (∀i,Near e e (W (w i)) (Y i)) → False) :
    ∃p,FitN W r e e b p (Finset.range r) := by
  let Z (i) := Finset.univ\coords r (W i)
  let O (i) := coords r (W i)
  obtain ⟨D,out,valid,lt,neg,ok⟩ := no_trace_possible (b:=b) (fun _ => e) (fun _ => e) Z O (by
    rw [Nat.min_eq_left le]
    rintro ⟨w,adj,Y,mono,_,near⟩
    exact bad w (fun i => vals (Y i)) (fun _ _ h => Finset.map_subset_map.mpr (mono h)) adj
      (fun i => (boxLabel W hr _ _).mp (near i)))
  refine ⟨_,D,out,valid,lt,neg,le_rfl,?_⟩
  intro i Y sub near j
  have obs : PEqualNP.Outside.L_lib_1420_aux.Boxes.bits (coords r Y) ++ [false,true]=input r (Y∩Finset.range r) := by
    rw [Finset.inter_eq_left.mpr sub]
    unfold bits input
    congr 2
    funext x
    exact Bool.eq_iff_iff.mpr (by simp [coords])
  have right : labelBit i j=decide (i=j) := Bool.eq_iff_iff.mpr (by simp [labelBit])
  rw [←obs,←right]
  apply ok _ i _ j
  exact (boxLabel W hr _ _).mpr (by simpa only [roundTrip sub] using near)
end Box
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux.Noisy
theorem tightIff (a e s : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (csub : C ⊆ Finset.range s) (rsub : R ⊆ Finset.range s)
    (fs : ∀i,F i ⊆ Finset.range s) (gs : ∀i,G i ⊆ Finset.range s)
    (cs : C.card=2*e) (rs : R.card=2*e) (wide : 2*(l+2) ≤ 2^a+1) (widg : 2*(m+2) ≤ 2^a+1) :
    let H := 2^a
    let M := 2*(H+1)
    let r := s+(2*e+1)*M
    let W := fun j : Fin M => payload H s C R F G j ∪ tagRow s e j.val
    (∃p,FitN W r e e (a+1) p (Finset.range r)) ↔
      ∀T U,Witness C F e T → Witness R G e U → ¬ Disjoint T U := by
  intro H M r W
  constructor
  · rintro ⟨p,fit⟩ T U left right
    exact forbidDisjoint a e s C R F G csub rsub cs rs gs T U left right fit
  · intro incompatible
    have sub (j) : W j ⊆ Finset.range r := by
      apply Finset.union_subset
      · have small : payload H s C R F G j ⊆ Finset.range s := by
          unfold payload
          split
          · exact plainSub csub fs _
          · exact Finset.sdiff_subset
        exact small.trans (Finset.range_mono (Nat.le_add_right ..))
      · intro x hx
        have hi := (Finset.mem_Ico.mp hx).2
        exact Finset.mem_range.mpr (hi.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left _ j.isLt.le) _))
    have pow : 2^(a+1)=2*H := by dsimp [H]; rw [pow_succ,Nat.mul_comm]
    apply Box.abstractFit W sub
    · have cap : M ≤ (2*e+1)*M := Nat.le_mul_of_pos_left _ (by omega)
      have idM : M=2*(H+1) := rfl
      dsimp only [r]
      omega
    · rw [pow]
      intro w Y ym adj near
      obtain ⟨T,U,wt,wu,dis⟩ := traceWitness H s e C R F G csub rsub fs gs cs rs wide widg w Y ym adj near
      exact incompatible T U wt wu dis
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.NotBracket (notCount)
theorem rank_split (l : List Gate) (e : Nat) (h : e < (l.filter mark).length) :
    ∃ a g b, l = a ++ g :: b ∧ mark g = true ∧ (a.filter mark).length = e := by
  induction l generalizing e with
  | nil => simp at h
  | cons g l ih =>
    by_cases hm : mark g = true
    · cases e with
      | zero => exact ⟨[], g, l, rfl, hm, rfl⟩
      | succ e =>
        obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
        exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩
    · obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
      exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩

theorem firstCircuit (C : Circuit) (v : valid N C) (pos : 0 < notCount C) (z : ℕ) (hz : z < N) :
    ∃ S : Circuit, valid N S ∧ notCount S=0 ∧ S.size ≤ C.size-notCount C ∧
      ∀ x : List Bool, x.length=N → x.getD z false=false →
        S.eval x = !(code C.gates x).getD 0 false := by
  obtain ⟨a,g,b,eq,mg,na⟩ := rank_split C.gates 0 (by simpa only [mark_count] using pos)
  have op : g.op=.not := by cases h : g.op <;> simp_all [mark]
  have sz : C.size = a.length+1+b.length := by simp [Circuit.size,eq]; omega
  have gp : gateAt C a.length=g := by simp [gateAt,eq,List.getD_append_right _ _ _ _ le_rfl]
  have gs (i) (h : i∈g.inputs) : i<N+a.length := v.2.1 a.length (by simp [eq]) i (gp ▸ h)
  let o := g.inputs.headD z
  let S : Circuit := ⟨a,o⟩
  have vS : valid N S := by
    refine ⟨fun h hh => v.1 h (by rw [eq]; exact List.mem_append_left _ hh),?_,?_⟩
    · intro j hj i hi
      have same : gateAt C j=gateAt S j := by
        unfold gateAt
        rw [eq,List.getD_append _ _ _ _ (show j < a.length from hj)]
      apply v.2.1 j (by simp [eq]; change j<a.length at hj; omega) i (same ▸ hi)
    · change g.inputs.headD z<N+a.length
      cases h : g.inputs with
      | nil => simp; omega
      | cons i t => exact gs i (by simp [h])
  have countS : notCount S=0 := (mark_count _).symm.trans na
  have cost : S.size ≤ C.size-notCount C := by
    have nb := List.length_filter_le mark b
    have nc : notCount C=(b.filter mark).length+1 := by
      rw [←mark_count,eq,List.filter_append,List.length_append,na]
      simp [List.filter_cons,mg]
    change a.length ≤ _
    omega
  refine ⟨S,vS,countS,cost,?_⟩
  intro x hx h0
  have noCode : code a x=[] := List.length_eq_zero_iff.mp ((code_len a x).trans na)
  rw [eq,code_append,noCode,List.nil_append]
  simp only [PEqualNP.Outside.L_lib_1420_aux.Drivers.code,op,List.getD_cons_zero]
  change (run a x).getD o false = !((GateOp.not).eval (g.inputs.map fun i => (run a x).getD i false))
  cases h : g.inputs with
  | nil => simpa [o,h,GateOp.eval] using (getD_run a x z (hx ▸ hz)).trans h0
  | cons i t => simp [o,h,GateOp.eval]
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1420_aux.Noisy PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.NotBracket (notCount)
def pinMap (s r t k : ℕ) :=
  if k<s then k else if k<r then if k<t then s+1 else s else s+(k-r)
theorem inputAt (s : ℕ) (X : Finset ℕ) (k : ℕ) (h : k<s) :
    (input s X).getD k false=decide (k∈X) := by
  rw [input,List.getD_append _ _ _ _ (by simpa)]
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
theorem inputFalse (s : ℕ) (X : Finset ℕ) : (input s X).getD s false=false := by
  rw [input,List.getD_append_right _ _ _ _ (by simp)]
  simp
theorem inputTrue (s : ℕ) (X : Finset ℕ) : (input s X).getD (s+1) false=true := by
  rw [input,List.getD_append_right _ _ _ _ (by simp)]
  simp
theorem pinsAgree (s r t : ℕ) (sr : s ≤ r) (X : Finset ℕ) (xs : X ⊆ Finset.range s) (k : ℕ) (hk : k<r+2) :
    (input s X).getD (pinMap s r t k) false=(input r (X∪Finset.Ico s t)).getD k false := by
  unfold pinMap
  by_cases small : k<s
  · rw [if_pos small,inputAt _ _ _ small,inputAt _ _ _ (by omega)]
    simp [Finset.mem_Ico,show ¬s ≤ k by omega]
  · rw [if_neg small]
    by_cases var : k<r
    · rw [if_pos var,inputAt _ _ _ var]
      have miss : k∉X := fun z => small (Finset.mem_range.mp (xs z))
      by_cases hi : k<t
      · rw [if_pos hi,inputTrue]
        simp [miss,Finset.mem_Ico,hi,show s ≤ k by omega]
      · rw [if_neg hi,inputFalse]
        simp [miss,Finset.mem_Ico,hi]
    · rw [if_neg var]
      rcases (by omega : k=r ∨ k=r+1) with rfl|rfl
      · simp only [Nat.sub_self,Nat.add_zero,inputFalse]
      · simp only [Nat.add_sub_cancel_left,inputTrue]
theorem pinCircuit (s r t : ℕ) (sr : s ≤ r) (C : Circuit) (hv : valid (r+2) C) :
    ∃ S : Circuit, valid (s+2) S ∧ notCount S=notCount C ∧ S.size=C.size ∧
       ∀X,X ⊆ Finset.range s → S.eval (input s X)=C.eval (input r (X∪Finset.Ico s t)) := by
  obtain ⟨fan,back,hout⟩ := hv
  let ρ := pinMap s r t
  let S : Circuit := ⟨C.gates.map (remap ρ),ρ C.output⟩
  have sz : S.size=C.size := by simp [S,Circuit.size]
  have hg (j) : gateAt S j=remap ρ (gateAt C j) := gateAt_map _ _ _ j
  have hρ (k j : ℕ) (h : k<r+2+j) : ρ k<s+2+j := by
    dsimp [ρ,pinMap]; split_ifs <;> omega
  have hS : ReadsBack (s+2) S := by
    intro j hj i hi
    rw [hg] at hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    exact hρ _ _ (back j (by simpa [S] using hj) k hk)
  refine ⟨S,⟨?_,hS,?_⟩,notCount_map _ _ _ _,sz,?_⟩
  · intro g mem
    obtain ⟨g0,inC,rfl⟩ := List.mem_map.mp mem
    simpa [remap] using fan g0 inC
  · change ρ C.output<s+2+S.size
    rw [sz]
    exact hρ _ _ hout
  · intro X hx
    let x := input s X
    let y := input r (X∪Finset.Ico s t)
    have lx : x.length=s+2 := by simp [x,input]
    have ly : y.length=r+2 := by simp [y,input]
    have key (k) : k<r+2+C.size → (S.wires x).getD (ρ k) false=(C.wires y).getD k false := by
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        by_cases var : k<r+2
        · change (run S.gates x).getD _ _=(run C.gates y).getD _ _
          rw [getD_run _ _ _ (by rw [lx]; exact hρ k 0 var),getD_run _ _ _ (by omega)]
          exact pinsAgree _ _ _ sr X hx k var
        · obtain ⟨j,rfl⟩ : ∃j,k=r+2+j := ⟨k-(r+2),by omega⟩
          have eq : ρ (r+2+j)=s+2+j := by dsimp [ρ,pinMap]; split_ifs <;> omega
          have lj : j<C.gates.length := by change j<C.size; omega
          rw [eq,wire_gate S _ hS x lx j (by rw [sz]; exact lj),wire_gate C _ back y ly j lj,hg]
          simp only [remap,List.map_map]
          congr 1
          apply List.map_congr_left
          intro i m
          have hi := back j lj i m
          exact ih i (by omega) (by omega)
    exact key _ hout
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1420_aux.Noisy PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.NotBracket (notCount)
def Path (D : Circuit) (H : ℕ) (z : ℕ → List Bool) :=
  ∀i,i<H → ordered (z i) (z (i+1)) ∧ ∃k,(run D.gates (z i)).getD k false=true ∧
    (run D.gates (z (i+1))).getD k false=false
theorem forceEndpoint (D : Circuit) (fan : FanInTwo D) (a : ℕ) (cost : notCount D ≤ a+1)
    (z : ℕ → List Bool) (p : Path D (2^a) z) (x : List Bool) :
    (ordered (z (2^a)) x → (code D.gates x).getD 0 false=false) ∧
    (ordered x (z 0) → (code D.gates x).getD 0 false=true) := by
  let H := 2^a
  let rank (v : List Bool) := driverNumber (code D.gates v)
  have ops g (m : g∈D.gates) := (fan g m).1
  have grow (k : ℕ) (hk : k ≤ H) : rank (z 0)+k ≤ rank (z k) := by
    induction k with
    | zero => simp
    | succ i ih =>
      obtain ⟨ord,w,old,new⟩ := p i (by omega)
      have inc := dn_step _ ops ord w old new
      have prev := ih (by omega)
      exact (Nat.add_le_add_right prev 1).trans inc
  have bound (v) : rank v<2^notCount D := by
    simpa only [rank,code_len,mark_count] using driver_bound (code D.gates v)
  have span := grow H le_rfl
  have boundEnd := bound (z H)
  have full : notCount D = a+1 := by
    by_contra neq
    have le : notCount D ≤ a := by omega
    have cap : 2^notCount D ≤ H := Nat.pow_le_pow_right (by decide) le
    omega
  have len : (code D.gates x).length=a+1 := by rw [code_len,mark_count,full]
  constructor
  · intro obs
    have rx : rank (z H) ≤ rank x := driver_mono _ ops obs
    have low : H ≤ driverNumber (code D.gates x) := by change H ≤ rank x; omega
    cases h : code D.gates x with
    | nil => simp_all
    | cons b tail =>
      have lt := driver_bound tail
      have sz : tail.length=a := by simpa [h] using len
      rw [sz] at lt
      rw [h] at low
      cases b <;> simp_all [driverNumber,H] <;> omega
  · intro obs
    have rx : rank x ≤ rank (z 0) := driver_mono _ ops obs
    have cap : 2^notCount D = H+H := by rw [full,pow_succ]; dsimp [H]; omega
    have low : driverNumber (code D.gates x)<2^a := by change rank x<H; omega
    exact dn_top _ a low 0 (by omega)

theorem orderedInput (r : ℕ) {A B : Finset ℕ} (h : A ⊆ B) : ordered (input r A) (input r B) := by
  apply input_order
  intro i yes
  simpa using h (of_decide_eq_true yes)
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1420_aux.Noisy PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.NotBracket (notCount)

theorem receiverPath (D : Circuit) (out : Fin M → ℕ) (H s r e start : ℕ)
    (B : Finset ℕ) (base : B ⊆ Finset.range r) (labels : start+H<M)
    (last : s+(2*e+1)*(start+H) ≤ r)
    (W : Fin M → Finset ℕ)
    (dec : ∀ i Y,Y ⊆ Finset.range r → Near e e (W i) Y → ∀j,
      (D.wires (input r (Y∩Finset.range r))).getD (out j) false=decide (i=j))
    (near : ∀k (hk : k ≤ H),Near e e (W ⟨start+k,by omega⟩) (B∪tagRow s e (start+k))) :
    Path D H (fun k => input r (B∪tagRow s e (start+k))) := by
  let Y (k : ℕ) := B∪tagRow s e (start+k)
  have sub (k) (hk : k ≤ H) : Y k ⊆ Finset.range r := by
    apply Finset.union_subset base
    intro x hx
    exact Finset.mem_range.mpr (((Finset.mem_Ico.mp hx).2.trans_le
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left hk start)) _)).trans_le last)
  have obs (k) (hk : k ≤ H) (j) : (D.wires (input r (Y k))).getD (out j) false=decide ((⟨start+k,by omega⟩ : Fin M)=j) := by
    simpa only [Finset.inter_eq_left.mpr (sub k hk)] using dec _ _ (sub k hk) (near k hk) j
  intro k hk
  refine ⟨orderedInput _ (Finset.union_subset_union (fun _ h => h) ?_),out ⟨start+k,by omega⟩,?_,?_⟩
  · intro x hx
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hx
    exact Finset.mem_Ico.mpr ⟨lo,hi.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : start+k ≤ start+(k+1))) _)⟩
  · change (D.wires (input r (Y k))).getD _ false=true
    simpa using obs k hk.le ⟨start+k,by omega⟩
  · have ne : (⟨start+(k+1),by omega⟩ : Fin M) ≠ ⟨start+k,by omega⟩ := fun eq => by have := congrArg Fin.val eq; simp at this
    change (D.wires (input r (Y (k+1)))).getD _ false=false
    simpa [ne] using obs (k+1) (by omega) ⟨start+k,by omega⟩

theorem readFirst (r : ℕ) (D : Circuit) (v : Valid r D) :
    ∃ S : Circuit, Valid r S ∧ notCount S=0 ∧ S.size ≤ D.size-notCount D ∧
      ∀Y,S.eval (input r Y) = !(code D.gates (input r Y)).getD 0 false := by
  by_cases h : 0 < notCount D
  · obtain ⟨S,vS,n,c,ev⟩ := firstCircuit D v h r (by omega)
    exact ⟨S,vS,n,c,fun Y => ev _ (by simp [input]) (inputFalse _ _)⟩
  · let S : Circuit := ⟨[],r+1⟩
    have good : Valid r S := by
      refine ⟨fun g m => False.elim (List.not_mem_nil m),fun j hj => False.elim (by change j<0 at hj; omega),?_⟩
      simp [S,Circuit.size]
    refine ⟨S,good,rfl,Nat.zero_le _,?_⟩
    intro Y
    have empty : code D.gates (input r Y)=[] := List.length_eq_zero_iff.mp (by rw [code_len,mark_count]; omega)
    simp only [empty,List.getD_nil,Bool.not_false]
    exact inputTrue r Y
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_lib_1420_aux.Noisy PEqualNP.Outside.L_lib_1420_aux.Drivers
open PEqualNP.NotBracket (notCount)
theorem tightSeparator (a e s : ℕ) (C R : Finset ℕ) (F : Fin l → Finset ℕ) (G : Fin m → Finset ℕ)
    (cs : C.card=2*e) (rs : R.card=2*e) (csub : C ⊆ Finset.range s) (rsub : R ⊆ Finset.range s)
    (gs : ∀i,G i ⊆ Finset.range s) :
    let H := 2^a
    let M := 2*(H+1)
    let r := s+(2*e+1)*M
    let W := fun j : Fin M => payload H s C R F G j ∪ tagRow s e j.val
    FitN W r e e (a+1) p (Finset.range r) →
      ∃S : Circuit,Valid s S ∧ notCount S=0 ∧ S.size ≤ p ∧ ∀X,X ⊆ Finset.range s →
        ((∃T,Witness C F e T ∧ T ⊆ X) → S.eval (input s X)=true) ∧
        ((∃U,Witness R G e U ∧ Disjoint X U) → S.eval (input s X)=false) := by
  intro H M r W fit
  obtain ⟨D,out,v,_,neg,cost,ev⟩ := fit
  obtain ⟨A,vA,nA,cA,readA⟩ := readFirst r D v
  have sr : s ≤ r := Nat.le_add_right ..
  let t := s+(2*e+1)*H
  obtain ⟨S,vS,nS,cS,readS⟩ := pinCircuit s r t sr A vA
  refine ⟨S,vS,nS.trans nA,cS.le.trans (cA.trans cost),?_⟩
  intro X xs
  rw [readS X xs,readA]
  let x := input r (X∪tagRow s e H)
  have hi (k) (hk : k ≤ M) : s+(2*e+1)*k ≤ r := Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _
  constructor
  · rintro ⟨T,wt,tx⟩
    let z (k : ℕ) := input r (T∪tagRow s e k)
    have path : Path D H z := by
      have b := receiverPath D out H s r e 0 T ((wt.1.trans csub).trans (Finset.range_mono sr))
        (by dsimp [M]; omega) (hi _ (by dsimp [M]; omega)) W ev (by
        intro k hk
        apply tagNear
        simpa [payload,hk] using plainNear wt cs k)
      simpa [z] using b
    have pin : ordered (z H) x := orderedInput _ (Finset.union_subset_union tx (fun _ h => h))
    have bit := (forceEndpoint D v.1 a neg z path x).1 pin
    change (!((code D.gates x).getD 0 false)) = true
    rw [bit]; rfl
  · rintro ⟨U,wu,dis⟩
    let B := Finset.range s\U
    let z (k : ℕ) := input r (B∪tagRow s e (H+1+k))
    have path : Path D H z := receiverPath D out H s r e (H+1) B
      ((show B ⊆ Finset.range s from Finset.sdiff_subset).trans (Finset.range_mono sr))
      (by dsimp [M]; omega) (hi _ (by dsimp [M]; omega)) W ev (by
        intro k hk
        apply tagNear
        simp only [payload,show ¬H+1+k ≤ H by omega,ite_false]
        exact complementNear (plainSub rsub gs _) (wu.1.trans rsub) (plainNear wu rs _))
    have xb : X ⊆ B := fun u h => Finset.mem_sdiff.mpr ⟨xs h,Finset.disjoint_left.mp dis h⟩
    have pin : ordered x (z 0) := by
      apply orderedInput _ (Finset.union_subset_union xb ?_)
      intro u hu
      obtain ⟨lo,high⟩ := Finset.mem_Ico.mp hu
      exact Finset.mem_Ico.mpr ⟨lo,high.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : H ≤ H+1+0)) _)⟩
    have bit := (forceEndpoint D v.1 a neg z path x).2 pin
    change (!((code D.gates x).getD 0 false)) = false
    rw [bit]; rfl
end PEqualNP.Outside.L_lib_1420_aux

namespace PEqualNP.Outside.L_lib_1420_aux
def combined (A B : Finset ℕ) := A∪B
theorem normUnion (d : DecidableEq Nat) (A B : Finset Nat) :
    @Max.max _ (@Finset.instMax Nat d) A B = combined A B := by
  rw [Subsingleton.elim d instDecidableEqNat]
  rfl
noncomputable def choose (P : Prop) (t : P → α) (f : ¬P → α) := @dite α P (Classical.propDecidable P) t f
theorem normChoose (P : Prop) (d : Decidable P) (t : P → α) (f : ¬P → α) :
    @dite α P d t f = choose P t f := by rw [Subsingleton.elim d (Classical.propDecidable P)]; rfl
noncomputable def condChoice (P : Prop) (t f : α) := @ite α P (Classical.propDecidable P) t f
theorem normCond (P : Prop) (d : Decidable P) (t f : α) :
    @ite α P d t f = condChoice P t f := by rw [Subsingleton.elim d (Classical.propDecidable P)]; rfl
end PEqualNP.Outside.L_lib_1420_aux
open PEqualNP.Outside.L_lib_1420_aux PEqualNP.Outside.L_lib_1420_aux.Noisy in
theorem PEqualNP.Outside.L_lib_1420 :
letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true]
let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
let fit := fun {m : Nat} (W : Fin m → Finset Nat) (r a f b p : Nat) (V : Finset Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
    (∀ i, out i < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ p ∧
    ∀ i Y, Y ⊆ Finset.range r → near a f (W i) Y →
      ∀ j, (D.wires (bits r (Y ∩ V))).getD (out j) false = decide (i=j)
let separates := fun (r p : Nat) (A B : Finset Nat → Prop) =>
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, valid r D ∧ PEqualNP.NotBracket.notCount D = 0 ∧ D.size ≤ p ∧
    ∀ X, X ⊆ Finset.range r → (A X → D.eval (bits r X) = true) ∧ (B X → D.eval (bits r X) = false)
let plain := fun {m : Nat} (C : Finset Nat) (F : Fin m → Finset Nat) (j : Nat) =>
  if j<2 then C else if u : (j-2)/2 < m then F ⟨(j-2)/2,u⟩ else ∅
let words := fun {l m : Nat} (H e s : Nat) (C R : Finset Nat) (F : Fin l → Finset Nat)
    (G : Fin m → Finset Nat) (j : Fin (2*(H+1))) =>
  let A := if j.val ≤ H then plain C F j.val else Finset.range s \ plain R G (H-(j.val-(H+1)))
  A ∪ Finset.Ico s (s+(2*e+1)*j.val)
∀ (a e s l m : Nat) (C R : Finset Nat) (F : Fin l → Finset Nat) (G : Fin m → Finset Nat),
  let H := 2^a
  let b := a+1
  let M := 2*(H+1)
  let r := s+(2*e+1)*M
  let W := words H e s C R F G
  let ok := fun {t : Nat} (A : Finset Nat) (Z : Fin t → Finset Nat) (T : Finset Nat) =>
    T ⊆ A ∧ T.card=e ∧ ∀ j, near e e (Z j) T
  let pos := fun X : Finset Nat => ∃ T, ok C F T ∧ T ⊆ X
  let neg := fun X : Finset Nat => ∃ U, ok R G U ∧ Disjoint X U
  2*(l+2) ≤ H+1 → 2*(m+2) ≤ H+1 →
  C ⊆ Finset.range s → R ⊆ Finset.range s → C.card=2*e → R.card=2*e →
  (∀ i, F i ⊆ Finset.range s) → (∀ i, G i ⊆ Finset.range s) →
  ((∃ p, fit W r e e b p (Finset.range r)) ↔ ∀ T U, ok C F T → ok R G U → ¬Disjoint T U) ∧
  (∀ p, fit W r e e b p (Finset.range r) → separates s p pos neg) ∧
  fit W r e e (b+1) (16*M*((2*e+1)*(e+1)+1)) (Finset.Ico s r) := by
  classical
  dsimp only
  intro a e s l m C R F G wide widg csub rsub cs rs fs gs
  constructor
  · simpa only [FitN,Valid,input,Near,Witness,payload,plain,tagRow,normTruth,normDiff,normInter,normUnion,normChoose,normCond] using
      tightIff a e s C R F G csub rsub fs gs cs rs wide widg
  constructor
  · intro p fit
    have result := tightSeparator (p:=p) a e s C R F G cs rs csub rsub gs
    simp only [FitN,Valid,input,Near,Witness,payload,plain,tagRow,normTruth,normDiff,normInter,normUnion,normChoose,normCond] at result fit ⊢
    exact result fit
  · simpa only [FitN,Valid,input,Near,payload,plain,tagRow,normTruth,normDiff,normInter,normUnion,normChoose,normCond] using
      slackDecoder a e s C R F G csub fs
