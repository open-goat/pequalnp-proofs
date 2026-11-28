import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1409_aux
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

structure Net (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n+j

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
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n where
  gates := p.gates++[g]
  fan := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
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
  refine ⟨q,⟨?_,by simp [q,extend],?_⟩,n+p.gates.length,by simp [q,extend],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,List.filter_append,List.length_append]
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

end PEqualNP.Outside.L_lib_1409_aux

namespace PEqualNP.Outside.L_lib_1409_aux
namespace StageNet
section WireFacts
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}
abbrev Col (m : ℕ) := Fin m → Bool
noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) :=
  List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true]
noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false
noncomputable def ix (gs : List Gate) := (List.range gs.length).filter fun j =>
  decide ((gs.getD j ⟨.or,[]⟩).op = GateOp.not)
noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) :=
  (ix gs).map fun j => val x gs (n+2+j)
noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m := fun i => decide (a∈x i)
noncomputable def base (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f=(fun _ => false) ∨ f=(fun _ => true) ∨ ∃ a, f=sing x a}
noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

theorem wirelen (gs : List Gate) (u : List Bool) : ((Circuit.mk gs 0).wires u).length=u.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simpa [Circuit.wires,List.foldl_append,Nat.add_assoc] using congrArg Nat.succ ih

theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p} (hp : p<n+2+gs.length) :
    val x (gs++[g]) p=val x gs p := by
  funext i
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD p false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs++[g]) (n+2+gs.length) i=g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change ( ((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD _ false = _
  rw [←len,List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs++[g])=ix gs ++ (if g.op=.not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append,List.length_singleton,List.range_succ,List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op=.not <;> simp [h]

theorem ixRange {gs : List Gate} {j} (h : j∈ix gs) : j<gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs++[g])=trace x gs ++ (if g.op=.not then [val x (gs++[g]) (n+2+gs.length)] else []) := by
  unfold trace
  rw [ixAdd,List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs,0⟩=(ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op=.not <;> simp [List.filter_append,h,ih]

theorem extendBack (gs : List Gate) (g : Gate) (h : ReadsBack (n+2) ⟨gs,0⟩)
    (ok : ∀ p∈g.inputs,p<n+2+gs.length) : ReadsBack (n+2) ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j<gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j=gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩ ∧ gs.length≤k ∧ trace x gs=tr ∧
    ∀ f∈S, ∃ p<n+2+gs.length, val x gs p=f
end WireFacts

section Compiler
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

theorem Built.start : Built x [] 0 (base x) := by
  refine ⟨[],by simp [FanInTwo],by simp [ReadsBack],by simp,rfl,?_⟩
  intro f hf
  rcases hf with rfl|rfl|⟨a,rfl⟩
  · refine ⟨n,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨n+1,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨a.val,by have := a.isLt; simp; omega,?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u∈x i)) ++ _).getD a.val false=_
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k≤K) (sub : T⊆S) : Built x tr K T := by
  obtain ⟨gs,fan,back,le,trace,signal⟩ := ih
  exact ⟨gs,fan,back,le.trans sz,trace,fun f hf => signal f (sub hf)⟩

theorem Built.andGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (conj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.and,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,conj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.orGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (disj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.or,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,disj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.notGate {f : Col m} (ih : Built x tr k S) (hf : f∈S) : Built x (tr++[inv f]) (k+1) (insert (inv f) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  let g : Gate := ⟨.not,[a]⟩
  have ev : val x (gs++[g]) (n+2+gs.length)=inv f := by
    funext i; rw [fresh]; simp [g,GateOp.eval,ea,inv]
  refine ⟨gs++[g],?_,?_,by simpa using sz,by simp [traceAdd,g,ht,ev],?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with old|new
    · exact fan j old
    · obtain rfl : j=g := List.mem_singleton.mp new
      simp [g]
  · apply extendBack _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl|mem
    · exact ⟨_,by simp,ev⟩
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

end Compiler

section Construction
open scoped Classical
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m))
    (b : ℕ) (f : Col m) := ∃ T, Built x tr (k+b) T ∧ S⊆T ∧ f∈T

theorem batch {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S⊆T → ∀ a∈s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k+s.card*b) T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fresh,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) : Col m :=
  fun j => decide (x i⊆x j ∧ v i=v j)
noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r-1-b.val)

theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r+1) v=hist r (fun i => v i/2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist,List.ofFn_succ',List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two,show r-1-(b:ℕ)+1 = r+1-1-b by have := b.isLt; omega]
  · simp

end Construction

end StageNet
end PEqualNP.Outside.L_lib_1409_aux

namespace PEqualNP.Outside.L_lib_1409_aux
namespace Encoder

theorem runCode {h r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (inj : Function.Injective W)
    (falls : (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card < 2^b) :
    ∃ v : Fin (h+1) → Nat, Monotone v ∧ (∀ i, v i < 2^(min b r)) ∧
      ∀ i j, i ≤ j → v i = v j → W i ⊆ W j := by
  classical
  let bad := Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)
  let before := fun i : Fin (h+1) => bad.filter (fun j => j.val < i.val)
  let v := fun i => (before i).card
  have sub {i j : Fin (h+1)} (le : i ≤ j) : before i ⊆ before j := by
    intro k mk
    obtain ⟨mb,lt⟩ := Finset.mem_filter.mp mk
    exact Finset.mem_filter.mpr ⟨mb,lt_of_lt_of_le lt le⟩
  have mono : Monotone v := fun _ _ le => Finset.card_le_card (sub le)
  have across (k : Fin h) (no : ¬ W k.castSucc ⊆ W k.succ) : v k.castSucc < v k.succ := by
    apply Finset.card_lt_card
    apply lt_of_le_of_ne (sub (Fin.castSucc_le_succ k))
    intro eq
    have mem : k ∈ before k.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩,Nat.lt_succ_self _⟩
    obtain ⟨_,lt⟩ := Finset.mem_filter.mp (eq ▸ mem : k ∈ before k.castSucc)
    exact (Nat.lt_irrefl k.val) lt
  refine ⟨v,mono,?_,?_⟩
  · intro i
    have bound : v i ≤ bad.card := Finset.card_le_card (Finset.filter_subset _ _)
    by_cases br : b ≤ r
    · rw [Nat.min_eq_left br]
      exact lt_of_le_of_lt bound falls
    · rw [Nat.min_eq_right (by omega)]
      have bc : bad.card ≤ h := by simpa using Finset.card_le_univ bad
      have hcap : h+1 ≤ 2^r := by simpa using Fintype.card_le_of_injective W inj
      omega
  · intro i j
    induction j using Fin.induction with
    | zero =>
      intro le _
      have eq : i = 0 := le_antisymm le (Fin.zero_le i)
      subst i
      exact Finset.Subset.refl _
    | succ j ih =>
      intro le eq
      by_cases same : i = j.succ
      · subst i
        exact Finset.Subset.refl _
      have small : i ≤ j.castSucc := by
        have lt : i < j.succ := lt_of_le_of_ne le same
        exact Nat.le_of_lt_succ lt
      have less := mono small
      have next := mono (Fin.castSucc_le_succ j)
      have last : W j.castSucc ⊆ W j.succ := by
        by_contra no
        have := across j no
        omega
      exact (ih small (by omega)).trans last

end Encoder
end PEqualNP.Outside.L_lib_1409_aux

namespace PEqualNP.Outside.L_lib_1409_aux
namespace Encoder
open StageNet
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {h m : Nat}

noncomputable def level (A : Finset (Fin h)) : Fin (h+1) :=
  ⟨A.sup (fun j => j.val+1), by
    apply Nat.lt_succ_of_le
    apply Finset.sup_le
    intro j _
    have := j.isLt
    omega⟩

noncomputable def suffix (x : Fin m → Finset (Fin h)) (k : Nat) : Col m :=
  fun j => decide (∃ a ∈ x j, k ≤ a.val)

lemma suffixBase (x : Fin m → Finset (Fin h)) : suffix x h = fun _ => false := by
  funext j
  unfold suffix
  apply decide_eq_false
  rintro ⟨a,_,ha⟩
  exact (Nat.not_le_of_lt a.isLt) ha

lemma suffixStep (x : Fin m → Finset (Fin h)) (k : Nat) (hk : k<h) :
    suffix x k = disj (sing x ⟨k,hk⟩) (suffix x (k+1)) := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [suffix, disj, sing, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,hg⟩
    by_cases hh : a.val=k
    · left
      have eq : a = ⟨k,hk⟩ := Fin.ext hh
      simpa [eq] using ha
    · right
      exact ⟨a,ha,by omega⟩
  · rintro (ha|⟨a,ha,hh⟩)
    · exact ⟨⟨k,hk⟩,ha,le_refl _⟩
    · exact ⟨a,ha,by omega⟩

lemma suffixBuild (x : Fin m → Finset (Fin h)) (t : Nat) (ht : t ≤ h) :
    ∃ S, Built x [] t S ∧ base x ⊆ S ∧ ∀ k, h-t ≤ k → k≤h → suffix x k ∈ S := by
  induction t with
  | zero =>
    refine ⟨base x, Built.start, Set.Subset.rfl, ?_⟩
    intro k hk hf
    have eq : k=h := by omega
    rw [eq,suffixBase]
    exact Or.inl rfl
  | succ t ih =>
    obtain ⟨S,B,sub,hs⟩ := ih (by omega)
    let j := h-(t+1)
    have hj : j<h := by dsimp [j];omega
    have prev := hs (j+1) (by dsimp [j];omega) (by dsimp [j];omega)
    have add := Built.orGate B (sub (Or.inr (Or.inr ⟨⟨j,hj⟩,rfl⟩))) prev
    refine ⟨_,add,sub.trans (Set.subset_insert _ _),?_⟩
    intro k hk he
    by_cases eq : k=j
    · rw [eq,suffixStep x j hj]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hs k (by dsimp [j] at eq;omega) he)

noncomputable def mark (rank : Fin m → Fin (h+1)) (v : Fin (h+1) → Nat)
    (i : Fin (h+1)) : Col m := fun j => decide (i≤rank j ∧ v i=v (rank j))

lemma thresholdBuild (x : Fin m → Finset (Fin h)) :
    ∃ S, Built x [] h S ∧ base x ⊆ S ∧
      ∀ i : Fin (h+1), (fun j => decide (i≤level (x j))) ∈ S := by
  obtain ⟨S,B,sub,allS⟩ := suffixBuild x h (le_refl _)
  refine ⟨S,B,sub,?_⟩
  intro i
  cases hi : i.val with
  | zero =>
    have eq : (fun j => decide (i≤level (x j))) = fun _ => true := by
      funext j; apply decide_eq_true; change i.val ≤ _;omega
    rw [eq];exact sub (Or.inr (Or.inl rfl))
  | succ k =>
    have eq : (fun j => decide (i≤level (x j))) = suffix x k := by
      funext j
      simp only [suffix, decide_eq_decide]
      change i.val ≤ (x j).sup (fun a => a.val+1) ↔ _
      rw [hi]
      constructor
      · intro hh
        by_contra! no
        have lim : (x j).sup (fun a => a.val+1) ≤ k := Finset.sup_le (fun a ha => by have := no a ha;omega)
        omega
      · rintro ⟨a,ha,hh⟩
        exact le_trans (by omega : k+1 ≤ a.val+1) (Finset.le_sup (f := fun a : Fin h => a.val+1) ha)
    rw [eq]
    exact allS k (by omega) (by have := i.isLt;omega)

lemma runStages (x : Fin m → Finset (Fin h)) (k : Nat) (v : Fin (h+1) → Nat)
    (cap : ∀ i, v i<2^k) (mono : Monotone v) :
    ∃ S, Built x (hist k (fun j => v (level (x j)))) (h+(h+1)*(2*k)+k) S ∧
      base x ⊆ S ∧ ∀ i, mark (fun j => level (x j)) v i ∈ S := by
  induction k generalizing v with
  | zero =>
    obtain ⟨S,B,sub,ts⟩ := thresholdBuild x
    have z : ∀ i,v i=0 := fun i => by have := cap i;simp at this;omega
    refine ⟨S,by simpa [hist] using B,sub,?_⟩
    intro i
    have hh : mark (fun j => level (x j)) v i = fun j => decide (i ≤ level (x j)) := by
      funext j
      simp [mark,z]
    rw [hh]
    exact ts i
  | succ k ih =>
    let u := fun i => v i/2
    have uc : ∀ i,u i<2^k := fun i => by have := cap i;simp [pow_succ] at this;dsimp [u];omega
    obtain ⟨S,B,sub,old⟩ := ih u uc (fun _ _ le => Nat.div_le_div_right (mono le))
    let rank := fun j => level (x j)
    let bit := fun i => (v i).testBit 0
    let sel := Finset.univ.filter (fun i => bit i = true)
    obtain ⟨T,BT,st,hit⟩ := anyFold sel (mark rank u) B (sub (Or.inl rfl))
      (fun i _ => old i)
    have eqn : (fun j => decide (∃ a∈sel, mark rank u a j=true)) = fun j => bit (rank j) := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mark,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ba,le,eq⟩
        have ord := mono le
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro bb
        exact ⟨rank j,bb,le_rfl,rfl⟩
    have hit' : (fun j => bit (rank j)) ∈ T := by
      rw [←eqn];convert hit using 1;funext j;apply Bool.eq_iff_iff.mpr;simp
    have BN := Built.notGate BT hit'
    have st' : S ⊆ insert (inv (fun j => bit (rank j))) T := st.trans (Set.subset_insert _ _)
    obtain ⟨U,BU,su,allU⟩ := batch (Finset.univ : Finset (Fin (h+1))) (mark rank v) 1 BN (by
      intro K R br sr i _
      have iw := sr (st' (old i))
      by_cases bi : bit i=true
      · have same : mark rank v i=mark rank u i := by
          funext j;simp only [mark,decide_eq_decide]
          constructor
          · rintro ⟨a,b⟩;exact ⟨a,congrArg (·/2) b⟩
          · rintro ⟨a,b⟩
            have ord := mono a
            simp [bit] at bi;dsimp [u] at b
            exact ⟨a,by omega⟩
        exact ⟨R,br.relax (by omega) Set.Subset.rfl,Set.Subset.rfl,same ▸ iw⟩
      · have bw : inv (fun j => bit (rank j)) ∈ R := sr (Set.mem_insert _ _)
        have made := Built.andGate br iw bw
        refine ⟨_,made,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [mark,conj,inv,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true']
        simp [bit] at bi
        simp [bit,u]
        grind)
    have lim : sel.card≤h+1 := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨U,BU.relax ?_ Set.Subset.rfl,(sub.trans st').trans su,fun i => allU i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    ring_nf at *
    omega

lemma encodeWithRuns {r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (v : Fin (h+1) → Nat)
    (mono : Monotone v) (cap : ∀ i, v i < 2^(min b r))
    (grow : ∀ i j, i ≤ j → v i = v j → W i ⊆ W j) :
    ∃ (C : Circuit) (wire : Fin r → Nat),
      FanInTwo C ∧ ReadsBack (h+2) C ∧ C.output < h+2+C.size ∧
      (∀ j, wire j < h+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 10*(r+1)*(h+1) ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1)=i.val →
        (Finset.univ.filter (fun j : Fin r => (C.wires (List.ofFn (fun j : Fin h => decide (j∈A)) ++ [false,true])).getD (wire j) false=true))=W i := by
  classical
  let n := Fintype.card (Finset (Fin h))
  let ixA : Finset (Fin h) ≃ Fin n := Fintype.equivFin _
  let x : Fin n → Finset (Fin h) := ixA.symm
  let rank := fun j => level (x j)
  let k := min b r
  obtain ⟨S,bs,baseS,marks⟩ := runStages x k v cap mono
  let col : Fin r → Col n := fun t j => decide (t∈W (rank j))
  obtain ⟨T,bt,_,hits⟩ := batch (Finset.univ : Finset (Fin r)) col (h+1) bs (by
    intro K U bu su t _
    let sel := Finset.univ.filter (fun a => t∈W a)
    obtain ⟨V,bv,uv,hv⟩ := anyFold sel (mark rank v) bu (su (baseS (Or.inl rfl))) (fun i _ => su (marks i))
    have same : col t = (fun j => decide (∃ a∈sel, mark rank v a j=true)) := by
      funext j
      simp only [col,mark,decide_eq_decide,decide_eq_true_eq,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro ht
        exact ⟨rank j,ht,le_rfl,rfl⟩
      · rintro ⟨a,hm,le,eq⟩
        exact grow a (rank j) le eq hm
    have lim : sel.card ≤ h+1 := by simpa using Finset.card_le_univ sel
    refine ⟨V,bv.relax (by omega) Set.Subset.rfl,uv,?_⟩
    rw [same]
    convert hv using 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp)
  obtain ⟨gs,fan,back,sz,ht,wire⟩ := bt
  choose tap valid data using fun a => wire _ (hits a (Finset.mem_univ _))
  have hlen := congrArg List.length ht
  simp [trace,hist] at hlen
  have nots := (countIx gs).trans hlen
  refine ⟨⟨gs,0⟩,tap,fan,back,by simp [Circuit.size],valid,nots.le.trans (Nat.min_le_left ..),?_,?_⟩
  · change gs.length - _ ≤ _
    simp only [Finset.card_univ,Fintype.card_fin] at sz
    have kr : k ≤ r := Nat.min_le_right ..
    have times := Nat.mul_le_mul_left (h+1) kr
    have nle := Nat.sub_le gs.length (PEqualNP.NotBracket.notCount ⟨gs,0⟩)
    nlinarith
  · intro A i hl
    have hA : x (ixA A)=A := ixA.symm_apply_apply A
    have hi : rank (ixA A)=i := Fin.ext (by simpa [rank,level,hA] using hl)
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have ev := congrFun (data t) (ixA A)
    simp only [val,raw,col,hi,hA] at ev
    rw [ev]
    simp

lemma encoder {r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (inj : Function.Injective W)
    (falls : (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card < 2^b) :
    ∃ (C : Circuit) (wire : Fin r → Nat),
      FanInTwo C ∧ ReadsBack (h+2) C ∧ C.output < h+2+C.size ∧
      (∀ j, wire j < h+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 10*(r+1)*(h+1) ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1)=i.val →
        (Finset.univ.filter (fun j : Fin r => (C.wires (List.ofFn (fun j : Fin h => decide (j∈A)) ++ [false,true])).getD (wire j) false=true))=W i := by
  obtain ⟨v,mono,cap,grow⟩ := runCode W inj falls
  exact encodeWithRuns W v mono cap grow

end Encoder
end PEqualNP.Outside.L_lib_1409_aux

namespace PEqualNP.Outside.L_lib_1409_aux
abbrev Word (r : ℕ) := Finset (Fin r)
abbrev Words (h r : ℕ) := Fin (h+1) → Word r

def Good {h r : ℕ} (W : Words h r) (e : ℕ) (i : Fin (h+1)) (Y : Word r) :=
  Y ⊆ W i ∧ (W i \ Y).card ≤ e

def Separate {h r : ℕ} (W : Words h r) (e : ℕ) :=
  ∀ i j, i ≠ j → e < (W i \ W j).card ∨ e < (W j \ W i).card

def meetW {h r : ℕ} (W : Words h r) (I : Finset (Fin (h+1))) : Word r :=
  Finset.univ.filter fun a => ∀ i ∈ I, a ∈ W i

def closedWords {h r : ℕ} (W : Words h r) := Finset.univ.image (meetW W)
def closeW {h r : ℕ} (W : Words h r) (Y : Word r) :=
  meetW W (Finset.univ.filter fun i => Y ⊆ W i)
def Capped {h r : ℕ} (W : Words h r) (c e : ℕ) :=
  ∀ (m : ℕ) (L : Fin m → Fin (h+1)) (V : Fin m → Word r),
    (∀ i, V i ∈ closedWords W ∧ Good W e (L i) (V i)) →
    (∀ i j, i ≤ j → V i ⊆ V j) → (∀ i j, i.val+1=j.val → L i≠L j) → m ≤ 2^c

theorem common_iff {h r : ℕ} {W : Words h r} {e} : Separate W e ↔
    ∀ i j Y, Good W e i Y → Good W e j Y → i=j := by
  constructor
  · intro sep i j Y hi hj
    by_contra ne
    have bound {A B : Word r} (sub : Y ⊆ B) (lim : (A \ Y).card ≤ e) : (A \ B).card ≤ e :=
      (Finset.card_le_card (Finset.sdiff_subset_sdiff (by rfl) sub)).trans lim
    rcases sep i j ne with lt | lt
    · exact lt.not_ge (bound hj.1 hi.2)
    · exact lt.not_ge (bound hi.1 hj.2)
  · intro uniq i j ne
    by_contra! no
    apply ne
    apply uniq i j (W i ∩ W j)
    · exact ⟨Finset.inter_subset_left,by simpa using no.1⟩
    · exact ⟨Finset.inter_subset_right,by simpa [Finset.inter_comm (W i)] using no.2⟩

theorem close_mem {h r : ℕ} (W : Words h r) (Y : Word r) : closeW W Y ∈ closedWords W :=
  Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem close_spec {h r : ℕ} (W : Words h r) (Y V : Word r) :
    V ⊆ closeW W Y ↔ ∀ i, ¬ V ⊆ W i → ∃ a ∈ Y, a ∉ W i := by
  classical
  simp only [closeW,meetW,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  grind

theorem close_good {h r : ℕ} {W : Words h r} {e i Y} (hy : Good W e i Y) :
    Good W e i (closeW W Y) := by
  have enlarges : Y ⊆ closeW W Y := by
    intro a ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, fun j hj => (Finset.mem_filter.mp hj).2 ha⟩
  exact ⟨fun a ha => (Finset.mem_filter.mp ha).2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy.1⟩),
    (Finset.card_le_card (Finset.sdiff_subset_sdiff (by rfl) enlarges)).trans hy.2⟩

theorem word_mem {h r : ℕ} (W : Words h r) (i : Fin (h+1)) : W i ∈ closedWords W := by
  apply Finset.mem_image.mpr
  refine ⟨{i},Finset.mem_univ _,?_⟩
  ext a
  simp [meetW]

theorem labels_le {h r : ℕ} {W : Words h r} {e} (s : Separate W e) :
    h+1 ≤ (closedWords W).card := by
  have inj : Function.Injective W := by
    intro i j eq
    apply common_iff.mp s i j (W i)
    · simp [Good]
    · simp [Good,eq]
  simpa using Finset.card_le_card_of_injOn (s:=Finset.univ) W
    (fun i _ => word_mem W i) inj.injOn
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
noncomputable def active {h r : ℕ} (W : Words h r) (e : ℕ) : Finset (Word r) := by
  classical
  exact (closedWords W).filter (fun z => ∃ i, Good W e i z)
abbrev Node {h r : ℕ} (W : Words h r) (e : ℕ) := ↥(active W e)
variable {h r e c : ℕ} {W : Words h r}

theorem nodeFacts (u : Node W e) : u.val ∈ closedWords W ∧ ∃ i, Good W e i u.val := by
  classical
  exact Finset.mem_filter.mp u.property
noncomputable def label (u : Node W e) : Fin (h+1) := (nodeFacts u).2.choose
theorem label_good (u : Node W e) : Good W e (label u) u.val := (nodeFacts u).2.choose_spec
def nodeOf (i : Fin (h+1)) (Y : Word r) (hy : Good W e i Y) : Node W e := by
  classical
  exact ⟨closeW W Y,Finset.mem_filter.mpr ⟨close_mem W Y,i,close_good hy⟩⟩
theorem label_node (sep : Separate W e) (i Y) (hy : Good W e i Y) :
    label (nodeOf i Y hy) = i :=
  common_iff.mp sep _ _ _ (label_good _) (close_good hy)

inductive Trace {h r : ℕ} {W : Words h r} {e : ℕ} : ℕ → Node W e → Prop where
  | first (u) : Trace 0 u
  | next {k u v} : Trace k u → u.val ⊆ v.val → label u ≠ label v → Trace (k+1) v

theorem traceCard {k : ℕ} {u : Node W e} (p : Trace k u) : k ≤ u.val.card := by
  induction p with
  | first => omega
  | @next k u v prev sub diff ih =>
    have ne : u.val ≠ v.val := fun eq => diff (congrArg label (Subtype.ext eq))
    have lt := Finset.card_lt_card (lt_of_le_of_ne sub ne)
    omega

theorem traceChain {k : ℕ} {u : Node W e} (p : Trace k u) :
    ∃ f : Fin (k+1) → Node W e, f (Fin.last k) = u ∧
      (∀ i j, i ≤ j → (f i).val ⊆ (f j).val) ∧
      (∀ i j : Fin (k+1), i.val+1=j.val → label (f i)≠label (f j)) := by
  induction p with
  | first u =>
    refine ⟨fun _ => u,rfl,fun _ _ _ => Finset.Subset.rfl,?_⟩
    intro i j eq
    omega
  | @next k u v prev sub diff ih =>
    obtain ⟨f,last,mono,alt⟩ := ih
    let g : Fin (k+1+1) → Node W e := Fin.snoc f v
    have gc (i : Fin (k+1)) : g i.castSucc = f i := Fin.snoc_castSucc ..
    have gl : g (Fin.last (k+1)) = v := Fin.snoc_last ..
    refine ⟨g,gl,?_,?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro le
        have eq := le_antisymm le (Fin.le_last j)
        rw [eq]
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _; rw [gc,gl]
          exact (mono i _ (Fin.le_last i)).trans (last ▸ sub)
        · intro le; rw [gc,gc]
          exact mono _ _ (Fin.castSucc_le_castSucc_iff.mp le)
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro eq; simp only [Fin.val_last] at eq; omega
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro eq
          simp only [Fin.val_castSucc,Fin.val_last] at eq
          have same : i = Fin.last k := Fin.ext (by simp; omega)
          simpa only [gc,gl,same,last] using diff
        · intro eq; rw [gc,gc]; exact alt _ _ eq

theorem traceCap (cap : Capped W c e) {k : ℕ} {u : Node W e} (p : Trace k u) : k < 2^c := by
  obtain ⟨f,_,mono,alt⟩ := traceChain p
  exact cap _ (fun i => label (f i)) (fun i => (f i).val)
    (fun i => ⟨(nodeFacts (f i)).1,label_good _⟩) mono alt

noncomputable def depth (u : Node W e) := by
  classical
  exact ((Finset.range (r+1)).filter (fun k => Trace k u)).max'
    ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),Trace.first u⟩⟩

theorem depthTrace (u : Node W e) : Trace (depth u) u := by
  classical
  unfold depth
  exact (Finset.mem_filter.mp (Finset.max'_mem ((Finset.range (r+1)).filter (fun k => Trace k u)) _)).2
theorem traceDepth {k : ℕ} {u : Node W e} (pk : Trace k u) : k ≤ depth u := by
  classical
  apply Finset.le_max' _ _
  have t := traceCard pk
  have t' : u.val.card ≤ r := by simpa using Finset.card_le_univ u.val
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),pk⟩
theorem depth_le {u v : Node W e} (sub : u.val ⊆ v.val) : depth u ≤ depth v := by
  by_cases eq : label u = label v
  · have lift {k} (p : Trace k u) : Trace k v := by
      cases p with
      | first => exact Trace.first _
      | next prev inc ne => exact Trace.next prev (inc.trans sub) (eq ▸ ne)
    exact traceDepth (lift (depthTrace _))
  · exact Nat.le_of_succ_le (traceDepth (Trace.next (depthTrace _) sub eq))
theorem depth_lt {u v : Node W e} (sub : u.val ⊆ v.val) (ne : label u ≠ label v) :
    depth u < depth v := traceDepth (Trace.next (depthTrace _) sub ne)
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
open CircuitLowerBounds

def Fits (h r b c e z : Nat) (W : Words h r) :=
  ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
    C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
    (∀ j, wire j < h+2+C.size) ∧ (∀ j, out j < r+2+D.size) ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
    (C.size - PEqualNP.NotBracket.notCount C) + (D.size - PEqualNP.NotBracket.notCount D) ≤ z ∧
    ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1) = i.val →
      let v := C.wires (List.ofFn (fun j : Fin h => decide (j ∈ A)) ++ [false,true])
      let msg := Finset.univ.filter (fun j : Fin r => v.getD (wire j) false = true)
      msg = W i ∧ ∀ Y : Finset (Fin r), Y ⊆ msg → (msg \ Y).card ≤ e →
        let w := D.wires (List.ofFn (fun j : Fin r => decide (j ∈ Y)) ++ [false,true])
        ∀ j, w.getD (out j) false = decide (i = j)
def falls {h r : ℕ} (W : Words h r) :=
  (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card

def inputs {r : ℕ} (Y : Word r) := List.ofFn (fun j : Fin r => decide (j∈Y)) ++ [false,true]
def initialWord (h : ℕ) (i : Fin (h+1)) : Word h := Finset.univ.filter (fun j => j.val < i.val)
theorem initialWordSup {h : ℕ} (i : Fin (h+1)) :
    (initialWord h i).sup (fun j => j.val+1) = i.val := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  · cases eq : i.val with
    | zero => exact Nat.zero_le _
    | succ k =>
      let j : Fin h := ⟨k,by have := i.isLt; omega⟩
      exact Finset.le_sup (f:=fun j : Fin h => j.val+1)
        (show j ∈ initialWord h i from Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [j,eq]⟩)

theorem phases {r b : ℕ} (C : Circuit) (legal : MetaComplexity.FanInTwo C) (neg : NotBracket.notCount C ≤ b) :
    ∃ p : Word r → ℕ, Monotone p ∧ (∀ Y, p Y < 2^b) ∧
    ∀ {Y Z : Word r}, Y ⊆ Z → p Y = p Z → ∀ j,
      (C.wires (inputs Y)).getD j false = true → (C.wires (inputs Z)).getD j false = true := by
  obtain ⟨v,m,cap,same⟩ := MarkedInversionRank.circuit_rank (n:=r) C legal
  let bits := fun Y : Word r => fun j : Fin r => decide (j∈Y)
  have mono : Monotone bits := by
    intro Y Z incl j
    apply Bool.le_iff_imp.mpr
    simpa only [bits,decide_eq_true_eq] using (fun mem : j ∈ Y => incl mem)
  exact ⟨fun Y => v (bits Y),m.comp mono,
    fun Y => (cap _).trans_le (Nat.pow_le_pow_right (by decide) neg),
    fun inc eq j => same _ _ (mono inc) eq j⟩

theorem required {h r b c e z} {W : Words h r} (fit : Fits h r b c e z W) :
    Separate W e ∧ falls W < 2^b ∧ Capped W c e := by
  obtain ⟨C,D,wire,out,fc,_,fd,_,_,_,_,_,bc,bd,_,ev⟩ := fit
  let msg := fun i : Fin (h+1) => Finset.univ.filter (fun j => (C.wires (inputs (initialWord h i))).getD (wire j) false = true)
  have read (i) : msg i = W i := (ev _ i (initialWordSup i)).1
  have decode {i} {Y : Word r} (good : Good W e i Y) (j) :
      (D.wires (inputs Y)).getD (out j) false = decide (i=j) := by
    have a := (ev _ i (initialWordSup i)).2
    change ∀ Z ⊆ msg i, (msg i \ Z).card ≤ e → _ at a
    rw [read] at a
    exact a Y good.1 good.2 j
  obtain ⟨p,pm,pc,ps⟩ := phases C fc bc (r:=h)
  obtain ⟨q,qm,qc,qs⟩ := phases D fd bd (r:=r)
  have pre {i j : Fin (h+1)} (le : i ≤ j) : initialWord h i ⊆ initialWord h j := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp hx).2 le⟩
  refine ⟨common_iff.mpr ?_,?_,?_⟩
  · intro i j Y hi hj
    have a := (decode hi i).symm.trans (decode hj i)
    simpa [eq_comm] using a.symm
  · let S := Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)
    let f := fun i : Fin h => p (initialWord h i.castSucc)
    have jump (i : Fin h) (hi : i∈S) : f i < p (initialWord h i.succ) := by
      have inc := pre (Fin.castSucc_le_succ i)
      apply lt_of_le_of_ne (pm inc)
      intro eq
      apply (Finset.mem_filter.mp hi).2
      rw [←read,←read]
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ps inc eq _ (Finset.mem_filter.mp hj).2⟩
    have strict (i j : Fin h) (hi : i∈S) (lt : i<j) : f i < f j :=
      (jump i hi).trans_le (pm (pre (show i.succ ≤ j.castSucc from lt)))
    have size := Finset.card_le_card_of_injOn (s:=S) (t:=Finset.range (2^b-1)) f (by
      intro i hi
      have a := jump i hi
      have lim := pc (initialWord h i.succ)
      exact Finset.mem_range.mpr (by omega)) (by
      intro i hi j hj eq
      rcases lt_trichotomy i j with l | m | g
      · exact False.elim ((strict i j hi l).ne eq)
      · exact m
      · exact False.elim ((strict j i hj g).ne eq.symm))
    change S.card < 2^b
    rw [Finset.card_range] at size
    have := Nat.two_pow_pos b
    omega
  · intro m L V hv mono alt
    cases m with
    | zero => exact Nat.zero_le _
    | succ m =>
      let f : Fin (m+1) → Fin (2^c) := fun i => ⟨q (V i),qc _⟩
      have strict : StrictMono f := by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        have inc := mono i.castSucc i.succ (Fin.castSucc_le_succ i)
        change q _ < q _
        apply lt_of_le_of_ne (qm inc)
        intro eq
        have a := qs inc eq (out (L i.castSucc)) (by simpa using decode (hv i.castSucc).2 (L i.castSucc))
        rw [decode (hv i.succ).2] at a
        exact alt _ _ rfl (of_decide_eq_true a).symm
      simpa using Fintype.card_le_of_injective f strict.injective
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
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
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
open FiniteGateBank OrderedThresholdBank CircuitLowerBounds
open scoped Classical
variable {h r e c : ℕ} {W : Words h r}
abbrev Sample (W : Words h r) (e : ℕ) := {s : Fin (h+1) × Word r // Good W e s.1 s.2}
def observed (x : Sample W e) := x.val.2
def source (x : Sample W e) := inputs (observed x)
def tag (x : Sample W e) : Node W e := nodeOf x.val.1 x.val.2 x.property
noncomputable def levelAt (x : Sample W e) := depth (tag x)
def firstNet (r : ℕ) := empty (r+2)
def miss (W : Words h r) (i : Fin (h+1)) (x : Sample W e) := ∃ a ∈ observed x, a ∉ W i
def containsNode (u : Node W e) (x : Sample W e) := u.val ⊆ (tag x).val
theorem srcWidth (x : Sample W e) : (source x).length = r+2 := by simp [source,inputs]

theorem startWires :
    ((firstNet r).has (source (W:=W) (e:=e)) (fun _ => false)) ∧
    ((firstNet r).has (source (W:=W) (e:=e)) (fun _ => true)) ∧
    ∀ a : Fin r, Has (firstNet r) (source (W:=W) (e:=e)) (fun x => a∈observed x) := by
  refine ⟨⟨r,by simp [firstNet,empty],?_⟩,⟨r+1,by simp [firstNet,empty],?_⟩,?_⟩
  · intro x
    simp [firstNet,empty,PulseList.run,source,inputs,List.getD_eq_getElem?_getD]
  · intro x
    simp [firstNet,empty,PulseList.run,source,inputs,List.getD_eq_getElem?_getD]
  · intro a
    refine ⟨a.val,by simp [firstNet,empty]; omega,?_⟩
    intro x
    simp [firstNet,empty,PulseList.run,source,inputs,bit,List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show a.val < (List.ofFn (fun j : Fin r => decide (j∈observed x))).length by simpa using a.isLt),a.isLt]

theorem nodesCount : Fintype.card (Node W e) ≤ (closedWords W).card := by
  classical
  change Fintype.card ↥(active W e) ≤ _
  rw [Fintype.card_coe]
  exact Finset.card_le_card (Finset.filter_subset ..)

theorem prepareNodes :
    ∃ p, Grow (source (W:=W) (e:=e)) (firstNet r) p
      ((h+1)*r + Fintype.card (Node W e)*(h+1)) 0 ∧
      ∀ u : Node W e, Has p source (containsNode u) := by
  classical
  obtain ⟨zero,one,singles⟩ := startWires (W:=W) (e:=e)
  obtain ⟨p,g,outs⟩ := batchPred (p:=firstNet r) Finset.univ (miss (e:=e) W) r (by
    intro i _ q keep
    let s := Finset.univ.filter (fun a : Fin r => a ∉ W i)
    obtain ⟨v,gv,hv⟩ := foldPred srcWidth s (fun a (x : Sample W e) => a∈observed x)
      q false (keep _ zero) (fun a _ => keep _ (singles a))
    refine ⟨v,allowance gv (by simpa using Finset.card_le_univ s),hasCong ?_ hv⟩
    intro x
    simp only [Bool.false_eq_true,if_false,s,Finset.mem_filter,Finset.mem_univ,true_and,miss]
    exact exists_congr fun _ => and_comm)
  obtain ⟨q,gq,qOut⟩ := batchPred (p:=p) Finset.univ (containsNode (W:=W) (e:=e)) (h+1) (by
    intro u _ v keep
    let s := Finset.univ.filter (fun i => ¬ u.val ⊆ W i)
    obtain ⟨z,gz,hz⟩ := foldPred srcWidth s (miss (e:=e) W) v true (keep _ (g.1 _ one))
      (fun i _ => keep _ (outs i (Finset.mem_univ _)))
    refine ⟨z,allowance gz (by simpa using Finset.card_le_univ s),hasCong ?_ hz⟩
    intro x
    change (if true = true then ∀ i∈s, miss W i x else _) ↔ u.val ⊆ closeW W (observed x)
    simpa [s,miss] using (close_spec W (observed x) u.val).symm)
  exact ⟨q,by simpa using chain g gq,fun u => qOut u (Finset.mem_univ _)⟩
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
open FiniteGateBank OrderedThresholdBank CircuitLowerBounds
open scoped Classical
variable {h r e c : ℕ} {W : Words h r}
def slots (r c : ℕ) := min r (2^c-1)

theorem levelBound (cap : Capped W c e) (x : Sample W e) : levelAt x ≤ slots r c := by
  have q := depthTrace (tag x)
  have a := traceCard q
  have b := traceCap cap q
  have sz : (tag x).val.card ≤ r := by simpa using Finset.card_le_univ (tag x).val
  unfold slots levelAt
  omega

theorem highSignal (x : Sample W e) (j : ℕ) : j ≤ levelAt x ↔
    ∃ u : Node W e, j ≤ depth u ∧ containsNode u x := by
  constructor
  · intro le; exact ⟨tag x,le,Finset.Subset.rfl⟩
  · rintro ⟨u,le,sub⟩; exact le.trans (depth_le sub)

theorem buildThresholds (cap : Capped W c e) :
    ∃ p, Grow (source (W:=W) (e:=e)) (firstNet r) p
      ((h+1)*r + Fintype.card (Node W e)*(h+1) + slots r c*Fintype.card (Node W e) + (4*slots r c+c)) c ∧
      (∀ u : Node W e, Has p source (containsNode u)) ∧
      ∀ u : Node W e, Has p source (fun x : Sample W e => levelAt x ≤ depth u) := by
  classical
  let k := slots r c
  obtain ⟨p,g,nodes⟩ := prepareNodes (W:=W) (e:=e)
  obtain ⟨zero,one,_⟩ := startWires (W:=W) (e:=e)
  let highAt := fun (a : Fin k) (x : Sample W e) => a.val+1 ≤ levelAt x
  obtain ⟨q,gq,highs⟩ := batchPred (p:=p) Finset.univ highAt (Fintype.card (Node W e)) (by
    intro a _ v keep
    let s := Finset.univ.filter (fun u : Node W e => a.val+1 ≤ depth u)
    obtain ⟨w,gw,hh⟩ := foldPred srcWidth s (containsNode (W:=W) (e:=e)) v false (keep _ (g.1 _ zero))
      (fun u _ => keep _ (nodes u))
    refine ⟨w,allowance gw (Finset.card_le_univ _),hasCong ?_ hh⟩
    intro x
    simpa [s,highAt] using (highSignal x (a.val+1)).symm)
  have gg := chain g gq
  have room : k < 2^c := by
    dsimp [k,slots]
    have := Nat.two_pow_pos c
    omega
  obtain ⟨v,gv,lows⟩ := decode (source (W:=W) (e:=e)) srcWidth c k room levelAt
    (levelBound cap) q (gg.1 _ zero) (by
      intro j pos le
      let a : Fin k := ⟨j-1,by omega⟩
      have eq : a.val+1=j := by dsimp [a]; omega
      have hi := highs a (Finset.mem_univ _)
      unfold Has at hi
      convert hi using 2
      funext x
      apply Bool.eq_iff_iff.mpr
      simp [high,bit,highAt] <;> omega)
  have gg' := chain gg gv
  refine ⟨v,by simpa [k] using gg',fun u => gv.1 _ (gq.1 _ (nodes u)),?_⟩
  intro u
  by_cases small : depth u < k
  · have old := lows (depth u+1) (by omega) (by omega)
    apply hasCong (F:=fun x : Sample W e => levelAt x < depth u+1) (fun x => Nat.lt_succ_iff)
    unfold Has
    convert old using 2
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [bit,low]
  · have keep := gg'.1 _ one
    unfold Has
    convert keep using 2
    rename_i x
    have bound := levelBound cap x
    have lim : levelAt x ≤ depth u := by change levelAt x ≤ k at bound; omega
    simp [bit,lim]

theorem decoder (sep : Separate W e) (cap : Capped W c e) :
    ∃ (D : Circuit) (out : Fin (h+1) → ℕ),
      MetaComplexity.FanInTwo D ∧ MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
      D.output < r+2+D.size ∧ (∀ j, out j < r+2+D.size) ∧ NotBracket.notCount D ≤ c ∧
      D.size - NotBracket.notCount D ≤ (h+1)*r + Fintype.card (Node W e)*(h+1) +
        slots r c*Fintype.card (Node W e) + 4*slots r c + Fintype.card (Node W e) + (h+1)*Fintype.card (Node W e) ∧
      ∀ i Y, Good W e i Y → ∀ j, (D.wires (inputs Y)).getD (out j) false = decide (i=j) := by
  classical
  obtain ⟨p,g,nodes,lows⟩ := buildThresholds cap
  obtain ⟨zero,_,_⟩ := startWires (W:=W) (e:=e)
  let term := fun (u : Node W e) (x : Sample W e) => containsNode u x ∧ levelAt x ≤ depth u
  obtain ⟨q,gq,terms⟩ := batchPred (p:=p) Finset.univ term 1 (by
    intro u _ v keep
    obtain ⟨w,gw,hw⟩ := binary srcWidth v _ _ (keep _ (nodes u)) (keep _ (lows u)) true
    refine ⟨w,gw,?_⟩
    unfold Has
    convert hw using 2
    apply Bool.eq_iff_iff.mpr
    simp [term,bit])
  let isLabel := fun (j : Fin (h+1)) (x : Sample W e) => x.val.1=j
  obtain ⟨v,gv,outs⟩ := batchPred (p:=q) Finset.univ isLabel (Fintype.card (Node W e)) (by
    intro j _ w keep
    let s := Finset.univ.filter (fun u : Node W e => label u=j)
    obtain ⟨z,gz,hz⟩ := foldPred srcWidth s term w false (keep _ (gq.1 _ (g.1 _ zero)))
      (fun u _ => keep _ (terms u (Finset.mem_univ _)))
    refine ⟨z,allowance gz (Finset.card_le_univ s),hasCong ?_ hz⟩
    intro x
    have lbl : label (tag x) = x.val.1 := label_node sep _ _ x.property
    simp only [isLabel,s,Finset.mem_filter,Finset.mem_univ,true_and,term,ite_false,Bool.false_eq_true]
    constructor
    · rintro ⟨u,hu,inc,low⟩
      have eq : label u = label (tag x) := by
        by_contra ne
        exact (Nat.not_lt_of_ge low) (depth_lt inc ne)
      exact lbl.symm.trans (eq.symm.trans hu)
    · intro eq
      exact ⟨tag x,lbl.trans eq,Finset.Subset.rfl,le_rfl⟩)
  have gg := chain (chain g gq) gv
  choose out valid data using fun j => outs j (Finset.mem_univ _)
  have cost : NotBracket.notCount ⟨v.gates,0⟩ = c := by simpa [Net.cost,firstNet,empty,NotBracket.notCount] using gg.2.2
  refine ⟨⟨v.gates,0⟩,out,v.fan,v.readsBack,by simp [Circuit.size],valid,cost.le,?_,?_⟩
  · change v.gates.length - _ ≤ _
    rw [cost]
    have lim := gg.2.1
    simp only [firstNet,empty,List.length_nil,zero_add,Finset.card_univ,Fintype.card_fin,Nat.mul_one] at lim
    omega
  · intro i Y good j
    let x : Sample W e := ⟨(i,Y),good⟩
    change (PulseList.run v.gates (source x)).getD (out j) false = _
    rw [data j x]
    apply Bool.eq_iff_iff.mpr
    simp [bit,isLabel,x]
end PEqualNP.Outside.L_lib_1409_aux
namespace PEqualNP.Outside.L_lib_1409_aux
def price {h r : ℕ} (W : Words h r) (c e : ℕ) : ℕ :=
  let K := (closedWords W).card
  let H := min (r+1) (min K (2^c))
  64*((r+1)*(h+1) + (r+1)*(min r e+1)*K + (H+1)*(K+1)^2)

theorem affordable {h r c e} {W : Words h r} (sep : Separate W e) :
    10*(r+1)*(h+1) + ((h+1)*r + Fintype.card (Node W e)*(h+1) +
      slots r c*Fintype.card (Node W e) + 4*slots r c + Fintype.card (Node W e) +
      (h+1)*Fintype.card (Node W e)) ≤ price W c e := by
  let K := (closedWords W).card
  let N := Fintype.card (Node W e)
  let n := h+1
  let k := slots r c
  let H := min (r+1) (min K (2^c))
  have nk : n ≤ K := labels_le sep
  have sk : N ≤ K := nodesCount
  have kr : k ≤ r := Nat.min_le_left ..
  have prod₁ : N*n ≤ K*K := Nat.mul_le_mul sk nk
  have prod₂ : n*N ≤ K*K := Nat.mul_le_mul nk sk
  have prod₃ : k*N ≤ r*K := Nat.mul_le_mul kr sk
  have b : r ≤ (r+1)*n := by dsimp [n]; nlinarith
  have b' : n*r ≤ (r+1)*n := by nlinarith
  have m : (r+1)*K ≤ (r+1)*(min r e+1)*K := by
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos (min r e)))
  have d : K*K ≤ (H+1)*(K+1)^2 := by
    calc
      _ ≤ (K+1)^2 := by nlinarith
      _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.succ_pos H)
  change 10*(r+1)*n + (n*r + N*n + k*N + 4*k + N + n*N) ≤
    64*((r+1)*n + (r+1)*(min r e+1)*K + (H+1)*(K+1)^2)
  nlinarith only [prod₁,prod₂,prod₃,kr,sk,b,b',m,d]

theorem sufficient {h r b c e : ℕ} {W : Words h r}
    (sep : Separate W e) (fall : falls W < 2^b) (caps : Capped W c e) :
    Fits h r b c e (price W c e) W := by
  have inj : Function.Injective W := by
    intro i j eq
    apply common_iff.mp sep i j (W i)
    · simp [Good]
    · simp [Good,eq]
  obtain ⟨C,wire,fc,bc,oc,wv,nc,sc,encode⟩ := Encoder.encoder W inj fall
  obtain ⟨D,out,fd,bd,od,ov,nd,sd,decode⟩ := decoder sep caps
  refine ⟨C,D,wire,out,fc,bc,fd,bd,oc,od,wv,ov,nc,nd,
    (Nat.add_le_add sc sd).trans (affordable sep),?_⟩
  intro A i lev
  dsimp only
  have correct := encode A i lev
  refine ⟨correct,?_⟩
  rw [correct]
  intro Y sub loss
  exact decode i Y ⟨sub,loss⟩

end PEqualNP.Outside.L_lib_1409_aux

open PEqualNP.Outside.L_lib_1409_aux in
theorem PEqualNP.Outside.L_lib_1409 :
let fit := fun (h r b c e z : Nat)
    (W : Fin (h+1) → Finset (Fin r)) =>
  ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
    C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
    (∀ j, wire j < h+2+C.size) ∧ (∀ j, out j < r+2+D.size) ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
    (C.size - PEqualNP.NotBracket.notCount C) + (D.size - PEqualNP.NotBracket.notCount D) ≤ z ∧
    ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1) = i.val →
      let v := C.wires (List.ofFn (fun j : Fin h => decide (j ∈ A)) ++ [false,true])
      let msg := Finset.univ.filter (fun j : Fin r => v.getD (wire j) false = true)
      msg = W i ∧ ∀ Y : Finset (Fin r), Y ⊆ msg → (msg \ Y).card ≤ e →
        let w := D.wires (List.ofFn (fun j : Fin r => decide (j ∈ Y)) ++ [false,true])
        ∀ j, w.getD (out j) false = decide (i = j)
∀ (h r b c e : Nat) (W : Fin (h+1) → Finset (Fin r)),
  let n := h+1
  let separate := ∀ i j, i ≠ j → e < (W i \ W j).card ∨ e < (W j \ W i).card
  let falls := (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card
  let meet := fun (I : Finset (Fin (h+1))) =>
    Finset.univ.filter (fun a : Fin r => ∀ i ∈ I, a ∈ W i)
  let Kset := Finset.univ.image meet
  let K := Kset.card
  let capped := ∀ (m : Nat) (L : Fin m → Fin (h+1)) (V : Fin m → Finset (Fin r)),
    (∀ i, V i ∈ Kset ∧ V i ⊆ W (L i) ∧ (W (L i) \ V i).card ≤ e) →
    (∀ i j, i ≤ j → V i ⊆ V j) → (∀ i j, i.val+1 = j.val → L i ≠ L j) → m ≤ 2^c
  let test := separate ∧ falls < 2^b ∧ capped
  let H := min (r+1) (min K (2^c))
  let price := 64*((r+1)*n + (r+1)*(min r e+1)*K + (H+1)*(K+1)^2)
  ((∃ z, fit h r b c e z W) ↔ test) ∧ (test → fit h r b c e price W) := by
  intro fit h r b c e W
  change ((∃ z, Fits h r b c e z W) ↔ Separate W e ∧ falls W < 2^b ∧ Capped W c e) ∧
    ((Separate W e ∧ falls W < 2^b ∧ Capped W c e) → Fits h r b c e (price W c e) W)
  refine ⟨⟨?_,?_⟩,fun ⟨s,f,k⟩ => sufficient s f k⟩
  · rintro ⟨z,w⟩
    exact required w
  · rintro ⟨s,f,k⟩
    exact ⟨_,sufficient s f k⟩
