import Mathlib
import PEqualNP.Defs
-- Machine combinators adapted from 773a44dea4b8f3176d5cc06e6ceb5ca0c8aee81a, lean/PEqualNP/Outside/L_meta_32050.lean.
namespace PEqualNP.Outside.L_meta_33617
namespace Lib
abbrev CPTs (f:List Bool → List Bool):Prop:=PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
end Lib
section MachinePart7
namespace Lib.Machines
open Turing
theorem d43 {σ : Type} (f : σ → Option σ) (n:ℕ) :
    (flip bind f)^[n] none=none:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply];exact ih
theorem d59 {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h:∀ c c',f c=some c' → g (emb c)=some (emb c')) :
    ∀ (n:ℕ) (a b : σ),(flip bind f)^[n] (some a)=some b →
      (flip bind g)^[n] (some (emb a))=some (emb b):=by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:=Option.some.inj hab
    rw [this];rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa:f a with
    | none =>
      have e:flip bind f (some a)=none:=hfa
      rw [e,d43] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind f (some a)=some c:=hfa
      have e':flip bind g (some (emb a))=some (emb c):=h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab
section pushes
variable {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
def pushes:TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q=>pushes q+1
  | .peek _ _ q=>pushes q
  | .pop _ _ q=>pushes q
  | .load _ q=>pushes q
  | .branch _ q₁ q₂=>max (pushes q₁) (pushes q₂)
  | .goto _=>0
  | .halt=>0
theorem d58 (q:TM2.Stmt Γ Λ σ) (v : σ) (S:∀ k,List (Γ k)) (k:K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length+pushes q:=by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_cons];omega
    · rw [Function.update_of_ne h];omega
  | peek k' f q ih=>exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux,pushes]
    refine (ih _ _).trans ?_
    by_cases h:k=k'
    · subst h
      rw [Function.update_self,List.length_tail];omega
    · rw [Function.update_of_ne h]
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux,pushes]
    cases f v
    · exact (ih₂ v S).trans (by have:=le_max_right (pushes q₁) (pushes q₂);omega)
    · exact (ih₁ v S).trans (by have:=le_max_left (pushes q₁) (pushes q₂);omega)
  | goto f=>simp [TM2.stepAux,pushes]
  | halt=>simp [TM2.stepAux,pushes]
end pushes
noncomputable def maxPush (tm:FinTM2):ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l=>pushes (tm.m l)
theorem d86 (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h:TM2.step tm.m c=some c') (k:tm.K) :
    (c'.stk k).length ≤ (c.stk k).length+maxPush tm:=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    refine (d58 _ _ _ _).trans ?_
    have:pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f:=fun l=>pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this
theorem d67 (tm:FinTM2) (k:tm.K) :
    ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a)=some b →
      (b.stk k).length ≤ (a.stk k).length+maxPush tm * n:=by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have:a=b:=Option.some.inj hab
    rw [this];simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa:TM2.step tm.m a with
    | none =>
      have e:flip bind (TM2.step tm.m) (some a)=none:=hfa
      rw [e,d43] at hab
      exact absurd hab (by simp)
    | some c =>
      have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa
      rw [e] at hab
      have h1:=ih c b hab
      have h2:=d86 tm a c hfa k
      rw [Nat.mul_succ];omega
theorem d4 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h;simp
  · simp [h]
theorem d5 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h;simp
  · simp [h]
theorem d37 (p:Polynomial ℕ) {x y:ℕ} (h:x ≤ y):p.eval x ≤ p.eval y:=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add,Polynomial.eval_add];exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.Machines
end MachinePart7
section MachinePart144
namespace Lib.Machines
open Turing
def d60:List Bool → TM2.Stmt (fun _:Unit=>Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit → TM2.Stmt (fun _:Unit=>Bool) Unit Bool :=
  fun _ => .pop () (fun _ o=>o.isSome)
    (.branch (fun s=>s)
      (.load (fun _=>false) (.goto fun _=>()))
      (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
  K:=Unit
  k₀:=()
  k₁:=()
  Γ _:=Bool
  Λ := Unit
  main:=()
  σ := Bool
  initialState:=false
  m:=d3 l
abbrev CLCfg:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
theorem d17 (S T:List Bool) :
    Function.update (fun _:Unit=>S) () T=fun _=>T:=by
  funext k
  simp
theorem d42 (l:List Bool) (v:Bool) (S:List Bool) :
    TM2.stepAux (d60 l) v (fun _:Unit=>S) =
      (⟨none,v,fun _=>l.reverse++S⟩:CLCfg):=by
  induction l generalizing S with
  | nil=>rfl
  | cons a l ih =>
    simp only [d60,TM2.stepAux]
    rw [d17,ih]
    simp
theorem d64 (l:List Bool) (x:Bool) (a:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>x :: a⟩:CLCfg) =
      some ⟨some (),false,fun _=>a⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp
theorem d76 (l:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:CLCfg) =
      some ⟨none,false,fun _=>l⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  rw [d42]
  simp
theorem d63 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (⟨some (),false,fun _=>a⟩:CLCfg)) =
      some ⟨none,false,fun _=>l⟩:=by
  induction a with
  | nil=>exact d76 l
  | cons x a ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d3 l))
        (some (⟨some (),false,fun _=>x :: a⟩:CLCfg)) =
        some ⟨some (),false,fun _=>a⟩:=d64 l x a
    rw [e,ih]
theorem d75 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
    (some c)) (d4 (d20 l) a)).trans
    (Eq.trans ?_ (congrArg some (d5 (d20 l) l)).symm)
  show (flip bind (TM2.step (d3 l)))^[a.length+1]
    (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:CLCfg)) =
    some (⟨none,false,Function.update (fun _=>[]) () l⟩:CLCfg)
  rw [d17,d17]
  exact d63 l a
theorem d11 (l:List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x:List Bool=>x)
      (fun x:List Bool=>x) (fun _:List Bool=>l)) :=
  ⟨{
    tm:=d20 l
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.X+1
    outputsFun:=fun a =>
      { steps:=a.length+1
        evals_in_steps:=by
          have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
          exact (congrArg (fun x=>(flip bind (TM2.step (d3 l)))^[a.length+1]
            (some (initList (d20 l) x))) (hm a)).trans
            ((d75 l a).trans
              (congrArg (fun x=>some (haltList (d20 l) x)) (hm l).symm))
        steps_le_m:=by simp } }⟩
end Lib.Machines
end MachinePart144
section MachinePart235
namespace Lib.Machines
open Turing
section update
variable {ι : Type} [DecidableEq ι] {β : ι → Type}
theorem d51 (E:∀ i,β i) {a b c : ι} (hab:a≠b) (hac:a≠c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z:=by
  rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
theorem d50 (E:∀ i,β i) {a b c : ι} (hbc:b≠c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z:=by
  rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ : CK M1 M2 → Type
  | none=>M2.Γ M2.k₀
  | some (Sum.inl k)=>M1.Γ k
  | some (Sum.inr k)=>M2.Γ k
abbrev CΛ : Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ : Type:=M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s=>f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr (Sum.inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s=>f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
  | .load a q => .load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s=>Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
      (.branch (fun s=>s.2.2.isSome)
        (.push none (fun s=>s.2.2.getD d) (.goto fun _=>Sum.inr (Sum.inr false)))
        (.goto fun _=>Sum.inr (Sum.inr true)))
def tB:Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o=>(s.1,s.2.1,o))
      (.branch (fun s=>s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s=>s.2.2.getD d)
          (.goto fun _=>Sum.inr (Sum.inr true)))
        (.goto fun _=>Sum.inr (Sum.inl M2.main)))
def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l=>tr1 (M1.m l)
  | Sum.inr (Sum.inl l)=>tr2 (M2.m l)
  | Sum.inr (Sum.inr false)=>tA M1 M2 φ d
  | Sum.inr (Sum.inr true)=>tB M1 M2 d
def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2 :=
  haveI:=M1.kFin
  haveI:=M2.kFin
  haveI:=M1.ΛFin
  haveI:=M2.ΛFin
  haveI:=M1.σFin
  haveI:=M2.σFin
  haveI:=M2.Γk₀Fin
  { K:=CK M1 M2
    k₀:=some (Sum.inl M1.k₀)
    k₁:=some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main:=Sum.inl M1.main
    σ := Cσ M1 M2
    initialState:=(M1.initialState,M2.initialState,none)
    Γk₀Fin:=M1.Γk₀Fin
    m:=prog M1 M2 φ d }
variable {M1 M2}
def d49 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl k)=>S k
  | some (Sum.inr _)=>[]
def d48 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
  | none=>[]
  | some (Sum.inl _)=>[]
  | some (Sum.inr k)=>S k
theorem d13 (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)) :
    (d49 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
      Function.update (d49 S) (some (Sum.inl k)) x:=by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)];rfl
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j=x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j=S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];rfl
theorem d12 (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)) :
    (d48 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
      Function.update (d48 S) (some (Sum.inr k)) x:=by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j=x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j=S j
      rw [Function.update_of_ne h]
theorem d56 :
    (d49 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
theorem d55 :
    (d48 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
  funext j;rcases j with _ | j | j <;> rfl
def emb1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),d49 c.stk⟩
def emb2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l=>Sum.inr (Sum.inl l)),(u,c.var,b),d48 c.stk⟩
theorem sim1 (w:M2.σ × Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
    (S:∀ k,List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (d49 S)=emb1 w (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
    rw [d13] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [d13] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
theorem sim2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
    (S:∀ k,List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (d48 S)=emb2 u b (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
    rw [d12] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [d12] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
theorem step1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h:TM2.step M1.m c=some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c)=some (emb1 w c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)
theorem step2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h:TM2.step M2.m c=some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c)=some (emb2 u b c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
theorem st_fst (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁))=l:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem st_snd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
  unfold st
  rw [Function.update_of_ne (by simp),Function.update_self]
theorem st_thd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))=u:=by
  unfold st
  rw [Function.update_self]
theorem d66 (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l'=st l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
theorem d41 (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u :=
  d50 _ (by simp) _ _ _ _
theorem d90 (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)) :
    Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u'=st l t u' :=
  Function.update_idem _ _ _
theorem d79 (l:List (M1.Γ M1.k₁)) :
    (st l [] []:∀ k,List (CΓ M1 M2 k)) =
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l:=by
  unfold st
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem st_end (u:List (M2.Γ M2.k₀)) :
    (st [] [] u:∀ k,List (CΓ M1 M2 k)) =
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u:=by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
end Lib.Machines
end MachinePart235
section MachinePart472
namespace Lib.Machines
open Turing
variable {M1 M2:FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)
abbrev CCfg (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem d89 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩:=by
  simp only [TM2.step,prog,tA,TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
    Option.getD_some]
  rw [d66,st_snd,d41]
theorem d105 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩:=by
  simp only [TM2.step,prog,tA,TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
  rw [d66]
theorem d88 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩:=by
  simp only [TM2.step,prog,tB,TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
  rw [d41,st_thd,d90]
theorem d104 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
    (u:List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩:CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
  simp only [TM2.step,prog,tB,TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d41]
theorem loopA (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)) :
    ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length+1]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact d105 φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ :=
      d89 φ dd v1 v2 b x l t u
    rw [e,ih]
    simp
theorem loopB (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) :
    ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length+1]
          (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact d104 φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩ :=
      d88 φ dd v1 v2 b x t u
    rw [e,ih]
    simp
theorem d120 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
    (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)) :
    ∃ n,n ≤ 2 * o.length+2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
            Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),
          Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩:=by
  cases d with
  | none =>
    have:=hd rfl
    have ho:o=[]:=by
      cases o with
      | nil=>rfl
      | cons x _=>exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1,by omega,?_⟩
    show some _=some _
    simp only [prog,tA,TM2.stepAux,List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩
    rw [Function.iterate_add_apply,← d79,loopA,loopB,← st_end]
    simp
theorem d114 (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
  rw [d4]
  refine Eq.trans ?_ (d4 (comp M1 M2 φ d) i).symm
  show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
  rw [d13,d56]
  rfl
theorem d115 (w:M2.σ × Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2):=by
  rw [d5]
  show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
  rw [d13,d56]
  rfl
theorem d112 (u:M1.σ) (i:List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
        Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2):=by
  rw [d4]
  show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
  rw [d12,d55]
  rfl
theorem d113 (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
  rw [d5]
  refine Eq.trans ?_ (d5 (comp M1 M2 φ d) o).symm
  show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
  rw [d12,d55]
  rfl
theorem d136 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
    (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
    (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
    (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n,n ≤ s1+(2 * o1.length+2)+s2∧o1.length ≤ i.length+maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2):=by
  have p1:=d59 (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState,none)) (step1 φ d _) s1 _ _ h1
  rw [d114 φ d,d115] at p1
  obtain ⟨nt,hnt,pt⟩:=d120 φ d hd M1.initialState M2.initialState o1
  have p2:=d59 (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [d112,d113 φ d] at p2
  refine ⟨s2+(nt+s1),by omega,?_,?_⟩
  · have:=d67 M1 M1.k₁ s1 _ _ h1
    rw [d5,d4] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h:M1.k₁=M1.k₀
    · rw [h,Function.update_self]
    · rw [Function.update_of_ne h];simp
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,p1,pt,p2]
    rfl
theorem d77 {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1:TM2ComputableInPolyTime ea eb f)
    (c2:TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d:Option (c2.tm.Γ c2.tm.k₀) :=
    if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd:d=none → IsEmpty (c2.tm.Γ c2.tm.k₀):=by
    intro h
    by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d,hn] at h
    · exact not_nonempty_iff.mp hn
  let T:Polynomial ℕ :=
    c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time)
  have key:∀ a,∃ n,n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
    intro a
    have r1:=c1.outputsFun a
    have r2:=c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)):=by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
      rw [hφ];exact r2.evals_in_steps
    obtain ⟨n,hn,hlen,hrun⟩:=d136 φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n,hn.trans ?_,hrun⟩
    have b1:=r1.steps_le_m
    have b2:=r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul:maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
    have b3:Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length+maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time:=d37 _ (by omega)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,List.length_map]
    omega
  exact ⟨{
    tm:=comp c1.tm c2.tm φ d
    inputAlphabet:=c1.inputAlphabet
    outputAlphabet:=c2.outputAlphabet
    time:=T
    outputsFun:=fun a =>
      ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.Machines
end MachinePart472
section MachinePart690
namespace Lib.Machines
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool → Type
  | some false => Γ₀
  | none=>Option Γ₀
  | some true => Γ₁
def fmProg (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push none (fun s=>s) (.goto fun _=>false))
        (.goto fun _=>true))
  | true =>
    .pop none (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.branch (fun s=>(s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
            | none => .goto fun _=>true)
          (.goto fun _=>true))
        .halt)
def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=Option Bool
  k₀:=some false
  k₁:=some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main:=false
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=fmProg φ d
def fst3 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _=>[])
    (some false) l) none t) (some true) u
theorem d99 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some false)=l:=by
  unfold fst3
  rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem d81 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u none=t:=by
  unfold fst3
  rw [Function.update_of_ne (by simp),Function.update_self]
theorem d131 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    fst3 l t u (some true)=u:=by
  unfold fst3
  rw [Function.update_self]
theorem d47 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (fst3 l t u) (some false) l'=fst3 l' t u :=
  d51 _ (by simp) (by simp) _ _ _ _
theorem d27 (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (fst3 l t u) none t'=fst3 l t' u :=
  d50 _ (by simp) _ _ _ _
theorem d82 (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (fst3 l t u) (some true) u'=fst3 l t u' :=
  Function.update_idem _ _ _
theorem d98 (l:List Γ₀) :
    (fst3 l [] []:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem d132 (u:List Γ₁) :
    (fst3 [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d134 (b:Option Γ₀) (x : Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some false,some x,fst3 l (some x :: t) u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d99]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
  rw [d47,d81,d27]
theorem d164 (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false,b,fst3 [] t u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,none,fst3 [] t u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d99]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [d47]
theorem d133 (hd:d=none → ∀ x,φ x=none) (b:Option Γ₀) (x : Γ₀)
    (t:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true,b,fst3 [] (some x :: t) u⟩:FCfg Γ₀ Γ₁) =
      some ⟨some true,some x,fst3 [] t ((φ x).toList++u)⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d81]
  simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
    Bool.cond_true,Option.bind_some]
  rw [d27]
  cases hφ : φ x with
  | none=>simp
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
        Option.toList_some,List.singleton_append]
      rw [d131,d82]
      simp [hφ]
theorem d163 (b:Option Γ₀) (u:List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true,b,fst3 [] [] u⟩:FCfg Γ₀ Γ₁) =
      some ⟨none,none,fst3 [] [] u⟩:=by
  simp only [TM2.step,fmProg,TM2.stepAux]
  rw [d81]
  simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
    Bool.cond_false]
  rw [d27]
theorem d162 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length+1]
          (some (⟨some false,b,fst3 l t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,none,fst3 [] (l.reverse.map some++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t b;exact d164 φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (fmProg φ d))
        (some (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some false,some x,fst3 l (some x :: t) u⟩:=d134 φ d b x l t u
    rw [e,ih]
    simp
theorem d161 (hd:d=none → ∀ x,φ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length+1]
          (some (⟨some true,b,fst3 [] (t.map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨none,none,fst3 [] [] ((t.filterMap φ).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u b;exact d163 φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (fmProg φ d))
        (some (⟨some true,b,fst3 [] ((x :: t).map some) u⟩:FCfg Γ₀ Γ₁)) =
        some ⟨some true,some x,fst3 [] (t.map some) ((φ x).toList++u)⟩ :=
      d133 φ d hd b x (t.map some) u
    rw [e,ih]
    cases hφ : φ x <;> simp [hφ]
theorem fm_run [Fintype Γ₀] (hd:d=none → ∀ x,φ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
        (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some c)) (d4 (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (d5 (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
    (some (⟨some false,none,Function.update (fun _=>[]) (some false) l⟩:FCfg Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) (some true) (l.filterMap φ)⟩:FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply,← d98,d162,← d132]
  have:=d161 φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
theorem d7 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:d=none → ∀ x,φ x=none:=by
    intro hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=fm φ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 2
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=fm_run φ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (fmProg φ d)))^[(ea a).length+1 +
            ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end MachinePart690
section MachinePart885
namespace Lib.Machines
open Turing
inductive TPK:Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq
instance:Fintype TPK :=
  Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive TPL:Type
  | a | b | c | e
  deriving DecidableEq
instance:Fintype TPL :=
  Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK → Type
  | .inp => Γ₀
  | .t1=>Option Γ₀
  | .t2=>Option Γ₀
  | .t3=>Option Γ₀
  | .out => Γ₁
def d52 (φ : Γ₀ → Option Γ₁) (d:Option Γ₁) (lbl:TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s=>(s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
      | none => .goto fun _=>lbl)
    (.goto fun _=>lbl)
def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push .t1 (fun s=>s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t2 (fun s=>s) (d52 φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (.push .t3 (fun s=>s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o=>o.join)
      (.branch (fun s=>s.isSome)
        (d52 φ₁ d .e)
        .halt)
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=tpProg φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
  | .inp=>l
  | .t1=>a
  | .t2=>b
  | .t3=>c
  | .out=>u
theorem d54 (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
  funext k;cases k <;> simp [st5]
theorem d31 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
  funext k;cases k <;> simp [st5]
theorem d30 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
  funext k;cases k <;> simp [st5]
theorem d29 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁) :
    Function.update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
  funext k;cases k <;> simp [st5]
theorem d53 (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁) :
    Function.update (st5 l a b c u) .out u'=st5 l a b c u':=by
  funext k;cases k <;> simp [st5]
theorem d106 (l:List Γ₀) :
    (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
  funext k;cases k <;> simp [st5]
theorem d151 (u:List Γ₁) :
    (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
  funext k;cases k <;> simp [st5]
abbrev TPCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d127 (s:Option Γ₀) (x : Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
    (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d54,d31]
theorem d150 (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,none,st5 [] a b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d54]
theorem d126 (hd:d=none → ∀ x,φ₂ x=none) (s:Option Γ₀) (x : Γ₀)
    (a b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x :: a) b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .b,some x,st5 [] a (some x :: b) c ((φ₂ x).toList++u)⟩:=by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,
        d53,hφ]
theorem d149 (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,none,st5 [] [] b c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d31]
theorem d125 (s:Option Γ₀) (x : Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x :: b) c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .c,some x,st5 [] [] b (some x :: c) u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d30,d29]
theorem d148 (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,none,st5 [] [] [] c u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d30]
theorem d124 (hd:d=none → ∀ x,φ₁ x=none) (s:Option Γ₀) (x : Γ₀)
    (c:List (Option Γ₀)) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x :: c) u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,hφ]
  | some y =>
    cases d with
    | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,d53,hφ]
theorem d147 (s:Option Γ₀) (u:List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:TPCfg Γ₀ Γ₁) =
      some ⟨none,none,st5 [] [] [] [] u⟩:=by
  simp [TM2.step,tpProg,TM2.stepAux,st5,d29]
theorem d146 (b c:List (Option Γ₀)) (u:List Γ₁) :
    ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
          (some (⟨some .a,s,st5 l a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
  intro l
  induction l with
  | nil=>intro a s;exact d150 φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=d127 φ₁ φ₂ d s x l a b c u
    rw [e,ih]
    simp
theorem d145 (hd:d=none → ∀ x,φ₂ x=none) (c:List (Option Γ₀)) :
    ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,none,
          st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro b u s;exact d149 φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b,s,st5 [] ((x :: t).map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .b,some x,st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList++u)⟩ :=
      d126 φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e,ih]
    cases hφ : φ₂ x <;> simp [hφ]
theorem d144 (u:List Γ₁) :
    ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
  intro t
  induction t with
  | nil=>intro c s;exact d148 φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c,s,st5 [] [] ((x :: t).map some) c u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .c,some x,st5 [] [] (t.map some) (some x :: c) u⟩ :=
      d125 φ₁ φ₂ d s x (t.map some) c u
    rw [e,ih]
    simp
theorem d143 (hd:d=none → ∀ x,φ₁ x=none) :
    ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
          (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact d147 φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e,s,st5 [] [] [] ((x :: t).map some) u⟩:TPCfg Γ₀ Γ₁)) =
        some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩ :=
      d124 φ₁ φ₂ d hd s x (t.map some) u
    rw [e,ih]
    cases hφ : φ₁ x <;> simp [hφ]
theorem tp_run [Fintype Γ₀] (hd₁:d=none → ∀ x,φ₁ x=none)
    (hd₂:d=none → ∀ x,φ₂ x=none) (l:List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
        (l.length+1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1 +
    (l.length+1)+(l.length+1)+(l.length+1)]
    (some c)) (d4 (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (d5 (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
      (l.length+1)]
    (some (⟨some .a,none,Function.update (fun _=>[]) .inp l⟩:TPCfg Γ₀ Γ₁)) =
    some (⟨none,none,Function.update (fun _=>[]) .out
      (l.filterMap φ₁++l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)
  have hA:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .a,none,st5 l [] [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
    simpa using d146 φ₁ φ₂ d [] [] [] l [] none
  have hB:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
    have:=d145 φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)) =
      some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
    simpa using d144 φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
      (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
    have:=d143 φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    ← d106,hA,hB,hC,hE,d151]
theorem d10 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ φ : αΓ → Option βΓ,d=none → ∀ x,φ x=none:=by
    intro φ hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=tp φ₁ φ₂ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 4 * Polynomial.X+Polynomial.C 4
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
          ((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length+1 +
            ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end MachinePart885
section MachinePart1171
namespace Lib.Machines
open Turing
inductive FX
  | I | W | T | O
  deriving DecidableEq
instance:Fintype FX :=
  Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x=>by cases x <;> simp)
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq
instance:Fintype FL :=
  Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k=>M.Γ k
  | Sum.inr FX.I=>Bool ⊕ Bool
  | Sum.inr FX.W=>Bool
  | Sum.inr FX.T=>Bool
  | Sum.inr FX.O=>Bool ⊕ Bool
abbrev FstΛ : Type:=M.Λ ⊕ FL
abbrev Fstσ : Type:=M.σ × Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool) → Bool
  | none=>false
  | some (Sum.inl b)=>b
  | some (Sum.inr b)=>b
def isFst:Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _)=>true
  | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr FL.l3)
variable (M)
def d0 (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l=>trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>isFst s.2)
          (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1)))
        (.goto fun _=>Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr FL.l2))
        (.goto fun _=>Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.O) (fun s=>Sum.inr (bit s.2)) (.goto fun _=>Sum.inr FL.l3))
        (.goto fun _=>Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l4))
        (.goto fun _=>Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr FX.O) (fun s=>Sum.inl (bit s.2)) (.goto fun _=>Sum.inr FL.l5))
        .halt)
def firstM (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ FX
    k₀:=Sum.inr FX.I
    k₁:=Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main:=Sum.inr FL.l1
    σ := Fstσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d0 M e₀ e₁ }
variable {M}
def fstk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)):∀ k,List (FstΓ M k)
  | Sum.inl k=>S k
  | Sum.inr FX.I=>i
  | Sum.inr FX.W=>w
  | Sum.inr FX.T=>t
  | Sum.inr FX.O=>o
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
theorem d23 (k:M.K) (x:List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x=fstk (Function.update S k x) i w t o:=by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show x=Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j=Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];cases j <;> rfl
theorem d33 (i':List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i'=fstk S i' w t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d45 (w':List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w'=fstk S i w' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d18 (t':List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t'=fstk S i w t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d46 (o':List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o'=fstk S i w t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end fstk
abbrev FCfg1 (M:FinTM2):Type:=TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl),(c.var,b),fstk c.stk i w t o⟩
theorem simF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trF q) ((v,b):Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
    rw [← d23] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← d23] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
theorem stepF (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) (b:Option (Bool ⊕ Bool))
    (i:List (Bool ⊕ Bool)) (w t:List Bool) (o:List (Bool ⊕ Bool))
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (d0 M e₀ e₁) (embF b i w t o c)=some (embF b i w t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)
end Lib.Machines
end MachinePart1171
section MachinePart1354
namespace Lib.Machines
open Turing
theorem d6 {σ : Type} (f : σ → Option σ) {a b:ℕ} {x y z : σ}
    (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z) :
    (flip bind f)^[b+a] (some x)=some z:=by
  rw [Function.iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k:M.K):fstk S i w t o (Sum.inl k)=S k:=rfl
@[simp] theorem fstk_I:fstk S i w t o (Sum.inr FX.I)=i:=rfl
@[simp] theorem fstk_W:fstk S i w t o (Sum.inr FX.W)=w:=rfl
@[simp] theorem fstk_T:fstk S i w t o (Sum.inr FX.T)=t:=rfl
@[simp] theorem fstk_O:fstk S i w t o (Sum.inr FX.O)=o:=rfl
end fstk
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:List Bool) (o:List (Bool ⊕ Bool))
theorem f1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33,d18,isFst,bit]
theorem f1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33,d45,isFst,bit]
theorem f1_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l1),(v,b),fstk S [] w t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l2),(v,none),fstk S [] w t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d33]
theorem loop1:∀ (i:List (Bool ⊕ Bool)) (w t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[i.length+1]
        (some (⟨some (Sum.inr FL.l1),(v,b),fstk S i w t o⟩:FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2),(v,none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse++w)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro w t b;exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:flip bind (TM2.step (d0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:flip bind (TM2.step (d0 M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e,ih];simp [List.filterMap_cons]
theorem d168 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f2_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inl M.main),(v,none),fstk S [] w [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop2:∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w t o⟩:FCfg1 M)) =
      some ⟨some (Sum.inl M.main),(v,none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=d168 e₀ e₁ v S w o b a t
    rw [e,ih];simp
theorem d167 (b:Option (Bool ⊕ Bool)) (a:Bool) (w:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d45,d46,bit]
theorem f3_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l3),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d45]
theorem loop3:∀ (w:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[w.length+1]
        (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] w [] o⟩:FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] (w.reverse.map Sum.inr++o)⟩:=by
  intro w
  induction w with
  | nil=>intro o b;exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩ :=
      d167 e₀ e₁ v S o b a w
    rw [e,ih];simp
theorem d166 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f4_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ []) [] [] t o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l5),(v,none),fstk (Function.update S M.k₁ []) [] [] t o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d23]
theorem loop4:∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
        (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5),(v,none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=d166 e₀ e₁ v S o b y m t
    rw [e,ih];simp
theorem d165 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M) =
      some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18,d46,bit]
theorem f5_nil (b:Option (Bool ⊕ Bool)) :
    TM2.step (d0 M e₀ e₁)
        (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
      some ⟨none,(v,none),fstk S [] [] [] o⟩:=by
  simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop5:∀ (t:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
        (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] t o⟩:FCfg1 M)) =
      some ⟨none,(v,none),fstk S [] [] [] (t.reverse.map Sum.inl++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d0 M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩ :=
      d165 e₀ e₁ v S o b a t
    rw [e,ih];simp
end Lib.Machines
end MachinePart1354
section MachinePart1525
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
theorem d97:(fstk (fun _=>[]) [] [] [] []:∀ k,List (FstΓ M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d96 (i:List (Bool ⊕ Bool)) :
    (fstk (fun _=>[]) i [] [] []:∀ k,List (FstΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.I) i :=
  (d33 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d97])
theorem d95 (o:List (Bool ⊕ Bool)) :
    (fstk (fun _=>[]) [] [] [] o:∀ k,List (FstΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.O) o :=
  (d46 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d97])
theorem d110 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        fstk (Function.update (fun _=>[]) M.k₀ l) i w t o⟩:FCfg1 M):=by
  rw [d4];rfl
theorem d111 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3),(M.initialState,b),
        fstk (Function.update (fun _=>[]) M.k₁ m) i w t o⟩:FCfg1 M):=by
  rw [d5];rfl
theorem d16 {γ δ : Type} (l:List γ) :
    l.filterMap (fun _=>(none:Option δ))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
theorem d26 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getLeft? = x:=by
  have h1:(Sum.getLeft? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
  have h2:(Sum.getLeft? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.append_nil]
theorem d24 (x w:List Bool) :
    (encodePair (x,w)).filterMap Sum.getRight? = w:=by
  have h1:(Sum.getRight? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
  have h2:(Sum.getRight? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
  simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
    List.filterMap_some,d16,List.nil_append]
theorem d9 (x w:List Bool) :
    (encodePair (x,w)).length=x.length+w.length:=by
  simp [encodePair]
theorem d107 (x w0:List Bool) (m:List (M.Γ M.k₁)) (s:ℕ)
    (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)) :
    ∃ n,n ≤ s+2 * x.length+2 * w0.length+2 * m.length+5 ∧
      (flip bind (TM2.step (d0 M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have q1:(flip bind (TM2.step (d0 M e₀ e₁)))^[(encodePair (x,w0)).length+1]
      (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
      some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M):=by
    have:=loop1 e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d96] at this
    exact (congrArg (fun c=>(flip bind (TM2.step (d0 M e₀ e₁)))^[
      (encodePair (x,w0)).length+1] (some c))
      (d4 (firstM M e₀ e₁) (encodePair (x,w0)))).trans this
  have q2:(flip bind (TM2.step (d0 M e₀ e₁)))^[x.reverse.length+1]
      (some (⟨some (Sum.inr FL.l2),(M.initialState,none),
        fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))):=by
    have:=loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none
    rw [d110]
    simpa using this
  have q3:=d59 (TM2.step M.m) (TM2.step (d0 M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [d111] at q3
  have q4:(flip bind (TM2.step (d0 M e₀ e₁)))^[w0.reverse.length+1]
      (some (⟨some (Sum.inr FL.l3),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M):=by
    have:=loop3 e₀ e₁ M.initialState (Function.update (fun _=>[]) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5:(flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
      (some (⟨some (Sum.inr FL.l4),(M.initialState,none),
        fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M):=by
    have:=loop4 e₀ e₁ M.initialState (fun _=>[]) (w0.map Sum.inr) m [] none
    simpa using this
  have q6:(flip bind (TM2.step (d0 M e₀ e₁)))^[(m.reverse.map e₁).length+1]
      (some (⟨some (Sum.inr FL.l5),(M.initialState,none),
        fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
    have:=loop5 e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [d95] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (d5 (firstM M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [d9,List.length_reverse,List.length_map]
  omega
theorem d61 (f:List Bool → List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(f p.1,p.2))):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let T:Polynomial ℕ :=
    c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X+Polynomial.C 5
  have key:∀ p:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (d0 c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
    rintro ⟨x,w⟩
    have hs:∃ s,s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
    obtain ⟨s,b1,h⟩:=hs
    obtain ⟨n,hn,hrun⟩:=d107 e₀ e₁ x w _ s h
    have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n,hn.trans ?_,hrun⟩
    have h':=h
    rw [d5,d4] at h'
    have hlen:=d67 c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self,List.length_map] at hlen
    have hin:((Function.update (fun _=>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length:=by
      by_cases hk:c.tm.k₁=c.tm.k₀
      · rw [hk,Function.update_self,List.length_map]
      · rw [Function.update_of_ne hk];simp
    have b2:Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length+w.length) c.time :=
      d37 _ (by omega)
    have hmul:maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length+w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,d9,List.length_map]
    omega
  exact ⟨{
    tm:=firstM c.tm e₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun p =>
      { steps:=Classical.choose (key p)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d0 c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l=>some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1,p.2))).symm))
        steps_le_m:=(Classical.choose_spec (key p)).1 } }⟩
end Lib.Machines
end MachinePart1525
section MachinePart1685
namespace Lib.Machines.Iter
open Turing
inductive IX
  | I | C | T | O
  deriving DecidableEq
instance:Fintype IX :=
  Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x=>by cases x <;> simp)
inductive IL
  | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq
instance:Fintype IL :=
  Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k=>M.Γ k
  | Sum.inr IX.I=>Bool ⊕ Bool
  | Sum.inr IX.C=>Bool
  | Sum.inr IX.T=>Bool
  | Sum.inr IX.O=>Bool
abbrev ItΛ : Type:=M.Λ ⊕ IL
abbrev Itσ : Type:=M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
  | .load a q => .load (fun s=>(a s.1,s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s=>Sum.inl (f s.1))
  | .halt => .goto (fun _=>Sum.inr IL.l4)
variable (M)
def d1 (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l=>trI (M.m l)
  | Sum.inr IL.l1 =>
    .pop (Sum.inr IX.I) (fun s o=>(s.1,o))
      (.branch (fun s=>s.2.isSome)
        (.branch (fun s=>isFst s.2)
          (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1))
          (.push (Sum.inr IX.C) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1)))
        (.goto fun _=>Sum.inr IL.l2))
  | Sum.inr IL.l2 =>
    .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr IL.l2))
        (.goto fun _=>Sum.inr IL.l3))
  | Sum.inr IL.l3 =>
    .pop (Sum.inr IX.C) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.goto fun _=>Sum.inl M.main)
        (.goto fun _=>Sum.inr IL.l5))
  | Sum.inr IL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l4))
        (.goto fun _=>Sum.inr IL.l2))
  | Sum.inr IL.l5 =>
    .pop (Sum.inl M.k₀) (fun s o=>(s.1,o.map fun y=>Sum.inl (d₀ y)))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l5))
        (.goto fun _=>Sum.inr IL.l6))
  | Sum.inr IL.l6 =>
    .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
      (.branch (fun s=>s.2.isSome)
        (.push (Sum.inr IX.O) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l6))
        .halt)
def iterM (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ IX
    k₀:=Sum.inr IX.I
    k₁:=Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main:=Sum.inr IL.l1
    σ := Itσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d1 M e₀ d₀ e₁ }
variable {M}
def istk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    ∀ k,List (ItΓ M k)
  | Sum.inl k=>S k
  | Sum.inr IX.I=>i
  | Sum.inr IX.C=>cn
  | Sum.inr IX.T=>t
  | Sum.inr IX.O=>o
section istk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
@[simp] theorem istk_M (k:M.K):istk S i cn t o (Sum.inl k)=S k:=rfl
@[simp] theorem istk_I:istk S i cn t o (Sum.inr IX.I)=i:=rfl
@[simp] theorem istk_C:istk S i cn t o (Sum.inr IX.C)=cn:=rfl
@[simp] theorem istk_T:istk S i cn t o (Sum.inr IX.T)=t:=rfl
@[simp] theorem istk_O:istk S i cn t o (Sum.inr IX.O)=o:=rfl
theorem d15 (k:M.K) (x:List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x=istk (Function.update S k x) i cn t o:=by
  funext j
  rcases j with j | j
  · by_cases h:j=k
    · subst h
      rw [Function.update_self]
      show x=Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j=Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)];cases j <;> rfl
theorem d32 (i':List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr IX.I) i'=istk S i' cn t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d44 (cn':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.C) cn'=istk S i cn' t o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d14 (t':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.T) t'=istk S i cn t' o:=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
  · rw [Function.update_of_ne (by simp)];rfl
theorem d72 (o':List Bool) :
    Function.update (istk S i cn t o) (Sum.inr IX.O) o'=istk S i cn t o':=by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_of_ne (by simp)];rfl
  · rw [Function.update_self];rfl
end istk
abbrev ICfg (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c:TM2.Cfg M.Γ M.Λ M.σ):ICfg M :=
  ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl),(c.var,b),istk c.stk i cn t o⟩
theorem simI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
    TM2.stepAux (trI q) ((v,b):Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih =>
    have:=ih v (Function.update S k (f v :: S k))
    rw [← d15] at this
    exact this
  | peek k f q ih=>exact ih _ _
  | pop k f q ih =>
    have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← d15] at this
    exact this
  | load a q ih=>exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI,TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f=>rfl
  | halt=>rfl
theorem stepI (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
    (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
    TM2.step (d1 M e₀ d₀ e₁) (embI b i cn t o c)=some (embI b i cn t o c'):=by
  obtain ⟨l,v,S⟩:=c
  cases l with
  | none=>simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)
theorem d108 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (l:List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main),(M.initialState,b),
        istk (Function.update (fun _=>[]) M.k₀ l) i cn t o⟩:ICfg M):=by
  rw [d4];rfl
theorem d109 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (m:List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr IL.l4),(M.initialState,b),
        istk (Function.update (fun _=>[]) M.k₁ m) i cn t o⟩:ICfg M):=by
  rw [d5];rfl
theorem d94:(istk (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by
  funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d93 (i:List (Bool ⊕ Bool)) :
    (istk (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.I) i :=
  (d32 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d94])
theorem d92 (o:List Bool) :
    (istk (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k)) =
      Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.O) o :=
  (d72 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d94])
end Lib.Machines.Iter
end MachinePart1685
section MachinePart1892
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
theorem i1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32,d14,isFst,bit]
theorem i1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32,d44,isFst,bit]
theorem i1_nil (b:Option (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l1),(v,b),istk S [] cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,none),istk S [] cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d32]
theorem iloop1 (o:List Bool) :
    ∀ (i:List (Bool ⊕ Bool)) (cn t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[i.length+1]
        (some (⟨some (Sum.inr IL.l1),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        istk S [] ((i.filterMap Sum.getRight?).reverse++cn)
          ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
  intro i
  induction i with
  | nil=>intro cn t b;exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons,Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
    | inr a =>
      have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M)) =
          some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e,ih];simp [List.filterMap_cons]
theorem d158 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i2_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l2),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l3),(v,none),istk S i cn [] o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop2 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨some (Sum.inr IL.l3),(v,none),
        istk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
  intro t
  induction t with
  | nil =>
    intro S b
    have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      d158 e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
theorem d157 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),istk S i (a :: cn) t o⟩:ICfg M) =
      some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),istk S i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d44]
theorem i3_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l3),(v,b),istk S i [] t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l5),(v,none),istk S i [] t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d44]
theorem d156 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i4_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ []) i cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l2),(v,none),istk (Function.update S M.k₁ []) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop4 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l2),(v,none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l4),(v,b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      d156 e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
theorem d155 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
    (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i5_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ []) i cn t o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l6),(v,none),istk (Function.update S M.k₀ []) i cn t o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop5 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    ∀ (m:List (M.Γ M.k₀)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
        (some (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr IL.l6),(v,none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
  intro m
  induction m with
  | nil=>intro t b;exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l5),(v,b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      d155 e₀ d₀ e₁ v S b y m i cn t o
    rw [e,ih];simp
theorem d154 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
    (cn t o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
      some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14,d72,bit]
theorem i6_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
    TM2.step (d1 M e₀ d₀ e₁)
        (⟨some (Sum.inr IL.l6),(v,b),istk S i cn [] o⟩:ICfg M) =
      some ⟨none,(v,none),istk S i cn [] o⟩:=by
  simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop6 (i:List (Bool ⊕ Bool)) (cn:List Bool) :
    ∀ (t o:List Bool) (b:Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
        (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn t o⟩:ICfg M)) =
      some ⟨none,(v,none),istk S i cn [] (t.reverse++o)⟩:=by
  intro t
  induction t with
  | nil=>intro o b;exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩ :=
      d154 e₀ d₀ e₁ v S b a i cn t o
    rw [e,ih];simp
theorem d28 (k:M.K) :
    Function.update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[] :=
  Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
end Lib.Machines.Iter
end MachinePart1892
section MachinePart2083
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
theorem d71 (g:List Bool → List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z) :
    ∀ (cn z:List Bool) (L:ℕ) (b:Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length,(g^[j] z).length ≤ L) →
      ∃ n,n ≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
        ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
              istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:ICfg M)) =
          some ⟨none,(M.initialState,none),
            istk (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
      rw [List.map_reverse,List.reverse_reverse,List.map_map]
      conv_rhs=>rw [← List.map_id z]
      exact List.map_congr_left fun a _=>hd a
    have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:ICfg M)) =
        some ⟨some (Sum.inr IL.l5),(M.initialState,none),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2:=iloop5 e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none
    rw [d28,List.append_nil] at q2
    have q3:=iloop6 e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil,hz] at q3
    refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3⟩
    have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
    simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s,m,hs,hm,hmg⟩:=hrun z
    rw [List.length_cons] at hL
    have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
    have hgz:(g z).length ≤ L:=hL 1 (by omega)
    have hml:m.length=(g z).length:=by rw [← hmg,List.length_map]
    have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩:ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))):=by
      rw [d108]
      exact d157 e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2:=d59 (TM2.step M.m) (TM2.step (d1 M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [d109] at q2
    have q3:=iloop4 e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (Sum.inl a))
    rw [d28,List.append_nil,List.map_reverse,hmg] at q3
    have q4:=iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none
    rw [List.append_nil,List.reverse_reverse] at q4
    obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by
      have:=hL (j+1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e:g^[(a :: cn).length] z=g^[cn.length] (g z):=Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3) q4) q5⟩
    have hp:p.eval z.length ≤ p.eval L:=d37 p (by omega)
    rw [List.length_reverse,List.length_cons,Nat.succ_mul]
    generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
    omega
theorem d80 (g:List Bool → List Bool) (p:Polynomial ℕ)
    (hd:∀ a,d₀ (e₀ a)=a)
    (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
        m.map e₁=g z)
    (y u:List Bool) (L:ℕ) (hL:∀ j ≤ u.length,(g^[j] y).length ≤ L) :
    ∃ n,n ≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
      ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)):=by
  have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
      some (⟨some (Sum.inr IL.l2),(M.initialState,none),
        istk (fun _=>[]) [] u.reverse y.reverse []⟩:ICfg M):=by
    have:=iloop1 e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
    rw [d26,d24,List.append_nil,List.append_nil,d93] at this
    exact (congrArg (fun c=>((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
      (d4 (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
  have q2:=iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none
  rw [List.append_nil,List.reverse_reverse] at q2
  obtain ⟨n,hn,q3⟩:=d71 e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse];exact hL)
  rw [List.length_reverse] at hn q3
  rw [d92] at q3
  have q3':((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3),(M.initialState,none),
        istk (Function.update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (d5 (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3'⟩
  rw [d9,List.length_reverse]
  omega
theorem d22 (g:List Bool → List Bool) (m:List Bool → ℕ)
    (hm:∀ y:List Bool,m (g y) ≤ m y)
    (hg:∀ y:List Bool,(g y).length ≤ y.length+m y) (y:List Bool) :
    ∀ j:ℕ,m (g^[j] y) ≤ m y∧(g^[j] y).length ≤ y.length+j * m y:=by
  intro j
  induction j with
  | zero=>simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',Nat.succ_mul]
    have h1:=hm (g^[j] y)
    have h2:=hg (g^[j] y)
    obtain ⟨i1,i2⟩:=ih
    generalize j * m y=A at i2 ⊢
    exact ⟨by omega,by omega⟩
theorem d70 (A B L V y u:ℕ) (hLV:L ≤ V) (hAB:A ≤ B) :
    A+2 * L+2 * y+u+5 ≤ B+2 * V+3 * (y+u)+5:=by
  omega
theorem iter_polyTime_measure (g:List Bool → List Bool)
    (c:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (m:List Bool → ℕ) (a:ℕ)
    (hm:∀ y:List Bool,m (g y) ≤ m y)
    (hg:∀ y:List Bool,(g y).length ≤ y.length+m y)
    (ha:∀ y:List Bool,m y ≤ a * y.length+a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>g^[p.2.length] p.1)):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀ → Bool:=c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let W:Polynomial ℕ :=
    Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
  let T:Polynomial ℕ :=
    Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
      Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:=by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
  have key:∀ q:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
    rintro ⟨y,u⟩
    have hL:∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length+u.length * (a * y.length+a):=by
      intro j hj
      have h1:=(d22 g m hm hg y j).2
      have h2:j * m y ≤ u.length * (a * y.length+a):=Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n,hn,hr⟩:=d80 e₀ d₀ e₁ g c.time hd hrun y u
      (y.length+u.length * (a * y.length+a)) hL
    have hLV:y.length+u.length * (a * y.length+a) ≤
        (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp:=d37 c.time hLV
    have hmul:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
          2 * (y.length+u.length * (a * y.length+a))+3) ≤
        (y.length+u.length) * (Polynomial.eval
          ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))
            c.time +
            2 * ((y.length+u.length) +
              (y.length+u.length) * (a * (y.length+u.length)+a))+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,d9]
    exact d70 _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm:=iterM c.tm e₀ d₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun q =>
      { steps:=Classical.choose (key q)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l=>some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
theorem iter_polyTime (g:List Bool → List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (k:ℕ) (hk:∀ y:List Bool,(g y).length ≤ y.length+k) :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
  iter_polyTime_measure g c (fun _=>k) k (fun _=>le_rfl) hk (fun _=>Nat.le_add_left k _)
end Lib.Machines.Iter
end MachinePart2083
section MachinePart2283
namespace Lib.Machines
open PEqualNP.Library
private theorem d2 {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ = l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
private theorem d8 {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ = []:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [hφ,ih]
theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg:PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a=>g (f a)):=by
  obtain ⟨c1⟩:=hf
  obtain ⟨c2⟩:=hg
  exact d77 ea eb ec f g c1 c2
theorem d84 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.2,p.1)):=by
  refine d10 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some (Sum.inl b)) s)
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some (Sum.inr b)) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ Sum.inl (fun _=>rfl) w,
    d2 Sum.inl _ Sum.inr (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
theorem d171 :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(x,x)):=by
  refine d10 _ _ _
    (fun b:Bool=>some (Sum.inl b)) (fun b:Bool=>some (Sum.inr b)) ?_
  intro x
  have h1:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inl (β := Bool) b))
    Sum.inl (fun _=>rfl) x
  have h2:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inr (α := Bool) b))
    Sum.inr (fun _=>rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair,h1,h2]
theorem d170 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d8 Sum.inr _ (fun _=>rfl) w]
  simp
theorem d169 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.2):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d8 Sum.inl _ (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
theorem d74 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1++p.2):=by
  refine d7 _ _ _
    (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
  rintro ⟨x,w⟩
  simp only [encodePair,List.filterMap_append]
  rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
    d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
  simp
theorem d38 {f:List Bool → List Bool}
    (hf:Lib.CPTs f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(f p.1,p.2)):=by
  obtain ⟨c⟩:=hf
  exact d61 f c
theorem d101 {g:List Bool → List Bool}
    (hg:Lib.CPTs g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.1,g p.2)) :=
  cpt_comp (cpt_comp d84 (d38 hg)) d84
theorem cpt_pair {f g:List Bool → List Bool}
    (hf:Lib.CPTs f)
    (hg:Lib.CPTs g) :
    PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
      PEqualNP.Library.encodePair (fun x:List Bool=>(f x,g x)) :=
  cpt_comp (cpt_comp d171 (d101 hg)) (d38 hf)
theorem cpt_id :
    Lib.CPTs (fun x:List Bool=>x):=by
  refine d7 _ _ _ (fun b:Bool=>some b) ?_
  intro x
  have h:=d2 (fun b:Bool=>b) (fun b:Bool=>some b) (fun b=>b)
    (fun _=>rfl) x
  simp only [List.map_id'] at h
  exact h.symm
end Lib.Machines
end MachinePart2283
section MachinePart2386
namespace Lib.Machines
open Turing
def fstRun {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q,[]=>(fin q).toList
  | q,a :: l=>(δ q a).2.toList++fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q,[]=>(fin q).toList
  | q,a :: l=>(δ q a).2.1.toList++(δ q a).2.2.toList++fstRun2 δ fin (δ q a).1 l
theorem d36 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁)
    (q:Q) (l:List Γ₀) :
    fstRun δ fin q l=fstRun2 (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [fstRun,fstRun2,ih]
inductive TrK:Type
  | inp | tmp | out
  deriving DecidableEq
instance:Fintype TrK :=
  Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK → Type
  | .inp => Γ₀
  | .tmp=>Q × Option Γ₀
  | .out => Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q × Option Γ₀ × Bool
def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q,some a)=>(δ q a).2.1
  | (q,none)=>fin q
def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q × Option Γ₀ → Option Γ₁
  | (q,some a)=>(δ q a).2.2
  | (_,none)=>none
def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁)
    (e:Q × Option Γ₀):List Γ₁ :=
  (trO1 δ fin e).toList++(trO2 δ e).toList
def d21 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q → List Γ₀ → List (Q × Option Γ₀)
  | q,[]=>[(q,none)]
  | q,a :: l=>(q,some a) :: d21 δ (δ q a).1 l
theorem d57 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q:Q) (l:List Γ₀) :
    (d21 δ q l).length=l.length+1:=by
  induction l generalizing q with
  | nil=>rfl
  | cons a l ih=>simp [d21,ih]
theorem d85 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q:Q)
    (l:List Γ₀):(d21 δ q l).flatMap (trOut δ fin)=fstRun2 δ fin q l:=by
  induction l generalizing q with
  | nil=>simp [d21,trOut,trO1,trO2,fstRun2]
  | cons a l ih=>simp [d21,trOut,trO1,trO2,fstRun2,ih]
def d65 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s=>(o s).isSome)
    (match d with
      | some dd => .push .out (fun s=>(o s).getD dd) next
      | none=>next)
    next
def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o=>(s.1,o,o.isSome))
      (.branch (fun s=>s.2.2)
        (.push .tmp (fun s=>(s.1,s.2.1))
          (.load (fun s=>(match s.2.1 with
              | some a=>(δ s.1 a).1
              | none=>s.1,none,false))
            (.goto fun _=>false)))
        (.push .tmp (fun s=>(s.1,none))
          (.load (fun _=>(q₀,none,false)) (.goto fun _=>true))))
  | true =>
    .pop .tmp (fun _ o=>match o with
        | some e=>(e.1,e.2,true)
        | none=>(q₀,none,false))
      (.branch (fun s=>s.2.2)
        (d65 (fun s=>trO2 δ (s.1,s.2.1)) d
          (d65 (fun s=>trO1 δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
        .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin:Q → Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
  K:=TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main:=false
  σ := TrS Γ₀ Q
  initialState:=(q₀,none,false)
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=trProg δ fin q₀ d
def trSt (l:List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
  | .inp=>l
  | .tmp=>t
  | .out=>u
theorem d40 (l l':List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (trSt l t u) .inp l'=trSt l' t u:=by
  funext k;cases k <;> simp [trSt]
theorem d19 (l:List Γ₀) (t t':List (Q × Option Γ₀)) (u:List Γ₁) :
    Function.update (trSt l t u) .tmp t'=trSt l t' u:=by
  funext k;cases k <;> simp [trSt]
theorem d78 (l:List Γ₀) (t:List (Q × Option Γ₀)) (u u':List Γ₁) :
    Function.update (trSt l t u) .out u'=trSt l t u':=by
  funext k;cases k <;> simp [trSt]
theorem d87 (l:List Γ₀) :
    (trSt l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
  funext k;cases k <;> simp [trSt]
theorem d121 (u:List Γ₁) :
    (trSt [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
  funext k;cases k <;> simp [trSt]
abbrev TrCfg (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem d25 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁) (hd:∀ _ : Γ₁,d≠none)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.stepAux (d65 o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList++u)):=by
  cases ho:o s with
  | none=>cases d <;> simp [d65,TM2.stepAux,ho]
  | some y =>
    cases d with
    | none=>exact absurd rfl (hd y)
    | some dd=>simp [d65,TM2.stepAux,ho,trSt,d78]
variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
  (d:Option Γ₁)
theorem d123 (s:TrS Γ₀ Q) (a : Γ₀) (l:List Γ₀) (t:List (Q × Option Γ₀))
    (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d142 (s:TrS Γ₀ Q) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(q₀,none,false),trSt [] ((s.1,none) :: t) u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d122 (hd:∀ _ : Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q × Option Γ₀)
    (t:List (Q × Option Γ₀)) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩:=by
  simp only [TM2.step,trProg,TM2.stepAux]
  have e1:(trSt [] (e :: t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e :: t:=rfl
  rw [e1]
  simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
  rw [d19,d25 _ _ hd,d25 _ _ hd]
  simp [TM2.stepAux,trOut]
theorem d141 (s:TrS Γ₀ Q) (u:List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] [] u⟩:TrCfg Γ₀ Γ₁ Q) =
      some ⟨none,(q₀,none,false),trSt [] [] u⟩:=by
  simp [TM2.step,trProg,TM2.stepAux,trSt,d19]
theorem d140 (u:List Γ₁) :
    ∀ (l:List Γ₀) (t:List (Q × Option Γ₀)) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
          (some (⟨some false,s,trSt l t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(q₀,none,false),trSt [] ((d21 δ s.1 l).reverse++t) u⟩:=by
  intro l
  induction l with
  | nil=>intro t s;exact d142 δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ :=
      d123 δ fin q₀ d s a l t u
    rw [e,ih]
    simp [d21]
theorem d139 (hd:∀ _ : Γ₁,d≠none) :
    ∀ (t:List (Q × Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length+1]
          (some (⟨some true,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none,(q₀,none,false),trSt [] [] (t.reverse.flatMap (trOut δ fin)++u)⟩:=by
  intro t
  induction t with
  | nil=>intro u s;exact d141 δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e':flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩ :=
      d122 δ fin q₀ d hd s e t u
    rw [e',ih]
    simp [List.flatMap_append]
theorem d138 [Fintype Γ₀] [Fintype Q] (hd:∀ _ : Γ₁,d≠none) (l:List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1 +
    (l.length+1)] (some c)) (d4 (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (d5 (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
    (some (⟨some false,(q₀,none,false),Function.update (fun _=>[]) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none,(q₀,none,false),Function.update (fun _=>[]) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
      (some (⟨some false,(q₀,none,false),trSt l [] []⟩:TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩:=by
    have:=d140 δ fin q₀ d [] l [] (q₀,none,false)
    rw [List.append_nil] at this
    exact this
  have hB:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1]
      (some (⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none,(q₀,none,false),trSt [] [] (fstRun2 δ fin q₀ l)⟩:=by
    have:=d139 δ fin q₀ d hd (d21 δ q₀ l).reverse [] (q₀,none,false)
    rw [List.length_reverse,d57,List.reverse_reverse,d85,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply,← d87,hA,hB,d121]
theorem fst2_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin:Q → Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ _ : βΓ,d≠none:=by
    intro y
    have hn:Nonempty βΓ := ⟨y⟩
    simp [d,hn]
  exact ⟨{
    tm:=trM δ fin q₀ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 3
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=d138 δ fin q₀ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
theorem fst_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin:Q → Option βΓ) (q₀:Q)
    (h:∀ a,eb (f a)=fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
    (fun a=>(h a).trans (d36 δ fin q₀ (ea a)))
end Lib.Machines
end MachinePart2386
section MachinePart2634
namespace Lib.Machines.Rev
open Turing PEqualNP.Library Lib.Machines
def prog:Unit → TM2.Stmt (fun _:Bool=>Bool) Unit (Option Bool)
  | () =>
    .pop false (fun _ o=>o)
      (.branch (fun s=>s.isSome)
        (.push true (fun s=>s.getD false) (.load (fun _=>none) (.goto fun _=>())))
        .halt)
def tm:FinTM2 where
  K:=Bool
  k₀:=false
  k₁:=true
  Γ _:=Bool
  Λ := Unit
  main:=()
  σ := Option Bool
  initialState:=none
  m:=prog
abbrev RCfg:Type:=TM2.Cfg (fun _:Bool=>Bool) Unit (Option Bool)
def st (l u:List Bool):Bool → List Bool:=fun k=>cond k u l
theorem d79 (l:List Bool) :
    st l []=Function.update (fun _=>([]:List Bool)) false l:=by
  funext k;cases k <;> simp [st]
theorem st_end (u:List Bool) :
    st [] u=Function.update (fun _=>([]:List Bool)) true u:=by
  funext k;cases k <;> simp [st]
theorem d103 (x:Bool) (l u:List Bool) :
    TM2.step prog (⟨some (),none,st (x :: l) u⟩:RCfg) =
      some ⟨some (),none,st l (x :: u)⟩:=by
  simp only [TM2.step,prog,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
    Option.getD_some,Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
theorem d129 (u:List Bool) :
    TM2.step prog (⟨some (),none,st [] u⟩:RCfg)=some ⟨none,none,st [] u⟩:=by
  simp only [TM2.step,prog,TM2.stepAux]
  simp only [st,Bool.cond_false,List.head?_nil,List.tail_nil,Option.isSome_none,
    Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
  funext k;cases k <;> simp [st]
theorem loop:∀ (l u:List Bool),
    (flip bind (TM2.step prog))^[l.length+1] (some (⟨some (),none,st l u⟩:RCfg)) =
      some ⟨none,none,st [] (l.reverse++u)⟩:=by
  intro l
  induction l with
  | nil=>intro u;exact d129 u
  | cons x l ih =>
    intro u
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step prog) (some (⟨some (),none,st (x :: l) u⟩:RCfg)) =
        some ⟨some (),none,st l (x :: u)⟩:=d103 x l u
    rw [e,ih]
    simp
theorem run (l:List Bool) :
    (flip bind (TM2.step prog))^[l.length+1] (some (initList tm l)) =
      some (haltList tm l.reverse):=by
  refine (congrArg (fun c=>(flip bind (TM2.step prog))^[l.length+1] (some c))
    (d4 tm l)).trans (Eq.trans ?_ (congrArg some (d5 tm l.reverse)).symm)
  show (flip bind (TM2.step prog))^[l.length+1]
    (some (⟨some (),none,Function.update (fun _=>[]) false l⟩:RCfg)) =
    some (⟨none,none,Function.update (fun _=>[]) true l.reverse⟩:RCfg)
  rw [← d79,loop,← st_end]
  simp
noncomputable def reverseComputable :
    TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x)
      (fun x:List Bool=>x.reverse) where
  tm:=tm
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.X+1
  outputsFun a :=
    { steps:=a.length+1
      evals_in_steps:=by
        have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
        exact (congrArg (fun l=>(flip bind (TM2.step prog))^[a.length+1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l=>some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m:=by simp }
end Lib.Machines.Rev
end MachinePart2634
section MachinePart2714
namespace Lib.Universal
def un (n:ℕ):List Bool:=List.replicate n true
def pairB (a b:List Bool):List Bool:=un a.length++false :: (a++b)
def unpairB (s:List Bool):List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem unpairB_pairB (a b:List Bool):unpairB (pairB a b)=(a,b):=by
  have h1:(pairB a b).takeWhile id=un a.length:=by
    simp [pairB,un]
  have h2:(pairB a b).dropWhile id=false :: (a++b):=by
    simp [pairB,un]
  simp [unpairB,h1,h2,un]
end Lib.Universal
end MachinePart2714
section MachinePart2729
namespace Lib.Universal
def bflag (b:Bool):List Bool:=if b then [true] else []
@[simp] theorem un_zero:un 0=[]:=rfl
@[simp] theorem un_length (n:ℕ):(un n).length=n:=List.length_replicate
theorem un_succ (n:ℕ):un (n+1)=true :: un n:=rfl
theorem un_inj {a b:ℕ} (h:un a=un b):a=b:=by
  have:=congrArg List.length h
  simpa [un] using this
def hd (s:List Bool):List Bool:=s.takeWhile id
def dropN (s:List Bool):List Bool:=(s.dropWhile id).tail
def sel (f a b:List Bool):List Bool:=if f=[] then a else b
def mulU (u v:List Bool):List Bool:=un (u.length * v.length)
def spread (s:List Bool):List Bool:=s.flatMap fun b=>if b then [true,false] else [false]
def blank (s:List Bool):List Bool:=s.map fun _=>false
theorem sel_append_left (f p a b:List Bool):sel f (p++a) (p++b)=p++sel f a b:=by
  unfold sel;split_ifs <;> rfl
theorem hd_length (s:List Bool):(hd s).length ≤ s.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix id)
theorem dropN_length (s:List Bool):(dropN s).length ≤ s.length:=by
  have h1:=List.IsSuffix.length_le (List.dropWhile_suffix (p:=id) (l:=s))
  simp only [dropN,List.length_tail]
  omega
theorem iter_length (g:List Bool → List Bool) (hg:∀ s,(g s).length ≤ s.length) (k:ℕ) :
    ∀ s,(g^[k] s).length ≤ s.length:=by
  induction k with
  | zero=>intro s;exact le_rfl
  | succ k ih=>intro s;rw [Function.iterate_succ_apply];exact (ih _).trans (hg s)
theorem sel_length (f a b:List Bool) (N:ℕ) (ha:a.length ≤ N) (hb:b.length ≤ N) :
    (sel f a b).length ≤ N:=by
  unfold sel;split_ifs <;> assumption
theorem unpairB_length (s:List Bool) :
    2 * (unpairB s).1.length+(unpairB s).2.length ≤ s.length:=by
  have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s))
  simp only [List.length_append] at h
  simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
  omega
theorem pairB_length (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
  simp [pairB];omega
end Lib.Universal
end MachinePart2729
section MachinePart2770
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem d39 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private theorem d119 {A B C:Type} (φl:A → Option C) (φr:B → Option C) (x:List A)
    (w:List B) :
    (x.map Sum.inl++w.map Sum.inr).filterMap (Sum.elim φl φr) =
      x.filterMap φl++w.filterMap φr:=by
  have h1:∀ x:List A,(x.map Sum.inl).filterMap (Sum.elim φl φr)=x.filterMap φl:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>simp [List.filterMap_cons,ih]
  have h2:∀ w:List B,(w.map Sum.inr).filterMap (Sum.elim φl φr)=w.filterMap φr:=by
    intro w;induction w with
    | nil=>rfl
    | cons a l ih=>simp [List.filterMap_cons,ih]
  rw [List.filterMap_append,h1,h2]
private theorem d100 {A C:Type} (g:A → C) (l:List A) :
    l.filterMap (fun a=>some (g a))=l.map g:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [ih]
private theorem d160 {A C:Type} (l:List A) :
    l.filterMap (fun _:A=>(none:Option C))=[]:=by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp
theorem d117 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>pairB p.1 p.2):=by
  have hA:ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(p.1,p.1++p.2)):=by
    refine d10 _ _ _
      (Sum.elim (fun b:Bool=>some (Sum.inl b)) (fun _:Bool=>none))
      (Sum.elim (fun b:Bool=>some (Sum.inr b)) (fun b:Bool=>some (Sum.inr b))) ?_
    rintro ⟨x,w⟩
    simp only [encodePair]
    rw [d119,d119,d100,d100,d100,d160]
    simp
  have hU:Lib.CPTs
      (fun a:List Bool=>a.map (fun _=>true)++[false]):=by
    refine fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
      (fun _=>some false) () ?_
    intro a
    induction a with
    | nil=>rfl
    | cons b l ih =>
      simp only [fstRun,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
      rw [← ih];rfl
  refine d39 (cpt_comp (cpt_comp hA (d38 hU)) d74) ?_
  rintro ⟨x,w⟩
  simp [pairB,un]
theorem d35 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then p.2 else []):=by
  obtain ⟨c⟩:=d11 []
  have hI:=Iter.iter_polyTime (fun _:List Bool=>([]:List Bool)) c 0 (by simp)
  refine d39 (cpt_comp d84 hI) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp [Function.iterate_succ_apply']
theorem d62 :
    ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>if p.1=[] then [] else p.2):=by
  have hneg:Lib.CPTs
      (fun x:List Bool=>if x=[] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (d11 [true])) d35
  refine d39 (cpt_comp (d38 hneg) d35) ?_
  rintro ⟨x,w⟩
  cases x with
  | nil=>simp
  | cons b l=>simp
theorem cpt_bitFlag {α αΓ : Type} {ea : α → List αΓ} {f : α → Bool}
    (hf:ComputableInPolyTime ea Computability.encodeBool f) :
    ComputableInPolyTime ea (fun x:List Bool=>x) (fun a=>if f a then [true] else []):=by
  have h:ComputableInPolyTime Computability.encodeBool (fun x:List Bool=>x)
      (fun b:Bool=>if b then [true] else []):=by
    refine d7 _ _ _ (fun b:Bool=>if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h
private def encT (u:List Bool):List Bool:=u.flatMap (fun b=>[true,b])
private def encF (v:List Bool):List Bool:=v.flatMap (fun b=>[false,b])
private def twD:Bool → Bool → Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private theorem d137 (l:List Bool) :
    fstRun twD (fun _=>none) false l=[] ∧
      fstRun twD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [fstRun,twD,ih.1,ih.2]
private def e0D:Bool → Bool → Bool × Option Bool × Option Bool
  | false,true=>(false,none,none)
  | false,false=>(true,none,none)
  | true,b=>(true,some false,some b)
private theorem d83 (l:List Bool) :
    fstRun2 e0D (fun _=>none) true l=encF l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun2,e0D,encF,ih]
private theorem d73 (l:List Bool) :
    fstRun2 e0D (fun _=>none) false l=encF (l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [fstRun2,e0D,ih,d83]
private def mkD:Bool × Bool → Bool → (Bool × Bool) × Option Bool
  | (d,false),t=>((d || !t,true),some (t || !d))
  | (d,true),b=>((d,false),some b)
private def mk (l:List Bool):List Bool:=fstRun mkD (fun _=>none) (false,false) l
private theorem d91 (q:Bool × Bool) (l:List Bool) :
    (fstRun mkD (fun _=>none) q l).length=l.length:=by
  induction l generalizing q with
  | nil=>rfl
  | cons b l ih=>obtain ⟨d,ph⟩:=q;cases ph <;> simp [fstRun,mkD,ih]
private theorem d130 (v:List Bool) :
    fstRun mkD (fun _=>none) (true,false) (encF v)=encF v:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [fstRun,mkD,encF] at ih ⊢;exact ih
private theorem d69 (u r:List Bool) :
    fstRun mkD (fun _=>none) (false,false) (encT u++r) =
      encT u++fstRun mkD (fun _=>none) (false,false) r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [fstRun,mkD,encT] at ih ⊢;exact ih
private theorem mk_nil (u:List Bool):mk (encT u++encF [])=encT u++encF []:=by
  unfold mk;rw [d69];rfl
private theorem d153 (u:List Bool) (b:Bool) (v:List Bool) :
    mk (encT u++encF (b :: v))=encT (u++[b])++encF v:=by
  unfold mk
  rw [d69]
  have h:fstRun mkD (fun _=>none) (false,false) (encF (b :: v)) =
      true :: b :: encF v:=by
    have h':=d130 v
    simp [fstRun,mkD,encF] at h' ⊢
    exact h'
  rw [h]
  simp [encT]
private theorem d152 (k:ℕ):∀ u t:List Bool,
    mk^[k] (encT u++encF t)=encT (u++t.take k)++encF (t.drop k):=by
  induction k with
  | zero=>intro u t;simp
  | succ k ih =>
    intro u t
    rw [Function.iterate_succ_apply]
    cases t with
    | nil=>rw [mk_nil,ih];simp
    | cons b t=>rw [d153,ih];simp
private def dcD:Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
  | none,t=>(some t,none)
  | some t,b=>(none,some (if t then Sum.inl b else Sum.inr b))
private theorem dcD_F (v:List Bool) :
    fstRun dcD (fun _=>none) none (encF v)=v.map Sum.inr:=by
  induction v with
  | nil=>rfl
  | cons b v ih=>simp [fstRun,dcD,encF] at ih ⊢;exact ih
private theorem dcD_T (u r:List Bool) :
    fstRun dcD (fun _=>none) none (encT u++r) =
      u.map Sum.inl++fstRun dcD (fun _=>none) none r:=by
  induction u with
  | nil=>rfl
  | cons b u ih=>simp [fstRun,dcD,encT] at ih ⊢;exact ih
private def rawDec (l:List (Bool ⊕ Bool)):List Bool × List Bool :=
  (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem d68 (u v:List Bool) :
    rawDec (u.map Sum.inl++v.map Sum.inr)=(u,v):=by
  have h1:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a :: ·) ih
  have h2:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h3:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = []:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact ih
  have h4:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x:=by
    intro x;induction x with
    | nil=>rfl
    | cons a l ih=>exact congrArg (a :: ·) ih
  simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
theorem d34 :
    ComputableInPolyTime (fun x:List Bool=>x) encodePair unpairB:=by
  have hTw:Lib.CPTs
      (fun s:List Bool=>s.takeWhile id) :=
    fst_polyTime _ _ _ twD (fun _=>none) true (fun s=>(d137 s).2.symm)
  have hE0:Lib.CPTs
      (fun s:List Bool=>encF (s.dropWhile id).tail) :=
    fst2_polyTime _ _ _ e0D (fun _=>none) false (fun s=>(d73 s).symm)
  have hMk:Lib.CPTs mk :=
    fst_polyTime _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
  obtain ⟨cMk⟩:=hMk
  have hIt:=Iter.iter_polyTime mk cMk 0 (fun y=>by simp [mk,d91])
  have hDc:ComputableInPolyTime (fun x:List Bool=>x) (fun l:List (Bool ⊕ Bool)=>l)
      (fun l:List Bool=>fstRun dcD (fun _=>none) none l) :=
    fst_polyTime _ _ _ dcD (fun _=>none) none (fun _=>rfl)
  have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool)=>l) encodePair rawDec:=by
    refine d10 _ _ _
      (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map Sum.inl)
      (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map Sum.inr) ?_
    intro l
    simp only [rawDec,encodePair,List.map_filterMap]
  refine d39 (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
  intro s
  have h:=d152 (s.takeWhile id).length [] (s.dropWhile id).tail
  have e:encT []++encF (s.dropWhile id).tail=encF (s.dropWhile id).tail:=rfl
  rw [e] at h
  simp only [h,List.nil_append]
  rw [dcD_T,dcD_F,d68]
  rfl
theorem cpt_iterB (g:List Bool → List Bool)
    (hg:Lib.CPTs g)
    (m:List Bool → ℕ) (a:ℕ)
    (hm:∀ y,m (g y) ≤ m y) (hgl:∀ y,(g y).length ≤ y.length+m y)
    (ha:∀ y,m y ≤ a * y.length+a) :
    Lib.CPTs
      (fun s:List Bool=>g^[(unpairB s).2.length] (unpairB s).1):=by
  obtain ⟨c⟩:=hg
  exact cpt_comp d34 (Iter.iter_polyTime_measure g c m a hm hgl ha)
end Lib.Universal
end MachinePart2770
section MachinePart2999
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
    ComputableInPolyTime ea eb f':=by
  obtain rfl:f=f':=funext e
  exact h
private def hdD:Bool → Bool → Bool × Option Bool
  | true,true=>(true,some true)
  | _,_=>(false,none)
private theorem d159 (l:List Bool) :
    fstRun hdD (fun _=>none) false l=[] ∧
      fstRun hdD (fun _=>none) true l=l.takeWhile id:=by
  induction l with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b l ih=>cases b <;> simp [fstRun,hdD,ih.1,ih.2]
theorem cpt_hd :
    Lib.CPTs hd :=
  fst_polyTime _ _ _ hdD (fun _=>none) true (fun s=>(d159 s).2.symm)
private def dnD:Bool → Bool → Bool × Option Bool
  | false,true=>(false,none)
  | false,false=>(true,none)
  | true,b=>(true,some b)
private theorem d135 (l:List Bool):fstRun dnD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,dnD,ih]
private theorem d116 (l:List Bool) :
    fstRun dnD (fun _=>none) false l=(l.dropWhile id).tail:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>cases b <;> simp [fstRun,dnD,ih,d135]
theorem cpt_dropN :
    Lib.CPTs dropN :=
  fst_polyTime _ _ _ dnD (fun _=>none) false (fun s=>(d116 s).symm)
private def tlD:Bool → Bool → Bool × Option Bool
  | false,_=>(true,none)
  | true,b=>(true,some b)
private theorem d128 (l:List Bool):fstRun tlD (fun _=>none) true l=l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,tlD,ih]
private theorem d102 (l:List Bool):fstRun tlD (fun _=>none) false l=l.tail:=by
  cases l with
  | nil=>rfl
  | cons b l=>simp [fstRun,tlD,d128]
theorem cpt_tail :
    Lib.CPTs
      (fun s:List Bool=>s.tail) :=
  fst_polyTime _ _ _ tlD (fun _=>none) false (fun s=>(d102 s).symm)
private theorem d118 (l:List Bool) :
    fstRun (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) () l=blank l:=by
  induction l with
  | nil=>rfl
  | cons b l ih=>simp [fstRun,blank] at ih ⊢;exact ih
theorem cpt_blank :
    Lib.CPTs blank :=
  fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) ()
    (fun s=>(d118 s).symm)
theorem cpt_const (l:List Bool) :
    Lib.CPTs
      (fun _:List Bool=>l) :=
  d11 l
theorem cpt_unpairB1 :
    Lib.CPTs
      (fun s:List Bool=>(unpairB s).1) :=
  cptc (cpt_comp d34 d170) (fun _=>rfl)
theorem cpt_unpairB2 :
    Lib.CPTs
      (fun s:List Bool=>(unpairB s).2) :=
  cptc (cpt_comp d34 d169) (fun _=>rfl)
theorem cpt_app2 {u v:List Bool → List Bool}
    (hu:Lib.CPTs u)
    (hv:Lib.CPTs v) :
    Lib.CPTs
      (fun s=>u s++v s) :=
  cptc (cpt_comp (cpt_pair hu hv) d74) (fun _=>rfl)
theorem cpt_pairB2 {u v:List Bool → List Bool}
    (hu:Lib.CPTs u)
    (hv:Lib.CPTs v) :
    Lib.CPTs
      (fun s=>pairB (u s) (v s)) :=
  cptc (cpt_comp (cpt_pair hu hv) d117) (fun _=>rfl)
theorem cpt_sel {f a b:List Bool → List Bool}
    (hf:Lib.CPTs f)
    (ha:Lib.CPTs a)
    (hb:Lib.CPTs b) :
    Lib.CPTs
      (fun s=>sel (f s) (a s) (b s)):=by
  have h1:=cpt_comp (cpt_pair hf ha) d35
  have h2:=cpt_comp (cpt_pair hf hb) d62
  refine cptc (cpt_app2 h1 h2) ?_
  intro s
  by_cases h:f s=[] <;> simp [sel,h]
theorem cpt_iterLen {g cnt arg:List Bool → List Bool}
    (hg:Lib.CPTs g)
    (hgl:∀ s,(g s).length ≤ s.length)
    (hcnt:Lib.CPTs cnt)
    (harg:Lib.CPTs arg) :
    Lib.CPTs
      (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 0 (fun y=>by simpa using hgl y)
  exact cptc (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
end Lib.Universal
end MachinePart2999
section Conversions
open PEqualNP.Library Lib.Machines Lib.Universal Lib.Machines.Rev
abbrev CPTs (f:List Bool → List Bool):Prop :=
  ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
def q22 {K:Type} {Γ : K → Type} {Λ σ : Type}:Turing.TM2.Stmt Γ Λ σ → Set (Σ k,Γ k)
  | .push k g q=>Set.range (fun v=>(⟨k,g v⟩ : Σ k,Γ k)) ∪ q22 q
  | .peek _ _ q=>q22 q
  | .pop _ _ q=>q22 q
  | .load _ q=>q22 q
  | .branch _ q₁ q₂=>q22 q₁ ∪ q22 q₂
  | .goto _ => ∅
  | .halt => ∅
lemma q110 {K:Type} {Γ : K → Type} {Λ σ : Type} [Finite σ]
    (q:Turing.TM2.Stmt Γ Λ σ):(q22 q).Finite:=by
  induction q with
  | push _ _ _ ih=>exact (Set.finite_range _).union ih
  | peek _ _ _ ih=>exact ih
  | pop _ _ _ ih=>exact ih
  | load _ _ ih=>exact ih
  | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
  | goto _=>exact Set.finite_empty
  | halt=>exact Set.finite_empty
def q29 {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) :
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ q22 q → s ∈ T k) →
    Turing.TM2.Stmt (fun k=>{s : Γ k // s ∈ T k}) Λ σ
  | .push k g q,h => .push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
      (q29 T q (fun j s hs=>h j s (Or.inr hs)))
  | .peek k f q,h => .peek k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .pop k f q,h => .pop k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
  | .load a q,h => .load a (q29 T q h)
  | .branch f q₁ q₂,h => .branch f
      (q29 T q₁ (fun j s hs=>h j s (Or.inl hs)))
      (q29 T q₂ (fun j s hs=>h j s (Or.inr hs)))
  | .goto f,_ => .goto f
  | .halt,_ => .halt
def q67 {K:Type} {Γ : K → Type} {Λ σ : Type} (T:∀ k,Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s : Γ k // s ∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
  ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma q181 {K:Type} {Γ : K → Type} {Λ σ : Type} (T:∀ k,Set (Γ k)) :
    Function.Injective (q67 (Λ := Λ) (σ := σ) T):=by
  rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
  simp only [q67,Turing.TM2.Cfg.mk.injEq] at h
  obtain ⟨rfl,rfl,hS⟩:=h
  congr 1
  funext k
  exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma q84 {K:Type} [DecidableEq K] {Γ : K → Type} (T:∀ k,Set (Γ k))
    (S:∀ k,List {s : Γ k // s ∈ T k}) (k:K) (l:List {s : Γ k // s ∈ T k}) :
    (fun j=>(Function.update S k l j).map Subtype.val) =
      Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
  funext j
  by_cases h:j=k
  · subst h;simp
  · simp [h]
lemma q125 {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
    (hq:∀ k s,(⟨k,s⟩ : Σ j,Γ j) ∈ q22 q → s ∈ T k)
    (v : σ) (S:∀ k,List {s : Γ k // s ∈ T k}) :
    q67 T (Turing.TM2.stepAux (q29 T q hq) v S) =
      Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
  induction q generalizing v S with
  | push k g q ih =>
    simp only [q29,Turing.TM2.stepAux]
    rw [ih,q84];rfl
  | peek k f q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [List.head?_map])
  | pop k f q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact (ih hq _ _).trans (by rw [q84,List.head?_map,List.map_tail])
  | load a q ih =>
    simp only [q29,Turing.TM2.stepAux]
    exact ih hq (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [q29,Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ v S
    · exact ih₁ _ v S
  | goto f=>rfl
  | halt=>rfl
lemma cpt_to_fast {f:List Bool → List Bool} (hf:CPTs f) :
    ∃ M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f,
      ∀ i,Finite (M.tm.Γ i):=by
  classical
  obtain ⟨c⟩:=hf
  let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
  let _:Fintype c.tm.K:=c.tm.kFin
  let _:Fintype c.tm.Λ := c.tm.ΛFin
  let _:Fintype c.tm.σ := c.tm.σFin
  let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
  let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k =>
    {s | k=c.tm.k₀∨k=c.tm.k₁∨(⟨k,s⟩ : Σ j,c.tm.Γ j) ∈ ⋃ l:c.tm.Λ,q22 (c.tm.m l)}
  let e₀:{s:c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inl rfl⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let e₁:{s:c.tm.Γ c.tm.k₁ // s ∈ T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun:=Subtype.val
      invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s ∈ T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
  let tm':Turing.FinTM2 :=
    { K:=c.tm.K
      kDecidableEq:=c.tm.kDecidableEq
      kFin:=c.tm.kFin
      k₀:=c.tm.k₀
      k₁:=c.tm.k₁
      Γ := fun k=>{s:c.tm.Γ k // s ∈ T k}
      Λ := c.tm.Λ
      main:=c.tm.main
      ΛFin:=c.tm.ΛFin
      σ := c.tm.σ
      initialState:=c.tm.initialState
      σFin:=c.tm.σFin
      Γk₀Fin:=hΓ0Fin
      m:=fun l=>q29 T (c.tm.m l) (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j=c.tm.k₀
    · subst h0;exact Finite.of_fintype _
    · by_cases h1:j=c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,q22 (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>q110 (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩ : ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,Option.map (q67 T) (tm'.step cfg)=c.tm.step (q67 T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (q67 T (Turing.TM2.stepAux (q29 T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (q125 T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (q67 T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (q67 T cfg)):=by
    intro steps
    induction steps with
    | zero=>intro cfg;rfl
    | succ steps ih =>
      intro cfg
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih];rfl
      | some cfg' =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  let M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f :=
    { tm:=tm'
      inputAlphabet:=e₀.trans c.inputAlphabet
      outputAlphabet:=e₁.trans c.outputAlphabet
      time:=c.time
      outputsFun:=fun a =>
        { steps:=(c.outputsFun a).steps
          evals_in_steps:=by
            have horig:=(c.outputsFun a).evals_in_steps
            have hinit:q67 T (Turing.initList tm' (a.map (e₀.trans c.inputAlphabet).invFun)) =
                Turing.initList c.tm (a.map c.inputAlphabet.invFun):=by
              simp only [q67,Turing.initList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₀
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,List.map_nil]
            have hhalt:q67 T (Turing.haltList tm' ((f a).map (e₁.trans c.outputAlphabet).invFun)) =
                Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun):=by
              simp only [q67,Turing.haltList]
              congr 1;funext k
              by_cases hk:k=c.tm.k₁
              · subst hk;dsimp only [tm']
                simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
              · dsimp only [tm']
                simp only [hk,↓reduceDIte,List.map_nil]
            apply Option.map_injective (q181 T)
            rw [hiter,hinit,horig]
            exact (congrArg some hhalt).symm
          steps_le_m:=(c.outputsFun a).steps_le_m } }
  exact ⟨M,hFin⟩
lemma q39 {f g:List Bool → List Bool} (hf:CPTs f) (h:∀ x,f x=g x):CPTs g:=by
  have:f=g:=funext h
  rwa [← this]
lemma q157:CPTs (fun s:List Bool=>s.reverse):=⟨Rev.reverseComputable⟩
lemma q121 {g cnt arg:List Bool → List Bool} (k:ℕ)
    (hg:CPTs g) (hgl:∀ s,(g s).length ≤ s.length+k)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c k hgl
  exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q213 {g cnt arg:List Bool → List Bool}
    (m:List Bool → ℕ) (a:ℕ)
    (hg:CPTs g)
    (hm:∀ y,m (g y) ≤ m y)
    (hgl:∀ y,(g y).length ≤ y.length+m y)
    (ha:∀ y,m y ≤ a * y.length+a)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  obtain ⟨c⟩:=hg
  have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
      (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure g c m a hm hgl ha
  exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q7 (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
  simp [pairB,un];omega
lemma q0 (y:List Bool) :
    2 * (unpairB y).1.length+(unpairB y).2.length ≤ y.length:=by
  dsimp only [unpairB]
  have hsplit:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
  have hylen:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
    conv_lhs=>rw [hsplit]
    exact List.length_append
  set a:=(y.takeWhile id).length
  set t:=(y.dropWhile id).tail
  have htlen:t.length ≤ (y.dropWhile id).length:=by
    dsimp only [t];cases y.dropWhile id <;> simp
  have htake:(t.take a).length=min a t.length:=List.length_take
  have hdrop:(t.drop a).length=t.length - a:=List.length_drop
  omega
lemma q18 {g cnt arg:List Bool → List Bool} (c:ℕ)
    (hg:CPTs g)
    (hw:∀ y,(unpairB (g y)).1=(unpairB y).1)
    (hgl:∀ y,(g y).length ≤ y.length+c * (unpairB y).1.length+c)
    (hcnt:CPTs cnt) (harg:CPTs arg) :
    CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
  refine q213 (fun y=>c * (unpairB y).1.length+c) c hg
    (fun y=>by rw [hw y])
    (fun y=>by have:=hgl y;omega)
    (fun y=>by
      have h1:(unpairB y).1.length ≤ y.length:=by have:=q0 y;omega
      have h2:=Nat.mul_le_mul_left c h1
      omega)
    hcnt harg
def q47 (s:List Bool):List Bool:=List.replicate s.length true
lemma q152 (s:List Bool):(q47 s).length=s.length:=List.length_replicate
lemma q89:CPTs q47 :=
  fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true)) (fun _=>none) () (fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp only [fstRun,q47,List.length_cons,List.replicate_succ];exact congrArg (true :: ·) ih)
def q79 (s:List Bool):List Bool :=
  pairB (unpairB s).1 ((unpairB s).2++(unpairB s).1)
lemma q169:CPTs q79 :=
  cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 cpt_unpairB1)
lemma q99 (a:List Bool):∀ k b,q79^[k] (pairB (q47 a) b)=pairB (q47 a) (b++un (k * a.length))
  | 0,b=>by simp [un]
  | k+1,b=>by
    rw [Function.iterate_succ_apply,q79,unpairB_pairB,q99 a k (b++q47 a)]
    congr 1
    simp [q47,un,List.append_assoc,← List.replicate_add,Nat.succ_mul,Nat.add_comm]
lemma q42 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>mulU (u s) (v s)):=by
  have h1:CPTs (fun s=>q79^[(u s).length] (pairB (q47 (v s)) [])) :=
    q18 1 q169 (fun y=>by rw [q79,unpairB_pairB])
      (fun y=>by
        rw [q79,q7,List.length_append]
        have:=q0 y
        omega)
      hu (cpt_pairB2 (cpt_comp hv q89) (cpt_const []))
  have h2:=cpt_comp h1 cpt_unpairB2
  have heq:(fun s=>(unpairB (q79^[(u s).length] (pairB (q47 (v s)) []))).2)=(fun s=>mulU (u s) (v s)):=by
    funext s
    rw [q99,unpairB_pairB,List.nil_append];rfl
  rwa [heq] at h2
def q17 (s:List Bool):List Bool :=
  match s with
  | true :: _=>[true]
  | _=>[]
lemma q35:CPTs q17 :=
  fst_polyTime _ _ _
    (fun (st:Bool) (b:Bool)=>if st then (false,if b then some true else none) else (false,none))
    (fun _=>none) true (fun s=>by
      have hfalse:∀ l,fstRun (fun (st:Bool) (b:Bool) =>
          if st then (false,if b then some true else none) else (false,none))
          (fun _=>none) false l=[]:=by
        intro l;induction l with | nil=>rfl | cons b l ih=>simp [fstRun,ih]
      cases s with
      | nil=>rfl
      | cons b l=>cases b <;> simp [fstRun,q17,hfalse])
def q133 (s:List Bool):List Bool:=sel s [true] []
lemma q138:CPTs q133 :=
  cpt_sel cpt_id (cpt_const [true]) (cpt_const [])
def takeN (lenU xs:List Bool):List Bool :=
  (unpairB (q47 lenU++false :: xs)).1
def dropN' (lenU xs:List Bool):List Bool :=
  (unpairB (q47 lenU++false :: xs)).2
lemma q12 (lenU xs:List Bool):takeN lenU xs=xs.take lenU.length:=by
  have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
    simp [q47]
  have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
    simp [q47]
  simp [takeN,unpairB,h1,h2,q152]
lemma q40 (lenU xs:List Bool):dropN' lenU xs=xs.drop lenU.length:=by
  have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
    simp [q47]
  have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
    simp [q47]
  simp [dropN',unpairB,h1,h2,q152]
lemma q24 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>takeN (u s) (v s)) :=
  q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB1) (fun _=>rfl)
lemma cpt_dropN' {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
    CPTs (fun s=>dropN' (u s) (v s)) :=
  q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB2) (fun _=>rfl)
end Conversions
end PEqualNP.Outside.L_meta_33617
namespace PEqualNP.Outside.L_meta_33617
open Lib.Machines Lib.Universal
def val:List Bool → ℕ
  | []=>0
  | b :: l=>b.toNat+2 * val l
lemma q124 (l:List Bool):val l < 2 ^ l.length:=by
  induction l with
  | nil=>simp [val]
  | cons b l ih =>
    simp only [val,List.length_cons,pow_succ]
    cases b <;> simp <;> omega
lemma q58 (a b:List Bool):val (a++b)=val a+2 ^ a.length * val b:=by
  induction a with
  | nil=>simp [val]
  | cons x l ih =>
    simp only [List.cons_append,val,List.length_cons,pow_succ,ih]
    ring
lemma q52 (k:ℕ):val (List.replicate k false)=0:=by
  induction k with
  | zero=>rfl
  | succ k ih=>simp [List.replicate_succ,val,ih]
lemma q37 (l:List Bool):val (blank l)=0:=by
  have h:blank l=List.replicate l.length false:=by
    induction l with
    | nil=>rfl
    | cons _ r ih=>simp [blank,List.replicate_succ,ih]
  rw [h,q52]
lemma q33 (l:List Bool):(blank l).length=l.length:=by
  induction l with
  | nil=>rfl
  | cons _ r ih=>simp [blank,ih]
lemma q140 (k:ℕ) (l:List Bool):val (l.take k)=val l % 2 ^ k:=by
  induction k generalizing l with
  | zero=>simp [val,Nat.mod_one]
  | succ k ih =>
    cases l with
    | nil=>simp [val]
    | cons b r =>
      simp only [List.take_succ_cons,val,ih,pow_succ']
      have hlt:b.toNat < 2:=by cases b <;> decide
      have hdiv:(b.toNat+2 * val r) % (2 * 2 ^ k)=b.toNat+2 * (val r % 2 ^ k):=by
        have h1:=Nat.div_add_mod (val r) (2 ^ k)
        have h2:val r % 2 ^ k < 2 ^ k:=Nat.mod_lt _ (by positivity)
        have h3:b.toNat+2 * val r=(2 * 2 ^ k) * (val r / 2 ^ k)+(b.toNat+2 * (val r % 2 ^ k)):=by
          linarith
        rw [h3,Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      exact hdiv.symm
lemma q194 (n:ℕ):val n.bits=n:=by
  induction n using Nat.binaryRec with
  | zero=>simp [val]
  | bit b m ih =>
    by_cases h:b=false∧m=0
    · rcases h with ⟨rfl,rfl⟩;simp [val]
    · rw [Nat.bits_append_bit m b (fun hm=>by subst hm;cases b <;> simp_all)]
      simp only [val,ih,Nat.bit]
      cases b <;> simp <;> omega
lemma q175 (k:ℕ) (hk:0 < k):k.bits.length=k.log2+1:=by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases h2:k < 2
    · have hk1:k=1:=by omega
      subst hk1;decide
    · have hdiv_pos:0 < k / 2:=by omega
      have hdiv_lt:k / 2 < k:=Nat.div_lt_self hk (by omega)
      have hlog:k.log2=(k / 2).log2+1:=by
        rw [Nat.log2_def];simp [show 2 ≤ k by omega]
      have hbits:k.bits=(decide (k % 2=1)) :: (k / 2).bits:=by
        have hdecomp:k=Nat.bit (decide (k % 2=1)) (k / 2):=by
          cases hmod:k % 2 with
          | zero=>simp [Nat.bit];omega
          | succ r =>
            have hr:r=0:=by omega
            subst hr;simp [Nat.bit];omega
        conv_lhs=>rw [hdecomp]
        rw [Nat.bits_append_bit (k / 2) (decide (k % 2=1)) (fun h0=>by omega)]
      rw [hbits,List.length_cons,ih (k / 2) hdiv_lt hdiv_pos,hlog]
lemma q78 (z h:ℕ):z.testBit h=z.bits.getD h false:=by
  induction h generalizing z with
  | zero =>
    by_cases hz:z=0
    · subst hz;simp
    · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1)) :: (z / 2).bits:=by
        conv_lhs=>rw [hdecomp]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0 => ?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits]
      simp [Nat.testBit_zero]
  | succ h ih =>
    by_cases hz:z=0
    · subst hz;simp
    · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
        cases hmod:z % 2 with
        | zero=>simp [Nat.bit];omega
        | succ r =>
          have hr:r=0:=by omega
          subst hr;simp [Nat.bit];omega
      have hbits:z.bits=(decide (z % 2=1)) :: (z / 2).bits:=by
        conv_lhs=>rw [hdecomp]
        refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0 => ?_
        have hmod1:z % 2=1:=by omega
        simp [hmod1]
      rw [hbits,List.getD_cons_succ,← ih (z / 2),Nat.testBit_succ]
def q28:List Bool → List Bool
  | []=>[true]
  | false :: l=>true :: l
  | true :: l=>false :: q28 l
lemma q182 (l:List Bool):val (q28 l)=val l+1:=by
  induction l with
  | nil=>simp [q28,val]
  | cons b l ih=>cases b <;> simp [q28,val,ih] <;> omega
lemma q183 (l:List Bool):(q28 l).length ≤ l.length+1:=by
  induction l with
  | nil=>simp [q28]
  | cons b l ih=>cases b <;> simp [q28] <;> omega
lemma q163 (n:ℕ):q28 n.bits=(n+1).bits:=by
  induction n using Nat.binaryRec with
  | zero=>decide
  | bit b m ih =>
    cases b with
    | false =>
      by_cases hm:m=0
      · subst hm;decide
      · have h1:(Nat.bit false m).bits=false :: m.bits :=
          Nat.bits_append_bit m false (fun h=>(hm h).elim)
        have h2:Nat.bit false m+1=Nat.bit true m:=by simp [Nat.bit]
        have h3:(Nat.bit true m).bits=true :: m.bits :=
          Nat.bits_append_bit m true (fun _=>by simp)
        rw [h1,h2,h3,q28]
    | true =>
      have h1:(Nat.bit true m).bits=true :: m.bits :=
        Nat.bits_append_bit m true (fun _=>by simp)
      have h2:Nat.bit true m+1=Nat.bit false (m+1):=by simp [Nat.bit];omega
      have h3:(Nat.bit false (m+1)).bits=false :: (m+1).bits :=
        Nat.bits_append_bit (m+1) false (fun h=>by omega)
      rw [h1,h2,h3,q28,ih]
lemma q139:CPTs q28:=by
  let δ : Bool → Bool → Bool × Option Bool:=fun c b =>
    match c,b with
    | false,b=>(false,some b)
    | true,false=>(false,some true)
    | true,true=>(true,some false)
  let fin:Bool → Option Bool:=fun c=>if c then some true else none
  refine fst_polyTime _ _ _ δ fin true fun s => ?_
  have hfalse:∀ l,fstRun δ fin false l=l:=by
    intro l;induction l with | nil=>rfl | cons b r ih=>simp [fstRun,δ,fin,ih]
  have htrue:∀ l,fstRun δ fin true l=q28 l:=by
    intro l
    induction l with
    | nil=>rfl
    | cons b r ih=>cases b <;> simp [fstRun,δ,fin,q28,hfalse,ih]
  exact (htrue s).symm
def q48 (u:List Bool):List Bool:=q28^[u.length] []
lemma q71 (u:List Bool):q48 u=u.length.bits:=by
  dsimp only [q48]
  have h:∀ k,q28^[k] []=k.bits:=by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,q163]
  exact h u.length
lemma q41:CPTs q48 :=
  q121 1 q139 q183 cpt_id (cpt_const [])
def q165 (kU zU:List Bool):List Bool :=
  takeN (q48 kU) (q48 zU++blank (q48 kU))
lemma q61 {uk uz:List Bool → List Bool} (hk:CPTs uk) (hz:CPTs uz) :
    CPTs (fun s=>q165 (uk s) (uz s)) :=
  q24 (cpt_comp hk q41)
    (cpt_app2 (cpt_comp hz q41) (cpt_comp (cpt_comp hk q41) cpt_blank))
lemma q86 (k z:ℕ) (hk:0 < k) :
    q165 (un k) (un z)=(List.range (k.log2+1)).map (fun h=>z.testBit h):=by
  dsimp only [q165]
  rw [q12,q71,q71,un_length,un_length]
  have hlen:k.bits.length=k.log2+1:=q175 k hk
  apply List.ext_getElem
  · rw [List.length_take,List.length_append,q33,hlen,List.length_map,List.length_range]
    omega
  · intro h hh1 hh2
    rw [List.length_map,List.length_range] at hh2
    rw [List.getElem_take,List.getElem_map,List.getElem_range,q78]
    by_cases hlt:h < z.bits.length
    · rw [List.getElem_append_left hlt,List.getD_eq_getElem _ _ hlt]
    · rw [List.getElem_append_right (by omega)]
      have hbl:∀ (l:List Bool) (i:ℕ) (hi:i < (blank l).length),(blank l)[i]=false:=by
        intro l
        induction l with
        | nil=>intro i hi;simp [blank] at hi
        | cons _ r ih =>
          intro i hi
          cases i with
          | zero=>rfl
          | succ i=>exact ih i (by simpa [blank] using hi)
      rw [hbl,List.getD_eq_default _ _ (by omega)]
end PEqualNP.Outside.L_meta_33617
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

def env (s : List Bool) := (unpairB s).1

def idx (s : List Bool) := (unpairB s).2.length

lemma env_pack (s : List Bool) (i : Nat) : env (pairB s (un i)) = s := by
  simp [env, unpairB_pairB]

lemma idx_pack (s : List Bool) (i : Nat) : idx (pairB s (un i)) = i := by
  simp [idx, unpairB_pairB]

abbrev NCPT (u : List Bool → Nat) := CPTs (fun s => un (u s))

def Test (p : List Bool → Prop) : Prop :=
  ∃ g : List Bool → List Bool, CPTs g ∧ ∀ s, g s ≠ [] ↔ p s

lemma str_id : CPTs (fun s : List Bool => s) := cpt_id

lemma str_env : CPTs env := cpt_unpairB1

lemma str_comp {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => v (u s)) := cpt_comp hu hv

lemma test_comp {u : List Bool → List Bool} {p : List Bool → Prop}
    (hu : CPTs u) (hp : Test p) : Test (fun s => p (u s)) := by
  obtain ⟨f, hf, h⟩ := hp
  exact ⟨fun s => f (u s), cpt_comp hu hf, fun s => h (u s)⟩

lemma nat_len {u : List Bool → List Bool} (hu : CPTs u) : NCPT (fun s => (u s).length) := by
  change CPTs (fun s => q47 (u s))
  exact cpt_comp hu q89

lemma nat_idx : NCPT idx := nat_len cpt_unpairB2

lemma nat_const (n : Nat) : NCPT (fun _ => n) := cpt_const _

lemma nat_add {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) :
    NCPT (fun s => u s + v s) :=
  q39 (cpt_app2 hu hv) (fun s => (List.replicate_add (u s) (v s) true).symm)

lemma nat_mul {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) :
    NCPT (fun s => u s * v s) :=
  q39 (q42 hu hv) (fun s => by simp [mulU])

lemma nat_sub {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) :
    NCPT (fun s => u s - v s) :=
  q39 (cpt_dropN' hv hu) (fun s => by simp [q40, un])

lemma str_take {u : List Bool → Nat} {v : List Bool → List Bool} (hu : NCPT u) (hv : CPTs v) :
    CPTs (fun s => (v s).take (u s)) := q39 (q24 hu hv) (by simp [q12])

lemma str_drop {u : List Bool → Nat} {v : List Bool → List Bool} (hu : NCPT u) (hv : CPTs v) :
    CPTs (fun s => (v s).drop (u s)) := q39 (cpt_dropN' hu hv) (by simp [q40])

lemma test_nonempty {u : List Bool → List Bool} (hu : CPTs u) : Test (fun s => u s ≠ []) :=
  ⟨u, hu, fun _ => Iff.rfl⟩

lemma test_not {p : List Bool → Prop} (hp : Test p) : Test (fun s => ¬p s) := by
  obtain ⟨f, hf, h⟩ := hp
  refine ⟨fun s => q133 (f s), cpt_comp hf q138, fun s => ?_⟩
  by_cases he : f s = [] <;> simp [q133, sel, he, ← h s]

lemma str_if {p : List Bool → Prop} [DecidablePred p] {u v : List Bool → List Bool}
    (hp : Test p) (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => if p s then u s else v s) := by
  obtain ⟨g, hg, hh⟩ := hp
  refine q39 (cpt_sel hg hv hu) (fun s => ?_)
  by_cases h : g s = []
  · have h' : ¬p s := fun k => ((hh s).mpr k) h
    simp [sel, h, h']
  · simp [sel, h, (hh s).mp h]

lemma test_and {p q : List Bool → Prop} (hp : Test p) (hq : Test q) :
    Test (fun s => p s ∧ q s) := by
  classical
  obtain ⟨f, hf, hh⟩ := hq
  refine ⟨fun s => if p s then f s else [], str_if hp hf (cpt_const []), fun s => ?_⟩
  by_cases h : p s <;> simp [h, hh]

lemma test_or {p q : List Bool → Prop} (hp : Test p) (hq : Test q) :
    Test (fun s => p s ∨ q s) := by
  obtain ⟨f, hf, h⟩ := hp
  obtain ⟨g, hg, h'⟩ := hq
  refine ⟨fun s => f s ++ g s, cpt_app2 hf hg, fun s => ?_⟩
  change f s ++ g s ≠ [] ↔ p s ∨ q s
  rw [Ne, List.append_eq_nil_iff, not_and_or, ← Ne, ← Ne, h, h']

lemma test_lt {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) : Test (fun s => u s < v s) := by
  refine ⟨fun s => un (v s - u s), nat_sub hv hu, fun s => ?_⟩
  rw [← List.length_pos_iff]
  simpa using Nat.sub_pos_iff_lt

lemma test_le {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) : Test (fun s => u s ≤ v s) := by
  simpa only [not_lt] using test_not (test_lt hv hu)

lemma test_eq {u v : List Bool → Nat} (hu : NCPT u) (hv : NCPT v) : Test (fun s => u s = v s) := by
  simpa only [le_antisymm_iff] using test_and (test_le hu hv) (test_le hv hu)

lemma test_bit {u : List Bool → Nat} {v : List Bool → List Bool} (hu : NCPT u) (hv : CPTs v) :
    Test (fun s => (v s)[u s]?.getD false = true) := by
  refine ⟨fun s => q17 ((v s).drop (u s)), cpt_comp (str_drop hu hv) q35, fun s => ?_⟩
  change q17 ((v s).drop (u s)) ≠ [] ↔ (v s)[u s]?.getD false = true
  rw [← List.head?_drop]
  cases (v s).drop (u s) with
  | nil => simp [q17]
  | cons b l => cases b <;> simp [q17]

lemma str_bit {p : List Bool → Prop} [DecidablePred p] (hp : Test p) :
    CPTs (fun s => [decide (p s)]) :=
  q39 (str_if hp (cpt_const [true]) (cpt_const [false])) (fun s => by split <;> simp_all)

def tabStep (cell : List Bool → List Bool) (y : List Bool) : List Bool :=
  let b := (unpairB y).1
  let e := (unpairB (unpairB y).2).1
  let t := unpairB (unpairB (unpairB y).2).2
  pairB b (pairB e (pairB (true :: t.1) (t.2 ++ (cell (pairB e t.1)).take b.length)))

lemma cpt_tabStep {cell : List Bool → List Bool} (hc : CPTs cell) : CPTs (tabStep cell) := by
  have hb := cpt_unpairB1
  have he := cpt_comp cpt_unpairB2 cpt_unpairB1
  have ht := cpt_comp cpt_unpairB2 cpt_unpairB2
  have hi := cpt_comp ht cpt_unpairB1
  have ha := cpt_comp ht cpt_unpairB2
  exact cpt_pairB2 hb (cpt_pairB2 he (cpt_pairB2 (cpt_app2 (cpt_const [true]) hi)
    (cpt_app2 ha (str_take (nat_len hb) (cpt_comp (cpt_pairB2 he hi) hc)))))

lemma tabStep_length (cell : List Bool → List Bool) (y : List Bool) :
    (tabStep cell y).length ≤ y.length + 5 * (unpairB y).1.length + 5 := by
  have h1 := q0 y
  have h2 := q0 (unpairB y).2
  have h3 := q0 (unpairB (unpairB y).2).2
  simp only [tabStep, pairB_length, List.length_cons, List.length_append, List.length_take]
  omega

def tab (count bound : Nat) (s : List Bool) (cell : List Bool → List Bool) : List Bool :=
  (List.range count).flatMap (fun i => (cell (pairB s (un i))).take bound)

lemma tab_run (cell : List Bool → List Bool) (b e : List Bool) (r : Nat) :
    (tabStep cell)^[r] (pairB b (pairB e (pairB [] []))) =
      pairB b (pairB e (pairB (un r) (tab r b.length e cell))) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [tabStep, unpairB_pairB, tab, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]
    rfl

lemma cpt_tab {u b : List Bool → Nat} {e cell : List Bool → List Bool}
    (hu : NCPT u) (hb : NCPT b) (he : CPTs e) (hc : CPTs cell) :
    CPTs (fun s => tab (u s) (b s) (e s) cell) := by
  have hi := q18 5 (cpt_tabStep hc) (fun y => by simp [tabStep, unpairB_pairB])
    (tabStep_length cell) hu (cpt_pairB2 hb (cpt_pairB2 he (cpt_const (pairB [] []))))
  refine q39 (cpt_comp hi (cpt_comp cpt_unpairB2 (cpt_comp cpt_unpairB2 cpt_unpairB2))) ?_
  intro s
  simp only [un_length, tab_run, unpairB_pairB]

lemma tab_eq (count bound : Nat) (s : List Bool) (cell : List Bool → List Bool)
    (h : ∀ i < count, (cell (pairB s (un i))).length ≤ bound) :
    tab count bound s cell = (List.range count).flatMap (fun i => cell (pairB s (un i))) := by
  unfold tab
  apply List.flatMap_congr
  exact fun i hi => List.take_of_length_le (h i (List.mem_range.mp hi))

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

def hdr (n : Nat) : List Bool := un n ++ [false]

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))

def paint (n : Nat) (G R : Fin n → Fin n → Bool) : List Bool :=
  hdr n ++ (pairs n).flatMap (fun e => [G e.1 e.2, R e.1 e.2])

abbrev Row (n : Nat) := Finset (Fin n) × Finset (Fin n)
abbrev Soft (n : Nat) := Row n × Bool

def bank {n : Nat} (s : Finset (Fin n)) : List Bool :=
  (List.finRange n).map (fun i => decide (i ∈ s))

def hardRow {n : Nat} (z : Row n) : List Bool := bank z.1 ++ bank z.2

def softRow {n : Nat} (z : Soft n) : List Bool := hardRow z.1 ++ [z.2]

def query (n : Nat) (hard : List (Row n)) (soft : List (Soft n)) : List Bool :=
  hdr n ++ hdr hard.length ++ hard.flatMap hardRow ++ hdr soft.length ++ soft.flatMap softRow

def inputN (s : List Bool) := (hd s).length

def inputH (s : List Bool) := inputN (dropN s)

def hardData (s : List Bool) := dropN (dropN s)

def softHeader (s : List Bool) := (hardData s).drop (2 * inputN s * inputH s)

def inputM (s : List Bool) := inputN (softHeader s)

def softData (s : List Bool) := dropN (softHeader s)

def permSuffix (s : List Bool) := (softData s).drop ((2 * inputN s + 1) * inputM s)

lemma nat_inputN : NCPT inputN := nat_len cpt_hd

lemma nat_inputH : NCPT inputH :=
  str_comp (u := dropN) (v := fun s => un (inputN s)) cpt_dropN nat_inputN

lemma cpt_hardData : CPTs hardData :=
  str_comp (u := dropN) (v := dropN) cpt_dropN cpt_dropN

lemma cpt_softHeader : CPTs softHeader :=
  str_drop (nat_mul (nat_mul (nat_const 2) nat_inputN) nat_inputH) cpt_hardData

lemma nat_inputM : NCPT inputM :=
  str_comp (u := softHeader) (v := fun s => un (inputN s)) cpt_softHeader nat_inputN

lemma cpt_softData : CPTs softData :=
  str_comp (u := softHeader) (v := dropN) cpt_softHeader cpt_dropN

lemma cpt_permSuffix : CPTs permSuffix :=
  str_drop (nat_mul (nat_add (nat_mul (nat_const 2) nat_inputN) (nat_const 1)) nat_inputM) cpt_softData

lemma hdr_inputN (n : Nat) (s : List Bool) : inputN (hdr n ++ s) = n := by
  simp [inputN, hd, hdr, un, List.append_assoc]

lemma hdr_dropN (n : Nat) (s : List Bool) : dropN (hdr n ++ s) = s := by
  simp [dropN, hdr, un, List.append_assoc]

lemma hardRow_len {n : Nat} (z : Row n) : (hardRow z).length = 2*n := by
  simp [hardRow, bank]; omega

lemma softRow_len {n : Nat} (z : Soft n) : (softRow z).length = 2*n+1 := by
  simp [softRow, hardRow_len]

lemma flatMap_len_of {α β : Type} (l : List α) (f : α → List β) (w : Nat)
    (h : ∀ a, (f a).length = w) : (l.flatMap f).length = w * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [h, ih, Nat.mul_succ, Nat.add_comm]

lemma inputN_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    inputN (query n hard soft ++ s) = n := by
  simpa only [query, List.append_assoc] using
    hdr_inputN n (hdr hard.length ++ (hard.flatMap hardRow ++ (hdr soft.length ++ (soft.flatMap softRow ++ s))))

lemma inputH_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    inputH (query n hard soft ++ s) = hard.length := by
  simp only [inputH, query, List.append_assoc, hdr_dropN, hdr_inputN]

lemma hardData_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    hardData (query n hard soft ++ s) = hard.flatMap hardRow ++ (hdr soft.length ++ (soft.flatMap softRow ++ s)) := by
  simp only [hardData, query, List.append_assoc, hdr_dropN]

lemma softHeader_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    softHeader (query n hard soft ++ s) = hdr soft.length ++ (soft.flatMap softRow ++ s) := by
  simp only [softHeader, inputN_query, inputH_query, hardData_query]
  exact List.drop_left' (flatMap_len_of hard hardRow (2*n) hardRow_len)

lemma inputM_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    inputM (query n hard soft ++ s) = soft.length := by
  simp only [inputM, softHeader_query, hdr_inputN]

lemma softData_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    softData (query n hard soft ++ s) = soft.flatMap softRow ++ s := by
  simp only [softData, softHeader_query, hdr_dropN]

lemma permSuffix_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (s : List Bool) :
    permSuffix (query n hard soft ++ s) = s := by
  simp only [permSuffix, softData_query, inputN_query, inputM_query]
  exact List.drop_left' (flatMap_len_of soft softRow (2*n+1) softRow_len)

lemma chunk_drop_take {α β : Type} (l : List α) (enc : α → List β) (w : Nat)
    (hlen : ∀ a, (enc a).length = w) (rest : List β) (i : Nat) (hi : i < l.length) :
    (((l.flatMap enc) ++ rest).drop (w*i)).take w = enc l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simpa only [List.flatMap_cons, List.append_assoc, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
        using (List.take_left' (l₂ := l.flatMap enc ++ rest) (hlen a))
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      rw [List.getElem_cons_succ, List.flatMap_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm,
        ← List.drop_drop, List.drop_left' (hlen a)]
      exact ih i hi'

lemma chunk_get {α β : Type} (l : List α) (enc : α → List β) (w : Nat)
    (hlen : ∀ a, (enc a).length = w) (rest : List β) (i : Nat) (hi : i < l.length)
    (j : Nat) (hj : j < w) :
    (l.flatMap enc ++ rest)[w*i+j]? = (enc l[i])[j]? := by
  rw [← List.getElem?_drop, ← List.getElem?_take_of_lt hj, chunk_drop_take l enc w hlen rest i hi]

lemma range_vals (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · simp

lemma bank_get {n : Nat} (t : Finset (Fin n)) (i : Fin n) :
    (bank t)[i.val]? = some (decide (i ∈ t)) := by
  have h : i.val < (bank t).length := by simpa [bank] using i.isLt
  rw [List.getElem?_eq_getElem h]
  simp [bank]

lemma mem_pairs {n : Nat} {e : Fin n × Fin n} : e ∈ pairs n ↔ e.1 < e.2 := by
  obtain ⟨i,j⟩ := e
  simp [pairs]

lemma flatMap_map_filter {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : α → List β) : (l.filter (fun a => decide (p a))).flatMap f =
      l.flatMap (fun a => if p a then f a else []) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

lemma pairs_flatMap_nat {α : Type} (n : Nat) (f : Nat → Nat → List α) :
    (pairs n).flatMap (fun e => f e.1.val e.2.val) =
      (List.range n).flatMap (fun i => (List.range n).flatMap (fun j => if i<j then f i j else [])) := by
  unfold pairs
  simp only [List.flatMap_assoc, List.flatMap_map, flatMap_map_filter]
  simp only [← range_vals n, List.flatMap_map, Fin.lt_iff_val_lt_val]

end PEqualNP.Outside.L_meta_33617.Machine


namespace PEqualNP.Outside.L_meta_33617.SoftScore

open scoped BigOperators

namespace Signed

open scoped Classical

variable {α ι : Type*}

noncomputable def count (xs : List α) (P : α → Prop) : Nat := by
  classical
  exact (xs.filter fun x => decide (P x)).length

private theorem count_cons (x : α) (xs : List α) (P : α → Prop) :
    count (x :: xs) P = count xs P + if P x then 1 else 0 := by
  classical
  by_cases h : P x <;> simp [count, h]

theorem count_eq_filter (xs : List α) (P : α → Prop) (p : α → Bool)
    (h : ∀ x, P x ↔ p x = true) : count xs P = (xs.filter p).length := by
  classical
  unfold count
  have hp : (fun x => decide (P x)) = p := by
    funext x
    by_cases hP : P x
    · rw [decide_eq_true hP, (h x).mp hP]
    · have hp : p x = false := by
        cases hx : p x
        · rfl
        · exact (hP ((h x).mpr hx)).elim
      rw [decide_eq_false hP, hp]
  rw [hp]

noncomputable def mass (xs : List α) (label : α → Bool) (P : α → Prop) : ℤ :=
  (count xs (fun x => label x = true ∧ P x) : ℤ) -
    count xs (fun x => label x = false ∧ P x)

private theorem mass_congr (xs : List α) (label : α → Bool) {P Q : α → Prop}
    (h : ∀ x, P x ↔ Q x) : mass xs label P = mass xs label Q := by
  have : P = Q := funext fun x => propext (h x)
  rw [this]

private theorem mass_false (xs : List α) (label : α → Bool) :
    mass xs label (fun _ => False) = 0 := by
  classical
  simp [mass, count]

private theorem mass_union (xs : List α) (label : α → Bool) (P Q : α → Prop) :
    mass xs label (fun x => P x ∨ Q x) =
      mass xs label P + mass xs label Q - mass xs label (fun x => P x ∧ Q x) := by
  classical
  induction xs with
  | nil => simp [mass, count]
  | cons x xs ih =>
    unfold mass at ih ⊢
    simp only [count_cons, Nat.cast_add]
    cases hl : label x <;> by_cases hp : P x <;> by_cases hq : Q x <;>
      simp [*] <;> linarith

private def allHits (H : ι → α → Prop) (S : Finset ι) (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∀ e ∈ S, H e x

private def anyHit (H : ι → α → Prop) (S : Finset ι) (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∃ e ∈ S, H e x

private theorem anyHit_empty (H : ι → α → Prop) (P : α → Prop) :
    anyHit H ∅ P = fun _ => False := by
  funext x
  simp [anyHit]

private theorem cross (H : ι → α → Prop) (S : Finset ι) (P : α → Prop) (e : ι) :
    (fun x => (P x ∧ H e x) ∧ anyHit H S P x) = anyHit H S (fun x => P x ∧ H e x) := by
  funext x
  apply propext
  simp only [anyHit]
  tauto

private theorem insert_subset_insert {U S : Finset ι} (hU : U ⊆ S) (e : ι) :
    insert e U ⊆ insert e S := by
  intro f hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hU hf)

variable (xs : List α) (label : α → Bool) (H : ι → α → Prop)

-- The overlap term in the signed union recurrence is itself a union on a
-- restricted domain. Induction cancels it without enumerating the powerset.
private theorem mass_any_of_all_zero (S : Finset ι) (P : α → Prop)
    (hz : ∀ U ⊆ S, U.Nonempty → mass xs label (allHits H U P) = 0) :
    mass xs label (anyHit H S P) = 0 := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty => simpa only [anyHit_empty] using mass_false xs label
  | @insert e S he ih =>
    have hs : S ⊆ insert e S := Finset.subset_insert _ _
    have h₁ : mass xs label (fun x => P x ∧ H e x) = 0 := by
      have h := hz {e} (by simp) (by simp)
      exact (mass_congr xs label (P := fun x => P x ∧ H e x) (Q := allHits H {e} P)
        (by intro x; simp [allHits])).trans h
    have h₂ : mass xs label (anyHit H S P) = 0 :=
      ih P fun U hU hne => hz U (hU.trans hs) hne
    have h₃ : mass xs label (anyHit H S fun x => P x ∧ H e x) = 0 := by
      apply ih
      intro U hU hne
      rw [mass_congr xs label (Q := allHits H (insert e U) P)
        (by intro x; simp [allHits, and_assoc])]
      exact hz (insert e U) (insert_subset_insert hU e) (by simp)
    calc
      _ = mass xs label (fun x => (P x ∧ H e x) ∨ anyHit H S P x) := by
        apply mass_congr
        intro x
        simp [anyHit, Finset.mem_insert]
        aesop
      _ = _ := by
        rw [mass_union, h₁, h₂, cross, h₃]
        simp

/-- All joint masses of order at least two vanish, so the union has only singleton mass. -/
theorem mass_any (S : Finset ι) (P : α → Prop)
    (hz : ∀ U ⊆ S, 2 ≤ U.card → mass xs label (fun x => P x ∧ ∀ e ∈ U, H e x) = 0) :
    mass xs label (fun x => P x ∧ ∃ e ∈ S, H e x) =
      ∑ e ∈ S, mass xs label (fun x => P x ∧ H e x) := by
  classical
  change mass xs label (anyHit H S P) = _
  induction S using Finset.induction_on with
  | empty => simpa only [anyHit_empty, Finset.sum_empty] using mass_false xs label
  | @insert e S he ih =>
    have hs : S ⊆ insert e S := Finset.subset_insert _ _
    have h₂ := ih fun U hU hc => hz U (hU.trans hs) hc
    have h₃ : mass xs label (anyHit H S fun x => P x ∧ H e x) = 0 := by
      apply mass_any_of_all_zero
      intro U hU hne
      rw [mass_congr xs label (Q := allHits H (insert e U) P)
        (by intro x; simp [allHits, and_assoc])]
      apply hz (insert e U) (insert_subset_insert hU e)
      have heU : e ∉ U := fun h => he (hU h)
      have hc := Finset.card_pos.mpr hne
      rw [Finset.card_insert_of_notMem heU]
      omega
    calc
      _ = mass xs label (fun x => (P x ∧ H e x) ∨ anyHit H S P x) := by
        apply mass_congr
        intro x
        simp [anyHit, Finset.mem_insert]
        aesop
      _ = _ := by
        rw [mass_union, h₂, cross, h₃]
        simp [Finset.sum_insert he]

/-- Agreement with `¬D ∨ hit` differs from agreement with `¬D` by signed hit mass on `D`. -/
theorem score_eq (xs : List α) (label : α → Bool) (D hit : α → Prop) :
    (count xs (fun x => ((¬ D x ∨ hit x) ↔ label x = true)) : ℤ) =
      count xs (fun x => (D x ∧ label x = false) ∨ (¬ D x ∧ label x = true)) +
        mass xs label (fun x => D x ∧ hit x) := by
  classical
  induction xs with
  | nil => simp [count, mass]
  | cons x xs ih =>
    unfold mass at ih ⊢
    simp only [count_cons, Nat.cast_add]
    cases hl : label x <;> by_cases hd : D x <;> by_cases hh : hit x <;>
      simp [*] <;> linarith

end Signed

abbrev Edge (n : Nat) := Fin n × Fin n
abbrev Test (n : Nat) := (Finset (Fin n) × Finset (Fin n)) × Bool

variable {n : Nat}

def ends (e : Edge n) : Finset (Fin n) := {e.1, e.2}

def hits (e : Edge n) (t : Test n) : Prop := ends e ⊆ t.1.1 ∨ ends e ⊆ t.1.2

def lists (S : Finset (Edge n)) (t : Test n) : Prop :=
  Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ S, hits e t

instance (e : Edge n) (t : Test n) : Decidable (hits e t) := by
  unfold hits
  infer_instance

instance (S : Finset (Edge n)) (t : Test n) : Decidable (lists S t) := by
  unfold lists
  infer_instance

def pos (soft : List (Test n)) (e : Edge n) : Nat :=
  (soft.filter fun t => t.2 && decide (lists {e} t)).length

def neg (soft : List (Test n)) (e : Edge n) : Nat :=
  (soft.filter fun t => !t.2 && decide (lists {e} t)).length

/-- Baseline: correct negatives on disjoint banks and correct positives on overlapping banks. -/
def base (soft : List (Test n)) : Nat :=
  (soft.filter fun t => decide ((Disjoint t.1.1 t.1.2 ∧ t.2 = false) ∨
    (¬ Disjoint t.1.1 t.1.2 ∧ t.2 = true))).length

/-- Restrict the posted balance hypothesis on matchings in `E` to subsets of `S`. -/
theorem balance_on_subsets (soft : List (Test n)) {E S : Finset (Edge n)}
    (hSE : S ⊆ E)
    (hS : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f))
    (balance : ∀ U ⊆ E, 2 ≤ U.card →
      (∀ e ∈ U, ∀ f ∈ U, e ≠ f → Disjoint (ends e) (ends f)) →
      (soft.filter fun t => t.2 && decide (lists U t)).length =
        (soft.filter fun t => !t.2 && decide (lists U t)).length) :
    ∀ U ⊆ S, 2 ≤ U.card →
      (soft.filter fun t => t.2 && decide (lists U t)).length =
        (soft.filter fun t => !t.2 && decide (lists U t)).length := by
  intro U hUS hc
  exact balance U (hUS.trans hSE) hc fun e he f hf hne => hS e (hUS he) f (hUS hf) hne

private theorem mass_lists (soft : List (Test n)) (S : Finset (Edge n)) :
    Signed.mass soft Prod.snd (lists S) =
      ((soft.filter fun t => t.2 && decide (lists S t)).length : ℤ) -
        (soft.filter fun t => !t.2 && decide (lists S t)).length := by
  unfold Signed.mass
  rw [Signed.count_eq_filter _ _ (fun t => t.2 && decide (lists S t)),
      Signed.count_eq_filter _ _ (fun t => !t.2 && decide (lists S t))] <;>
    intro t <;> simp

/-- For the posted score (agreement with the label), a hit raises the score on a true label. -/
theorem score_int (soft : List (Test n)) (S : Finset (Edge n))
    (balance : ∀ U ⊆ S, 2 ≤ U.card →
      (soft.filter fun t => t.2 && decide (lists U t)).length =
        (soft.filter fun t => !t.2 && decide (lists U t)).length)
    (predict : Finset (Fin n) → Finset (Fin n) → Bool)
    (hp : ∀ t : Test n, predict t.1.1 t.1.2 = true ↔
      ¬ Disjoint t.1.1 t.1.2 ∨ ∃ e ∈ S, hits e t) :
    ((soft.filter fun t => decide (predict t.1.1 t.1.2 = t.2)).length : ℤ) =
      (base soft : ℤ) + ∑ e ∈ S, ((pos soft e : ℤ) - neg soft e) := by
  classical
  have hscore := Signed.score_eq soft Prod.snd (fun t => Disjoint t.1.1 t.1.2)
    (fun t => ∃ e ∈ S, hits e t)
  rw [Signed.count_eq_filter _ _ (fun t => decide (predict t.1.1 t.1.2 = t.2)),
      Signed.count_eq_filter _ _ (fun t => decide ((Disjoint t.1.1 t.1.2 ∧ t.2 = false) ∨
        (¬ Disjoint t.1.1 t.1.2 ∧ t.2 = true)))] at hscore
  · rw [hscore, Signed.mass_any soft Prod.snd hits S (fun t => Disjoint t.1.1 t.1.2)]
    · congr 1
      apply Finset.sum_congr rfl
      intro e _
      have he : (fun t => Disjoint t.1.1 t.1.2 ∧ hits e t) = lists {e} := by
        funext t
        simp [lists]
      rw [he]
      exact mass_lists soft {e}
    · intro U hU hc
      change Signed.mass soft Prod.snd (lists U) = 0
      rw [mass_lists, balance U hU hc, sub_self]
  · intro t
    simp
  · intro t
    simp only [decide_eq_true_eq, ← hp t]
    cases h₁ : predict t.1.1 t.1.2 <;> cases h₂ : t.2 <;> simp [*]

/-- Natural weighted-score identity, with subtraction in each weight justified by `neg ≤ m`. -/
theorem score_nat (soft : List (Test n)) (S : Finset (Edge n))
    (balance : ∀ U ⊆ S, 2 ≤ U.card →
      (soft.filter fun t => t.2 && decide (lists U t)).length =
        (soft.filter fun t => !t.2 && decide (lists U t)).length)
    (predict : Finset (Fin n) → Finset (Fin n) → Bool)
    (hp : ∀ t : Test n, predict t.1.1 t.1.2 = true ↔
      ¬ Disjoint t.1.1 t.1.2 ∨ ∃ e ∈ S, hits e t) :
    (soft.length + 1) * S.card +
        (soft.filter fun t => decide (predict t.1.1 t.1.2 = t.2)).length =
      base soft + ∑ e ∈ S, (soft.length + 1 + pos soft e - neg soft e) := by
  have hb (e : Edge n) : neg soft e ≤ soft.length + 1 + pos soft e := by
    have h : neg soft e ≤ soft.length := List.length_filter_le ..
    omega
  apply Int.ofNat_inj.mp
  push_cast [Int.ofNat_sub (hb _)]
  rw [score_int soft S balance predict hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

end PEqualNP.Outside.L_meta_33617.SoftScore
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

private def decDiff (x : List Bool) : List Bool :=
  if ((unpairB (env x)).1)[idx x]?.getD false = ((unpairB (env x)).2)[idx x]?.getD false
  then [] else [true]

private lemma cpt_decDiff : CPTs decDiff := by
  have ha := test_bit nat_idx (cpt_comp str_env cpt_unpairB1)
  have hb := test_bit nat_idx (cpt_comp str_env cpt_unpairB2)
  have he := test_or (test_and ha hb) (test_and (test_not ha) (test_not hb))
  refine q39 (str_if he (cpt_const []) (cpt_const [true])) (fun x => ?_)
  unfold decDiff
  cases ((unpairB (env x)).1)[idx x]?.getD false <;>
    cases ((unpairB (env x)).2)[idx x]?.getD false <;> simp

private lemma test_decStrEq {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    Test (fun s => u s = v s) := by
  let diff s := tab (u s).length 1 (pairB (u s) (v s)) decDiff
  have hd : CPTs diff := cpt_tab (nat_len hu) (nat_const 1) (cpt_pairB2 hu hv) cpt_decDiff
  have hnil (s : List Bool) : diff s = [] ↔
      ∀ i < (u s).length, (u s)[i]?.getD false = (v s)[i]?.getD false := by
    simp only [diff, tab, List.flatMap_eq_nil_iff, List.mem_range, decDiff,
      env_pack, idx_pack, unpairB_pairB]
    apply forall_congr'
    intro i
    constructor <;> intro h hi
    · specialize h hi
      by_contra hn
      simp [hn] at h
    · simp [h hi]
  obtain ⟨g, hg, h⟩ := test_and (test_eq (nat_len hu) (nat_len hv)) (test_not (test_nonempty hd))
  refine ⟨g, hg, fun s => (h s).trans ?_⟩
  change ((u s).length = (v s).length ∧ ¬¬ (diff s = [])) ↔ u s = v s
  rw [not_not, hnil]
  constructor
  · rintro ⟨hl, hp⟩
    apply List.ext_getElem hl
    intro i hi hj
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
      using hp i hi
  · intro hEq
    simp [hEq]

private lemma decTabOneLength (n : Nat) (s : List Bool) (cell : List Bool → List Bool) :
    (tab n 1 s cell).length ≤ n := by
  unfold tab
  have h (l : List Nat) :
      (l.flatMap (fun i => (cell (pairB s (un i))).take 1)).length ≤ l.length := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h := List.length_take_le 1 (cell (pairB s (un i)))
      omega
  simpa using h (List.range n)

abbrev decQ (m : Nat) : Nat := 2 * (2 * m + 1)

def decK (n m : Nat) : Nat := 4 * n + (n * n) * decQ m + 2 * m

def decFirst (n m i j : Nat) : Nat := 4 * n + (i * n + j) * decQ m

private lemma nat_decQ {m : List Bool → Nat} (hm : NCPT m) : NCPT (fun s => decQ (m s)) :=
  nat_mul (nat_const 2) (nat_add (nat_mul (nat_const 2) hm) (nat_const 1))

private lemma nat_decK {n m : List Bool → Nat} (hn : NCPT n) (hm : NCPT m) :
    NCPT (fun s => decK (n s) (m s)) :=
  nat_add (nat_add (nat_mul (nat_const 4) hn) (nat_mul (nat_mul hn hn) (nat_decQ hm)))
    (nat_mul (nat_const 2) hm)

private lemma nat_decFirst {n m i j : List Bool → Nat}
    (hn : NCPT n) (hm : NCPT m) (hi : NCPT i) (hj : NCPT j) :
    NCPT (fun s => decFirst (n s) (m s) (i s) (j s)) :=
  nat_add (nat_mul (nat_const 4) hn) (nat_mul (nat_add (nat_mul hi hn) hj) (nat_decQ hm))

private def decInput (x : List Bool) : List Bool := env (env x)

private def decKAt (x : List Bool) : Nat := decK (inputN (decInput x)) (inputM (decInput x))

private def decWidth (x : List Bool) : Nat := (decKAt x).bits.length

private def decActual (x : List Bool) : List Bool :=
  let w := decWidth x
  ((permSuffix (decInput x)).drop (w * idx (env x))).take w

private def decExpected (x : List Bool) : List Bool :=
  q165 (un (decKAt x)) (un (decFirst (inputN (decInput x)) (inputM (decInput x))
    (idx (env x)) (idx x)))

private lemma cpt_decInput : CPTs decInput := str_comp (u := env) (v := env) str_env str_env

private lemma nat_decN : NCPT (fun x => inputN (decInput x)) :=
  str_comp (u := decInput) (v := fun s => un (inputN s)) cpt_decInput nat_inputN

private lemma nat_decM : NCPT (fun x => inputM (decInput x)) :=
  str_comp (u := decInput) (v := fun s => un (inputM s)) cpt_decInput nat_inputM

private lemma nat_decKAt : NCPT decKAt := nat_decK nat_decN nat_decM

private lemma nat_decWidth : NCPT decWidth := by
  have h : CPTs (fun s => (decKAt s).bits) :=
    q39 (str_comp nat_decKAt q41) (fun s => by simp [q71])
  exact nat_len h

private lemma nat_decI : NCPT (fun x => idx (env x)) :=
  str_comp (u := env) (v := fun s => un (idx s)) str_env nat_idx

private lemma cpt_decActual : CPTs decActual :=
  str_take nat_decWidth (str_drop (nat_mul nat_decWidth nat_decI)
    (str_comp (u := decInput) (v := permSuffix) cpt_decInput cpt_permSuffix))

private lemma cpt_decExpected : CPTs decExpected :=
  q61 nat_decKAt (nat_decFirst nat_decN nat_decM nat_decI nat_idx)

private def decCell (x : List Bool) : List Bool :=
  if idx (env x) < idx x then [decide (decActual x = decExpected x)] else []

private lemma cpt_decCell : CPTs decCell :=
  str_if (test_lt nat_decI nat_idx) (str_bit (test_decStrEq cpt_decActual cpt_decExpected))
    (cpt_const [])

private def decRow (x : List Bool) : List Bool := tab (inputN (env x)) 1 x decCell

private lemma cpt_decRow : CPTs decRow :=
  cpt_tab (str_comp (u := env) (v := fun s => un (inputN s)) str_env nat_inputN)
    (nat_const 1) str_id cpt_decCell

def decode (s : List Bool) : List Bool := tab (inputN s) (inputN s) s decRow

theorem cpt_decode : CPTs decode := cpt_tab nat_inputN nat_inputN str_id cpt_decRow

private lemma decode_rows (s : List Bool) {n m : Nat} (hn : inputN s = n) (hm : inputM s = m) :
    decode s = (pairs n).flatMap (fun e =>
      [decide (((permSuffix s).drop ((decK n m).bits.length * e.1.val)).take (decK n m).bits.length =
        q165 (un (decK n m)) (un (decFirst n m e.1.val e.2.val)))]) := by
  have hrow (i : Nat) (_ : i < n) : (decRow (pairB s (un i))).length ≤ n := by
    simpa only [decRow, env_pack, hn] using decTabOneLength n (pairB s (un i)) decCell
  have hcell (x : List Bool) : (decCell x).length ≤ 1 := by
    unfold decCell
    split <;> simp
  let f (i j : Nat) : List Bool :=
    [decide (((permSuffix s).drop ((decK n m).bits.length * i)).take (decK n m).bits.length =
      q165 (un (decK n m)) (un (decFirst n m i j)))]
  change decode s = (pairs n).flatMap (fun e => f e.1.val e.2.val)
  simp only [decode, hn]
  rw [tab_eq _ _ _ _ hrow, pairs_flatMap_nat n f]
  apply List.flatMap_congr
  intro i _
  rw [decRow, env_pack, hn, tab_eq _ _ _ _ (fun j _ => hcell _)]
  apply List.flatMap_congr
  intro j _
  simp only [f, decCell, decActual, decExpected, decWidth, decKAt, decInput, idx_pack, env_pack, hn, hm]

def decBits (k z : Nat) : List Bool := (List.range (k.log2 + 1)).map (fun h => z.testBit h)

def decFields {k : Nat} (P : Equiv.Perm (Fin k)) : List Bool :=
  (List.finRange k).flatMap (fun i => decBits k (P i).val)

private lemma decField_at {k : Nat} (hk : 0 < k) (P : Equiv.Perm (Fin k)) (i : Fin k) :
    ((decFields P).drop (k.bits.length * i.val)).take k.bits.length = decBits k (P i).val := by
  have hi : i.val < (List.finRange k).length := by simpa using i.isLt
  have hw (j : Fin k) : (decBits k (P j).val).length = k.bits.length := by
    simp [decBits, q175 k hk]
  have hidx : (List.finRange k)[i.val] = i := by
    apply Fin.ext
    simp
  simpa only [decFields, List.append_nil, hidx] using
    chunk_drop_take (List.finRange k) (fun j => decBits k (P j).val) k.bits.length hw [] i.val hi

private lemma decField_val {k z : Nat} (hz : z < k) : val (q165 (un k) (un z)) = z := by
  rw [q165, q12, q71, q71, un_length, un_length, q140, q58, q194, q37, mul_zero, add_zero]
  apply Nat.mod_eq_of_lt
  calc
    z < k := hz
    _ = val k.bits := (q194 k).symm
    _ < 2 ^ k.bits.length := q124 _

def decOrig {n : Nat} (m : Nat) (i : Fin n) : Fin (decK n m) :=
  ⟨i.val, by have := i.isLt; unfold decK; omega⟩

def decFirstVertex {n : Nat} (m : Nat) (e : Fin n × Fin n) : Fin (decK n m) :=
  ⟨decFirst n m e.1.val e.2.val, by
    have h : e.1.val * n + e.2.val < n * n := by
      calc
        e.1.val * n + e.2.val < e.1.val * n + n := Nat.add_lt_add_left e.2.isLt _
        _ = (e.1.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ n * n := Nat.mul_le_mul_right n e.1.isLt
    have hp : 0 < decQ m := by unfold decQ; omega
    have := Nat.mul_lt_mul_of_pos_right h hp
    unfold decFirst decK
    omega⟩

/-- Reading the permutation field of the first endpoint tests for its first path vertex. -/
theorem decode_spec (s : List Bool) {n m : Nat} (hn : inputN s = n) (hm : inputM s = m)
    (P : Equiv.Perm (Fin (decK n m))) (hs : permSuffix s = decFields P) :
    decode s = (pairs n).map (fun e => decide (P (decOrig m e.1) = decFirstVertex m e)) := by
  rw [decode_rows s hn hm, List.map_eq_flatMap]
  apply List.flatMap_congr
  intro e _
  have hk : 0 < decK n m := Nat.zero_lt_of_lt (decOrig m e.1).isLt
  change [decide (((permSuffix s).drop ((decK n m).bits.length * (decOrig m e.1).val)).take
      (decK n m).bits.length = q165 (un (decK n m)) (un (decFirstVertex m e).val))] = _
  rw [hs, decField_at hk P (decOrig m e.1), decBits, ← q86 _ (P (decOrig m e.1)).val hk]
  simp only [List.cons.injEq, eq_self, and_true, decide_eq_decide]
  constructor
  · intro h
    apply Fin.ext
    simpa only [decField_val (P (decOrig m e.1)).isLt, decField_val (decFirstVertex m e).isLt]
      using congrArg val h
  · intro h
    rw [h]

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

private def revN (s : List Bool) := inputN s + 2

private def revInput (y : List Bool) := env (env y)
private def revI (y : List Bool) := idx (env y)
private def revJ (y : List Bool) := idx y
private def revPack (s : List Bool) (i j : Nat) := pairB (pairB s (un i)) (un j)

private lemma nat_revComp {u : List Bool → List Bool} {v : List Bool → Nat}
    (hu : CPTs u) (hv : NCPT v) : NCPT (fun s => v (u s)) :=
  str_comp (u := u) (v := fun s => un (v s)) hu hv

private lemma nat_revN : NCPT revN := nat_add nat_inputN (nat_const 2)
private lemma cpt_revInput : CPTs revInput := str_comp (u := env) (v := env) str_env str_env
private lemma nat_revI : NCPT revI := nat_revComp (u := env) (v := idx) str_env nat_idx
private lemma nat_revJ : NCPT revJ := nat_idx
private lemma nat_revV : NCPT (fun y => inputN (revInput y)) :=
  nat_revComp cpt_revInput nat_inputN

-- The preceding full rows contribute v-(a+1) pairs each; j follows j-(i+1)
-- earlier entries of row i. The row count is itself a bounded unary tabulation.
private def revRankTerm (x : List Bool) := un ((env x).length - (idx x + 1))
private def revRank (v i j : Nat) :=
  (tab i v (un v) revRankTerm).length + (j - (i+1))

private lemma nat_revRank {v i j : List Bool → Nat} (hv : NCPT v) (hi : NCPT i) (hj : NCPT j) :
    NCPT (fun y => revRank (v y) (i y) (j y)) :=
  nat_add (nat_len (cpt_tab hi hv hv
    (nat_sub (nat_len str_env) (nat_add nat_idx (nat_const 1)))))
    (nat_sub hj (nat_add hi (nat_const 1)))

private def revRead (c : Nat) (y : List Bool) : Bool :=
  let s := revInput y
  (dropN s)[2 * revRank (inputN s) (revI y) (revJ y) + c]?.getD false

private lemma test_revRead (c : Nat) : Test (fun y => revRead c y = true) :=
  test_bit (nat_add (nat_mul (nat_const 2) (nat_revRank nat_revV nat_revI nat_revJ)) (nat_const c))
    (cpt_comp cpt_revInput cpt_dropN)

private abbrev revOld (y : List Bool) : Prop :=
  revI y < inputN (revInput y) ∧ revJ y < inputN (revInput y) ∧ revRead 0 y = true

private abbrev revForced (y : List Bool) : Prop :=
  revI y = inputN (revInput y) ∧ revJ y = inputN (revInput y) + 1

private def revChoose (probe : Bool) (y : List Bool) : Bool :=
  if probe then decide (revOld y ∧ revRead 1 y = true)
  else decide (¬(revForced y ∨ revOld y))

private lemma test_revOld : Test revOld :=
  test_and (test_lt nat_revI nat_revV) (test_and (test_lt nat_revJ nat_revV) (test_revRead 0))

private lemma test_revChoose (probe : Bool) : Test (fun y => revChoose probe y = true) := by
  cases probe
  · simpa only [revChoose, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using
      test_not (test_or (test_and (test_eq nat_revI nat_revV)
        (test_eq nat_revJ (nat_add nat_revV (nat_const 1)))) test_revOld)
  · simpa only [revChoose, ↓reduceIte, decide_eq_true_eq] using
      test_and test_revOld (test_revRead 1)

private def revGridInner (b : List Bool → Nat) (f : List Bool → List Bool) (x : List Bool) :=
  tab (revN (env x)) (b (env x)) x (fun y => if revI y < revJ y then f y else [])

private def revGrid (b : List Bool → Nat) (f : List Bool → List Bool) (s : List Bool) :=
  tab (revN s) (revN s * b s) s (revGridInner b f)

private lemma cpt_revGrid {b : List Bool → Nat} {f : List Bool → List Bool}
    (hb : NCPT b) (hf : CPTs f) : CPTs (revGrid b f) :=
  cpt_tab nat_revN (nat_mul nat_revN hb) str_id
    (cpt_tab (nat_revComp (u := env) (v := revN) str_env nat_revN)
      (nat_revComp (u := env) (v := b) str_env hb) str_id
      (str_if (test_lt nat_revI nat_revJ) hf (cpt_const [])))

private def revGate (probe : Bool) (f : List Bool → List Bool) (y : List Bool) :=
  if revChoose probe y then f y else []

private lemma cpt_revGate (probe : Bool) {f : List Bool → List Bool} (hf : CPTs f) :
    CPTs (revGate probe f) := str_if (test_revChoose probe) hf (cpt_const [])

private def revRowBit (z : List Bool) : List Bool :=
  [decide (idx z = revI (env z) ∨ idx z = revJ (env z))]

private lemma cpt_revRowBit : CPTs revRowBit :=
  str_bit (test_or (test_eq nat_idx (nat_revComp (u := env) (v := revI) str_env nat_revI))
    (test_eq nat_idx (nat_revComp (u := env) (v := revJ) str_env nat_revJ)))

private def revRow (probe : Bool) (y : List Bool) :=
  let n := revN (revInput y)
  tab n 1 y revRowBit ++ List.replicate n false ++ (if probe then [true] else [])

private lemma cpt_revRow (probe : Bool) : CPTs (revRow probe) := by
  have hn := nat_revComp (u := revInput) (v := revN) cpt_revInput nat_revN
  have hz : CPTs (fun y => List.replicate (revN (revInput y)) false) :=
    q39 (cpt_comp hn cpt_blank) (by intro y; simp [blank, un])
  exact cpt_app2 (cpt_app2 (cpt_tab hn (nat_const 1) str_id cpt_revRowBit) hz)
    (cpt_const (if probe then [true] else []))

private def revWidth (s : List Bool) := 2 * revN s + 1
private def revCount (probe : Bool) (s : List Bool) :=
  (revGrid (fun _ => 1) (revGate probe (fun _ => [true])) s).length
private def revRows (probe : Bool) := revGrid revWidth (revGate probe (revRow probe))

def reverseQ (s : List Bool) : List Bool :=
  hdr (revN s) ++ hdr (revCount false s) ++ revRows false s ++
    hdr (revCount true s) ++ revRows true s

lemma cpt_reverseQ : CPTs reverseQ := by
  have count (probe : Bool) : NCPT (revCount probe) :=
    nat_len (cpt_revGrid (nat_const 1) (cpt_revGate probe (cpt_const [true])))
  have rows (probe : Bool) : CPTs (revRows probe) :=
    cpt_revGrid (nat_add (nat_mul (nat_const 2) nat_revN) (nat_const 1))
      (cpt_revGate probe (cpt_revRow probe))
  exact cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 nat_revN (cpt_const [false]))
    (cpt_app2 (count false) (cpt_const [false]))) (rows false))
    (cpt_app2 (count true) (cpt_const [false]))) (rows true)

private lemma rev_range'_split (s : Nat) {n k : Nat} (h : k < n) :
    List.range' s n = List.range' s k ++ (s+k) :: List.range' (s+k+1) (n-(k+1)) := by
  calc
    List.range' s n = List.range' s (k + (n-k)) := by rw [Nat.add_sub_of_le (Nat.le_of_lt h)]
    _ = List.range' s k ++ List.range' (s+k) (n-k) := List.range'_append_1.symm
    _ = _ := by
      have h₁ : n-k = (n-(k+1))+1 := by omega
      rw [h₁]
      rfl

private lemma rev_range_split {n k : Nat} (h : k < n) :
    List.range n = List.range k ++ k :: List.range' (k+1) (n-(k+1)) := by
  simpa only [← List.range_eq_range', Nat.zero_add] using rev_range'_split 0 h

private lemma rev_range_filter {v a : Nat} (ha : a < v) :
    ((List.range v).filter (fun j => decide (a < j))) = List.range' (a+1) (v-(a+1)) := by
  have h₀ : ((List.range a).filter (fun j => decide (a < j))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    have := List.mem_range.mp hj
    simp only [decide_eq_true_eq]
    omega
  have h₁ : ((List.range' (a+1) (v-(a+1))).filter (fun j => decide (a < j))) =
      List.range' (a+1) (v-(a+1)) := by
    apply List.filter_eq_self.mpr
    intro j hj
    obtain ⟨k, _, hk⟩ := List.mem_range'.mp hj
    simp only [decide_eq_true_eq]
    omega
  rw [rev_range_split ha, List.filter_append]
  simp [h₀, h₁]

private def revNatPairs (v : Nat) :=
  (List.range v).flatMap (fun i => ((List.range v).filter (fun j => decide (i < j))).map (fun j => (i,j)))

private lemma rev_pairs_vals (v : Nat) :
    (pairs v).map (fun e => (e.1.val, e.2.val)) = revNatPairs v := by
  calc
    (pairs v).map (fun e => (e.1.val, e.2.val)) =
        (pairs v).flatMap (fun e => [(e.1.val, e.2.val)]) := List.map_eq_flatMap
    _ = (List.range v).flatMap (fun i => (List.range v).flatMap (fun j => if i < j then [(i,j)] else [])) :=
      pairs_flatMap_nat v (fun i j => [(i,j)])
    _ = revNatPairs v := by
      unfold revNatPairs
      apply List.flatMap_congr
      intro i _
      rw [List.map_eq_flatMap, flatMap_map_filter]

private lemma rev_rank_prefix {v i j : Nat} (hij : i < j) (hjv : j < v) :
    ∃ a b, revNatPairs v = a ++ (i,j) :: b ∧ a.length = revRank v i j := by
  let row := fun a => ((List.range v).filter (fun b => decide (a < b))).map (fun b => (a,b))
  let head := (List.range i).flatMap row
  let tail := (List.range' (i+1) (v-(i+1))).flatMap row
  let k := j-(i+1)
  have h₀ : i < v := hij.trans hjv
  have hk : k < v-(i+1) := by dsimp [k]; omega
  have hkj : i+1+k = j := by dsimp [k]; omega
  let before := (List.range' (i+1) k).map (fun b => (i,b))
  let after := (List.range' (i+1+k+1) (v-(i+1)-(k+1))).map (fun b => (i,b))
  have hrow : row i = before ++ (i,j) :: after := by
    dsimp [row, before, after]
    rw [rev_range_filter h₀, rev_range'_split (i+1) hk, List.map_append, List.map_cons]
    rw [hkj]
  have hhead : head.length = (tab i v (un v) revRankTerm).length := by
    rw [tab_eq]
    · simp only [head, List.length_flatMap]
      congr 1
      apply List.map_congr_left
      intro a ha
      have ha' := (List.mem_range.mp ha).trans h₀
      simp [row, rev_range_filter ha', revRankTerm, env_pack, idx_pack]
    · intro a _
      simp [revRankTerm, env_pack, idx_pack]
  refine ⟨head ++ before, after ++ tail, ?_, ?_⟩
  · change (List.range v).flatMap row = _
    rw [rev_range_split h₀, List.flatMap_append, List.flatMap_cons, hrow]
    simp [head, tail, List.append_assoc]
  · simp [revRank, before, k, hhead]

private def revLift {v : Nat} (F : Fin v → Fin v → Bool) (e : Nat × Nat) : Bool :=
  if h : e.1 < v ∧ e.2 < v then F ⟨e.1,h.1⟩ ⟨e.2,h.2⟩ else false

private lemma rev_matrix {v : Nat} (G R : Fin v → Fin v → Bool) :
    dropN (paint v G R) = (revNatPairs v).flatMap (fun e => [revLift G e, revLift R e]) := by
  rw [paint, hdr_dropN, ← rev_pairs_vals, List.flatMap_map]
  apply List.flatMap_congr
  intro e _
  simp [revLift, e.1.isLt, e.2.isLt]

private lemma rev_read_paint {v i j : Nat} (G R : Fin v → Fin v → Bool)
    (hi : i < v) (hj : j < v) (hij : i < j) (c : Bool) :
    revRead c.toNat (revPack (paint v G R) i j) = (if c then R else G) ⟨i,hi⟩ ⟨j,hj⟩ := by
  obtain ⟨a,b,hab,har⟩ := rev_rank_prefix hij hj
  have hv : inputN (paint v G R) = v := hdr_inputN _ _
  simp only [revRead, revInput, revI, revJ, revPack, env_pack, idx_pack, hv]
  rw [rev_matrix, hab, List.flatMap_append, List.flatMap_cons]
  have hz : (a.flatMap (fun e => [revLift G e, revLift R e])).length = 2 * revRank v i j := by
    rw [flatMap_len_of _ _ 2 (fun _ => rfl), har]
  have hle : (a.flatMap (fun e => [revLift G e, revLift R e])).length ≤
      2 * revRank v i j + c.toNat := by rw [hz]; omega
  rw [List.getElem?_append_right hle, hz, Nat.add_sub_cancel_left]
  cases c <;> simp [revLift, hi, hj]

private lemma rev_tab_length (n b : Nat) (s : List Bool) (f : List Bool → List Bool) :
    (tab n b s f).length ≤ n*b := by
  induction n with
  | zero => simp [tab]
  | succ n ih =>
    simp only [tab, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.length_append, List.length_take, Nat.succ_mul] at ih ⊢
    exact Nat.add_le_add ih (Nat.min_le_left ..)

private lemma rev_grid_spec (b : List Bool → Nat) (f : List Bool → List Bool) (s : List Bool)
    (hf : ∀ i < revN s, ∀ j < revN s, (f (revPack s i j)).length ≤ b s) :
    revGrid b f s = (pairs (revN s)).flatMap (fun e => f (revPack s e.1.val e.2.val)) := by
  rw [revGrid, tab_eq, pairs_flatMap_nat (revN s) (fun i j => f (revPack s i j))]
  · apply List.flatMap_congr
    intro i hi
    simp only [revGridInner, env_pack]
    rw [tab_eq]
    · apply List.flatMap_congr
      intro j _
      simp [revI, revJ, revPack, env_pack, idx_pack]
    · intro j hj
      simp only [revI, revJ, env_pack, idx_pack]
      split
      · exact hf i (List.mem_range.mp hi) j hj
      · simp
  · intro i _
    simpa only [revGridInner, env_pack] using
      rev_tab_length (revN s) (b s) (pairB s (un i)) (fun y => if revI y < revJ y then f y else [])

private lemma rev_grid_filter {b : List Bool → Nat} {f : List Bool → List Bool} {s : List Bool}
    {n : Nat} (hs : revN s = n) (probe : Bool) (p : Fin n × Fin n → Bool)
    (hp : ∀ e ∈ pairs n, revChoose probe (revPack s e.1.val e.2.val) = p e)
    (hf : ∀ i < revN s, ∀ j < revN s, (f (revPack s i j)).length ≤ b s) :
    revGrid b (revGate probe f) s =
      ((pairs n).filter p).flatMap (fun e => f (revPack s e.1.val e.2.val)) := by
  subst n
  rw [rev_grid_spec]
  · have hfilter : (pairs (revN s)).filter p =
        (pairs (revN s)).filter (fun e => decide (p e = true)) := by
      apply List.filter_congr
      intro e _
      cases p e <;> rfl
    rw [hfilter, flatMap_map_filter]
    apply List.flatMap_congr
    intro e he
    simp [revGate, hp e he]
  · intro i hi j hj
    unfold revGate
    split
    · exact hf i hi j hj
    · simp

private def revPostedRow {n : Nat} (e : Fin n × Fin n) : List Bool :=
  (List.finRange n).map (fun i => decide (i = e.1 ∨ i = e.2))

private lemma rev_row_spec {s : List Bool} {n : Nat} (hs : revN s = n)
    (probe : Bool) (e : Fin n × Fin n) :
    revRow probe (revPack s e.1.val e.2.val) =
      revPostedRow e ++ List.replicate n false ++ (if probe then [true] else []) := by
  simp only [revRow, revInput, revPack, env_pack, hs]
  rw [tab_eq n 1 (pairB (pairB s (un e.1.val)) (un e.2.val)) revRowBit (fun _ _ => le_rfl)]
  have hmap : (List.finRange n).map (fun i => decide (i = e.1 ∨ i = e.2)) =
      (List.range n).map (fun k => decide (k = e.1.val ∨ k = e.2.val)) := by
    rw [← range_vals, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Fin.ext_iff]
  rw [revPostedRow, hmap, List.map_eq_flatMap]
  simp only [revRowBit, revI, revJ, env_pack, idx_pack]

private lemma rev_row_bound (probe : Bool) (s : List Bool) (i j : Nat) :
    (revRow probe (revPack s i j)).length ≤ revWidth s := by
  have htab := rev_tab_length (revN s) 1 (revPack s i j) revRowBit
  simp only [revRow, revInput, revPack, env_pack, revWidth, List.length_append,
    List.length_replicate, Nat.mul_one] at htab ⊢
  cases probe <;> simp <;> omega

private lemma rev_block_spec {s : List Bool} {n : Nat} (hs : revN s = n)
    (probe : Bool) (p : Fin n × Fin n → Bool)
    (hp : ∀ e ∈ pairs n, revChoose probe (revPack s e.1.val e.2.val) = p e) :
    revCount probe s = ((pairs n).filter p).length ∧
    revRows probe s = ((pairs n).filter p).flatMap (fun e =>
      revPostedRow e ++ List.replicate n false ++ (if probe then [true] else [])) := by
  constructor
  · unfold revCount
    rw [rev_grid_filter (b := fun _ => 1) (f := fun _ => [true]) hs probe p hp (by intros; exact le_rfl)]
    simpa only [Nat.one_mul] using flatMap_len_of ((pairs n).filter p) (fun _ => [true]) 1 (fun _ => rfl)
  · unfold revRows
    rw [rev_grid_filter (b := revWidth) (f := revRow probe) hs probe p hp
      (fun i _ j _ => rev_row_bound probe s i j)]
    apply List.flatMap_congr
    exact fun e _ => rev_row_spec hs probe e

private lemma rev_mem_old {v i j : Nat} (F : Fin v → Fin v → Bool) (hij : i < j) :
    (i,j) ∈ ((pairs v).filter (fun e => F e.1 e.2)).map (fun e => (e.1.val,e.2.val)) ↔
      ∃ (hi : i < v) (hj : j < v), F ⟨i,hi⟩ ⟨j,hj⟩ = true := by
  simp only [List.mem_map, List.mem_filter, mem_pairs]
  constructor
  · rintro ⟨⟨a,b⟩, ⟨_, hF⟩, he⟩
    obtain ⟨ha,hb⟩ := Prod.mk.inj he
    subst i
    subst j
    exact ⟨a.isLt, b.isLt, hF⟩
  · rintro ⟨hi,hj,hF⟩
    exact ⟨(⟨i,hi⟩,⟨j,hj⟩), ⟨hij,hF⟩, rfl⟩

private lemma rev_choose_paint {v n : Nat} (G R : Fin v → Fin v → Bool) (probe : Bool)
    (e : Fin n × Fin n) (he : e.1 < e.2) :
    revChoose probe (revPack (paint v G R) e.1.val e.2.val) =
      if probe then
        decide ((e.1.val,e.2.val) ∈ ((pairs v).filter (fun z => G z.1 z.2 && R z.1 z.2)).map
          (fun z => (z.1.val,z.2.val)))
      else
        decide ((e.1.val,e.2.val) ∉ (v,v+1) :: ((pairs v).filter (fun z => G z.1 z.2)).map
          (fun z => (z.1.val,z.2.val))) := by
  let i := e.1.val
  let j := e.2.val
  have hij : i < j := he
  have hv : inputN (paint v G R) = v := hdr_inputN _ _
  have hforced : (revForced (revPack (paint v G R) i j)) ↔ (i,j) = (v,v+1) := by
    simp [revForced, revI, revJ, revInput, revPack, env_pack, idx_pack, hv]
  have hold : revOld (revPack (paint v G R) i j) ↔
      ∃ (hi : i < v) (hj : j < v), G ⟨i,hi⟩ ⟨j,hj⟩ = true := by
    simp only [revOld, revI, revJ, revInput, revPack, env_pack, idx_pack, hv]
    constructor
    · rintro ⟨hi,hj,hbit⟩
      exact ⟨hi,hj,(rev_read_paint G R hi hj hij false).symm.trans hbit⟩
    · rintro ⟨hi,hj,hbit⟩
      exact ⟨hi,hj,(rev_read_paint G R hi hj hij false).trans hbit⟩
  change revChoose probe (revPack (paint v G R) i j) =
    if probe then
      decide ((i,j) ∈ ((pairs v).filter (fun z => G z.1 z.2 && R z.1 z.2)).map
        (fun z => (z.1.val,z.2.val)))
    else
      decide ((i,j) ∉ (v,v+1) :: ((pairs v).filter (fun z => G z.1 z.2)).map
        (fun z => (z.1.val,z.2.val)))
  cases probe
  · simp only [revChoose, Bool.false_eq_true, ↓reduceIte, List.mem_cons, hforced, hold,
      rev_mem_old (i := i) (j := j) G hij,
      decide_eq_decide]
  · simp only [revChoose, ↓reduceIte, hold,
      rev_mem_old (i := i) (j := j) (fun a b => G a b && R a b) hij,
      Bool.and_eq_true, decide_eq_decide]
    constructor
    · rintro ⟨⟨hi,hj,hG⟩,hR⟩
      exact ⟨hi,hj,hG,(rev_read_paint G R hi hj hij true).symm.trans hR⟩
    · rintro ⟨hi,hj,hG,hR⟩
      exact ⟨⟨hi,hj,hG⟩,(rev_read_paint G R hi hj hij true).trans hR⟩

lemma reverseQ_spec (h : Nat) (G R : Fin (2*h) → Fin (2*h) → Bool) :
    let v := 2*h
    let n := v+2
    let oldEdges := ((pairs v).filter (fun e => G e.1 e.2)).map (fun e => (e.1.val,e.2.val))
    let reds := ((pairs v).filter (fun e => G e.1 e.2 && R e.1 e.2)).map (fun e => (e.1.val,e.2.val))
    let bans := (pairs n).filter (fun e => decide ((e.1.val,e.2.val) ∉ (v,v+1)::oldEdges))
    let probes := (pairs n).filter (fun e => decide ((e.1.val,e.2.val) ∈ reds))
    let row := fun (e : Fin n × Fin n) => (List.finRange n).map
      (fun i => decide (i = e.1 ∨ i = e.2))
    let zero := List.replicate n false
    reverseQ (paint v G R) = hdr n ++ hdr bans.length ++
      bans.flatMap (fun e => row e ++ zero) ++ hdr probes.length ++
      probes.flatMap (fun e => row e ++ zero ++ [true]) := by
  dsimp only
  have hn : revN (paint (2*h) G R) = 2*h+2 := by simp [revN, paint, hdr_inputN]
  let oldEdges := ((pairs (2*h)).filter (fun z => G z.1 z.2)).map (fun z => (z.1.val,z.2.val))
  let reds := ((pairs (2*h)).filter (fun z => G z.1 z.2 && R z.1 z.2)).map (fun z => (z.1.val,z.2.val))
  let ban (e : Fin (2*h+2) × Fin (2*h+2)) := decide ((e.1.val,e.2.val) ∉ (2*h,2*h+1)::oldEdges)
  let probe (e : Fin (2*h+2) × Fin (2*h+2)) := decide ((e.1.val,e.2.val) ∈ reds)
  have hban := rev_block_spec hn false ban (by
    intro e he
    simpa only [ban, oldEdges, Bool.false_eq_true, ↓reduceIte] using
      rev_choose_paint G R false e (mem_pairs.mp he))
  have hprobe := rev_block_spec hn true probe (by
    intro e he
    simpa only [probe, reds, ↓reduceIte] using rev_choose_paint G R true e (mem_pairs.mp he))
  rw [reverseQ, hn, hban.1, hban.2, hprobe.1, hprobe.2]
  simp [revPostedRow, ban, probe, oldEdges, reds]

end PEqualNP.Outside.L_meta_33617.Machine



/- Circuit normal form and probe correspondence ported from
   lean/PEqualNP.Outside.L_meta_33617.lean at 773a44dea4b8f3176d5cc06e6ceb5ca0c8aee81a,
   lines 11–1874 and 2675–2720. Namespace rebased; new Fin-endpoint bridge follows. -/
namespace PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def reads (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem reads_le (g : Gate) : (reads g).length ≤ g.inputs.length := by
  cases h : g.op <;> simp [reads, h, Nat.min_le_right]

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  ((reads g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ reads g, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem eval_congr_reads (g : Gate) (w w' : List Bool)
    (h : ∀ a ∈ reads g, w.getD a false = w'.getD a false) :
    g.op.eval (g.inputs.map fun a => w.getD a false) =
      g.op.eval (g.inputs.map fun a => w'.getD a false) := by
  by_cases hn : g.op = .not
  · rw [hn]
    cases hi : g.inputs with
    | nil => simp [GateOp.eval, hi]
    | cons a l =>
      have ha := h a (by simp [reads, hn, hi])
      change (!w.getD a false) = !w'.getD a false
      rw [ha]
  · have he : g.inputs.map (fun a => w.getD a false) =
        g.inputs.map (fun a => w'.getD a false) := by
      apply List.map_congr_left
      intro a ha
      exact h a (by cases ho : g.op <;> simp_all [reads])
    rw [he]

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply eval_congr_reads
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (reads g).toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hg)) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (reads g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem getD_take_eq (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD w false =
      (wiresFrom (C.gates.take k) (List.ofFn x)).getD w false := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  conv_lhs => rw [← List.take_append_drop k C.gates]
  rw [wiresFrom_append]
  apply getD_wiresFrom
  rw [length_wiresFrom]
  simpa [List.length_take, Nat.min_eq_left hk] using hw

theorem wire_support (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ k + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        (C.wires (List.ofFn x)).getD w false =
          (C.wires (List.ofFn y)).getD w false := by
  let S := (suppsFrom (C.gates.take k) (inputSupps n)).getD w ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom (C.gates.take k) 0 (inputSupps n)
      (fun g hg => hfan g (List.mem_of_mem_take hg)) cnt_inputs {w}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
      List.length_take, Nat.min_eq_left hk] using hc
  · intro x y heq
    rw [getD_take_eq C n k w hk hw x, getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y (C.gates.take k) _ _ _ (agree_inputs x y)).2.2 w heq

theorem wire_essential_bound (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (E : Finset (Fin n))
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) :
    E.card ≤ k + 1 := by
  obtain ⟨S, hcard, hdep⟩ := wire_support C n k w hk hw hfan
  apply le_trans (Finset.card_le_card (t := S) ?_) hcard
  intro i hi
  by_contra hni
  obtain ⟨x, y, hxy, hne⟩ := hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  apply hxy j
  intro hji
  subst j
  exact hni hj

def RO (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ Q : Finset (Fin n) → ((Fin n → Bool) → Bool) → Prop,
    (∀ i : Fin n, Q {i} (fun x => x i)) →
    (∀ A B a b, Disjoint A B → Q A a → Q B b →
      Q (A ∪ B) (fun x => a x && b x) ∧ Q (A ∪ B) (fun x => a x || b x)) → Q S f

theorem ro_leaf (i : Fin n) : RO {i} (fun x => x i) := fun _ hl _ => hl i

theorem ro_and {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x && b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1

theorem ro_or {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x || b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2

def Fam (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (W : Finset ℕ) : Prop :=
  (∀ w ∈ W, RO (L.getD w ∅) (F w)) ∧
  (∀ w ∈ W, ∀ v ∈ W, w ≠ v → Disjoint (L.getD w ∅) (L.getD v ∅))

def Tight (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card = t + W.card → Fam L F W

theorem tight_inputs : Tight 0 (inputSupps n) (fun j x => (List.ofFn x).getD j false) := by
  intro W heq
  have hvalid : ∀ j ∈ W, j < n := by
    intro j hj
    by_contra hn
    have hz : (inputSupps n).getD j ∅ = ∅ :=
      List.getD_eq_default _ _ (by simp [inputSupps]; omega)
    have he := heq
    rw [← Finset.insert_erase hj, Finset.biUnion_insert, hz, Finset.empty_union] at he
    rw [Finset.insert_erase hj] at he
    have hc := cnt_inputs (n := n) (W.erase j)
    have hcard := Finset.card_erase_add_one hj
    omega
  constructor
  · intro j hj
    have hv := hvalid j hj
    have hs : (inputSupps n).getD j ∅ = {⟨j, hv⟩} := by simp [inputSupps, hv]
    have hf : (fun x : Fin n → Bool => (List.ofFn x).getD j false) = (fun x => x ⟨j,hv⟩) := by
      funext x; simp [hv]
    rw [hs]
    change RO {⟨j,hv⟩} (fun x : Fin n → Bool => (List.ofFn x).getD j false)
    rw [hf]
    exact ro_leaf _
  · intro j hj k hk hne
    have hjn := hvalid j hj
    have hkn := hvalid k hk
    simpa [inputSupps, hjn, hkn, Fin.ext_iff] using hne

theorem union_step (L : List (Finset (Fin n))) (g : Gate) (W : Finset ℕ)
    (hW : L.length ∈ W) :
    (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi ⊢
    obtain ⟨j, hjW, hij⟩ := hi
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hij
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
      exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
    · rw [getD_snoc_ne _ _ _ _ hjl] at hij
      exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
  · intro hi
    obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_union.mp hj with hj | hj
    · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_of_mem_erase hj, ?_⟩
      rw [getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hj)]
      exact hi
    · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
      rw [getD_snoc_eq]
      exact (mem_gateSupp L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩

theorem binary_of_reads (g : Gate)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : g.inputs.length ≤ 2) (hcard : (reads g).toFinset.card = 2) :
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ (g.op = .and ∨ g.op = .or) := by
  have hn : g.op ≠ .not := by
    intro hn
    have hc := List.toFinset_card_le (reads g)
    have hl : (reads g).length ≤ 1 := by simp [reads,hn]
    omega
  have hop : g.op = .and ∨ g.op = .or := by rcases ho with h | h | h <;> simp_all
  have hr : reads g = g.inputs := by rcases hop with h | h <;> simp [reads,h]
  rw [hr] at hcard
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hi] at hcard
  · simp [hi] at hcard
  · refine ⟨a,b,rfl,?_,hop⟩
    intro hab
    simp [hi,hab] at hcard
  · simp [hi] at hlen

def nextF (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (g : Gate)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  if j = L.length then g.op.eval (g.inputs.map fun a => F a x) else F j x

theorem tight_step (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool)
    (g : Gate) (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hc : Cnt t L) (ht : Tight t L F) :
    Tight (t+1) (L ++ [gateSupp L g]) (nextF L F g) := by
  intro W heq
  have hW : L.length ∈ W := by
    by_contra hn
    have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun h => hn (h ▸ hj))
    rw [hU] at heq
    have := hc W
    omega
  let E := W.erase L.length
  let B := (reads g).toFinset
  let P := E ∪ B
  have hEc : E.card+1 = W.card := Finset.card_erase_add_one hW
  have hBc : B.card ≤ 2 := le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hlen)
  have hPc : P.card ≤ E.card + B.card := Finset.card_union_le _ _
  have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      (P.biUnion fun j => L.getD j ∅) := union_step L g W hW
  rw [hU] at heq
  have hcP := hc P
  have hB2 : B.card = 2 := by omega
  have hPexact : P.card = E.card + B.card := by omega
  have hTexact : (P.biUnion fun j => L.getD j ∅).card = t + P.card := by omega
  have hEB : Disjoint E B := Finset.card_union_eq_card_add_card.mp hPexact
  obtain ⟨a,b,hin,hab,hop⟩ := binary_of_reads g ho hlen hB2
  have hreads : reads g = [a,b] := by rcases hop with h | h <;> simp [reads,h,hin]
  have haB : a ∈ B := by simp [B,hreads]
  have hbB : b ∈ B := by simp [B,hreads]
  have haP : a ∈ P := Finset.mem_union_right _ haB
  have hbP : b ∈ P := Finset.mem_union_right _ hbB
  have hF := ht P hTexact
  have hEP : E ⊆ P := Finset.subset_union_left
  have hneA : ∀ w ∈ E, w ≠ a := by
    intro w hw hwa; subst w
    exact Finset.disjoint_left.mp hEB hw haB
  have hneB : ∀ w ∈ E, w ≠ b := by
    intro w hw hwb; subst w
    exact Finset.disjoint_left.mp hEB hw hbB
  have hS : gateSupp L g = L.getD a ∅ ∪ L.getD b ∅ := by simp [gateSupp,hreads]
  have hnew : RO (gateSupp L g) (nextF L F g L.length) := by
    rw [hS]
    have hd := hF.2 a haP b hbP hab
    rcases hop with hop | hop
    · have hf : nextF L F g L.length = (fun x => F a x && F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_and hd (hF.1 a haP) (hF.1 b hbP)
    · have hf : nextF L F g L.length = (fun x => F a x || F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_or hd (hF.1 a haP) (hF.1 b hbP)
  have hother : ∀ w ∈ E, (L ++ [gateSupp L g]).getD w ∅ = L.getD w ∅ :=
    fun w hw => getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hw)
  have hnewdis : ∀ w ∈ E, Disjoint (gateSupp L g) (L.getD w ∅) := by
    intro w hw
    rw [hS,Finset.disjoint_union_left]
    exact ⟨hF.2 a haP w (hEP hw) (hneA w hw).symm,
      hF.2 b hbP w (hEP hw) (hneB w hw).symm⟩
  constructor
  · intro w hw
    by_cases hwk : w = L.length
    · subst w
      rw [getD_snoc_eq]
      exact hnew
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      have hf : nextF L F g w = F w := by funext x; simp [nextF,hwk]
      rw [hf]
      exact hF.1 w (hEP hwE)
  · intro w hw v hv hne
    by_cases hwk : w = L.length
    · subst w
      have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
      rw [getD_snoc_eq,hother v hvE]
      exact hnewdis v hvE
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      by_cases hvk : v = L.length
      · subst v
        rw [getD_snoc_eq]
        exact (hnewdis w hwE).symm
      · have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hvk,hv⟩
        rw [hother v hvE]
        exact hF.2 w (hEP hwE) v (hEP hvE) hne

theorem tight_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n)))
    (v : (Fin n → Bool) → List Bool), (∀ x, (v x).length = L.length) →
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    Cnt t L → Tight t L (fun j x => (v x).getD j false) →
    Tight (t+gs.length) (suppsFrom gs L) (fun j x => (wiresFrom gs (v x)).getD j false) := by
  induction gs with
  | nil => intro t L v hv _ hc ht; exact ht
  | cons g gs ih =>
    intro t L v hv hg hc ht
    let v' := fun x : Fin n → Bool => v x ++ [g.op.eval (g.inputs.map fun a => (v x).getD a false)]
    have hv' : ∀ x, (v' x).length = (L ++ [gateSupp L g]).length := by
      intro x; simp [v',hv x]
    have hf : (fun j x => (v' x).getD j false) =
        nextF L (fun j x => (v x).getD j false) g := by
      funext j x
      by_cases hj : j = L.length
      · subst j
        simp only [nextF,ite_true]
        dsimp only [v']
        rw [← hv x,getD_snoc_eq]
      · simp only [nextF,hj,ite_false]
        exact getD_snoc_ne _ _ _ _ (by rw [hv x]; exact hj)
    have hgg := hg g List.mem_cons_self
    have ht' : Tight (t+1) (L ++ [gateSupp L g]) (fun j x => (v' x).getD j false) := by
      rw [hf]
      exact tight_step t L _ g hgg.1 hgg.2 hc ht
    have hres := ih (t+1) (L ++ [gateSupp L g]) v' hv'
      (fun g' h => hg g' (List.mem_cons_of_mem g h)) (cnt_step t L g hgg.2 hc) ht'
    simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
      suppsFrom,wiresFrom,List.foldl_cons,v'] using hres

theorem wire_read_once (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n+k)
    (hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (E : Finset (Fin n)) (hE : E.card = k+1)
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
      (C.wires (List.ofFn x)).getD w false ≠ (C.wires (List.ofFn y)).getD w false) :
    RO E (fun x => (C.wires (List.ofFn x)).getD w false) := by
  let gs := C.gates.take k
  let L := suppsFrom gs (inputSupps n)
  let S := L.getD w ∅
  have hlen : gs.length = k := by simp [gs,List.length_take,Nat.min_eq_left hk]
  have hfan' : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hfan g (List.mem_of_mem_take hg)
  have hc := cnt_suppsFrom gs 0 (inputSupps n) (fun g hg => (hfan' g hg).2) cnt_inputs
  have hSc : S.card ≤ k+1 := by
    have := hc {w}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
  have hdep : ∀ x y : Fin n → Bool, (∀ i ∈ S,x i=y i) →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
    intro x y hxy
    rw [getD_take_eq C n k w hk hw x,getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y gs _ _ _ (agree_inputs x y)).2.2 w hxy
  have hsub : E ⊆ S := by
    intro i hi
    by_contra hni
    obtain ⟨x,y,hxy,hne⟩ := hsens i hi
    apply hne (hdep x y ?_)
    intro j hj
    exact hxy j (fun h => hni (h ▸ hj))
  have hES : E = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hT := tight_suppsFrom gs 0 (inputSupps n) (fun x => List.ofFn x)
    (fun x => by simp [inputSupps]) hfan' cnt_inputs tight_inputs
  have heq : (({w} : Finset ℕ).biUnion fun j => L.getD j ∅).card = (0+gs.length)+({w} : Finset ℕ).card := by
    have hS : S.card = k+1 := by rw [←hES]; exact hE
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
  have hR := (hT {w} heq).1 w (Finset.mem_singleton_self w)
  change RO S _ at hR
  rw [←hES] at hR
  have hf : (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) =
      (fun x => (C.wires (List.ofFn x)).getD w false) := by
    funext x; exact (getD_take_eq C n k w hk hw x).symm
  change RO E (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) at hR
  rw [hf] at hR
  exact hR

end PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce

namespace PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce

variable {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}

theorem ro_nonempty (h : RO S f) : S.Nonempty := by
  apply h (fun S _ => S.Nonempty)
  · intro i; exact Finset.singleton_nonempty i
  · intro A B a b hd ha hb
    exact ⟨ha.mono Finset.subset_union_left,ha.mono Finset.subset_union_left⟩

theorem ro_zero (h : RO S f) (x : Fin n → Bool) (hx : ∀ i ∈ S,x i=false) : f x=false := by
  apply h (fun S f => ∀ x, (∀ i ∈ S,x i=false) → f x=false) ?_ ?_ x hx
  · intro i x hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x hx
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl

theorem ro_depends (h : RO S f) (x y : Fin n → Bool) (hx : ∀ i ∈ S,x i=y i) : f x=f y := by
  apply h (fun S f => ∀ x y, (∀ i ∈ S,x i=y i) → f x=f y) ?_ ?_ x y hx
  · intro i x y hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x y hx <;> dsimp only <;>
      rw [ha x y (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x y (fun i hi => hx i (Finset.mem_union_right _ hi))]

theorem ro_mono (h : RO S f) (x y : Fin n → Bool)
    (hxy : ∀ i,x i=true → y i=true) (hf : f x=true) : f y=true := by
  apply h (fun _ f => ∀ x y, (∀ i,x i=true → y i=true) → f x=true → f y=true) ?_ ?_ x y hxy hf
  · intro i x y hxy hf; exact hxy i hf
  · intro A B a b hd ha hb
    constructor
    · intro x y hxy hf
      simp only [Bool.and_eq_true] at hf ⊢
      exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
    · intro x y hxy hf
      simp only [Bool.or_eq_true] at hf ⊢
      exact hf.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))

theorem ro_split (h : RO S f) :
    (∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)) := by
  let Q := fun S f => RO S f ∧
    ((∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)))
  have hQ : Q S f := h Q (fun i => ⟨ro_leaf i,Or.inl ⟨i,rfl,rfl⟩⟩) (by
    intro A B a b hd ha hb
    constructor
    · exact ⟨ro_and hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inl rfl⟩⟩
    · exact ⟨ro_or hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inr rfl⟩⟩)
  exact hQ.2

def pair (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)
def single (i : Fin n) : Fin n → Bool := fun k => decide (k=i)

theorem pair_comm (i j : Fin n) : pair i j=pair j i := by funext k; simp [pair,or_comm]

theorem pair_zero (h : RO S f) (i j : Fin n) (hi : i ∉ S) (hj : j ∉ S) : f (pair i j)=false := by
  apply ro_zero h
  intro k hk
  simp only [pair,decide_eq_false_iff_not,not_or]
  exact ⟨fun hki => hi (hki ▸ hk),fun hkj => hj (hkj ▸ hk)⟩

theorem pair_left (h : RO S f) (i j : Fin n) (hj : j ∉ S) :
    f (pair i j)=f (single i) := by
  apply ro_depends h
  intro k hk
  have hkj : k≠j := fun hkj => hj (hkj ▸ hk)
  simp [pair,single,hkj]

theorem pair_right (h : RO S f) (i j : Fin n) (hi : i ∉ S) :
    f (pair i j)=f (single j) := by rw [pair_comm]; exact pair_left h j i hi

end PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath

namespace PEqualNP.Outside.L_meta_33617.L853.R017

open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath

variable {n : ℕ}

def NoSingle (f : (Fin n → Bool) → Bool) : Prop := ∀ i, f (single i) = false

def PairCover (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i ∈ S, ∃ j ∈ S, f (pair i j) = true

def Quadratic (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ ∃ i ∈ S, ∃ j ∈ S, f (pair i j) = true ∧ x i = true ∧ x j = true

theorem single_le {i : Fin n} {x : Fin n → Bool} (hi : x i = true) :
    ∀ j, single i j = true → x j = true := by
  intro j hj
  have : j = i := by simpa [single] using hj
  simpa [this] using hi

theorem pair_le {i j : Fin n} {x : Fin n → Bool} (hi : x i = true) (hj : x j = true) :
    ∀ t, pair i j t = true → x t = true := by
  intro t ht
  have : t = i ∨ t = j := by simpa [pair] using ht
  rcases this with rfl | rfl <;> assumption

theorem ro_some_true {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (x : Fin n → Bool) (hx : f x = true) : ∃ i ∈ S, x i = true := by
  by_contra hn
  have hz : ∀ i ∈ S, x i = false := by
    intro i hi
    have h : x i ≠ true := fun ht => hn ⟨i, hi, ht⟩
    exact Bool.eq_false_iff.mpr h
  have h := ro_zero hf x hz
  rw [hx] at h
  contradiction

theorem ro_all_singletons {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hs : ∀ i ∈ S, f (single i) = true) (x : Fin n → Bool) :
    f x = true ↔ ∃ i ∈ S, x i = true := by
  constructor
  · exact ro_some_true hf x
  · rintro ⟨i, hi, hx⟩
    exact ro_mono hf _ _ (single_le hx) (hs i hi)

theorem and_cover_singletons {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hc : PairCover (A ∪ B) (fun x => a x && b x)) :
    (∀ i ∈ A, a (single i) = true) ∧ (∀ j ∈ B, b (single j) = true) := by
  constructor
  · intro i hi
    obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_left _ hi)
    have hia : i ∉ B := Finset.disjoint_left.mp hd hi
    have hja : j ∉ A := by
      intro hjA
      have hjB : j ∉ B := Finset.disjoint_left.mp hd hjA
      have hz := pair_zero hb i j hia hjB
      simp only [hz, Bool.and_false] at hp
      contradiction
    have hpA : a (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true ∧ b (pair i j) = true).1
    rwa [pair_left ha i j hja] at hpA
  · intro i hi
    obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_right _ hi)
    have hia : i ∉ A := Finset.disjoint_right.mp hd hi
    have hja : j ∉ B := by
      intro hjB
      have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
      have hz := pair_zero ha i j hia hjA
      simp only [hz, Bool.false_and] at hp
      contradiction
    have hpB : b (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true ∧ b (pair i j) = true).2
    rwa [pair_left hb i j hja] at hpB

theorem or_cover_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hs : NoSingle (fun x => a x || b x))
    (hc : PairCover (A ∪ B) (fun x => a x || b x)) : PairCover A a := by
  intro i hi
  obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_left _ hi)
  have hia : i ∉ B := Finset.disjoint_left.mp hd hi
  have hsA : ∀ t, a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
  have hsB : ∀ t, b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
  have hpA : a (pair i j) = true := by
    have hp' : a (pair i j) = true ∨ b (pair i j) = true := by simpa only [Bool.or_eq_true] using hp
    rcases hp' with h | h
    · exact h
    · rw [pair_right hb i j hia, hsB j] at h
      contradiction
  have hjA : j ∈ A := by
    by_contra hjA
    rw [pair_left ha i j hjA, hsA i] at hpA
    contradiction
  exact ⟨j, hjA, hpA⟩

theorem pair_cover_quadratic {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hs : NoSingle f) (hc : PairCover S f) : Quadratic S f := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) => RO S f ∧ (NoSingle f → PairCover S f → Quadratic S f)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hs hc
    have h := hs i
    simp [single] at h) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hs hc x
      constructor
      · intro hx
        obtain ⟨hi, hj⟩ := and_cover_singletons hd ha.1 hb.1 hc
        obtain ⟨i, hiA, hxi⟩ := ro_some_true ha.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true ∧ b x = true).1
        obtain ⟨j, hjB, hxj⟩ := ro_some_true hb.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true ∧ b x = true).2
        refine ⟨i, Finset.mem_union_left _ hiA, j, Finset.mem_union_right _ hjB, ?_, hxi, hxj⟩
        have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
        have hiB : i ∉ B := Finset.disjoint_left.mp hd hiA
        dsimp only
        rw [pair_left ha.1 i j hjA, pair_right hb.1 i j hiB, hi i hiA, hj j hjB]
        rfl
      · rintro ⟨i, hi, j, hj, hp, hxi, hxj⟩
        exact ro_mono (ro_and hd ha.1 hb.1) _ _ (pair_le hxi hxj) hp
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hs hc x
      have hsA : NoSingle a := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
      have hsB : NoSingle b := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
      have hcA := or_cover_left hd ha.1 hb.1 hs hc
      have hcB : PairCover B b := by
        have hs' : NoSingle (fun x => b x || a x) := by simpa only [Bool.or_comm] using hs
        have hc' : PairCover (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hc
        exact or_cover_left hd.symm hb.1 ha.1 hs' hc'
      constructor
      · intro hx
        have hx' : a x = true ∨ b x = true := by simpa only [Bool.or_eq_true] using hx
        rcases hx' with h | h
        · obtain ⟨i, hi, j, hj, hp, hxi, hxj⟩ := (ha.2 hsA hcA x).mp h
          refine ⟨i, Finset.mem_union_left _ hi, j, Finset.mem_union_left _ hj, ?_, hxi, hxj⟩
          simp only [hp, Bool.true_or]
        · obtain ⟨i, hi, j, hj, hp, hxi, hxj⟩ := (hb.2 hsB hcB x).mp h
          refine ⟨i, Finset.mem_union_right _ hi, j, Finset.mem_union_right _ hj, ?_, hxi, hxj⟩
          simp only [hp, Bool.or_true]
      · rintro ⟨i, hi, j, hj, hp, hxi, hxj⟩
        exact ro_mono (ro_or hd ha.1 hb.1) _ _ (pair_le hxi hxj) hp)
  exact hQ.2 hs hc

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R017

open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath

variable {n : ℕ}

theorem or_pair_inside_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hs : NoSingle (fun x => a x || b x))
    {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) || b (pair i j)) = true) :
    j ∈ A ∧ a (pair i j) = true := by
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  have hsA : ∀ t, a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
  have hsB : ∀ t, b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
  have hpA : a (pair i j) = true := by
    rcases Bool.or_eq_true_iff.mp hp with h | h
    · exact h
    · rw [pair_right hb i j hiB, hsB j] at h
      contradiction
  refine ⟨?_, hpA⟩
  by_contra hjA
  rw [pair_left ha i j hjA, hsA i] at hpA
  contradiction

theorem and_cross_pair {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hc : PairCover (A ∪ B) (fun x => a x && b x))
    {i j : Fin n} (hi : i ∈ A) (hj : j ∈ B) :
    (a (pair i j) && b (pair i j)) = true := by
  obtain ⟨hsA, hsB⟩ := and_cover_singletons hd ha hb hc
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  have hjA : j ∉ A := Finset.disjoint_right.mp hd hj
  rw [pair_left ha i j hjA, pair_right hb i j hiB, hsA i hi, hsB j hj]
  rfl

theorem and_pair_cross_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (hb : RO B b)
    {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) && b (pair i j)) = true) :
    j ∈ B := by
  by_contra hjB
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  rw [pair_zero hb i j hiB hjB, Bool.and_false] at hp
  contradiction

def Matched (mate : Fin n → Fin n) (color : Fin n → Bool)
    (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  NoSingle f ∧
  (∀ i ∈ S, mate i ∈ S) ∧
  (∀ i ∈ S, f (pair i (mate i)) = true) ∧
  (∀ i j, color i ≠ color j → j ≠ mate i → f (pair i j) = false)

theorem matched_cover {mate : Fin n → Fin n} {color : Fin n → Bool}
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool} (h : Matched mate color S f) :
    PairCover S f := fun i hi => ⟨mate i, h.2.1 i hi, h.2.2.1 i hi⟩

theorem matched_or_left {mate : Fin n → Fin n} {color : Fin n → Bool}
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x || b x)) :
    Matched mate color A a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (Bool.or_eq_false_iff.mp (hm.1 i)).1
  · intro i hi
    exact (or_pair_inside_left hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).1
  · intro i hi
    exact (or_pair_inside_left hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).2
  · intro i j hc hj
    exact (Bool.or_eq_false_iff.mp (hm.2.2.2 i j hc hj)).1

theorem matched_or_right {mate : Fin n → Fin n} {color : Fin n → Bool}
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x || b x)) :
    Matched mate color B b := by
  have h : Matched mate color (B ∪ A) (fun x => b x || a x) := by
    simpa only [Finset.union_comm, Bool.or_comm] using hm
  exact matched_or_left hd.symm hb ha h

theorem and_color_injective_left {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x && b x)) :
    ∀ i ∈ A, ∀ j ∈ A, color i = color j → i = j := by
  intro i hi j hj hij
  have hmj : mate j ∈ B := and_pair_cross_left hd hb hj
    (hm.2.2.1 j (Finset.mem_union_left _ hj))
  have ht : (a (pair i (mate j)) && b (pair i (mate j))) = true :=
    and_cross_pair hd ha hb (matched_cover hm) hi hmj
  have hcm : color i ≠ color (mate j) := by
    intro h
    exact hcol j (h.symm.trans hij)
  have hmate : mate j = mate i := by
    by_contra hne
    have hf := hm.2.2.2 i (mate j) hcm hne
    dsimp only at hf
    rw [hf] at ht
    contradiction
  exact (hmi.injective hmate).symm

def SameColorMatching (color : Fin n → Bool) (S : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, color i = color j → color i = color l →
    f (pair i j) = true → f (pair i l) = true → j = l

theorem matched_same_color_matching {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) : SameColorMatching color S f := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) =>
    RO S f ∧ (Matched mate color S f → SameColorMatching color S f)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hm
    have hs := hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      have hinjA := and_color_injective_left hmi hcol hd ha.1 hb.1 hm
      have hm' : Matched mate color (B ∪ A) (fun x => b x && a x) := by
        simpa only [Finset.union_comm, Bool.and_comm] using hm
      have hinjB := and_color_injective_left hmi hcol hd.symm hb.1 ha.1 hm'
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB := and_pair_cross_left hd hb.1 hi hpj
        have hlB := and_pair_cross_left hd hb.1 hi hpl
        exact hinjB j hjB l hlB (hij.symm.trans hil)
      · have hpj' : (b (pair i j) && a (pair i j)) = true := by simpa only [Bool.and_comm] using hpj
        have hpl' : (b (pair i l) && a (pair i l)) = true := by simpa only [Bool.and_comm] using hpl
        have hjA := and_pair_cross_left hd.symm ha.1 hi hpj'
        have hlA := and_pair_cross_left hd.symm ha.1 hi hpl'
        exact hinjA j hjA l hlA (hij.symm.trans hil)
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA, hpjA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hpj
        obtain ⟨hlA, hplA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hpl
        exact ha.2 (matched_or_left hd ha.1 hb.1 hm) i hi j hjA l hlA hij hil hpjA hplA
      · have hm' : Matched mate color (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hm
        have hpj' : (b (pair i j) || a (pair i j)) = true := by simpa only [Bool.or_comm] using hpj
        have hpl' : (b (pair i l) || a (pair i l)) = true := by simpa only [Bool.or_comm] using hpl
        obtain ⟨hjB, hpjB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hpj'
        obtain ⟨hlB, hplB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hpl'
        exact hb.2 (matched_or_right hd ha.1 hb.1 hm) i hi j hjB l hlB hij hil hpjB hplB)
  exact hQ.2 hm

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R017
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
variable {n : ℕ}

theorem matched_mirror_true {mate : Fin n → Fin n} {color : Fin n → Bool}
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) :
    ∀ i ∈ S, ∀ j ∈ S, f (pair i j) = true → f (pair (mate i) (mate j)) = true := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) =>
    RO S f ∧ (Matched mate color S f →
      ∀ i ∈ S, ∀ j ∈ S, f (pair i j) = true → f (pair (mate i) (mate j)) = true)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hm
    have hs := hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj hp
      have hm' : Matched mate color (B ∪ A) (fun x => b x && a x) := by
        simpa only [Finset.union_comm, Bool.and_comm] using hm
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB := and_pair_cross_left hd hb.1 hi hp
        have hmiB := and_pair_cross_left hd hb.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjA := and_pair_cross_left hd.symm ha.1 hjB
          (hm'.2.2.1 j (Finset.mem_union_left _ hjB))
        have h := and_cross_pair hd.symm hb.1 ha.1 (matched_cover hm') hmiB hmjA
        simpa only [Bool.and_comm] using h
      · have hp' : (b (pair i j) && a (pair i j)) = true := by
          simpa only [Bool.and_comm] using hp
        have hjA := and_pair_cross_left hd.symm ha.1 hi hp'
        have hmiA := and_pair_cross_left hd.symm ha.1 hi
          (hm'.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjB := and_pair_cross_left hd hb.1 hjA (hm.2.2.1 j (Finset.mem_union_left _ hjA))
        exact and_cross_pair hd ha.1 hb.1 (matched_cover hm) hmiA hmjB
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj hp
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA, hpA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hp
        have h := ha.2 (matched_or_left hd ha.1 hb.1 hm) i hi j hjA hpA
        dsimp only
        rw [h, Bool.true_or]
      · have hm' : Matched mate color (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hm
        have hp' : (b (pair i j) || a (pair i j)) = true := by
          simpa only [Bool.or_comm] using hp
        obtain ⟨hjB, hpB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hp'
        have h := hb.2 (matched_or_right hd ha.1 hb.1 hm) i hi j hjB hpB
        dsimp only
        rw [h, Bool.or_true])
  exact hQ.2 hm

theorem matched_mirror {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) :
    f (pair i j) = f (pair (mate i) (mate j)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact matched_mirror_true hf hm i hi j hj
  · intro h
    have h' := matched_mirror_true hf hm (mate i) (hm.2.1 i hi) (mate j) (hm.2.1 j hj) h
    simpa only [hmi i, hmi j] using h'

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R017

variable {α : Type*}

theorem relation_involution (R : α → α → Prop)
    (hs : ∀ {a b}, R a b → R b a) (hi : ∀ a, ¬ R a a)
    (hu : ∀ a b c, R a b → R a c → b = c) :
    ∃ p : Equiv.Perm α, Function.Involutive p ∧
      (∀ a b, R a b ↔ p a = b ∧ b ≠ a) ∧
      (∀ q : Equiv.Perm α, (∀ a b, R a b ↔ q a = b ∧ b ≠ a) → q = p) := by
  classical
  let p : α → α := fun a => if h : ∃ b, R a b then Classical.choose h else a
  have hpR : ∀ a b, R a b → p a = b := by
    intro a b h
    have he : ∃ b, R a b := ⟨b, h⟩
    dsimp only [p]
    rw [dite_eq_left he]
    exact hu a _ b (Classical.choose_spec he) h
  have hp : ∀ a, p a = a ∨ R a (p a) := by
    intro a
    by_cases he : ∃ b, R a b
    · right
      dsimp only [p]
      rw [dite_eq_left he]
      exact Classical.choose_spec he
    · left
      simp [p, he]
  have hpi : Function.Involutive p := by
    intro a
    rcases hp a with h | h
    · rw [h, h]
    · exact hpR _ _ (hs h)
  let e : Equiv.Perm α := hpi.toPerm p
  have heval : ∀ a, e a = p a := fun _ => rfl
  have hiff : ∀ a b, R a b ↔ e a = b ∧ b ≠ a := by
    intro a b
    constructor
    · intro h
      refine ⟨hpR a b h, ?_⟩
      intro hab
      exact hi a (hab ▸ h)
    · rintro ⟨hab, hn⟩
      rcases hp a with h | h
      · exact False.elim (hn (hab.symm.trans h))
      · exact hab ▸ h
  refine ⟨e, hpi, hiff, ?_⟩
  intro q hq
  apply Equiv.ext
  intro a
  by_cases h : p a = a
  · by_cases hqa : q a = a
    · exact hqa.trans h.symm
    · have hr := (hq a (q a)).2 ⟨rfl, hqa⟩
      have he := hpR a (q a) hr
      exact False.elim (hqa (he.symm.trans h))
  · have hr := (hiff a (e a)).2 ⟨rfl, h⟩
    exact (hq a (e a)).1 hr |>.1

theorem relation_involution_commutes {R : α → α → Prop} {p : Equiv.Perm α}
    (hp : ∀ a b, R a b ↔ p a = b ∧ b ≠ a)
    (σ : α → α) (hσ : Function.Involutive σ)
    (hR : ∀ a b, R a b → R (σ a) (σ b)) :
    ∀ a, p (σ a) = σ (p a) := by
  intro a
  by_cases he : p a = a
  · by_cases he' : p (σ a) = σ a
    · rw [he, he']
    · have h := hR (σ a) (p (σ a)) ((hp _ _).2 ⟨rfl, he'⟩)
      rw [hσ a] at h
      obtain ⟨hpa, hne⟩ := (hp _ _).1 h
      exact False.elim (hne (hpa.symm.trans he))
  · have h := hR a (p a) ((hp _ _).2 ⟨rfl, he⟩)
    exact ((hp _ _).1 h).1

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R017
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
variable {n : ℕ}

theorem bool_opposite_equal : ∀ a b c d : Bool, a ≠ c → b ≠ d → c = d → a = b := by decide

theorem matched_involution_normal_form {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) :
    ∃ p : Equiv.Perm (Fin n), Function.Involutive p ∧
      (∀ i, color (p i) = color i) ∧
      (∀ i, p (mate i) = mate (p i)) ∧
      (∀ i, i ∉ S → p i = i) ∧
      (∀ x, f x = true ↔ ∃ i ∈ S,
        (x i = true ∧ x (mate i) = true) ∨
        (p i ≠ i ∧ x i = true ∧ x (p i) = true)) ∧
      (∀ i j, (i ∈ S ∧ j ∈ S ∧ color i = color j ∧ f (pair i j) = true) ↔
        p i = j ∧ j ≠ i) := by
  classical
  let R : Fin n → Fin n → Prop := fun i j =>
    i ∈ S ∧ j ∈ S ∧ color i = color j ∧ f (pair i j) = true
  have hsym : ∀ {i j}, R i j → R j i := by
    intro i j h
    refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
    rw [pair_comm]
    exact h.2.2.2
  have hirr : ∀ i, ¬ R i i := by
    intro i h
    have hp : pair i i = single i := by funext j; simp [pair, single]
    have htrue := h.2.2.2
    rw [hp, hm.1 i] at htrue
    contradiction
  have hunique : ∀ i j l, R i j → R i l → j = l := by
    intro i j l h1 h2
    exact matched_same_color_matching hmi hcol hf hm i h1.1 j h1.2.1 l h2.2.1
      h1.2.2.1 h2.2.2.1 h1.2.2.2 h2.2.2.2
  obtain ⟨p, hpi, hp, hpu⟩ := relation_involution R hsym hirr hunique
  have hcolor : ∀ i, color (p i) = color i := by
    intro i
    by_cases he : p i = i
    · rw [he]
    · exact ((hp i (p i)).2 ⟨rfl, he⟩).2.2.1.symm
  have hmirror : ∀ i j, R i j → R (mate i) (mate j) := by
    intro i j h
    refine ⟨hm.2.1 i h.1, hm.2.1 j h.2.1, ?_, ?_⟩
    · exact bool_opposite_equal _ _ _ _ (hcol i) (hcol j) h.2.2.1
    · exact matched_mirror_true hf hm i h.1 j h.2.1 h.2.2.2
  have hcomm := relation_involution_commutes hp mate hmi hmirror
  have hout : ∀ i, i ∉ S → p i = i := by
    intro i hi
    by_contra he
    exact hi ((hp i (p i)).2 ⟨rfl, he⟩).1
  refine ⟨p, hpi, hcolor, hcomm, hout, ?_, hp⟩
  intro x
  constructor
  · intro hfx
    obtain ⟨i, hi, j, hj, hpair, hxi, hxj⟩ :=
      (pair_cover_quadratic hf hm.1 (matched_cover hm) x).1 hfx
    by_cases hc : color i = color j
    · have hrij : R i j := ⟨hi, hj, hc, hpair⟩
      obtain ⟨hpij, hji⟩ := (hp i j).1 hrij
      refine ⟨i, hi, Or.inr ⟨?_, hxi, ?_⟩⟩
      · simpa only [hpij] using hji
      · simpa only [hpij] using hxj
    · have hjm : j = mate i := by
        by_contra hne
        have hz := hm.2.2.2 i j hc hne
        rw [hz] at hpair
        contradiction
      exact ⟨i, hi, Or.inl ⟨hxi, hjm ▸ hxj⟩⟩
  · rintro ⟨i, hi, h | h⟩
    · exact ro_mono hf _ _ (pair_le h.1 h.2) (hm.2.2.1 i hi)
    · have hr := (hp i (p i)).2 ⟨rfl, h.1⟩
      exact ro_mono hf _ _ (pair_le h.2.1 h.2.2) hr.2.2.2

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
variable {k : ℕ}

abbrev row (i : Fin k) : Fin (k+k) := Fin.castAdd k i
abbrev col (i : Fin k) : Fin (k+k) := Fin.natAdd k i
def mate : Fin (k+k) → Fin (k+k) := Fin.append col row
def color : Fin (k+k) → Bool := Fin.append (fun _ => false) (fun _ => true)

@[simp] theorem mate_row (i : Fin k) : mate (row i) = col i := Fin.append_left _ _ i
@[simp] theorem mate_col (i : Fin k) : mate (col i) = row i := Fin.append_right _ _ i
@[simp] theorem color_row (i : Fin k) : color (row i) = false := Fin.append_left _ _ i
@[simp] theorem color_col (i : Fin k) : color (col i) = true := Fin.append_right _ _ i

theorem mate_involutive : Function.Involutive (mate (k := k)) := by
  intro i
  induction i using Fin.addCases with
  | left j => exact (congrArg mate (mate_row j)).trans (mate_col j)
  | right j => exact (congrArg mate (mate_col j)).trans (mate_row j)

theorem color_mate (i : Fin (k+k)) : color (mate i) ≠ color i := by
  induction i using Fin.addCases with
  | left j => change color (mate (row j)) ≠ color (row j); rw [mate_row, color_col, color_row]; decide
  | right j => change color (mate (col j)) ≠ color (col j); rw [mate_col, color_row, color_col]; decide

theorem row_injective : Function.Injective (row (k := k)) := Fin.castAdd_injective k k

theorem col_injective : Function.Injective (col (k := k)) := Fin.natAdd_injective k k

@[simp] theorem row_eq_iff (i j : Fin k) : row i = row j ↔ i = j := row_injective.eq_iff
@[simp] theorem col_eq_iff (i j : Fin k) : col i = col j ↔ i = j := col_injective.eq_iff

theorem perm_row (p : Equiv.Perm (Fin (k+k)))
    (hc : ∀ i, color (p i) = color i) (i : Fin k) : ∃ j, p (row i) = row j := by
  have hcolor := hc (row i)
  generalize he : p (row i) = v at *
  induction v using Fin.addCases with
  | left j => exact ⟨j, rfl⟩
  | right j =>
    rw [color_row] at hcolor
    change color (col j) = false at hcolor
    rw [color_col] at hcolor
    contradiction

def invFunction (p : Equiv.Perm (Fin k)) (x y : Fin k → Bool) : Bool :=
  decide (∃ i : Fin k,
    (x i = true ∧ y i = true) ∨
    (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
      (y i = true ∧ y (p i) = true))))

theorem ro_equality_normal_form (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_meta_33617.L853.R017.Matched mate color Finset.univ f) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  classical
  obtain ⟨p, hpi, hcol, hcomm, hout, hfn, hedge⟩ :=
    PEqualNP.Outside.L_meta_33617.L853.R017.matched_involution_normal_form mate_involutive color_mate hf hm
  choose q hq using perm_row p hcol
  have hqi : Function.Involutive q := by
    intro i
    apply row_injective
    rw [← hq (q i), ← hq i, hpi (row i)]
  let e : Equiv.Perm (Fin k) := hqi.toPerm q
  have hp_row : ∀ i, p (row i) = row (e i) := hq
  have hp_col : ∀ i, p (col i) = col (e i) := by
    intro i
    rw [← mate_row i, hcomm, hp_row, mate_row]
  have hnrow : ∀ i, p (row i) ≠ row i ↔ e i ≠ i := by
    intro i
    rw [hp_row]
    exact not_congr (row_injective.eq_iff)
  have hncol : ∀ i, p (col i) ≠ col i ↔ e i ≠ i := by
    intro i
    rw [hp_col]
    exact not_congr (col_injective.eq_iff)
  refine ⟨e, hqi, ?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  rw [hfn]
  simp only [invFunction, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    induction v using Fin.addCases with
    | left i =>
      rcases h with h | ⟨hn, h1, h2⟩
      · refine ⟨i, Or.inl ?_⟩
        simpa only [mate_row, Fin.append_left, Fin.append_right] using h
      · refine ⟨i, Or.inr ⟨(hnrow i).mp hn, Or.inl ⟨?_, ?_⟩⟩⟩
        · simpa only [Fin.append_left] using h1
        · simpa only [hp_row, Fin.append_left] using h2
    | right i =>
      rcases h with h | ⟨hn, h1, h2⟩
      · refine ⟨i, Or.inl ?_⟩
        simpa only [mate_col, Fin.append_left, Fin.append_right] using h.symm
      · refine ⟨i, Or.inr ⟨(hncol i).mp hn, Or.inr ⟨?_, ?_⟩⟩⟩
        · simpa only [Fin.append_right] using h1
        · simpa only [hp_col, Fin.append_right] using h2
  · rintro ⟨i, h | ⟨hn, h | h⟩⟩
    · refine ⟨row i, Finset.mem_univ _, Or.inl ?_⟩
      simpa only [mate_row, Fin.append_left, Fin.append_right] using h
    · refine ⟨row i, Finset.mem_univ _, Or.inr ⟨(hnrow i).mpr hn, ?_, ?_⟩⟩
      · simpa only [Fin.append_left] using h.1
      · simpa only [hp_row, Fin.append_left] using h.2
    · refine ⟨col i, Finset.mem_univ _, Or.inr ⟨(hncol i).mpr hn, ?_, ?_⟩⟩
      · simpa only [Fin.append_right] using h.1
      · simpa only [hp_col, Fin.append_right] using h.2

theorem invFunction_pair_test (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (i j : Fin k) :
    invFunction p (pair i j) (fun _ => false) = true ↔ p i = j ∧ j ≠ i := by
  simp only [invFunction, decide_eq_true_eq, Bool.false_eq_true, and_false, or_false, false_or,
    pair]
  constructor
  · rintro ⟨a, hn, ha, hpa⟩
    have ha' : a = i ∨ a = j := by simpa using ha
    have hpa' : p a = i ∨ p a = j := by simpa using hpa
    rcases ha' with hai | haj
    · subst a
      rcases hpa' with h | h
      · exact False.elim (hn h)
      · exact ⟨h, fun hji => hn (h.trans hji)⟩
    · subst a
      rcases hpa' with h | h
      · have hij : p i = j := by rw [← h, hp j]
        exact ⟨hij, fun hji => hn (h.trans hji.symm)⟩
      · exact False.elim (hn h)
  · rintro ⟨hij, hji⟩
    refine ⟨i, ?_, ?_, ?_⟩
    · exact fun h => hji (hij.symm.trans h)
    · simp
    · simp [hij]

theorem invFunction_injective (p q : Equiv.Perm (Fin k))
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (he : ∀ x y, invFunction p x y = invFunction q x y) : p = q := by
  have hr : ∀ i j, (p i = j ∧ j ≠ i) ↔ (q i = j ∧ j ≠ i) := by
    intro i j
    rw [← invFunction_pair_test p hp i j, ← invFunction_pair_test q hq i j, he]
  apply Equiv.ext
  intro i
  by_cases hn : p i = i
  · by_cases hnq : q i = i
    · exact hn.trans hnq.symm
    · have h := (hr i (q i)).2 ⟨rfl, hnq⟩
      exact False.elim (hnq (h.1.symm.trans hn))
  · exact ((hr i (p i)).1 ⟨rfl, hn⟩).1.symm

theorem ro_equality_unique_normal_form (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_meta_33617.L853.R017.Matched mate color Finset.univ f) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  obtain ⟨p, hp, he⟩ := ro_equality_normal_form f hf hm
  refine ⟨p, ⟨hp, he⟩, ?_⟩
  intro q hq
  apply invFunction_injective q p hq.1 hp
  intro x y
  exact (hq.2 x y).symm.trans (he x y)

end PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn

namespace PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
variable {k : ℕ}

theorem exists_other (hk : 2 ≤ k) (i : Fin k) : ∃ j : Fin k, j ≠ i := by
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  by_cases hi : i = z
  · refine ⟨o, ?_⟩
    intro h
    have hv := congrArg Fin.val (h.trans hi)
    change 1 = 0 at hv
    omega
  · exact ⟨z, Ne.symm hi⟩

theorem equality_matched (hk : 2 ≤ k) (f : (Fin (k+k) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hrep : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j)) :
    PEqualNP.Outside.L_meta_33617.L853.R017.Matched mate color Finset.univ f := by
  have hs : PEqualNP.Outside.L_meta_33617.L853.R017.NoSingle f := by
    intro v
    apply Bool.eq_false_iff.mpr
    intro htrue
    induction v using Fin.addCases with
    | left i =>
      obtain ⟨j, hji⟩ := exists_other hk i
      have hx := hmono (single (row i)) (pair (row i) (col j)) (by
        intro t ht
        have he : t = row i := by simpa [single] using ht
        simp [pair, he]) htrue
      rw [hrep, decide_eq_false (Ne.symm hji)] at hx
      contradiction
    | right i =>
      obtain ⟨j, hji⟩ := exists_other hk i
      have hx := hmono (single (col i)) (pair (row j) (col i)) (by
        intro t ht
        have he : t = col i := by simpa [single] using ht
        simp [pair, he]) htrue
      rw [hrep, decide_eq_false hji] at hx
      contradiction
  refine ⟨hs, by simp, ?_, ?_⟩
  · intro v hv
    induction v using Fin.addCases with
    | left i =>
      change f (pair (row i) (mate (row i))) = true
      rw [mate_row, hrep]
      simp
    | right i =>
      change f (pair (col i) (mate (col i))) = true
      rw [mate_col, pair_comm, hrep]
      simp
  · intro v w hc hne
    induction v using Fin.addCases with
    | left i =>
      induction w using Fin.addCases with
      | left j => exact False.elim (hc ((color_row i).trans (color_row j).symm))
      | right j =>
        change col j ≠ mate (row i) at hne
        rw [mate_row] at hne
        have hij : i ≠ j := fun h => hne (congrArg col h.symm)
        rw [hrep, decide_eq_false hij]
    | right i =>
      induction w using Fin.addCases with
      | left j =>
        change row j ≠ mate (col i) at hne
        rw [mate_col] at hne
        have hji : j ≠ i := fun h => hne (congrArg row h)
        rw [pair_comm, hrep, decide_eq_false hji]
      | right j => exact False.elim (hc ((color_col i).trans (color_col j).symm))

theorem equality_ro_classification (hk : 2 ≤ k) (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f)
    (hrep : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j)) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  exact ro_equality_unique_normal_form f hf (equality_matched hk f (ro_mono hf) hrep)

end PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn

namespace PEqualNP.Outside.L_meta_33617.L853.R017.CircuitForward

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
open PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn

theorem eval_gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi
    exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hi hv⟩

theorem wiresFrom_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' hl h; exact h
  | cons g gs ih =>
    intro w w' hl h i hi
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
      (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
      (w' ++ [g.op.eval (g.inputs.map fun a => w'.getD a false)]) (by simp [hl]) ?_ i hi
    intro j hj
    by_cases he : j = w.length
    · rw [he, getD_snoc_eq] at hj
      rw [he, hl, getD_snoc_eq]
      exact eval_gate_mono g (hm g List.mem_cons_self) w w' (fun a _ => h a) hj
    · rw [getD_snoc_ne _ _ _ _ he] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

theorem circuit_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true)
    (he : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  apply wiresFrom_mono C.gates (fun g hg => (hm g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output he
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = true := by simpa [hjn] using hj
    simpa [hjn] using h ⟨j, hjn⟩ hx
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

theorem ofFn_pair_row_col {k : ℕ} (i j : Fin k) :
    List.ofFn (pair (row i) (col j)) = oneEach i j := by
  have h : pair (row i) (col j) =
      Fin.append (single i) (single j) := by
    funext v
    induction v using Fin.addCases with
    | left t =>
      have hne : row t ≠ col j := by
        intro h
        have hval := congrArg (fun z : Fin (k+k) => z.val) h
        change t.val = k + j.val at hval
        omega
      simp only [pair, single, Fin.append_left]
      simp only [hne, or_false]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using row_injective.eq_iff)
    | right t =>
      have hne : col t ≠ row i := by
        intro h
        have hval := congrArg (fun z : Fin (k+k) => z.val) h
        change k + t.val = i.val at hval
        omega
      simp only [pair, single, Fin.append_right]
      simp only [hne, false_or]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using col_injective.eq_iff)
  rw [h, List.ofFn_fin_append]
  rfl

theorem equality_read_once {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
    (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
    (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
    RO Finset.univ (fun x : Fin (k+k) → Bool => C.eval (List.ofFn x)) := by
  let f : (Fin (k+k) → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have hrep' : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j) := by
    intro i j
    exact (congrArg C.eval (ofFn_pair_row_col i j)).trans (hrep i j)
  have hm' := equality_matched hk f (circuit_mono C hm) hrep'
  have hsens : ∀ i ∈ (Finset.univ : Finset (Fin (k+k))),
      ∃ x y : Fin (k+k) → Bool, (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD C.output false ≠
          (C.wires (List.ofFn y)).getD C.output false := by
    intro i hi
    refine ⟨pair i (mate i), single (mate i), ?_, ?_⟩
    · intro j hji
      simp [pair, single, hji]
    · change f (pair i (mate i)) ≠ f (single (mate i))
      rw [hm'.2.2.1 i hi, hm'.1 (mate i)]
      decide
  have hvalid : C.output < (k+k) + C.gates.length := by
    let z : Fin k := ⟨0, by omega⟩
    have ht := hrep' z z
    have ht' : (C.wires (List.ofFn (pair (row z) (col z)))).getD C.output false = true := by
      change f (pair (row z) (col z)) = true
      simpa only [decide_true] using ht
    by_contra hn
    have hl : (C.wires (List.ofFn (pair (row z) (col z)))).length = (k+k) + C.gates.length := by
      rw [wires_eq, length_wiresFrom]
      simp
    rw [List.getD_eq_default _ _ (by omega)] at ht'
    contradiction
  have hb := wire_essential_bound C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg => (hm g hg).2) Finset.univ hsens
  have hcard : (Finset.univ : Finset (Fin (k+k))).card = C.gates.length + 1 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hb ⊢
    change C.gates.length + 1 ≤ 2*k at hsize
    omega
  exact wire_read_once C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg => ⟨by have h := (hm g hg).1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto, (hm g hg).2⟩)
    Finset.univ hcard hsens

theorem equality_circuit_classification {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
    (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
    (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
  have h := equality_ro_classification hk
    (fun x : Fin (k+k) → Bool => C.eval (List.ofFn x))
    (equality_read_once hk C hm hsize hrep) (by
      intro i j
      rw [ofFn_pair_row_col]
      exact hrep i j)
  simpa only [List.ofFn_fin_append] using h

end PEqualNP.Outside.L_meta_33617.L853.R017.CircuitForward

namespace PEqualNP.Outside.L_meta_33617.L853.R017

 theorem official_forward : ∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) →
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := by
  intro k hk f h
  obtain ⟨C, hm, hs, hr, he⟩ := h
  obtain ⟨p, hp, hu⟩ := CircuitForward.equality_circuit_classification hk C hm hs hr
  refine ⟨p, ⟨hp.1, ?_⟩, ?_⟩
  · intro x y
    exact (he x y).trans (hp.2 x y)
  · intro q hq
    apply hu q
    refine ⟨hq.1, ?_⟩
    intro x y
    exact (he x y).symm.trans (hq.2 x y)

end PEqualNP.Outside.L_meta_33617.L853.R017

namespace PEqualNP.Outside.L_meta_33617.L853.R020.ROCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce

variable {n : ℕ}

def GateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Compiled (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ m : ℕ, n ≤ m → ∃ (gs : List Gate) (out : ℕ),
    (∀ g ∈ gs, GateOK g) ∧ gs.length + 1 = S.card ∧ out < m + gs.length ∧
    ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = f (fun i : Fin n => w.getD i.val false)

theorem compiled_leaf (i : Fin n) : Compiled {i} (fun x => x i) := by
  intro m hm
  refine ⟨[], i.val, ?_, by simp, ?_, ?_⟩
  · simp
  · have := i.isLt
    simp only [List.length_nil, Nat.add_zero]
    omega
  · intro w hw
    rfl

theorem compiled_join {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : Compiled A a) (hb : Compiled B b)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    Compiled (A ∪ B) (fun x => op.eval [a x, b x]) := by
  intro m hm
  obtain ⟨ga, oa, oka, lena, ra, eva⟩ := ha m hm
  obtain ⟨gb, ob, okb, lenb, rb, evb⟩ := hb (m + ga.length) (by omega)
  let M := m + ga.length + gb.length
  refine ⟨ga ++ gb ++ [⟨op, [oa, ob]⟩], M, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact oka g hg
    · exact okb g hg
    · subst g
      exact ⟨hop, by simp⟩
  · rw [Finset.card_union_of_disjoint hd]
    simp only [List.length_append, List.length_singleton]
    omega
  · simp only [List.length_append, List.length_singleton]
    dsimp [M]
    omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    let wa := wiresFrom ga w
    let wb := wiresFrom gb wa
    have hwa : wa.length = m + ga.length := by
      dsimp [wa]
      rw [length_wiresFrom, hw]
    have hwb : wb.length = M := by
      dsimp [wb]
      rw [length_wiresFrom, hwa]
    have eqa : wb.getD oa false = a (fun i : Fin n => w.getD i.val false) := by
      dsimp [wb]
      rw [getD_wiresFrom gb wa oa (by omega)]
      exact eva w hw
    have eqb : wb.getD ob false = b (fun i : Fin n => w.getD i.val false) := by
      dsimp [wb]
      rw [evb wa hwa]
      congr 1
      funext i
      exact getD_wiresFrom ga w i.val (by have := i.isLt; omega)
    change (wiresFrom [⟨op, [oa, ob]⟩] wb).getD M false = _
    change (wb ++ [op.eval [wb.getD oa false, wb.getD ob false]]).getD M false = _
    rw [← hwb, getD_snoc_eq, eqa, eqb]

theorem ro_compiled {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) : Compiled S f := by
  apply h Compiled compiled_leaf
  intro A B a b hd ha hb
  constructor
  · simpa only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq]
      using compiled_join hd ha hb GateOp.and (Or.inl rfl)
  · simpa only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      using compiled_join hd ha hb GateOp.or (Or.inr rfl)

theorem ro_circuit {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧ C.output < n + C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨gs, out, hok, hlen, hout, heval⟩ := ro_compiled h n (le_refl n)
  refine ⟨⟨gs, out⟩, ?_, hlen, hout, ?_⟩
  · intro g hg
    obtain ⟨ho, hl⟩ := hok g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
  · intro x
    change (wiresFrom gs (List.ofFn x)).getD out false = f x
    rw [heval (List.ofFn x) (by simp)]
    congr 1
    funext i
    simp

theorem ro_circuit_exists {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨C, hC, hsize, _, heval⟩ := ro_circuit h
  exact ⟨C, hC, hsize, heval⟩

end PEqualNP.Outside.L_meta_33617.L853.R020.ROCompiler

namespace PEqualNP.Outside.L_meta_33617.L853.R019.InvolutionRO

open PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn

variable {k : ℕ}

theorem row_ne_col (i j : Fin k) : row i ≠ col j := by
  intro h
  have e := congrArg (fun z : Fin (k+k) => z.val) h
  change i.val = k + j.val at e
  omega

theorem col_ne_row (i j : Fin k) : col i ≠ row j := (row_ne_col j i).symm

def supp (S : Finset (Fin k)) : Finset (Fin (k+k)) := S.image row ∪ S.image col

def clause (p : Equiv.Perm (Fin k)) (i : Fin k) (x : Fin (k+k) → Bool) : Prop :=
  (x (row i) = true ∧ x (col i) = true) ∨
  (p i ≠ i ∧ ((x (row i) = true ∧ x (row (p i)) = true) ∨
    (x (col i) = true ∧ x (col (p i)) = true)))

noncomputable def evalOn (p : Equiv.Perm (Fin k)) (S : Finset (Fin k))
    (x : Fin (k+k) → Bool) : Bool := by
  classical
  exact decide (∃ i ∈ S, clause p i x)

theorem supp_union (S T : Finset (Fin k)) : supp (S ∪ T) = supp S ∪ supp T := by
  classical
  ext i
  simp only [supp, Finset.mem_union, Finset.mem_image]
  aesop

theorem supp_disjoint {S T : Finset (Fin k)} (hd : Disjoint S T) :
    Disjoint (supp S) (supp T) := by
  classical
  rw [Finset.disjoint_left] at hd ⊢
  intro v hv hw
  simp only [supp, Finset.mem_union, Finset.mem_image] at hv hw
  rcases hv with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact hd hi ((row_injective he) ▸ hj)
    · exact col_ne_row j i he
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact row_ne_col j i he
    · exact hd hi ((col_injective he) ▸ hj)

theorem evalOn_union (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k)) :
    evalOn p (S ∪ T) = fun x => evalOn p S x || evalOn p T x := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [evalOn, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union]
  aesop

theorem fixed_ro (p : Equiv.Perm (Fin k)) (i : Fin k) (hi : p i = i) :
    RO (supp {i}) (evalOn p {i}) := by
  have hr := ro_and (by simpa using row_ne_col i i) (ro_leaf (row i)) (ro_leaf (col i))
  convert hr using 1
  · simp [supp]
  · funext x
    simp [evalOn, clause, hi]

theorem pair_ro (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (i j : Fin k) (hij : i ≠ j) (hpij : p i = j) :
    RO (supp {i,j}) (evalOn p {i,j}) := by
  have hpji : p j = i := by rw [← hpij, hp i]
  have hA := ro_or (by simpa using row_ne_col i j) (ro_leaf (row i)) (ro_leaf (col j))
  have hB := ro_or (by simpa using col_ne_row i j) (ro_leaf (col i)) (ro_leaf (row j))
  have hd : Disjoint (({row i} ∪ {col j}) : Finset (Fin (k+k))) ({col i} ∪ {row j}) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    simp only [Finset.mem_union, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl
    · rcases hw with he | he
      · exact row_ne_col i i he
      · exact hij (row_injective he)
    · rcases hw with he | he
      · exact hij.symm (col_injective he)
      · exact col_ne_row j j he
  have hr := ro_and hd hA hB
  convert hr using 1
  · ext v
    simp only [supp, Finset.image_insert, Finset.image_singleton, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [evalOn, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left, clause, hpij, hpji, Bool.and_eq_true, Bool.or_eq_true]
    tauto

theorem union_ro (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k))
    (hd : Disjoint S T) (hS : RO (supp S) (evalOn p S)) (hT : RO (supp T) (evalOn p T)) :
    RO (supp (S ∪ T)) (evalOn p (S ∪ T)) := by
  rw [supp_union, evalOn_union]
  exact ro_or (supp_disjoint hd) hS hT

theorem invariant_ro (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, p i ∈ S) (hne : S.Nonempty) :
    RO (supp S) (evalOn p S) := by
  classical
  revert hS hne
  refine Finset.strongInductionOn S ?_
  intro S ih hS hne
  obtain ⟨i, hi⟩ := hne
  by_cases hfix : p i = i
  · let T := S.erase i
    have ht : T ⊂ S := Finset.erase_ssubset hi
    have hclose : ∀ j ∈ T, p j ∈ T := by
      intro j hj
      have hjs := Finset.mem_erase.mp hj
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        apply hjs.1
        exact p.injective (he.trans hfix.symm)
      · exact hS j hjs.2
    have heq : S = {i} ∪ T := by simp [T, hi]
    by_cases hempty : T = ∅
    · rw [heq, hempty, Finset.union_empty]
      exact fixed_ro p i hfix
    · rw [heq]
      apply union_ro p {i} T
      · simp [T]
      · exact fixed_ro p i hfix
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
  · let j := p i
    have hij : i ≠ j := Ne.symm hfix
    have hj : j ∈ S := hS i hi
    have hpji : p j = i := hp i
    let T := (S.erase i).erase j
    have ht : T ⊂ S :=
      lt_of_le_of_lt (Finset.erase_subset j (S.erase i)) (Finset.erase_ssubset hi)
    have hclose : ∀ a ∈ T, p a ∈ T := by
      intro a ha
      have h := Finset.mem_erase.mp ha
      have h' := Finset.mem_erase.mp h.2
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        exact h'.1 (p.injective he)
      · apply Finset.mem_erase.mpr
        constructor
        · intro he
          exact h.1 (p.injective (he.trans hpji.symm))
        · exact hS a h'.2
    have heq : S = {i,j} ∪ T := by
      ext a
      simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase]
      constructor
      · intro ha
        by_cases hai : a = i
        · exact Or.inl (Or.inl hai)
        · by_cases haj : a = j
          · exact Or.inl (Or.inr haj)
          · exact Or.inr ⟨haj,hai,ha⟩
      · rintro ((rfl | rfl) | ⟨-, -, ha⟩)
        · exact hi
        · exact hj
        · exact ha
    by_cases hempty : T = ∅
    · rw [heq, hempty, Finset.union_empty]
      exact pair_ro p hp i j hij rfl
    · rw [heq]
      apply union_ro p {i,j} T
      · simp [T, Finset.disjoint_left]
      · exact pair_ro p hp i j hij rfl
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)

theorem involution_ro (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    RO Finset.univ (fun x : Fin (k+k) → Bool => invFunction p (fun i => x (row i))
      (fun i => x (col i))) := by
  have h := invariant_ro p hp Finset.univ (by simp) ⟨⟨0,hk⟩,Finset.mem_univ _⟩
  have hs : supp (Finset.univ : Finset (Fin k)) = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    induction v using Fin.addCases with
    | left i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    | right i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [hs] at h
  have he : evalOn p Finset.univ = (fun x : Fin (k+k) → Bool => invFunction p (fun i => x (row i)) (fun i => x (col i))) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [evalOn, clause, invFunction]
  rw [he] at h
  exact h

end PEqualNP.Outside.L_meta_33617.L853.R019.InvolutionRO

namespace PEqualNP.Outside.L_meta_33617.L853.R019.InverseBridge
open PEqualNP.Outside.L_meta_33617.L853.R017.RowColumn PEqualNP.Outside.L_meta_33617.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_33617.L853.R012.ReadOncePath
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem invFunction_oneEach {k : ℕ} (p : Equiv.Perm (Fin k)) (i j : Fin k) :
    invFunction p (single i) (single j) = decide (i = j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [invFunction, single, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨hai,haj⟩ | ⟨hne,h | h⟩⟩
    · exact hai.symm.trans haj
    · exact False.elim (hne (h.2.trans h.1.symm))
    · exact False.elim (hne (h.2.trans h.1.symm))
  · intro hij
    exact ⟨i,Or.inl ⟨rfl,hij⟩⟩

theorem involution_circuit_of_compiler
    (compileRO : ∀ {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool},
      RO S f → ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧
        ∀ x, C.eval (List.ofFn x) = f x)
    {k : ℕ} (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
      Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
  obtain ⟨C, hm, hs, he⟩ := compileRO (InvolutionRO.involution_ro hk p hp)
  have hfull : ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
    intro x y
    simpa only [List.ofFn_fin_append, Fin.append_left, Fin.append_right]
      using he (Fin.append x y)
  refine ⟨C,hm,?_,?_,hfull⟩
  · simp only [Finset.card_univ, Fintype.card_fin] at hs
    omega
  · intro i j
    change C.eval (List.ofFn (single i) ++ List.ofFn (single j)) = decide (i = j)
    rw [hfull, invFunction_oneEach]

end PEqualNP.Outside.L_meta_33617.L853.R019.InverseBridge

namespace PEqualNP.Outside.L_meta_33617.L853.R019

theorem official_full : ∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := by
  intro k hk f
  constructor
  · exact PEqualNP.Outside.L_meta_33617.L853.R017.official_forward k hk f
  · rintro ⟨p, ⟨hp, hf⟩, hu⟩
    obtain ⟨C, hm, hs, hr, he⟩ := InverseBridge.involution_circuit_of_compiler
      (fun h => PEqualNP.Outside.L_meta_33617.L853.R020.ROCompiler.ro_circuit_exists h) (by omega : 0 < k) p hp
    refine ⟨C, hm, hs, hr, ?_⟩
    intro x y
    exact (hf x y).trans (he x y).symm

end PEqualNP.Outside.L_meta_33617.L853.R019

namespace PEqualNP.Outside.L_meta_33617.CircuitReverse

open PEqualNP.Outside.L_meta_33617.L853
def invFunOf {k : ℕ} (p : Equiv.Perm (Fin k)) : (Fin k → Bool) → (Fin k → Bool) → Bool :=
  fun x y => decide (∃ i : Fin k,
    (x i = true ∧ y i = true) ∨
    (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true))))

theorem invFunOf_probe {k : ℕ} (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (a b : ℕ) (ha : a < k) (hb : b < k) (hab : a < b) :
    invFunOf p (fun i => decide (i.val = a ∨ i.val = b)) (fun _ => false) = true ↔
      p ⟨a, ha⟩ = ⟨b, hb⟩ := by
  simp only [invFunOf, decide_eq_true_eq, Bool.false_eq_true, and_false, or_false, false_or]
  constructor
  · rintro ⟨i, hne, hi, hpi⟩
    rcases hi with hia | hib
    · have hi' : i = ⟨a, ha⟩ := Fin.ext hia
      subst hi'
      rcases hpi with h1 | h2
      · exact absurd (Fin.ext h1) hne
      · exact Fin.ext h2
    · have hi' : i = ⟨b, hb⟩ := Fin.ext hib
      subst hi'
      rcases hpi with h1 | h2
      · have hpa : p ⟨b, hb⟩ = ⟨a, ha⟩ := Fin.ext h1
        have := congrArg p hpa
        rw [hp ⟨b, hb⟩] at this
        exact this.symm
      · exact absurd (Fin.ext h2) hne
  · intro h
    refine ⟨⟨a, ha⟩, ?_, Or.inl rfl, Or.inr ?_⟩
    · intro heq; rw [h] at heq; have := congrArg Fin.val heq; dsimp only at this; omega
    · rw [h]

theorem invFunOf_inj {k : ℕ} (hk : 2 ≤ k) {p q : Equiv.Perm (Fin k)}
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (heq : invFunOf p = invFunOf q) : p = q := by
  have hk0 : 0 < k := by omega
  obtain ⟨C, hm, hs, hr, he⟩ := L853.R019.InverseBridge.involution_circuit_of_compiler
    (fun h => L853.R020.ROCompiler.ro_circuit_exists h) hk0 p hp
  have hiff := (L853.R019.official_full k hk (invFunOf p)).mp
    ⟨C, hm, hs, hr, fun x y => (he x y).symm⟩
  obtain ⟨r, -, huniq⟩ := hiff
  have hp1 : p = r := huniq p ⟨hp, fun _ _ => rfl⟩
  have hq1 : q = r := huniq q ⟨hq, fun x y => congrFun (congrFun heq x) y⟩
  exact hp1.trans hq1.symm

abbrev Fn (n : Nat) := (Fin n → Bool) → (Fin n → Bool) → Bool

def CircuitOK {n : Nat} (f : Fn n) : Prop :=
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i =>
    ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))

@[simp] theorem mem_pairs {n : Nat} {e : Fin n × Fin n} :
    e ∈ pairs n ↔ e.1 < e.2 := by
  rcases e with ⟨a, b⟩
  simp [pairs]

theorem pairs_nodup (n : Nat) : (pairs n).Nodup := by
  rw [pairs, List.nodup_flatMap]
  constructor
  · intro a _
    exact ((List.nodup_finRange n).filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange n).pairwise_of_forall_ne
    intro a _ b _ hab e ha hb
    simp only [List.mem_map, List.mem_filter] at ha hb
    obtain ⟨j, _, rfl⟩ := ha
    obtain ⟨k, _, hk⟩ := hb
    exact hab (congrArg Prod.fst hk).symm

def ends {n : Nat} (e : Fin n × Fin n) : Finset (Fin n) := {e.1,e.2}
def obs {n : Nat} (f : Fn n) (A B : Finset (Fin n)) : Bool :=
  f (fun i => decide (i ∈ A)) (fun i => decide (i ∈ B))
def hit {n : Nat} (f : Fn n) (e : Fin n × Fin n) : Bool :=
  f (fun i => decide (i = e.1 ∨ i = e.2)) (fun _ => false)

theorem hit_eq_obs {n : Nat} (f : Fn n) (e : Fin n × Fin n) :
    hit f e = obs f (ends e) ∅ := by simp [hit, obs, ends]

theorem hit_invFunOf {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) {e : Fin n × Fin n} (he : e.1 < e.2) :
    hit (invFunOf p) e = decide (p e.1 = e.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, hit]
  simpa only [Fin.val_inj, Fin.eta] using
    invFunOf_probe p hp e.1.val e.2.val e.1.isLt e.2.isLt he

def selected {n : Nat} (p : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  ((pairs n).filter (fun e => decide (p e.1 = e.2))).toFinset

@[simp] theorem mem_selected {n : Nat} {p : Equiv.Perm (Fin n)}
    {e : Fin n × Fin n} : e ∈ selected p ↔ e.1 < e.2 ∧ p e.1 = e.2 := by
  simp [selected]

theorem obs_invFunOf {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) (A B : Finset (Fin n)) :
    obs (invFunOf p) A B = true ↔
      ¬ Disjoint A B ∨ ∃ e ∈ selected p, ends e ⊆ A ∨ ends e ⊆ B := by
  simp only [obs, invFunOf, decide_eq_true_eq]
  have hmk (i j : Fin n) (h : p i = j) (hn : j ≠ i) (D : Finset (Fin n))
      (hi : i ∈ D) (hj : j ∈ D) :
      ∃ e ∈ selected p, ends e ⊆ D := by
    rcases lt_or_gt_of_ne hn with hl | hl
    · refine ⟨(j,i), mem_selected.mpr ⟨hl, ?_⟩, ?_⟩
      · rw [← h, hp]
      · simp [ends, Finset.insert_subset_iff, hj, hi]
    · exact ⟨(i,j), mem_selected.mpr ⟨hl,h⟩, by simp [ends, Finset.insert_subset_iff, hi, hj]⟩
  constructor
  · rintro ⟨i, h | ⟨hn, h | h⟩⟩
    · exact Or.inl (fun hd => (Finset.disjoint_left.mp hd h.1 h.2))
    · obtain ⟨e, he, hD⟩ := hmk i (p i) rfl hn A h.1 h.2
      exact Or.inr ⟨e, he, Or.inl hD⟩
    · obtain ⟨e, he, hD⟩ := hmk i (p i) rfl hn B h.1 h.2
      exact Or.inr ⟨e, he, Or.inr hD⟩
  · rintro (hd | ⟨e, he, h | h⟩)
    · have hx : ∃ i ∈ A, i ∈ B := by
        by_contra hn
        exact hd (Finset.disjoint_left.mpr fun i hi hj => hn ⟨i,hi,hj⟩)
      obtain ⟨i, hi, hj⟩ := hx
      exact ⟨i, Or.inl ⟨hi,hj⟩⟩
    · obtain ⟨hlt, hpq⟩ := mem_selected.mp he
      exact ⟨e.1, Or.inr ⟨by rw [hpq]; exact ne_of_gt hlt,
        Or.inl ⟨h (by simp [ends]), by rw [hpq]; exact h (by simp [ends])⟩⟩⟩
    · obtain ⟨hlt, hpq⟩ := mem_selected.mp he
      exact ⟨e.1, Or.inr ⟨by rw [hpq]; exact ne_of_gt hlt,
        Or.inr ⟨h (by simp [ends]), by rw [hpq]; exact h (by simp [ends])⟩⟩⟩

def Matching {n : Nat} (S : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ S, e.1 < e.2) ∧
    ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f)

private theorem selected_partner {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) {e : Fin n × Fin n} (he : e ∈ selected p)
    {i : Fin n} (hi : i ∈ ends e) :
    p i ≠ i ∧ e = (min i (p i), max i (p i)) := by
  obtain ⟨hlt, heq⟩ := mem_selected.mp he
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · rw [heq, min_eq_left hlt.le, max_eq_right hlt.le]
    exact ⟨hlt.ne', Prod.ext rfl rfl⟩
  · have hr : p e.2 = e.1 := by rw [← heq, hp]
    rw [hr, min_eq_right hlt.le, max_eq_left hlt.le]
    exact ⟨hlt.ne, Prod.ext rfl rfl⟩

theorem matching_selected {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) : Matching (selected p) := by
  refine ⟨fun _ h => (mem_selected.mp h).1, ?_⟩
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hne ((selected_partner hp he hi).2.trans (selected_partner hp hf hj).2.symm)

theorem existsUnique_selected {n : Nat} {S : Finset (Fin n × Fin n)}
    (hS : Matching S) :
    ∃! p : Equiv.Perm (Fin n), Function.Involutive p ∧ selected p = S := by
  classical
  let J (a b : Fin n) : Prop := a ≠ b ∧ (min a b, max a b) ∈ S
  have hsym {a b : Fin n} (h : J a b) : J b a := by
    exact ⟨h.1.symm, by simpa only [min_comm b a, max_comm b a] using h.2⟩
  have hj {a b : Fin n} (h : J a b) : a ∈ ends (min a b, max a b) := by
    rcases le_total a b with hl | hl
    · simp [ends, min_eq_left hl]
    · simp [ends, max_eq_left hl]
  have hu (a b c : Fin n) (hb : J a b) (hc : J a c) : b = c := by
    have he : (min a b,max a b) = (min a c,max a c) := by
      by_contra hn
      exact Finset.disjoint_left.mp (hS.2 _ hb.2 _ hc.2 hn) (hj hb) (hj hc)
    have hbc : b ∈ ends (min a c,max a c) := by
      rw [← he]
      simpa only [min_comm b a, max_comm b a] using hj (hsym hb)
    rcases le_total a c with hl | hl
    · simpa [ends, min_eq_left hl, max_eq_right hl, hb.1.symm] using hbc
    · simpa [ends, min_eq_right hl, max_eq_left hl, hb.1.symm] using hbc
  obtain ⟨p,hp,hiff,huniq⟩ := L853.R017.relation_involution J
    (fun h => hsym h) (fun _ h => h.1 rfl) hu
  have uniqueRel (q : Equiv.Perm (Fin n)) (hq : Function.Involutive q) :
      selected q = S ↔ ∀ a b, J a b ↔ q a = b ∧ b ≠ a := by
    constructor
    · intro hqS a b
      have go (x y : Fin n) (hlt : x < y) :
          J x y ↔ q x = y ∧ y ≠ x := by
        simp [J, min_eq_left hlt.le, max_eq_right hlt.le, ← hqS, hlt, hlt.ne, hlt.ne']
      rcases lt_trichotomy a b with hl | rfl | hl
      · exact go a b hl
      · simp [J]
      · have hswap : q b = a ↔ q a = b := ⟨fun h => by rw [← h, hq],
            fun h => by rw [← h, hq]⟩
        exact (⟨hsym, hsym⟩ : J a b ↔ J b a).trans
          ((go b a hl).trans (by simp [hswap, hl.ne, hl.ne']))
    · intro hr
      ext e
      constructor
      · intro he
        obtain ⟨hlt,hqeq⟩ := mem_selected.mp he
        have hm := ((hr e.1 e.2).mpr ⟨hqeq,hlt.ne'⟩).2
        simpa [min_eq_left hlt.le,max_eq_right hlt.le] using hm
      · intro he
        have hlt := hS.1 e he
        exact mem_selected.mpr ⟨hlt, ((hr e.1 e.2).mp ⟨hlt.ne,
          by simpa [min_eq_left hlt.le,max_eq_right hlt.le] using he⟩).1⟩
  exact ⟨p, ⟨hp,(uniqueRel p hp).mpr hiff⟩, fun q hq =>
    huniq q ((uniqueRel q hq.1).mp hq.2)⟩

def allowed {n : Nat} (hard : List (Finset (Fin n) × Finset (Fin n))) :
    Finset (Fin n × Fin n) :=
  (pairs n).toFinset.filter (fun e =>
    ∀ z ∈ hard, ¬ ends e ⊆ z.1 ∧ ¬ ends e ⊆ z.2)

def Valid {n : Nat} (hard : List (Finset (Fin n) × Finset (Fin n))) (f : Fn n) :
    Prop := CircuitOK f ∧ ∀ z ∈ hard, obs f z.1 z.2 = false

theorem circuit_iff {n : Nat} (hn : 2 ≤ n) (f : Fn n) :
    CircuitOK f ↔ ∃! p : Equiv.Perm (Fin n), Function.Involutive p ∧ f = invFunOf p := by
  apply (L853.R019.official_full n hn f).trans
  apply existsUnique_congr
  intro p
  exact and_congr_right (fun _ => ⟨fun h => funext fun x => funext (h x),
    fun h x y => by rw [h]; rfl⟩)

theorem valid_invFunOf {n : Nat} (hn : 2 ≤ n)
    (hard : List (Finset (Fin n) × Finset (Fin n))) {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) :
    Valid hard (invFunOf p) ↔
      (∀ z ∈ hard, Disjoint z.1 z.2) ∧ selected p ⊆ allowed hard := by
  have hC : CircuitOK (invFunOf p) :=
    (circuit_iff hn _).mpr ⟨p,⟨hp,rfl⟩,fun q hq => invFunOf_inj hn hq.1 hp hq.2.symm⟩
  constructor
  · intro h
    have no (z : Finset (Fin n) × Finset (Fin n)) (hz : z ∈ hard) :
        ¬ (¬ Disjoint z.1 z.2 ∨ ∃ e ∈ selected p, ends e ⊆ z.1 ∨ ends e ⊆ z.2) := by
      intro hh
      have ht := (obs_invFunOf hp z.1 z.2).mpr hh
      rw [h.2 z hz] at ht
      contradiction
    refine ⟨fun z hz => not_not.mp (fun hh => no z hz (Or.inl hh)), ?_⟩
    intro e he
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (mem_pairs.mpr (mem_selected.mp he).1), ?_⟩
    exact fun z hz => ⟨fun hh => no z hz (Or.inr ⟨e,he,Or.inl hh⟩),
      fun hh => no z hz (Or.inr ⟨e,he,Or.inr hh⟩)⟩
  · rintro ⟨hd, hs⟩
    refine ⟨hC, fun z hz => ?_⟩
    apply Bool.eq_false_iff.mpr
    intro ht
    have ht' := (obs_invFunOf hp _ _).mp ht
    revert ht'
    rintro (h | ⟨e,he,h | h⟩)
    · exact h (hd z hz)
    · exact ((Finset.mem_filter.mp (hs he)).2 z hz).1 h
    · exact ((Finset.mem_filter.mp (hs he)).2 z hz).2 h

/-- Graph of the bijection between valid functions and the admissible Fin-endpoint matchings.
Hard-bank overlap makes the target empty as well as the domain. -/
def Corresponds {n : Nat} (f : Fn n) (S : Finset (Fin n × Fin n)) : Prop :=
  ∃ p : Equiv.Perm (Fin n), Function.Involutive p ∧ f = invFunOf p ∧ selected p = S

theorem valid_matching_unique {n : Nat} (hn : 2 ≤ n)
    {hard : List (Finset (Fin n) × Finset (Fin n))} {f : Fn n} (hf : Valid hard f) :
    (∀ z ∈ hard, Disjoint z.1 z.2) ∧
    ∃! S, Matching S ∧ S ⊆ allowed hard ∧ Corresponds f S := by
  obtain ⟨p,⟨hp,rfl⟩,hu⟩ := (circuit_iff hn f).mp hf.1
  obtain ⟨hd,he⟩ := (valid_invFunOf hn hard hp).mp hf
  refine ⟨hd, selected p, ⟨matching_selected hp, he, p,hp,rfl,rfl⟩, ?_⟩
  rintro S ⟨_,_,q,hq,hf,hS⟩
  rw [hu q ⟨hq,hf⟩] at hS
  exact hS.symm

theorem matching_valid_unique {n : Nat} (hn : 2 ≤ n)
    {hard : List (Finset (Fin n) × Finset (Fin n))}
    (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    {S : Finset (Fin n × Fin n)} (hS : Matching S) (he : S ⊆ allowed hard) :
    ∃! f, Valid hard f ∧ Corresponds f S := by
  obtain ⟨p,⟨hp,hsp⟩,hu⟩ := existsUnique_selected hS
  refine ⟨invFunOf p, ⟨(valid_invFunOf hn hard hp).mpr ⟨hd,hsp ▸ he⟩,
      p,hp,rfl,hsp⟩, ?_⟩
  rintro f ⟨_,q,hq,rfl,hsq⟩
  rw [hu q ⟨hq,hsq⟩]

theorem corresponds_obs {n : Nat} {f : Fn n} {S : Finset (Fin n × Fin n)}
    (h : Corresponds f S) (A B : Finset (Fin n)) :
    obs f A B = true ↔ ¬ Disjoint A B ∨ ∃ e ∈ S, ends e ⊆ A ∨ ends e ⊆ B := by
  obtain ⟨p,hp,rfl,rfl⟩ := h
  exact obs_invFunOf hp A B

theorem corresponds_hit {n : Nat} {f : Fn n} {S : Finset (Fin n × Fin n)}
    (h : Corresponds f S) {e : Fin n × Fin n} (he : e ∈ pairs n) :
    obs f (ends e) ∅ = decide (e ∈ S) := by
  obtain ⟨p,hp,rfl,rfl⟩ := h
  rw [← hit_eq_obs, hit_invFunOf hp (mem_pairs.mp he)]
  apply Bool.eq_iff_iff.mpr
  simp [mem_pairs.mp he]

theorem selected_of_moved {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) {i : Fin n} (hi : p i ≠ i) :
    (min i (p i), max i (p i)) ∈ selected p := by
  rcases lt_or_gt_of_ne hi with h | h
  · simpa [min_eq_right h.le, max_eq_left h.le, mem_selected, h] using hp i
  · simp [min_eq_left h.le, max_eq_right h.le, mem_selected, h]

theorem full_selected_iff {n : Nat} {p : Equiv.Perm (Fin n)}
    (hp : Function.Involutive p) :
    2 * (selected p).card = n ↔ ∀ i, p i ≠ i := by
  let S := selected p
  let U := S.image Prod.fst ∪ S.image Prod.snd
  have hcard : U.card = 2 * S.card := by
    have hfst : Set.InjOn (Prod.fst : Fin n × Fin n → Fin n) (↑S : Set _) := by
      intro e he f hf h
      exact Prod.ext h (((mem_selected.mp he).2.symm.trans
        (congrArg p h)).trans (mem_selected.mp hf).2)
    have hsnd : Set.InjOn (Prod.snd : Fin n × Fin n → Fin n) (↑S : Set _) := by
      intro e he f hf h
      exact Prod.ext (p.injective (((mem_selected.mp he).2.trans h).trans
        (mem_selected.mp hf).2.symm)) h
    have hd : Disjoint (S.image Prod.fst) (S.image Prod.snd) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hi
      obtain ⟨f,hf,hfq⟩ := Finset.mem_image.mp hj
      have eq := (selected_partner hp he (show i ∈ ends e by simp [ends, heq])).2.trans
        (selected_partner hp hf (show i ∈ ends f by simp [ends, hfq])).2.symm
      subst f
      exact (mem_selected.mp he).1.ne (heq.trans hfq.symm)
    dsimp only [U]
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hfst,
      Finset.card_image_of_injOn hsnd, two_mul]
  have hm (i : Fin n) : i ∈ U ↔ p i ≠ i := by
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
        exact (selected_partner hp he (by simp [ends])).1
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
        exact (selected_partner hp he (by simp [ends])).1
    · intro hi
      have he := selected_of_moved hp hi
      rcases le_total i (p i) with hl | hl
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨_,he,min_eq_left hl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨_,he,max_eq_left hl⟩
  change 2 * S.card = n ↔ _
  rw [← hcard]
  constructor
  · intro hc i
    have hu : U = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [hc])
    exact (hm i).mp (by simp [hu])
  · intro hh
    have hu : U = Finset.univ := Finset.eq_univ_of_forall fun i => (hm i).mpr (hh i)
    simp [hu]

def Perfect (v : Nat) (G : Fin v → Fin v → Bool) (p : Equiv.Perm (Fin v)) : Prop :=
  Function.Involutive p ∧ ∀ i, p i ≠ i ∧ G (min i (p i)) (max i (p i)) = true

def vals {n : Nat} (e : Fin n × Fin n) : Nat × Nat := (e.1.val,e.2.val)
def oldEdges {v : Nat} (G : Fin v → Fin v → Bool) : List (Nat × Nat) :=
  ((pairs v).filter (fun e => G e.1 e.2)).map vals
def reds {v : Nat} (G R : Fin v → Fin v → Bool) : List (Nat × Nat) :=
  ((pairs v).filter (fun e => G e.1 e.2 && R e.1 e.2)).map vals
def bans {v : Nat} (G : Fin v → Fin v → Bool) : List (Fin (v+2) × Fin (v+2)) :=
  (pairs (v+2)).filter fun e => decide (vals e ∉ (v,v+1) :: oldEdges G)
def probes {v : Nat} (G R : Fin v → Fin v → Bool) : List (Fin (v+2) × Fin (v+2)) :=
  (pairs (v+2)).filter fun e => decide (vals e ∈ reds G R)

def ReverseOK {h : Nat} (G : Fin (2*h) → Fin (2*h) → Bool) (f : Fn (2*h+2)) : Prop :=
  CircuitOK f ∧ (∀ e ∈ bans G, hit f e = false) ∧
    ((pairs (2*h+2)).filter (hit f)).length = h+1

private def incl {v : Nat} (i : Fin v) : Fin (v+2) := ⟨i.val, by omega⟩
private def leftPad (v : Nat) : Fin (v+2) := ⟨v, by omega⟩
private def rightPad (v : Nat) : Fin (v+2) := ⟨v+1, by omega⟩
private def liftEdge {v : Nat} (e : Fin v × Fin v) : Fin (v+2) × Fin (v+2) :=
  (incl e.1,incl e.2)

private theorem incl_inj {v : Nat} : Function.Injective (@incl v) :=
  fun _ _ h => Fin.ext (congrArg (fun i : Fin (v+2) => i.val) h)

private theorem liftEdge_inj {v : Nat} : Function.Injective (@liftEdge v) :=
  fun _ _ h => Prod.ext (incl_inj (congrArg Prod.fst h)) (incl_inj (congrArg Prod.snd h))

private theorem vals_inj {v : Nat} : Function.Injective (@vals v) :=
  fun _ _ h => Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

private theorem liftEdge_order {v : Nat} (e : Fin v × Fin v) :
    (liftEdge e).1 < (liftEdge e).2 ↔ e.1 < e.2 := Iff.rfl

private theorem pad_cases {v : Nat} (i : Fin (v+2)) :
    (∃ a : Fin v, i = incl a) ∨ i = leftPad v ∨ i = rightPad v := by
  by_cases h : i.val < v
  · exact Or.inl ⟨⟨i.val,h⟩,rfl⟩
  · have hi := i.isLt
    by_cases e : i.val = v
    · exact Or.inr (Or.inl (Fin.ext e))
    · exact Or.inr (Or.inr (Fin.ext (by change i.val = v+1; omega)))

private theorem edge_allowed {v : Nat} {G : Fin v → Fin v → Bool}
    {e : Fin (v+2) × Fin (v+2)} (he : e.1 < e.2) :
    e ∉ bans G ↔
      e = (leftPad v,rightPad v) ∨
        ∃ a : Fin v × Fin v, a.1 < a.2 ∧ G a.1 a.2 = true ∧ e = liftEdge a := by
  classical
  simp only [bans, List.mem_filter, mem_pairs, he, true_and, decide_eq_true_eq, not_not,
    List.mem_cons, oldEdges, List.mem_map]
  apply or_congr
  · exact ⟨fun h => vals_inj h, fun h => congrArg vals h⟩
  · constructor
    · rintro ⟨a,ha,eq⟩
      exact ⟨a,ha.1,ha.2,vals_inj eq.symm⟩
    · rintro ⟨a,ha,hG,rfl⟩
      exact ⟨a,⟨ha,hG⟩,rfl⟩

private theorem probe_iff {v : Nat} {G R : Fin v → Fin v → Bool}
    {e : Fin (v+2) × Fin (v+2)} :
    e ∈ probes G R ↔
      ∃ a : Fin v × Fin v, a.1 < a.2 ∧ G a.1 a.2 = true ∧ R a.1 a.2 = true ∧
        e = liftEdge a := by
  simp only [probes, List.mem_filter, mem_pairs, decide_eq_true_eq, reds, List.mem_map,
    Bool.and_eq_true]
  constructor
  · rintro ⟨_,a,⟨ha,hG,hR⟩,eq⟩
    exact ⟨a,ha,hG,hR,vals_inj eq.symm⟩
  · rintro ⟨a,ha,hG,hR,rfl⟩
    exact ⟨(liftEdge_order a).mpr ha,a,⟨ha,hG,hR⟩,rfl⟩

private def Padded {v : Nat} (G : Fin v → Fin v → Bool) (p : Equiv.Perm (Fin (v+2))) :
    Prop :=
  Function.Involutive p ∧ (∀ i, p i ≠ i) ∧ ∀ e ∈ selected p, e ∉ bans G

private theorem padded_inc {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) (i : Fin (v+2)) :
    (min i (q i), max i (q i)) = (leftPad v,rightPad v) ∨
      ∃ a : Fin v × Fin v, a.1 < a.2 ∧ G a.1 a.2 = true ∧
        (min i (q i), max i (q i)) = liftEdge a := by
  have he := selected_of_moved hq.1 (hq.2.1 i)
  exact (edge_allowed (mem_selected.mp he).1).mp (hq.2.2 _ he)

private theorem endpoints_sorted {n : Nat} (a b : Fin n) :
    a ∈ ends (min a b,max a b) ∧ b ∈ ends (min a b,max a b) := by
  rcases le_total a b with h | h
  · simp [ends, min_eq_left h, max_eq_right h]
  · simp [ends, min_eq_right h, max_eq_left h]

private theorem not_pad_old {v : Nat} (i : Fin v) :
    incl i ≠ leftPad v ∧ incl i ≠ rightPad v := by
  have hi := i.isLt
  constructor <;> intro h <;>
    have hh := congrArg (fun i : Fin (v+2) => i.val) h
  · change i.val = v at hh
    omega
  · change i.val = v+1 at hh
    omega

private theorem restrict_bound {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) (i : Fin v) :
    (q (incl i)).val < v := by
  obtain ⟨hi,hq'⟩ := endpoints_sorted (incl i) (q (incl i))
  rcases padded_inc hq (incl i) with h | ⟨a,_,_,h⟩
  · rw [h] at hi
    rcases (show incl i = leftPad v ∨ incl i = rightPad v by simpa [ends] using hi) with h | h
    · exact ((not_pad_old i).1 h).elim
    · exact ((not_pad_old i).2 h).elim
  · rw [h] at hq'
    rcases (show q (incl i) = incl a.1 ∨ q (incl i) = incl a.2 by
      simpa [ends, liftEdge] using hq') with h | h
    · rw [h]
      exact a.1.isLt
    · rw [h]
      exact a.2.isLt

private theorem padded_swap {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) :
    q (leftPad v) = rightPad v ∧ q (rightPad v) = leftPad v := by
  have hh : q (leftPad v) = rightPad v := by
    obtain ⟨hi,hq'⟩ := endpoints_sorted (leftPad v) (q (leftPad v))
    rcases padded_inc hq (leftPad v) with h | ⟨a,_,_,h⟩
    · rw [h] at hq'
      simpa [ends, hq.2.1 (leftPad v)] using hq'
    · rw [h] at hi
      rcases (show leftPad v = incl a.1 ∨ leftPad v = incl a.2 by
        simpa [ends, liftEdge] using hi) with h | h
      · exact ((not_pad_old a.1).1 h.symm).elim
      · exact ((not_pad_old a.2).1 h.symm).elim
  exact ⟨hh, by rw [← hh, hq.1]⟩

private def restrictFn {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) (i : Fin v) : Fin v :=
  ⟨(q (incl i)).val, restrict_bound hq i⟩

private theorem incl_restrict {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) (i : Fin v) :
    incl (restrictFn hq i) = q (incl i) := Fin.ext rfl

private theorem incl_min {v : Nat} (a b : Fin v) :
    incl (min a b) = min (incl a) (incl b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (show incl a ≤ incl b from h)]
  · rw [min_eq_right h, min_eq_right (show incl b ≤ incl a from h)]

private theorem incl_max {v : Nat} (a b : Fin v) :
    incl (max a b) = max (incl a) (incl b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (show incl a ≤ incl b from h)]
  · rw [max_eq_left h, max_eq_left (show incl b ≤ incl a from h)]

private def restrictPerm {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) : Equiv.Perm (Fin v) :=
  (show Function.Involutive (restrictFn hq) from fun i => incl_inj (by
    rw [incl_restrict, incl_restrict, hq.1])).toPerm _

private theorem restrict_perfect {v : Nat} {G : Fin v → Fin v → Bool}
    {q : Equiv.Perm (Fin (v+2))} (hq : Padded G q) : Perfect v G (restrictPerm hq) := by
  constructor
  · intro i
    change restrictFn hq (restrictFn hq i) = i
    exact incl_inj (by rw [incl_restrict, incl_restrict, hq.1])
  · intro i
    change restrictFn hq i ≠ i ∧ G (min i (restrictFn hq i)) (max i (restrictFn hq i)) = true
    refine ⟨fun he => hq.2.1 (incl i) ((incl_restrict hq i).symm.trans (congrArg incl he)), ?_⟩
    have h := padded_inc hq (incl i)
    rw [← incl_restrict hq i, ← incl_min, ← incl_max] at h
    rcases h with h | ⟨a,_,hG,he⟩
    · have hv := congrArg (fun e => (e : Fin (v+2) × Fin (v+2)).1.val) h
      have hm := (min i (restrictFn hq i)).isLt
      change (min i (restrictFn hq i)).val = v at hv
      omega
    · have he' : (min i (restrictFn hq i),max i (restrictFn hq i)) = a := liftEdge_inj he
      exact congrArg (fun e : Fin v × Fin v => G e.1 e.2) he' |>.trans hG

private def extendFn {v : Nat} (p : Equiv.Perm (Fin v)) (i : Fin (v+2)) : Fin (v+2) :=
  if h : i.val < v then incl (p ⟨i.val,h⟩)
  else if i = leftPad v then rightPad v else leftPad v

@[simp] private theorem extend_incl {v : Nat} (p : Equiv.Perm (Fin v)) (i : Fin v) :
    extendFn p (incl i) = incl (p i) := by simp [extendFn, incl, i.isLt]

@[simp] private theorem extend_left {v : Nat} (p : Equiv.Perm (Fin v)) :
    extendFn p (leftPad v) = rightPad v := by simp [extendFn, leftPad]

@[simp] private theorem extend_right {v : Nat} (p : Equiv.Perm (Fin v)) :
    extendFn p (rightPad v) = leftPad v := by
  have h : rightPad v ≠ leftPad v := fun h => by
    have hh := congrArg Fin.val h
    change v+1 = v at hh
    omega
  have hh : ¬ (rightPad v).val < v := by change ¬ v+1 < v; omega
  simp [extendFn, h, hh]

private def extendPerm {v : Nat} {p : Equiv.Perm (Fin v)} (hp : Function.Involutive p) :
    Equiv.Perm (Fin (v+2)) :=
  (show Function.Involutive (extendFn p) from fun i => by
    rcases pad_cases i with ⟨a,rfl⟩ | rfl | rfl
    · simp [hp a]
    · simp
    · simp).toPerm _

private theorem extend_padded {v : Nat} {G : Fin v → Fin v → Bool}
    {p : Equiv.Perm (Fin v)} (hp : Perfect v G p) : Padded G (extendPerm hp.1) := by
  have hI : Function.Involutive (extendPerm hp.1) := by
    intro i
    change extendFn p (extendFn p i) = i
    rcases pad_cases i with ⟨a,rfl⟩ | rfl | rfl
    · simp [hp.1 a]
    · simp
    · simp
  have hn (i : Fin (v+2)) : extendPerm hp.1 i ≠ i := by
    change extendFn p i ≠ i
    rcases pad_cases i with ⟨a,rfl⟩ | rfl | rfl
    · rw [extend_incl]
      exact fun h => (hp.2 a).1 (incl_inj h)
    · rw [extend_left]
      intro h
      have hv := congrArg Fin.val h
      change v+1 = v at hv
      omega
    · rw [extend_right]
      intro h
      have hv := congrArg Fin.val h
      change v = v+1 at hv
      omega
  refine ⟨hI, hn, fun e he => ?_⟩
  apply (edge_allowed (mem_selected.mp he).1).mpr
  have heq := (selected_partner hI he (show e.1 ∈ ends e by simp [ends])).2
  let i := e.1
  change e = (min i (extendFn p i),max i (extendFn p i)) at heq
  have hl : leftPad v < rightPad v := by change v < v+1; omega
  rcases pad_cases i with ⟨a,ha⟩ | ha | ha
  · rw [ha, extend_incl, ← incl_min, ← incl_max] at heq
    refine Or.inr ⟨(min a (p a),max a (p a)), ?_, (hp.2 a).2, heq⟩
    exact (mem_selected.mp (selected_of_moved hp.1 (hp.2 a).1)).1
  · left
    simpa only [ha, extend_left, min_eq_left hl.le, max_eq_right hl.le] using heq
  · left
    simpa only [ha, extend_right, min_eq_right hl.le, max_eq_left hl.le] using heq

private def paddedEquiv {v : Nat} (G : Fin v → Fin v → Bool) :
    {p : Equiv.Perm (Fin v) // Perfect v G p} ≃
      {q : Equiv.Perm (Fin (v+2)) // Padded G q} where
  toFun p := ⟨extendPerm p.2.1, extend_padded p.2⟩
  invFun q := ⟨restrictPerm q.2, restrict_perfect q.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply incl_inj
    change incl (restrictFn (extend_padded p.2) i) = incl (p.val i)
    rw [incl_restrict]
    exact extend_incl p.val i
  right_inv q := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change extendFn (restrictPerm q.2) i = q.val i
    rcases pad_cases i with ⟨a,rfl⟩ | rfl | rfl
    · rw [extend_incl]
      exact incl_restrict q.2 a
    · rw [extend_left, (padded_swap q.2).1]
    · rw [extend_right, (padded_swap q.2).2]

private theorem reverse_inv_iff {h : Nat} {G : Fin (2*h) → Fin (2*h) → Bool}
    {q : Equiv.Perm (Fin (2*h+2))} (hq : Function.Involutive q) :
    ReverseOK G (invFunOf q) ↔ Padded G q := by
  have hn : 2 ≤ 2*h+2 := by omega
  have hc : CircuitOK (invFunOf q) :=
    (circuit_iff hn _).mpr ⟨q,⟨hq,rfl⟩,fun p hp => invFunOf_inj hn hp.1 hq hp.2.symm⟩
  have hcount : ((pairs (2*h+2)).filter (hit (invFunOf q))).length = (selected q).card := by
    rw [selected, List.toFinset_card_of_nodup ((pairs_nodup _).filter _)]
    congr 1
    apply List.filter_congr
    intro e he
    exact hit_invFunOf hq (mem_pairs.mp he)
  have hfull : ((pairs (2*h+2)).filter (hit (invFunOf q))).length = h+1 ↔
      ∀ i, q i ≠ i := by
    rw [hcount, ← full_selected_iff hq]
    omega
  have hb : (∀ e ∈ bans G, hit (invFunOf q) e = false) ↔
      ∀ e ∈ selected q, e ∉ bans G := by
    constructor
    · intro h e he hb
      have hh := h e hb
      simpa [hit_invFunOf hq (mem_selected.mp he).1, (mem_selected.mp he).2] using hh
    · intro h e he
      have hl : e.1 < e.2 := mem_pairs.mp (List.mem_filter.mp he).1
      rw [hit_invFunOf hq hl, decide_eq_false_iff_not]
      exact fun hp => h e (mem_selected.mpr ⟨hl,hp⟩) he
  simp only [ReverseOK, Padded, hc, hq, true_and, hb, hfull, and_comm]

private noncomputable def reverseFnEquiv {h : Nat} (G : Fin (2*h) → Fin (2*h) → Bool) :
    {q : Equiv.Perm (Fin (2*h+2)) // Padded G q} ≃
      {f : Fn (2*h+2) // ReverseOK G f} :=
  Equiv.ofBijective (fun q => ⟨invFunOf q.val,(reverse_inv_iff q.2.1).mpr q.2⟩) (by
    have hn : 2 ≤ 2*h+2 := by omega
    constructor
    · intro p q he
      exact Subtype.ext (invFunOf_inj hn p.2.1 q.2.1 (congrArg Subtype.val he))
    · intro f
      obtain ⟨q,⟨hq,he⟩,_⟩ := (circuit_iff hn f.val).mp f.2.1
      exact ⟨⟨q,(reverse_inv_iff hq).mp (he ▸ f.2)⟩,Subtype.ext he.symm⟩)

def redCount {v : Nat} (R : Fin v → Fin v → Bool) (p : Equiv.Perm (Fin v)) : Nat :=
  ((pairs v).filter (fun e => decide (p e.1 = e.2) && R e.1 e.2)).length

private theorem probes_extend {v : Nat} {G R : Fin v → Fin v → Bool}
    {p : Equiv.Perm (Fin v)} (hp : Perfect v G p) :
    redCount R p = ((probes G R).filter (hit (invFunOf (extendPerm hp.1)))).length := by
  let q := extendPerm hp.1
  have hq := (extend_padded hp).1
  have heval (a : Fin v × Fin v) : q (liftEdge a).1 = (liftEdge a).2 ↔ p a.1 = a.2 := by
    change extendFn p (incl a.1) = incl a.2 ↔ _
    rw [extend_incl]
    exact ⟨fun h => incl_inj h, congrArg incl⟩
  have hnod : (probes G R).Nodup := (pairs_nodup _).filter _
  rw [redCount, ← List.toFinset_card_of_nodup ((pairs_nodup _).filter _),
    ← List.toFinset_card_of_nodup (hnod.filter _)]
  apply Finset.card_bij (fun a _ => liftEdge a)
  · intro a ha
    simp only [List.mem_toFinset, List.mem_filter, mem_pairs, Bool.and_eq_true,
      decide_eq_true_eq] at ha
    have hG := (hp.2 a.1).2
    rw [ha.2.1, min_eq_left ha.1.le, max_eq_right ha.1.le] at hG
    have hl := (liftEdge_order a).mpr ha.1
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨probe_iff.mpr ⟨a,ha.1,hG,ha.2.2,rfl⟩,
      by rw [hit_invFunOf hq hl, decide_eq_true_eq]; exact (heval a).mpr ha.2.1⟩)
  · intro a _ b _ he
    exact liftEdge_inj he
  · intro e he
    obtain ⟨he,hh⟩ := List.mem_filter.mp (List.mem_toFinset.mp he)
    obtain ⟨a,ha,_,hR,rfl⟩ := probe_iff.mp he
    rw [hit_invFunOf hq ((liftEdge_order a).mpr ha), decide_eq_true_eq] at hh
    refine ⟨a, ?_, rfl⟩
    simp [mem_pairs, ha, (heval a).mp hh, hR]

/-- The reverse cardinality clause, without the machine/encoding equality. -/
theorem reverse_card (h : Nat) (G R : Fin (2*h) → Fin (2*h) → Bool) (j : Nat) :
    Nat.card {p : Equiv.Perm (Fin (2*h)) // Perfect (2*h) G p ∧ redCount R p = j} =
      Nat.card {f : Fn (2*h+2) // ReverseOK G f ∧ ((probes G R).filter (hit f)).length = j} := by
  let e := (paddedEquiv G).trans (reverseFnEquiv G)
  have hh (p : {p : Equiv.Perm (Fin (2*h)) // Perfect (2*h) G p}) :
      redCount R p.val = ((probes G R).filter (hit (e p).val)).length :=
    probes_extend p.2
  apply Nat.card_congr
  exact
    { toFun := fun p => ⟨(e ⟨p.val,p.2.1⟩).val, (e ⟨p.val,p.2.1⟩).2,
        (hh ⟨p.val,p.2.1⟩).symm.trans p.2.2⟩
      invFun := fun f => ⟨(e.symm ⟨f.val,f.2.1⟩).val, (e.symm ⟨f.val,f.2.1⟩).2,
        (hh (e.symm ⟨f.val,f.2.1⟩)).trans (by rw [e.apply_symm_apply]; exact f.2.2)⟩
      left_inv := fun p => Subtype.ext (congrArg
        (fun a : {p : Equiv.Perm (Fin (2*h)) // Perfect (2*h) G p} => a.val)
        (e.symm_apply_apply ⟨p.val,p.2.1⟩))
      right_inv := fun f => Subtype.ext (congrArg
        (fun a : {f : Fn (2*h+2) // ReverseOK G f} => a.val)
        (e.apply_symm_apply ⟨f.val,f.2.1⟩)) }

end PEqualNP.Outside.L_meta_33617.CircuitReverse


namespace PEqualNP.Outside.L_meta_33617.Gadget

abbrev H (m : Nat) := 2*m+1
abbrev Q (m : Nat) := 2*H m
def K (n m : Nat) := 4*n + (n*n)*Q m + 2*m
abbrev Pair (n : Nat) := Fin n × Fin n
abbrev Vertex (n m : Nat) := Fin n ⊕ ((Fin n × Fin 3) ⊕
  ((Pair n × Fin (Q m)) ⊕ (Fin m × Fin 2)))

def orig (i : Fin n) : Vertex n m := .inl i
def tri (i : Fin n) (s : Fin 3) : Vertex n m := .inr (.inl (i,s))
def path (p : Pair n) (r : Fin (Q m)) : Vertex n m := .inr (.inr (.inl (p,r)))
def pad (i : Fin m) (s : Fin 2) : Vertex n m := .inr (.inr (.inr (i,s)))

def index (n m : Nat) : Vertex n m ≃ Fin (K n m) :=
  (((Equiv.refl _).sumCongr (finProdFinEquiv.sumCongr
    (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv).sumCongr
      finProdFinEquiv))).trans
    (((Equiv.refl _).sumCongr ((Equiv.refl _).sumCongr finSumFinEquiv)).trans
      (((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv))).trans
        (finCongr (by unfold K; omega))

@[simp] theorem index_orig (i : Fin n) : (index n m (orig i)).val = i.val := rfl
@[simp] theorem index_tri (i : Fin n) (s : Fin 3) :
    (index n m (tri i s)).val = n + 3*i.val + s.val := by
  change n + (s.val + 3*i.val) = _
  omega
@[simp] theorem index_path (p : Pair n) (r : Fin (Q m)) :
    (index n m (path p r)).val = 4*n + (p.1.val*n+p.2.val)*Q m+r.val := by
  change n + (n*3 + (r.val + Q m * (p.2.val + n*p.1.val))) = _
  rw [Nat.mul_comm n p.1.val, Nat.add_comm p.2.val, Nat.mul_comm (Q m)]
  omega
@[simp] theorem index_pad (i : Fin m) (s : Fin 2) :
    (index n m (pad i s : Vertex n m)).val = 4*n + (n*n)*Q m + 2*i.val+s.val := by
  change n + (n*3 + ((n*n)*Q m + (s.val + 2*i.val))) = _
  omega

inductive Edge (n m : Nat)
  | ab (i : Fin n)
  | ac (i : Fin n)
  | bc (i : Fin n)
  | link (i : Fin (n-1))
  | spoke (i : Fin n)
  | walk (p : Pair n) (s : Fin (Q m+1))
  | fixed (i : Fin m)
  deriving DecidableEq, Fintype

def leftLink (i : Fin (n-1)) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def rightLink (i : Fin (n-1)) : Fin n := ⟨i.val+1, by have := i.isLt; omega⟩

@[simp] theorem leftLink_val (i : Fin (n-1)) : (leftLink i).val = i.val := rfl
@[simp] theorem rightLink_val (i : Fin (n-1)) : (rightLink i).val = i.val+1 := rfl

abbrev first (m : Nat) : Fin (Q m) := ⟨0, by unfold Q H; omega⟩
abbrev last (m : Nat) : Fin (Q m) := ⟨Q m-1, by unfold Q H; omega⟩
abbrev enter (m : Nat) : Fin (Q m+1) := 0
abbrev exit (m : Nat) : Fin (Q m+1) := Fin.last (Q m)

def walkEnds (p : Pair n) (s : Fin (Q m+1)) : Vertex n m × Vertex n m :=
  if h₀ : s.val = 0 then (orig p.1, path p (first m))
  else if hQ : s.val = Q m then (orig p.2, path p (last m))
  else (path p ⟨s.val-1, by have := s.isLt; omega⟩,
        path p ⟨s.val, by have := s.isLt; omega⟩)

/-- Endpoint pairs are oriented in increasing encoded order, including the exit edge. -/
def ends : Edge n m → Vertex n m × Vertex n m
  | .ab i => (tri i 0, tri i 1)
  | .ac i => (tri i 0, tri i 2)
  | .bc i => (tri i 1, tri i 2)
  | .link i => (tri (leftLink i) 2, tri (rightLink i) 0)
  | .spoke i => (orig i, tri i 1)
  | .walk p s => walkEnds p s
  | .fixed i => (pad i 0, pad i 1)

def indices (e : Edge n m) : Nat × Nat :=
  ((index n m (ends e).1).val, (index n m (ends e).2).val)

def allowed (a : Nat → Nat → Bool) (p : Pair n) : Bool :=
  decide (p.1 < p.2) && a p.1.val p.2.val

def live (a : Nat → Nat → Bool) : Edge n m → Bool
  | .walk p s => if s.val = 0 ∨ s.val = Q m then allowed a p else true
  | _ => true

def paint (w : Nat → Nat → Nat) (b : Nat) : Edge n m → Bool
  | .walk p s => decide (s.val < Q m ∧ s.val % 2 = 0 ∧ s.val/2 < w p.1.val p.2.val)
  | .fixed i => decide (i.val < b)
  | _ => false

def joins (x y : Nat) (p : Nat × Nat) : Prop :=
  (x = p.1 ∧ y = p.2) ∨ (x = p.2 ∧ y = p.1)
instance (x y : Nat) (p : Nat × Nat) : Decidable (joins x y p) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def graph (n m : Nat) (a : Nat → Nat → Bool) (x y : Nat) : Bool :=
  decide (∃ e : Edge n m, live a e = true ∧ joins x y (indices e))

def color (n m : Nat) (a : Nat → Nat → Bool) (w : Nat → Nat → Nat) (b x y : Nat) : Bool :=
  decide (∃ e : Edge n m, live a e = true ∧ paint w b e = true ∧ joins x y (indices e))

def G (n m : Nat) (a : Nat → Nat → Bool) (x y : Fin (K n m)) := graph n m a x.val y.val
def R (n m : Nat) (a : Nat → Nat → Bool) (w : Nat → Nat → Nat) (b : Nat)
    (x y : Fin (K n m)) := color n m a w b x.val y.val

def Perfect (a : Nat → Nat → Bool) (P : Equiv.Perm (Fin (K n m))) : Prop :=
  Function.Involutive P ∧ ∀ x, P x ≠ x ∧ G n m a (min x (P x)) (max x (P x)) = true

def endpoints (e : Pair n) : Finset (Fin n) := {e.1,e.2}

def Admissible (a : Nat → Nat → Bool) (S : Finset (Pair n)) : Prop :=
  (∀ e ∈ S, allowed a e = true) ∧
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (endpoints e) (endpoints f)

def extract (P : Equiv.Perm (Fin (K n m))) : Finset (Pair n) :=
  Finset.univ.filter fun p => P (index n m (orig p.1)) = index n m (path p (first m))

@[simp] theorem mem_extract (P : Equiv.Perm (Fin (K n m))) (p : Pair n) :
    p ∈ extract P ↔ P (index n m (orig p.1)) = index n m (path p (first m)) := by
  exact Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])

/-- On a path whose internal vertices have degree two, successive selected-edge bits
are complementary, so edge zero and the last edge agree on an odd-length path. -/
theorem walk_bits (q : Nat) (b : Fin (q+1) → Bool)
    (hb : ∀ i : Nat, ∀ hi : i < q,
      b ⟨i, by omega⟩ = !b ⟨i+1, by omega⟩) (s : Fin (q+1)) :
    b s = (if s.val % 2 = 0 then b 0 else !b 0) := by
  obtain ⟨s,hs⟩ := s
  induction s with
  | zero => rfl
  | succ s ih =>
    have hs' : s < q := by omega
    have h := hb s hs'
    have hh := ih (by omega)
    have hh' : (s+1)%2 = 0 ↔ s%2 ≠ 0 := by omega
    change b ⟨s+1,hs⟩ = (if (s+1)%2 = 0 then b 0 else !b 0)
    by_cases he : s%2 = 0 <;> cases h₀ : b 0 <;> cases h₁ : b ⟨s+1,hs⟩ <;>
      simp_all [hh']

/-- A private triangle consumes a spoke exactly when its original vertex is unused.
The outgoing link carries incoming parity plus the used-original bit. -/
theorem triangle_bits (u incoming outgoing spoke ab ac bc : Bool)
    (hu : u = !spoke)
    (ha : incoming.toNat + ab.toNat + ac.toNat = 1)
    (hb : spoke.toNat + ab.toNat + bc.toNat = 1)
    (hc : outgoing.toNat + ac.toNat + bc.toNat = 1) :
    outgoing = (incoming ^^ u) ∧ ab = (u && !incoming) ∧
    ac = (!u && !incoming) ∧ bc = (u && incoming) := by
  cases u <;> cases incoming <;> cases outgoing <;> cases spoke <;>
    cases ab <;> cases ac <;> cases bc <;> simp_all [Bool.toNat]

theorem triangle_bits_build (u incoming : Bool) :
    incoming.toNat + (u && !incoming).toNat + (!u && !incoming).toNat = 1 ∧
    (!u).toNat + (u && !incoming).toNat + (u && incoming).toNat = 1 ∧
    (incoming ^^ u).toNat + (!u && !incoming).toNat + (u && incoming).toNat = 1 := by
  cases u <;> cases incoming <;> decide

theorem indices_lt (e : Edge n m) : (indices e).1 < (indices e).2 := by
  cases e with
  | walk p s =>
    simp only [indices, ends, walkEnds]
    have h₁ := p.1.isLt
    have h₂ := p.2.isLt
    have hs := s.isLt
    split_ifs <;> simp only [Prod.fst, Prod.snd, index_orig, index_path] <;> omega
  | ab i | ac i | bc i | link i | spoke i | fixed i =>
    try have := i.isLt
    simp only [indices, ends, index_orig, index_tri, index_pad,
      leftLink_val, rightLink_val]
    omega

theorem ends_injective : Function.Injective (@ends n m) := by
  intro e f h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  clear h
  cases e <;> cases f <;> simp only [ends, walkEnds] at h₁ h₂
  all_goals
    (try split_ifs at h₁ h₂) <;>
      simp_all only [orig, tri, path, pad, Prod.fst, Prod.snd, Sum.inr.injEq,
        Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two,
        leftLink_val, rightLink_val, reduceCtorEq, and_true, true_and, first, last,
        Edge.ab.injEq, Edge.ac.injEq, Edge.bc.injEq, Edge.link.injEq, Edge.spoke.injEq,
        Edge.walk.injEq, Edge.fixed.injEq] <;> (try simp only [Q, H] at *) <;> omega

def Inc (x : Vertex n m) (e : Edge n m) : Prop := x = (ends e).1 ∨ x = (ends e).2

def Cover (take : Edge n m → Bool) : Prop :=
  ∀ x : Vertex n m, ∃! e, take e = true ∧ Inc x e

def Compatible (a : Nat → Nat → Bool) (take : Edge n m → Bool) : Prop :=
  ∀ e, take e = true → live a e = true

def leftSlot (r : Fin (Q m)) : Fin (Q m+1) := ⟨r.val, by have := r.isLt; omega⟩
def rightSlot (r : Fin (Q m)) : Fin (Q m+1) := ⟨r.val+1, by have := r.isLt; omega⟩

theorem inc_path (p : Pair n) (r : Fin (Q m)) (e : Edge n m) :
    Inc (path p r) e ↔ e = .walk p (leftSlot r) ∨ e = .walk p (rightSlot r) := by
  cases e with
  | walk p' s =>
    simp only [Inc, ends, walkEnds]
    have hr := r.isLt
    have hs := s.isLt
    split
    · simp only [path, orig, Prod.snd, Prod.fst, Sum.inr.injEq, Sum.inl.injEq,
        reduceCtorEq, Prod.mk.injEq, false_or, Edge.walk.injEq]
      by_cases hp : p = p'
      · subst p'
        simp only [true_and, Fin.ext_iff, leftSlot, rightSlot, first]
        omega
      · simp [hp, Ne.symm hp]
    · split
      · simp only [path, orig, Prod.snd, Prod.fst, Sum.inr.injEq, Sum.inl.injEq,
          reduceCtorEq, Prod.mk.injEq, false_or, Edge.walk.injEq]
        by_cases hp : p = p'
        · subst p'
          simp only [true_and, Fin.ext_iff, leftSlot, rightSlot, last]
          omega
        · simp [hp, Ne.symm hp]
      · simp only [path, Prod.snd, Prod.fst, Sum.inr.injEq, Sum.inl.injEq,
          Prod.mk.injEq, Edge.walk.injEq]
        by_cases hp : p = p'
        · subst p'
          simp only [true_and, Fin.ext_iff, leftSlot, rightSlot]
          omega
        · simp [hp, Ne.symm hp]
  | ab _ | ac _ | bc _ | link _ | spoke _ | fixed _ =>
    simp [Inc, ends, path, orig, tri, pad]

theorem inc_orig (i : Fin n) (e : Edge n m) :
    Inc (orig i) e ↔ e = .spoke i ∨
      ∃ p : Pair n, (e = .walk p (enter m) ∧ i = p.1) ∨
        (e = .walk p (exit m) ∧ i = p.2) := by
  cases e with
  | walk p s =>
    have hs := s.isLt
    simp only [Inc, ends, walkEnds]
    split_ifs with h₀ hQ
    · have h : s = enter m := Fin.ext h₀
      have h' : s ≠ exit m := fun h' => by
        have := congrArg Fin.val h'; change s.val = Q m at this; unfold Q H at *; omega
      simp [orig, path, h, h', show enter m ≠ exit m from h ▸ h']
    · have h : s = exit m := Fin.ext hQ
      have h' : s ≠ enter m := fun h' => h₀ (congrArg Fin.val h')
      simp [orig, path, h, h', show exit m ≠ enter m from h ▸ h']
    · have h₀' : s ≠ enter m := fun h' => h₀ (congrArg Fin.val h')
      have hQ' : s ≠ exit m := fun h' => hQ (congrArg Fin.val h')
      simp [orig, path, h₀', hQ']
  | ab _ | ac _ | bc _ | link _ | spoke _ | fixed _ =>
    simp [Inc, ends, path, orig, tri, pad, eq_comm]

theorem inc_pad (i : Fin m) (s : Fin 2) (e : Edge n m) :
    Inc (pad i s : Vertex n m) e ↔ e = .fixed i := by
  cases e with
  | fixed j =>
    fin_cases s <;> simp [Inc, ends, pad, eq_comm]
  | walk p s =>
    simp only [Inc, ends, walkEnds]
    split_ifs <;> simp [pad, orig, path]
  | ab _ | ac _ | bc _ | link _ | spoke _ =>
    simp [Inc, ends, orig, tri, pad]

private theorem two_cover {α : Type*} (take : α → Bool) {e f : α} (hne : e ≠ f) :
    (∃! g, take g = true ∧ (g = e ∨ g = f)) ↔ take e = !take f := by
  constructor
  · rintro ⟨g, ⟨hg, hgo⟩, uniq⟩
    rcases hgo with hge | hgf
    · subst g
      have hf : take f ≠ true := fun hf =>
        hne (uniq f ⟨hf, Or.inr rfl⟩).symm
      cases he : take e <;> cases h' : take f <;> simp_all
    · subst g
      have he : take e ≠ true := fun he => hne (uniq e ⟨he, Or.inl rfl⟩)
      cases h' : take e <;> cases hf : take f <;> simp_all
  · intro h
    cases he : take e <;> cases hf : take f
    · simp [he,hf] at h
    · exact ⟨f, ⟨hf, Or.inr rfl⟩, fun g hg =>
        hg.2.elim (fun h => by subst g; simp_all) id⟩
    · exact ⟨e, ⟨he, Or.inl rfl⟩, fun g hg =>
        hg.2.elim id (fun h => by subst g; simp_all)⟩
    · simp [he,hf] at h

theorem cover_walk {take : Edge n m → Bool} (h : Cover take) (p : Pair n)
    (s : Fin (Q m+1)) :
    take (.walk p s) = (if s.val % 2 = 0 then take (.walk p (enter m))
      else !take (.walk p (enter m))) := by
  apply walk_bits (Q m) (fun s => take (.walk p s)) _ s
  intro r hr
  have hh := h (path p ⟨r,hr⟩)
  simp only [inc_path] at hh
  exact (two_cover take (fun he => by
    have hs := (Edge.walk.inj he).2
    have hv := congrArg Fin.val hs
    change r = r+1 at hv
    omega)).mp hh

theorem active_exit {take : Edge n m → Bool} (h : Cover take) (p : Pair n) :
    take (.walk p (exit m)) = take (.walk p (enter m)) := by
  have hm : (exit m).val % 2 = 0 := by change Q m % 2 = 0; unfold Q; omega
  simpa [hm] using cover_walk h p (exit m)

theorem walk_enter_ends (p : Pair n) :
    ends (.walk p (enter m)) = (orig p.1, path p (first m)) := by simp [ends,walkEnds]

theorem walk_exit_ends (p : Pair n) :
    ends (.walk p (exit m)) = (orig p.2, path p (last m)) := by
  have hm : (exit m).val ≠ 0 := by change Q m ≠ 0; unfold Q H; omega
  simp [ends, walkEnds, hm]

theorem cover_fixed {take : Edge n m → Bool} (h : Cover take) (i : Fin m) :
    take (.fixed i) = true := by
  obtain ⟨e,⟨he,hi⟩,_⟩ := h (pad i 0)
  simpa [(inc_pad i 0 e).mp hi] using he

end PEqualNP.Outside.L_meta_33617.Gadget

namespace PEqualNP.Outside.L_meta_33617.Gadget

def active (take : Edge n m → Bool) : Finset (Pair n) :=
  Finset.univ.filter fun p => take (.walk p (enter m)) = true

@[simp] theorem mem_active {take : Edge n m → Bool} {p : Pair n} :
    p ∈ active take ↔ take (.walk p (enter m)) = true := by
  exact Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])

def support (S : Finset (Pair n)) : Finset (Fin n) := S.biUnion endpoints

theorem mem_support {S : Finset (Pair n)} {i : Fin n} :
    i ∈ support S ↔ ∃ p ∈ S, i ∈ endpoints p := Finset.mem_biUnion

def used (S : Finset (Pair n)) (i : Fin n) : Bool := decide (i ∈ support S)

def endEdge (p : Pair n) (i : Fin n) (m : Nat) : Edge n m :=
  .walk p (if i = p.1 then enter m else exit m)

private theorem terminal_inc (i : Fin n) (p : Pair n) {a : Nat → Nat → Bool}
    (ha : allowed a p = true) (hi : i ∈ endpoints p) :
    Inc (orig i) (endEdge p i m) := by
  apply (inc_orig i _).mpr
  right
  use p
  by_cases hf : i = p.1
  · exact Or.inl ⟨by simp [endEdge, hf], hf⟩
  · exact Or.inr ⟨by simp [endEdge, hf], by simpa [endpoints, hf] using hi⟩

private theorem terminal_taken {take : Edge n m → Bool} {S : Finset (Pair n)}
    (hs : ∀ p, take (.walk p (enter m)) = decide (p ∈ S) ∧
      take (.walk p (exit m)) = decide (p ∈ S))
    {p : Pair n} (hp : p ∈ S) (i : Fin n) : take (endEdge p i m) = true := by
  obtain ⟨he,hx⟩ := hs p
  by_cases hf : i = p.1 <;> simp [endEdge, hf, he, hx, hp]

private theorem classify_orig {take : Edge n m → Bool} {S : Finset (Pair n)}
    {a : Nat → Nat → Bool} (hS : ∀ p ∈ S, allowed a p = true)
    (hs : ∀ p, take (.walk p (enter m)) = decide (p ∈ S) ∧
      take (.walk p (exit m)) = decide (p ∈ S))
    (i : Fin n) (e : Edge n m) (ht : take e = true) (hi : Inc (orig i) e) :
    e = .spoke i ∨ ∃ p ∈ S, i ∈ endpoints p ∧ e = endEdge p i m := by
  rcases (inc_orig i e).mp hi with he | ⟨p, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · exact Or.inl he
  · have hp : p ∈ S := of_decide_eq_true ((hs p).1.symm.trans ht)
    exact Or.inr ⟨p,hp,by simp [endpoints],by simp [endEdge]⟩
  · have hp : p ∈ S := of_decide_eq_true ((hs p).2.symm.trans ht)
    have hlt : p.1 < p.2 := by simpa [allowed] using
      (Bool.and_eq_true_iff.mp (hS p hp)).1
    have hn : p.2 ≠ p.1 := (ne_of_lt hlt).symm
    exact Or.inr ⟨p,hp,by simp [endpoints],by simp [endEdge, hn]⟩

theorem enter_exit_active {take : Edge n m → Bool} (h : Cover take) (p : Pair n) :
    take (.walk p (enter m)) = decide (p ∈ active take) ∧
    take (.walk p (exit m)) = decide (p ∈ active take) := by
  rw [active_exit h]
  cases he : take (.walk p (enter m)) <;> simp [he]

theorem active_admissible {take : Edge n m → Bool} {a : Nat → Nat → Bool}
    (h : Cover take) (ha : Compatible a take) : Admissible a (active take) := by
  have hl (p) (hp : p ∈ active take) : allowed a p = true := by
    have ht := ha (.walk p (enter m)) (mem_active.mp hp)
    simpa [live] using ht
  refine ⟨hl, fun p hp q hq hn => Finset.disjoint_left.mpr ?_⟩
  intro i hi hq'
  have h₁ := terminal_inc (m := m) i p (hl p hp) hi
  have h₂ := terminal_inc (m := m) i q (hl q hq) hq'
  have hh := (h (orig i)).unique
    ⟨terminal_taken (enter_exit_active h) hp i, h₁⟩
    ⟨terminal_taken (enter_exit_active h) hq i, h₂⟩
  unfold endEdge at hh
  exact hn (Edge.walk.inj hh).1

theorem cover_spoke {take : Edge n m → Bool} {a : Nat → Nat → Bool}
    (h : Cover take) (ha : Compatible a take) (i : Fin n) :
    take (.spoke i) = !used (active take) i := by
  have hS := (active_admissible h ha).1
  by_cases hi : i ∈ support (active take)
  · obtain ⟨p,hp,hip⟩ := mem_support.mp hi
    have ht := terminal_taken (enter_exit_active h) hp i
    have hn : take (.spoke i) ≠ true := by
      intro ht'
      have he := (h (orig i)).unique ⟨ht, terminal_inc i p (hS p hp) hip⟩
        ⟨ht', (inc_orig i _).mpr (Or.inl rfl)⟩
      cases he
    cases he : take (.spoke i) <;> simp_all [used]
  · obtain ⟨e,⟨ht,he⟩,_⟩ := h (orig i)
    rcases classify_orig hS (enter_exit_active h) i e ht he with rfl | ⟨p,hp,hp',_⟩
    · simp [used, hi, ht]
    · exact False.elim (hi (mem_support.mpr ⟨p,hp,hp'⟩))

def usedPrefix (S : Finset (Pair n)) (t : Nat) : Finset (Fin n) :=
  (support S).filter fun i => i.val < t

def parity (S : Finset (Pair n)) (t : Nat) : Bool :=
  decide ((usedPrefix S t).card % 2 = 1)

theorem prefix_step (S : Finset (Pair n)) (i : Fin n) :
    usedPrefix S (i.val+1) =
      if i ∈ support S then insert i (usedPrefix S i.val) else usedPrefix S i.val := by
  by_cases hi : i ∈ support S <;> ext j
  · by_cases he : j = i
    · subst j
      simp [usedPrefix, hi]
    · have hl : j ≤ i ↔ j < i := ⟨fun h => lt_of_le_of_ne h he, le_of_lt⟩
      simp [usedPrefix, hi, he, hl]
  · by_cases he : j = i
    · subst j
      simp [usedPrefix, hi]
    · have hl : j ≤ i ↔ j < i := ⟨fun h => lt_of_le_of_ne h he, le_of_lt⟩
      simp [usedPrefix, hi, he, hl]

theorem parity_step (S : Finset (Pair n)) (i : Fin n) :
    parity S (i.val+1) = (parity S i.val ^^ used S i) := by
  have hn : i ∉ usedPrefix S i.val := by simp [usedPrefix]
  unfold parity used
  rw [prefix_step]
  by_cases hi : i ∈ support S
  · simp only [hi, if_pos, decide_true, Bool.xor_true, Finset.card_insert_of_notMem hn]
    by_cases h : (usedPrefix S i.val).card % 2 = 1
    · simp [h, show ((usedPrefix S i.val).card+1)%2 ≠ 1 by omega]
    · simp [h, show ((usedPrefix S i.val).card+1)%2 = 1 by omega]
  · simp [hi]

@[simp] theorem parity_zero (S : Finset (Pair n)) : parity S 0 = false := by
  simp [parity,usedPrefix]

theorem support_card {S : Finset (Pair n)} {a : Nat → Nat → Bool}
    (hS : Admissible a S) : (support S).card = 2*S.card := by
  unfold support
  have he : (S : Set (Pair n)).PairwiseDisjoint endpoints := by
    intro e he f hf hne
    exact hS.2 e he f hf hne
  rw [Finset.card_biUnion he]
  calc
    _ = ∑ e ∈ S, 2 := Finset.sum_congr rfl fun e he => by
      have ht := (Bool.and_eq_true_iff.mp (hS.1 e he)).1
      have hlt : e.1 < e.2 := of_decide_eq_true ht
      exact Finset.card_pair (ne_of_lt hlt)
    _ = 2 * S.card := by simp [Nat.mul_comm]

theorem parity_end {S : Finset (Pair n)} {a : Nat → Nat → Bool}
    (hS : Admissible a S) : parity S n = false := by
  have h : usedPrefix S n = support S := by
    ext i
    simp [usedPrefix, i.isLt]
  simp [parity, h, support_card hS]

def atLink (n m t : Nat) : Option (Edge n m) :=
  if h : 0 < t ∧ t < n then some (.link ⟨t-1, by omega⟩) else none

def trace (take : Edge n m → Bool) (t : Nat) : Bool := (atLink n m t).elim false take

theorem atLink_eq (t : Nat) (j : Fin (n-1)) :
    atLink n m t = some (.link j) ↔ t = j.val+1 := by
  have hj := j.isLt
  by_cases h : 0 < t ∧ t < n
  · simp only [atLink, dif_pos h, Option.some.injEq, Edge.link.injEq, Fin.ext_iff]
    omega
  · constructor
    · intro he
      simp [atLink, h] at he
    · intro ht
      exfalso
      apply h
      rw [ht]
      exact ⟨by omega,by omega⟩

private theorem atLink_some (t : Nat) (e : Edge n m) :
    atLink n m t = some e ↔ ∃ j : Fin (n-1), e = .link j ∧ t = j.val+1 := by
  constructor
  · intro he
    by_cases h : 0 < t ∧ t < n
    · let j : Fin (n-1) := ⟨t-1, by omega⟩
      have hj : atLink n m t = some (.link j) := by simp [atLink,h,j]
      exact ⟨j, Option.some.inj (he.symm.trans hj), (atLink_eq t j).mp hj⟩
    · simp [atLink,h] at he
  · rintro ⟨j,rfl,hj⟩
    exact (atLink_eq t j).mpr hj

@[simp] theorem trace_zero (take : Edge n m → Bool) : trace take 0 = false := by
  simp [trace, atLink]

@[simp] theorem trace_end (take : Edge n m → Bool) : trace take n = false := by
  simp [trace, atLink]

theorem trace_link (take : Edge n m → Bool) (j : Fin (n-1)) :
    trace take (j.val+1) = take (.link j) := by
  unfold trace
  rw [(atLink_eq (m := m) (j.val+1) j).mpr rfl]
  rfl

def nearTri (i : Fin n) (s : Fin 3) : Edge n m × Edge n m × Option (Edge n m) :=
  if s = 0 then (.ab i,.ac i,atLink n m i.val)
  else if s = 1 then (.ab i,.bc i,some (.spoke i))
  else (.ac i,.bc i,atLink n m (i.val+1))

theorem inc_tri (i : Fin n) (s : Fin 3) (e : Edge n m) :
    Inc (tri i s) e ↔
      e = (nearTri i s).1 ∨ e = (nearTri i s).2.1 ∨ (nearTri i s).2.2 = some e := by
  cases e <;> fin_cases s <;> simp [nearTri, Inc, ends, walkEnds, atLink_some]
  all_goals
    (try split_ifs) <;>
      simp only [orig, tri, path, pad, Prod.fst, Prod.snd, Sum.inr.injEq, Sum.inl.injEq,
        Prod.mk.injEq, Option.some.injEq, reduceCtorEq, Edge.ab.injEq, Edge.ac.injEq,
        Edge.bc.injEq, Edge.link.injEq, Edge.spoke.injEq, Fin.ext_iff, Fin.val_zero,
        Fin.val_one, Fin.val_two, leftLink_val, rightLink_val,
        false_or, or_false, and_true, true_and, and_false, false_and] <;>
      (try simp) <;> (try omega)

def optionBit (take : α → Bool) (c : Option α) := c.elim false take

private theorem cover_optional {α : Type*} [DecidableEq α] (take : α → Bool)
    (e f : α) (c : Option α) (hef : e ≠ f)
    (hec : c ≠ some e) (hfc : c ≠ some f) :
    (∃! g, take g = true ∧ (g = e ∨ g = f ∨ c = some g)) ↔
      (take e).toNat + (take f).toNat + (optionBit take c).toNat = 1 := by
  let U : Finset α := insert e (insert f c.toFinset)
  have hcard := (Finset.card_eq_one_iff_existsUnique
    (s := U.filter fun g => take g = true)).symm
  have hmem (g : α) : g ∈ (U.filter fun g => take g = true) ↔
      take g = true ∧ (g = e ∨ g = f ∨ c = some g) := by
    simp only [U, Finset.mem_filter, Finset.mem_insert]
    cases c <;> simp <;> tauto
  simp_rw [hmem] at hcard
  rw [hcard]
  cases c with
  | none =>
      cases h₁ : take e <;> cases h₂ : take f <;>
        simp [U, Finset.filter_insert, Finset.filter_singleton, h₁, h₂, optionBit, Bool.toNat,
          hef, Finset.card_insert_of_notMem]
  | some g =>
      have heg : e ≠ g := fun h => hec (by simp [h])
      have hfg : f ≠ g := fun h => hfc (by simp [h])
      cases h₁ : take e <;> cases h₂ : take f <;> cases h₃ : take g <;>
        simp [U, Finset.filter_insert, Finset.filter_singleton, h₁, h₂, h₃, optionBit, Bool.toNat,
          hef, heg, hfg, Finset.card_insert_of_notMem]

private theorem triangle_degree (take : Edge n m → Bool) (i : Fin n) (s : Fin 3) :
    (∃! e, take e = true ∧ Inc (tri i s) e) ↔
      (take (nearTri i s).1).toNat + (take (nearTri i s).2.1).toNat +
        (optionBit take (nearTri i s).2.2).toNat = 1 := by
  simp_rw [inc_tri]
  apply cover_optional
  all_goals
    fin_cases s <;> simp [nearTri, atLink] <;> split_ifs <;> simp

theorem triangle_local {take : Edge n m → Bool} (h : Cover take)
    {a : Nat → Nat → Bool} (ha : Compatible a take) (i : Fin n) :
    trace take (i.val+1) = (trace take i.val ^^ used (active take) i) ∧
    take (.ab i) = (used (active take) i && !trace take i.val) ∧
    take (.ac i) = (!used (active take) i && !trace take i.val) ∧
    take (.bc i) = (used (active take) i && trace take i.val) := by
  apply triangle_bits _ _ _ (take (.spoke i))
  · rw [cover_spoke h ha]
    simp
  · simpa [nearTri, optionBit, trace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (triangle_degree take i 0).mp (h (tri i 0))
  · simpa [nearTri, optionBit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (triangle_degree take i 1).mp (h (tri i 1))
  · simpa [nearTri, optionBit, trace, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (triangle_degree take i 2).mp (h (tri i 2))

theorem trace_parity {take : Edge n m → Bool} (h : Cover take)
    {a : Nat → Nat → Bool} (ha : Compatible a take) (t : Nat) (ht : t ≤ n) :
    trace take t = parity (active take) t := by
  induction t with
  | zero => simp
  | succ t ih =>
      let i : Fin n := ⟨t, by omega⟩
      exact (triangle_local h ha i).1.trans
        ((congrArg (fun b => b ^^ used (active take) i) (ih (by omega))).trans
          (parity_step (active take) i).symm)

def walkTake (S : Finset (Pair n)) (p : Pair n) (s : Fin (Q m+1)) : Bool :=
  if s.val % 2 = 0 then decide (p ∈ S) else !decide (p ∈ S)

def liftBits (S : Finset (Pair n)) : Edge n m → Bool
  | .ab i => used S i && !parity S i.val
  | .ac i => !used S i && !parity S i.val
  | .bc i => used S i && parity S i.val
  | .link i => parity S (i.val+1)
  | .spoke i => !used S i
  | .walk p s => walkTake S p s
  | .fixed _ => true

theorem liftBits_terminals (S : Finset (Pair n)) (p : Pair n) :
    liftBits (m := m) S (.walk p (enter m)) = decide (p ∈ S) ∧
    liftBits (m := m) S (.walk p (exit m)) = decide (p ∈ S) := by
  have hm : (exit m).val % 2 = 0 := by change Q m % 2 = 0; unfold Q H; omega
  simp [liftBits, walkTake, hm]

theorem liftBits_active (S : Finset (Pair n)) : active (liftBits (m := m) S) = S := by
  ext p
  rw [mem_active, (liftBits_terminals (m := m) S p).1]
  simp

theorem liftBits_compatible {S : Finset (Pair n)} {a : Nat → Nat → Bool}
    (hS : Admissible a S) : Compatible a (liftBits (m := m) S) := by
  intro e he
  cases e with
  | walk p s =>
    simp only [live]
    split_ifs with hs
    · rcases hs with hs | hs
      · have h : s = enter m := Fin.ext hs
        subst s
        exact hS.1 p (of_decide_eq_true ((liftBits_terminals S p).1.symm.trans he))
      · have h : s = exit m := Fin.ext hs
        subst s
        exact hS.1 p (of_decide_eq_true ((liftBits_terminals S p).2.symm.trans he))
    · rfl
  | ab _ | ac _ | bc _ | link _ | spoke _ | fixed _ => rfl

theorem trace_liftBits {S : Finset (Pair n)} {a : Nat → Nat → Bool}
    (hS : Admissible a S) (t : Nat) (ht : t ≤ n) :
    trace (liftBits (m := m) S) t = parity S t := by
  by_cases hz : t = 0
  · subst t; simp
  by_cases hn : t = n
  · subst t; simp [parity_end hS]
  let j : Fin (n-1) := ⟨t-1,by omega⟩
  have hj : t = j.val+1 := by change t = t-1+1; omega
  rw [hj, trace_link]
  rfl

theorem liftBits_cover {S : Finset (Pair n)} {a : Nat → Nat → Bool}
    (hS : Admissible a S) : Cover (liftBits (m := m) S) := by
  let take := liftBits (m := m) S
  change Cover take
  intro x
  rcases x with i | ⟨i,s⟩ | ⟨p,r⟩ | ⟨i,s⟩
  · change ∃! e, take e = true ∧ Inc (orig i) e
    by_cases hi : i ∈ support S
    · obtain ⟨p,hp,hip⟩ := mem_support.mp hi
      refine ⟨endEdge p i m,
        ⟨terminal_taken (liftBits_terminals S) hp i, terminal_inc i p (hS.1 p hp) hip⟩, ?_⟩
      rintro e ⟨he,hin⟩
      rcases classify_orig hS.1 (liftBits_terminals S) i e he hin with rfl | ⟨q,hq,hiq,rfl⟩
      · simp [take, liftBits, used, hi] at he
      · have heq : p = q := by
          by_contra hn
          exact Finset.disjoint_left.mp (hS.2 p hp q hq hn) hip hiq
        simp [heq]
    · refine ⟨.spoke i, ⟨by simp [take, liftBits, used, hi], (inc_orig i _).mpr
        (Or.inl rfl)⟩, ?_⟩
      rintro e ⟨he,hin⟩
      rcases classify_orig hS.1 (liftBits_terminals S) i e he hin with rfl | ⟨p,hp,hip,_⟩
      · rfl
      · exact False.elim (hi (mem_support.mpr ⟨p,hp,hip⟩))
  · change ∃! e, take e = true ∧ Inc (tri i s) e
    apply (triangle_degree take i s).mpr
    have ht := trace_liftBits (m := m) hS i.val (Nat.le_of_lt i.isLt)
    have ht' := trace_liftBits (m := m) hS (i.val+1) i.isLt
    have hp := parity_step S i
    simp only [trace] at ht ht'
    obtain ⟨ha,hb,hc⟩ := triangle_bits_build (used S i) (parity S i.val)
    fin_cases s
    · simpa [nearTri, optionBit, take, liftBits, ht,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ha
    · simpa [nearTri, optionBit, take, liftBits, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hb
    · simpa [nearTri, optionBit, take, liftBits, ht', hp,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
  · change ∃! e, take e = true ∧ Inc (path p r) e
    simp_rw [inc_path]
    apply (two_cover take (fun h => by
      have := congrArg Fin.val (Edge.walk.inj h).2
      change r.val = r.val+1 at this
      omega)).mpr
    have hmod : (r.val+1) % 2 = 0 ↔ r.val % 2 ≠ 0 := by omega
    change walkTake S p (leftSlot r) = !walkTake S p (rightSlot r)
    by_cases he : r.val % 2 = 0 <;> simp [walkTake, leftSlot, rightSlot, hmod, he]
  · change ∃! e, take e = true ∧ Inc (pad i s) e
    refine ⟨.fixed i,⟨rfl, (inc_pad i s _).mpr rfl⟩, ?_⟩
    exact fun e h => (inc_pad i s e).mp h.2

theorem cover_normal {take : Edge n m → Bool} {a : Nat → Nat → Bool}
    (h : Cover take) (ha : Compatible a take) : take = liftBits (active take) := by
  funext e
  cases e with
  | ab i =>
    exact (triangle_local h ha i).2.1.trans (by
      rw [trace_parity h ha i.val (Nat.le_of_lt i.isLt)]; rfl)
  | ac i =>
    exact (triangle_local h ha i).2.2.1.trans (by
      rw [trace_parity h ha i.val (Nat.le_of_lt i.isLt)]; rfl)
  | bc i =>
    exact (triangle_local h ha i).2.2.2.trans (by
      rw [trace_parity h ha i.val (Nat.le_of_lt i.isLt)]; rfl)
  | link i =>
    change take (.link i) = parity (active take) (i.val+1)
    rw [← trace_link take i]
    apply trace_parity h ha
    have := i.isLt
    omega
  | spoke i => exact cover_spoke h ha i
  | fixed i => exact cover_fixed h i
  | walk p s =>
    have hh := (enter_exit_active h p).1
    change take (.walk p s) = walkTake (active take) p s
    unfold walkTake
    rw [← hh]
    exact cover_walk h p s

noncomputable def selectionEquiv (n m : Nat) (a : Nat → Nat → Bool) :
    {take : Edge n m → Bool // Cover take ∧ Compatible a take} ≃
      {S : Finset (Pair n) // Admissible a S} where
  toFun T := ⟨active T.val, active_admissible T.2.1 T.2.2⟩
  invFun S := ⟨liftBits S.val, liftBits_cover S.2, liftBits_compatible S.2⟩
  left_inv T := Subtype.ext (cover_normal T.2.1 T.2.2).symm
  right_inv S := Subtype.ext (liftBits_active (m := m) S.val)

def Adj (e : Edge n m) (x y : Vertex n m) : Prop :=
  (x = (ends e).1 ∧ y = (ends e).2) ∨ (x = (ends e).2 ∧ y = (ends e).1)

private theorem adj_symm {e : Edge n m} {x y : Vertex n m} (h : Adj e x y) : Adj e y x := by
  unfold Adj at *
  tauto

private theorem adj_inc {e : Edge n m} {x y : Vertex n m} (h : Adj e x y) : Inc x e := by
  unfold Adj Inc at *
  tauto

private theorem adj_ne {e : Edge n m} {x y : Vertex n m} (h : Adj e x y) : x ≠ y := by
  have hn : (ends e).1 ≠ (ends e).2 := by
    intro he
    have hx := congrArg (fun x => (index n m x).val) he
    exact (ne_of_lt (indices_lt e)) hx
  intro he
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact hn (hx.symm.trans (he.trans hy))
  · exact hn (hy.symm.trans (he.symm.trans hx))

private theorem adj_edge_unique {e f : Edge n m} {x y : Vertex n m}
    (h : Adj e x y) (h' : Adj f x y) : e = f := by
  have h₁ := indices_lt e
  have h₂ := indices_lt f
  change (index n m (ends e).1).val < (index n m (ends e).2).val at h₁
  change (index n m (ends f).1).val < (index n m (ends f).2).val at h₂
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rcases h' with ⟨hx',hy'⟩ | ⟨hx',hy'⟩
  · exact ends_injective (Prod.ext (hx.symm.trans hx') (hy.symm.trans hy'))
  · rw [← hx, ← hy] at h₁
    rw [← hx', ← hy'] at h₂
    omega
  · rw [← hx, ← hy] at h₁
    rw [← hx', ← hy'] at h₂
    omega
  · exact ends_injective (Prod.ext (hy.symm.trans hy') (hx.symm.trans hx'))

private theorem adj_neighbor_unique {e : Edge n m} {x y z : Vertex n m}
    (h : Adj e x y) (h' : Adj e x z) : y = z := by
  rcases h with ⟨hx, hy⟩ | ⟨hx,hy⟩ <;> rcases h' with ⟨hx',hz⟩ | ⟨hx',hz⟩
  · exact hy.trans hz.symm
  · exact False.elim (adj_ne (e := e) (x := x) (y := x) (Or.inl ⟨hx,hx'⟩) rfl)
  · exact False.elim (adj_ne (e := e) (x := x) (y := x) (Or.inr ⟨hx,hx'⟩) rfl)
  · exact hy.trans hz.symm

private theorem joins_adj (e : Edge n m) (x y : Vertex n m) :
    joins (index n m x).val (index n m y).val (indices e) ↔ Adj e x y := by
  unfold joins indices Adj
  exact or_congr
    (and_congr (Iff.intro (fun h => (index n m).injective (Fin.ext h))
        (congrArg fun v => (index n m v).val))
      (Iff.intro (fun h => (index n m).injective (Fin.ext h))
        (congrArg fun v => (index n m v).val)))
    (and_congr (Iff.intro (fun h => (index n m).injective (Fin.ext h))
        (congrArg fun v => (index n m v).val))
      (Iff.intro (fun h => (index n m).injective (Fin.ext h))
        (congrArg fun v => (index n m v).val)))

theorem graph_adj (a : Nat → Nat → Bool) (x y : Vertex n m) :
    G n m a (min (index n m x) (index n m y)) (max (index n m x) (index n m y)) = true ↔
      ∃ e : Edge n m, live a e = true ∧ Adj e x y := by
  simp only [G, graph, Fin.val_min, Fin.val_max, decide_eq_true_eq]
  rcases le_total (index n m x).val (index n m y).val with h | h
  · simp only [min_eq_left h, max_eq_right h, joins_adj]
  · simp only [min_eq_right h, max_eq_left h, joins_adj]
    exact ⟨fun ⟨e,he,hxy⟩ => ⟨e,he,adj_symm hxy⟩, fun ⟨e,he,hxy⟩ => ⟨e,he,adj_symm hxy⟩⟩

def selected (P : Equiv.Perm (Fin (K n m))) (e : Edge n m) : Bool :=
  decide (P (index n m (ends e).1) = index n m (ends e).2)

theorem selected_from_adj {P : Equiv.Perm (Fin (K n m))}
    (hi : Function.Involutive P) {e : Edge n m} {x y : Vertex n m}
    (h : Adj e x y) (hp : P (index n m x) = index n m y) :
    selected P e = true := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact decide_eq_true hp
  · exact decide_eq_true (hi.eq_iff.mp hp).symm

private theorem adj_from_selected {P : Equiv.Perm (Fin (K n m))}
    (hi : Function.Involutive P) {e : Edge n m} {x : Vertex n m}
    (h : selected P e = true) (hx : Inc x e) :
    Adj e x ((index n m).symm (P (index n m x))) := by
  have hp : P (index n m (ends e).1) = index n m (ends e).2 := of_decide_eq_true h
  rcases hx with hx | hx
  · exact Or.inl ⟨hx,by rw [hx,hp]; simp⟩
  · have hp' := congrArg P hp
    rw [hi] at hp'
    exact Or.inr ⟨hx,by rw [hx,← hp']; simp⟩

private theorem perfect_adj {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) (x : Vertex n m) :
    ∃ e : Edge n m, live a e = true ∧ Adj e x ((index n m).symm (P (index n m x))) := by
  apply (graph_adj a x ((index n m).symm (P (index n m x)))).mp
  simpa only [Equiv.apply_symm_apply] using (hP.2 (index n m x)).2

theorem selected_cover {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) : Cover (selected P) := by
  intro x
  obtain ⟨e,_,he⟩ := perfect_adj hP x
  have hs := selected_from_adj hP.1 he (by simp)
  refine ⟨e,⟨hs,adj_inc he⟩,?_⟩
  rintro f ⟨hf,hx⟩
  exact adj_edge_unique (adj_from_selected hP.1 hf hx) he

theorem selected_compatible {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) : Compatible a (selected P) := by
  intro e he
  obtain ⟨f,hf,hx⟩ := perfect_adj hP (ends e).1
  have ha := adj_from_selected hP.1 he (Or.inl rfl)
  simpa only [adj_edge_unique hx ha] using hf

private theorem cover_adj_unique {take : Edge n m → Bool} (h : Cover take) (x : Vertex n m) :
    ∃! y, ∃ e, take e = true ∧ Adj e x y := by
  obtain ⟨e,⟨he,hx⟩,hu⟩ := h x
  have han : ∃ y, Adj e x y := by
    rcases hx with hx | hx
    · exact ⟨(ends e).2,Or.inl ⟨hx,rfl⟩⟩
    · exact ⟨(ends e).1,Or.inr ⟨hx,rfl⟩⟩
  obtain ⟨y,hy⟩ := han
  refine ⟨y,⟨e,he,hy⟩,?_⟩
  rintro z ⟨f,hf,hz⟩
  have heq := hu f ⟨hf,adj_inc hz⟩
  exact adj_neighbor_unique (heq ▸ hz) hy

noncomputable def next {take : Edge n m → Bool} (h : Cover take)
    (x : Vertex n m) : Vertex n m := (cover_adj_unique h x).exists.choose

theorem next_spec {take : Edge n m → Bool} (h : Cover take) (x : Vertex n m) :
    ∃ e, take e = true ∧ Adj e x (next h x) := (cover_adj_unique h x).exists.choose_spec

theorem next_involutive {take : Edge n m → Bool} (h : Cover take) :
    Function.Involutive (next h) := by
  intro x
  obtain ⟨e,he,ha⟩ := next_spec h x
  exact (cover_adj_unique h (next h x)).unique (next_spec h (next h x))
    ⟨e,he,adj_symm ha⟩

noncomputable def ofCover {take : Edge n m → Bool} (h : Cover take) :
    Equiv.Perm (Fin (K n m)) :=
  (index n m).symm.trans
    ((⟨next h, next h, next_involutive h, next_involutive h⟩ :
      Equiv.Perm (Vertex n m)).trans (index n m))

@[simp] theorem ofCover_index {take : Edge n m → Bool} (h : Cover take) (x : Vertex n m) :
    ofCover h (index n m x) = index n m (next h x) := by
  simp only [ofCover, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem ofCover_perfect {take : Edge n m → Bool} {a : Nat → Nat → Bool}
    (h : Cover take) (ha : Compatible a take) : Perfect a (ofCover h) := by
  constructor
  · intro x
    obtain ⟨v,rfl⟩ := (index n m).surjective x
    rw [ofCover_index,ofCover_index,next_involutive h]
  · intro x
    obtain ⟨v,rfl⟩ := (index n m).surjective x
    obtain ⟨e,he,hadj⟩ := next_spec h v
    rw [ofCover_index]
    exact ⟨fun hn => adj_ne hadj ((index n m).injective hn).symm,
      (graph_adj a _ _).mpr ⟨e,ha e he,hadj⟩⟩

theorem selected_ofCover {take : Edge n m → Bool} (h : Cover take) :
    selected (ofCover h) = take := by
  funext e
  have hiff : selected (ofCover h) e = true ↔ take e = true := by
    unfold selected
    rw [decide_eq_true_eq, ofCover_index]
    constructor
    · intro he
      obtain ⟨f,hf,hx⟩ := next_spec h (ends e).1
      rw [(index n m).injective he] at hx
      have hfe := adj_edge_unique hx (Or.inl ⟨rfl,rfl⟩ : Adj e (ends e).1 (ends e).2)
      exact hfe ▸ hf
    · intro he
      exact congrArg (index n m) ((cover_adj_unique h (ends e).1).unique
        (next_spec h (ends e).1) ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
  exact Bool.eq_iff_iff.mpr hiff

theorem ofCover_selected {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) : ofCover (selected_cover hP) = P := by
  apply Equiv.ext
  intro x
  obtain ⟨v,rfl⟩ := (index n m).surjective x
  rw [ofCover_index, ← (index n m).apply_symm_apply (P (index n m v))]
  apply congrArg (index n m)
  obtain ⟨e,_,he⟩ := perfect_adj hP v
  exact (cover_adj_unique (selected_cover hP) v).unique
    (next_spec (selected_cover hP) v) ⟨e,selected_from_adj hP.1 he (by simp),he⟩

theorem active_selected (P : Equiv.Perm (Fin (K n m))) : active (selected P) = extract P := by
  ext p
  simp [selected,walk_enter_ends]

noncomputable def gadgetEquiv (n m : Nat) (a : Nat → Nat → Bool) :
    {P : Equiv.Perm (Fin (K n m)) // Perfect a P} ≃
    {S : Finset (Pair n) // Admissible a S} :=
  (show {P : Equiv.Perm (Fin (K n m)) // Perfect a P} ≃
      {take : Edge n m → Bool // Cover take ∧ Compatible a take} from
    { toFun := fun P => ⟨selected P.val,selected_cover P.2,selected_compatible P.2⟩
      invFun := fun T => ⟨ofCover T.2.1,ofCover_perfect T.2.1 T.2.2⟩
      left_inv := fun P => Subtype.ext (ofCover_selected P.2)
      right_inv := fun T => Subtype.ext (selected_ofCover T.2.1) }).trans
      (selectionEquiv n m a)

theorem gadgetEquiv_extract {a : Nat → Nat → Bool}
    (P : {P : Equiv.Perm (Fin (K n m)) // Perfect a P}) :
    ((gadgetEquiv n m a) P).val = extract P.val := by
  change active (selected P.val) = extract P.val
  exact active_selected P.val

def originalIndex (i : Fin n) (m : Nat) : Fin (K n m) := index n m (orig i)

theorem mem_extract_val (P : Equiv.Perm (Fin (K n m))) (p : Pair n) :
    p ∈ extract P ↔ (P (originalIndex p.1 m)).val =
      4*n + (p.1.val*n+p.2.val)*Q m := by
  rw [mem_extract, Fin.ext_iff]
  simp [originalIndex, first]

-- Enumeration lemmas adapted from the accepted L_lib_957, pin
-- 773a44dea4b8f3176d5cc06e6ceb5ca0c8aee81a, lean/PEqualNP/Outside/L_lib_957.lean.
def pairs (v : Nat) := (List.finRange v).flatMap (fun i =>
  ((List.finRange v).filter (fun j => decide (i < j))).map (fun j => (i,j)))

theorem mem_pairs {v : Nat} {z : Pair v} : z ∈ pairs v ↔ z.1 < z.2 := by
  rcases z with ⟨i,j⟩
  simp [pairs, List.mem_flatMap,List.mem_finRange]

theorem pairs_nodup (v : Nat) : (pairs v).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    apply List.Nodup.map (fun _ _ h => congrArg Prod.snd h)
    exact (List.nodup_finRange v).filter _
  · apply (List.nodup_finRange v).imp
    intro x y h z hx hy
    obtain ⟨u, -,rfl⟩ := List.mem_map.mp hx
    obtain ⟨w,-,hw⟩ := List.mem_map.mp hy
    exact h (congrArg Prod.fst hw).symm

def finEnds (e : Edge n m) : Pair (K n m) :=
  (index n m (ends e).1, index n m (ends e).2)

theorem finEnds_inj : Function.Injective (@finEnds n m) := by
  intro e f h
  exact ends_injective (Prod.ext ((index n m).injective (congrArg Prod.fst h))
    ((index n m).injective (congrArg Prod.snd h)))

def redLabels (take : Edge n m → Bool) (w : Nat → Nat → Nat) (b : Nat) : Finset (Edge n m) :=
  Finset.univ.filter (fun e => take e = true ∧ paint w b e = true)

def redCount (a : Nat → Nat → Bool) (w : Nat → Nat → Nat) (b : Nat)
    (P : Equiv.Perm (Fin (K n m))) : Nat :=
  ((pairs (K n m)).filter (fun e => decide (P e.1 = e.2) && R n m a w b e.1 e.2)).length

private theorem redLabels_list {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) (w : Nat → Nat → Nat) (b : Nat) :
    (redLabels (selected P) w b).card = redCount a w b P := by
  let L := (pairs (K n m)).filter (fun e => decide (P e.1 = e.2) && R n m a w b e.1 e.2)
  have hL : L.toFinset.card = redCount a w b P :=
    List.toFinset_card_of_nodup ((pairs_nodup _).filter _)
  rw [← hL]
  apply Finset.card_bij (fun e _ => finEnds e)
  · intro e he
    have ht := (Finset.mem_filter.mp he).2
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨mem_pairs.mpr (indices_lt e), Bool.and_eq_true_iff.mpr ⟨ht.1,?_⟩⟩
    apply decide_eq_true
    exact ⟨e,selected_compatible hP e ht.1,ht.2,Or.inl ⟨rfl,rfl⟩⟩
  · intro e he f hf hef
    exact finEnds_inj hef
  · intro xy hxy
    obtain ⟨hxy,hred⟩ := List.mem_filter.mp (List.mem_toFinset.mp hxy)
    have ht := Bool.and_eq_true_iff.mp hred
    have hh : xy.1.val < xy.2.val := mem_pairs.mp hxy
    obtain ⟨e,he,hred,hj⟩ := of_decide_eq_true ht.2
    have heq : finEnds e = xy := by
      have hlt := indices_lt e
      rcases hj with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Prod.ext (Fin.ext h₁.symm) (Fin.ext h₂.symm)
      · change xy.1.val = (indices e).2 at h₁
        change xy.2.val = (indices e).1 at h₂
        omega
    refine ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,hred⟩,heq⟩
    rw [← heq] at ht
    exact ht.1

def below (k t : Nat) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val < t)

theorem mem_below {k t : Nat} {i : Fin k} : i ∈ below k t ↔ i.val < t := by
  exact Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])

private theorem card_below {k t : Nat} (h : t ≤ k) : (below k t).card = t := by
  suffices hc : (below k t).card = (Finset.range t).card by simpa using hc
  apply Finset.card_bij (fun i _ => i.val)
  · exact fun i hi => Finset.mem_range.mpr (mem_below.mp hi)
  · exact fun i _ j _ h => Fin.ext h
  · intro i hi
    have hit := Finset.mem_range.mp hi
    exact ⟨⟨i,lt_of_lt_of_le hit h⟩, mem_below.mpr hit, rfl⟩

def evenSlot (t : Fin (H m)) : Fin (Q m+1) := ⟨2*t.val, by
  have := t.isLt
  unfold Q
  omega⟩

def fixedRed (n m b : Nat) : Finset (Edge n m) :=
  (below m b).map ⟨Edge.fixed, fun _ _ he => Edge.fixed.inj he⟩

def walkRed (w : Nat → Nat → Nat) (p : Pair n) : Finset (Edge n m) :=
  (below (H m) (w p.1.val p.2.val)).map
    ⟨fun t => .walk p (evenSlot t), fun _ _ he => Fin.ext (by
      have hs := congrArg Fin.val (Edge.walk.inj he).2
      change 2 * _ = 2 * _ at hs
      omega)⟩

private theorem redLabels_lift (S : Finset (Pair n)) (w : Nat → Nat → Nat) (b : Nat) :
    redLabels (liftBits (m := m) S) w b = fixedRed n m b ∪ S.biUnion (walkRed w) := by
  ext e
  simp only [redLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_biUnion, fixedRed, walkRed, Finset.mem_map, mem_below]
  cases e with
  | ab i | ac i | bc i | link i | spoke i =>
    simp [paint]
  | fixed i =>
    simp only [paint,liftBits,decide_eq_true_eq,true_and,reduceCtorEq,and_false,
      exists_false,or_false]
    change i.val < b ↔ ∃ a : Fin m, a.val < b ∧ Edge.fixed a = (Edge.fixed i : Edge n m)
    simp [Edge.fixed.injEq]
  | walk p s =>
    simp only [liftBits, paint, walkTake, decide_eq_true_eq, reduceCtorEq, and_false,
      exists_false, false_or]
    constructor
    · rintro ⟨hs, hQ, hpar, hw⟩
      have hp : p ∈ S := of_decide_eq_true (by simpa only [if_pos hpar] using hs)
      let t : Fin (H m) := ⟨s.val/2, by unfold Q at hQ; omega⟩
      exact ⟨p,hp,t,hw,congrArg (Edge.walk p) (Fin.ext (by
        change 2*(s.val/2)=s.val; omega))⟩
    · rintro ⟨p',hp',t,ht,he⟩
      cases he
      have hb := t.isLt
      have hh : (evenSlot t).val < Q m := by change 2*t.val < 2*H m; omega
      have hp : (evenSlot t).val % 2 = 0 := by change (2*t.val)%2 = 0; omega
      have hd : (evenSlot t).val / 2 = t.val := by change (2*t.val)/2 = t.val; omega
      simp [hp, hh, hd, ht, hp']

theorem red_count {a : Nat → Nat → Bool} {P : Equiv.Perm (Fin (K n m))}
    (hP : Perfect a P) (w : Nat → Nat → Nat) (b : Nat) (hb : b ≤ m)
    (hw : ∀ p : Pair n, w p.1.val p.2.val ≤ H m) :
    redCount a w b P = b + ∑ p ∈ extract P, w p.1.val p.2.val := by
  have hnorm : selected P = liftBits (extract P) := by
    exact (cover_normal (selected_cover hP) (selected_compatible hP)).trans
      (congrArg liftBits (active_selected P))
  rw [← redLabels_list hP w b, hnorm, redLabels_lift]
  have hdis : Disjoint (fixedRed n m b) ((extract P).biUnion (walkRed (m := m) w)) := by
    refine Finset.disjoint_left.mpr ?_
    simp only [fixedRed, walkRed, Finset.mem_map, Finset.mem_biUnion]
    rintro e ⟨i,hi,rfl⟩ ⟨p,hp,t,ht,he⟩
    cases he
  rw [Finset.card_union_of_disjoint hdis]
  have hpair : ((extract P : Finset (Pair n)) : Set (Pair n)).PairwiseDisjoint
      (walkRed (m := m) w) := by
    intro p hp q hq hn
    refine Finset.disjoint_left.mpr ?_
    simp only [walkRed, Finset.mem_map]
    rintro e ⟨t,ht,rfl⟩ ⟨s,hs,he⟩
    exact hn (Edge.walk.inj he).1.symm
  rw [Finset.card_biUnion hpair]
  simp only [fixedRed, walkRed, Finset.card_map, card_below hb, card_below (hw _)]

end PEqualNP.Outside.L_meta_33617.Gadget
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

lemma nat_comp {u : List Bool → List Bool} {v : List Bool → Nat} (hu : CPTs u) (hv : NCPT v) :
    NCPT (fun s => v (u s)) :=
  str_comp (u := u) (v := fun s => un (v s)) hu hv

lemma test_congr {p q : List Bool → Prop} (hp : Test p) (h : ∀ s, p s ↔ q s) : Test q := by
  obtain ⟨g,hg,hh⟩ := hp
  exact ⟨g,hg, fun s => (hh s).trans (h s)⟩

lemma test_decide {p : List Bool → Prop} [DecidablePred p] (hp : Test p) :
    Test (fun s => decide (p s) = true) :=
  test_congr hp (fun s => (Iff.of_eq (@decide_eq_true_eq (p s) (inferInstance : Decidable (p s)))).symm)

lemma str_pack {u : List Bool → List Bool} {v : List Bool → Nat} (hu : CPTs u) (hv : NCPT v) :
    CPTs (fun s => pairB (u s) (un (v s))) := cpt_pairB2 hu hv

lemma test_bounded {u : List Bool → Nat} {e : List Bool → List Bool}
    {p : List Bool → Nat → Prop} (hu : NCPT u) (he : CPTs e)
    (hp : Test (fun t => p (env t) (idx t))) : Test (fun s => ∃ i < u s, p (e s) i) := by
  classical
  let cell := fun t => if p (env t) (idx t) then [true] else []
  have hl (s : List Bool) (i : Nat) : (cell (pairB (e s) (un i))).length ≤ 1 := by
    unfold cell; split <;> simp
  refine ⟨fun s => tab (u s) 1 (e s) cell, cpt_tab hu (nat_const 1) he
    (str_if hp (cpt_const [true]) (cpt_const [])), fun s => ?_⟩
  change tab (u s) 1 (e s) cell ≠ [] ↔ ∃ i < u s, p (e s) i
  rw [tab_eq _ _ _ _ (fun i _ => hl s i)]
  simp [List.flatMap_eq_nil_iff, cell, env_pack, idx_pack]

def tally (u : Nat) (e : List Bool) (p : List Bool → Nat → Bool) : Nat :=
  ((List.range u).filter (p e)).length

lemma flatMap_single_filter {α : Type} (l : List α) (p : α → Bool) :
    (l.flatMap (fun a => if p a then [true] else [])).length = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

lemma nat_tally {u : List Bool → Nat} {e : List Bool → List Bool}
    {p : List Bool → Nat → Bool} (hu : NCPT u) (he : CPTs e)
    (hp : Test (fun t => p (env t) (idx t) = true)) : NCPT (fun s => tally (u s) (e s) p) := by
  let cell := fun t => if p (env t) (idx t) then [true] else []
  have hl (s : List Bool) (i : Nat) : (cell (pairB (e s) (un i))).length ≤ 1 := by
    unfold cell; split <;> simp
  apply q39 (nat_len (cpt_tab hu (nat_const 1) he (str_if hp (cpt_const [true]) (cpt_const []))))
  intro s
  change un ((tab (u s) 1 (e s) cell).length) = un (tally (u s) (e s) p)
  rw [tab_eq _ _ _ _ (fun i _ => hl s i)]
  simp only [cell, env_pack, idx_pack, flatMap_single_filter, tally]

lemma tally_get {α : Type} (l : List α) (s : List Bool) (p : List Bool → Nat → Bool) (q : α → Bool)
    (h : ∀ i : Fin l.length, p s i.val = q (l.get i)) :
    tally l.length s p = (l.filter q).length := by
  unfold tally
  rw [← range_vals, List.filter_map, List.length_map]
  have hget : (List.finRange l.length).map l.get = l := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  conv_rhs => rw [← hget]
  rw [List.filter_map, List.length_map]
  exact congrArg List.length (List.filter_congr (fun i _ => h i))

def bitAt (data : List Bool) (off : Nat) : Bool := data[off]?.getD false

def rowBit (data : List Bool) (width row off : Nat) : Prop := bitAt data (width*row+off) = true

lemma test_rowBit {d : List Bool → List Bool} {w r o : List Bool → Nat}
    (hd : CPTs d) (hw : NCPT w) (hr : NCPT r) (ho : NCPT o) :
    Test (fun s => rowBit (d s) (w s) (r s) (o s)) :=
  test_bit (nat_add (nat_mul hw hr) ho) hd

def bothInBank (data : List Bool) (width row off i j : Nat) : Prop :=
  rowBit data width row (off+i) ∧ rowBit data width row (off+j)

def contained (data : List Bool) (n width row i j : Nat) : Prop :=
  bothInBank data width row 0 i j ∨ bothInBank data width row n i j

lemma test_contained {d : List Bool → List Bool} {n w r i j : List Bool → Nat}
    (hd : CPTs d) (hn : NCPT n) (hw : NCPT w) (hr : NCPT r) (hi : NCPT i) (hj : NCPT j) :
    Test (fun s => contained (d s) (n s) (w s) (r s) (i s) (j s)) := by
  unfold contained bothInBank
  apply_rules [test_or, test_and, test_rowBit, nat_add, nat_const]


abbrev wHard (s : List Bool) : Nat := 2 * inputN s
abbrev wSoft (s : List Bool) : Nat := 2 * inputN s + 1

lemma nat_wHard : NCPT wHard := nat_mul (nat_const 2) nat_inputN
lemma nat_wSoft : NCPT wSoft := nat_add nat_wHard (nat_const 1)

def input2 (s : List Bool) (i j : Nat) : List Bool := pairB (pairB s (un i)) (un j)

def base2 (s : List Bool) := env (env s)
def fst2 (s : List Bool) := idx (env s)
def snd2 (s : List Bool) := idx s

lemma input2_base (s : List Bool) (i j : Nat) : base2 (input2 s i j) = s := by
  simp [base2, input2, env_pack]
lemma input2_fst (s : List Bool) (i j : Nat) : fst2 (input2 s i j) = i := by
  simp [fst2, input2, env_pack, idx_pack]
lemma input2_snd (s : List Bool) (i j : Nat) : snd2 (input2 s i j) = j := by
  simp [snd2, input2, idx_pack]

lemma str_base2 : CPTs base2 := str_comp (u := env) (v := env) str_env str_env
lemma nat_fst2 : NCPT fst2 := nat_comp (u := env) (v := idx) str_env nat_idx
lemma nat_snd2 : NCPT snd2 := nat_idx
lemma str_input2 {u : List Bool → List Bool} {i j : List Bool → Nat}
    (hu : CPTs u) (hi : NCPT i) (hj : NCPT j) : CPTs (fun s => input2 (u s) (i s) (j s)) :=
  str_pack (str_pack hu hi) hj

def hardBans (s : List Bool) (i j : Nat) : Prop :=
  ∃ r < inputH s, contained (hardData s) (inputN s) (wHard s) r i j

noncomputable def allowedInput (s : List Bool) (i j : Nat) : Bool := by
  classical
  exact decide (¬hardBans s i j)

lemma test_allowedInput {u : List Bool → List Bool} {i j : List Bool → Nat}
    (hu : CPTs u) (hi : NCPT i) (hj : NCPT j) :
    Test (fun s => allowedInput (u s) (i s) (j s) = true) := by
  have ht := test_bounded (nat_comp hu nat_inputH) (str_input2 hu hi hj)
    (p := fun t r => contained (hardData (base2 t)) (inputN (base2 t)) (wHard (base2 t)) r (fst2 t) (snd2 t))
    (test_contained (str_comp (str_comp str_env str_base2) cpt_hardData)
      (nat_comp (str_comp str_env str_base2) nat_inputN) (nat_comp (str_comp str_env str_base2) nat_wHard)
      nat_idx (nat_comp str_env nat_fst2) (nat_comp str_env nat_snd2))
  apply test_congr (test_not ht)
  intro s
  simp only [input2_base, input2_fst, input2_snd]
  let p : Prop := hardBans (u s) (i s) (j s)
  change ¬p ↔ @decide (¬p) (@instDecidableNot p (Classical.propDecidable p)) = true
  exact (@decide_eq_true_iff (¬p) (@instDecidableNot p (Classical.propDecidable p))).symm

def overlapping (s : List Bool) (r : Nat) : Prop :=
  ∃ i < inputN s, rowBit (softData s) (wSoft s) r i ∧ rowBit (softData s) (wSoft s) r (inputN s+i)

def labeled (s : List Bool) (r : Nat) : Prop := rowBit (softData s) (wSoft s) r (wHard s)

lemma test_overlapping {u : List Bool → List Bool} {r : List Bool → Nat}
    (hu : CPTs u) (hr : NCPT r) : Test (fun s => overlapping (u s) (r s)) := by
  have ht := test_bounded (nat_comp hu nat_inputN) (str_pack hu hr)
    (p := fun t i => rowBit (softData (env t)) (wSoft (env t)) (idx t) i ∧
      rowBit (softData (env t)) (wSoft (env t)) (idx t) (inputN (env t)+i))
    (by
      have he := str_comp (u := env) (v := env) str_env str_env
      have hD := str_comp (u := fun t => env (env t)) (v := softData) he cpt_softData
      have hW := nat_comp (u := fun t => env (env t)) (v := wSoft) he nat_wSoft
      have hN := nat_comp (u := fun t => env (env t)) (v := inputN) he nat_inputN
      have hR := nat_comp (u := env) (v := idx) str_env nat_idx
      exact test_and (test_rowBit hD hW hR nat_idx)
        (test_rowBit hD hW hR (nat_add hN nat_idx)))
  simpa only [overlapping, env_pack, idx_pack] using ht

lemma test_labeled {u : List Bool → List Bool} {r : List Bool → Nat}
    (hu : CPTs u) (hr : NCPT r) : Test (fun s => labeled (u s) (r s)) := by
  exact test_rowBit (str_comp (u := u) (v := softData) hu cpt_softData)
    (nat_comp (u := u) (v := wSoft) hu nat_wSoft) hr
    (nat_comp (u := u) (v := wHard) hu nat_wHard)

def baseEvent (s : List Bool) (r : Nat) : Prop := overlapping s r ↔ labeled s r

noncomputable def inputBase (s : List Bool) : Nat := by
  classical
  exact tally (inputM s) s (fun s r => decide (baseEvent s r))

lemma nat_inputBase : NCPT inputBase := by
  classical
  unfold inputBase
  apply nat_tally nat_inputM str_id
  apply test_decide
  exact test_congr (test_or (test_and (test_overlapping str_env nat_idx) (test_labeled str_env nat_idx))
    (test_and (test_not (test_overlapping str_env nat_idx)) (test_not (test_labeled str_env nat_idx))))
    (fun s => by unfold baseEvent; tauto)

def marginalEvent (positive : Bool) (s : List Bool) (r i j : Nat) : Prop :=
  ¬overlapping s r ∧ contained (softData s) (inputN s) (wSoft s) r i j ∧
    (labeled s r ↔ positive = true)

noncomputable def marginal (positive : Bool) (s : List Bool) (i j : Nat) : Nat := by
  classical
  exact tally (inputM s) (input2 s i j) (fun p r => decide (marginalEvent positive (base2 p) r (fst2 p) (snd2 p)))

lemma nat_marginal (positive : Bool) {u : List Bool → List Bool} {i j : List Bool → Nat}
    (hu : CPTs u) (hi : NCPT i) (hj : NCPT j) : NCPT (fun s => marginal positive (u s) (i s) (j s)) := by
  classical
  unfold marginal
  apply nat_tally (nat_comp hu nat_inputM) (str_input2 hu hi hj)
  apply test_decide
  have hbase := str_comp (u := env) (v := base2) str_env str_base2
  unfold marginalEvent
  apply test_and (test_not (test_overlapping hbase nat_idx))
  apply test_and (test_contained (str_comp hbase cpt_softData) (nat_comp hbase nat_inputN)
    (nat_comp hbase nat_wSoft) nat_idx (nat_comp str_env nat_fst2) (nat_comp str_env nat_snd2))
  cases positive
  · simp only [Bool.false_eq_true, iff_false]
    exact test_not (test_labeled hbase nat_idx)
  · simp only [iff_true]
    exact test_labeled hbase nat_idx

noncomputable def inputWeight (s : List Bool) (i j : Nat) : Nat :=
  inputM s + 1 + marginal true s i j - marginal false s i j

lemma nat_inputWeight {u : List Bool → List Bool} {i j : List Bool → Nat}
    (hu : CPTs u) (hi : NCPT i) (hj : NCPT j) :
    NCPT (fun s => inputWeight (u s) (i s) (j s)) := by
  unfold inputWeight
  exact nat_sub (nat_add (nat_add (nat_comp (u := u) (v := inputM) hu nat_inputM) (nat_const 1))
    (nat_marginal true hu hi hj)) (nat_marginal false hu hi hj)

lemma marginal_le (positive : Bool) (s : List Bool) (i j : Nat) :
    marginal positive s i j ≤ inputM s := by
  unfold marginal tally
  exact (List.length_filter_le _ _).trans_eq List.length_range

lemma inputWeight_le (s : List Bool) (i j : Nat) : inputWeight s i j ≤ 2 * inputM s + 1 := by
  have := marginal_le true s i j
  unfold inputWeight
  omega

lemma inputBase_le (s : List Bool) : inputBase s ≤ inputM s := by
  unfold inputBase tally
  exact (List.length_filter_le _ _).trans_eq List.length_range

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Machine

lemma bank_len {n : Nat} (t : Finset (Fin n)) : (bank t).length = n := by simp [bank]

lemma bank_hardLeft {n : Nat} (z : Row n) (i : Fin n) :
    (hardRow z)[i.val]? = some (decide (i ∈ z.1)) := by
  rw [hardRow, List.getElem?_append_left (by simpa [bank_len] using i.isLt), bank_get]

lemma bank_hardRight {n : Nat} (z : Row n) (i : Fin n) :
    (hardRow z)[n+i.val]? = some (decide (i ∈ z.2)) := by
  rw [hardRow, List.getElem?_append_right (by simp [bank_len]), bank_len, Nat.add_sub_cancel_left, bank_get]

lemma bank_softLeft {n : Nat} (z : Soft n) (i : Fin n) :
    (softRow z)[i.val]? = some (decide (i ∈ z.1.1)) := by
  rw [softRow, List.getElem?_append_left (by rw [hardRow_len]; have := i.isLt; omega), bank_hardLeft]

lemma bank_softRight {n : Nat} (z : Soft n) (i : Fin n) :
    (softRow z)[n+i.val]? = some (decide (i ∈ z.1.2)) := by
  rw [softRow, List.getElem?_append_left (by rw [hardRow_len]; have := i.isLt; omega), bank_hardRight]

lemma bank_softLabel {n : Nat} (z : Soft n) : (softRow z)[2*n]? = some z.2 := by
  rw [softRow, List.getElem?_append_right (by simp [hardRow_len]), hardRow_len, Nat.sub_self]
  rfl

lemma hardBit_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (r : Fin hard.length)
    (off : Nat) (h : off < 2*n) :
    rowBit (hardData (query n hard soft ++ [])) (2*n) r.val off ↔
    ((hardRow (hard.get r))[off]?).getD false = true := by
  simp only [rowBit, bitAt, hardData_query]
  rw [chunk_get hard hardRow (2*n) hardRow_len _ r.val r.isLt off h]
  rfl

lemma softBit_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (r : Fin soft.length)
    (off : Nat) (h : off < 2*n+1) :
    rowBit (softData (query n hard soft ++ [])) (2*n+1) r.val off ↔
    ((softRow (soft.get r))[off]?).getD false = true := by
  simp only [rowBit, bitAt, softData_query]
  rw [chunk_get soft softRow (2*n+1) softRow_len _ r.val r.isLt off h]
  rfl

lemma subset_pair_iff {n : Nat} (i j : Fin n) (B : Finset (Fin n)) :
    ({i,j} : Finset (Fin n)) ⊆ B ↔ i ∈ B ∧ j ∈ B := by
  constructor
  · intro h
    exact ⟨h (by simp),h (by simp)⟩
  · rintro ⟨hi,hj⟩ x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton.mp hx]
      exact hj

lemma hardContained_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (r : Fin hard.length) (i j : Fin n) :
    contained (hardData (query n hard soft)) n (2*n) r.val i.val j.val ↔
      ({i,j} : Finset (Fin n)) ⊆ (hard.get r).1 ∨ ({i,j} : Finset (Fin n)) ⊆ (hard.get r).2 := by
  have hi := i.isLt
  have hj := j.isLt
  have h₁ : ∀ x : Fin n,
      rowBit (hardData (query n hard soft)) (2*n) r.val x.val ↔ x ∈ (hard.get r).1 := by
    intro x
    have hx := x.isLt
    simpa [bank_hardLeft] using hardBit_query hard soft r x.val (by omega)
  have h₂ : ∀ x : Fin n,
      rowBit (hardData (query n hard soft)) (2*n) r.val (n+x.val) ↔ x ∈ (hard.get r).2 := by
    intro x
    have hx := x.isLt
    simpa [bank_hardRight] using hardBit_query hard soft r (n+x.val) (by omega)
  simp only [contained, bothInBank, Nat.zero_add, h₁, h₂, subset_pair_iff]

lemma softContained_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (r : Fin soft.length) (i j : Fin n) :
    contained (softData (query n hard soft)) n (2*n+1) r.val i.val j.val ↔
      SoftScore.hits (i,j) (soft.get r) := by
  have h₁ : ∀ x : Fin n,
      rowBit (softData (query n hard soft)) (2*n+1) r.val x.val ↔ x ∈ (soft.get r).1.1 := by
    intro x
    have hx := x.isLt
    simpa [bank_softLeft] using softBit_query hard soft r x.val (by omega)
  have h₂ : ∀ x : Fin n,
      rowBit (softData (query n hard soft)) (2*n+1) r.val (n+x.val) ↔ x ∈ (soft.get r).1.2 := by
    intro x
    have hx := x.isLt
    simpa [bank_softRight] using softBit_query hard soft r (n+x.val) (by omega)
  simp only [contained, bothInBank, Nat.zero_add, h₁, h₂, SoftScore.hits, SoftScore.ends,
    Prod.fst, Prod.snd, subset_pair_iff]

lemma allowedInput_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (i j : Fin n) :
    allowedInput (query n hard soft) i.val j.val = true ↔
      ∀ z ∈ hard, ¬(({i,j} : Finset (Fin n)) ⊆ z.1) ∧ ¬(({i,j} : Finset (Fin n)) ⊆ z.2) := by
  classical
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hh : inputH (query n hard soft) = hard.length := by simpa using inputH_query hard soft []
  simp only [allowedInput, decide_eq_true_eq, hardBans, wHard, hn, hh, not_exists, not_and]
  constructor
  · intro h z hz
    obtain ⟨r,hr⟩ := List.mem_iff_get.mp hz
    rw [← hr]
    have hh' := h r.val r.isLt
    exact not_or.mp (fun hh => hh' ((hardContained_query hard soft r i j).mpr hh))
  · intro h r hr hc
    let r' : Fin hard.length := ⟨r,hr⟩
    have hh := h (hard.get r') (List.get_mem _ _)
    exact (not_or.mpr hh) ((hardContained_query hard soft r' i j).mp hc)

lemma overlapping_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (r : Fin soft.length) : overlapping (query n hard soft) r.val ↔
      ¬Disjoint (soft.get r).1.1 (soft.get r).1.2 := by
  classical
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  simp only [overlapping, wSoft, hn, Finset.disjoint_left, not_forall, not_not, not_imp]
  constructor
  · rintro ⟨i,hi,hl,hr⟩
    let x : Fin n := ⟨i,hi⟩
    have h₁ := softBit_query hard soft r x.val (by omega)
    have h₂ := softBit_query hard soft r (n+x.val) (by omega)
    simp only [List.append_nil, bank_softLeft, bank_softRight, Option.getD_some, decide_eq_true_eq] at h₁ h₂
    exact ⟨x,h₁.mp hl,h₂.mp hr⟩
  · rintro ⟨x,hl,hr⟩
    have hx := x.isLt
    have h₁ := softBit_query hard soft r x.val (by omega)
    have h₂ := softBit_query hard soft r (n+x.val) (by omega)
    simp only [List.append_nil, bank_softLeft, bank_softRight, Option.getD_some, decide_eq_true_eq] at h₁ h₂
    exact ⟨x.val,hx,h₁.mpr hl,h₂.mpr hr⟩

lemma labeled_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (r : Fin soft.length) : labeled (query n hard soft) r.val ↔ (soft.get r).2 = true := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  simp only [labeled, wSoft, wHard, hn]
  simpa [bank_softLabel] using softBit_query hard soft r (2*n) (by omega)

lemma base_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) :
    inputBase (query n hard soft) = SoftScore.base soft := by
  classical
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  unfold inputBase SoftScore.base
  rw [hm]
  apply tally_get
  intro r
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, baseEvent, overlapping_query, labeled_query]
  cases (soft.get r).2 <;> simp

lemma marginal_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (i j : Fin n) (b : Bool) :
    marginal b (query n hard soft) i.val j.val = if b then SoftScore.pos soft (i,j) else SoftScore.neg soft (i,j) := by
  classical
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  unfold marginal SoftScore.pos SoftScore.neg
  rw [hm]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply tally_get <;> intro r <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq, marginalEvent, input2_base, input2_fst, input2_snd, overlapping_query,
      not_not, wSoft, hn, softContained_query, labeled_query, SoftScore.lists, Finset.mem_singleton,
      forall_eq, Bool.and_eq_true, Bool.not_eq_true'] <;>
    cases (soft.get r).2 <;> simp [and_left_comm, and_comm, and_assoc]

lemma weight_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (i j : Fin n) :
    inputWeight (query n hard soft) i.val j.val =
      soft.length + 1 + SoftScore.pos soft (i,j) - SoftScore.neg soft (i,j) := by
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  simp [inputWeight, hm, marginal_query]

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Machine

open Lib.Machines Lib.Universal

abbrev inputWidth (s : List Bool) : Nat := 2 * inputM s + 1
abbrev inputQ (s : List Bool) : Nat := 2 * inputWidth s
abbrev inputK (s : List Bool) : Nat := 4 * inputN s + (inputN s * inputN s) * inputQ s + 2 * inputM s

lemma nat_inputWidth : NCPT inputWidth := nat_add (nat_mul (nat_const 2) nat_inputM) (nat_const 1)
lemma nat_inputQ : NCPT inputQ := nat_mul (nat_const 2) nat_inputWidth
lemma nat_inputK : NCPT inputK := by
  unfold inputK
  apply_rules [nat_add, nat_mul, nat_const, nat_inputN, nat_inputM, nat_inputQ]

lemma test_bounded_two {u : List Bool → List Bool} {n m : List Bool → Nat}
    {p : List Bool → Nat → Nat → Prop} (hu : CPTs u) (hn : NCPT n) (hm : NCPT m)
    (hp : Test (fun z => p (base2 z) (fst2 z) (snd2 z))) :
    Test (fun s => ∃ i < n (u s), ∃ j < m (u s), p (u s) i j) := by
  have h₁ := test_bounded (nat_comp str_env hm) str_id
    (p := fun z j => p (env z) (idx z) j) hp
  have h₂ := test_bounded (nat_comp hu hn) hu
    (p := fun z i => ∃ j < m z, p z i j) h₁
  exact h₂

def joined (x y u v : Nat) : Prop := (x = u ∧ y = v) ∨ (x = v ∧ y = u)

lemma test_joined {x y u v : List Bool → Nat} (hx : NCPT x) (hy : NCPT y) (hu : NCPT u) (hv : NCPT v) :
    Test (fun s => joined (x s) (y s) (u s) (v s)) :=
  test_or (test_and (test_eq hx hu) (test_eq hy hv)) (test_and (test_eq hx hv) (test_eq hy hu))

def triA (s : List Bool) (i : Nat) : Nat := inputN s + 3*i

def atCore (s : List Bool) (x y i : Nat) : Prop :=
  let a := triA s i
  joined x y a (a+1) ∨ joined x y a (a+2) ∨ joined x y (a+1) (a+2) ∨
  (i+1 < inputN s ∧ joined x y (a+2) (a+3)) ∨ joined x y i (a+1)

lemma test_atCore {u : List Bool → List Bool} {x y i : List Bool → Nat}
    (hu : CPTs u) (hx : NCPT x) (hy : NCPT y) (hi : NCPT i) :
    Test (fun s => atCore (u s) (x s) (y s) (i s)) := by
  have hn := nat_comp (u := u) (v := inputN) hu nat_inputN
  have ha : NCPT (fun s => triA (u s) (i s)) := nat_add hn (nat_mul (nat_const 3) hi)
  have ha1 := nat_add ha (nat_const 1)
  have ha2 := nat_add ha (nat_const 2)
  have ha3 := nat_add ha (nat_const 3)
  exact test_or (test_joined hx hy ha ha1)
    (test_or (test_joined hx hy ha ha2)
      (test_or (test_joined hx hy ha1 ha2)
        (test_or (test_and (test_lt (nat_add hi (nat_const 1)) hn)
          (test_joined hx hy ha2 ha3)) (test_joined hx hy hi ha1))))

def padA (s : List Bool) (i : Nat) : Nat := inputK s - 2 * inputM s + 2*i

def atPad (s : List Bool) (x y i : Nat) : Prop :=
  joined x y (padA s i) (padA s i+1)

lemma test_atPad {u : List Bool → List Bool} {x y i : List Bool → Nat}
    (hu : CPTs u) (hx : NCPT x) (hy : NCPT y) (hi : NCPT i) :
    Test (fun s => atPad (u s) (x s) (y s) (i s)) := by
  have hk := nat_comp (u := u) (v := inputK) hu nat_inputK
  have hm := nat_comp (u := u) (v := inputM) hu nat_inputM
  have hp : NCPT (fun s => padA (u s) (i s)) :=
    nat_add (nat_sub hk (nat_mul (nat_const 2) hm)) (nat_mul (nat_const 2) hi)
  exact test_joined hx hy hp (nat_add hp (nat_const 1))

def pathA (s : List Bool) (i j : Nat) : Nat :=
  4 * inputN s + (i * inputN s + j) * inputQ s

lemma nat_pathA {u : List Bool → List Bool} {i j : List Bool → Nat}
    (hu : CPTs u) (hi : NCPT i) (hj : NCPT j) : NCPT (fun s => pathA (u s) (i s) (j s)) := by
  have hn := nat_comp (u := u) (v := inputN) hu nat_inputN
  have hq := nat_comp (u := u) (v := inputQ) hu nat_inputQ
  exact nat_add (nat_mul (nat_const 4) hn) (nat_mul (nat_add (nat_mul hi hn) hj) hq)

def atWalk (s : List Bool) (x y i j t : Nat) : Prop :=
  let a := pathA s i j
  let valid := i < j ∧ allowedInput s i j = true
  (t = 0 ∧ valid ∧ joined x y i a) ∨
  (t = inputQ s ∧ valid ∧ joined x y j (a+(inputQ s-1))) ∨
  (t ≠ 0 ∧ t ≠ inputQ s ∧ joined x y (a+(t-1)) (a+t))

lemma test_atWalk {u : List Bool → List Bool} {x y i j t : List Bool → Nat}
    (hu : CPTs u) (hx : NCPT x) (hy : NCPT y) (hi : NCPT i) (hj : NCPT j) (ht : NCPT t) :
    Test (fun s => atWalk (u s) (x s) (y s) (i s) (j s) (t s)) := by
  have hq := nat_comp (u := u) (v := inputQ) hu nat_inputQ
  have ha := nat_pathA hu hi hj
  have hv := test_and (test_lt hi hj) (test_allowedInput hu hi hj)
  have h0 : Test (fun s => t s = 0) := test_eq ht (nat_const 0)
  have hQ : Test (fun s => t s = inputQ (u s)) := test_eq ht hq
  exact test_or (test_and h0 (test_and hv (test_joined hx hy hi ha)))
    (test_or (test_and hQ (test_and hv
      (test_joined hx hy hj (nat_add ha (nat_sub hq (nat_const 1))))))
      (test_and (test_not h0) (test_and (test_not hQ)
        (test_joined hx hy (nat_add ha (nat_sub ht (nat_const 1))) (nat_add ha ht)))))

def walkRange (red : Bool) (s : List Bool) : Nat := if red then inputWidth s else inputQ s + 1

def coloredWalk (red : Bool) (s : List Bool) (x y i j t : Nat) : Prop :=
  if red then atWalk s x y i j (2*t) ∧ t < inputWeight s i j else atWalk s x y i j t

lemma nat_walkRange (red : Bool) : NCPT (walkRange red) := by
  cases red
  · exact nat_add nat_inputQ (nat_const 1)
  · exact nat_inputWidth

lemma test_coloredWalk (red : Bool) {u : List Bool → List Bool} {x y i j t : List Bool → Nat}
    (hu : CPTs u) (hx : NCPT x) (hy : NCPT y) (hi : NCPT i) (hj : NCPT j) (ht : NCPT t) :
    Test (fun s => coloredWalk red (u s) (x s) (y s) (i s) (j s) (t s)) := by
  cases red
  · exact test_atWalk hu hx hy hi hj ht
  · exact test_and (test_atWalk hu hx hy hi hj (nat_mul (nat_const 2) ht))
      (test_lt ht (nat_inputWeight hu hi hj))

def someWalk (red : Bool) (s : List Bool) (x y : Nat) : Prop :=
  ∃ i < inputN s, ∃ j < inputN s, ∃ t < walkRange red s, coloredWalk red s x y i j t

lemma test_someWalk (red : Bool) {u : List Bool → List Bool} {x y : List Bool → Nat}
    (hu : CPTs u) (hx : NCPT x) (hy : NCPT y) : Test (fun s => someWalk red (u s) (x s) (y s)) := by
  have hu' := str_input2 hu hx hy
  have hn := nat_comp str_base2 nat_inputN
  let p (z : List Bool) (i j : Nat) := ∃ t < walkRange red (base2 z),
    coloredWalk red (base2 z) (fst2 z) (snd2 z) i j t
  have hroot := str_comp (str_comp str_env str_base2) str_base2
  have hlast := str_comp str_env str_base2
  have hlocal : Test (fun z => p (base2 z) (fst2 z) (snd2 z)) :=
    test_bounded (nat_comp (str_comp str_base2 str_base2) (nat_walkRange red)) str_id
      (p := fun z t => coloredWalk red (base2 (base2 z)) (fst2 (base2 z)) (snd2 (base2 z)) (fst2 z) (snd2 z) t)
      (test_coloredWalk red hroot (nat_comp hlast nat_fst2) (nat_comp hlast nat_snd2)
        (nat_comp str_env nat_fst2) (nat_comp str_env nat_snd2) nat_idx)
  have h := test_bounded_two hu' hn hn hlocal
  simpa only [p, someWalk, input2_base, input2_fst, input2_snd] using h

def graphPred (s : List Bool) (x y : Nat) : Prop :=
  (∃ i < inputN s, atCore s x y i) ∨ (∃ i < inputM s, atPad s x y i) ∨ someWalk false s x y

def colorPred (s : List Bool) (x y : Nat) : Prop :=
  (∃ i < inputM s, i < inputBase s ∧ atPad s x y i) ∨ someWalk true s x y

lemma test_graphPred : Test (fun z => graphPred (base2 z) (fst2 z) (snd2 z)) := by
  have he := str_comp str_env str_base2
  have hx := nat_comp str_env nat_fst2
  have hy := nat_comp str_env nat_snd2
  unfold graphPred
  exact test_or (test_bounded (nat_comp str_base2 nat_inputN) str_id
    (p := fun z i => atCore (base2 z) (fst2 z) (snd2 z) i) (test_atCore he hx hy nat_idx))
    (test_or (test_bounded (nat_comp str_base2 nat_inputM) str_id
      (p := fun z i => atPad (base2 z) (fst2 z) (snd2 z) i) (test_atPad he hx hy nat_idx))
      (test_someWalk false str_base2 nat_fst2 nat_snd2))

lemma test_colorPred : Test (fun z => colorPred (base2 z) (fst2 z) (snd2 z)) := by
  have he := str_comp str_env str_base2
  have hx := nat_comp str_env nat_fst2
  have hy := nat_comp str_env nat_snd2
  unfold colorPred
  exact test_or (test_bounded (nat_comp str_base2 nat_inputM) str_id
    (p := fun z i => i < inputBase (base2 z) ∧ atPad (base2 z) (fst2 z) (snd2 z) i)
    (test_and (test_lt nat_idx (nat_comp he nat_inputBase)) (test_atPad he hx hy nat_idx)))
    (test_someWalk true str_base2 nat_fst2 nat_snd2)

lemma flatMap_bound {α β : Type} (xs : List α) (f : α → List β) (b : Nat)
    (h : ∀ a ∈ xs, (f a).length ≤ b) : (xs.flatMap f).length ≤ b*xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hr := ih (fun t h' => h t (by simp [h']))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

lemma cpt_pairs {k : List Bool → Nat} {cell : List Bool → List Bool} (hk : NCPT k) (hc : CPTs cell)
    (hcell : ∀ s i j, (cell (input2 s i j)).length ≤ 2) :
    CPTs (fun s => (pairs (k s)).flatMap (fun z => cell (input2 s z.1.val z.2.val))) := by
  let inner : List Bool → List Bool := fun z => if fst2 z < snd2 z then cell z else []
  let outer : List Bool → List Bool := fun z => tab (k (env z)) 2 z inner
  have hinner : CPTs inner := str_if (test_lt nat_fst2 nat_snd2) hc (cpt_const [])
  have houter : CPTs outer := cpt_tab (nat_comp str_env hk) (nat_const 2) str_id hinner
  refine q39 (cpt_tab hk (nat_mul (nat_const 2) hk) str_id houter) (fun s => ?_)
  change tab (k s) (2*k s) s outer = _
  have hentry (i j : Nat) : (inner (input2 s i j)).length ≤ 2 := by
    simp only [inner, input2_fst, input2_snd]
    split
    · exact hcell s i j
    · simp
  have htab (i : Nat) : outer (pairB s (un i)) =
      (List.range (k s)).flatMap (fun j => inner (input2 s i j)) := by
    dsimp only [outer]
    rw [env_pack, tab_eq _ _ _ _ (fun j _ => hentry i j)]
    rfl
  have hrow (i : Nat) : (outer (pairB s (un i))).length ≤ 2*k s := by
    rw [htab]
    simpa only [List.length_range] using
      (flatMap_bound (List.range (k s)) (fun j => inner (input2 s i j)) 2
        (fun j _ => hentry i j))
  let f (i j : Nat) := cell (input2 s i j)
  change tab (k s) (2*k s) s outer = (pairs (k s)).flatMap (fun e => f e.1.val e.2.val)
  rw [tab_eq _ _ _ _ (fun i _ => hrow i), pairs_flatMap_nat (k s) f]
  apply List.flatMap_congr
  intro i _
  rw [htab]
  apply List.flatMap_congr
  intro j _
  simp only [f, inner, input2_fst, input2_snd]

def hardOverlap (s : List Bool) : Prop :=
  ∃ r < inputH s, ∃ i < inputN s,
    rowBit (hardData s) (wHard s) r i ∧ rowBit (hardData s) (wHard s) r (inputN s+i)

lemma test_hardOverlap : Test hardOverlap := by
  have hd := str_comp (u := base2) (v := hardData) str_base2 cpt_hardData
  have hw := nat_comp (u := base2) (v := wHard) str_base2 nat_wHard
  have hn := nat_comp (u := base2) (v := inputN) str_base2 nat_inputN
  exact test_bounded_two str_id nat_inputH nat_inputN
    (test_and (test_rowBit hd hw nat_fst2 nat_snd2)
      (test_rowBit hd hw nat_fst2 (nat_add hn nat_snd2)))

lemma hardOverlap_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) :
    hardOverlap (query n hard soft) ↔ ¬ ∀ z ∈ hard, Disjoint z.1 z.2 := by
  classical
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hh : inputH (query n hard soft) = hard.length := by simpa using inputH_query hard soft []
  simp only [hardOverlap, wHard, hn, hh, Finset.disjoint_left, not_forall, not_not]
  constructor
  · rintro ⟨r,hr,i,hi,hl,hr'⟩
    let j : Fin hard.length := ⟨r,hr⟩
    let x : Fin n := ⟨i,hi⟩
    have h₁ := hardBit_query hard soft j x.val (by omega)
    have h₂ := hardBit_query hard soft j (n+x.val) (by omega)
    simp only [List.append_nil, bank_hardLeft, bank_hardRight, Option.getD_some, decide_eq_true_eq] at h₁ h₂
    exact ⟨hard.get j, List.get_mem _ _, x, h₁.mp hl, h₂.mp hr'⟩
  · rintro ⟨z,hz,x,hl,hr⟩
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hz
    have hx := x.isLt
    have h₁ := hardBit_query hard soft j x.val (by omega)
    have h₂ := hardBit_query hard soft j (n+x.val) (by omega)
    simp only [List.append_nil, bank_hardLeft, bank_hardRight, Option.getD_some, decide_eq_true_eq] at h₁ h₂
    exact ⟨j.val,j.isLt,x.val,hx,h₁.mpr hl,h₂.mpr hr⟩

noncomputable def writeCell (s : List Bool) : List Bool := by
  classical
  exact [decide (graphPred (base2 s) (fst2 s) (snd2 s)), decide (colorPred (base2 s) (fst2 s) (snd2 s))]

noncomputable def write (s : List Bool) : List Bool := by
  classical
  exact if hardOverlap s then hdr 1
    else hdr (inputK s) ++ (pairs (inputK s)).flatMap (fun z => writeCell (input2 s z.1.val z.2.val))

lemma cpt_write : CPTs write := by
  classical
  unfold write
  apply str_if test_hardOverlap (cpt_const (hdr 1))
  apply cpt_app2 (cpt_app2 nat_inputK (cpt_const [false]))
  apply cpt_pairs nat_inputK
  · exact cpt_app2 (str_bit test_graphPred) (str_bit test_colorPred)
  · simp [writeCell]

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Machine

lemma inputQ_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) :
    inputQ (query n hard soft) = Gadget.Q soft.length := by
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  simp only [inputQ, inputWidth, hm]

lemma inputK_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) :
    inputK (query n hard soft) = Gadget.K n soft.length := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  simp only [inputK, hn, hm, inputQ_query, Gadget.K]

lemma atCore_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (x y : Nat) :
    (∃ i < inputN (query n hard soft), atCore (query n hard soft) x y i) ↔
    (∃ i : Fin n, Gadget.joins x y (Gadget.indices (.ab i : Gadget.Edge n soft.length)) ∨
      Gadget.joins x y (Gadget.indices (.ac i : Gadget.Edge n soft.length)) ∨
      Gadget.joins x y (Gadget.indices (.bc i : Gadget.Edge n soft.length)) ∨
      (∃ j : Fin (n-1), j.val = i.val ∧ Gadget.joins x y (Gadget.indices (.link j : Gadget.Edge n soft.length))) ∨
      Gadget.joins x y (Gadget.indices (.spoke i : Gadget.Edge n soft.length))) := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  simp only [atCore, triA, hn, Gadget.indices, Gadget.ends, Gadget.index_tri, Gadget.index_orig,
    Gadget.leftLink_val, Gadget.rightLink_val, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero]
  have hlink (i : Nat) :
      (i+1 < n ∧ joined x y (n+3*i+2) (n+3*i+3)) ↔
        ∃ j : Fin (n-1), j.val = i ∧
        Gadget.joins x y (n+3*j.val+2, n+3*(j.val+1)) := by
    constructor
    · rintro ⟨hi,h⟩
      refine ⟨⟨i,by omega⟩,rfl,?_⟩
      simpa [joined, Gadget.joins, Nat.mul_add, Nat.add_assoc] using h
    · rintro ⟨j,rfl,h⟩
      refine ⟨by have := j.isLt; omega,?_⟩
      simpa [joined, Gadget.joins, Nat.mul_add, Nat.add_assoc] using h
  simp only [hlink]
  simp only [joined, Gadget.joins]
  exact ⟨fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩, fun ⟨i,h⟩ => ⟨i.val,i.isLt,h⟩⟩

lemma atPad_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (x y : Nat) (i : Fin soft.length) :
    atPad (query n hard soft) x y i.val ↔
      Gadget.joins x y (Gadget.indices (.fixed i : Gadget.Edge n soft.length)) := by
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  have hp : padA (query n hard soft) i.val = 4*n + (n*n)*Gadget.Q soft.length + 2*i.val := by
    rw [padA, inputK_query, hm, Gadget.K]
    omega
  change joined x y (padA (query n hard soft) i.val) (padA (query n hard soft) i.val + 1) ↔
    Gadget.joins x y ((Gadget.index n soft.length (Gadget.pad i 0)).val,
      (Gadget.index n soft.length (Gadget.pad i 1)).val)
  rw [hp, Gadget.index_pad, Gadget.index_pad, Fin.val_zero, Fin.val_one, Nat.add_zero] <;> rfl

lemma atWalk_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (x y : Nat) (p : Fin n × Fin n) (t : Fin (Gadget.Q soft.length+1)) :
    atWalk (query n hard soft) x y p.1.val p.2.val t.val ↔
      Gadget.live (allowedInput (query n hard soft)) (.walk p t) = true ∧
      Gadget.joins x y (Gadget.indices (.walk p t)) := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hQ : Gadget.Q soft.length ≠ 0 := by unfold Gadget.Q Gadget.H; omega
  have hv : Gadget.allowed (allowedInput (query n hard soft)) p = true ↔
      p.1.val < p.2.val ∧ allowedInput (query n hard soft) p.1.val p.2.val = true := by
    simp only [Gadget.allowed, Bool.and_eq_true_iff, decide_eq_true_eq, Fin.lt_def]
  change atWalk (query n hard soft) x y p.1.val p.2.val t.val ↔
    (if t.val = 0 ∨ t.val = Gadget.Q soft.length then
      Gadget.allowed (allowedInput (query n hard soft)) p else true) = true ∧
    Gadget.joins x y ((Gadget.index n soft.length (Gadget.walkEnds p t).1).val,
      (Gadget.index n soft.length (Gadget.walkEnds p t).2).val)
  simp only [atWalk, pathA, hn, inputQ_query]
  by_cases h₀ : t.val = 0
  · have ht : t.val ≠ Gadget.Q soft.length := by rw [h₀]; exact Ne.symm hQ
    rw [Gadget.walkEnds, dif_pos h₀]
    simp only [Prod.fst, Prod.snd, Gadget.index_orig, Gadget.index_path,
      show (Gadget.first soft.length).val = 0 from rfl, Nat.add_zero]
    simp only [h₀, ht, true_or, if_true, true_and, false_and, or_false, false_or,
      not_true_eq_false, hv, and_assoc, joined, Gadget.joins]
    simp [Ne.symm hQ]
  · by_cases ht : t.val = Gadget.Q soft.length
    · rw [Gadget.walkEnds, dif_neg h₀, dif_pos ht]
      simp only [Prod.fst, Prod.snd, Gadget.index_orig, Gadget.index_path,
        show (Gadget.last soft.length).val = Gadget.Q soft.length - 1 from rfl]
      simp only [h₀, ht, or_true, if_true, true_and, false_and, or_false, false_or,
        not_true_eq_false, hv, and_assoc, joined, Gadget.joins]
      simp [hQ]
    · rw [Gadget.walkEnds, dif_neg h₀, dif_neg ht]
      simp only [Prod.fst, Prod.snd, Gadget.index_path]
      simp only [h₀, ht, false_or, if_false, true_and, false_and, not_false_eq_true,
        eq_self, joined, Gadget.joins]
      simp [h₀, ht]

lemma someWalk_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (x y : Nat) :
    someWalk false (query n hard soft) x y ↔
      ∃ p : Fin n × Fin n, ∃ t : Fin (Gadget.Q soft.length+1),
        Gadget.live (allowedInput (query n hard soft)) (.walk p t) = true ∧
          Gadget.joins x y (Gadget.indices (.walk p t)) := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  simp only [someWalk, walkRange, coloredWalk, Bool.false_eq_true, ↓reduceIte, hn, inputQ_query]
  constructor
  · rintro ⟨i,hi,j,hj,t,ht,hh⟩
    exact ⟨(⟨i,hi⟩,⟨j,hj⟩),⟨t,ht⟩,(atWalk_query hard soft x y _ _).mp hh⟩
  · rintro ⟨p,t,hh⟩
    exact ⟨p.1.val,p.1.isLt,p.2.val,p.2.isLt,t.val,t.isLt,(atWalk_query hard soft x y p t).mpr hh⟩

lemma someWalk_red_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (x y : Nat) :
    someWalk true (query n hard soft) x y ↔
      ∃ p : Fin n × Fin n, ∃ t : Fin (Gadget.Q soft.length+1),
        Gadget.live (allowedInput (query n hard soft)) (.walk p t) = true ∧
        Gadget.paint (inputWeight (query n hard soft)) (inputBase (query n hard soft)) (.walk p t) = true ∧
        Gadget.joins x y (Gadget.indices (.walk p t)) := by
  have hn : inputN (query n hard soft) = n := by simpa using inputN_query hard soft []
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  simp only [someWalk, walkRange, coloredWalk, ↓reduceIte, hn, inputWidth, hm]
  constructor
  · rintro ⟨i,hi,j,hj,t,ht,hw,hc⟩
    let u : Fin (Gadget.Q soft.length+1) := ⟨2*t,by unfold Gadget.Q Gadget.H; omega⟩
    obtain ⟨ha,hxy⟩ := (atWalk_query hard soft x y (⟨i,hi⟩,⟨j,hj⟩) u).mp hw
    refine ⟨_,u,ha,?_,hxy⟩
    simp only [Gadget.paint, decide_eq_true_eq, u, Gadget.Q, Gadget.H]
    omega
  · rintro ⟨p,u,ha,hc,hxy⟩
    simp only [Gadget.paint, decide_eq_true_eq, Gadget.Q, Gadget.H] at hc
    have ht := hc.1
    have he := hc.2.1
    have hu : 2 * (u.val / 2) = u.val := by omega
    refine ⟨p.1.val,p.1.isLt,p.2.val,p.2.isLt,u.val/2,by omega,?_,hc.2.2⟩
    rw [hu]
    exact (atWalk_query hard soft x y p u).mpr ⟨ha,hxy⟩

lemma graphPred_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (x y : Nat) :
    @decide (graphPred (query n hard soft) x y) (Classical.propDecidable _) =
      Gadget.graph n soft.length (allowedInput (query n hard soft)) x y := by
  classical
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, graphPred, Gadget.graph, atCore_query, someWalk_query, hm]
  constructor
  · rintro (⟨i,h|h|h|⟨j,_,h⟩|h⟩ | ⟨i,hi,h⟩ | ⟨p,t,ha,hxy⟩)
    · exact ⟨.ab i,rfl,h⟩
    · exact ⟨.ac i,rfl,h⟩
    · exact ⟨.bc i,rfl,h⟩
    · exact ⟨.link j,rfl,h⟩
    · exact ⟨.spoke i,rfl,h⟩
    · exact ⟨.fixed ⟨i,hi⟩,rfl,(atPad_query hard soft x y ⟨i,hi⟩).mp h⟩
    · exact ⟨.walk p t,ha,hxy⟩
  · rintro ⟨e,ha,hxy⟩
    cases e with
    | ab i => exact Or.inl ⟨i,Or.inl hxy⟩
    | ac i => exact Or.inl ⟨i,Or.inr (Or.inl hxy)⟩
    | bc i => exact Or.inl ⟨i,Or.inr (Or.inr (Or.inl hxy))⟩
    | link i => exact Or.inl ⟨Gadget.leftLink i,Or.inr (Or.inr (Or.inr (Or.inl ⟨i,rfl,hxy⟩)))⟩
    | spoke i => exact Or.inl ⟨i,Or.inr (Or.inr (Or.inr (Or.inr hxy)))⟩
    | fixed i => exact Or.inr (Or.inl ⟨i.val,i.isLt,(atPad_query hard soft x y i).mpr hxy⟩)
    | walk p t => exact Or.inr (Or.inr ⟨p,t,ha,hxy⟩)

lemma colorPred_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n)) (x y : Nat) :
    @decide (colorPred (query n hard soft) x y) (Classical.propDecidable _) =
      Gadget.color n soft.length (allowedInput (query n hard soft)) (inputWeight (query n hard soft))
        (inputBase (query n hard soft)) x y := by
  classical
  have hm : inputM (query n hard soft) = soft.length := by simpa using inputM_query hard soft []
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, colorPred, Gadget.color, someWalk_red_query, hm]
  constructor
  · rintro (⟨i,hi,hb,h⟩ | ⟨p,t,ha,hc,hxy⟩)
    · exact ⟨.fixed ⟨i,hi⟩,rfl,by simpa [Gadget.paint] using hb,(atPad_query hard soft x y ⟨i,hi⟩).mp h⟩
    · exact ⟨.walk p t,ha,hc,hxy⟩
  · rintro ⟨e,ha,hc,hxy⟩
    cases e with
    | fixed i => exact Or.inl ⟨i.val,i.isLt,by simpa [Gadget.paint] using hc,(atPad_query hard soft x y i).mpr hxy⟩
    | walk p t => exact Or.inr ⟨p,t,ha,hc,hxy⟩
    | _ => simp [Gadget.paint] at hc

lemma write_query {n : Nat} (hard : List (Row n)) (soft : List (Soft n))
    (hd : ∀ z ∈ hard, Disjoint z.1 z.2) :
    write (query n hard soft) =
      paint (Gadget.K n soft.length) (Gadget.G n soft.length (allowedInput (query n hard soft)))
        (Gadget.R n soft.length (allowedInput (query n hard soft)) (inputWeight (query n hard soft))
          (inputBase (query n hard soft))) := by
  classical
  have h : ¬hardOverlap (query n hard soft) := fun h => (hardOverlap_query hard soft).mp h hd
  simp only [write, if_neg h]
  refine (congrArg
    (fun k => hdr k ++ (pairs k).flatMap (fun e => writeCell (input2 (query n hard soft) e.1.val e.2.val)))
    (inputK_query hard soft)).trans ?_
  unfold paint
  apply congrArg (List.append (hdr (Gadget.K n soft.length)))
  apply List.flatMap_congr
  intro e _
  simp only [writeCell, input2_base, input2_fst, input2_snd, graphPred_query, colorPred_query, Gadget.G, Gadget.R]

end PEqualNP.Outside.L_meta_33617.Machine
namespace PEqualNP.Outside.L_meta_33617.Forward

open CircuitReverse

abbrev Qr := Machine.query

def code {n : Nat} (f : Fn n) : List Bool := (pairs n).map (fun e => obs f (ends e) ∅)

def size {n : Nat} (f : Fn n) : Nat := ((code f).filter id).length

def score {n : Nat} (soft : List (Machine.Soft n)) (f : Fn n) : Nat :=
  (soft.filter (fun t => decide (obs f t.1.1 t.1.2 = t.2))).length

def scode {n : Nat} (S : Finset (Fin n × Fin n)) : List Bool :=
  (pairs n).map (fun e => decide (e ∈ S))

lemma eq_scode {n : Nat} {f : Fn n} {S : Finset (Fin n × Fin n)}
    (h : Corresponds f S) : code f = scode S :=
  List.map_congr_left (fun _ he => corresponds_hit h he)

lemma scode_inj {n : Nat} {S T : Finset (Fin n × Fin n)}
    (hs : S ⊆ (pairs n).toFinset) (ht : T ⊆ (pairs n).toFinset)
    (h : scode S = scode T) : S = T := by
  ext x
  by_cases hx : x ∈ pairs n
  · obtain ⟨i,hi,hx'⟩ := List.mem_iff_getElem.mp hx
    have hh := congrArg (fun l : List Bool => l[i]?) h
    simp [scode, List.getElem?_eq_getElem hi, hx'] at hh
    exact hh
  · have hs' : x ∉ S := fun h => hx (List.mem_toFinset.mp (hs h))
    have ht' : x ∉ T := fun h => hx (List.mem_toFinset.mp (ht h))
    simp [hs',ht']

lemma scode_size {n : Nat} {S : Finset (Fin n × Fin n)}
    (hs : S ⊆ (pairs n).toFinset) : ((scode S).filter id).length = S.card := by
  unfold scode
  rw [List.filter_map, List.length_map]
  let l := (pairs n).filter (fun e => decide (e ∈ S))
  have hl : l.toFinset = S := by
    ext e
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨List.mem_toFinset.mp (hs h),h⟩⟩
  change l.length = S.card
  have hnodup : l.Nodup := (pairs_nodup n).filter _
  exact (List.toFinset_card_of_nodup hnodup).symm.trans (congrArg Finset.card hl)

lemma admissible_iff {n : Nat} (hard : List (Machine.Row n)) (soft : List (Machine.Soft n))
    (S : Finset (Fin n × Fin n)) :
    Gadget.Admissible (Machine.allowedInput (Qr n hard soft)) S ↔ Matching S ∧ S ⊆ allowed hard := by
  constructor
  · rintro ⟨h₁,h₂⟩
    have hs : ∀ e ∈ S, e.1 < e.2 := fun e he =>
      of_decide_eq_true (Bool.and_eq_true_iff.mp (h₁ e he)).1
    exact ⟨⟨hs,h₂⟩, fun e he => Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (mem_pairs.mpr (hs e he)),
        (Machine.allowedInput_query hard soft e.1 e.2).mp (Bool.and_eq_true_iff.mp (h₁ e he)).2⟩⟩
  · rintro ⟨⟨hs,hdis⟩,he⟩
    refine ⟨fun e h => ?_,hdis⟩
    unfold Gadget.allowed
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hs e h),
      (Machine.allowedInput_query hard soft e.1 e.2).mpr ((Finset.mem_filter.mp (he h)).2)⟩

noncomputable abbrev A (n : Nat) (hard : List (Machine.Row n)) (soft : List (Machine.Soft n)) :=
  Machine.allowedInput (Qr n hard soft)
noncomputable abbrev W (n : Nat) (hard : List (Machine.Row n)) (soft : List (Machine.Soft n)) :=
  Machine.inputWeight (Qr n hard soft)
noncomputable abbrev B (n : Nat) (hard : List (Machine.Row n)) (soft : List (Machine.Soft n)) :=
  Machine.inputBase (Qr n hard soft)

def Balance {n : Nat} (hard : List (Machine.Row n)) (soft : List (Machine.Soft n)) : Prop :=
  ∀ S ⊆ allowed hard, 2 ≤ S.card →
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f)) →
    (soft.filter (fun t => t.2 && decide (SoftScore.lists S t))).length =
      (soft.filter (fun t => !t.2 && decide (SoftScore.lists S t))).length

private noncomputable def pickMatchingFn {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (S : {S : Finset (Fin n × Fin n) // Gadget.Admissible (A n hard soft) S}) :
    {f : Fn n // Valid hard f} :=
  let h := (admissible_iff hard soft S.val).mp S.2
  let ex := (matching_valid_unique hn hd h.1 h.2).exists
  ⟨ex.choose, ex.choose_spec.1⟩

private lemma pickMatchingFn_corr {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (S : {S : Finset (Fin n × Fin n) // Gadget.Admissible (A n hard soft) S}) :
    Corresponds (pickMatchingFn hn hard soft hd S).val S.val :=
  (matching_valid_unique hn hd ((admissible_iff hard soft S.val).mp S.2).1
    ((admissible_iff hard soft S.val).mp S.2).2).exists.choose_spec.2

noncomputable def matchFnEquiv {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2) :
    {S : Finset (Fin n × Fin n) // Gadget.Admissible (A n hard soft) S} ≃ {f : Fn n // Valid hard f} := by
  apply Equiv.ofBijective (pickMatchingFn hn hard soft hd)
  constructor
  · intro S T h
    have he : (pickMatchingFn hn hard soft hd S).val = (pickMatchingFn hn hard soft hd T).val :=
      congrArg Subtype.val h
    have hT := pickMatchingFn_corr hn hard soft hd T
    rw [← he] at hT
    obtain ⟨_, U, _, hu⟩ := valid_matching_unique hn (pickMatchingFn hn hard soft hd S).2
    have hs := (admissible_iff hard soft S.val).mp S.2
    have ht := (admissible_iff hard soft T.val).mp T.2
    exact Subtype.ext ((hu S.val ⟨hs.1, hs.2, pickMatchingFn_corr hn hard soft hd S⟩).trans
      (hu T.val ⟨ht.1, ht.2, hT⟩).symm)
  · intro f
    obtain ⟨_, S, hs, _⟩ := valid_matching_unique hn f.2
    let U : {S : Finset (Fin n × Fin n) // Gadget.Admissible (A n hard soft) S} :=
      ⟨S, (admissible_iff hard soft S).mpr ⟨hs.1, hs.2.1⟩⟩
    let g := pickMatchingFn hn hard soft hd U
    obtain ⟨_, _, hu⟩ := matching_valid_unique hn hd hs.1 hs.2.1
    exact ⟨U, Subtype.ext ((hu g.val ⟨g.2, pickMatchingFn_corr hn hard soft hd U⟩).trans
      (hu f.val ⟨f.2, hs.2.2⟩).symm)⟩

lemma matchFnEquiv_corr {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (S : {S : Finset (Fin n × Fin n) // Gadget.Admissible (A n hard soft) S}) :
    Corresponds ((matchFnEquiv hn hard soft hd) S).val S.val :=
  pickMatchingFn_corr hn hard soft hd S

noncomputable def graphFnEquiv {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2) :=
  (Gadget.gadgetEquiv n soft.length (A n hard soft)).trans (matchFnEquiv hn hard soft hd)

lemma graphFnEquiv_corr {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (P : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P}) :
    Corresponds ((graphFnEquiv hn hard soft hd) P).val (Gadget.extract P.val) := by
  rw [← Gadget.gadgetEquiv_extract P]
  exact matchFnEquiv_corr hn hard soft hd ((Gadget.gadgetEquiv n soft.length (A n hard soft)) P)

lemma extract_subset {n : Nat} (hard : List (Machine.Row n)) (soft : List (Machine.Soft n))
    (P : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P}) :
    Gadget.extract P.val ⊆ allowed hard := by
  rw [← Gadget.gadgetEquiv_extract P]
  exact ((admissible_iff hard soft _).mp ((Gadget.gadgetEquiv n soft.length (A n hard soft)) P).2).2

lemma allowed_subset {n : Nat} (hard : List (Machine.Row n)) : allowed hard ⊆ (pairs n).toFinset :=
  Finset.filter_subset _ _

lemma graphFnEquiv_size {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (P : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P}) :
    size ((graphFnEquiv hn hard soft hd) P).val = (Gadget.extract P.val).card := by
  unfold size
  rw [eq_scode (graphFnEquiv_corr hn hard soft hd P)]
  exact scode_size ((extract_subset hard soft P).trans (allowed_subset hard))

lemma graphFnEquiv_red {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2) (hbal : Balance hard soft)
    (P : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P}) :
    Gadget.redCount (A n hard soft) (W n hard soft) (B n hard soft) P.val =
      (soft.length+1) * size ((graphFnEquiv hn hard soft hd) P).val + score soft ((graphFnEquiv hn hard soft hd) P).val := by
  let f := ((graphFnEquiv hn hard soft hd) P).val
  let S := Gadget.extract P.val
  have hf := graphFnEquiv_corr hn hard soft hd P
  have he := extract_subset hard soft P
  have hs : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f) := by
    change ∀ e ∈ Gadget.extract P.val, ∀ f ∈ Gadget.extract P.val, e ≠ f →
      Disjoint (ends e) (ends f)
    rw [← Gadget.gadgetEquiv_extract P]
    exact ((Gadget.gadgetEquiv n soft.length (A n hard soft)) P).2.2
  have hm : Machine.inputM (Qr n hard soft) = soft.length := by
    simpa only [List.append_nil] using Machine.inputM_query hard soft []
  have hb : B n hard soft ≤ soft.length :=
    (Machine.inputBase_le (Qr n hard soft)).trans_eq hm
  have hw (p : Fin n × Fin n) : W n hard soft p.1.val p.2.val ≤ Gadget.H soft.length :=
    (Machine.inputWeight_le (Qr n hard soft) p.1.val p.2.val).trans_eq
      (congrArg (fun m => 2 * m + 1) hm)
  rw [Gadget.red_count P.2 _ _ hb hw, graphFnEquiv_size hn hard soft hd P]
  change B n hard soft + (∑ e ∈ S, W n hard soft e.1.val e.2.val) =
    (soft.length + 1) * S.card + score soft f
  have hbase : B n hard soft = SoftScore.base soft := Machine.base_query hard soft
  rw [hbase]
  have hsum : (∑ e ∈ S, W n hard soft e.1.val e.2.val) =
      ∑ e ∈ S, (soft.length + 1 + SoftScore.pos soft e - SoftScore.neg soft e) := by
    exact Finset.sum_congr rfl fun e _ => Machine.weight_query hard soft e.1 e.2
  rw [hsum]
  exact (SoftScore.score_nat soft S (SoftScore.balance_on_subsets soft he hs hbal)
    (obs f) (fun t => corresponds_obs hf t.1.1 t.1.2)).symm

lemma quotient_weight_unique {m a b s j : Nat} (hb : b ≤ m) (hj : j ≤ m)
    (h : (m+1)*a+b = (m+1)*s+j) : a=s ∧ b=j := by
  have hm : 0 < m+1 := by omega
  have hba : b < m+1 := by omega
  have hbj : j < m+1 := by omega
  have hab := congrArg (fun x : Nat => x / (m+1)) h
  change ((m+1)*a+b)/(m+1) = ((m+1)*s+j)/(m+1) at hab
  simp only [Nat.mul_add_div hm, Nat.div_eq_of_lt hba, Nat.div_eq_of_lt hbj, Nat.add_zero] at hab
  exact ⟨hab,by rw [hab] at h; omega⟩

lemma card_of_pred {α β : Type} (e : α ≃ β) {p : α → Prop} {q : β → Prop}
    (h : ∀ a, p a ↔ q (e a)) : Nat.card {a // p a} = Nat.card {b // q b} := by
  apply Nat.card_congr
  exact e.subtypeEquiv h

lemma card_nested {α : Type} {p q : α → Prop} :
    Nat.card {a : α // p a ∧ q a} = Nat.card {a : {a : α // p a} // q a.val} := by
  apply Nat.card_congr
  exact
    { toFun := fun a => ⟨⟨a.val, a.2.1⟩, a.2.2⟩
      invFun := fun a => ⟨a.val.val, a.val.2, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma graphFnEquiv_card {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2) (hbal : Balance hard soft)
    (s j : Nat) (hj : j ≤ soft.length) :
    Nat.card {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P ∧
      Gadget.redCount (A n hard soft) (W n hard soft) (B n hard soft) P = (soft.length+1)*s+j} =
    Nat.card {f : Fn n // Valid hard f ∧ size f = s ∧ score soft f = j} := by
  rw [card_nested, card_nested]
  apply card_of_pred (graphFnEquiv hn hard soft hd)
  intro P
  rw [graphFnEquiv_red hn hard soft hd hbal P]
  constructor
  · exact quotient_weight_unique (List.length_filter_le _ _) hj
  · rintro ⟨h₁,h₂⟩; rw [h₁,h₂]

end PEqualNP.Outside.L_meta_33617.Forward
namespace PEqualNP.Outside.L_meta_33617.Forward

open CircuitReverse

lemma decode_extract {n : Nat} (hard : List (Machine.Row n)) (soft : List (Machine.Soft n))
    (P : Equiv.Perm (Fin (Gadget.K n soft.length))) :
    Machine.decode (Qr n hard soft ++ Machine.decFields P) = scode (Gadget.extract P) := by
  classical
  let suffix := Machine.decFields P
  have hd := Machine.decode_spec (Qr n hard soft ++ suffix) (Machine.inputN_query hard soft suffix)
    (Machine.inputM_query hard soft suffix) P (Machine.permSuffix_query hard soft suffix)
  change Machine.decode (Qr n hard soft ++ suffix) = scode (Gadget.extract P)
  rw [hd]
  unfold scode
  apply List.map_congr_left
  intro e he
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Gadget.mem_extract]
  have h₁ : Machine.decOrig soft.length e.1 = Gadget.index n soft.length (Gadget.orig e.1) :=
    Fin.ext (Gadget.index_orig e.1).symm
  have h₂ : Machine.decFirstVertex soft.length e = Gadget.index n soft.length (Gadget.path e (Gadget.first soft.length)) := by
    apply Fin.ext
    change Machine.decFirst n soft.length e.1.val e.2.val = _
    rw [Gadget.index_path]
    change Machine.decFirst n soft.length e.1.val e.2.val =
      4*n + (e.1.val*n+e.2.val)*Gadget.Q soft.length + 0
    rw [Nat.add_zero]
    rfl
  rw [h₁,h₂] <;> exact Iff.rfl

lemma graphFnEquiv_decode {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2)
    (P : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P}) :
    Machine.decode (Qr n hard soft ++ Machine.decFields P.val) = code ((graphFnEquiv hn hard soft hd) P).val :=
  (decode_extract hard soft P.val).trans (eq_scode (graphFnEquiv_corr hn hard soft hd P)).symm

lemma unique_decode {n : Nat} (hn : 2 ≤ n) (hard : List (Machine.Row n))
    (soft : List (Machine.Soft n)) (hd : ∀ z ∈ hard, Disjoint z.1 z.2) (f : Fn n) (hf : Valid hard f) :
    ∃! P : Equiv.Perm (Fin (Gadget.K n soft.length)), Gadget.Perfect (A n hard soft) P ∧
      Machine.decode (Qr n hard soft ++ Machine.decFields P) = code f := by
  let e := graphFnEquiv hn hard soft hd
  let p := e.symm ⟨f,hf⟩
  have hval : (e p).val = f := congrArg Subtype.val (e.apply_symm_apply ⟨f,hf⟩)
  have hp : Machine.decode (Qr n hard soft ++ Machine.decFields p.val) = code f :=
    (graphFnEquiv_decode hn hard soft hd p).trans (congrArg code hval)
  refine ⟨p.val, ⟨p.2, hp⟩, ?_⟩
  intro Q hQ
  let q : {P : Equiv.Perm (Fin (Gadget.K n soft.length)) // Gadget.Perfect (A n hard soft) P} := ⟨Q,hQ.1⟩
  suffices q = p from congrArg Subtype.val this
  apply (Gadget.gadgetEquiv n soft.length (A n hard soft)).injective
  apply Subtype.ext
  rw [Gadget.gadgetEquiv_extract q, Gadget.gadgetEquiv_extract p]
  apply scode_inj ((extract_subset hard soft q).trans (allowed_subset hard))
    ((extract_subset hard soft p).trans (allowed_subset hard))
  exact (decode_extract hard soft q.val).symm.trans
    (hQ.2.trans (hp.symm.trans (decode_extract hard soft p.val)))

lemma bad_graph_empty {P : Equiv.Perm (Fin 1)} {G : Fin 1 → Fin 1 → Bool} :
    ¬ Perfect 1 G P := by
  intro h
  exact (h.2 0).1 (Subsingleton.elim _ _)

lemma both_empty_card {α β : Type} {p : α → Prop} {q : β → Prop}
    (hp : ∀ a, ¬p a) (hq : ∀ b, ¬q b) : Nat.card {a // p a} = Nat.card {b // q b} := by
  haveI : IsEmpty {a // p a} := ⟨fun a => hp a.val a.2⟩
  haveI : IsEmpty {b // q b} := ⟨fun b => hq b.val b.2⟩
  simp only [Nat.card_of_isEmpty]

end PEqualNP.Outside.L_meta_33617.Forward

set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.L_meta_33617 :
let header := fun j : Nat => List.replicate j true ++ [false]
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
let bits := fun (w z : Nat) => (List.range w).map (fun h => z.testBit h)
let pairs := fun k : Nat => (List.finRange k).flatMap (fun i =>
    ((List.finRange k).filter (fun j => decide (i < j))).map (fun j => (i,j)))
let paint := fun (k : Nat) (G R : Fin k → Fin k → Bool) =>
  header k ++ (pairs k).flatMap (fun z => [G z.1 z.2, R z.1 z.2])
let perfect := fun (k : Nat) (G : Fin k → Fin k → Bool) (P : Equiv.Perm (Fin k)) =>
  Function.Involutive P ∧ ∀ i, P i ≠ i ∧ G (min i (P i)) (max i (P i)) = true
∃ write decode reverseQ : List Bool → List Bool, fast write ∧ fast decode ∧ fast reverseQ ∧
  (
∀ (n : Nat), 2 ≤ n →
  ∀ (hard : List (Finset (Fin n) × Finset (Fin n)))
    (soft : List ((Finset (Fin n) × Finset (Fin n)) × Bool)),
  let m := soft.length
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let E := (pairs n).toFinset.filter (fun e =>
    ∀ z ∈ hard, ¬(ends e ⊆ z.1) ∧ ¬(ends e ⊆ z.2))
  let lists := fun (S : Finset (Fin n × Fin n)) (t : (Finset (Fin n) × Finset (Fin n)) × Bool) =>
    Disjoint t.1.1 t.1.2 ∧ ∀ e ∈ S, ends e ⊆ t.1.1 ∨ ends e ⊆ t.1.2
  (∀ S ⊆ E, 2 ≤ S.card →
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → Disjoint (ends e) (ends f)) →
    (soft.filter (fun t => t.2 && decide (lists S t))).length =
      (soft.filter (fun t => !t.2 && decide (lists S t))).length) →
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R T : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ T))
  let valid := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    ∀ z ∈ hard, obs f z.1 z.2 = false
  let code := fun f : Fn => (pairs n).map (fun e => obs f (ends e) ∅)
  let size := fun f : Fn => ((code f).filter id).length
  let score := fun f : Fn => (soft.filter (fun t => decide (obs f t.1.1 t.1.2 = t.2))).length
  let bank := fun B : Finset (Fin n) => (List.finRange n).map (fun i => decide (i ∈ B))
  let input := header n ++ header hard.length ++ hard.flatMap (fun z => bank z.1 ++ bank z.2) ++
    header m ++ soft.flatMap (fun t => bank t.1.1 ++ bank t.1.2 ++ [t.2])
  ∃ (k : Nat) (G R : Fin k → Fin k → Bool), write input = paint k G R ∧
    let out := fun P : Equiv.Perm (Fin k) => decode (input ++
      (List.finRange k).flatMap (fun i => bits (k.log2+1) (P i).val))
    let red := fun P : Equiv.Perm (Fin k) => ((pairs k).filter
      (fun e => decide (P e.1 = e.2) && R e.1 e.2)).length
    (∀ P, perfect k G P → ∃ f : Fn, valid f ∧ out P = code f ∧ red P = (m+1)*size f+score f) ∧
    (∀ f : Fn, valid f → ∃! P : Equiv.Perm (Fin k), perfect k G P ∧ out P = code f) ∧
    ∀ s j : Nat, s ≤ n/2 → j ≤ m →
      Nat.card {P : Equiv.Perm (Fin k) // perfect k G P ∧ red P = (m+1)*s+j} =
        Nat.card {f : Fn // valid f ∧ size f = s ∧ score f = j}) ∧
  ∀ (h : Nat) (G R : Fin (2*h) → Fin (2*h) → Bool),
    let v := 2*h
    let n := v+2
    let oldEdges := ((pairs v).filter (fun e => G e.1 e.2)).map (fun e => (e.1.val,e.2.val))
    let reds := ((pairs v).filter (fun e => G e.1 e.2 && R e.1 e.2)).map (fun e => (e.1.val,e.2.val))
    let bans := (pairs n).filter (fun e => decide ((e.1.val,e.2.val) ∉ (v,v+1)::oldEdges))
    let probes := (pairs n).filter (fun e => decide ((e.1.val,e.2.val) ∈ reds))
    let row := fun (e : Fin n × Fin n) => (List.finRange n).map
      (fun i => decide (i = e.1 ∨ i = e.2))
    let zero := List.replicate n false
    reverseQ (paint v G R) = header n ++ header bans.length ++
      bans.flatMap (fun e => row e ++ zero) ++ header probes.length ++
      probes.flatMap (fun e => row e ++ zero ++ [true]) ∧
    let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
    let hit := fun (f : Fn) (e : Fin n × Fin n) =>
      f (fun i => decide (i = e.1 ∨ i = e.2)) (fun _ => false)
    let ok := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
      PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
      (∀ e ∈ bans, hit f e = false) ∧ ((pairs n).filter (hit f)).length = h+1
    ∀ j : Nat, Nat.card {P : Equiv.Perm (Fin v) // perfect v G P ∧
      ((pairs v).filter (fun e => decide (P e.1 = e.2) && R e.1 e.2)).length = j} =
      Nat.card {f : Fn // ok f ∧ (probes.filter (hit f)).length = j}
 := by
  classical
  refine ⟨PEqualNP.Outside.L_meta_33617.Machine.write,
    PEqualNP.Outside.L_meta_33617.Machine.decode,
    PEqualNP.Outside.L_meta_33617.Machine.reverseQ,
    PEqualNP.Outside.L_meta_33617.cpt_to_fast PEqualNP.Outside.L_meta_33617.Machine.cpt_write,
    PEqualNP.Outside.L_meta_33617.cpt_to_fast PEqualNP.Outside.L_meta_33617.Machine.cpt_decode,
    PEqualNP.Outside.L_meta_33617.cpt_to_fast PEqualNP.Outside.L_meta_33617.Machine.cpt_reverseQ, ?_, ?_⟩
  · intro n hn hard soft
    dsimp only
    intro hbalance
    let hbal : PEqualNP.Outside.L_meta_33617.Forward.Balance hard soft := hbalance
    by_cases hd : ∀ z ∈ hard, Disjoint z.1 z.2
    · refine ⟨PEqualNP.Outside.L_meta_33617.Gadget.K n soft.length,
        PEqualNP.Outside.L_meta_33617.Gadget.G n soft.length (PEqualNP.Outside.L_meta_33617.Forward.A n hard soft),
        PEqualNP.Outside.L_meta_33617.Gadget.R n soft.length
          (PEqualNP.Outside.L_meta_33617.Forward.A n hard soft)
          (PEqualNP.Outside.L_meta_33617.Forward.W n hard soft)
          (PEqualNP.Outside.L_meta_33617.Forward.B n hard soft),
        PEqualNP.Outside.L_meta_33617.Machine.write_query hard soft hd, ?_, ?_, ?_⟩
      · intro p hp
        let q : {P // PEqualNP.Outside.L_meta_33617.Gadget.Perfect
            (PEqualNP.Outside.L_meta_33617.Forward.A n hard soft) P} := ⟨p,hp⟩
        let f := (PEqualNP.Outside.L_meta_33617.Forward.graphFnEquiv hn hard soft hd) q
        exact ⟨f.val, f.2, PEqualNP.Outside.L_meta_33617.Forward.graphFnEquiv_decode hn hard soft hd q,
          PEqualNP.Outside.L_meta_33617.Forward.graphFnEquiv_red hn hard soft hd hbal q⟩
      · exact PEqualNP.Outside.L_meta_33617.Forward.unique_decode hn hard soft hd
      · intro s j _ hj
        exact PEqualNP.Outside.L_meta_33617.Forward.graphFnEquiv_card hn hard soft hd hbal s j hj
    · let G : Fin 1 → Fin 1 → Bool := fun _ _ => false
      let R : Fin 1 → Fin 1 → Bool := fun _ _ => false
      have hb : PEqualNP.Outside.L_meta_33617.Machine.hardOverlap
          (PEqualNP.Outside.L_meta_33617.Machine.query n hard soft) :=
        (PEqualNP.Outside.L_meta_33617.Machine.hardOverlap_query hard soft).mpr hd
      have hpaint : PEqualNP.Outside.L_meta_33617.Machine.write
          (PEqualNP.Outside.L_meta_33617.Machine.query n hard soft) =
          PEqualNP.Outside.L_meta_33617.Machine.paint 1 G R := by
        rw [PEqualNP.Outside.L_meta_33617.Machine.write, if_pos hb]
        decide
      have hv (f : PEqualNP.Outside.L_meta_33617.CircuitReverse.Fn n) :
          ¬ PEqualNP.Outside.L_meta_33617.CircuitReverse.Valid hard f :=
        fun hf => hd (PEqualNP.Outside.L_meta_33617.CircuitReverse.valid_matching_unique hn hf).1
      refine ⟨1,G,R,hpaint,?_,?_,?_⟩
      · intro p hp
        exact (PEqualNP.Outside.L_meta_33617.Forward.bad_graph_empty hp).elim
      · intro f hf
        exact (hv f hf).elim
      · intro s j _ _
        apply PEqualNP.Outside.L_meta_33617.Forward.both_empty_card
        · intro p hp
          exact PEqualNP.Outside.L_meta_33617.Forward.bad_graph_empty hp.1
        · intro f hf
          exact hv f hf.1
  · intro h G R
    refine ⟨PEqualNP.Outside.L_meta_33617.Machine.reverseQ_spec h G R, ?_⟩
    dsimp only
    intro j
    exact PEqualNP.Outside.L_meta_33617.CircuitReverse.reverse_card h G R j
