import PEqualNP.Defs
import Mathlib.Data.Nat.Bits
namespace PEqualNP.Outside.L_meta_32567
namespace Lib
abbrev qe (f:List Bool→List Bool):Prop:=PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
end Lib
section
namespace Lib.qz
open Turing
theorem d43 {σ:Type} (f:σ→Option σ) (n:ℕ):
 (flip bind f)^[n] none=none:=by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [Function.iterate_succ_apply];exact ih
theorem d59 {σ τ:Type} (f:σ→Option σ) (g:τ→Option τ) (emb:σ→τ)
 (h:∀ c c',f c=some c'→ g (emb c)=some (emb c')):
 ∀ (n:ℕ) (a b:σ),(flip bind f)^[n] (some a)=some b→
   (flip bind g)^[n] (some (emb a))=some (emb b):=by
 intro n
 induction n with
 | zero=>
   intro a b hab
   have:a=b:=Option.some.inj hab
   rw [this];rfl
 | succ n ih=>
   intro a b hab
   rw [Function.iterate_succ_apply] at hab ⊢
   cases hfa:f a with
   | none=>
     have e:flip bind f (some a)=none:=hfa
     rw [e,d43] at hab
     exact absurd hab (by simp)
   | some c=>
     have e:flip bind f (some a)=some c:=hfa
     have e':flip bind g (some (emb a))=some (emb c):=h a c hfa
     rw [e] at hab
     rw [e']
     exact ih c b hab
section pushes
variable {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
def pushes:TM2.Stmt Γ Λ σ→ℕ
 | .push _ _ q=>pushes q+1
 | .peek _ _ q=>pushes q
 | .pop _ _ q=>pushes q
 | .load _ q=>pushes q
 | .branch _ q₁ q₂=>max (pushes q₁) (pushes q₂)
 | .goto _=>0
 | .halt=>0
theorem d58 (q:TM2.Stmt Γ Λ σ) (v:σ) (S:∀ k,List (Γ k)) (k:K):
 ((TM2.stepAux q v S).stk k).length≤(S k).length+pushes q:=by
 induction q generalizing v S with
 | push k' f q ih=>
   simp only [TM2.stepAux,pushes]
   refine (ih _ _).trans ?_
   by_cases h:k=k'
   · subst h
     rw [Function.update_self,List.length_cons];omega
   · rw [Function.update_of_ne h];omega
 | peek k' f q ih=>exact ih _ _
 | pop k' f q ih=>
   simp only [TM2.stepAux,pushes]
   refine (ih _ _).trans ?_
   by_cases h:k=k'
   · subst h
     rw [Function.update_self,List.length_tail];omega
   · rw [Function.update_of_ne h]
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [TM2.stepAux,pushes]
   cases f v
   · exact (ih₂ v S).trans (by have:=le_max_right (pushes q₁) (pushes q₂);omega)
   · exact (ih₁ v S).trans (by have:=le_max_left (pushes q₁) (pushes q₂);omega)
 | goto f=>simp [TM2.stepAux,pushes]
 | halt=>simp [TM2.stepAux,pushes]
end pushes
noncomputable def maxPush (tm:FinTM2):ℕ:=
 (@Finset.univ tm.Λ tm.ΛFin).sup fun l=>pushes (tm.m l)
theorem d86 (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
 (h:TM2.step tm.m c=some c') (k:tm.K):
 (c'.stk k).length≤(c.stk k).length+maxPush tm:=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   refine (d58 _ _ _ _).trans ?_
   have:pushes (tm.m l)≤ maxPush tm:=
    Finset.le_sup (f:=fun l=>pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
   simpa using this
theorem d67 (tm:FinTM2) (k:tm.K):
 ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
   (flip bind (TM2.step tm.m))^[n] (some a)=some b→
   (b.stk k).length≤(a.stk k).length+maxPush tm * n:=by
 intro n
 induction n with
 | zero=>
   intro a b hab
   have:a=b:=Option.some.inj hab
   rw [this];simp
 | succ n ih=>
   intro a b hab
   rw [Function.iterate_succ_apply] at hab
   cases hfa:TM2.step tm.m a with
   | none=>
     have e:flip bind (TM2.step tm.m) (some a)=none:=hfa
     rw [e,d43] at hab
     exact absurd hab (by simp)
   | some c=>
     have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa
     rw [e] at hab
     have h1:=ih c b hab
     have h2:=d86 tm a c hfa k
     rw [Nat.mul_succ];omega
theorem d4 (tm:FinTM2) (s:List (tm.Γ tm.k₀)):
 initList tm s=
  (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩:
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold initList
 congr 1
 funext k
 by_cases h:k=tm.k₀
 · subst h;simp
 · simp [h]
theorem d5 (tm:FinTM2) (s:List (tm.Γ tm.k₁)):
 haltList tm s=
  (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩:
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold haltList
 congr 1
 funext k
 by_cases h:k=tm.k₁
 · subst h;simp
 · simp [h]
theorem d37 (p:Polynomial ℕ) {x y:ℕ} (h:x≤y):p.eval x≤p.eval y:=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq=>
   rw [Polynomial.eval_add,Polynomial.eval_add];exact add_le_add hp hq
 | monomial d c=>
   rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.qz
end
section
namespace Lib.qz
open Turing
def d60:List Bool→TM2.Stmt (fun _:Unit=>Bool) Unit Bool
 | []=>.halt
 | a::l=>.push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit→TM2.Stmt (fun _:Unit=>Bool) Unit Bool:=
 fun _=>.pop () (fun _ o=>o.isSome)
  (.branch (fun s=>s)
    (.load (fun _=>false) (.goto fun _=>()))
    (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
 K:=Unit
 k₀:=()
 k₁:=()
 Γ _:=Bool
 Λ:=Unit
 main:=()
 σ:=Bool
 initialState:=false
 m:=d3 l
abbrev kH:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
theorem d17 (S T:List Bool):
 Function.update (fun _:Unit=>S) () T=fun _=>T:=by
 funext k
 simp
theorem d42 (l:List Bool) (v:Bool) (S:List Bool):
 TM2.stepAux (d60 l) v (fun _:Unit=>S)=
  (⟨none,v,fun _=>l.reverse++S⟩:kH):=by
 induction l generalizing S with
 | nil=>rfl
 | cons a l ih=>
   simp only [d60,TM2.stepAux]
   rw [d17,ih]
   simp
theorem d64 (l:List Bool) (x:Bool) (a:List Bool):
 TM2.step (d3 l) (⟨some (),false,fun _=>x::a⟩:kH)=
  some ⟨some (),false,fun _=>a⟩:=by
 simp only [TM2.step,d3,TM2.stepAux]
 rw [d17]
 simp
theorem d76 (l:List Bool):
 TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:kH)=
  some ⟨none,false,fun _=>l⟩:=by
 simp only [TM2.step,d3,TM2.stepAux]
 rw [d17]
 simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
 rw [d42]
 simp
theorem d63 (l:List Bool) (a:List Bool):
 (flip bind (TM2.step (d3 l)))^[a.length+1]
   (some (⟨some (),false,fun _=>a⟩:kH))=
   some ⟨none,false,fun _=>l⟩:=by
 induction a with
 | nil=>exact d76 l
 | cons x a ih=>
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (d3 l))
    (some (⟨some (),false,fun _=>x::a⟩:kH))=
    some ⟨some (),false,fun _=>a⟩:=d64 l x a
   rw [e,ih]
theorem d75 (l:List Bool) (a:List Bool):
 (flip bind (TM2.step (d3 l)))^[a.length+1]
   (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
  (some c)) (d4 (d20 l) a)).trans
  (Eq.trans ?_ (congrArg some (d5 (d20 l) l)).symm)
 show (flip bind (TM2.step (d3 l)))^[a.length+1]
  (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:kH))=
  some (⟨none,false,Function.update (fun _=>[]) () l⟩:kH)
 rw [d17,d17]
 exact d63 l a
theorem d11 (l:List Bool):
 Nonempty (Turing.TM2ComputableInPolyTime (fun x:List Bool=>x)
  (fun x:List Bool=>x) (fun _:List Bool=>l)):=
 ⟨{
   tm:=d20 l
   inputAlphabet:=Equiv.refl _
   outputAlphabet:=Equiv.refl _
   time:=Polynomial.X+1
   outputsFun:=fun a=>
    { steps:=a.length+1
      evals_in_steps:=by
       have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
       exact (congrArg (fun x=>(flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (initList (d20 l) x))) (hm a)).trans
        ((d75 l a).trans
          (congrArg (fun x=>some (haltList (d20 l) x)) (hm l).symm))
      steps_le_m:=by simp } }⟩
end Lib.qz
end
section
namespace Lib.qz
open Turing
section update
variable {ι:Type} [DecidableEq ι] {β:ι→Type}
theorem d51 (E:∀ i,β i) {a b c:ι} (hab:a≠b) (hac:a≠c)
 (x x':β a) (y:β b) (z:β c):
 Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x'=
  Function.update (Function.update (Function.update E a x') b y) c z:=by
 rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
theorem d50 (E:∀ i,β i) {a b c:ι} (hbc:b≠c)
 (x:β a) (y y':β b) (z:β c):
 Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y'=
  Function.update (Function.update (Function.update E a x) b y') c z:=by
 rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ:CK M1 M2→Type
 | none=>M2.Γ M2.k₀
 | some (Sum.inl k)=>M1.Γ k
 | some (Sum.inr k)=>M2.Γ k
abbrev CΛ:Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ:Type:=M1.σ×M2.σ×Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (Sum.inl k)) (fun s=>f s.1) (tr1 q)
 | .peek k f q=>.peek (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .pop k f q=>.pop (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (tr1 q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
 | .goto f=>.goto (fun s=>Sum.inl (f s.1))
 | .halt=>.goto (fun _=>Sum.inr (Sum.inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q=>.push (some (Sum.inr k)) (fun s=>f s.2.1) (tr2 q)
 | .peek k f q=>.peek (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .pop k f q=>.pop (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .load a q=>.load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
 | .goto f=>.goto (fun s=>Sum.inr (Sum.inl (f s.2.1)))
 | .halt=>.halt
variable (M1 M2)
def tA (φ:M1.Γ M1.k₁→M2.Γ M2.k₀):
    Option (M2.Γ M2.k₀)→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>Sum.inr (Sum.inl M2.main))
 | some d=>
   .pop (some (Sum.inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
     (.branch (fun s=>s.2.2.isSome)
       (.push none (fun s=>s.2.2.getD d) (.goto fun _=>Sum.inr (Sum.inr false)))
       (.goto fun _=>Sum.inr (Sum.inr true)))
def tB:Option (M2.Γ M2.k₀)→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none=>.goto (fun _=>Sum.inr (Sum.inl M2.main))
 | some d=>
   .pop none (fun s o=>(s.1,s.2.1,o))
     (.branch (fun s=>s.2.2.isSome)
       (.push (some (Sum.inr M2.k₀)) (fun s=>s.2.2.getD d)
         (.goto fun _=>Sum.inr (Sum.inr true)))
       (.goto fun _=>Sum.inr (Sum.inl M2.main)))
def zm (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):
    CΛ M1 M2→TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | Sum.inl l=>tr1 (M1.m l)
 | Sum.inr (Sum.inl l)=>tr2 (M2.m l)
 | Sum.inr (Sum.inr false)=>tA M1 M2 φ d
 | Sum.inr (Sum.inr true)=>tB M1 M2 d
def comp (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2:=
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
   Γ:=CΓ M1 M2
   Λ:=CΛ M1 M2
   main:=Sum.inl M1.main
   σ:=Cσ M1 M2
   initialState:=(M1.initialState,M2.initialState,none)
   Γk₀Fin:=M1.Γk₀Fin
   m:=zm M1 M2 φ d }
variable {M1 M2}
def d49 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (Sum.inl k)=>S k
 | some (Sum.inr _)=>[]
def d48 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (Sum.inl _)=>[]
 | some (Sum.inr k)=>S k
theorem d13 (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)):
 (d49 (Function.update S k x):∀ k,List (CΓ M1 M2 k))=
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
theorem d12 (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)):
 (d48 (Function.update S k x):∀ k,List (CΓ M1 M2 k))=
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
theorem d56:
 (d49 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j;rcases j with _ | j | j <;> rfl
theorem d55:
 (d48 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j;rcases j with _ | j | j <;> rfl
def jH (w:M2.σ×Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ):
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=
 ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),d49 c.stk⟩
def jI (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ):
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2):=
 ⟨c.l.map (fun l=>Sum.inr (Sum.inl l)),(u,c.var,b),d48 c.stk⟩
theorem qed (w:M2.σ×Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
 (S:∀ k,List (M1.Γ k)):
 TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (d49 S)=jH w (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>
   have:=ih v (Function.update S k (f v::S k))
   rw [d13] at this
   exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>
   have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [d13] at this
   exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [tr1,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem qee (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
 (S:∀ k,List (M2.Γ k)):
 TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (d48 S)=jI u b (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>
   have:=ih v (Function.update S k (f v::S k))
   rw [d12] at this
   exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>
   have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [d12] at this
   exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [tr2,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
variable (φ:M1.Γ M1.k₁→M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
theorem qck (w:M2.σ×Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
 (h:TM2.step M1.m c=some c'):
 TM2.step (zm M1 M2 φ d) (jH w c)=some (jH w c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (qed w (M1.m l) v S)
theorem qcl (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
 (h:TM2.step M2.m c=some c'):
 TM2.step (zm M1 M2 φ d) (jI u b c)=some (jI u b c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (qee u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k):=
 Function.update (Function.update (Function.update (fun _=>[])
  (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
theorem qaW (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁))=l:=by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem w6 (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_self]
theorem qbV (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))=u:=by
 unfold st
 rw [Function.update_self]
theorem d66 (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l'=st l' t u:=
 d51 _ (by simp) (by simp) _ _ _ _
theorem d41 (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)):
 Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u:=
 d50 _ (by simp) _ _ _ _
theorem d90 (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)):
 Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u'=st l t u':=
 Function.update_idem _ _ _
theorem d79 (l:List (M1.Γ M1.k₁)):
 (st l [] []:∀ k,List (CΓ M1 M2 k))=
   Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l:=by
 unfold st
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem w5 (u:List (M2.Γ M2.k₀)):
 (st [] [] u:∀ k,List (CΓ M1 M2 k))=
   Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u:=by
 unfold st
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
end Lib.qz
end
section
namespace Lib.qz
open Turing
variable {M1 M2:FinTM2} (φ:M1.Γ M1.k₁→M2.Γ M2.k₀)
abbrev vV (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem d89 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):
 TM2.step (zm M1 M2 φ (some dd))
  (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x::l) t u⟩:vV M1 M2)=
  some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩:=by
 simp only [TM2.step,zm,tA,TM2.stepAux]
 rw [qaW]
 simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
  Option.getD_some]
 rw [d66,w6,d41]
theorem qcu (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (t u:List (M2.Γ M2.k₀)):
 TM2.step (zm M1 M2 φ (some dd))
  (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩:vV M1 M2)=
  some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩:=by
 simp only [TM2.step,zm,tA,TM2.stepAux]
 rw [qaW]
 simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
 rw [d66]
theorem d88 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)):
 TM2.step (zm M1 M2 φ (some dd))
  (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x::t) u⟩:vV M1 M2)=
  some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x::u)⟩:=by
 simp only [TM2.step,zm,tB,TM2.stepAux]
 rw [w6]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
 rw [d41,qbV,d90]
theorem qct (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
 (u:List (M2.Γ M2.k₀)):
 TM2.step (zm M1 M2 φ (some dd))
  (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩:vV M1 M2)=
  some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
 simp only [TM2.step,zm,tB,TM2.stepAux]
 rw [w6]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [d41]
theorem qcf (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)):
 ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (zm M1 M2 φ (some dd))))^[l.length+1]
     (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩:vV M1 M2))=
     some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t b;exact qcu φ dd v1 v2 b t u
 | cons x l ih=>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (zm M1 M2 φ (some dd)))
    (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x::l) t u⟩:vV M1 M2))=
    some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x::t) u⟩:=
    d89 φ dd v1 v2 b x l t u
   rw [e,ih]
   simp
theorem qcg (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ):
 ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (zm M1 M2 φ (some dd))))^[t.length+1]
     (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩:vV M1 M2))=
     some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u b;exact qct φ dd v1 v2 b u
 | cons x t ih=>
   intro u b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (zm M1 M2 φ (some dd)))
    (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x::t) u⟩:vV M1 M2))=
    some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x::u)⟩:=
    d88 φ dd v1 v2 b x t u
   rw [e,ih]
   simp
theorem qcI (d:Option (M2.Γ M2.k₀)) (hd:d=none→IsEmpty (M2.Γ M2.k₀))
 (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)):
 ∃ n,n≤2 * o.length+2∧
   (flip bind (TM2.step (zm M1 M2 φ d)))^[n]
     (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
       Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩:
       vV M1 M2))=
     some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
       (o.map φ)⟩:=by
 cases d with
 | none=>
   have:=hd rfl
   have ho:o=[]:=by
    cases o with
    | nil=>rfl
    | cons x _=>exact (IsEmpty.false (φ x)).elim
   subst ho
   refine ⟨1,by omega,?_⟩
   show some _=some _
   simp only [zm,tA,TM2.stepAux,List.map_nil]
   rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
 | some dd=>
   refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩
   rw [Function.iterate_add_apply,← d79,qcf,qcg,← w5]
   simp
theorem qcD (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)):
 jH (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
 rw [d4]
 refine Eq.trans ?_ (d4 (comp M1 M2 φ d) i).symm
 show (⟨_,_,d49 _⟩:vV M1 M2)=_
 rw [d13,d56]
 rfl
theorem qcE (w:M2.σ×Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)):
 jH w (haltList M1 o)=
  (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
    Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩:
    vV M1 M2):=by
 rw [d5]
 show (⟨_,_,d49 _⟩:vV M1 M2)=_
 rw [d13,d56]
 rfl
theorem qcB (u:M1.σ) (i:List (M2.Γ M2.k₀)):
 jI u none (initList M2 i)=
  (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
    Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩:
    vV M1 M2):=by
 rw [d4]
 show (⟨_,_,d48 _⟩:vV M1 M2)=_
 rw [d12,d55]
 rfl
theorem qcC (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)):
 jI M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
 rw [d5]
 refine Eq.trans ?_ (d5 (comp M1 M2 φ d) o).symm
 show (⟨_,_,d48 _⟩:vV M1 M2)=_
 rw [d12,d55]
 rfl
theorem qcY (d:Option (M2.Γ M2.k₀)) (hd:d=none→IsEmpty (M2.Γ M2.k₀))
 (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
 (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
 (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ)))=
   some (haltList M2 o2)):
 ∃ n,n≤ s1+(2 * o1.length+2)+s2∧o1.length≤ i.length+maxPush M1 * s1∧
   (flip bind (TM2.step (zm M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i))=
     some (haltList (comp M1 M2 φ d) o2):=by
 have p1:=d59 (TM2.step M1.m) (TM2.step (zm M1 M2 φ d))
  (jH (M2.initialState,none)) (qck φ d _) s1 _ _ h1
 rw [qcD φ d,qcE] at p1
 obtain ⟨nt,hnt,pt⟩:=qcI φ d hd M1.initialState M2.initialState o1
 have p2:=d59 (TM2.step M2.m) (TM2.step (zm M1 M2 φ d))
  (jI M1.initialState none) (qcl φ d _ _) s2 _ _ h2
 rw [qcB,qcC φ d] at p2
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
theorem d77 {α β γ αΓ βΓ γΓ:Type} (ea:α→List αΓ) (eb:β→List βΓ)
 (ec:γ→List γΓ) (f:α→β) (g:β→γ) (c1:TM2ComputableInPolyTime ea eb f)
 (c2:TM2ComputableInPolyTime eb ec g):
 Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
 classical
 let φ:c1.tm.Γ c1.tm.k₁→c2.tm.Γ c2.tm.k₀:=
  fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
 let d:Option (c2.tm.Γ c2.tm.k₀):=
  if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
 have hd:d=none→IsEmpty (c2.tm.Γ c2.tm.k₀):=by
  intro h
  by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
  · simp [d,hn] at h
  · exact not_nonempty_iff.mp hn
 let T:Polynomial ℕ:=
  c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time) +
   Polynomial.C 2) +
   c2.time.comp (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time)
 have key:∀ a,∃ n,n≤T.eval (ea a).length∧
  (flip bind (TM2.step (zm c1.tm c2.tm φ d)))^[n]
    (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a))))=
    some (haltList (comp c1.tm c2.tm φ d)
     (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
  intro a
  have r1:=c1.outputsFun a
  have r2:=c2.outputsFun (f a)
  have hφ:(List.map c1.outputAlphabet.invFun (eb (f a))).map φ=
   List.map c2.inputAlphabet.invFun (eb (f a)):=by
   rw [List.map_map]
   refine List.map_congr_left fun y _=>?_
   show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
   exact congrArg _ (c1.outputAlphabet.right_inv y)
  have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
   (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ)))=
   some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
   rw [hφ];exact r2.evals_in_steps
  obtain ⟨n,hn,hlen,hrun⟩:=qcY φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
  refine ⟨n,hn.trans ?_,hrun⟩
  have b1:=r1.steps_le_m
  have b2:=r2.steps_le_m
  simp only [List.length_map] at hlen
  have hmul:maxPush c1.tm * r1.steps≤
   maxPush c1.tm * Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
  have b3:Polynomial.eval (eb (f a)).length c2.time≤
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
  outputsFun:=fun a=>
   ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
     (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.qz
end
section
namespace Lib.qz
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool→Type
 | some false=>Γ₀
 | none=>Option Γ₀
 | some true=>Γ₁
def zN (φ:Γ₀→Option Γ₁) (d:Option Γ₁):Bool→TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
 | false=>
   .pop (some false) (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push none (fun s=>s) (.goto fun _=>false))
       (.goto fun _=>true))
 | true=>
   .pop none (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.branch (fun s=>(s.bind φ).isSome)
         (match d with
           | some dd=>.push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
           | none=>.goto fun _=>true)
         (.goto fun _=>true))
       .halt)
def fm [Fintype Γ₀] (φ:Γ₀→Option Γ₁) (d:Option Γ₁):FinTM2 where
 K:=Option Bool
 k₀:=some false
 k₁:=some true
 Γ:=FΓ Γ₀ Γ₁
 Λ:=Bool
 main:=false
 σ:=Option Γ₀
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=zN φ d
def zr (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k):=
 Function.update (Function.update (Function.update (fun _=>[])
  (some false) l) none t) (some true) u
theorem d99 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 zr l t u (some false)=l:=by
 unfold zr
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem d81 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 zr l t u none=t:=by
 unfold zr
 rw [Function.update_of_ne (by simp),Function.update_self]
theorem qcT (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 zr l t u (some true)=u:=by
 unfold zr
 rw [Function.update_self]
theorem d47 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 Function.update (zr l t u) (some false) l'=zr l' t u:=
 d51 _ (by simp) (by simp) _ _ _ _
theorem d27 (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁):
 Function.update (zr l t u) none t'=zr l t' u:=
 d50 _ (by simp) _ _ _ _
theorem d82 (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁):
 Function.update (zr l t u) (some true) u'=zr l t u':=
 Function.update_idem _ _ _
theorem d98 (l:List Γ₀):
 (zr l [] []:∀ k,List (FΓ Γ₀ Γ₁ k))=
   Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
 unfold zr
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem qcU (u:List Γ₁):
 (zr [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k))=
   Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
 unfold zr
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
abbrev km (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ:Γ₀→Option Γ₁) (d:Option Γ₁)
theorem qcW (b:Option Γ₀) (x:Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zN φ d) (⟨some false,b,zr (x::l) t u⟩:km Γ₀ Γ₁)=
  some ⟨some false,some x,zr l (some x::t) u⟩:=by
 simp only [TM2.step,zN,TM2.stepAux]
 rw [d99]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
 rw [d47,d81,d27]
theorem qdq (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zN φ d) (⟨some false,b,zr [] t u⟩:km Γ₀ Γ₁)=
  some ⟨some true,none,zr [] t u⟩:=by
 simp only [TM2.step,zN,TM2.stepAux]
 rw [d99]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [d47]
theorem qcV (hd:d=none→∀ x,φ x=none) (b:Option Γ₀) (x:Γ₀)
 (t:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (zN φ d) (⟨some true,b,zr [] (some x::t) u⟩:km Γ₀ Γ₁)=
  some ⟨some true,some x,zr [] t ((φ x).toList++u)⟩:=by
 simp only [TM2.step,zN,TM2.stepAux]
 rw [d81]
 simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
  Bool.cond_true,Option.bind_some]
 rw [d27]
 cases hφ:φ x with
 | none=>simp
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
   | some dd=>
     simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
      Option.toList_some,List.singleton_append]
     rw [qcT,d82]
     simp [hφ]
theorem qdp (b:Option Γ₀) (u:List Γ₁):
 TM2.step (zN φ d) (⟨some true,b,zr [] [] u⟩:km Γ₀ Γ₁)=
  some ⟨none,none,zr [] [] u⟩:=by
 simp only [TM2.step,zN,TM2.stepAux]
 rw [d81]
 simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
  Bool.cond_false]
 rw [d27]
theorem qdo (u:List Γ₁):
 ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
   (flip bind (TM2.step (zN φ d)))^[l.length+1]
     (some (⟨some false,b,zr l t u⟩:km Γ₀ Γ₁))=
     some ⟨some true,none,zr [] (l.reverse.map some++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t b;exact qdq φ d b t u
 | cons x l ih=>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (zN φ d))
    (some (⟨some false,b,zr (x::l) t u⟩:km Γ₀ Γ₁))=
    some ⟨some false,some x,zr l (some x::t) u⟩:=qcW φ d b x l t u
   rw [e,ih]
   simp
theorem qdn (hd:d=none→∀ x,φ x=none):
 ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
   (flip bind (TM2.step (zN φ d)))^[t.length+1]
     (some (⟨some true,b,zr [] (t.map some) u⟩:km Γ₀ Γ₁))=
     some ⟨none,none,zr [] [] ((t.filterMap φ).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u b;exact qdp φ d b u
 | cons x t ih=>
   intro u b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (zN φ d))
    (some (⟨some true,b,zr [] ((x::t).map some) u⟩:km Γ₀ Γ₁))=
    some ⟨some true,some x,zr [] (t.map some) ((φ x).toList++u)⟩:=
    qcV φ d hd b x (t.map some) u
   rw [e,ih]
   cases hφ:φ x <;> simp [hφ]
theorem qbs [Fintype Γ₀] (hd:d=none→∀ x,φ x=none) (l:List Γ₀):
 (flip bind (TM2.step (zN φ d)))^[l.length+1+(l.length+1)]
   (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (zN φ d)))^[l.length+1+(l.length+1)]
  (some c)) (d4 (fm φ d) l)).trans
  (Eq.trans ?_ (congrArg some (d5 (fm φ d) (l.filterMap φ))).symm)
 show (flip bind (TM2.step (zN φ d)))^[l.length+1+(l.length+1)]
  (some (⟨some false,none,Function.update (fun _=>[]) (some false) l⟩:km Γ₀ Γ₁))=
  some (⟨none,none,Function.update (fun _=>[]) (some true) (l.filterMap φ)⟩:km Γ₀ Γ₁)
 rw [Function.iterate_add_apply,← d98,qdo,← qcU]
 have:=qdn φ d hd l.reverse [] none
 rw [List.length_reverse] at this
 simpa [List.filterMap_reverse] using this
theorem d7 {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (φ:αΓ→Option βΓ)
 (h:∀ a,eb (f a)=(ea a).filterMap φ):
 Nonempty (TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:d=none→∀ x,φ x=none:=by
  intro hdn x
  by_cases hn:Nonempty βΓ
  · simp [d,hn] at hdn
  · cases hφ:φ x with
    | none=>rfl
    | some y=>exact absurd ⟨y⟩ hn
 exact ⟨{
  tm:=fm φ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 2
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=
       fun γ l=>by simp
      have:=qbs φ d hd (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (zN φ d)))^[(ea a).length+1 +
       ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
       Polynomial.eval_X]
      omega } }⟩
end Lib.qz
end
section
namespace Lib.qz
open Turing
inductive TPK:Type
 | inp | t1 | t2 | t3 | out
 deriving DecidableEq
instance:Fintype TPK:=
 Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive TPL:Type
 | a | b | c | e
 deriving DecidableEq
instance:Fintype TPL:=
 Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK→Type
 | .inp=>Γ₀
 | .t1=>Option Γ₀
 | .t2=>Option Γ₀
 | .t3=>Option Γ₀
 | .out=>Γ₁
def d52 (φ:Γ₀→Option Γ₁) (d:Option Γ₁) (lbl:TPL):
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀):=
 .branch (fun s=>(s.bind φ).isSome)
   (match d with
     | some dd=>.push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
     | none=>.goto fun _=>lbl)
   (.goto fun _=>lbl)
def qM (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁):
    TPL→TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
 | .a=>
   .pop .inp (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push .t1 (fun s=>s) (.goto fun _=>.a))
       (.goto fun _=>.b))
 | .b=>
   .pop .t1 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.push .t2 (fun s=>s) (d52 φ₂ d .b))
       (.goto fun _=>.c))
 | .c=>
   .pop .t2 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (.push .t3 (fun s=>s) (.goto fun _=>.c))
       (.goto fun _=>.e))
 | .e=>
   .pop .t3 (fun _ o=>o.join)
     (.branch (fun s=>s.isSome)
       (d52 φ₁ d .e)
       .halt)
def tp [Fintype Γ₀] (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁):FinTM2 where
 K:=TPK
 k₀:=.inp
 k₁:=.out
 Γ:=TPΓ Γ₀ Γ₁
 Λ:=TPL
 main:=.a
 σ:=Option Γ₀
 initialState:=none
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=qM φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
 | .inp=>l
 | .t1=>a
 | .t2=>b
 | .t3=>c
 | .out=>u
theorem d54 (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):
 Function.update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
 funext k;cases k <;> simp [st5]
theorem d31 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁):
 Function.update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
 funext k;cases k <;> simp [st5]
theorem d30 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁):
 Function.update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
 funext k;cases k <;> simp [st5]
theorem d29 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁):
 Function.update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
 funext k;cases k <;> simp [st5]
theorem d53 (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁):
 Function.update (st5 l a b c u) .out u'=st5 l a b c u':=by
 funext k;cases k <;> simp [st5]
theorem qcv (l:List Γ₀):
 (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k))=
   Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
 funext k;cases k <;> simp [st5]
theorem qdd (u:List Γ₁):
 (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k))=
   Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
 funext k;cases k <;> simp [st5]
abbrev zG (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂:Γ₀→Option Γ₁) (d:Option Γ₁)
theorem qcP (s:Option Γ₀) (x:Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
 (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .a,s,st5 (x::l) a b c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d54,d31]
theorem qdc (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .b,none,st5 [] a b c u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d54]
theorem qcO (hd:d=none→∀ x,φ₂ x=none) (s:Option Γ₀) (x:Γ₀)
 (a b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x::a) b c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .b,some x,st5 [] a (some x::b) c ((φ₂ x).toList++u)⟩:=by
 cases hφ:φ₂ x with
 | none=>
   cases d <;>
    simp [TM2.step,qM,d52,TM2.stepAux,st5,d31,d30,hφ]
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
   | some dd=>
     simp [TM2.step,qM,d52,TM2.stepAux,st5,d31,d30,
      d53,hφ]
theorem qdb (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .c,none,st5 [] [] b c u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d31]
theorem qcN (s:Option Γ₀) (x:Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x::b) c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .c,some x,st5 [] [] b (some x::c) u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d30,d29]
theorem qda (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:zG Γ₀ Γ₁)=
  some ⟨some .e,none,st5 [] [] [] c u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d30]
theorem qcM (hd:d=none→∀ x,φ₁ x=none) (s:Option Γ₀) (x:Γ₀)
 (c:List (Option Γ₀)) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x::c) u⟩:zG Γ₀ Γ₁)=
  some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
 cases hφ:φ₁ x with
 | none=>
   cases d <;>
    simp [TM2.step,qM,d52,TM2.stepAux,st5,d29,hφ]
 | some y=>
   cases d with
   | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
   | some dd=>
     simp [TM2.step,qM,d52,TM2.stepAux,st5,d29,d53,hφ]
theorem qc9 (s:Option Γ₀) (u:List Γ₁):
 TM2.step (qM φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:zG Γ₀ Γ₁)=
  some ⟨none,none,st5 [] [] [] [] u⟩:=by
 simp [TM2.step,qM,TM2.stepAux,st5,d29]
theorem qc8 (b c:List (Option Γ₀)) (u:List Γ₁):
 ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1]
     (some (⟨some .a,s,st5 l a b c u⟩:zG Γ₀ Γ₁))=
     some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
 intro l
 induction l with
 | nil=>intro a s;exact qdc φ₁ φ₂ d s a b c u
 | cons x l ih=>
   intro a s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (qM φ₁ φ₂ d))
    (some (⟨some .a,s,st5 (x::l) a b c u⟩:zG Γ₀ Γ₁))=
    some ⟨some .a,some x,st5 l (some x::a) b c u⟩:=qcP φ₁ φ₂ d s x l a b c u
   rw [e,ih]
   simp
theorem qc7 (hd:d=none→∀ x,φ₂ x=none) (c:List (Option Γ₀)):
 ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (qM φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:zG Γ₀ Γ₁))=
     some ⟨some .c,none,
      st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro b u s;exact qdb φ₁ φ₂ d s b c u
 | cons x t ih=>
   intro b u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (qM φ₁ φ₂ d))
    (some (⟨some .b,s,st5 [] ((x::t).map some) b c u⟩:zG Γ₀ Γ₁))=
    some ⟨some .b,some x,st5 [] (t.map some) (some x::b) c ((φ₂ x).toList++u)⟩:=
    qcO φ₁ φ₂ d hd s x (t.map some) b c u
   rw [e,ih]
   cases hφ:φ₂ x <;> simp [hφ]
theorem qc6 (u:List Γ₁):
 ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (qM φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:zG Γ₀ Γ₁))=
     some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
 intro t
 induction t with
 | nil=>intro c s;exact qda φ₁ φ₂ d s c u
 | cons x t ih=>
   intro c s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (qM φ₁ φ₂ d))
    (some (⟨some .c,s,st5 [] [] ((x::t).map some) c u⟩:zG Γ₀ Γ₁))=
    some ⟨some .c,some x,st5 [] [] (t.map some) (some x::c) u⟩:=
    qcN φ₁ φ₂ d s x (t.map some) c u
   rw [e,ih]
   simp
theorem qc5 (hd:d=none→∀ x,φ₁ x=none):
 ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (qM φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:zG Γ₀ Γ₁))=
     some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u s;exact qc9 φ₁ φ₂ d s u
 | cons x t ih=>
   intro u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (qM φ₁ φ₂ d))
    (some (⟨some .e,s,st5 [] [] [] ((x::t).map some) u⟩:zG Γ₀ Γ₁))=
    some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩:=
    qcM φ₁ φ₂ d hd s x (t.map some) u
   rw [e,ih]
   cases hφ:φ₁ x <;> simp [hφ]
theorem qbW [Fintype Γ₀] (hd₁:d=none→∀ x,φ₁ x=none)
 (hd₂:d=none→∀ x,φ₂ x=none) (l:List Γ₀):
 (flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
   (l.length+1)]
   (some (initList (tp φ₁ φ₂ d) l))=
   some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1 +
  (l.length+1)+(l.length+1)+(l.length+1)]
  (some c)) (d4 (tp φ₁ φ₂ d) l)).trans
  (Eq.trans ?_ (congrArg some
    (d5 (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
 show (flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
  (l.length+1)]
  (some (⟨some .a,none,Function.update (fun _=>[]) .inp l⟩:zG Γ₀ Γ₁))=
  some (⟨none,none,Function.update (fun _=>[]) .out
   (l.filterMap φ₁++l.filterMap φ₂)⟩:zG Γ₀ Γ₁)
 have hA:(flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .a,none,st5 l [] [] [] []⟩:zG Γ₀ Γ₁))=
  some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
  simpa using qc8 φ₁ φ₂ d [] [] [] l [] none
 have hB:(flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:zG Γ₀ Γ₁))=
  some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
  have:=qc7 φ₁ φ₂ d hd₂ [] l.reverse [] [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
 have hC:(flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:zG Γ₀ Γ₁))=
  some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
  simpa using qc6 φ₁ φ₂ d (l.filterMap φ₂) l [] none
 have hE:(flip bind (TM2.step (qM φ₁ φ₂ d)))^[l.length+1]
  (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:
    zG Γ₀ Γ₁))=
  some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
  have:=qc5 φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
 rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
  ← qcv,hA,hB,hC,hE,qdd]
theorem d10 {α β αΓ βΓ:Type} [Fintype αΓ] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (φ₁ φ₂:αΓ→Option βΓ)
 (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:∀ φ:αΓ→Option βΓ,d=none→∀ x,φ x=none:=by
  intro φ hdn x
  by_cases hn:Nonempty βΓ
  · simp [d,hn] at hdn
  · cases hφ:φ x with
    | none=>rfl
    | some y=>exact absurd ⟨y⟩ hn
 exact ⟨{
  tm:=tp φ₁ φ₂ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 4 * Polynomial.X+Polynomial.C 4
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
      ((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=
       fun γ l=>by simp
      have:=qbW φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (qM φ₁ φ₂ d)))^[(ea a).length+1 +
       ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
       (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (tp φ₁ φ₂ d) l))
         ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
       Polynomial.eval_X]
      omega } }⟩
end Lib.qz
end
section
namespace Lib.qz
open Turing
inductive FX
 | I | W | T | O
 deriving DecidableEq
instance:Fintype FX:=
 Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x=>by cases x <;> simp)
inductive FL
 | l1 | l2 | l3 | l4 | l5
 deriving DecidableEq
instance:Fintype FL:=
 Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev kn:M.K ⊕ FX→Type
 | Sum.inl k=>M.Γ k
 | Sum.inr FX.I=>Bool ⊕ Bool
 | Sum.inr FX.W=>Bool
 | Sum.inr FX.T=>Bool
 | Sum.inr FX.O=>Bool ⊕ Bool
abbrev wv:Type:=M.Λ ⊕ FL
abbrev ww:Type:=M.σ×Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool)→Bool
 | none=>false
 | some (Sum.inl b)=>b
 | some (Sum.inr b)=>b
def uJ:Option (Bool ⊕ Bool)→Bool
 | some (Sum.inl _)=>true
 | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ→TM2.Stmt (kn M) (wv M) (ww M)
 | .push k f q=>.push (Sum.inl k) (fun s=>f s.1) (trF q)
 | .peek k f q=>.peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .pop k f q=>.pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (trF q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trF q₁) (trF q₂)
 | .goto f=>.goto (fun s=>Sum.inl (f s.1))
 | .halt=>.goto (fun _=>Sum.inr FL.l3)
variable (M)
def d0 (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):
    wv M→TM2.Stmt (kn M) (wv M) (ww M)
 | Sum.inl l=>trF (M.m l)
 | Sum.inr FL.l1=>
   .pop (Sum.inr FX.I) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.branch (fun s=>uJ s.2)
         (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1))
         (.push (Sum.inr FX.W) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1)))
       (.goto fun _=>Sum.inr FL.l2))
 | Sum.inr FL.l2=>
   .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr FL.l2))
       (.goto fun _=>Sum.inl M.main))
 | Sum.inr FL.l3=>
   .pop (Sum.inr FX.W) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr FX.O) (fun s=>Sum.inr (bit s.2)) (.goto fun _=>Sum.inr FL.l3))
       (.goto fun _=>Sum.inr FL.l4))
 | Sum.inr FL.l4=>
   .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l4))
       (.goto fun _=>Sum.inr FL.l5))
 | Sum.inr FL.l5=>
   .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr FX.O) (fun s=>Sum.inl (bit s.2)) (.goto fun _=>Sum.inr FL.l5))
       .halt)
def vC (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool):FinTM2:=
 haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ FX
   k₀:=Sum.inr FX.I
   k₁:=Sum.inr FX.O
   Γ:=kn M
   Λ:=wv M
   main:=Sum.inr FL.l1
   σ:=ww M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
   m:=d0 M e₀ e₁ }
variable {M}
def qv (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)):∀ k,List (kn M k)
 | Sum.inl k=>S k
 | Sum.inr FX.I=>i
 | Sum.inr FX.W=>w
 | Sum.inr FX.T=>t
 | Sum.inr FX.O=>o
section qv
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool))
theorem d23 (k:M.K) (x:List (M.Γ k)):
 Function.update (qv S i w t o) (Sum.inl k) x=qv (Function.update S k x) i w t o:=by
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
theorem d33 (i':List (Bool ⊕ Bool)):
 Function.update (qv S i w t o) (Sum.inr FX.I) i'=qv S i' w t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d45 (w':List Bool):
 Function.update (qv S i w t o) (Sum.inr FX.W) w'=qv S i w' t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d18 (t':List Bool):
 Function.update (qv S i w t o) (Sum.inr FX.T) t'=qv S i w t' o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d46 (o':List (Bool ⊕ Bool)):
 Function.update (qv S i w t o) (Sum.inr FX.O) o'=qv S i w t o':=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
end qv
abbrev zc (M:FinTM2):Type:=TM2.Cfg (kn M) (wv M) (ww M)
def u3 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
    (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):zc M:=
 ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl),(c.var,b),qv c.stk i w t o⟩
theorem qef (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)):
 TM2.stepAux (trF q) ((v,b):ww M) (qv S i w t o)=
  u3 b i w t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>
   have:=ih v (Function.update S k (f v::S k))
   rw [← d23] at this
   exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>
   have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [← d23] at this
   exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [trF,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem qcm (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool) (b:Option (Bool ⊕ Bool))
 (i:List (Bool ⊕ Bool)) (w t:List Bool) (o:List (Bool ⊕ Bool))
 (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c'):
 TM2.step (d0 M e₀ e₁) (u3 b i w t o c)=some (u3 b i w t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (qef b i w t o (M.m l) v S)
end Lib.qz
end
section
namespace Lib.qz
open Turing
theorem d6 {σ:Type} (f:σ→Option σ) {a b:ℕ} {x y z:σ}
 (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z):
 (flip bind f)^[b+a] (some x)=some z:=by
 rw [Function.iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
section qv
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool))
@[simp] theorem qek (k:M.K):qv S i w t o (Sum.inl k)=S k:=rfl
@[simp] theorem qej:qv S i w t o (Sum.inr FX.I)=i:=rfl
@[simp] theorem qen:qv S i w t o (Sum.inr FX.W)=w:=rfl
@[simp] theorem qem:qv S i w t o (Sum.inr FX.T)=t:=rfl
@[simp] theorem qel:qv S i w t o (Sum.inr FX.O)=o:=rfl
end qv
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:List Bool) (o:List (Bool ⊕ Bool))
theorem qbl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l1),(v,b),qv S (Sum.inl a::i) w t o⟩:zc M)=
  some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),qv S i w (a::t) o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33,d18,uJ,bit]
theorem qbm (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l1),(v,b),qv S (Sum.inr a::i) w t o⟩:zc M)=
  some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),qv S i (a::w) t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33,d45,uJ,bit]
theorem qbn (b:Option (Bool ⊕ Bool)) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l1),(v,b),qv S [] w t o⟩:zc M)=
  some ⟨some (Sum.inr FL.l2),(v,none),qv S [] w t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33]
theorem qca:∀ (i:List (Bool ⊕ Bool)) (w t:List Bool) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (d0 M e₀ e₁)))^[i.length+1]
   (some (⟨some (Sum.inr FL.l1),(v,b),qv S i w t o⟩:zc M))=
   some ⟨some (Sum.inr FL.l2),(v,none),
    qv S [] ((i.filterMap Sum.getRight?).reverse++w)
     ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i
 induction i with
 | nil=>intro w t b;exact qbn e₀ e₁ v S w o b t
 | cons x i ih=>
   intro w t b
   rw [List.length_cons,Function.iterate_succ_apply]
   cases x with
   | inl a=>
     have e:flip bind (TM2.step (d0 M e₀ e₁))
      (some (⟨some (Sum.inr FL.l1),(v,b),qv S (Sum.inl a::i) w t o⟩:zc M))=
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),qv S i w (a::t) o⟩:=
      qbl e₀ e₁ v S w o b a i t
     rw [e,ih];simp [List.filterMap_cons]
   | inr a=>
     have e:flip bind (TM2.step (d0 M e₀ e₁))
      (some (⟨some (Sum.inr FL.l1),(v,b),qv S (Sum.inr a::i) w t o⟩:zc M))=
      some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),qv S i (a::w) t o⟩:=
      qbm e₀ e₁ v S w o b a i t
     rw [e,ih];simp [List.filterMap_cons]
theorem qdu (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l2),(v,b),qv S [] w (a::t) o⟩:zc M)=
  some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
   qv (Function.update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem qbo (b:Option (Bool ⊕ Bool)):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l2),(v,b),qv S [] w [] o⟩:zc M)=
  some ⟨some (Sum.inl M.main),(v,none),qv S [] w [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18]
theorem qcb:∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
   (some (⟨some (Sum.inr FL.l2),(v,b),qv S [] w t o⟩:zc M))=
   some ⟨some (Sum.inl M.main),(v,none),
    qv (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
 intro t
 induction t with
 | nil=>
   intro S b
   have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
   rw [this]
   exact qbo e₀ e₁ v S w o b
 | cons a t ih=>
   intro S b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l2),(v,b),qv S [] w (a::t) o⟩:zc M))=
    some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
     qv (Function.update S M.k₀ (e₀ a::S M.k₀)) [] w t o⟩:=qdu e₀ e₁ v S w o b a t
   rw [e,ih];simp
theorem qdt (b:Option (Bool ⊕ Bool)) (a:Bool) (w:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l3),(v,b),qv S [] (a::w) [] o⟩:zc M)=
  some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),qv S [] w [] (Sum.inr a::o)⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d45,d46,bit]
theorem qbp (b:Option (Bool ⊕ Bool)):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l3),(v,b),qv S [] [] [] o⟩:zc M)=
  some ⟨some (Sum.inr FL.l4),(v,none),qv S [] [] [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d45]
theorem qcc:∀ (w:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (d0 M e₀ e₁)))^[w.length+1]
   (some (⟨some (Sum.inr FL.l3),(v,b),qv S [] w [] o⟩:zc M))=
   some ⟨some (Sum.inr FL.l4),(v,none),qv S [] [] [] (w.reverse.map Sum.inr++o)⟩:=by
 intro w
 induction w with
 | nil=>intro o b;exact qbp e₀ e₁ v S o b
 | cons a w ih=>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l3),(v,b),qv S [] (a::w) [] o⟩:zc M))=
    some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),qv S [] w [] (Sum.inr a::o)⟩:=
    qdt e₀ e₁ v S o b a w
   rw [e,ih];simp
theorem qds (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l4),(v,b),qv (Function.update S M.k₁ (y::m)) [] [] t o⟩:
    zc M)=
  some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
   qv (Function.update S M.k₁ m) [] [] (e₁ y::t) o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem qbq (b:Option (Bool ⊕ Bool)) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l4),(v,b),qv (Function.update S M.k₁ []) [] [] t o⟩:zc M)=
  some ⟨some (Sum.inr FL.l5),(v,none),qv (Function.update S M.k₁ []) [] [] t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d23]
theorem qcd:∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
   (some (⟨some (Sum.inr FL.l4),(v,b),qv (Function.update S M.k₁ m) [] [] t o⟩:
     zc M))=
   some ⟨some (Sum.inr FL.l5),(v,none),
    qv (Function.update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact qbq e₀ e₁ v S o b t
 | cons y m ih=>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l4),(v,b),qv (Function.update S M.k₁ (y::m)) [] [] t o⟩:
      zc M))=
    some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
     qv (Function.update S M.k₁ m) [] [] (e₁ y::t) o⟩:=qds e₀ e₁ v S o b y m t
   rw [e,ih];simp
theorem qdr (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l5),(v,b),qv S [] [] (a::t) o⟩:zc M)=
  some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),qv S [] [] t (Sum.inl a::o)⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d46,bit]
theorem qbr (b:Option (Bool ⊕ Bool)):
 TM2.step (d0 M e₀ e₁)
  (⟨some (Sum.inr FL.l5),(v,b),qv S [] [] [] o⟩:zc M)=
  some ⟨none,(v,none),qv S [] [] [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18]
theorem qce:∀ (t:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
 (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
   (some (⟨some (Sum.inr FL.l5),(v,b),qv S [] [] t o⟩:zc M))=
   some ⟨none,(v,none),qv S [] [] [] (t.reverse.map Sum.inl++o)⟩:=by
 intro t
 induction t with
 | nil=>intro o b;exact qbr e₀ e₁ v S o b
 | cons a t ih=>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l5),(v,b),qv S [] [] (a::t) o⟩:zc M))=
    some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),qv S [] [] t (Sum.inl a::o)⟩:=
    qdr e₀ e₁ v S o b a t
   rw [e,ih];simp
end Lib.qz
end
section
namespace Lib.qz
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (e₁:M.Γ M.k₁→Bool)
theorem d97:(qv (fun _=>[]) [] [] [] []:∀ k,List (kn M k))=fun _=>[]:=by
 funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d96 (i:List (Bool ⊕ Bool)):
 (qv (fun _=>[]) i [] [] []:∀ k,List (kn M k))=
   Function.update (fun _=>[]:∀ k,List (kn M k)) (Sum.inr FX.I) i:=
 (d33 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d97])
theorem d95 (o:List (Bool ⊕ Bool)):
 (qv (fun _=>[]) [] [] [] o:∀ k,List (kn M k))=
   Function.update (fun _=>[]:∀ k,List (kn M k)) (Sum.inr FX.O) o:=
 (d46 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d97])
theorem qcz (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)):
 u3 b i w t o (initList M l)=
  (⟨some (Sum.inl M.main),(M.initialState,b),
    qv (Function.update (fun _=>[]) M.k₀ l) i w t o⟩:zc M):=by
 rw [d4];rfl
theorem qcA (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)):
 u3 b i w t o (haltList M m)=
  (⟨some (Sum.inr FL.l3),(M.initialState,b),
    qv (Function.update (fun _=>[]) M.k₁ m) i w t o⟩:zc M):=by
 rw [d5];rfl
theorem d16 {γ δ:Type} (l:List γ):
 l.filterMap (fun _=>(none:Option δ))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
theorem d26 (x w:List Bool):
 (encodePair (x,w)).filterMap Sum.getLeft?=x:=by
 have h1:(Sum.getLeft? ∘ (Sum.inl:Bool→Bool ⊕ Bool):Bool→Option Bool)=some:=rfl
 have h2:(Sum.getLeft? ∘ (Sum.inr:Bool→Bool ⊕ Bool):Bool→Option Bool)=fun _=>none:=rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
  List.filterMap_some,d16,List.append_nil]
theorem d24 (x w:List Bool):
 (encodePair (x,w)).filterMap Sum.getRight?=w:=by
 have h1:(Sum.getRight? ∘ (Sum.inl:Bool→Bool ⊕ Bool):Bool→Option Bool)=fun _=>none:=rfl
 have h2:(Sum.getRight? ∘ (Sum.inr:Bool→Bool ⊕ Bool):Bool→Option Bool)=some:=rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
  List.filterMap_some,d16,List.nil_append]
theorem d9 (x w:List Bool):
 (encodePair (x,w)).length=x.length+w.length:=by
 simp [encodePair]
theorem qcw (x w0:List Bool) (m:List (M.Γ M.k₁)) (s:ℕ)
 (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)):
 ∃ n,n≤ s+2 * x.length+2 * w0.length+2 * m.length+5∧
   (flip bind (TM2.step (d0 M e₀ e₁)))^[n]
     (some (initList (vC M e₀ e₁) (encodePair (x,w0))))=
     some (haltList (vC M e₀ e₁) (encodePair (m.map e₁,w0))):=by
 have q1:(flip bind (TM2.step (d0 M e₀ e₁)))^[(encodePair (x,w0)).length+1]
  (some (initList (vC M e₀ e₁) (encodePair (x,w0))))=
  some (⟨some (Sum.inr FL.l2),(M.initialState,none),
   qv (fun _=>[]) [] w0.reverse x.reverse []⟩:zc M):=by
  have:=qca e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none
  rw [d26,d24,List.append_nil,List.append_nil,d96] at this
  exact (congrArg (fun c=>(flip bind (TM2.step (d0 M e₀ e₁)))^[
   (encodePair (x,w0)).length+1] (some c))
   (d4 (vC M e₀ e₁) (encodePair (x,w0)))).trans this
 have q2:(flip bind (TM2.step (d0 M e₀ e₁)))^[x.reverse.length+1]
  (some (⟨some (Sum.inr FL.l2),(M.initialState,none),
    qv (fun _=>[]) [] w0.reverse x.reverse []⟩:zc M))=
  some (u3 none [] w0.reverse [] [] (initList M (x.map e₀))):=by
  have:=qcb e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none
  rw [qcz]
  simpa using this
 have q3:=d59 (TM2.step M.m) (TM2.step (d0 M e₀ e₁))
  (u3 none [] w0.reverse [] []) (qcm e₀ e₁ none [] w0.reverse [] []) s _ _ h
 rw [qcA] at q3
 have q4:(flip bind (TM2.step (d0 M e₀ e₁)))^[w0.reverse.length+1]
  (some (⟨some (Sum.inr FL.l3),(M.initialState,none),
    qv (Function.update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:zc M))=
  some (⟨some (Sum.inr FL.l4),(M.initialState,none),
   qv (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:zc M):=by
  have:=qcc e₀ e₁ M.initialState (Function.update (fun _=>[]) M.k₁ m) w0.reverse [] none
  simpa using this
 have q5:(flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
  (some (⟨some (Sum.inr FL.l4),(M.initialState,none),
    qv (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:zc M))=
  some (⟨some (Sum.inr FL.l5),(M.initialState,none),
   qv (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:zc M):=by
  have:=qcd e₀ e₁ M.initialState (fun _=>[]) (w0.map Sum.inr) m [] none
  simpa using this
 have q6:(flip bind (TM2.step (d0 M e₀ e₁)))^[(m.reverse.map e₁).length+1]
  (some (⟨some (Sum.inr FL.l5),(M.initialState,none),
    qv (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:zc M))=
  some (haltList (vC M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have:=qce e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map Sum.inr) none
  rw [d95] at this
  refine this.trans (Eq.trans ?_
   (congrArg some (d5 (vC M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
  simp [encodePair]
  rfl
 refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3)
  q4) q5) q6⟩
 simp only [d9,List.length_reverse,List.length_map]
 omega
theorem d61 (f:List Bool→List Bool)
 (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f):
 Nonempty (TM2ComputableInPolyTime encodePair encodePair
  (fun p:List Bool×List Bool=>(f p.1,p.2))):=by
 let e₀:Bool→c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
 let e₁:c.tm.Γ c.tm.k₁→Bool:=c.outputAlphabet
 let T:Polynomial ℕ:=
  c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c.tm) * c.time) +
   Polynomial.C 2 * Polynomial.X+Polynomial.C 5
 have key:∀ p:List Bool×List Bool,∃ n,n≤T.eval (encodePair p).length∧
  (flip bind (TM2.step (d0 c.tm e₀ e₁)))^[n]
    (some (initList (vC c.tm e₀ e₁) (encodePair p)))=
    some (haltList (vC c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
  rintro ⟨x,w⟩
  have hs:∃ s,s≤Polynomial.eval x.length c.time∧
   (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀)))=
     some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))):=
   ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
  obtain ⟨s,b1,h⟩:=hs
  obtain ⟨n,hn,hrun⟩:=qcw e₀ e₁ x w _ s h
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
   c.tm.k₁).length≤x.length:=by
   by_cases hk:c.tm.k₁=c.tm.k₀
   · rw [hk,Function.update_self,List.length_map]
   · rw [Function.update_of_ne hk];simp
  have b2:Polynomial.eval x.length c.time≤Polynomial.eval (x.length+w.length) c.time:=
   d37 _ (by omega)
  have hmul:maxPush c.tm * s≤
   maxPush c.tm * Polynomial.eval (x.length+w.length) c.time:=
   Nat.mul_le_mul_left _ (b1.trans b2)
  simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_X,d9,List.length_map]
  omega
 exact ⟨{
  tm:=vC c.tm e₀ e₁
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun p=>
   { steps:=Classical.choose (key p)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=
       fun γ l=>by simp
      exact (congrArg (fun l=>(flip bind (TM2.step (d0 c.tm e₀ e₁)))^[
       Classical.choose (key p)] (some (initList (vC c.tm e₀ e₁) l)))
       (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
       (congrArg (fun l=>some (haltList (vC c.tm e₀ e₁) l))
         (hm _ (encodePair (f p.1,p.2))).symm))
     steps_le_m:=(Classical.choose_spec (key p)).1 } }⟩
end Lib.qz
end
section
namespace Lib.qz.y1
open Turing
inductive IX
 | I | C | T | O
 deriving DecidableEq
instance:Fintype IX:=
 Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x=>by cases x <;> simp)
inductive IL
 | l1 | l2 | l3 | l4 | l5 | l6
 deriving DecidableEq
instance:Fintype IL:=
 Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev ItΓ:M.K ⊕ IX→Type
 | Sum.inl k=>M.Γ k
 | Sum.inr IX.I=>Bool ⊕ Bool
 | Sum.inr IX.C=>Bool
 | Sum.inr IX.T=>Bool
 | Sum.inr IX.O=>Bool
abbrev ItΛ:Type:=M.Λ ⊕ IL
abbrev Itσ:Type:=M.σ×Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ→TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | .push k f q=>.push (Sum.inl k) (fun s=>f s.1) (trI q)
 | .peek k f q=>.peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .pop k f q=>.pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .load a q=>.load (fun s=>(a s.1,s.2)) (trI q)
 | .branch f q₁ q₂=>.branch (fun s=>f s.1) (trI q₁) (trI q₂)
 | .goto f=>.goto (fun s=>Sum.inl (f s.1))
 | .halt=>.goto (fun _=>Sum.inr IL.l4)
variable (M)
def d1 (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool):
    ItΛ M→TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | Sum.inl l=>trI (M.m l)
 | Sum.inr IL.l1=>
   .pop (Sum.inr IX.I) (fun s o=>(s.1,o))
     (.branch (fun s=>s.2.isSome)
       (.branch (fun s=>uJ s.2)
         (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1))
         (.push (Sum.inr IX.C) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1)))
       (.goto fun _=>Sum.inr IL.l2))
 | Sum.inr IL.l2=>
   .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr IL.l2))
       (.goto fun _=>Sum.inr IL.l3))
 | Sum.inr IL.l3=>
   .pop (Sum.inr IX.C) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.goto fun _=>Sum.inl M.main)
       (.goto fun _=>Sum.inr IL.l5))
 | Sum.inr IL.l4=>
   .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l4))
       (.goto fun _=>Sum.inr IL.l2))
 | Sum.inr IL.l5=>
   .pop (Sum.inl M.k₀) (fun s o=>(s.1,o.map fun y=>Sum.inl (d₀ y)))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l5))
       (.goto fun _=>Sum.inr IL.l6))
 | Sum.inr IL.l6=>
   .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
     (.branch (fun s=>s.2.isSome)
       (.push (Sum.inr IX.O) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l6))
       .halt)
def yd (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool):FinTM2:=
 haveI:=M.kFin
 haveI:=M.ΛFin
 haveI:=M.σFin
 { K:=M.K ⊕ IX
   k₀:=Sum.inr IX.I
   k₁:=Sum.inr IX.O
   Γ:=ItΓ M
   Λ:=ItΛ M
   main:=Sum.inr IL.l1
   σ:=Itσ M
   initialState:=(M.initialState,none)
   Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
   m:=d1 M e₀ d₀ e₁ }
variable {M}
def qt (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool):
    ∀ k,List (ItΓ M k)
 | Sum.inl k=>S k
 | Sum.inr IX.I=>i
 | Sum.inr IX.C=>cn
 | Sum.inr IX.T=>t
 | Sum.inr IX.O=>o
section qt
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
@[simp] theorem qeq (k:M.K):qt S i cn t o (Sum.inl k)=S k:=rfl
@[simp] theorem qep:qt S i cn t o (Sum.inr IX.I)=i:=rfl
@[simp] theorem qeo:qt S i cn t o (Sum.inr IX.C)=cn:=rfl
@[simp] theorem qes:qt S i cn t o (Sum.inr IX.T)=t:=rfl
@[simp] theorem qer:qt S i cn t o (Sum.inr IX.O)=o:=rfl
theorem d15 (k:M.K) (x:List (M.Γ k)):
 Function.update (qt S i cn t o) (Sum.inl k) x=qt (Function.update S k x) i cn t o:=by
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
theorem d32 (i':List (Bool ⊕ Bool)):
 Function.update (qt S i cn t o) (Sum.inr IX.I) i'=qt S i' cn t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d44 (cn':List Bool):
 Function.update (qt S i cn t o) (Sum.inr IX.C) cn'=qt S i cn' t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d14 (t':List Bool):
 Function.update (qt S i cn t o) (Sum.inr IX.T) t'=qt S i cn t' o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d72 (o':List Bool):
 Function.update (qt S i cn t o) (Sum.inr IX.O) o'=qt S i cn t o':=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
end qt
abbrev zo (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def u4 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
    (c:TM2.Cfg M.Γ M.Λ M.σ):zo M:=
 ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl),(c.var,b),qt c.stk i cn t o⟩
theorem qeg (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
 (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)):
 TM2.stepAux (trI q) ((v,b):Itσ M) (qt S i cn t o)=
  u4 b i cn t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih=>
   have:=ih v (Function.update S k (f v::S k))
   rw [← d15] at this
   exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih=>
   have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
   rw [← d15] at this
   exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [trI,TM2.stepAux]
   cases f v
   · exact ih₂ v S
   · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem qcn (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
 (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c'):
 TM2.step (d1 M e₀ d₀ e₁) (u4 b i cn t o c)=some (u4 b i cn t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
   simp only [TM2.step,Option.some.injEq] at h
   subst h
   exact congrArg some (qeg b i cn t o (M.m l) v S)
theorem qcx (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
 (l:List (M.Γ M.k₀)):
 u4 b i cn t o (initList M l)=
  (⟨some (Sum.inl M.main),(M.initialState,b),
    qt (Function.update (fun _=>[]) M.k₀ l) i cn t o⟩:zo M):=by
 rw [d4];rfl
theorem qcy (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
 (m:List (M.Γ M.k₁)):
 u4 b i cn t o (haltList M m)=
  (⟨some (Sum.inr IL.l4),(M.initialState,b),
    qt (Function.update (fun _=>[]) M.k₁ m) i cn t o⟩:zo M):=by
 rw [d5];rfl
theorem d94:(qt (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by
 funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d93 (i:List (Bool ⊕ Bool)):
 (qt (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k))=
   Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.I) i:=
 (d32 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d94])
theorem d92 (o:List Bool):
 (qt (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k))=
   Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.O) o:=
 (d72 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d94])
end Lib.qz.y1
end
section
namespace Lib.qz.y1
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
theorem qbt (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l1),(v,b),qt S (Sum.inl a::i) cn t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),qt S i cn (a::t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32,d14,uJ,bit]
theorem qbu (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l1),(v,b),qt S (Sum.inr a::i) cn t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),qt S i (a::cn) t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32,d44,uJ,bit]
theorem qbv (b:Option (Bool ⊕ Bool)) (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l1),(v,b),qt S [] cn t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l2),(v,none),qt S [] cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32]
theorem qbB (o:List Bool):
 ∀ (i:List (Bool ⊕ Bool)) (cn t:List Bool) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[i.length+1]
    (some (⟨some (Sum.inr IL.l1),(v,b),qt S i cn t o⟩:zo M))=
   some ⟨some (Sum.inr IL.l2),(v,none),
    qt S [] ((i.filterMap Sum.getRight?).reverse++cn)
     ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i
 induction i with
 | nil=>intro cn t b;exact qbv e₀ d₀ e₁ v S b cn t o
 | cons x i ih=>
   intro cn t b
   rw [List.length_cons,Function.iterate_succ_apply]
   cases x with
   | inl a=>
     have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
      (some (⟨some (Sum.inr IL.l1),(v,b),qt S (Sum.inl a::i) cn t o⟩:zo M))=
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),qt S i cn (a::t) o⟩:=
      qbt e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih];simp [List.filterMap_cons]
   | inr a=>
     have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
      (some (⟨some (Sum.inr IL.l1),(v,b),qt S (Sum.inr a::i) cn t o⟩:zo M))=
      some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),qt S i (a::cn) t o⟩:=
      qbu e₀ d₀ e₁ v S b a i cn t o
     rw [e,ih];simp [List.filterMap_cons]
theorem qdk (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l2),(v,b),qt S i cn (a::t) o⟩:zo M)=
  some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
   qt (Function.update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem qbw (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l2),(v,b),qt S i cn [] o⟩:zo M)=
  some ⟨some (Sum.inr IL.l3),(v,none),qt S i cn [] o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14]
theorem qaQ (i:List (Bool ⊕ Bool)) (cn o:List Bool):
 ∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (Sum.inr IL.l2),(v,b),qt S i cn t o⟩:zo M))=
   some ⟨some (Sum.inr IL.l3),(v,none),
    qt (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
 intro t
 induction t with
 | nil=>
   intro S b
   have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
   rw [this]
   exact qbw e₀ d₀ e₁ v S b i cn o
 | cons a t ih=>
   intro S b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l2),(v,b),qt S i cn (a::t) o⟩:zo M))=
    some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
     qt (Function.update S M.k₀ (e₀ a::S M.k₀)) i cn t o⟩:=
    qdk e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih];simp
theorem qdj (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l3),(v,b),qt S i (a::cn) t o⟩:zo M)=
  some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),qt S i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d44]
theorem qbx (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l3),(v,b),qt S i [] t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l5),(v,none),qt S i [] t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d44]
theorem qdi (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
 (i:List (Bool ⊕ Bool)) (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l4),(v,b),qt (Function.update S M.k₁ (y::m)) i cn t o⟩:
    zo M)=
  some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
   qt (Function.update S M.k₁ m) i cn (e₁ y::t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem qby (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l4),(v,b),qt (Function.update S M.k₁ []) i cn t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l2),(v,none),qt (Function.update S M.k₁ []) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d15]
theorem qbC (i:List (Bool ⊕ Bool)) (cn o:List Bool):
 ∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (Sum.inr IL.l4),(v,b),qt (Function.update S M.k₁ m) i cn t o⟩:
      zo M))=
   some ⟨some (Sum.inr IL.l2),(v,none),
    qt (Function.update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact qby e₀ d₀ e₁ v S b i cn t o
 | cons y m ih=>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l4),(v,b),
      qt (Function.update S M.k₁ (y::m)) i cn t o⟩:zo M))=
    some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
     qt (Function.update S M.k₁ m) i cn (e₁ y::t) o⟩:=
    qdi e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih];simp
theorem qdh (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
 (i:List (Bool ⊕ Bool)) (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l5),(v,b),qt (Function.update S M.k₀ (y::m)) i cn t o⟩:
    zo M)=
  some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
   qt (Function.update S M.k₀ m) i cn (d₀ y::t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem qbz (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l5),(v,b),qt (Function.update S M.k₀ []) i cn t o⟩:zo M)=
  some ⟨some (Sum.inr IL.l6),(v,none),qt (Function.update S M.k₀ []) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d15]
theorem qbD (i:List (Bool ⊕ Bool)) (cn o:List Bool):
 ∀ (m:List (M.Γ M.k₀)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (Sum.inr IL.l5),(v,b),qt (Function.update S M.k₀ m) i cn t o⟩:
      zo M))=
   some ⟨some (Sum.inr IL.l6),(v,none),
    qt (Function.update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact qbz e₀ d₀ e₁ v S b i cn t o
 | cons y m ih=>
   intro t b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l5),(v,b),
      qt (Function.update S M.k₀ (y::m)) i cn t o⟩:zo M))=
    some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
     qt (Function.update S M.k₀ m) i cn (d₀ y::t) o⟩:=
    qdh e₀ d₀ e₁ v S b y m i cn t o
   rw [e,ih];simp
theorem qdg (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
 (cn t o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l6),(v,b),qt S i cn (a::t) o⟩:zo M)=
  some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),qt S i cn t (a::o)⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d72,bit]
theorem qbA (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool):
 TM2.step (d1 M e₀ d₀ e₁)
  (⟨some (Sum.inr IL.l6),(v,b),qt S i cn [] o⟩:zo M)=
  some ⟨none,(v,none),qt S i cn [] o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14]
theorem qbE (i:List (Bool ⊕ Bool)) (cn:List Bool):
 ∀ (t o:List Bool) (b:Option (Bool ⊕ Bool)),
 ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (Sum.inr IL.l6),(v,b),qt S i cn t o⟩:zo M))=
   some ⟨none,(v,none),qt S i cn [] (t.reverse++o)⟩:=by
 intro t
 induction t with
 | nil=>intro o b;exact qbA e₀ d₀ e₁ v S b i cn o
 | cons a t ih=>
   intro o b
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l6),(v,b),qt S i cn (a::t) o⟩:zo M))=
    some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),qt S i cn t (a::o)⟩:=
    qdg e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih];simp
theorem d28 (k:M.K):
 Function.update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[]:=
 Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
end Lib.qz.y1
end
section
namespace Lib.qz.y1
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool→M.Γ M.k₀) (d₀:M.Γ M.k₀→Bool) (e₁:M.Γ M.k₁→Bool)
theorem d71 (g:List Bool→List Bool) (p:Polynomial ℕ)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧
   (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧
     m.map e₁=g z):
 ∀ (cn z:List Bool) (L:ℕ) (b:Option (Bool ⊕ Bool)),
   (∀ j≤cn.length,(g^[j] z).length≤L)→
   ∃ n,n≤cn.length * (p.eval L+2 * L+3)+2 * L+3∧
     ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
        (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
          qt (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:zo M))=
       some ⟨none,(M.initialState,none),
        qt (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
 intro cn
 induction cn with
 | nil=>
   intro z L b hL
   have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
    rw [List.map_reverse,List.reverse_reverse,List.map_map]
    conv_rhs=>rw [← List.map_id z]
    exact List.map_congr_left fun a _=>hd a
   have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
    (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
      qt (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:zo M))=
    some ⟨some (Sum.inr IL.l5),(M.initialState,none),
     qt (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:=
    qbx e₀ d₀ e₁ M.initialState _ b [] [] []
   have q2:=qbD e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none
   rw [d28,List.append_nil] at q2
   have q3:=qbE e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
    ((z.map e₀).reverse.map d₀) [] none
   rw [List.append_nil,hz] at q3
   refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3⟩
   have hz0:z.length≤L:=hL 0 (Nat.zero_le _)
   simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
   omega
 | cons a cn ih=>
   intro z L b hL
   obtain ⟨s,m,hs,hm,hmg⟩:=hrun z
   rw [List.length_cons] at hL
   have hz0:z.length≤L:=hL 0 (Nat.zero_le _)
   have hgz:(g z).length≤L:=hL 1 (by omega)
   have hml:m.length=(g z).length:=by rw [← hmg,List.length_map]
   have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
    (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
      qt (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] (a::cn) [] []⟩:zo M))=
    some (u4 (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))):=by
    rw [qcx]
    exact qdj e₀ d₀ e₁ M.initialState _ b a [] cn [] []
   have q2:=d59 (TM2.step M.m) (TM2.step (d1 M e₀ d₀ e₁))
    (u4 (some (Sum.inl a)) [] cn [] []) (qcn e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
    s _ _ hm
   rw [qcy] at q2
   have q3:=qbC e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (Sum.inl a))
   rw [d28,List.append_nil,List.map_reverse,hmg] at q3
   have q4:=qaQ e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none
   rw [List.append_nil,List.reverse_reverse] at q4
   obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by
    have:=hL (j+1) (by omega)
    rwa [Function.iterate_succ_apply] at this)
   have e:g^[(a::cn).length] z=g^[cn.length] (g z):=Function.iterate_succ_apply g _ z
   rw [e]
   refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3) q4) q5⟩
   have hp:p.eval z.length≤p.eval L:=d37 p (by omega)
   rw [List.length_reverse,List.length_cons,Nat.succ_mul]
   generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
   omega
theorem d80 (g:List Bool→List Bool) (p:Polynomial ℕ)
 (hd:∀ a,d₀ (e₀ a)=a)
 (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s≤p.eval z.length∧
   (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m)∧
     m.map e₁=g z)
 (y u:List Bool) (L:ℕ) (hL:∀ j≤u.length,(g^[j] y).length≤L):
 ∃ n,n≤u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5∧
   ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n] (some (initList (yd M e₀ d₀ e₁) (encodePair (y,u))))=
     some (haltList (yd M e₀ d₀ e₁) (g^[u.length] y)):=by
 have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
  (some (initList (yd M e₀ d₀ e₁) (encodePair (y,u))))=
  some (⟨some (Sum.inr IL.l2),(M.initialState,none),
   qt (fun _=>[]) [] u.reverse y.reverse []⟩:zo M):=by
  have:=qbB e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
  rw [d26,d24,List.append_nil,List.append_nil,d93] at this
  exact (congrArg (fun c=>((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
   (d4 (yd M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2:=qaQ e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none
 rw [List.append_nil,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩:=d71 e₀ d₀ e₁ g p hd hrun u.reverse y L none
  (by rw [List.length_reverse];exact hL)
 rw [List.length_reverse] at hn q3
 rw [d92] at q3
 have q3':((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
  (some (⟨some (Sum.inr IL.l3),(M.initialState,none),
    qt (Function.update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:zo M))=
  some (haltList (yd M e₀ d₀ e₁) (g^[u.length] y)):=
  q3.trans (congrArg some (d5 (yd M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3'⟩
 rw [d9,List.length_reverse]
 omega
theorem d22 (g:List Bool→List Bool) (m:List Bool→ℕ)
 (hm:∀ y:List Bool,m (g y)≤ m y)
 (hg:∀ y:List Bool,(g y).length≤y.length+m y) (y:List Bool):
 ∀ j:ℕ,m (g^[j] y)≤ m y∧(g^[j] y).length≤y.length+j * m y:=by
 intro j
 induction j with
 | zero=>simp
 | succ j ih=>
   rw [Function.iterate_succ_apply',Nat.succ_mul]
   have h1:=hm (g^[j] y)
   have h2:=hg (g^[j] y)
   obtain ⟨i1,i2⟩:=ih
   generalize j * m y=A at i2 ⊢
   exact ⟨by omega,by omega⟩
theorem d70 (A B L V y u:ℕ) (hLV:L≤V) (hAB:A≤B):
 A+2 * L+2 * y+u+5≤B+2 * V+3 * (y+u)+5:=by
 omega
theorem vj (g:List Bool→List Bool)
 (c:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
 (m:List Bool→ℕ) (a:ℕ)
 (hm:∀ y:List Bool,m (g y)≤ m y)
 (hg:∀ y:List Bool,(g y).length≤y.length+m y)
 (ha:∀ y:List Bool,m y≤a * y.length+a):
 Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:List Bool=>x) (fun p:List Bool×List Bool=>g^[p.2.length] p.1)):=by
 let e₀:Bool→c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
 let d₀:c.tm.Γ c.tm.k₀→Bool:=c.inputAlphabet
 let e₁:c.tm.Γ c.tm.k₁→Bool:=c.outputAlphabet
 let W:Polynomial ℕ:=
  Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
 let T:Polynomial ℕ:=
  Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
   Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
 have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
 have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
  s≤c.time.eval z.length∧
  (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀)))=
    some (haltList c.tm m)∧m.map e₁=g z:=by
  intro z
  refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
   (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
  rw [List.map_map]
  conv_rhs=>rw [← List.map_id (g z)]
  exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
 have key:∀ q:List Bool×List Bool,∃ n,n≤T.eval (encodePair q).length∧
  (flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[n]
    (some (initList (yd c.tm e₀ d₀ e₁) (encodePair q)))=
    some (haltList (yd c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
  rintro ⟨y,u⟩
  have hL:∀ j≤u.length,
   (g^[j] y).length≤y.length+u.length * (a * y.length+a):=by
   intro j hj
   have h1:=(d22 g m hm hg y j).2
   have h2:j * m y≤u.length * (a * y.length+a):=Nat.mul_le_mul hj (ha y)
   omega
  obtain ⟨n,hn,hr⟩:=d80 e₀ d₀ e₁ g c.time hd hrun y u
   (y.length+u.length * (a * y.length+a)) hL
  have hLV:y.length+u.length * (a * y.length+a)≤
   (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a):=
   Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
  have hp:=d37 c.time hLV
  have hmul:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
        2 * (y.length+u.length * (a * y.length+a))+3)≤
   (y.length+u.length) * (Polynomial.eval
     ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))
       c.time +
       2 * ((y.length+u.length) +
         (y.length+u.length) * (a * (y.length+u.length)+a))+3):=
   Nat.mul_le_mul (by omega) (by omega)
  refine ⟨n,hn.trans ?_,hr⟩
  simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_X,Polynomial.eval_comp,d9]
  exact d70 _ _ _ _ _ _ hLV hmul
 exact ⟨{
  tm:=yd c.tm e₀ d₀ e₁
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=T
  outputsFun:=fun q=>
   { steps:=Classical.choose (key q)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=
       fun γ l=>by simp
      exact (congrArg (fun l=>(flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[
       Classical.choose (key q)] (some (initList (yd c.tm e₀ d₀ e₁) l)))
       (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
       (congrArg (fun l=>some (haltList (yd c.tm e₀ d₀ e₁) l))
         (hm _ (g^[q.2.length] q.1)).symm))
     steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
theorem vT (g:List Bool→List Bool)
 (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
 (k:ℕ) (hk:∀ y:List Bool,(g y).length≤y.length+k):
 ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>g^[p.2.length] p.1):=
 vj g c (fun _=>k) k (fun _=>le_rfl) hk (fun _=>Nat.le_add_left k _)
end Lib.qz.y1
end
section
namespace Lib.qz
open PEqualNP.Library
private theorem d2 {α β γ:Type} (h:α→β) (φ:β→Option γ) (g:α→γ)
 (hφ:∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ=l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
private theorem d8 {α β γ:Type} (h:α→β) (φ:β→Option γ)
 (hφ:∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
theorem qa {α β γ αΓ βΓ γΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {ec:γ→List γΓ} {f:α→β} {g:β→γ}
 (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
 (hg:PEqualNP.Library.ComputableInPolyTime eb ec g):
 PEqualNP.Library.ComputableInPolyTime ea ec (fun a=>g (f a)):=by
 obtain ⟨c1⟩:=hf
 obtain ⟨c2⟩:=hg
 exact d77 ea eb ec f g c1 c2
theorem d84:
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:List Bool×List Bool=>(p.2,p.1)):=by
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
theorem qdx:
 PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
  PEqualNP.Library.encodePair (fun x:List Bool=>(x,x)):=by
 refine d10 _ _ _
  (fun b:Bool=>some (Sum.inl b)) (fun b:Bool=>some (Sum.inr b)) ?_
 intro x
 have h1:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inl (β:=Bool) b))
  Sum.inl (fun _=>rfl) x
 have h2:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inr (α:=Bool) b))
  Sum.inr (fun _=>rfl) x
 simp only [List.map_id'] at h1 h2
 simp only [encodePair,h1,h2]
theorem qdw:
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:List Bool=>x) (fun p:List Bool×List Bool=>p.1):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
  d8 Sum.inr _ (fun _=>rfl) w]
 simp
theorem qdv:
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:List Bool=>x) (fun p:List Bool×List Bool=>p.2):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d8 Sum.inl _ (fun _=>rfl) x,
  d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
 simp
theorem d74:
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  (fun x:List Bool=>x) (fun p:List Bool×List Bool=>p.1++p.2):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
  d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
 simp
theorem d38 {f:List Bool→List Bool}
 (hf:Lib.qe f):
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:List Bool×List Bool=>(f p.1,p.2)):=by
 obtain ⟨c⟩:=hf
 exact d61 f c
theorem qcq {g:List Bool→List Bool}
 (hg:Lib.qe g):
 PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
  PEqualNP.Library.encodePair (fun p:List Bool×List Bool=>(p.1,g p.2)):=
 qa (qa d84 (d38 hg)) d84
theorem vn {f g:List Bool→List Bool}
 (hf:Lib.qe f)
 (hg:Lib.qe g):
 PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
  PEqualNP.Library.encodePair (fun x:List Bool=>(f x,g x)):=
 qa (qa qdx (qcq hg)) (d38 hf)
theorem wD:
 Lib.qe (fun x:List Bool=>x):=by
 refine d7 _ _ _ (fun b:Bool=>some b) ?_
 intro x
 have h:=d2 (fun b:Bool=>b) (fun b:Bool=>some b) (fun b=>b)
  (fun _=>rfl) x
 simp only [List.map_id'] at h
 exact h.symm
end Lib.qz
end
section
namespace Lib.qz
open Turing
def ql {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁) (fin:Q→Option Γ₁):
    Q→List Γ₀→List Γ₁
 | q,[]=>(fin q).toList
 | q,a::l=>(δ q a).2.toList++ql δ fin (δ q a).1 l
def zB {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁):
    Q→List Γ₀→List Γ₁
 | q,[]=>(fin q).toList
 | q,a::l=>(δ q a).2.1.toList++(δ q a).2.2.toList++zB δ fin (δ q a).1 l
theorem d36 {Γ₀ Γ₁ Q:Type} (δ:Q→Γ₀→Q×Option Γ₁) (fin:Q→Option Γ₁)
 (q:Q) (l:List Γ₀):
 ql δ fin q l=zB (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [ql,zB,ih]
inductive TrK:Type
 | inp | tmp | out
 deriving DecidableEq
instance:Fintype TrK:=
 Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK→Type
 | .inp=>Γ₀
 | .tmp=>Q×Option Γ₀
 | .out=>Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q×Option Γ₀×Bool
def qaF (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁):
    Q×Option Γ₀→Option Γ₁
 | (q,some a)=>(δ q a).2.1
 | (q,none)=>fin q
def qaG (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁):Q×Option Γ₀→Option Γ₁
 | (q,some a)=>(δ q a).2.2
 | (_,none)=>none
def kV (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁)
    (e:Q×Option Γ₀):List Γ₁:=
 (qaF δ fin e).toList++(qaG δ e).toList
def d21 (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁):Q→List Γ₀→List (Q×Option Γ₀)
 | q,[]=>[(q,none)]
 | q,a::l=>(q,some a)::d21 δ (δ q a).1 l
theorem d57 (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (q:Q) (l:List Γ₀):
 (d21 δ q l).length=l.length+1:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [d21,ih]
theorem d85 (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q:Q)
 (l:List Γ₀):(d21 δ q l).flatMap (kV δ fin)=zB δ fin q l:=by
 induction l generalizing q with
 | nil=>simp [d21,kV,qaF,qaG,zB]
 | cons a l ih=>simp [d21,kV,qaF,qaG,zB,ih]
def d65 (o:TrS Γ₀ Q→Option Γ₁) (d:Option Γ₁)
    (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)):
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q):=
 .branch (fun s=>(o s).isSome)
   (match d with
     | some dd=>.push .out (fun s=>(o s).getD dd) next
     | none=>next)
   next
def zA (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q₀:Q)
    (d:Option Γ₁):Bool→TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
 | false=>
   .pop .inp (fun s o=>(s.1,o,o.isSome))
     (.branch (fun s=>s.2.2)
       (.push .tmp (fun s=>(s.1,s.2.1))
         (.load (fun s=>(match s.2.1 with
            | some a=>(δ s.1 a).1
            | none=>s.1,none,false))
           (.goto fun _=>false)))
       (.push .tmp (fun s=>(s.1,none))
         (.load (fun _=>(q₀,none,false)) (.goto fun _=>true))))
 | true=>
   .pop .tmp (fun _ o=>match o with
     | some e=>(e.1,e.2,true)
     | none=>(q₀,none,false))
     (.branch (fun s=>s.2.2)
       (d65 (fun s=>qaG δ (s.1,s.2.1)) d
         (d65 (fun s=>qaF δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
       .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁)
    (fin:Q→Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
 K:=TrK
 k₀:=.inp
 k₁:=.out
 Γ:=TrΓ Γ₀ Γ₁ Q
 Λ:=Bool
 main:=false
 σ:=TrS Γ₀ Q
 initialState:=(q₀,none,false)
 Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
 m:=zA δ fin q₀ d
def zd (l:List Γ₀) (t:List (Q×Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
 | .inp=>l
 | .tmp=>t
 | .out=>u
theorem d40 (l l':List Γ₀) (t:List (Q×Option Γ₀)) (u:List Γ₁):
 Function.update (zd l t u) .inp l'=zd l' t u:=by
 funext k;cases k <;> simp [zd]
theorem d19 (l:List Γ₀) (t t':List (Q×Option Γ₀)) (u:List Γ₁):
 Function.update (zd l t u) .tmp t'=zd l t' u:=by
 funext k;cases k <;> simp [zd]
theorem d78 (l:List Γ₀) (t:List (Q×Option Γ₀)) (u u':List Γ₁):
 Function.update (zd l t u) .out u'=zd l t u':=by
 funext k;cases k <;> simp [zd]
theorem d87 (l:List Γ₀):
 (zd l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k))=
   Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
 funext k;cases k <;> simp [zd]
theorem qcJ (u:List Γ₁):
 (zd [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k))=
   Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
 funext k;cases k <;> simp [zd]
abbrev vR (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem d25 (o:TrS Γ₀ Q→Option Γ₁) (d:Option Γ₁) (hd:∀ _:Γ₁,d≠none)
 (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
 (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.stepAux (d65 o d next) s (zd l t u)=
  TM2.stepAux next s (zd l t ((o s).toList++u)):=by
 cases ho:o s with
 | none=>cases d <;> simp [d65,TM2.stepAux,ho]
 | some y=>
   cases d with
   | none=>exact absurd rfl (hd y)
   | some dd=>simp [d65,TM2.stepAux,ho,zd,d78]
variable (δ:Q→Γ₀→Q×Option Γ₁×Option Γ₁) (fin:Q→Option Γ₁) (q₀:Q)
 (d:Option Γ₁)
theorem qcL (s:TrS Γ₀ Q) (a:Γ₀) (l:List Γ₀) (t:List (Q×Option Γ₀))
 (u:List Γ₁):
 TM2.step (zA δ fin q₀ d) (⟨some false,s,zd (a::l) t u⟩:vR Γ₀ Γ₁ Q)=
  some ⟨some false,((δ s.1 a).1,none,false),zd l ((s.1,some a)::t) u⟩:=by
 simp [TM2.step,zA,TM2.stepAux,zd,d40,d19]
theorem qc4 (s:TrS Γ₀ Q) (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.step (zA δ fin q₀ d) (⟨some false,s,zd [] t u⟩:vR Γ₀ Γ₁ Q)=
  some ⟨some true,(q₀,none,false),zd [] ((s.1,none)::t) u⟩:=by
 simp [TM2.step,zA,TM2.stepAux,zd,d40,d19]
theorem qcK (hd:∀ _:Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q×Option Γ₀)
 (t:List (Q×Option Γ₀)) (u:List Γ₁):
 TM2.step (zA δ fin q₀ d) (⟨some true,s,zd [] (e::t) u⟩:vR Γ₀ Γ₁ Q)=
  some ⟨some true,(e.1,e.2,true),zd [] t (kV δ fin e++u)⟩:=by
 simp only [TM2.step,zA,TM2.stepAux]
 have e1:(zd [] (e::t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e::t:=rfl
 rw [e1]
 simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
 rw [d19,d25 _ _ hd,d25 _ _ hd]
 simp [TM2.stepAux,kV]
theorem qc3 (s:TrS Γ₀ Q) (u:List Γ₁):
 TM2.step (zA δ fin q₀ d) (⟨some true,s,zd [] [] u⟩:vR Γ₀ Γ₁ Q)=
  some ⟨none,(q₀,none,false),zd [] [] u⟩:=by
 simp [TM2.step,zA,TM2.stepAux,zd,d19]
theorem qc2 (u:List Γ₁):
 ∀ (l:List Γ₀) (t:List (Q×Option Γ₀)) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1]
     (some (⟨some false,s,zd l t u⟩:vR Γ₀ Γ₁ Q))=
     some ⟨some true,(q₀,none,false),zd [] ((d21 δ s.1 l).reverse++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t s;exact qc4 δ fin q₀ d s t u
 | cons a l ih=>
   intro t s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step (zA δ fin q₀ d))
    (some (⟨some false,s,zd (a::l) t u⟩:vR Γ₀ Γ₁ Q))=
    some ⟨some false,((δ s.1 a).1,none,false),zd l ((s.1,some a)::t) u⟩:=
    qcL δ fin q₀ d s a l t u
   rw [e,ih]
   simp [d21]
theorem qc1 (hd:∀ _:Γ₁,d≠none):
 ∀ (t:List (Q×Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (zA δ fin q₀ d)))^[t.length+1]
     (some (⟨some true,s,zd [] t u⟩:vR Γ₀ Γ₁ Q))=
     some ⟨none,(q₀,none,false),zd [] [] (t.reverse.flatMap (kV δ fin)++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u s;exact qc3 δ fin q₀ d s u
 | cons e t ih=>
   intro u s
   rw [List.length_cons,Function.iterate_succ_apply]
   have e':flip bind (TM2.step (zA δ fin q₀ d))
    (some (⟨some true,s,zd [] (e::t) u⟩:vR Γ₀ Γ₁ Q))=
    some ⟨some true,(e.1,e.2,true),zd [] t (kV δ fin e++u)⟩:=
    qcK δ fin q₀ d hd s e t u
   rw [e',ih]
   simp [List.flatMap_append]
theorem qc0 [Fintype Γ₀] [Fintype Q] (hd:∀ _:Γ₁,d≠none) (l:List Γ₀):
 (flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
   (some (initList (trM δ fin q₀ d) l))=
   some (haltList (trM δ fin q₀ d) (zB δ fin q₀ l)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1+1 +
  (l.length+1)] (some c)) (d4 (trM δ fin q₀ d) l)).trans
  (Eq.trans ?_ (congrArg some (d5 (trM δ fin q₀ d) (zB δ fin q₀ l))).symm)
 show (flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
  (some (⟨some false,(q₀,none,false),Function.update (fun _=>[]) .inp l⟩:
    vR Γ₀ Γ₁ Q))=
  some (⟨none,(q₀,none,false),Function.update (fun _=>[]) .out (zB δ fin q₀ l)⟩:
   vR Γ₀ Γ₁ Q)
 have hA:(flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1]
  (some (⟨some false,(q₀,none,false),zd l [] []⟩:vR Γ₀ Γ₁ Q))=
  some ⟨some true,(q₀,none,false),zd [] (d21 δ q₀ l).reverse []⟩:=by
  have:=qc2 δ fin q₀ d [] l [] (q₀,none,false)
  rw [List.append_nil] at this
  exact this
 have hB:(flip bind (TM2.step (zA δ fin q₀ d)))^[l.length+1+1]
  (some (⟨some true,(q₀,none,false),zd [] (d21 δ q₀ l).reverse []⟩:
    vR Γ₀ Γ₁ Q))=
  some ⟨none,(q₀,none,false),zd [] [] (zB δ fin q₀ l)⟩:=by
  have:=qc1 δ fin q₀ d hd (d21 δ q₀ l).reverse [] (q₀,none,false)
  rw [List.length_reverse,d57,List.reverse_reverse,d85,
   List.append_nil] at this
  exact this
 rw [Function.iterate_add_apply,← d87,hA,hB,qcJ]
theorem yM {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (δ:Q→αΓ→Q×Option βΓ×Option βΓ)
 (fin:Q→Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=zB δ fin q₀ (ea a)):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
 classical
 let d:Option βΓ:=if h:Nonempty βΓ then some (Classical.choice h) else none
 have hd:∀ _:βΓ,d≠none:=by
  intro y
  have hn:Nonempty βΓ:=⟨y⟩
  simp [d,hn]
 exact ⟨{
  tm:=trM δ fin q₀ d
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 3
  outputsFun:=fun a=>
   { steps:=(ea a).length+1+1+((ea a).length+1)
     evals_in_steps:=by
      have hm:∀ (γ:Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l:=
       fun γ l=>by simp
      have:=qc0 δ fin q₀ d hd (ea a)
      exact (congrArg (fun l=>(flip bind (TM2.step (zA δ fin q₀ d)))^[(ea a).length +
       1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
       (hm αΓ (ea a))).trans
       (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
         ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
     steps_le_m:=by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
       Polynomial.eval_X]
      omega } }⟩
theorem qK {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea:α→List αΓ)
 (eb:β→List βΓ) (f:α→β) (δ:Q→αΓ→Q×Option βΓ) (fin:Q→Option βΓ) (q₀:Q)
 (h:∀ a,eb (f a)=ql δ fin q₀ (ea a)):
 Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=
 yM ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
  (fun a=>(h a).trans (d36 δ fin q₀ (ea a)))
end Lib.qz
end
section
namespace Lib.qz.Rev
open Turing PEqualNP.Library Lib.qz
def zm:Unit→TM2.Stmt (fun _:Bool=>Bool) Unit (Option Bool)
 | ()=>
   .pop false (fun _ o=>o)
     (.branch (fun s=>s.isSome)
       (.push true (fun s=>s.getD false) (.load (fun _=>none) (.goto fun _=>())))
       .halt)
def tm:FinTM2 where
 K:=Bool
 k₀:=false
 k₁:=true
 Γ _:=Bool
 Λ:=Unit
 main:=()
 σ:=Option Bool
 initialState:=none
 m:=zm
abbrev jB:Type:=TM2.Cfg (fun _:Bool=>Bool) Unit (Option Bool)
def st (l u:List Bool):Bool→List Bool:=fun k=>cond k u l
theorem d79 (l:List Bool):
 st l []=Function.update (fun _=>([]:List Bool)) false l:=by
 funext k;cases k <;> simp [st]
theorem w5 (u:List Bool):
 st [] u=Function.update (fun _=>([]:List Bool)) true u:=by
 funext k;cases k <;> simp [st]
theorem qcs (x:Bool) (l u:List Bool):
 TM2.step zm (⟨some (),none,st (x::l) u⟩:jB)=
  some ⟨some (),none,st l (x::u)⟩:=by
 simp only [TM2.step,zm,TM2.stepAux]
 simp only [st,Bool.cond_false,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
  Option.getD_some,Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
 funext k;cases k <;> simp [st]
theorem qcR (u:List Bool):
 TM2.step zm (⟨some (),none,st [] u⟩:jB)=some ⟨none,none,st [] u⟩:=by
 simp only [TM2.step,zm,TM2.stepAux]
 simp only [st,Bool.cond_false,List.head?_nil,List.tail_nil,Option.isSome_none,
  Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
 funext k;cases k <;> simp [st]
theorem loop:∀ (l u:List Bool),
 (flip bind (TM2.step zm))^[l.length+1] (some (⟨some (),none,st l u⟩:jB))=
   some ⟨none,none,st [] (l.reverse++u)⟩:=by
 intro l
 induction l with
 | nil=>intro u;exact qcR u
 | cons x l ih=>
   intro u
   rw [List.length_cons,Function.iterate_succ_apply]
   have e:flip bind (TM2.step zm) (some (⟨some (),none,st (x::l) u⟩:jB))=
    some ⟨some (),none,st l (x::u)⟩:=qcs x l u
   rw [e,ih]
   simp
theorem run (l:List Bool):
 (flip bind (TM2.step zm))^[l.length+1] (some (initList tm l))=
   some (haltList tm l.reverse):=by
 refine (congrArg (fun c=>(flip bind (TM2.step zm))^[l.length+1] (some c))
  (d4 tm l)).trans (Eq.trans ?_ (congrArg some (d5 tm l.reverse)).symm)
 show (flip bind (TM2.step zm))^[l.length+1]
  (some (⟨some (),none,Function.update (fun _=>[]) false l⟩:jB))=
  some (⟨none,none,Function.update (fun _=>[]) true l.reverse⟩:jB)
 rw [← d79,loop,← w5]
 simp
noncomputable def uR:
 TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x)
  (fun x:List Bool=>x.reverse) where
 tm:=tm
 inputAlphabet:=Equiv.refl _
 outputAlphabet:=Equiv.refl _
 time:=Polynomial.X+1
 outputsFun a:=
  { steps:=a.length+1
    evals_in_steps:=by
     have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
     exact (congrArg (fun l=>(flip bind (TM2.step zm))^[a.length+1]
      (some (initList tm l))) (hm a)).trans
      ((run a).trans (congrArg (fun l=>some (haltList tm l)) (hm a.reverse).symm))
    steps_le_m:=by simp }
end Lib.qz.Rev
end
section
namespace Lib.z9
def un (n:ℕ):List Bool:=List.replicate n true
def qc (a b:List Bool):List Bool:=un a.length++false::(a++b)
def unpairB (s:List Bool):List Bool×List Bool:=
 (((s.dropWhile id).tail).take (s.takeWhile id).length,
  ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem qj (a b:List Bool):unpairB (qc a b)=(a,b):=by
 have h1:(qc a b).takeWhile id=un a.length:=by
  simp [qc,un]
 have h2:(qc a b).dropWhile id=false::(a++b):=by
  simp [qc,un]
 simp [unpairB,h1,h2,un]
end Lib.z9
end
section
namespace Lib.z9
def qev (b:Bool):List Bool:=if b then [true] else []
@[simp] theorem qei:un 0=[]:=rfl
@[simp] theorem qN (n:ℕ):(un n).length=n:=List.length_replicate
theorem qeh (n:ℕ):un (n+1)=true::un n:=rfl
theorem qeu {a b:ℕ} (h:un a=un b):a=b:=by
 have:=congrArg List.length h
 simpa [un] using this
def hd (s:List Bool):List Bool:=s.takeWhile id
def dropN (s:List Bool):List Bool:=(s.dropWhile id).tail
def sel (f a b:List Bool):List Bool:=if f=[] then a else b
def qJ (u v:List Bool):List Bool:=un (u.length * v.length)
def qet (s:List Bool):List Bool:=s.flatMap fun b=>if b then [true,false] else [false]
def blank (s:List Bool):List Bool:=s.map fun _=>false
theorem qa9 (f p a b:List Bool):sel f (p++a) (p++b)=p++sel f a b:=by
 unfold sel;split_ifs <;> rfl
theorem qcp (s:List Bool):(hd s).length≤ s.length:=
 List.IsPrefix.length_le (List.takeWhile_prefix id)
theorem qbk (s:List Bool):(dropN s).length≤ s.length:=by
 have h1:=List.IsSuffix.length_le (List.dropWhile_suffix (p:=id) (l:=s))
 simp only [dropN,List.length_tail]
 omega
theorem qbY (g:List Bool→List Bool) (hg:∀ s,(g s).length≤ s.length) (k:ℕ):
 ∀ s,(g^[k] s).length≤ s.length:=by
 induction k with
 | zero=>intro s;exact le_rfl
 | succ k ih=>intro s;rw [Function.iterate_succ_apply];exact (ih _).trans (hg s)
theorem qcj (f a b:List Bool) (N:ℕ) (ha:a.length≤N) (hb:b.length≤N):
 (sel f a b).length≤N:=by
 unfold sel;split_ifs <;> assumption
theorem qbf (s:List Bool):
 2 * (unpairB s).1.length+(unpairB s).2.length≤ s.length:=by
 have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s))
 simp only [List.length_append] at h
 simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
 omega
theorem qbH (a b:List Bool):(qc a b).length=2 * a.length+b.length+1:=by
 simp [qc];omega
end Lib.z9
end
section
namespace Lib.z9
open PEqualNP.Library Lib.qz
private theorem d39 {α β αΓ βΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {f f':α→β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a):
 ComputableInPolyTime ea eb f':=by
 obtain rfl:f=f':=funext e
 exact h
private theorem qbi {A B C:Type} (φl:A→Option C) (φr:B→Option C) (x:List A)
 (w:List B):
 (x.map Sum.inl++w.map Sum.inr).filterMap (Sum.elim φl φr)=
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
private theorem qa0 {A C:Type} (g:A→C) (l:List A):
 l.filterMap (fun a=>some (g a))=l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [ih]
private theorem qdm {A C:Type} (l:List A):
 l.filterMap (fun _:A=>(none:Option C))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
theorem qcG:
 ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>qc p.1 p.2):=by
 have hA:ComputableInPolyTime encodePair encodePair
  (fun p:List Bool×List Bool=>(p.1,p.1++p.2)):=by
  refine d10 _ _ _
   (Sum.elim (fun b:Bool=>some (Sum.inl b)) (fun _:Bool=>none))
   (Sum.elim (fun b:Bool=>some (Sum.inr b)) (fun b:Bool=>some (Sum.inr b))) ?_
  rintro ⟨x,w⟩
  simp only [encodePair]
  rw [qbi,qbi,qa0,qa0,qa0,qdm]
  simp
 have hU:Lib.qe
  (fun a:List Bool=>a.map (fun _=>true)++[false]):=by
  refine qK _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
   (fun _=>some false) () ?_
  intro a
  induction a with
  | nil=>rfl
  | cons b l ih=>
    simp only [ql,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
    rw [← ih];rfl
 refine d39 (qa (qa hA (d38 hU)) d74) ?_
 rintro ⟨x,w⟩
 simp [qc,un]
theorem d35:
 ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>if p.1=[] then p.2 else []):=by
 obtain ⟨c⟩:=d11 []
 have hI:=y1.vT (fun _:List Bool=>([]:List Bool)) c 0 (by simp)
 refine d39 (qa d84 hI) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp [Function.iterate_succ_apply']
theorem d62:
 ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>if p.1=[] then [] else p.2):=by
 have hneg:Lib.qe
  (fun x:List Bool=>if x=[] then [true] else []):=
  qa (vn wD (d11 [true])) d35
 refine d39 (qa (d38 hneg) d35) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp
theorem qbX {α αΓ:Type} {ea:α→List αΓ} {f:α→Bool}
 (hf:ComputableInPolyTime ea Computability.encodeBool f):
 ComputableInPolyTime ea (fun x:List Bool=>x) (fun a=>if f a then [true] else []):=by
 have h:ComputableInPolyTime Computability.encodeBool (fun x:List Bool=>x)
  (fun b:Bool=>if b then [true] else []):=by
  refine d7 _ _ _ (fun b:Bool=>if b then some true else none) ?_
  intro b
  cases b <;> simp [Computability.encodeBool]
 exact qa hf h
private def yq (u:List Bool):List Bool:=u.flatMap (fun b=>[true,b])
private def vg (v:List Bool):List Bool:=v.flatMap (fun b=>[false,b])
private def twD:Bool→Bool→Bool×Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem qcZ (l:List Bool):
 ql twD (fun _=>none) false l=[]∧
  ql twD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [ql,twD,ih.1,ih.2]
private def e0D:Bool→Bool→Bool×Option Bool×Option Bool
 | false,true=>(false,none,none)
 | false,false=>(true,none,none)
 | true,b=>(true,some false,some b)
private theorem d83 (l:List Bool):
 zB e0D (fun _=>none) true l=vg l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [zB,e0D,vg,ih]
private theorem d73 (l:List Bool):
 zB e0D (fun _=>none) false l=vg (l.dropWhile id).tail:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [zB,e0D,ih,d83]
private def mkD:Bool×Bool→Bool→(Bool×Bool)×Option Bool
 | (d,false),t=>((d||!t,true),some (t||!d))
 | (d,true),b=>((d,false),some b)
private def mk (l:List Bool):List Bool:=ql mkD (fun _=>none) (false,false) l
private theorem d91 (q:Bool×Bool) (l:List Bool):
 (ql mkD (fun _=>none) q l).length=l.length:=by
 induction l generalizing q with
 | nil=>rfl
 | cons b l ih=>obtain ⟨d,ph⟩:=q;cases ph <;> simp [ql,mkD,ih]
private theorem qcS (v:List Bool):
 ql mkD (fun _=>none) (true,false) (vg v)=vg v:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [ql,mkD,vg] at ih ⊢;exact ih
private theorem d69 (u r:List Bool):
 ql mkD (fun _=>none) (false,false) (yq u++r)=
  yq u++ql mkD (fun _=>none) (false,false) r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [ql,mkD,yq] at ih ⊢;exact ih
private theorem qbG (u:List Bool):mk (yq u++vg [])=yq u++vg []:=by
 unfold mk;rw [d69];rfl
private theorem qdf (u:List Bool) (b:Bool) (v:List Bool):
 mk (yq u++vg (b::v))=yq (u++[b])++vg v:=by
 unfold mk
 rw [d69]
 have h:ql mkD (fun _=>none) (false,false) (vg (b::v))=
  true::b::vg v:=by
  have h':=qcS v
  simp [ql,mkD,vg] at h' ⊢
  exact h'
 rw [h]
 simp [yq]
private theorem qde (k:ℕ):∀ u t:List Bool,
 mk^[k] (yq u++vg t)=yq (u++t.take k)++vg (t.drop k):=by
 induction k with
 | zero=>intro u t;simp
 | succ k ih=>
   intro u t
   rw [Function.iterate_succ_apply]
   cases t with
   | nil=>rw [qbG,ih];simp
   | cons b t=>rw [qdf,ih];simp
private def dcD:Option Bool→Bool→Option Bool×Option (Bool ⊕ Bool)
 | none,t=>(some t,none)
 | some t,b=>(none,some (if t then Sum.inl b else Sum.inr b))
private theorem qb4 (v:List Bool):
 ql dcD (fun _=>none) none (vg v)=v.map Sum.inr:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [ql,dcD,vg] at ih ⊢;exact ih
private theorem qb5 (u r:List Bool):
 ql dcD (fun _=>none) none (yq u++r)=
  u.map Sum.inl++ql dcD (fun _=>none) none r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [ql,dcD,yq] at ih ⊢;exact ih
private def rawDec (l:List (Bool ⊕ Bool)):List Bool×List Bool:=
 (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem d68 (u v:List Bool):
 rawDec (u.map Sum.inl++v.map Sum.inr)=(u,v):=by
 have h1:∀ x:List Bool,(x.map (Sum.inl (β:=Bool))).filterMap Sum.getLeft?=x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a::·) ih
 have h2:∀ x:List Bool,(x.map (Sum.inr (α:=Bool))).filterMap Sum.getLeft?=[]:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h3:∀ x:List Bool,(x.map (Sum.inl (β:=Bool))).filterMap Sum.getRight?=[]:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h4:∀ x:List Bool,(x.map (Sum.inr (α:=Bool))).filterMap Sum.getRight?=x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a::·) ih
 simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
theorem d34:
 ComputableInPolyTime (fun x:List Bool=>x) encodePair unpairB:=by
 have hTw:Lib.qe
  (fun s:List Bool=>s.takeWhile id):=
  qK _ _ _ twD (fun _=>none) true (fun s=>(qcZ s).2.symm)
 have hE0:Lib.qe
  (fun s:List Bool=>vg (s.dropWhile id).tail):=
  yM _ _ _ e0D (fun _=>none) false (fun s=>(d73 s).symm)
 have hMk:Lib.qe mk:=
  qK _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
 obtain ⟨cMk⟩:=hMk
 have hIt:=y1.vT mk cMk 0 (fun y=>by simp [mk,d91])
 have hDc:ComputableInPolyTime (fun x:List Bool=>x) (fun l:List (Bool ⊕ Bool)=>l)
  (fun l:List Bool=>ql dcD (fun _=>none) none l):=
  qK _ _ _ dcD (fun _=>none) none (fun _=>rfl)
 have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool)=>l) encodePair rawDec:=by
  refine d10 _ _ _
   (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map Sum.inl)
   (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map Sum.inr) ?_
  intro l
  simp only [rawDec,encodePair,List.map_filterMap]
 refine d39 (qa (qa (qa (vn hE0 hTw) hIt) hDc) hRaw) ?_
 intro s
 have h:=qde (s.takeWhile id).length [] (s.dropWhile id).tail
 have e:yq []++vg (s.dropWhile id).tail=vg (s.dropWhile id).tail:=rfl
 rw [e] at h
 simp only [h,List.nil_append]
 rw [qb5,qb4,d68]
 rfl
theorem qco (g:List Bool→List Bool)
 (hg:Lib.qe g)
 (m:List Bool→ℕ) (a:ℕ)
 (hm:∀ y,m (g y)≤ m y) (hgl:∀ y,(g y).length≤y.length+m y)
 (ha:∀ y,m y≤a * y.length+a):
 Lib.qe
  (fun s:List Bool=>g^[(unpairB s).2.length] (unpairB s).1):=by
 obtain ⟨c⟩:=hg
 exact qa d34 (y1.vj g c m a hm hgl ha)
end Lib.z9
end
section
namespace Lib.z9
open PEqualNP.Library Lib.qz
private theorem jG {α β αΓ βΓ:Type} {ea:α→List αΓ} {eb:β→List βΓ}
 {f f':α→β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a):
 ComputableInPolyTime ea eb f':=by
 obtain rfl:f=f':=funext e
 exact h
private def hdD:Bool→Bool→Bool×Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem qdl (l:List Bool):
 ql hdD (fun _=>none) false l=[]∧
  ql hdD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [ql,hdD,ih.1,ih.2]
theorem vb:
 Lib.qe hd:=
 qK _ _ _ hdD (fun _=>none) true (fun s=>(qdl s).2.symm)
private def dnD:Bool→Bool→Bool×Option Bool
 | false,true=>(false,none)
 | false,false=>(true,none)
 | true,b=>(true,some b)
private theorem qcX (l:List Bool):ql dnD (fun _=>none) true l=l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [ql,dnD,ih]
private theorem qcF (l:List Bool):
 ql dnD (fun _=>none) false l=(l.dropWhile id).tail:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [ql,dnD,ih,qcX]
theorem va:
 Lib.qe dropN:=
 qK _ _ _ dnD (fun _=>none) false (fun s=>(qcF s).symm)
private def tlD:Bool→Bool→Bool×Option Bool
 | false,_=>(true,none)
 | true,b=>(true,some b)
private theorem qcQ (l:List Bool):ql tlD (fun _=>none) true l=l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [ql,tlD,ih]
private theorem qcr (l:List Bool):ql tlD (fun _=>none) false l=l.tail:=by
 cases l with
 | nil=>rfl
 | cons b l=>simp [ql,tlD,qcQ]
theorem vW:
 Lib.qe
  (fun s:List Bool=>s.tail):=
 qK _ _ _ tlD (fun _=>none) false (fun s=>(qcr s).symm)
private theorem qcH (l:List Bool):
 ql (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) () l=blank l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [ql,blank] at ih ⊢;exact ih
theorem kh:
 Lib.qe blank:=
 qK _ _ _ (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) ()
  (fun s=>(qcH s).symm)
theorem qh (l:List Bool):
 Lib.qe
  (fun _:List Bool=>l):=
 d11 l
theorem qf:
 Lib.qe
  (fun s:List Bool=>(unpairB s).1):=
 jG (qa d34 qdw) (fun _=>rfl)
theorem qb:
 Lib.qe
  (fun s:List Bool=>(unpairB s).2):=
 jG (qa d34 qdv) (fun _=>rfl)
theorem qi {u v:List Bool→List Bool}
 (hu:Lib.qe u)
 (hv:Lib.qe v):
 Lib.qe
  (fun s=>u s++v s):=
 jG (qa (vn hu hv) d74) (fun _=>rfl)
theorem qd {u v:List Bool→List Bool}
 (hu:Lib.qe u)
 (hv:Lib.qe v):
 Lib.qe
  (fun s=>qc (u s) (v s)):=
 jG (qa (vn hu hv) qcG) (fun _=>rfl)
theorem zh {f a b:List Bool→List Bool}
 (hf:Lib.qe f)
 (ha:Lib.qe a)
 (hb:Lib.qe b):
 Lib.qe
  (fun s=>sel (f s) (a s) (b s)):=by
 have h1:=qa (vn hf ha) d35
 have h2:=qa (vn hf hb) d62
 refine jG (qi h1 h2) ?_
 intro s
 by_cases h:f s=[] <;> simp [sel,h]
theorem qai {g cnt arg:List Bool→List Bool}
 (hg:Lib.qe g)
 (hgl:∀ s,(g s).length≤ s.length)
 (hcnt:Lib.qe cnt)
 (harg:Lib.qe arg):
 Lib.qe
  (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>g^[p.2.length] p.1):=
  y1.vT g c 0 (fun y=>by simpa using hgl y)
 exact jG (qa (vn harg hcnt) hI) (fun _=>rfl)
end Lib.z9
end
section
namespace L8.z3.za
open PEqualNP.CircuitLowerBounds
def a3 (gs:List Gate) (w:List Bool):List Bool:=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
theorem a91 (C:Circuit) (x:List Bool):C.wires x=a3 C.gates x:=rfl
theorem a18 (gs gs':List Gate) (w:List Bool):
 a3 (gs++gs') w=a3 gs' (a3 gs w):=by
 simp [a3,List.foldl_append]
theorem a39 (gs:List Gate):∀ w:List Bool,
 ∃ t:List Bool,a3 gs w=w++t∧t.length=gs.length:=by
 induction gs with
 | nil=>intro w;exact ⟨[],by simp [a3],rfl⟩
 | cons g gs ih=>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t,?_,by simp [hl]⟩
   have:a3 (g::gs) w
       =a3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
   rw [this,ht];simp
theorem a12 (gs:List Gate) (w:List Bool):
 (a3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=a39 gs w
 rw [ht];simp [hl]
theorem a28 (gs:List Gate) (w:List Bool) (i:ℕ) (h:i < w.length):
 (a3 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=a39 gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop:=
 g.inputs.length≤2
variable {n:ℕ}
theorem a8 {α:Type} (L:List α) (S d:α) (j:ℕ) (h:j≠L.length):
 (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 · exact List.getD_append _ _ _ _ hj
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
theorem a7 {α:Type} (L:List α) (S d:α):(L++[S]).getD L.length d=S:=by
 simp
def zP (g:Gate):List ℕ:=
 match g.op with
 | .not=>g.inputs.take 1
 | _=>g.inputs
theorem a84 (g:Gate):(zP g).length≤g.inputs.length:=by
 cases h:g.op <;> simp [zP,h,Nat.min_le_right]
def a9 (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n):=
 ((zP g).map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
theorem a60 (l:List ℕ) (F:ℕ→Finset (Fin n)) (i:Fin n):
 i∈(l.map F).foldr (· ∪ ·) ∅↔∃ a∈l,i∈F a:=by
 induction l with
 | nil=>simp
 | cons b l ih=>simp [ih]
theorem a27 (L:List (Finset (Fin n))) (g:Gate) (i:Fin n):
 i∈a9 L g↔∃ a∈zP g,i∈L.getD a ∅:=
 a60 _ _ _
def a37 (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)):=
 gs.foldl (fun L g=>L++[a9 L g]) L
def a6 (n:ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n=>{i}
def qar (x y:Fin n→Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop:=
 L.length=w.length∧w.length=w'.length∧
  ∀ j:ℕ,(∀ i∈L.getD j ∅,x i=y i)→w.getD j false=w'.getD j false
theorem a56 (g:Gate) (w w':List Bool)
 (h:∀ a∈zP g,w.getD a false=w'.getD a false):
 g.op.eval (g.inputs.map fun a=>w.getD a false)=
  g.op.eval (g.inputs.map fun a=>w'.getD a false):=by
 by_cases hn:g.op=.not
 · rw [hn]
   cases hi:g.inputs with
   | nil=>simp [GateOp.eval,hi]
   | cons a l=>
     have ha:=h a (by simp [zP,hn,hi])
     change (!w.getD a false)=!w'.getD a false
     rw [ha]
 · have he:g.inputs.map (fun a=>w.getD a false)=
    g.inputs.map (fun a=>w'.getD a false):=by
    apply List.map_congr_left
    intro a ha
    exact h a (by cases ho:g.op <;> simp_all [zP])
   rw [he]
theorem a40 (x y:Fin n→Bool) (gs:List Gate):
 ∀ (L:List (Finset (Fin n))) (w w':List Bool),qar x y L w w'→
   qar x y (a37 gs L) (a3 gs w) (a3 gs w'):=by
 induction gs with
 | nil=>intro L w w' h;exact h
 | cons g gs ih=>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[a9 L g])
    (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
    (w'++[g.op.eval (g.inputs.map fun i=>w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   · subst hjl
     rw [a7] at hj
     rw [h1,a7,h2,a7]
     apply a56
     intro a ha
     exact h3 a (fun i hi=>hj i ((a27 L g i).2 ⟨a,ha,hi⟩))
   · rw [a8 _ _ _ _ hjl] at hj
     rw [a8 _ _ _ _ (by omega),a8 _ _ _ _ (by omega)]
     exact h3 j hj
theorem a58 (x y:Fin n→Bool):
 qar x y (a6 n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [a6],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 · have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [a6,hjn])
   simp [hjn,hx]
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
def Cnt (t:ℕ) (L:List (Finset (Fin n))):Prop:=
 ∀ W:Finset ℕ,(W.biUnion fun j=>L.getD j ∅).card≤t+W.card
theorem a47:Cnt 0 (a6 n):=by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn:j < n
 · simp [a6,hjn]
 · rw [List.getD_eq_default _ _ (by simp [a6];omega)];simp
theorem a87 (t:ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length≤2)
 (h:Cnt t L):Cnt (t+1) (L++[a9 L g]):=by
 intro W
 by_cases hW:L.length∈W
 · have hsub:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)
    ⊆((W.erase L.length ∪ (zP g).toFinset).biUnion fun j=>L.getD j ∅):=by
    intro i hi
    rw [Finset.mem_biUnion] at hi ⊢
    obtain ⟨j,hjW,hij⟩:=hi
    by_cases hjl:j=L.length
    · subst hjl
      rw [a7] at hij
      obtain ⟨a,ha,hia⟩:=(a27 L g i).1 hij
      exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
    · rw [a8 _ _ _ _ hjl] at hij
      exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1:(W.erase L.length ∪ (zP g).toFinset).card≤(W.card - 1)+2:=by
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_erase_of_mem hW]
    exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (a84 g) hg)) _
   have hWpos:1≤W.card:=Finset.card_pos.2 ⟨_,hW⟩
   have:=h (W.erase L.length ∪ (zP g).toFinset)
   have:=Finset.card_le_card hsub
   omega
 · have heq:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)
    =(W.biUnion fun j=>L.getD j ∅):=by
    apply Finset.biUnion_congr rfl
    intro j hj
    exact a8 _ _ _ _ (fun e=>hW (e ▸ hj))
   rw [heq]
   have:=h W
   omega
theorem a53 (gs:List Gate):∀ (t:ℕ) (L:List (Finset (Fin n))),
 (∀ g∈gs,Ok g)→Cnt t L→Cnt (t+gs.length) (a37 gs L):=by
 induction gs with
 | nil=>intro t L _ h;exact h
 | cons g gs ih=>
   intro t L hok h
   have:=ih (t+1) (L++[a9 L g]) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
    (a87 t L g (hok g List.mem_cons_self) h)
   rw [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega]
   exact this
theorem a20 (C:Circuit) (n k w:Nat)
 (hk:k≤C.gates.length) (hw:w < n+k) (x:Fin n→Bool):
 (C.wires (List.ofFn x)).getD w false=
   (a3 (C.gates.take k) (List.ofFn x)).getD w false:=by
 change (a3 C.gates (List.ofFn x)).getD w false=_
 conv_lhs=>rw [← List.take_append_drop k C.gates]
 rw [a18]
 apply a28
 rw [a12]
 simpa [List.length_take,Nat.min_eq_left hk] using hw
theorem a70 (C:Circuit) (n k w:Nat)
 (hk:k≤C.gates.length) (hw:w < n+k)
 (hfan:∀ g∈C.gates,g.inputs.length≤2):
 ∃ S:Finset (Fin n),S.card≤k+1∧
   ∀ x y:Fin n→Bool,(∀ i∈S,x i=y i)→
     (C.wires (List.ofFn x)).getD w false=
       (C.wires (List.ofFn y)).getD w false:=by
 let S:=(a37 (C.gates.take k) (a6 n)).getD w ∅
 refine ⟨S,?_,?_⟩
 · have hc:=a53 (C.gates.take k) 0 (a6 n)
    (fun g hg=>hfan g (List.mem_of_mem_take hg)) a47 {w}
   simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,
    List.length_take,Nat.min_eq_left hk] using hc
 · intro x y heq
   rw [a20 C n k w hk hw x,a20 C n k w hk hw y]
   exact (a40 x y (C.gates.take k) _ _ _ (a58 x y)).2.2 w heq
theorem a41 (C:Circuit) (n k w:Nat)
 (hk:k≤C.gates.length) (hw:w < n+k)
 (hfan:∀ g∈C.gates,g.inputs.length≤2)
 (E:Finset (Fin n))
 (hsens:∀ i∈E,∃ x y:Fin n→Bool,
   (∀ j,j≠i→x j=y j)∧
     (C.wires (List.ofFn x)).getD w false≠
       (C.wires (List.ofFn y)).getD w false):
 E.card≤k+1:=by
 obtain ⟨S,hcard,hdep⟩:=a70 C n k w hk hw hfan
 apply le_trans (Finset.card_le_card (t:=S) ?_) hcard
 intro i hi
 by_contra hni
 obtain ⟨x,y,hxy,hne⟩:=hsens i hi
 apply hne (hdep x y ?_)
 intro j hj
 apply hxy j
 intro hji
 subst j
 exact hni hj
def RO (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool):Prop:=
 ∀ Q:Finset (Fin n)→((Fin n→Bool)→Bool)→Prop,
   (∀ i:Fin n,Q {i} (fun x=>x i))→
   (∀ A B a b,Disjoint A B→Q A a→Q B b→
     Q (A ∪ B) (fun x=>a x&&b x)∧Q (A ∪ B) (fun x=>a x||b x))→Q S f
theorem a34 (i:Fin n):RO {i} (fun x=>x i):=fun _ hl _=>hl i
theorem yK {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b):
 RO (A ∪ B) (fun x=>a x&&b x):=
 fun Q hl hj=>(hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1
theorem yU {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b):
 RO (A ∪ B) (fun x=>a x||b x):=
 fun Q hl hj=>(hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2
def Fam (L:List (Finset (Fin n))) (F:ℕ→(Fin n→Bool)→Bool) (W:Finset ℕ):Prop:=
 (∀ w∈W,RO (L.getD w ∅) (F w))∧
 (∀ w∈W,∀ v∈W,w≠v→Disjoint (L.getD w ∅) (L.getD v ∅))
def uG (t:ℕ) (L:List (Finset (Fin n))) (F:ℕ→(Fin n→Bool)→Bool):Prop:=
 ∀ W:Finset ℕ,(W.biUnion fun j=>L.getD j ∅).card=t+W.card→Fam L F W
theorem a71:uG 0 (a6 n) (fun j x=>(List.ofFn x).getD j false):=by
 intro W heq
 have hvalid:∀ j∈W,j < n:=by
  intro j hj
  by_contra hn
  have hz:(a6 n).getD j ∅=∅:=
   List.getD_eq_default _ _ (by simp [a6];omega)
  have he:=heq
  rw [← Finset.insert_erase hj,Finset.biUnion_insert,hz,Finset.empty_union] at he
  rw [Finset.insert_erase hj] at he
  have hc:=a47 (n:=n) (W.erase j)
  have hcard:=Finset.card_erase_add_one hj
  omega
 constructor
 · intro j hj
   have hv:=hvalid j hj
   have hs:(a6 n).getD j ∅={⟨j,hv⟩}:=by simp [a6,hv]
   have hf:(fun x:Fin n→Bool=>(List.ofFn x).getD j false)=(fun x=>x ⟨j,hv⟩):=by
    funext x;simp [hv]
   rw [hs]
   change RO {⟨j,hv⟩} (fun x:Fin n→Bool=>(List.ofFn x).getD j false)
   rw [hf]
   exact a34 _
 · intro j hj k hk hne
   have hjn:=hvalid j hj
   have hkn:=hvalid k hk
   simpa [a6,hjn,hkn,Fin.ext_iff] using hne
theorem a78 (L:List (Finset (Fin n))) (g:Gate) (W:Finset ℕ)
 (hW:L.length∈W):
 (W.biUnion fun j=>(L++[a9 L g]).getD j ∅)=
   ((W.erase L.length ∪ (zP g).toFinset).biUnion fun j=>L.getD j ∅):=by
 ext i
 constructor
 · intro hi
   rw [Finset.mem_biUnion] at hi ⊢
   obtain ⟨j,hjW,hij⟩:=hi
   by_cases hjl:j=L.length
   · subst hjl
     rw [a7] at hij
     obtain ⟨a,ha,hia⟩:=(a27 L g i).1 hij
     exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
   · rw [a8 _ _ _ _ hjl] at hij
     exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
 · intro hi
   obtain ⟨j,hj,hi⟩:=Finset.mem_biUnion.mp hi
   rcases Finset.mem_union.mp hj with hj | hj
   · refine Finset.mem_biUnion.mpr ⟨j,Finset.mem_of_mem_erase hj,?_⟩
     rw [a8 _ _ _ _ (Finset.ne_of_mem_erase hj)]
     exact hi
   · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
     rw [a7]
     exact (a27 L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩
theorem a62 (g:Gate)
 (ho:g.op=.and∨g.op=.or∨g.op=.not)
 (hlen:g.inputs.length≤2) (hcard:(zP g).toFinset.card=2):
 ∃ a b,g.inputs=[a,b]∧a≠b∧(g.op=.and∨g.op=.or):=by
 have hn:g.op≠.not:=by
  intro hn
  have hc:=List.toFinset_card_le (zP g)
  have hl:(zP g).length≤1:=by simp [zP,hn]
  omega
 have hop:g.op=.and∨g.op=.or:=by rcases ho with h | h | h <;> simp_all
 have hr:zP g=g.inputs:=by rcases hop with h | h <;> simp [zP,h]
 rw [hr] at hcard
 rcases hi:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
 · simp [hi] at hcard
 · simp [hi] at hcard
 · refine ⟨a,b,rfl,?_,hop⟩
   intro hab
   simp [hi,hab] at hcard
 · simp [hi] at hlen
def yg (L:List (Finset (Fin n))) (F:ℕ→(Fin n→Bool)→Bool) (g:Gate)
    (j:ℕ) (x:Fin n→Bool):Bool:=
 if j=L.length then g.op.eval (g.inputs.map fun a=>F a x) else F j x
theorem a80 (t:ℕ) (L:List (Finset (Fin n))) (F:ℕ→(Fin n→Bool)→Bool)
 (g:Gate) (ho:g.op=.and∨g.op=.or∨g.op=.not) (hlen:g.inputs.length≤2)
 (hc:Cnt t L) (ht:uG t L F):
 uG (t+1) (L++[a9 L g]) (yg L F g):=by
 intro W heq
 have hW:L.length∈W:=by
  by_contra hn
  have hU:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)=
   (W.biUnion fun j=>L.getD j ∅):=by
   apply Finset.biUnion_congr rfl
   intro j hj
   exact a8 _ _ _ _ (fun h=>hn (h ▸ hj))
  rw [hU] at heq
  have:=hc W
  omega
 let E:=W.erase L.length
 let B:=(zP g).toFinset
 let P:=E ∪ B
 have hEc:E.card+1=W.card:=Finset.card_erase_add_one hW
 have hBc:B.card≤2:=le_trans (List.toFinset_card_le _) (le_trans (a84 g) hlen)
 have hPc:P.card≤E.card+B.card:=Finset.card_union_le _ _
 have hU:(W.biUnion fun j=>(L++[a9 L g]).getD j ∅)=
  (P.biUnion fun j=>L.getD j ∅):=a78 L g W hW
 rw [hU] at heq
 have hcP:=hc P
 have hB2:B.card=2:=by omega
 have hPexact:P.card=E.card+B.card:=by omega
 have hTexact:(P.biUnion fun j=>L.getD j ∅).card=t+P.card:=by omega
 have hEB:Disjoint E B:=Finset.card_union_eq_card_add_card.mp hPexact
 obtain ⟨a,b,hin,hab,hop⟩:=a62 g ho hlen hB2
 have hreads:zP g=[a,b]:=by rcases hop with h | h <;> simp [zP,h,hin]
 have haB:a∈B:=by simp [B,hreads]
 have hbB:b∈B:=by simp [B,hreads]
 have haP:a∈P:=Finset.mem_union_right _ haB
 have hbP:b∈P:=Finset.mem_union_right _ hbB
 have hF:=ht P hTexact
 have hEP:E⊆P:=Finset.subset_union_left
 have hneA:∀ w∈E,w≠a:=by
  intro w hw hwa;subst w
  exact Finset.disjoint_left.mp hEB hw haB
 have hneB:∀ w∈E,w≠b:=by
  intro w hw hwb;subst w
  exact Finset.disjoint_left.mp hEB hw hbB
 have hS:a9 L g=L.getD a ∅ ∪ L.getD b ∅:=by simp [a9,hreads]
 have hnew:RO (a9 L g) (yg L F g L.length):=by
  rw [hS]
  have hd:=hF.2 a haP b hbP hab
  rcases hop with hop | hop
  · have hf:yg L F g L.length=(fun x=>F a x&&F b x):=by
     funext x;simp [yg,hin,hop,GateOp.eval]
    rw [hf];exact yK hd (hF.1 a haP) (hF.1 b hbP)
  · have hf:yg L F g L.length=(fun x=>F a x||F b x):=by
     funext x;simp [yg,hin,hop,GateOp.eval]
    rw [hf];exact yU hd (hF.1 a haP) (hF.1 b hbP)
 have hother:∀ w∈E,(L++[a9 L g]).getD w ∅=L.getD w ∅:=
  fun w hw=>a8 _ _ _ _ (Finset.ne_of_mem_erase hw)
 have hnewdis:∀ w∈E,Disjoint (a9 L g) (L.getD w ∅):=by
  intro w hw
  rw [hS,Finset.disjoint_union_left]
  exact ⟨hF.2 a haP w (hEP hw) (hneA w hw).symm,
   hF.2 b hbP w (hEP hw) (hneB w hw).symm⟩
 constructor
 · intro w hw
   by_cases hwk:w=L.length
   · subst w
     rw [a7]
     exact hnew
   · have hwE:w∈E:=Finset.mem_erase.mpr ⟨hwk,hw⟩
     rw [hother w hwE]
     have hf:yg L F g w=F w:=by funext x;simp [yg,hwk]
     rw [hf]
     exact hF.1 w (hEP hwE)
 · intro w hw v hv hne
   by_cases hwk:w=L.length
   · subst w
     have hvE:v∈E:=Finset.mem_erase.mpr ⟨hne.symm,hv⟩
     rw [a7,hother v hvE]
     exact hnewdis v hvE
   · have hwE:w∈E:=Finset.mem_erase.mpr ⟨hwk,hw⟩
     rw [hother w hwE]
     by_cases hvk:v=L.length
     · subst v
       rw [a7]
       exact (hnewdis w hwE).symm
     · have hvE:v∈E:=Finset.mem_erase.mpr ⟨hvk,hv⟩
       rw [hother v hvE]
       exact hF.2 w (hEP hwE) v (hEP hvE) hne
theorem a59 (gs:List Gate):∀ (t:ℕ) (L:List (Finset (Fin n)))
 (v:(Fin n→Bool)→List Bool),(∀ x,(v x).length=L.length)→
 (∀ g∈gs,(g.op=.and∨g.op=.or∨g.op=.not)∧g.inputs.length≤2)→
 Cnt t L→uG t L (fun j x=>(v x).getD j false)→
 uG (t+gs.length) (a37 gs L) (fun j x=>(a3 gs (v x)).getD j false):=by
 induction gs with
 | nil=>intro t L v hv _ hc ht;exact ht
 | cons g gs ih=>
   intro t L v hv hg hc ht
   let v':=fun x:Fin n→Bool=>v x++[g.op.eval (g.inputs.map fun a=>(v x).getD a false)]
   have hv':∀ x,(v' x).length=(L++[a9 L g]).length:=by
    intro x;simp [v',hv x]
   have hf:(fun j x=>(v' x).getD j false)=
    yg L (fun j x=>(v x).getD j false) g:=by
    funext j x
    by_cases hj:j=L.length
    · subst j
      simp only [yg,ite_true]
      dsimp only [v']
      rw [← hv x,a7]
    · simp only [yg,hj,ite_false]
      exact a8 _ _ _ _ (by rw [hv x];exact hj)
   have hgg:=hg g List.mem_cons_self
   have ht':uG (t+1) (L++[a9 L g]) (fun j x=>(v' x).getD j false):=by
    rw [hf]
    exact a80 t L _ g hgg.1 hgg.2 hc ht
   have hres:=ih (t+1) (L++[a9 L g]) v' hv'
    (fun g' h=>hg g' (List.mem_cons_of_mem g h)) (a87 t L g hgg.2 hc) ht'
   simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
    a37,a3,List.foldl_cons,v'] using hres
theorem a65 (C:Circuit) (n k w:Nat)
 (hk:k≤C.gates.length) (hw:w < n+k)
 (hfan:∀ g∈C.gates,(g.op=.and∨g.op=.or∨g.op=.not)∧g.inputs.length≤2)
 (E:Finset (Fin n)) (hE:E.card=k+1)
 (hsens:∀ i∈E,∃ x y:Fin n→Bool,
   (∀ j,j≠i→x j=y j)∧
   (C.wires (List.ofFn x)).getD w false≠(C.wires (List.ofFn y)).getD w false):
 RO E (fun x=>(C.wires (List.ofFn x)).getD w false):=by
 let gs:=C.gates.take k
 let L:=a37 gs (a6 n)
 let S:=L.getD w ∅
 have hlen:gs.length=k:=by simp [gs,List.length_take,Nat.min_eq_left hk]
 have hfan':∀ g∈gs,(g.op=.and∨g.op=.or∨g.op=.not)∧g.inputs.length≤2:=
  fun g hg=>hfan g (List.mem_of_mem_take hg)
 have hc:=a53 gs 0 (a6 n) (fun g hg=>(hfan' g hg).2) a47
 have hSc:S.card≤k+1:=by
  have:=hc {w}
  simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
 have hdep:∀ x y:Fin n→Bool,(∀ i∈S,x i=y i)→
  (C.wires (List.ofFn x)).getD w false=(C.wires (List.ofFn y)).getD w false:=by
  intro x y hxy
  rw [a20 C n k w hk hw x,a20 C n k w hk hw y]
  exact (a40 x y gs _ _ _ (a58 x y)).2.2 w hxy
 have hsub:E⊆S:=by
  intro i hi
  by_contra hni
  obtain ⟨x,y,hxy,hne⟩:=hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  exact hxy j (fun h=>hni (h ▸ hj))
 have hES:E=S:=Finset.eq_of_subset_of_card_le hsub (by omega)
 have hT:=a59 gs 0 (a6 n) (fun x=>List.ofFn x)
  (fun x=>by simp [a6]) hfan' a47 a71
 have heq:(({w}:Finset ℕ).biUnion fun j=>L.getD j ∅).card=(0+gs.length)+({w}:Finset ℕ).card:=by
  have hS:S.card=k+1:=by rw [←hES];exact hE
  simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
 have hR:=(hT {w} heq).1 w (Finset.mem_singleton_self w)
 change RO S _ at hR
 rw [←hES] at hR
 have hf:(fun x:Fin n→Bool=>(a3 gs (List.ofFn x)).getD w false)=
  (fun x=>(C.wires (List.ofFn x)).getD w false):=by
  funext x;exact (a20 C n k w hk hw x).symm
 change RO E (fun x:Fin n→Bool=>(a3 gs (List.ofFn x)).getD w false) at hR
 rw [hf] at hR
 exact hR
end L8.z3.za
namespace L8.z3.zq
open L8.z3.za
variable {n:ℕ} {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
theorem qb1 (h:RO S f):S.Nonempty:=by
 apply h (fun S _=>S.Nonempty)
 · intro i;exact Finset.singleton_nonempty i
 · intro A B a b hd ha hb
   exact ⟨ha.mono Finset.subset_union_left,ha.mono Finset.subset_union_left⟩
theorem a89 (h:RO S f) (x:Fin n→Bool) (hx:∀ i∈S,x i=false):f x=false:=by
 apply h (fun S f=>∀ x,(∀ i∈S,x i=false)→f x=false) ?_ ?_ x hx
 · intro i x hx;exact hx i (Finset.mem_singleton_self _)
 · intro A B a b hd ha hb
   constructor <;> intro x hx
   · dsimp only
     rw [ha x (fun i hi=>hx i (Finset.mem_union_left _ hi)),
      hb x (fun i hi=>hx i (Finset.mem_union_right _ hi))];rfl
   · dsimp only
     rw [ha x (fun i hi=>hx i (Finset.mem_union_left _ hi)),
      hb x (fun i hi=>hx i (Finset.mem_union_right _ hi))];rfl
theorem a82 (h:RO S f) (x y:Fin n→Bool) (hx:∀ i∈S,x i=y i):f x=f y:=by
 apply h (fun S f=>∀ x y,(∀ i∈S,x i=y i)→f x=f y) ?_ ?_ x y hx
 · intro i x y hx;exact hx i (Finset.mem_singleton_self _)
 · intro A B a b hd ha hb
   constructor <;> intro x y hx <;> dsimp only <;>
    rw [ha x y (fun i hi=>hx i (Finset.mem_union_left _ hi)),
     hb x y (fun i hi=>hx i (Finset.mem_union_right _ hi))]
theorem a63 (h:RO S f) (x y:Fin n→Bool)
 (hxy:∀ i,x i=true→y i=true) (hf:f x=true):f y=true:=by
 apply h (fun _ f=>∀ x y,(∀ i,x i=true→y i=true)→f x=true→f y=true) ?_ ?_ x y hxy hf
 · intro i x y hxy hf;exact hxy i hf
 · intro A B a b hd ha hb
   constructor
   · intro x y hxy hf
     simp only [Bool.and_eq_true] at hf ⊢
     exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
   · intro x y hxy hf
     simp only [Bool.or_eq_true] at hf ⊢
     exact hf.elim (fun h=>Or.inl (ha x y hxy h)) (fun h=>Or.inr (hb x y hxy h))
theorem qec (h:RO S f):
 (∃ i:Fin n,S={i}∧f=(fun x=>x i))∨
 ∃ A B a b,Disjoint A B∧S=A∪B∧RO A a∧RO B b∧
   (f=(fun x=>a x&&b x)∨f=(fun x=>a x||b x)):=by
 let Q:=fun S f=>RO S f∧
  ((∃ i:Fin n,S={i}∧f=(fun x=>x i))∨
  ∃ A B a b,Disjoint A B∧S=A∪B∧RO A a∧RO B b∧
    (f=(fun x=>a x&&b x)∨f=(fun x=>a x||b x)))
 have hQ:Q S f:=h Q (fun i=>⟨a34 i,Or.inl ⟨i,rfl,rfl⟩⟩) (by
  intro A B a b hd ha hb
  constructor
  · exact ⟨yK hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inl rfl⟩⟩
  · exact ⟨yU hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inr rfl⟩⟩)
 exact hQ.2
def qu (i j:Fin n):Fin n→Bool:=fun k=>decide (k=i∨k=j)
def qP (i:Fin n):Fin n→Bool:=fun k=>decide (k=i)
theorem a54 (i j:Fin n):qu i j=qu j i:=by funext k;simp [qu,or_comm]
theorem a66 (h:RO S f) (i j:Fin n) (hi:i∉S) (hj:j∉S):f (qu i j)=false:=by
 apply a89 h
 intro k hk
 simp only [qu,decide_eq_false_iff_not,not_or]
 exact ⟨fun hki=>hi (hki ▸ hk),fun hkj=>hj (hkj ▸ hk)⟩
theorem a26 (h:RO S f) (i j:Fin n) (hj:j∉S):
 f (qu i j)=f (qP i):=by
 apply a82 h
 intro k hk
 have hkj:k≠j:=fun hkj=>hj (hkj ▸ hk)
 simp [qu,qP,hkj]
theorem a45 (h:RO S f) (i j:Fin n) (hi:i∉S):
 f (qu i j)=f (qP j):=by rw [a54];exact a26 h j i hi
end L8.z3.zq
namespace L8.zL
open L8.z3.za L8.z3.zq
variable {n:ℕ}
def vl (f:(Fin n→Bool)→Bool):Prop:=∀ i,f (qP i)=false
def a17 (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool):Prop:=
 ∀ i∈S,∃ j∈S,f (qu i j)=true
def a76 (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool):Prop:=
 ∀ x,f x=true↔∃ i∈S,∃ j∈S,f (qu i j)=true∧x i=true∧x j=true
theorem a88 {i:Fin n} {x:Fin n→Bool} (hi:x i=true):
 ∀ j,qP i j=true→x j=true:=by
 intro j hj
 have:j=i:=by simpa [qP] using hj
 simpa [this] using hi
theorem a75 {i j:Fin n} {x:Fin n→Bool} (hi:x i=true) (hj:x j=true):
 ∀ t,qu i j t=true→x t=true:=by
 intro t ht
 have:t=i∨t=j:=by simpa [qu] using ht
 rcases this with rfl | rfl <;> assumption
theorem a42 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (x:Fin n→Bool) (hx:f x=true):∃ i∈S,x i=true:=by
 by_contra hn
 have hz:∀ i∈S,x i=false:=by
  intro i hi
  have h:x i≠true:=fun ht=>hn ⟨i,hi,ht⟩
  exact Bool.eq_false_iff.mpr h
 have h:=a89 hf x hz
 rw [hx] at h
 contradiction
theorem qaY {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hs:∀ i∈S,f (qP i)=true) (x:Fin n→Bool):
 f x=true↔∃ i∈S,x i=true:=by
 constructor
 · exact a42 hf x
 · rintro ⟨i,hi,hx⟩
   exact a63 hf _ _ (a88 hx) (hs i hi)
theorem a21 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hc:a17 (A ∪ B) (fun x=>a x&&b x)):
 (∀ i∈A,a (qP i)=true)∧(∀ j∈B,b (qP j)=true):=by
 constructor
 · intro i hi
   obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_left _ hi)
   have hia:i∉B:=Finset.disjoint_left.mp hd hi
   have hja:j∉A:=by
    intro hjA
    have hjB:j∉B:=Finset.disjoint_left.mp hd hjA
    have hz:=a66 hb i j hia hjB
    simp only [hz,Bool.and_false] at hp
    contradiction
   have hpA:a (qu i j)=true:=(by simpa only [Bool.and_eq_true] using hp:a (qu i j)=true∧b (qu i j)=true).1
   rwa [a26 ha i j hja] at hpA
 · intro i hi
   obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_right _ hi)
   have hia:i∉A:=Finset.disjoint_right.mp hd hi
   have hja:j∉B:=by
    intro hjB
    have hjA:j∉A:=Finset.disjoint_right.mp hd hjB
    have hz:=a66 ha i j hia hjA
    simp only [hz,Bool.false_and] at hp
    contradiction
   have hpB:b (qu i j)=true:=(by simpa only [Bool.and_eq_true] using hp:a (qu i j)=true∧b (qu i j)=true).2
   rwa [a26 hb i j hja] at hpB
theorem a51 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hs:vl (fun x=>a x||b x))
 (hc:a17 (A ∪ B) (fun x=>a x||b x)):a17 A a:=by
 intro i hi
 obtain ⟨j,hj,hp⟩:=hc i (Finset.mem_union_left _ hi)
 have hia:i∉B:=Finset.disjoint_left.mp hd hi
 have hsA:∀ t,a (qP t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
 have hsB:∀ t,b (qP t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
 have hpA:a (qu i j)=true:=by
  have hp':a (qu i j)=true∨b (qu i j)=true:=by simpa only [Bool.or_eq_true] using hp
  rcases hp' with h | h
  · exact h
  · rw [a45 hb i j hia,hsB j] at h
    contradiction
 have hjA:j∈A:=by
  by_contra hjA
  rw [a26 ha i j hjA,hsA i] at hpA
  contradiction
 exact ⟨j,hjA,hpA⟩
theorem a43 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hs:vl f) (hc:a17 S f):a76 S f:=by
 let Q:=fun (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool)=>RO S f∧(vl f→a17 S f→a76 S f)
 have hQ:Q S f:=hf Q (by
  intro i
  refine ⟨a34 i,?_⟩
  intro hs hc
  have h:=hs i
  simp [qP] at h) (by
  intro A B a b hd ha hb
  constructor
  · refine ⟨yK hd ha.1 hb.1,?_⟩
    intro hs hc x
    constructor
    · intro hx
      obtain ⟨hi,hj⟩:=a21 hd ha.1 hb.1 hc
      obtain ⟨i,hiA,hxi⟩:=a42 ha.1 x (by simpa only [Bool.and_eq_true] using hx:a x=true∧b x=true).1
      obtain ⟨j,hjB,hxj⟩:=a42 hb.1 x (by simpa only [Bool.and_eq_true] using hx:a x=true∧b x=true).2
      refine ⟨i,Finset.mem_union_left _ hiA,j,Finset.mem_union_right _ hjB,?_,hxi,hxj⟩
      have hjA:j∉A:=Finset.disjoint_right.mp hd hjB
      have hiB:i∉B:=Finset.disjoint_left.mp hd hiA
      dsimp only
      rw [a26 ha.1 i j hjA,a45 hb.1 i j hiB,hi i hiA,hj j hjB]
      rfl
    · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
      exact a63 (yK hd ha.1 hb.1) _ _ (a75 hxi hxj) hp
  · refine ⟨yU hd ha.1 hb.1,?_⟩
    intro hs hc x
    have hsA:vl a:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
    have hsB:vl b:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
    have hcA:=a51 hd ha.1 hb.1 hs hc
    have hcB:a17 B b:=by
     have hs':vl (fun x=>b x||a x):=by simpa only [Bool.or_comm] using hs
     have hc':a17 (B ∪ A) (fun x=>b x||a x):=by
      simpa only [Finset.union_comm,Bool.or_comm] using hc
     exact a51 hd.symm hb.1 ha.1 hs' hc'
    constructor
    · intro hx
      have hx':a x=true∨b x=true:=by simpa only [Bool.or_eq_true] using hx
      rcases hx' with h | h
      · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩:=(ha.2 hsA hcA x).mp h
        refine ⟨i,Finset.mem_union_left _ hi,j,Finset.mem_union_left _ hj,?_,hxi,hxj⟩
        simp only [hp,Bool.true_or]
      · obtain ⟨i,hi,j,hj,hp,hxi,hxj⟩:=(hb.2 hsB hcB x).mp h
        refine ⟨i,Finset.mem_union_right _ hi,j,Finset.mem_union_right _ hj,?_,hxi,hxj⟩
        simp only [hp,Bool.or_true]
    · rintro ⟨i,hi,j,hj,hp,hxi,hxj⟩
      exact a63 (yU hd ha.1 hb.1) _ _ (a75 hxi hxj) hp)
 exact hQ.2 hs hc
end L8.zL
namespace L8.zL
open L8.z3.za L8.z3.zq
variable {n:ℕ}
theorem a4 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hs:vl (fun x=>a x||b x))
 {i j:Fin n} (hi:i∈A) (hp:(a (qu i j)||b (qu i j))=true):
 j∈A∧a (qu i j)=true:=by
 have hiB:i∉B:=Finset.disjoint_left.mp hd hi
 have hsA:∀ t,a (qP t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).1
 have hsB:∀ t,b (qP t)=false:=fun t=>(Bool.or_eq_false_iff.mp (hs t)).2
 have hpA:a (qu i j)=true:=by
  rcases Bool.or_eq_true_iff.mp hp with h | h
  · exact h
  · rw [a45 hb i j hiB,hsB j] at h
    contradiction
 refine ⟨?_,hpA⟩
 by_contra hjA
 rw [a26 ha i j hjA,hsA i] at hpA
 contradiction
theorem a29 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hc:a17 (A ∪ B) (fun x=>a x&&b x))
 {i j:Fin n} (hi:i∈A) (hj:j∈B):
 (a (qu i j)&&b (qu i j))=true:=by
 obtain ⟨hsA,hsB⟩:=a21 hd ha hb hc
 have hiB:i∉B:=Finset.disjoint_left.mp hd hi
 have hjA:j∉A:=Finset.disjoint_right.mp hd hj
 rw [a26 ha i j hjA,a45 hb i j hiB,hsA i hi,hsB j hj]
 rfl
theorem a0 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (hb:RO B b)
 {i j:Fin n} (hi:i∈A) (hp:(a (qu i j)&&b (qu i j))=true):
 j∈B:=by
 by_contra hjB
 have hiB:i∉B:=Finset.disjoint_left.mp hd hi
 rw [a66 hb i j hiB hjB,Bool.and_false] at hp
 contradiction
def qZ (qo:Fin n→Fin n) (qs:Fin n→Bool)
    (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool):Prop:=
 vl f∧
 (∀ i∈S,qo i∈S)∧
 (∀ i∈S,f (qu i (qo i))=true)∧
 (∀ i j,qs i≠qs j→j≠qo i→f (qu i j)=false)
theorem a23 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool} (h:qZ qo qs S f):
 a17 S f:=fun i hi=>⟨qo i,h.2.1 i hi,h.2.2.1 i hi⟩
theorem a24 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hm:qZ qo qs (A ∪ B) (fun x=>a x||b x)):
 qZ qo qs A a:=by
 refine ⟨?_,?_,?_,?_⟩
 · intro i
   exact (Bool.or_eq_false_iff.mp (hm.1 i)).1
 · intro i hi
   exact (a4 hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).1
 · intro i hi
   exact (a4 hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).2
 · intro i j hc hj
   exact (Bool.or_eq_false_iff.mp (hm.2.2.2 i j hc hj)).1
theorem a35 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hm:qZ qo qs (A ∪ B) (fun x=>a x||b x)):
 qZ qo qs B b:=by
 have h:qZ qo qs (B ∪ A) (fun x=>b x||a x):=by
  simpa only [Finset.union_comm,Bool.or_comm] using hm
 exact a24 hd.symm hb ha h
theorem a13 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 (hmi:Function.Involutive qo) (hcol:∀ i,qs (qo i)≠qs i)
 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:RO A a) (hb:RO B b)
 (hm:qZ qo qs (A ∪ B) (fun x=>a x&&b x)):
 ∀ i∈A,∀ j∈A,qs i=qs j→i=j:=by
 intro i hi j hj hij
 have hmj:qo j∈B:=a0 hd hb hj
  (hm.2.2.1 j (Finset.mem_union_left _ hj))
 have ht:(a (qu i (qo j))&&b (qu i (qo j)))=true:=
  a29 hd ha hb (a23 hm) hi hmj
 have hcm:qs i≠qs (qo j):=by
  intro h
  exact hcol j (h.symm.trans hij)
 have hmate:qo j=qo i:=by
  by_contra hne
  have hf:=hm.2.2.2 i (qo j) hcm hne
  dsimp only at hf
  rw [hf] at ht
  contradiction
 exact (hmi.injective hmate).symm
def a31 (qs:Fin n→Bool) (S:Finset (Fin n))
    (f:(Fin n→Bool)→Bool):Prop:=
 ∀ i∈S,∀ j∈S,∀ l∈S,qs i=qs j→qs i=qs l→
   f (qu i j)=true→f (qu i l)=true→j=l
theorem a22 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 (hmi:Function.Involutive qo) (hcol:∀ i,qs (qo i)≠qs i)
 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hm:qZ qo qs S f):a31 qs S f:=by
 let Q:=fun (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool)=>
  RO S f∧(qZ qo qs S f→a31 qs S f)
 have hQ:Q S f:=hf Q (by
  intro i
  refine ⟨a34 i,?_⟩
  intro hm
  have hs:=hm.1 i
  simp [qP] at hs) (by
  intro A B a b hd ha hb
  constructor
  · refine ⟨yK hd ha.1 hb.1,?_⟩
    intro hm i hi j hj l hl hij hil hpj hpl
    have hinjA:=a13 hmi hcol hd ha.1 hb.1 hm
    have hm':qZ qo qs (B ∪ A) (fun x=>b x&&a x):=by
     simpa only [Finset.union_comm,Bool.and_comm] using hm
    have hinjB:=a13 hmi hcol hd.symm hb.1 ha.1 hm'
    rcases Finset.mem_union.mp hi with hi | hi
    · have hjB:=a0 hd hb.1 hi hpj
      have hlB:=a0 hd hb.1 hi hpl
      exact hinjB j hjB l hlB (hij.symm.trans hil)
    · have hpj':(b (qu i j)&&a (qu i j))=true:=by simpa only [Bool.and_comm] using hpj
      have hpl':(b (qu i l)&&a (qu i l))=true:=by simpa only [Bool.and_comm] using hpl
      have hjA:=a0 hd.symm ha.1 hi hpj'
      have hlA:=a0 hd.symm ha.1 hi hpl'
      exact hinjA j hjA l hlA (hij.symm.trans hil)
  · refine ⟨yU hd ha.1 hb.1,?_⟩
    intro hm i hi j hj l hl hij hil hpj hpl
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨hjA,hpjA⟩:=a4 hd ha.1 hb.1 hm.1 hi hpj
      obtain ⟨hlA,hplA⟩:=a4 hd ha.1 hb.1 hm.1 hi hpl
      exact ha.2 (a24 hd ha.1 hb.1 hm) i hi j hjA l hlA hij hil hpjA hplA
    · have hm':qZ qo qs (B ∪ A) (fun x=>b x||a x):=by
       simpa only [Finset.union_comm,Bool.or_comm] using hm
      have hpj':(b (qu i j)||a (qu i j))=true:=by simpa only [Bool.or_comm] using hpj
      have hpl':(b (qu i l)||a (qu i l))=true:=by simpa only [Bool.or_comm] using hpl
      obtain ⟨hjB,hpjB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hpj'
      obtain ⟨hlB,hplB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hpl'
      exact hb.2 (a35 hd ha.1 hb.1 hm) i hi j hjB l hlB hij hil hpjB hplB)
 exact hQ.2 hm
end L8.zL
namespace L8.zL
open L8.z3.za L8.z3.zq
variable {n:ℕ}
theorem a11 {qo:Fin n→Fin n} {qs:Fin n→Bool}
 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hm:qZ qo qs S f):
 ∀ i∈S,∀ j∈S,f (qu i j)=true→f (qu (qo i) (qo j))=true:=by
 let Q:=fun (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool)=>
  RO S f∧(qZ qo qs S f→
   ∀ i∈S,∀ j∈S,f (qu i j)=true→f (qu (qo i) (qo j))=true)
 have hQ:Q S f:=hf Q (by
  intro i
  refine ⟨a34 i,?_⟩
  intro hm
  have hs:=hm.1 i
  simp [qP] at hs) (by
  intro A B a b hd ha hb
  constructor
  · refine ⟨yK hd ha.1 hb.1,?_⟩
    intro hm i hi j hj hp
    have hm':qZ qo qs (B ∪ A) (fun x=>b x&&a x):=by
     simpa only [Finset.union_comm,Bool.and_comm] using hm
    rcases Finset.mem_union.mp hi with hi | hi
    · have hjB:=a0 hd hb.1 hi hp
      have hmiB:=a0 hd hb.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))
      have hmjA:=a0 hd.symm ha.1 hjB
       (hm'.2.2.1 j (Finset.mem_union_left _ hjB))
      have h:=a29 hd.symm hb.1 ha.1 (a23 hm') hmiB hmjA
      simpa only [Bool.and_comm] using h
    · have hp':(b (qu i j)&&a (qu i j))=true:=by
       simpa only [Bool.and_comm] using hp
      have hjA:=a0 hd.symm ha.1 hi hp'
      have hmiA:=a0 hd.symm ha.1 hi
       (hm'.2.2.1 i (Finset.mem_union_left _ hi))
      have hmjB:=a0 hd hb.1 hjA (hm.2.2.1 j (Finset.mem_union_left _ hjA))
      exact a29 hd ha.1 hb.1 (a23 hm) hmiA hmjB
  · refine ⟨yU hd ha.1 hb.1,?_⟩
    intro hm i hi j hj hp
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨hjA,hpA⟩:=a4 hd ha.1 hb.1 hm.1 hi hp
      have h:=ha.2 (a24 hd ha.1 hb.1 hm) i hi j hjA hpA
      dsimp only
      rw [h,Bool.true_or]
    · have hm':qZ qo qs (B ∪ A) (fun x=>b x||a x):=by
       simpa only [Finset.union_comm,Bool.or_comm] using hm
      have hp':(b (qu i j)||a (qu i j))=true:=by
       simpa only [Bool.or_comm] using hp
      obtain ⟨hjB,hpB⟩:=a4 hd.symm hb.1 ha.1 hm'.1 hi hp'
      have h:=hb.2 (a35 hd ha.1 hb.1 hm) i hi j hjB hpB
      dsimp only
      rw [h,Bool.or_true])
 exact hQ.2 hm
theorem qbb {qo:Fin n→Fin n} {qs:Fin n→Bool}
 (hmi:Function.Involutive qo)
 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hm:qZ qo qs S f)
 {i j:Fin n} (hi:i∈S) (hj:j∈S):
 f (qu i j)=f (qu (qo i) (qo j)):=by
 apply Bool.eq_iff_iff.mpr
 constructor
 · exact a11 hf hm i hi j hj
 · intro h
   have h':=a11 hf hm (qo i) (hm.2.1 i hi) (qo j) (hm.2.1 j hj) h
   simpa only [hmi i,hmi j] using h'
end L8.zL
namespace L8.zL
variable {α:Type*}
theorem a44 (R:α→α→Prop)
 (hs:∀ {a b},R a b→R b a) (hi:∀ a,¬ R a a)
 (hu:∀ a b c,R a b→R a c→b=c):
 ∃ p:Equiv.Perm α,Function.Involutive p∧
   (∀ a b,R a b↔p a=b∧b≠a)∧
   (∀ q:Equiv.Perm α,(∀ a b,R a b↔q a=b∧b≠a)→q=p):=by
 classical
 let p:α→α:=fun a=>if h:∃ b,R a b then Classical.choose h else a
 have hpR:∀ a b,R a b→p a=b:=by
  intro a b h
  have he:∃ b,R a b:=⟨b,h⟩
  dsimp only [p]
  rw [dite_eq_left he]
  exact hu a _ b (Classical.choose_spec he) h
 have hp:∀ a,p a=a∨R a (p a):=by
  intro a
  by_cases he:∃ b,R a b
  · right
    dsimp only [p]
    rw [dite_eq_left he]
    exact Classical.choose_spec he
  · left
    simp [p,he]
 have hpi:Function.Involutive p:=by
  intro a
  rcases hp a with h | h
  · rw [h,h]
  · exact hpR _ _ (hs h)
 let e:Equiv.Perm α:=hpi.toPerm p
 have heval:∀ a,e a=p a:=fun _=>rfl
 have hiff:∀ a b,R a b↔e a=b∧b≠a:=by
  intro a b
  constructor
  · intro h
    refine ⟨hpR a b h,?_⟩
    intro hab
    exact hi a (hab ▸ h)
  · rintro ⟨hab,hn⟩
    rcases hp a with h | h
    · exact False.elim (hn (hab.symm.trans h))
    · exact hab ▸ h
 refine ⟨e,hpi,hiff,?_⟩
 intro q hq
 apply Equiv.ext
 intro a
 by_cases h:p a=a
 · by_cases hqa:q a=a
   · exact hqa.trans h.symm
   · have hr:=(hq a (q a)).2 ⟨rfl,hqa⟩
     have he:=hpR a (q a) hr
     exact False.elim (hqa (he.symm.trans h))
 · have hr:=(hiff a (e a)).2 ⟨rfl,h⟩
   exact (hq a (e a)).1 hr |>.1
theorem a19 {R:α→α→Prop} {p:Equiv.Perm α}
 (hp:∀ a b,R a b↔p a=b∧b≠a)
 (σ:α→α) (hσ:Function.Involutive σ)
 (hR:∀ a b,R a b→R (σ a) (σ b)):
 ∀ a,p (σ a)=σ (p a):=by
 intro a
 by_cases he:p a=a
 · by_cases he':p (σ a)=σ a
   · rw [he,he']
   · have h:=hR (σ a) (p (σ a)) ((hp _ _).2 ⟨rfl,he'⟩)
     rw [hσ a] at h
     obtain ⟨hpa,hne⟩:=(hp _ _).1 h
     exact False.elim (hne (hpa.symm.trans he))
 · have h:=hR a (p a) ((hp _ _).2 ⟨rfl,he⟩)
   exact ((hp _ _).1 h).1
end L8.zL
namespace L8.zL
open L8.z3.za L8.z3.zq
variable {n:ℕ}
theorem a48:∀ a b c d:Bool,a≠c→b≠d→c=d→a=b:=by decide
theorem yf {qo:Fin n→Fin n} {qs:Fin n→Bool}
 (hmi:Function.Involutive qo) (hcol:∀ i,qs (qo i)≠qs i)
 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (hf:RO S f) (hm:qZ qo qs S f):
 ∃ p:Equiv.Perm (Fin n),Function.Involutive p∧
   (∀ i,qs (p i)=qs i)∧
   (∀ i,p (qo i)=qo (p i))∧
   (∀ i,i∉S→p i=i)∧
   (∀ x,f x=true↔∃ i∈S,
     (x i=true∧x (qo i)=true)∨
     (p i≠i∧x i=true∧x (p i)=true))∧
   (∀ i j,(i∈S∧j∈S∧qs i=qs j∧f (qu i j)=true)↔
     p i=j∧j≠i):=by
 classical
 let R:Fin n→Fin n→Prop:=fun i j=>
  i∈S∧j∈S∧qs i=qs j∧f (qu i j)=true
 have hsym:∀ {i j},R i j→R j i:=by
  intro i j h
  refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
  rw [a54]
  exact h.2.2.2
 have hirr:∀ i,¬ R i i:=by
  intro i h
  have hp:qu i i=qP i:=by funext j;simp [qu,qP]
  have htrue:=h.2.2.2
  rw [hp,hm.1 i] at htrue
  contradiction
 have hunique:∀ i j l,R i j→R i l→j=l:=by
  intro i j l h1 h2
  exact a22 hmi hcol hf hm i h1.1 j h1.2.1 l h2.2.1
   h1.2.2.1 h2.2.2.1 h1.2.2.2 h2.2.2.2
 obtain ⟨p,hpi,hp,hpu⟩:=a44 R hsym hirr hunique
 have hcolor:∀ i,qs (p i)=qs i:=by
  intro i
  by_cases he:p i=i
  · rw [he]
  · exact ((hp i (p i)).2 ⟨rfl,he⟩).2.2.1.symm
 have hmirror:∀ i j,R i j→R (qo i) (qo j):=by
  intro i j h
  refine ⟨hm.2.1 i h.1,hm.2.1 j h.2.1,?_,?_⟩
  · exact a48 _ _ _ _ (hcol i) (hcol j) h.2.2.1
  · exact a11 hf hm i h.1 j h.2.1 h.2.2.2
 have hcomm:=a19 hp qo hmi hmirror
 have hout:∀ i,i∉S→p i=i:=by
  intro i hi
  by_contra he
  exact hi ((hp i (p i)).2 ⟨rfl,he⟩).1
 refine ⟨p,hpi,hcolor,hcomm,hout,?_,hp⟩
 intro x
 constructor
 · intro hfx
   obtain ⟨i,hi,j,hj,hpair,hxi,hxj⟩:=
    (a43 hf hm.1 (a23 hm) x).1 hfx
   by_cases hc:qs i=qs j
   · have hrij:R i j:=⟨hi,hj,hc,hpair⟩
     obtain ⟨hpij,hji⟩:=(hp i j).1 hrij
     refine ⟨i,hi,Or.inr ⟨?_,hxi,?_⟩⟩
     · simpa only [hpij] using hji
     · simpa only [hpij] using hxj
   · have hjm:j=qo i:=by
      by_contra hne
      have hz:=hm.2.2.2 i j hc hne
      rw [hz] at hpair
      contradiction
     exact ⟨i,hi,Or.inl ⟨hxi,hjm ▸ hxj⟩⟩
 · rintro ⟨i,hi,h | h⟩
   · exact a63 hf _ _ (a75 h.1 h.2) (hm.2.2.1 i hi)
   · have hr:=(hp i (p i)).2 ⟨rfl,h.1⟩
     exact a63 hf _ _ (a75 h.2.1 h.2.2) hr.2.2.2
end L8.zL
namespace L8.zL.vZ
open L8.z3.za L8.z3.zq
variable {k:ℕ}
abbrev row (i:Fin k):Fin (k+k):=Fin.castAdd k i
abbrev col (i:Fin k):Fin (k+k):=Fin.natAdd k i
def qo:Fin (k+k)→Fin (k+k):=Fin.append col row
def qs:Fin (k+k)→Bool:=Fin.append (fun _=>false) (fun _=>true)
@[simp] theorem vq (i:Fin k):qo (row i)=col i:=Fin.append_left _ _ i
@[simp] theorem yt (i:Fin k):qo (col i)=row i:=Fin.append_right _ _ i
@[simp] theorem yI (i:Fin k):qs (row i)=false:=Fin.append_left _ _ i
@[simp] theorem yH (i:Fin k):qs (col i)=true:=Fin.append_right _ _ i
theorem a61:Function.Involutive (qo (k:=k)):=by
 intro i
 induction i using Fin.addCases with
 | left j=>exact (congrArg qo (vq j)).trans (yt j)
 | right j=>exact (congrArg qo (yt j)).trans (vq j)
theorem a86 (i:Fin (k+k)):qs (qo i)≠qs i:=by
 induction i using Fin.addCases with
 | left j=>change qs (qo (row j))≠qs (row j);rw [vq,yH,yI];decide
 | right j=>change qs (qo (col j))≠qs (col j);rw [yt,yI,yH];decide
theorem a10:Function.Injective (row (k:=k)):=Fin.castAdd_injective k k
theorem a14:Function.Injective (col (k:=k)):=Fin.natAdd_injective k k
@[simp] theorem qci (i j:Fin k):row i=row j↔i=j:=a10.eq_iff
@[simp] theorem qb3 (i j:Fin k):col i=col j↔i=j:=a14.eq_iff
theorem a92 (p:Equiv.Perm (Fin (k+k)))
 (hc:∀ i,qs (p i)=qs i) (i:Fin k):∃ j,p (row i)=row j:=by
 have hcolor:=hc (row i)
 generalize he:p (row i)=v at *
 induction v using Fin.addCases with
 | left j=>exact ⟨j,rfl⟩
 | right j=>
   rw [yI] at hcolor
   change qs (col j)=false at hcolor
   rw [yH] at hcolor
   contradiction
def a5 (p:Equiv.Perm (Fin k)) (x y:Fin k→Bool):Bool:=
 decide (∃ i:Fin k,
  (x i=true∧y i=true)∨
  (p i≠i∧((x i=true∧x (p i)=true)∨
    (y i=true∧y (p i)=true))))
theorem a32 (f:(Fin (k+k)→Bool)→Bool)
 (hf:RO Finset.univ f) (hm:L8.zL.qZ qo qs Finset.univ f):
 ∃ p:Equiv.Perm (Fin k),Function.Involutive p∧
   ∀ x y,f (Fin.append x y)=a5 p x y:=by
 classical
 obtain ⟨p,hpi,hcol,hcomm,hout,hfn,hedge⟩:=
  L8.zL.yf a61 a86 hf hm
 choose q hq using a92 p hcol
 have hqi:Function.Involutive q:=by
  intro i
  apply a10
  rw [← hq (q i),← hq i,hpi (row i)]
 let e:Equiv.Perm (Fin k):=hqi.toPerm q
 have hp_row:∀ i,p (row i)=row (e i):=hq
 have hp_col:∀ i,p (col i)=col (e i):=by
  intro i
  rw [← vq i,hcomm,hp_row,vq]
 have hnrow:∀ i,p (row i)≠row i↔e i≠i:=by
  intro i
  rw [hp_row]
  exact not_congr (a10.eq_iff)
 have hncol:∀ i,p (col i)≠col i↔e i≠i:=by
  intro i
  rw [hp_col]
  exact not_congr (a14.eq_iff)
 refine ⟨e,hqi,?_⟩
 intro x y
 apply Bool.eq_iff_iff.mpr
 rw [hfn]
 simp only [a5,decide_eq_true_eq]
 constructor
 · rintro ⟨v,hv,h⟩
   induction v using Fin.addCases with
   | left i=>
     rcases h with h | ⟨hn,h1,h2⟩
     · refine ⟨i,Or.inl ?_⟩
       simpa only [vq,Fin.append_left,Fin.append_right] using h
     · refine ⟨i,Or.inr ⟨(hnrow i).mp hn,Or.inl ⟨?_,?_⟩⟩⟩
       · simpa only [Fin.append_left] using h1
       · simpa only [hp_row,Fin.append_left] using h2
   | right i=>
     rcases h with h | ⟨hn,h1,h2⟩
     · refine ⟨i,Or.inl ?_⟩
       simpa only [yt,Fin.append_left,Fin.append_right] using h.symm
     · refine ⟨i,Or.inr ⟨(hncol i).mp hn,Or.inr ⟨?_,?_⟩⟩⟩
       · simpa only [Fin.append_right] using h1
       · simpa only [hp_col,Fin.append_right] using h2
 · rintro ⟨i,h | ⟨hn,h | h⟩⟩
   · refine ⟨row i,Finset.mem_univ _,Or.inl ?_⟩
     simpa only [vq,Fin.append_left,Fin.append_right] using h
   · refine ⟨row i,Finset.mem_univ _,Or.inr ⟨(hnrow i).mpr hn,?_,?_⟩⟩
     · simpa only [Fin.append_left] using h.1
     · simpa only [hp_row,Fin.append_left] using h.2
   · refine ⟨col i,Finset.mem_univ _,Or.inr ⟨(hncol i).mpr hn,?_,?_⟩⟩
     · simpa only [Fin.append_right] using h.1
     · simpa only [hp_col,Fin.append_right] using h.2
theorem a16 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
 (i j:Fin k):
 a5 p (qu i j) (fun _=>false)=true↔p i=j∧j≠i:=by
 simp only [a5,decide_eq_true_eq,Bool.false_eq_true,and_false,or_false,false_or,
  qu]
 constructor
 · rintro ⟨a,hn,ha,hpa⟩
   have ha':a=i∨a=j:=by simpa using ha
   have hpa':p a=i∨p a=j:=by simpa using hpa
   rcases ha' with hai | haj
   · subst a
     rcases hpa' with h | h
     · exact False.elim (hn h)
     · exact ⟨h,fun hji=>hn (h.trans hji)⟩
   · subst a
     rcases hpa' with h | h
     · have hij:p i=j:=by rw [← h,hp j]
       exact ⟨hij,fun hji=>hn (h.trans hji.symm)⟩
     · exact False.elim (hn h)
 · rintro ⟨hij,hji⟩
   refine ⟨i,?_,?_,?_⟩
   · exact fun h=>hji (hij.symm.trans h)
   · simp
   · simp [hij]
theorem a38 (p q:Equiv.Perm (Fin k))
 (hp:Function.Involutive p) (hq:Function.Involutive q)
 (he:∀ x y,a5 p x y=a5 q x y):p=q:=by
 have hr:∀ i j,(p i=j∧j≠i)↔(q i=j∧j≠i):=by
  intro i j
  rw [← a16 p hp i j,← a16 q hq i j,he]
 apply Equiv.ext
 intro i
 by_cases hn:p i=i
 · by_cases hnq:q i=i
   · exact hn.trans hnq.symm
   · have h:=(hr i (q i)).2 ⟨rfl,hnq⟩
     exact False.elim (hnq (h.1.symm.trans hn))
 · exact ((hr i (p i)).1 ⟨rfl,hn⟩).1.symm
theorem a15 (f:(Fin (k+k)→Bool)→Bool)
 (hf:RO Finset.univ f) (hm:L8.zL.qZ qo qs Finset.univ f):
 ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
  ∀ x y,f (Fin.append x y)=a5 p x y:=by
 obtain ⟨p,hp,he⟩:=a32 f hf hm
 refine ⟨p,⟨hp,he⟩,?_⟩
 intro q hq
 apply a38 q p hq.1 hp
 intro x y
 exact (hq.2 x y).symm.trans (he x y)
end L8.zL.vZ
namespace L8.zL.vZ
open L8.z3.za L8.z3.zq
variable {k:ℕ}
theorem a55 (hk:2≤k) (i:Fin k):∃ j:Fin k,j≠i:=by
 let z:Fin k:=⟨0,by omega⟩
 let o:Fin k:=⟨1,by omega⟩
 by_cases hi:i=z
 · refine ⟨o,?_⟩
   intro h
   have hv:=congrArg Fin.val (h.trans hi)
   change 1=0 at hv
   omega
 · exact ⟨z,Ne.symm hi⟩
theorem a36 (hk:2≤k) (f:(Fin (k+k)→Bool)→Bool)
 (hmono:∀ x y,(∀ i,x i=true→y i=true)→f x=true→f y=true)
 (hrep:∀ i j:Fin k,f (qu (row i) (col j))=decide (i=j)):
 L8.zL.qZ qo qs Finset.univ f:=by
 have hs:L8.zL.vl f:=by
  intro v
  apply Bool.eq_false_iff.mpr
  intro htrue
  induction v using Fin.addCases with
  | left i=>
    obtain ⟨j,hji⟩:=a55 hk i
    have hx:=hmono (qP (row i)) (qu (row i) (col j)) (by
     intro t ht
     have he:t=row i:=by simpa [qP] using ht
     simp [qu,he]) htrue
    rw [hrep,decide_eq_false (Ne.symm hji)] at hx
    contradiction
  | right i=>
    obtain ⟨j,hji⟩:=a55 hk i
    have hx:=hmono (qP (col i)) (qu (row j) (col i)) (by
     intro t ht
     have he:t=col i:=by simpa [qP] using ht
     simp [qu,he]) htrue
    rw [hrep,decide_eq_false hji] at hx
    contradiction
 refine ⟨hs,by simp,?_,?_⟩
 · intro v hv
   induction v using Fin.addCases with
   | left i=>
     change f (qu (row i) (qo (row i)))=true
     rw [vq,hrep]
     simp
   | right i=>
     change f (qu (col i) (qo (col i)))=true
     rw [yt,a54,hrep]
     simp
 · intro v w hc hne
   induction v using Fin.addCases with
   | left i=>
     induction w using Fin.addCases with
     | left j=>exact False.elim (hc ((yI i).trans (yI j).symm))
     | right j=>
       change col j≠qo (row i) at hne
       rw [vq] at hne
       have hij:i≠j:=fun h=>hne (congrArg col h.symm)
       rw [hrep,decide_eq_false hij]
   | right i=>
     induction w using Fin.addCases with
     | left j=>
       change row j≠qo (col i) at hne
       rw [yt] at hne
       have hji:j≠i:=fun h=>hne (congrArg row h)
       rw [a54,hrep,decide_eq_false hji]
     | right j=>exact False.elim (hc ((yH i).trans (yH j).symm))
theorem a25 (hk:2≤k) (f:(Fin (k+k)→Bool)→Bool)
 (hf:RO Finset.univ f)
 (hrep:∀ i j:Fin k,f (qu (row i) (col j))=decide (i=j)):
 ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
  ∀ x y,f (Fin.append x y)=a5 p x y:=by
 exact a15 f hf (a36 hk f (a63 hf) hrep)
end L8.zL.vZ
namespace L8.zL.kx
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open L8.z3.za L8.z3.zq
open L8.zL.vZ
theorem a67 (g:Gate) (hg:g.op=GateOp.and∨g.op=GateOp.or)
 (w w':List Bool)
 (h:∀ i∈g.inputs,w.getD i false=true→w'.getD i false=true)
 (he:g.op.eval (g.inputs.map fun i=>w.getD i false)=true):
 g.op.eval (g.inputs.map fun i=>w'.getD i false)=true:=by
 rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
 · intro i hi
   exact h i hi (he i hi)
 · obtain ⟨i,hi,hv⟩:=he
   exact ⟨i,hi,h i hi hv⟩
theorem a64 (gs:List Gate)
 (hm:∀ g∈gs,g.op=GateOp.and∨g.op=GateOp.or):
 ∀ w w':List Bool,w.length=w'.length→
 (∀ i,w.getD i false=true→w'.getD i false=true)→
 ∀ i,(a3 gs w).getD i false=true→(a3 gs w').getD i false=true:=by
 induction gs with
 | nil=>intro w w' hl h;exact h
 | cons g gs ih=>
   intro w w' hl h i hi
   apply ih (fun g' hg'=>hm g' (List.mem_cons_of_mem _ hg'))
    (w++[g.op.eval (g.inputs.map fun a=>w.getD a false)])
    (w'++[g.op.eval (g.inputs.map fun a=>w'.getD a false)]) (by simp [hl]) ?_ i hi
   intro j hj
   by_cases he:j=w.length
   · rw [he,a7] at hj
     rw [he,hl,a7]
     exact a67 g (hm g List.mem_cons_self) w w' (fun a _=>h a) hj
   · rw [a8 _ _ _ _ he] at hj
     rw [a8 _ _ _ _ (by omega)]
     exact h j hj
theorem a74 {n:ℕ} (C:Circuit) (hm:Monotone2 C)
 (x y:Fin n→Bool) (h:∀ i,x i=true→y i=true)
 (he:C.eval (List.ofFn x)=true):C.eval (List.ofFn y)=true:=by
 apply a64 C.gates (fun g hg=>(hm g hg).1)
  (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output he
 intro j hj
 by_cases hjn:j < n
 · have hx:x ⟨j,hjn⟩=true:=by simpa [hjn] using hj
   simpa [hjn] using h ⟨j,hjn⟩ hx
 · rw [List.getD_eq_default _ _ (by simp;omega)] at hj
   contradiction
theorem a30 {k:ℕ} (i j:Fin k):
 List.ofFn (qu (row i) (col j))=oneEach i j:=by
 have h:qu (row i) (col j)=
  Fin.append (qP i) (qP j):=by
  funext v
  induction v using Fin.addCases with
  | left t=>
    have hne:row t≠col j:=by
     intro h
     have hval:=congrArg (fun z:Fin (k+k)=>z.val) h
     change t.val=k+j.val at hval
     omega
    simp only [qu,qP,Fin.append_left]
    simp only [hne,or_false]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using a10.eq_iff)
  | right t=>
    have hne:col t≠row i:=by
     intro h
     have hval:=congrArg (fun z:Fin (k+k)=>z.val) h
     change k+t.val=i.val at hval
     omega
    simp only [qu,qP,Fin.append_right]
    simp only [hne,false_or]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using a14.eq_iff)
 rw [h,List.ofFn_fin_append]
 rfl
theorem a49 {k:ℕ} (hk:2≤k) (C:Circuit)
 (hm:Monotone2 C) (hsize:C.size+1≤2*k)
 (hrep:Represents (fun i j:Fin k=>decide (i=j)) C):
 RO Finset.univ (fun x:Fin (k+k)→Bool=>C.eval (List.ofFn x)):=by
 let f:(Fin (k+k)→Bool)→Bool:=fun x=>C.eval (List.ofFn x)
 have hrep':∀ i j:Fin k,f (qu (row i) (col j))=decide (i=j):=by
  intro i j
  exact (congrArg C.eval (a30 i j)).trans (hrep i j)
 have hm':=a36 hk f (a74 C hm) hrep'
 have hsens:∀ i∈(Finset.univ:Finset (Fin (k+k))),
  ∃ x y:Fin (k+k)→Bool,(∀ j,j≠i→x j=y j)∧
    (C.wires (List.ofFn x)).getD C.output false≠
      (C.wires (List.ofFn y)).getD C.output false:=by
  intro i hi
  refine ⟨qu i (qo i),qP (qo i),?_,?_⟩
  · intro j hji
    simp [qu,qP,hji]
  · change f (qu i (qo i))≠f (qP (qo i))
    rw [hm'.2.2.1 i hi,hm'.1 (qo i)]
    decide
 have hvalid:C.output < (k+k)+C.gates.length:=by
  let z:Fin k:=⟨0,by omega⟩
  have ht:=hrep' z z
  have ht':(C.wires (List.ofFn (qu (row z) (col z)))).getD C.output false=true:=by
   change f (qu (row z) (col z))=true
   simpa only [decide_true] using ht
  by_contra hn
  have hl:(C.wires (List.ofFn (qu (row z) (col z)))).length=(k+k)+C.gates.length:=by
   rw [a91,a12]
   simp
  rw [List.getD_eq_default _ _ (by omega)] at ht'
  contradiction
 have hb:=a41 C (k+k) C.gates.length C.output le_rfl hvalid
  (fun g hg=>(hm g hg).2) Finset.univ hsens
 have hcard:(Finset.univ:Finset (Fin (k+k))).card=C.gates.length+1:=by
  simp only [Finset.card_univ,Fintype.card_fin] at hb ⊢
  change C.gates.length+1≤2*k at hsize
  omega
 exact a65 C (k+k) C.gates.length C.output le_rfl hvalid
  (fun g hg=>⟨by have h:=(hm g hg).1;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h;tauto,(hm g hg).2⟩)
  Finset.univ hcard hsens
theorem v9 {k:ℕ} (hk:2≤k) (C:Circuit)
 (hm:Monotone2 C) (hsize:C.size+1≤2*k)
 (hrep:Represents (fun i j:Fin k=>decide (i=j)) C):
 ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
  ∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
 have h:=a25 hk
  (fun x:Fin (k+k)→Bool=>C.eval (List.ofFn x))
  (a49 hk C hm hsize hrep) (by
    intro i j
    rw [a30]
    exact hrep i j)
 simpa only [List.ofFn_fin_append] using h
end L8.zL.kx
namespace L8.zL
 theorem u6:∀ (k:Nat),2≤k→∀ f:(Fin k→Bool)→(Fin k→Bool)→Bool,
  (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1≤2*k∧
    PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C∧
    ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y))→
  ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
   ∀ x y,f x y=decide (∃ i:Fin k,
       (x i=true∧y i=true)∨
       (p i≠i∧((x i=true∧x (p i)=true)∨
         (y i=true∧y (p i)=true)))):=by
  intro k hk f h
  obtain ⟨C,hm,hs,hr,he⟩:=h
  obtain ⟨p,hp,hu⟩:=kx.v9 hk C hm hs hr
  refine ⟨p,⟨hp.1,?_⟩,?_⟩
  · intro x y
    exact (he x y).trans (hp.2 x y)
  · intro q hq
    apply hu q
    refine ⟨hq.1,?_⟩
    intro x y
    exact (he x y).symm.trans (hq.2 x y)
end L8.zL
namespace L8.qbh.jb
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open L8.z3.za
variable {n:ℕ}
def qbg (g:Gate):Prop:=
 (g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2
def a50 (S:Finset (Fin n)) (f:(Fin n→Bool)→Bool):Prop:=
 ∀ m:ℕ,n≤ m→∃ (gs:List Gate) (out:ℕ),
   (∀ g∈gs,qbg g)∧gs.length+1=S.card∧out < m+gs.length∧
   ∀ w:List Bool,w.length=m→
     (a3 gs w).getD out false=f (fun i:Fin n=>w.getD i.val false)
theorem a69 (i:Fin n):a50 {i} (fun x=>x i):=by
 intro m hm
 refine ⟨[],i.val,?_,by simp,?_,?_⟩
 · simp
 · have:=i.isLt
   simp only [List.length_nil,Nat.add_zero]
   omega
 · intro w hw
   rfl
theorem a52 {A B:Finset (Fin n)} {a b:(Fin n→Bool)→Bool}
 (hd:Disjoint A B) (ha:a50 A a) (hb:a50 B b)
 (op:GateOp) (hop:op=GateOp.and∨op=GateOp.or):
 a50 (A ∪ B) (fun x=>op.eval [a x,b x]):=by
 intro m hm
 obtain ⟨ga,oa,oka,lena,ra,eva⟩:=ha m hm
 obtain ⟨gb,ob,okb,lenb,rb,evb⟩:=hb (m+ga.length) (by omega)
 let M:=m+ga.length+gb.length
 refine ⟨ga++gb++[⟨op,[oa,ob]⟩],M,?_,?_,?_,?_⟩
 · intro g hg
   simp only [List.mem_append,List.mem_singleton] at hg
   rcases hg with (hg | hg) | hg
   · exact oka g hg
   · exact okb g hg
   · subst g
     exact ⟨hop,by simp⟩
 · rw [Finset.card_union_of_disjoint hd]
   simp only [List.length_append,List.length_singleton]
   omega
 · simp only [List.length_append,List.length_singleton]
   dsimp [M]
   omega
 · intro w hw
   rw [a18,a18]
   let wa:=a3 ga w
   let wb:=a3 gb wa
   have hwa:wa.length=m+ga.length:=by
    dsimp [wa]
    rw [a12,hw]
   have hwb:wb.length=M:=by
    dsimp [wb]
    rw [a12,hwa]
   have eqa:wb.getD oa false=a (fun i:Fin n=>w.getD i.val false):=by
    dsimp [wb]
    rw [a28 gb wa oa (by omega)]
    exact eva w hw
   have eqb:wb.getD ob false=b (fun i:Fin n=>w.getD i.val false):=by
    dsimp [wb]
    rw [evb wa hwa]
    congr 1
    funext i
    exact a28 ga w i.val (by have:=i.isLt;omega)
   change (a3 [⟨op,[oa,ob]⟩] wb).getD M false=_
   change (wb++[op.eval [wb.getD oa false,wb.getD ob false]]).getD M false=_
   rw [← hwb,a7,eqa,eqb]
theorem a77 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (h:RO S f):a50 S f:=by
 apply h a50 a69
 intro A B a b hd ha hb
 constructor
 · simpa only [GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,id_eq]
    using a52 hd ha hb GateOp.and (Or.inl rfl)
 · simpa only [GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
    using a52 hd ha hb GateOp.or (Or.inr rfl)
theorem a83 {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (h:RO S f):
 ∃ C:Circuit,Monotone2 C∧C.size+1=S.card∧C.output < n+C.size∧
   ∀ x:Fin n→Bool,C.eval (List.ofFn x)=f x:=by
 obtain ⟨gs,out,hok,hlen,hout,heval⟩:=a77 h n (le_refl n)
 refine ⟨⟨gs,out⟩,?_,hlen,hout,?_⟩
 · intro g hg
   obtain ⟨ho,hl⟩:=hok g hg
   exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ho,hl⟩
 · intro x
   change (a3 gs (List.ofFn x)).getD out false=f x
   rw [heval (List.ofFn x) (by simp)]
   congr 1
   funext i
   simp
theorem uS {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool}
 (h:RO S f):
 ∃ C:Circuit,Monotone2 C∧C.size+1=S.card∧
   ∀ x:Fin n→Bool,C.eval (List.ofFn x)=f x:=by
 obtain ⟨C,hC,hsize,_,heval⟩:=a83 h
 exact ⟨C,hC,hsize,heval⟩
end L8.qbh.jb
namespace L8.jA.k8
open L8.z3.za L8.z3.zq L8.zL.vZ
variable {k:ℕ}
theorem a33 (i j:Fin k):row i≠col j:=by
 intro h
 have e:=congrArg (fun z:Fin (k+k)=>z.val) h
 change i.val=k+j.val at e
 omega
theorem a57 (i j:Fin k):col i≠row j:=(a33 j i).symm
def vM (S:Finset (Fin k)):Finset (Fin (k+k)):=S.image row ∪ S.image col
def jg (p:Equiv.Perm (Fin k)) (i:Fin k) (x:Fin (k+k)→Bool):Prop:=
 (x (row i)=true∧x (col i)=true)∨
 (p i≠i∧((x (row i)=true∧x (row (p i))=true)∨
   (x (col i)=true∧x (col (p i))=true)))
noncomputable def vd (p:Equiv.Perm (Fin k)) (S:Finset (Fin k))
 (x:Fin (k+k)→Bool):Bool:=by
 classical
 exact decide (∃ i∈S,jg p i x)
theorem a81 (S T:Finset (Fin k)):vM (S ∪ T)=vM S ∪ vM T:=by
 classical
 ext i
 simp only [vM,Finset.mem_union,Finset.mem_image]
 aesop
theorem a68 {S T:Finset (Fin k)} (hd:Disjoint S T):
 Disjoint (vM S) (vM T):=by
 classical
 rw [Finset.disjoint_left] at hd ⊢
 intro v hv hw
 simp only [vM,Finset.mem_union,Finset.mem_image] at hv hw
 rcases hv with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
 · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
   · exact hd hi ((a10 he) ▸ hj)
   · exact a57 j i he
 · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
   · exact a33 j i he
   · exact hd hi ((a14 he) ▸ hj)
theorem a73 (p:Equiv.Perm (Fin k)) (S T:Finset (Fin k)):
 vd p (S ∪ T)=fun x=>vd p S x||vd p T x:=by
 funext x
 apply Bool.eq_iff_iff.mpr
 simp only [vd,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
 aesop
theorem a85 (p:Equiv.Perm (Fin k)) (i:Fin k) (hi:p i=i):
 RO (vM {i}) (vd p {i}):=by
 have hr:=yK (by simpa using a33 i i) (a34 (row i)) (a34 (col i))
 convert hr using 1
 · simp [vM]
 · funext x
   simp [vd,jg,hi]
theorem a90 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
 (i j:Fin k) (hij:i≠j) (hpij:p i=j):
 RO (vM {i,j}) (vd p {i,j}):=by
 have hpji:p j=i:=by rw [← hpij,hp i]
 have hA:=yU (by simpa using a33 i j) (a34 (row i)) (a34 (col j))
 have hB:=yU (by simpa using a57 i j) (a34 (col i)) (a34 (row j))
 have hd:Disjoint (({row i} ∪ {col j}):Finset (Fin (k+k))) ({col i} ∪ {row j}):=by
  rw [Finset.disjoint_left]
  intro v hv hw
  simp only [Finset.mem_union,Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl
  · rcases hw with he | he
    · exact a33 i i he
    · exact hij (a10 he)
  · rcases hw with he | he
    · exact hij.symm (a14 he)
    · exact a57 j j he
 have hr:=yK hd hA hB
 convert hr using 1
 · ext v
   simp only [vM,Finset.image_insert,Finset.image_singleton,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton]
   tauto
 · funext x
   apply Bool.eq_iff_iff.mpr
   simp only [vd,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton,
    exists_eq_or_imp,exists_eq_left,jg,hpij,hpji,Bool.and_eq_true,Bool.or_eq_true]
   tauto
theorem a79 (p:Equiv.Perm (Fin k)) (S T:Finset (Fin k))
 (hd:Disjoint S T) (hS:RO (vM S) (vd p S)) (hT:RO (vM T) (vd p T)):
 RO (vM (S ∪ T)) (vd p (S ∪ T)):=by
 rw [a81,a73]
 exact yU (a68 hd) hS hT
theorem a72 (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p)
 (S:Finset (Fin k)) (hS:∀ i∈S,p i∈S) (hne:S.Nonempty):
 RO (vM S) (vd p S):=by
 classical
 revert hS hne
 refine Finset.strongInductionOn S ?_
 intro S ih hS hne
 obtain ⟨i,hi⟩:=hne
 by_cases hfix:p i=i
 · let T:=S.erase i
   have ht:T ⊂ S:=Finset.erase_ssubset hi
   have hclose:∀ j∈T,p j∈T:=by
    intro j hj
    have hjs:=Finset.mem_erase.mp hj
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      apply hjs.1
      exact p.injective (he.trans hfix.symm)
    · exact hS j hjs.2
   have heq:S={i} ∪ T:=by simp [T,hi]
   by_cases hempty:T=∅
   · rw [heq,hempty,Finset.union_empty]
     exact a85 p i hfix
   · rw [heq]
     apply a79 p {i} T
     · simp [T]
     · exact a85 p i hfix
     · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
 · let j:=p i
   have hij:i≠j:=Ne.symm hfix
   have hj:j∈S:=hS i hi
   have hpji:p j=i:=hp i
   let T:=(S.erase i).erase j
   have ht:T ⊂ S:=
    lt_of_le_of_lt (Finset.erase_subset j (S.erase i)) (Finset.erase_ssubset hi)
   have hclose:∀ a∈T,p a∈T:=by
    intro a ha
    have h:=Finset.mem_erase.mp ha
    have h':=Finset.mem_erase.mp h.2
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact h'.1 (p.injective he)
    · apply Finset.mem_erase.mpr
      constructor
      · intro he
        exact h.1 (p.injective (he.trans hpji.symm))
      · exact hS a h'.2
   have heq:S={i,j} ∪ T:=by
    ext a
    simp only [T,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
     Finset.mem_erase]
    constructor
    · intro ha
      by_cases hai:a=i
      · exact Or.inl (Or.inl hai)
      · by_cases haj:a=j
        · exact Or.inl (Or.inr haj)
        · exact Or.inr ⟨haj,hai,ha⟩
    · rintro ((rfl | rfl) | ⟨-,-,ha⟩)
      · exact hi
      · exact hj
      · exact ha
   by_cases hempty:T=∅
   · rw [heq,hempty,Finset.union_empty]
     exact a90 p hp i j hij rfl
   · rw [heq]
     apply a79 p {i,j} T
     · simp [T,Finset.disjoint_left]
     · exact a90 p hp i j hij rfl
     · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
theorem j9 (hk:0 < k) (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p):
 RO Finset.univ (fun x:Fin (k+k)→Bool=>a5 p (fun i=>x (row i))
  (fun i=>x (col i))):=by
 have h:=a72 p hp Finset.univ (by simp) ⟨⟨0,hk⟩,Finset.mem_univ _⟩
 have hs:vM (Finset.univ:Finset (Fin k))=Finset.univ:=by
  ext v
  simp only [Finset.mem_univ,iff_true]
  induction v using Fin.addCases with
  | left i=>exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  | right i=>exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
 rw [hs] at h
 have he:vd p Finset.univ=(fun x:Fin (k+k)→Bool=>a5 p (fun i=>x (row i)) (fun i=>x (col i))):=by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [vd,jg,a5]
 rw [he] at h
 exact h
end L8.jA.k8
namespace L8.jA.kX
open L8.zL.vZ L8.z3.za L8.z3.zq
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem a46 {k:ℕ} (p:Equiv.Perm (Fin k)) (i j:Fin k):
 a5 p (qP i) (qP j)=decide (i=j):=by
 apply Bool.eq_iff_iff.mpr
 simp only [a5,qP,decide_eq_true_eq]
 constructor
 · rintro ⟨a,⟨hai,haj⟩ | ⟨hne,h | h⟩⟩
   · exact hai.symm.trans haj
   · exact False.elim (hne (h.2.trans h.1.symm))
   · exact False.elim (hne (h.2.trans h.1.symm))
 · intro hij
   exact ⟨i,Or.inl ⟨rfl,hij⟩⟩
theorem yc
 (compileRO:∀ {n:ℕ} {S:Finset (Fin n)} {f:(Fin n→Bool)→Bool},
   RO S f→∃ C:Circuit,Monotone2 C∧C.size+1=S.card∧
    ∀ x,C.eval (List.ofFn x)=f x)
 {k:ℕ} (hk:0 < k) (p:Equiv.Perm (Fin k)) (hp:Function.Involutive p):
 ∃ C:Circuit,Monotone2 C∧C.size+1≤2*k∧
   Represents (fun i j:Fin k=>decide (i=j)) C∧
   ∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
 obtain ⟨C,hm,hs,he⟩:=compileRO (k8.j9 hk p hp)
 have hfull:∀ x y,C.eval (List.ofFn x++List.ofFn y)=a5 p x y:=by
  intro x y
  simpa only [List.ofFn_fin_append,Fin.append_left,Fin.append_right]
   using he (Fin.append x y)
 refine ⟨C,hm,?_,?_,hfull⟩
 · simp only [Finset.card_univ,Fintype.card_fin] at hs
   omega
 · intro i j
   change C.eval (List.ofFn (qP i)++List.ofFn (qP j))=decide (i=j)
   rw [hfull,a46]
end L8.jA.kX
namespace L8.jA
theorem wc:∀ (k:Nat),2≤k→∀ f:(Fin k→Bool)→(Fin k→Bool)→Bool,
 (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1≤2*k∧
   PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C∧
   ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y))↔
 ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
  ∀ x y,f x y=decide (∃ i:Fin k,
      (x i=true∧y i=true)∨
      (p i≠i∧((x i=true∧x (p i)=true)∨
        (y i=true∧y (p i)=true)))):=by
 intro k hk f
 constructor
 · exact L8.zL.u6 k hk f
 · rintro ⟨p,⟨hp,hf⟩,hu⟩
   obtain ⟨C,hm,hs,hr,he⟩:=kX.yc
    (fun h=>L8.qbh.jb.uS h) (by omega:0 < k) p hp
   refine ⟨C,hm,hs,hr,?_⟩
   intro x y
   exact (hf x y).trans (he x y).symm
end L8.jA
theorem qaJ:
∀ (k:Nat),2≤k→∀ f:(Fin k→Bool)→(Fin k→Bool)→Bool,
  (∃ C:PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.Monotone2 C∧C.size+1≤2*k∧
    PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C∧
    ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y))↔
  ∃! p:Equiv.Perm (Fin k),Function.Involutive p∧
   ∀ x y,f x y=decide (∃ i:Fin k,
       (x i=true∧y i=true)∨
       (p i≠i∧((x i=true∧x (p i)=true)∨
         (y i=true∧y (p i)=true)))):=L8.jA.wc
end
section
namespace qaZ
namespace qr
open Finset
def qT (t:Nat):Finset Nat:={2*t,2*t+1,2*t+2}
def qE (r t:Nat):Finset Nat:=
 if 2*t+2≤r then {2*t,2*t+1}
 else if r≤2*t then {2*t+1,2*t+2}
 else {2*t,2*t+2}
theorem qay (t:Nat) (A:Finset Nat) (hs:A⊆qT t) (hc:A.card=2):
 A={2*t,2*t+1}∨A={2*t,2*t+2}∨A={2*t+1,2*t+2}:=by
 obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hc
 have hx:=hs (Finset.mem_insert_self x {y})
 have hy:=hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
 simp only [qT,Finset.mem_insert,Finset.mem_singleton] at hx hy
 rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
  simp_all [Finset.pair_comm]
theorem qaL (e r:Nat) (hr:r≤2*e):
 (Finset.range (2*e+1) \ {r}) ∪ {2*e+1,2*e+2}=
   Finset.range (2*(e+1)+1) \ {r}:=by
 ext x
 simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
  Finset.mem_insert,Finset.mem_singleton]
 omega
theorem add_left (e:Nat):
 (Finset.range (2*e+1) \ {2*e}) ∪ {2*e,2*e+1}=
   Finset.range (2*(e+1)+1) \ {2*e+2}:=by
 ext x
 simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
  Finset.mem_insert,Finset.mem_singleton]
 omega
theorem qaK (e:Nat):
 (Finset.range (2*e+1) \ {2*e}) ∪ {2*e,2*e+2}=
   Finset.range (2*(e+1)+1) \ {2*e+1}:=by
 ext x
 simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
  Finset.mem_insert,Finset.mem_singleton]
 omega
theorem kY (e t:Nat) (ht:t<e):
 qE (2*e) t=qE (2*e+1) t∧qE (2*e) t=qE (2*e+2) t:=by
 have h0:2*t+2≤2*e:=by omega
 have h1:2*t+2≤2*e+1:=by omega
 have h2:2*t+2≤2*e+2:=by omega
 simp only [qE,if_pos h0,if_pos h1,if_pos h2,and_self]
theorem yD (e:Nat) (f:Nat→Finset Nat)
 (hs:∀ t<e,f t⊆qT t)
 (hc:∀ t<e,(f t).card=2)
 (hd:∀ i<e,∀ j<e,i≠j→Disjoint (f i) (f j)):
 ∃ r,r≤2*e∧(∀ t<e,f t=qE r t)∧
   (Finset.range e).biUnion f=Finset.range (2*e+1) \ {r}:=by
 induction e with
 | zero=>
   refine ⟨0,by omega,by omega,?_⟩
   simp
 | succ e ih=>
   obtain ⟨r,hr,hf,hunion⟩:=ih (fun t ht=>hs t (by omega))
    (fun t ht=>hc t (by omega)) (fun i hi j hj hij=>hd i (by omega) j (by omega) hij)
   have hdis:Disjoint ((Finset.range e).biUnion f) (f e):=by
    apply Finset.disjoint_left.mpr
    intro x hx hxe
    obtain ⟨t,ht,hxt⟩:=Finset.mem_biUnion.mp hx
    exact Finset.disjoint_left.mp (hd t (by have:=Finset.mem_range.mp ht; omega) e (by omega)
     (Nat.ne_of_lt (Finset.mem_range.mp ht))) hxt hxe
   have hforce (he:2*e∈f e):r=2*e:=by
    by_contra hne
    have hm:2*e∈(Finset.range e).biUnion f:=by
     rw [hunion]
     simp only [Finset.mem_sdiff,Finset.mem_range,Finset.mem_singleton]
     exact ⟨by omega,Ne.symm hne⟩
    exact Finset.disjoint_left.mp hdis hm he
   have hbi:(Finset.range (e+1)).biUnion f=(Finset.range e).biUnion f ∪ f e:=by
    rw [Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]
   rcases qay e (f e) (hs e (by omega)) (hc e (by omega)) with he|he|he
   · have hre:r=2*e:=hforce (by simp [he])
     subst r
     refine ⟨2*e+2,by omega,?_,?_⟩
     · intro t ht
       by_cases hte:t<e
       · exact (hf t hte).trans (kY e t hte).2
       · have hte:t=e:=by omega
         subst t
         simp [he,qE]
     · rw [hbi,hunion,he]
       exact add_left e
   · have hre:r=2*e:=hforce (by simp [he])
     subst r
     refine ⟨2*e+1,by omega,?_,?_⟩
     · intro t ht
       by_cases hte:t<e
       · exact (hf t hte).trans (kY e t hte).1
       · have hte:t=e:=by omega
         subst t
         simp [he,qE]
     · rw [hbi,hunion,he]
       exact qaK e
   · refine ⟨r,by omega,?_,?_⟩
     · intro t ht
       by_cases hte:t<e
       · exact hf t hte
       · have hte:t=e:=by omega
         subst t
         have hn:¬2*e+2≤r:=by omega
         simp [he,qE,hn,hr]
     · rw [hbi,hunion,he]
       exact qaL e r hr
theorem zR (r t:Nat):qE r t⊆qT t:=by
 intro x hx
 unfold qE at hx
 split_ifs at hx <;> simp only [Finset.mem_insert,Finset.mem_singleton,qT] at * <;> aesop
theorem vO (r t:Nat):(qE r t).card=2:=by
 have h1:2*t≠2*t+1:=by omega
 have h2:2*t≠2*t+2:=by omega
 have h3:2*t+1≠2*t+2:=by omega
 unfold qE
 split_ifs <;> simp [h1,h2,h3]
theorem kk (r t:Nat):r∉qE r t:=by
 unfold qE
 split_ifs <;> simp only [Finset.mem_insert,Finset.mem_singleton,not_or] <;> omega
theorem yh (r i j:Nat) (hij:i≠j):Disjoint (qE r i) (qE r j):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 unfold qE at hx hy
 split_ifs at hx hy <;> simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy <;> omega
theorem yE (e:Nat) (f:Nat→Finset Nat) (r s:Nat)
 (hr:r≤2*e) (hs:s≤2*e)
 (hunion:(Finset.range e).biUnion f=Finset.range (2*e+1) \ {r})
 (hf:∀ t<e,f t=qE s t):r=s:=by
 by_contra hne
 have hm:s∈(Finset.range e).biUnion f:=by
  rw [hunion]
  simp only [Finset.mem_sdiff,Finset.mem_range,Finset.mem_singleton]
  exact ⟨by omega,Ne.symm hne⟩
 obtain ⟨t,ht,hst⟩:=Finset.mem_biUnion.mp hm
 rw [hf t (Finset.mem_range.mp ht)] at hst
 exact kk s t hst
theorem yi (e r:Nat) (hr:r≤2*e):
 (Finset.range e).biUnion (qE r)=Finset.range (2*e+1) \ {r}:=by
 obtain ⟨s,hs,hf,hunion⟩:=yD e (qE r)
  (fun t _=>zR r t) (fun t _=>vO r t)
  (fun i _ j _ hij=>yh r i j hij)
 have he:s=r:=yE e (qE r) s r hs hr hunion (fun _ _=>rfl)
 simpa only [he] using hunion
theorem qaV (e:Nat) (f:Nat→Finset Nat)
 (hs:∀ t<e,f t⊆qT t) (hc:∀ t<e,(f t).card=2)
 (hd:∀ i<e,∀ j<e,i≠j→Disjoint (f i) (f j)):
 ∃! r,r≤2*e∧∀ t<e,f t=qE r t:=by
 obtain ⟨r,hr,hf,hunion⟩:=yD e f hs hc hd
 refine ⟨r,⟨hr,hf⟩,?_⟩
 intro s hs
 exact (yE e f r s hr hs.1 hunion hs.2).symm
def qas (e:Nat) (f:Fin e→Finset Nat):Prop:=
 (∀ t,f t⊆qT t.val∧(f t).card=2)∧
 ∀ i j,i≠j→Disjoint (f i) (f j)
def ud (e:Nat) (r:Fin (2*e+1)):{f:Fin e→Finset Nat // qas e f}:=
 ⟨fun t=>qE r.val t.val,
   (fun t=>⟨zR _ _,vO _ _⟩),
   fun i j hij=>yh _ _ _ (fun he=>hij (Fin.ext he))⟩
theorem k4 (e:Nat):Function.Injective (ud e):=by
 intro r s he
 apply Fin.ext
 apply yE e (qE r.val) r.val s.val (by omega) (by omega) (yi e r.val (by omega))
 intro t ht
 exact congrFun (congrArg Subtype.val he) ⟨t,ht⟩
theorem kM (e:Nat):Function.Surjective (ud e):=by
 classical
 intro f
 let g (t:Nat):=if ht:t<e then f.val ⟨t,ht⟩ else ∅
 have hg (t:Fin e):g t.val=f.val t:=by simp only [g,dif_pos t.isLt]
 obtain ⟨r,hr,hf,hunion⟩:=yD e g
  (fun t ht=>by simpa only [g,dif_pos ht] using (f.property.1 ⟨t,ht⟩).1)
  (fun t ht=>by simpa only [g,dif_pos ht] using (f.property.1 ⟨t,ht⟩).2)
  (fun i hi j hj hij=>by
    simpa only [g,dif_pos hi,dif_pos hj] using f.property.2 ⟨i,hi⟩ ⟨j,hj⟩ (by simpa using hij))
 refine ⟨⟨r,by omega⟩,?_⟩
 apply Subtype.ext
 funext t
 exact (hf t.val t.isLt).symm.trans (hg t)
noncomputable def qaU (e:Nat):Fin (2*e+1) ≃ {f:Fin e→Finset Nat // qas e f}:=
 Equiv.ofBijective (ud e) ⟨k4 e,kM e⟩
theorem qaI (e:Nat):Nat.card {f:Fin e→Finset Nat // qas e f}=2*e+1:=by
 rw [← Nat.card_congr (qaU e),Nat.card_fin]
theorem ja (i j x y:Nat) (hx:x∈qT i) (hy:y∈qT i)
 (hx':x∈qT j) (hy':y∈qT j) (hne:x≠y):i=j:=by
 simp only [qT,Finset.mem_insert,Finset.mem_singleton] at hx hy hx' hy'
 omega
def q8 (p:Nat→Nat) (A:Finset Nat):Prop:=
 ∀ x∈A,p x∈A∧p x≠x
theorem y7 (p:Nat→Nat) (hp:Function.Involutive p) (a:Nat) (ha:p a≠a):
 q8 p {a,p a}:=by
 intro x hx
 simp only [Finset.mem_insert,Finset.mem_singleton] at hx
 rcases hx with rfl|rfl
 · exact ⟨by simp,ha⟩
 · rw [hp a]
   exact ⟨by simp,Ne.symm ha⟩
theorem wT (p:Nat→Nat) (hp:Function.Involutive p) (a x:Nat)
 (hx:x∈({a,p a}:Finset Nat)):({x,p x}:Finset Nat)={a,p a}:=by
 simp only [Finset.mem_insert,Finset.mem_singleton] at hx
 rcases hx with rfl|rfl
 · rfl
 · rw [hp a,Finset.pair_comm]
theorem w9 (e:Nat) (p:Nat→Nat) (hp:Function.Involutive p)
 (hw:∀ t<e,∃ x,x∈qT t∧p x∈qT t∧p x≠x):
 ∃ r,r≤2*e∧∀ t<e,q8 p (qE r t):=by
 classical
 have hw' (t:Fin e):∃ x,x∈qT t.val∧p x∈qT t.val∧p x≠x:=hw t.val t.isLt
 choose a ha hpa hne using hw'
 let f (t:Nat):=if ht:t<e then ({a ⟨t,ht⟩,p (a ⟨t,ht⟩)}:Finset Nat) else ∅
 have hf (t:Fin e):f t.val={a t,p (a t)}:=by simp only [f,dif_pos t.isLt]
 have hs (t:Nat) (ht:t<e):f t⊆qT t:=by
  rw [hf ⟨t,ht⟩]
  exact Finset.insert_subset_iff.mpr ⟨ha _,Finset.singleton_subset_iff.mpr (hpa _)⟩
 have hc (t:Nat) (ht:t<e):(f t).card=2:=by
  rw [hf ⟨t,ht⟩]
  simp [Ne.symm (hne ⟨t,ht⟩)]
 have hd (i:Nat) (hi:i<e) (j:Nat) (hj:j<e) (hij:i≠j):Disjoint (f i) (f j):=by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  rw [hf ⟨i,hi⟩] at hxi
  rw [hf ⟨j,hj⟩] at hxj
  have he:=(wT p hp (a ⟨i,hi⟩) x hxi).symm.trans (wT p hp (a ⟨j,hj⟩) x hxj)
  have hsub:({a ⟨i,hi⟩,p (a ⟨i,hi⟩)}:Finset Nat)⊆qT j:=by
   rw [he]
   exact Finset.insert_subset_iff.mpr ⟨ha _,Finset.singleton_subset_iff.mpr (hpa _)⟩
  exact hij (ja i j (a ⟨i,hi⟩) (p (a ⟨i,hi⟩)) (ha ⟨i,hi⟩) (hpa ⟨i,hi⟩)
   (hsub (by simp)) (hsub (by simp)) (Ne.symm (hne ⟨i,hi⟩)))
 obtain ⟨r,hr,hroot,hunion⟩:=yD e f hs hc hd
 refine ⟨r,hr,?_⟩
 intro t ht
 rw [← hroot t ht,hf ⟨t,ht⟩]
 exact y7 p hp _ (hne _)
theorem qbd (e r:Nat) (hr:r≤2*e) (p:Nat→Nat)
 (hpaired:∀ t<e,q8 p (qE r t))
 (x:Nat) (hx:x<2*e+1) (hxr:x≠r):
 ∃ t<e,x∈qE r t∧p x∈qE r t∧p x≠x:=by
 have hm:x∈(Finset.range e).biUnion (qE r):=by
  rw [yi e r hr]
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx,by simpa using hxr⟩
 obtain ⟨t,ht,hxt⟩:=Finset.mem_biUnion.mp hm
 exact ⟨t,Finset.mem_range.mp ht,hxt,hpaired t (Finset.mem_range.mp ht) x hxt⟩
end qr
namespace LoosePathStructure
open Finset
def leaf (e j:Nat):=if j=0 then 0 else if j=e+1 then 2*e else 2*j-1
def qF (e:Nat) (z:Nat×Nat):Finset Nat:=
 {z.1*(2*e+1)+2*z.2,z.1*(2*e+1)+2*z.2+1,z.1*(2*e+1)+2*z.2+2}
def qn (v e m:Nat) (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (z:Fin m×Bool):Finset Nat:=
 {v*(2*e+1)+2*z.1.val,v*(2*e+1)+2*z.1.val+1,
   (wire z).1.val*(2*e+1)+leaf e (wire z).2.val}
lemma vt {e j:Nat} (h:j < e+2):leaf e j < 2*e+1:=by
 unfold leaf
 split_ifs <;> omega
lemma kO {e:Nat} (he:0 < e):
 Function.Injective (fun j:Fin (e+2)=>leaf e j.val):=by
 intro i j h
 apply Fin.ext
 have hi:=i.isLt
 have hj:=j.isLt
 dsimp only [leaf] at h
 split_ifs at h <;> omega
lemma z1 {q u u' a a':Nat} (ha:a < q) (ha':a' < q)
 (h:u*q+a=u'*q+a'):u=u'∧a=a':=by
 have hu:u=u':=by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hh | hh
  · have:u+1≤u':=hh
    nlinarith
  · have:u'+1≤u:=hh
    nlinarith
 subst u'
 exact ⟨rfl,by omega⟩
lemma yX {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (z:Fin m×Bool):
 (wire z).1.val*(2*e+1)+leaf e (wire z).2.val < v*(2*e+1):=by
 have ha:=vt (wire z).2.isLt
 have hb:=(wire z).1.isLt
 nlinarith
lemma wg (e:Nat) (z:Nat×Nat):(qF e z).card=3:=by
 simp [qF,card_insert_of_notMem]
lemma uC {v:Nat} (e:Nat):
 Set.InjOn (qF e) (↑((range v ×ˢ range e)):Set (Nat×Nat)):=by
 intro a ha b hb hab
 simp only [mem_coe,mem_product,mem_range] at ha hb
 have hmin:a.1*(2*e+1)+2*a.2=b.1*(2*e+1)+2*b.2:=by
  have h1:a.1*(2*e+1)+2*a.2∈qF e b:=by rw [← hab]; simp [qF]
  have h2:b.1*(2*e+1)+2*b.2∈qF e a:=by rw [hab]; simp [qF]
  simp only [qF,mem_insert,mem_singleton] at h1 h2
  omega
 have hh:=z1 (q:=2*e+1) (by omega:2*a.2 < 2*e+1)
  (by omega:2*b.2 < 2*e+1) hmin
 exact Prod.ext hh.1 (by omega)
lemma jz {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (z:Fin m×Bool):(qn v e m wire z).card=3:=by
 have hp:=yX wire z
 unfold qn
 rw [card_insert_of_notMem,card_insert_of_notMem,card_singleton]
 · simp only [mem_singleton]; omega
 · simp only [mem_insert,mem_singleton]; omega
lemma kG {v e m:Nat} (he:0 < e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):
 Function.Injective (qn v e m wire):=by
 intro a b hab
 have ha:=yX wire a
 have hb:=yX wire b
 have hport:(wire a).1.val*(2*e+1)+leaf e (wire a).2.val=
  (wire b).1.val*(2*e+1)+leaf e (wire b).2.val:=by
  have hh:(wire a).1.val*(2*e+1)+leaf e (wire a).2.val∈qn v e m wire b:=by
   rw [← hab]; simp [qn]
  simp only [qn,mem_insert,mem_singleton] at hh
  omega
 have hh:=z1 (vt (wire a).2.isLt) (vt (wire b).2.isLt) hport
 apply wire.injective
 exact Prod.ext (Fin.ext hh.1) (kO he hh.2)
lemma yC {v e:Nat} {z:Nat×Nat} (hz:z∈(range v ×ˢ range e))
 {x:Nat} (hx:x∈qF e z):x < v*(2*e+1):=by
 simp only [mem_product,mem_range] at hz
 simp only [qF,mem_insert,mem_singleton] at hx
 rcases hx with rfl | rfl | rfl <;> nlinarith [hz.1,hz.2]
theorem qa7 {v e m:Nat} (he:0 < e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):
 let A:=((range v ×ˢ range e)).image (qF e)
 let B:=univ.image (qn v e m wire)
 (A ∪ B).card=v*e+2*m∧∀ R∈A ∪ B,R.card=3:=by
 dsimp
 have hd:Disjoint (((range v ×ˢ range e)).image (qF e))
  (univ.image (qn v e m wire)):=by
  rw [disjoint_left]
  intro R ha hb
  obtain ⟨a,hidx,rfl⟩:=mem_image.mp ha
  obtain ⟨b,_,h⟩:=mem_image.mp hb
  have hmem:v*(2*e+1)+2*b.1.val∈qF e a:=by rw [← h]; simp [qn]
  have:=yC hidx hmem
  omega
 constructor
 · rw [card_union_of_disjoint hd,card_image_of_injOn (uC e),
    card_image_of_injective _ (kG he wire),card_product,
    card_range,card_range,card_univ,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool]
   omega
 · intro R hR
   rcases mem_union.mp hR with hR | hR
   · obtain ⟨a,_,rfl⟩:=mem_image.mp hR
     exact wg e a
   · obtain ⟨a,_,rfl⟩:=mem_image.mp hR
     exact jz wire a
lemma wP (e x:Nat) (he:0 < e) (hx:x≤2*e):
 (∑ t∈range e,if x∈({2*t,2*t+1,2*t+2}:Finset Nat) then 1 else 0) +
   (if x=0∨x=2*e∨x % 2=1 then 1 else 0)=2:=by
 induction e with
 | zero=>omega
 | succ e ih=>
   by_cases he0:e=0
   · subst e
     have:x≤2:=by omega
     interval_cases x <;> decide
   · have he:0 < e:=by omega
     rw [sum_range_succ]
     simp only [mem_insert,mem_singleton]
     by_cases hsmall:x≤2*e
     · have hi:=ih he hsmall
       simp only [mem_insert,mem_singleton] at hi
       have hp:((if x=2*e∨x=2*e+1∨x=2*e+2 then 1 else 0) +
        (if x=0∨x=2*(e+1)∨x %2=1 then 1 else 0):Nat)=
        (if x=0∨x=2*e∨x %2=1 then 1 else 0):=by
        split_ifs <;> omega
       rw [Nat.add_assoc,hp]
       exact hi
     · have hz:∑ t∈range e,(if x∈({2*t,2*t+1,2*t+2}:Finset Nat) then 1 else 0)=0:=by
        apply sum_eq_zero
        intro t ht
        have ht':t < e:=mem_range.mp ht
        simp only [mem_insert,mem_singleton]
        rw [if_neg (by omega)]
       simp only [mem_insert,mem_singleton] at hz
       rw [hz]
       split_ifs <;> omega
lemma wY {e a u x t:Nat} (hx:x < 2*e+1) (ht:t < e):
 a*(2*e+1)+x∈qF e (u,t)↔u=a∧x∈({2*t,2*t+1,2*t+2}:Finset Nat):=by
 simp only [qF,mem_insert,mem_singleton]
 constructor
 · intro h
   rcases h with h | h | h
   · have hh:=z1 hx (by omega:2*t < 2*e+1) h
     exact ⟨hh.1.symm,Or.inl hh.2⟩
   · have hh:=z1 hx (by omega:2*t+1 < 2*e+1) (by omega:a*(2*e+1)+x=u*(2*e+1)+(2*t+1))
     exact ⟨hh.1.symm,Or.inr (Or.inl hh.2)⟩
   · have hh:=z1 hx (by omega:2*t+2 < 2*e+1) (by omega:a*(2*e+1)+x=u*(2*e+1)+(2*t+2))
     exact ⟨hh.1.symm,Or.inr (Or.inr hh.2)⟩
 · rintro ⟨rfl,h⟩
   rcases h with rfl | rfl | rfl <;> omega
lemma qaz {v e a x:Nat} (ha:a < v) (hx:x < 2*e+1):
 ((((range v ×ˢ range e).image (qF e)).filter
   (fun R=>a*(2*e+1)+x∈R)).card)=
   ∑ t∈range e,if x∈({2*t,2*t+1,2*t+2}:Finset Nat) then 1 else 0:=by
 rw [card_eq_sum_ones,sum_filter,sum_image (uC e),sum_product]
 have hi:∀ u∈range v,∀ t∈range e,
  (if a*(2*e+1)+x∈qF e (u,t) then 1 else 0)=
  if u=a then (if x∈({2*t,2*t+1,2*t+2}:Finset Nat) then 1 else 0) else 0:=by
  intro u hu t ht
  simp only [wY hx (mem_range.mp ht)]
  split_ifs <;> simp_all
 trans ∑ u∈range v,∑ t∈range e,
  if u=a then (if x∈({2*t,2*t+1,2*t+2}:Finset Nat) then 1 else 0) else 0
 · apply sum_congr rfl
   intro u hu
   exact sum_congr rfl (hi u hu)
 · simp only [sum_ite_irrel,sum_const_zero]
   simp [ha]
lemma uY {e x:Nat} (he:0 < e) (hx:x < 2*e+1):
 (∃ j:Fin (e+2),leaf e j.val=x)↔x=0∨x=2*e∨x %2=1:=by
 constructor
 · rintro ⟨j,hj⟩
   have ht:=j.isLt
   dsimp only [leaf] at hj
   split_ifs at hj <;> omega
 · rintro (h | h | h)
   · exact ⟨⟨0,by omega⟩,by simp [leaf,h]⟩
   · exact ⟨⟨e+1,by omega⟩,by simp [leaf,h]⟩
   · refine ⟨⟨(x+1)/2,by omega⟩,?_⟩
     dsimp only [leaf]
     split_ifs <;> omega
lemma qa5 {v e m:Nat} (he:0 < e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):
 Function.Injective (fun z=>(wire z).1.val*(2*e+1)+leaf e (wire z).2.val):=by
 intro a b h
 have hh:=z1 (vt (wire a).2.isLt) (vt (wire b).2.isLt) h
 apply wire.injective
 exact Prod.ext (Fin.ext hh.1) (kO he hh.2)
lemma kS {v e m x:Nat}
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (hx:x < v*(2*e+1)) (z:Fin m×Bool):
 x∈qn v e m wire z↔x=(wire z).1.val*(2*e+1)+leaf e (wire z).2.val:=by
 simp only [qn,mem_insert,mem_singleton]
 omega
lemma u8 {v e m a x:Nat} (he:0 < e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (ha:a < v) (hx:x < 2*e+1):
 ((univ.image (qn v e m wire)).filter (fun R=>a*(2*e+1)+x∈R)).card=
   if x=0∨x=2*e∨x %2=1 then 1 else 0:=by
 have hlow:a*(2*e+1)+x < v*(2*e+1):=by nlinarith
 by_cases hl:x=0∨x=2*e∨x %2=1
 · rw [if_pos hl]
   obtain ⟨j,hj⟩:=(uY he hx).mpr hl
   let z:=wire.symm (⟨a,ha⟩,j)
   have hz:wire z=(⟨a,ha⟩,j):=wire.apply_symm_apply _
   have hf:((univ.image (qn v e m wire)).filter
    (fun R=>a*(2*e+1)+x∈R))={qn v e m wire z}:=by
    ext R
    simp only [mem_filter,mem_image,mem_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩
      have hp:=(kS wire hlow w).mp hw
      have hwz:w=z:=qa5 he wire (by dsimp only; rw [hz]; dsimp; omega)
      rw [hwz]
    · rintro rfl
      refine ⟨⟨z,rfl⟩,(kS wire hlow z).mpr ?_⟩
      rw [hz]
      dsimp
      omega
   rw [hf,card_singleton]
 · rw [if_neg hl]
   rw [card_eq_zero]
   apply eq_empty_iff_forall_notMem.mpr
   intro R hR
   obtain ⟨hR,hmem⟩:=mem_filter.mp hR
   obtain ⟨z,_,rfl⟩:=mem_image.mp hR
   have hp:=(kS wire hlow z).mp hmem
   have hh:=z1 hx (vt (wire z).2.isLt) hp
   exact hl ((uY he hx).mp ⟨(wire z).2,hh.2.symm⟩)
lemma uV {v e m:Nat} (he:0 < e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (j:Fin m) (r:Nat) (hr:r < 2):
 ((univ.image (qn v e m wire)).filter
   (fun R=>v*(2*e+1)+2*j.val+r∈R)).card=2:=by
 have hmem (z:Fin m×Bool):v*(2*e+1)+2*j.val+r∈qn v e m wire z↔z.1=j:=by
  have hp:=yX wire z
  simp only [qn,mem_insert,mem_singleton]
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    have hh:=congrArg Fin.val h
    omega
 have hf:((univ.image (qn v e m wire)).filter
  (fun R=>v*(2*e+1)+2*j.val+r∈R))=
  {qn v e m wire (j,false),qn v e m wire (j,true)}:=by
  ext R
  simp only [mem_filter,mem_image,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · rintro ⟨⟨⟨z,b⟩,rfl⟩,hz⟩
    have hzj:=(hmem (z,b)).mp hz
    dsimp at hzj
    subst z
    cases b <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨(j,false),rfl⟩,(hmem _).mpr rfl⟩
    · exact ⟨⟨(j,true),rfl⟩,(hmem _).mpr rfl⟩
 rw [hf,card_pair]
 intro h
 have hh:=kG he wire h
 have:=congrArg Prod.snd hh
 simp at this
 theorem qbj {v e m:Nat} (he:0 < e)
  (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (i:Fin (v*(2*e+1)+2*m)):
  ((((range v ×ˢ range e).image (qF e)) ∪
    (univ.image (qn v e m wire))).filter (fun R=>i.val∈R)).card=2:=by
  let A:=(range v ×ˢ range e).image (qF e)
  let B:=univ.image (qn v e m wire)
  have hd:Disjoint A B:=by
   rw [disjoint_left]
   intro R hA hB
   obtain ⟨a,ha,rfl⟩:=mem_image.mp hA
   obtain ⟨b,_,h⟩:=mem_image.mp hB
   have hh:v*(2*e+1)+2*b.1.val∈qF e a:=by rw [←h]; simp [qn]
   have ht:=yC ha hh
   omega
  change ((A ∪ B).filter _).card=2
  rw [filter_union,card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _))]
  by_cases hlow:i.val < v*(2*e+1)
  · let a:=i.val/(2*e+1)
    let x:=i.val %(2*e+1)
    have hq:0 < 2*e+1:=by omega
    have ha:a < v:=(Nat.div_lt_iff_lt_mul hq).mpr hlow
    have hx:x < 2*e+1:=Nat.mod_lt _ hq
    have hix:i.val=a*(2*e+1)+x:=by dsimp [a,x]; simpa [Nat.mul_comm] using (Nat.div_add_mod i.val (2*e+1)).symm
    dsimp only [A,B]
    rw [hix,qaz ha hx,u8 he wire ha hx]
    exact wP e x he (by omega)
  · have hz:(A.filter (fun R=>i.val∈R)).card=0:=by
     rw [card_eq_zero]
     apply eq_empty_iff_forall_notMem.mpr
     intro R hR
     obtain ⟨hR,hmem⟩:=mem_filter.mp hR
     obtain ⟨a,ha,rfl⟩:=mem_image.mp hR
     exact hlow (yC ha hmem)
    rw [hz,Nat.zero_add]
    let d:=i.val-v*(2*e+1)
    have hd':d < 2*m:=by have:=i.isLt; dsimp [d]; omega
    let j:Fin m:=⟨d/2,by omega⟩
    have hix:i.val=v*(2*e+1)+2*j.val+d %2:=by dsimp [j,d]; omega
    dsimp only [B]
    rw [hix]
    exact uV he wire j (d %2) (by omega)
end LoosePathStructure
namespace qO
open Finset
def ka {v e:Nat} (r:Fin v→Fin (2*e+1)) (i:Fin v):Nat:=
 i.val*(2*e+1)+(r i).val
def qG (v e:Nat) {m:Nat} (z:Fin m×Bool):Nat:=
 v*(2*e+1)+2*z.1.val+z.2.toNat
def qx {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (z:Fin m×Bool):Nat:=
 (wire z).1.val*(2*e+1)+LoosePathStructure.leaf e (wire z).2.val
def z5 {v e:Nat} (r:Fin v→Fin (2*e+1)) (it:Fin v×Fin e):Finset Nat:=
 (qr.qE (r it.1).val it.2.val).image (fun x=>it.1.val*(2*e+1)+x)
theorem yB {e r t x:Nat} (ht:t<e) (hx:x∈qr.qE r t):x<2*e+1:=by
 have hh:=qr.zR r t hx
 simp only [qr.qT,Finset.mem_insert,Finset.mem_singleton] at hh
 omega
theorem k1 {v e:Nat} (r:Fin v→Fin (2*e+1)) (it:Fin v×Fin e):
 (z5 r it).card=2:=by
 rw [z5,Finset.card_image_of_injective _ (fun _ _ h=>Nat.add_left_cancel h)]
 exact qr.vO _ _
theorem y8 {v e:Nat} (r:Fin v→Fin (2*e+1)) (it:Fin v×Fin e)
 {x:Nat} (hx:x∈z5 r it):x<v*(2*e+1):=by
 obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
 have hyb:=yB it.2.isLt hy
 have hib:=it.1.isLt
 nlinarith
theorem qbU {v e:Nat} (r:Fin v→Fin (2*e+1)) (i:Fin v):
 ka r i<v*(2*e+1):=by
 have hi:=i.isLt
 have hr:=(r i).isLt
 dsimp [ka]
 nlinarith
theorem uT {v e:Nat} (r:Fin v→Fin (2*e+1)) (i:Fin v)
 (it:Fin v×Fin e):ka r i∉z5 r it:=by
 intro hh
 obtain ⟨x,hx,he⟩:=Finset.mem_image.mp hh
 have hxb:=yB it.2.isLt hx
 have hb:=LoosePathStructure.z1 hxb (r i).isLt he
 have hi:it.1=i:=Fin.ext hb.1
 rw [hi,hb.2] at hx
 exact qr.kk _ _ hx
theorem uQ {v e:Nat} (r:Fin v→Fin (2*e+1))
 (a b:Fin v×Fin e) (hab:a≠b):Disjoint (z5 r a) (z5 r b):=by
 apply Finset.disjoint_left.mpr
 intro x hxa hxb
 obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hxa
 obtain ⟨z,hz,hf⟩:=Finset.mem_image.mp hxb
 have hb:=LoosePathStructure.z1 (yB a.2.isLt hy) (yB b.2.isLt hz)
  (he.trans hf.symm)
 have hi:a.1=b.1:=Fin.ext hb.1
 have ht:a.2.val≠b.2.val:=by
  intro ht
  exact hab (Prod.ext hi (Fin.ext ht))
 rw [hi,hb.2] at hy
 exact Finset.disjoint_left.mp (qr.yh _ _ _ ht) hy hz
theorem zw (v e:Nat) {m:Nat} (z:Fin m×Bool):v*(2*e+1)≤qG v e z:=by
 simp only [qG]
 omega
theorem yV (v e:Nat) {m:Nat} (z:Fin m×Bool):
 qG v e z<v*(2*e+1)+2*m:=by
 have hz:=z.1.isLt
 rcases z with ⟨j,b⟩
 have hj:=j.isLt
 cases b <;> simp [qG] <;> omega
theorem vJ (v e m:Nat):Function.Injective (qG v e (m:=m)):=by
 rintro ⟨i,a⟩ ⟨j,b⟩ he
 cases a <;> cases b <;> simp [qG] at he
 all_goals first | (exfalso; omega) | (apply Prod.ext; exact Fin.ext (by omega); rfl)
theorem vF {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (z:Fin m×Bool):qx wire z<v*(2*e+1):=LoosePathStructure.yX wire z
theorem yu {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):Function.Injective (qx wire):=by
 intro x y hh
 have hb:=LoosePathStructure.z1
  (LoosePathStructure.vt (wire x).2.isLt) (LoosePathStructure.vt (wire y).2.isLt) hh
 apply wire.injective
 exact Prod.ext (Fin.ext hb.1) (LoosePathStructure.kO he hb.2)
def zb (v e:Nat) {m:Nat} (j:Fin m):Finset Nat:=
 {qG v e (j,false),qG v e (j,true)}
def vm {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (o:S→Bool) (z:S×Bool):Nat:=
 qx wire (z.1.val,Bool.xor z.2 (o z.1))
def q9 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (o:S→Bool) (z:S×Bool):Finset Nat:=
 {qG v e (z.1.val,z.2),vm wire S o z}
theorem uN (v e:Nat) {m:Nat} (j:Fin m):(zb v e j).card=2:=by
 have hne:qG v e (j,false)≠qG v e (j,true):=by
  intro hh
  have ht:=vJ v e m hh
  exact Bool.false_ne_true (congrArg Prod.snd ht)
 simp [zb,hne]
theorem jc {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (o:S→Bool) (z:S×Bool):(q9 wire S o z).card=2:=by
 have hlo:=vF wire (z.1.val,Bool.xor z.2 (o z.1))
 have hhi:=zw v e (z.1.val,z.2)
 have hne:qG v e (z.1.val,z.2)≠vm wire S o z:=by
  unfold vm
  omega
 simp [q9,hne]
theorem kJ {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (o:S→Bool):Function.Injective (vm wire S o):=by
 rintro ⟨i,a⟩ ⟨j,b⟩ hh
 have hp:=yu he wire hh
 have hij:i=j:=Subtype.ext (congrArg Prod.fst hp)
 subst j
 apply Prod.ext
 · rfl
 · have hb:=congrArg (fun z:Fin m×Bool=>z.2) hp
   cases a <;> cases b <;> cases ho:o i <;> simp_all
theorem kB (v e:Nat) {m:Nat} (i j:Fin m) (hij:i≠j):
 Disjoint (zb v e i) (zb v e j):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 simp only [zb,Finset.mem_insert,Finset.mem_singleton] at hx hy
 rcases hx with rfl|rfl <;> rcases hy with h|h
 all_goals exact hij (congrArg Prod.fst (vJ v e m h))
theorem k3 {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (o:S→Bool) (a b:S×Bool) (hab:a≠b):
 Disjoint (q9 wire S o a) (q9 wire S o b):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 simp only [q9,Finset.mem_insert,Finset.mem_singleton] at hx hy
 rcases hx with hx|hx <;> rcases hy with hy|hy
 · have hh:=vJ v e m (hx.symm.trans hy)
   exact hab (Prod.ext (Subtype.ext (congrArg (fun z:Fin m×Bool=>z.1) hh))
    (congrArg (fun z:Fin m×Bool=>z.2) hh))
 · have hhi:=zw v e (a.1.val,a.2)
   have hlo:=vF wire (b.1.val,Bool.xor b.2 (o b.1))
   change x=qx wire (b.1.val,Bool.xor b.2 (o b.1)) at hy
   omega
 · have hhi:=zw v e (b.1.val,b.2)
   have hlo:=vF wire (a.1.val,Bool.xor a.2 (o a.1))
   change x=qx wire (a.1.val,Bool.xor a.2 (o a.1)) at hx
   omega
 · exact hab (kJ he wire S o (hx.symm.trans hy))
def y2 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)):Prop:=
 ∀ z:Fin m×Bool,z.1∈S→ka r (wire z).1=qx wire z
theorem vP {v e m:Nat} (r:Fin v→Fin (2*e+1))
 (it:Fin v×Fin e) (j:Fin m):Disjoint (z5 r it) (zb v e j):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 have hlo:=y8 r it hx
 simp only [zb,Finset.mem_insert,Finset.mem_singleton] at hy
 rcases hy with rfl|rfl
 · have:=zw v e (j,false); omega
 · have:=zw v e (j,true); omega
theorem yj {v e m:Nat}
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (hpin:y2 wire S r)
 (it:Fin v×Fin e) (z:S×Bool):
 Disjoint (z5 r it) (q9 wire S o z):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 simp only [q9,Finset.mem_insert,Finset.mem_singleton] at hy
 rcases hy with rfl|rfl
 · have hlo:=y8 r it hx
   have:=zw v e (z.1.val,z.2)
   omega
 · have hp:=hpin (z.1.val,Bool.xor z.2 (o z.1)) z.1.property
   change qx wire (z.1.val,Bool.xor z.2 (o z.1))∈z5 r it at hx
   rw [← hp] at hx
   exact uT r _ it hx
theorem vE {v e m:Nat}
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (o:S→Bool) (j:Fin m) (hj:j∉S) (z:S×Bool):
 Disjoint (zb v e j) (q9 wire S o z):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 simp only [zb,q9,Finset.mem_insert,Finset.mem_singleton] at hx hy
 rcases hy with hy|hy
 · rcases hx with hx|hx
   all_goals
    have hh:=vJ v e m (hx.symm.trans hy)
    have he:j=z.1.val:=congrArg (fun z:Fin m×Bool=>z.1) hh
    exact hj (he ▸ z.1.property)
 · have hlo:=vF wire (z.1.val,Bool.xor z.2 (o z.1))
   change x=qx wire (z.1.val,Bool.xor z.2 (o z.1)) at hy
   rcases hx with hx|hx
   · have:=zw v e (j,false); omega
   · have:=zw v e (j,true); omega
def zu (v e m:Nat) (S:Finset (Fin m)):=
 (Fin v×Fin e) ⊕ ({j:Fin m // j∉S} ⊕ (S×Bool))
def ze {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool):zu v e m S→Finset Nat:=
 Sum.elim (z5 r) (Sum.elim (fun j=>zb v e j.val) (q9 wire S o))
theorem jK {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (i:zu v e m S):
 (ze wire S r o i).card=2:=by
 rcases i with i|i
 · exact k1 r i
 · rcases i with i|i
   · exact uN v e i.val
   · exact jc wire S o i
theorem uA {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (hpin:y2 wire S r)
 (a b:zu v e m S) (hab:a≠b):
 Disjoint (ze wire S r o a) (ze wire S r o b):=by
 rcases a with a|a <;> rcases b with b|b
 · exact uQ r a b (fun h=>hab (congrArg Sum.inl h))
 · rcases b with b|b
   · exact vP r a b.val
   · exact yj wire S r o hpin a b
 · rcases a with a|a
   · exact (vP r b a.val).symm
   · exact (yj wire S r o hpin b a).symm
 · rcases a with a|a <;> rcases b with b|b
   · exact kB v e a.val b.val
      (fun h=>hab (congrArg (fun j=>Sum.inr (Sum.inl j)) (Subtype.ext h)))
   · exact vE wire S o a.val a.property b
   · exact (vE wire S o b.val b.property a).symm
   · exact k3 he wire S o a b
      (fun h=>hab (congrArg (fun j=>Sum.inr (Sum.inr j)) h))
theorem jn {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool)
 (i:zu v e m S) {x:Nat} (hx:x∈ze wire S r o i):
 x<v*(2*e+1)+2*m:=by
 rcases i with i|i
 · have:=y8 r i hx; omega
 · rcases i with i|i
   · change x∈zb v e i.val at hx
     simp only [zb,Finset.mem_insert,Finset.mem_singleton] at hx
     rcases hx with rfl|rfl
     · exact yV v e _
     · exact yV v e _
   · change x∈q9 wire S o i at hx
     simp only [q9,Finset.mem_insert,Finset.mem_singleton] at hx
     rcases hx with rfl|rfl
     · exact yV v e _
     · have:=vF wire (i.1.val,Bool.xor i.2 (o i.1)); exact lt_of_lt_of_le this (by omega)
noncomputable instance pairIndexFintype (v e m:Nat) (S:Finset (Fin m)):
 Fintype (zu v e m S):=by
 classical
 unfold zu
 infer_instance
theorem jP (v e m:Nat) (S:Finset (Fin m)):
 Fintype.card (zu v e m S)=v*e+m+S.card:=by
 classical
 have hs:S.card≤m:=by simpa using Finset.card_le_card (Finset.subset_univ S)
 change Fintype.card ((Fin v×Fin e) ⊕ ({j:Fin m // j∉S} ⊕ (S×Bool)))=_
 simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
  Fintype.card_coe,Fintype.card_subtype_compl]
 omega
theorem qaw (v e m:Nat) (S:Finset (Fin m)):
 v*(2*e+1)+2*m-2*Fintype.card (zu v e m S)=v-2*S.card:=by
 rw [jP]
 have he:v*(2*e+1)+2*m=(2*(v*e+m))+v:=by ring
 rw [he]
 omega
end qO
namespace z2
open Finset
def vK {α:Type*} [DecidableEq α] (P:α→α) (R:Finset α):Prop:=
 ∃ z,z∈R∧P z∈R∧P z≠z
theorem kK {α:Type*} [DecidableEq α] (P:α→α)
 (hP:Function.Involutive P) (u v x:α) (hn:P u≠v)
 (hh:vK P {u,v,x}):P x=u∨P x=v:=by
 have hn':P v≠u:=by
  intro h
  have he:=congrArg P h
  rw [hP] at he
  exact hn he.symm
 obtain ⟨z,hz,hpz,hne⟩:=hh
 simp only [mem_insert,mem_singleton] at hz hpz
 rcases hz with rfl|rfl|rfl
 · rcases hpz with h|h|h
   · exact (hne h).elim
   · exact (hn h).elim
   · left; rw [←h,hP]
 · rcases hpz with h|h|h
   · exact (hn' h).elim
   · exact (hne h).elim
   · right; rw [←h,hP]
 · rcases hpz with h|h|h
   · exact Or.inl h
   · exact Or.inr h
   · exact (hne h).elim
theorem qaH {α:Type*} [DecidableEq α] (P:α→α)
 (hP:Function.Involutive P) (u v x y:α) (hxy:x≠y)
 (hx:vK P {u,v,x}) (hy:vK P {u,v,y}):
 P u=v∨(P u=x∧P v=y)∨(P u=y∧P v=x):=by
 by_cases hn:P u=v
 · exact Or.inl hn
 right
 have hx':=kK P hP u v x hn hx
 have hy':=kK P hP u v y hn hy
 have hne:P x≠P y:=fun h=>hxy (hP.injective h)
 rcases hx' with hx'|hx' <;> rcases hy' with hy'|hy'
 · exact (hne (hx'.trans hy'.symm)).elim
 · left; exact ⟨by rw [←hx',hP],by rw [←hy',hP]⟩
 · right; exact ⟨by rw [←hy',hP],by rw [←hx',hP]⟩
 · exact (hne (hx'.trans hy'.symm)).elim
end z2
namespace qX
def zF {k:Nat} (P:Equiv.Perm (Fin k)) (x:Nat):Nat:=
 if hx:x < k then (P ⟨x,hx⟩).val else x
theorem zZ {k:Nat} (P:Equiv.Perm (Fin k)) (x:Fin k):
 zF P x.val=(P x).val:=by
 simp [zF,x.isLt]
theorem jt {k:Nat} (P:Equiv.Perm (Fin k))
 (hP:Function.Involutive P):Function.Involutive (zF P):=by
 intro x
 by_cases hx:x < k
 · let z:Fin k:=⟨x,hx⟩
   change zF P (zF P z.val)=z.val
   rw [zZ,zZ,hP]
 · simp [zF,hx]
def vf (p:Nat→Nat) (δ x:Nat):Nat:=
 if δ≤p (δ+x) then p (δ+x)-δ else x
theorem u7 (p:Nat→Nat) (hp:Function.Involutive p) (δ:Nat):
 Function.Involutive (vf p δ):=by
 intro x
 by_cases hx:δ≤p (δ+x)
 · have hsub:δ+(p (δ+x)-δ)=p (δ+x):=by omega
   simp only [vf,if_pos hx]
   rw [hsub,hp]
   simp
 · simp [vf,hx]
theorem k2 (p:Nat→Nat) (δ x y:Nat) (h:p (δ+x)=δ+y):
 vf p δ x=y:=by
 simp [vf,h]
theorem we (p:Nat→Nat) (δ x y:Nat)
 (hne:y≠x) (h:vf p δ x=y):p (δ+x)=δ+y:=by
 unfold vf at h
 split_ifs at h with hx
 · omega
 · exact False.elim (hne h.symm)
theorem j0 (p:Nat→Nat) (δ x:Nat) (h:p (δ+x) < δ):
 vf p δ x=x:=by
 simp [vf,show ¬δ≤p (δ+x) by omega]
end qX
namespace qr
open Finset
theorem kd (p:Nat→Nat) (t:Nat) (A B:Finset Nat)
 (hA:A⊆qT t) (hB:B⊆qT t) (hcA:A.card=2) (hcB:B.card=2)
 (hpA:q8 p A) (hpB:q8 p B):A=B:=by
 classical
 have hex:∃ x,x∈A∧x∈B:=by
  by_contra! hn
  have hd:Disjoint A B:=disjoint_left.mpr (fun x ha hb=>hn x ha hb)
  have hh:(A ∪ B).card≤(qT t).card:=card_le_card (union_subset hA hB)
  rw [card_union_of_disjoint hd,hcA,hcB] at hh
  have htr:(qT t).card=3:=by simp [qT]
  omega
 obtain ⟨x,hxA,hxB⟩:=hex
 have ha:=hpA x hxA
 have hb:=hpB x hxB
 have hpa:({x,p x}:Finset Nat)=A:=by
  apply eq_of_subset_of_card_le
  · exact insert_subset_iff.mpr ⟨hxA,singleton_subset_iff.mpr ha.1⟩
  · rw [hcA,card_pair (Ne.symm ha.2)]
 have hpb:({x,p x}:Finset Nat)=B:=by
  apply eq_of_subset_of_card_le
  · exact insert_subset_iff.mpr ⟨hxB,singleton_subset_iff.mpr hb.1⟩
  · rw [hcB,card_pair (Ne.symm hb.2)]
 exact hpa.symm.trans hpb
theorem kF (e r s:Nat) (hr:r≤2*e) (hs:s≤2*e)
 (p:Nat→Nat) (hpr:∀ t<e,q8 p (qE r t))
 (hps:∀ t<e,q8 p (qE s t)):r=s:=by
 apply yE e (qE r) r s hr hs
 · exact yi e r hr
 · intro t ht
   exact kd p t _ _ (zR r t) (zR s t)
    (vO r t) (vO s t) (hpr t ht) (hps t ht)
end qr
namespace qX
open Finset qr
theorem kW (e δ:Nat) (p:Nat→Nat) (hp:Function.Involutive p)
 (hw:∀ t<e,∃ x,x∈(qT t).image (fun y=>δ+y)∧
   p x∈(qT t).image (fun y=>δ+y)∧p x≠x):
 ∃ r,r≤2*e∧∀ t<e,q8 p ((qE r t).image (fun y=>δ+y)):=by
 have hw':∀ t<e,∃ x,x∈qT t∧vf p δ x∈qT t∧vf p δ x≠x:=by
  intro t ht
  obtain ⟨z,hz,hpz,hne⟩:=hw t ht
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hz
  obtain ⟨y,hy,hyz⟩:=mem_image.mp hpz
  have hs:=k2 p δ x y hyz.symm
  exact ⟨x,hx,by rw [hs]; exact hy,by rw [hs]; omega⟩
 obtain ⟨r,hr,hpr⟩:=w9 e (vf p δ) (u7 p hp δ) hw'
 refine ⟨r,hr,?_⟩
 intro t ht z hz
 obtain ⟨x,hx,rfl⟩:=mem_image.mp hz
 obtain ⟨hy,hne⟩:=hpr t ht x hx
 have hpair:=we p δ x (vf p δ x) hne rfl
 exact ⟨mem_image.mpr ⟨vf p δ x,hy,hpair.symm⟩,by omega⟩
theorem ju (e δ r:Nat) (hr:r≤2*e) (p:Nat→Nat)
 (hpr:∀ t<e,q8 p ((qE r t).image (fun y=>δ+y)))
 (x:Nat) (hx:x<2*e+1)
 (hout:p (δ+x)<δ∨δ+(2*e+1)≤p (δ+x)):x=r:=by
 by_contra hne
 have hm:x∈(range e).biUnion (qE r):=by
  rw [yi e r hr]
  exact mem_sdiff.mpr ⟨mem_range.mpr hx,by simpa using hne⟩
 obtain ⟨t,ht,hxt⟩:=mem_biUnion.mp hm
 have ht':=mem_range.mp ht
 have hglob:δ+x∈(qE r t).image (fun y=>δ+y):=mem_image.mpr ⟨x,hxt,rfl⟩
 obtain ⟨y,hy,hyz⟩:=mem_image.mp (hpr t ht' (δ+x) hglob).1
 have hyt:=zR r t hy
 simp only [qT,mem_insert,mem_singleton] at hyt
 omega
end qX
namespace vv
open Finset qO qr LoosePathStructure qX z2
theorem uI {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m))
 (p:Nat→Nat) (hp:Function.Involutive p)
 (hpath:∀ i:Fin v,∀ t:Fin e,vK p (qF e (i.val,t.val)))
 (hswitch:∀ z:Fin m×Bool,vK p (qn v e m wire z))
 (hactive:∀ j:Fin m,j∈S↔p (qG v e (j,false))≠qG v e (j,true)):
 ∃ r:Fin v→Fin (2*e+1),∃ o:S→Bool,
   y2 wire S r∧∀ i:zu v e m S,q8 p (ze wire S r o i):=by
 classical
 have hroots (i:Fin v):∃ r:Fin (2*e+1),
  ∀ t:Fin e,q8 p ((qE r.val t.val).image (fun x=>i.val*(2*e+1)+x)):=by
  have hw:∀ t<e,∃ x,x∈(qT t).image (fun y=>i.val*(2*e+1)+y)∧
   p x∈(qT t).image (fun y=>i.val*(2*e+1)+y)∧p x≠x:=by
   intro t ht
   have h:=hpath i ⟨t,ht⟩
   simpa [vK,qF,qT,Nat.add_assoc] using h
  obtain ⟨r,hr,hpr⟩:=kW e (i.val*(2*e+1)) p hp hw
  exact ⟨⟨r,by omega⟩,fun t=>hpr t.val t.isLt⟩
 choose r hr using hroots
 have hsw (z:Fin m×Bool):vK p {qG v e (z.1,false),qG v e (z.1,true),qx wire z}:=by
  simpa [qn,qG,qx] using hswitch z
 have hpin:y2 wire S r:=by
  intro z hz
  have hpz:=kK p hp (qG v e (z.1,false)) (qG v e (z.1,true))
   (qx wire z) ((hactive z.1).mp hz) (hsw z)
  have hlim:(wire z).1.val*(2*e+1)+(2*e+1)≤v*(2*e+1):=by
   have:=(wire z).1.isLt
   nlinarith
  have hrt:leaf e (wire z).2.val=(r (wire z).1).val:=by
   apply ju e ((wire z).1.val*(2*e+1)) (r (wire z).1).val
    (by have:=(r (wire z).1).isLt; omega) p
    (fun t ht=>hr (wire z).1 ⟨t,ht⟩) _ (vt (wire z).2.isLt)
   right
   have h1:=zw v e (z.1,false)
   have h2:=zw v e (z.1,true)
   dsimp only [qx] at hpz
   omega
  dsimp only [ka,qx]
  rw [hrt]
 have horient (j:S):∃ o:Bool,∀ b:Bool,
  p (qG v e (j.val,b))=qx wire (j.val,Bool.xor b o):=by
  have hxy:qx wire (j.val,false)≠qx wire (j.val,true):=by
   intro h
   have hh:=qO.yu he wire h
   have:=congrArg Prod.snd hh
   simp at this
  have hc:=qaH p hp (qG v e (j.val,false)) (qG v e (j.val,true))
   (qx wire (j.val,false)) (qx wire (j.val,true)) hxy (hsw (j.val,false)) (hsw (j.val,true))
  rcases hc with hc | hc | hc
  · exact False.elim (((hactive j.val).mp j.property) hc)
  · refine ⟨false,?_⟩
    intro b
    cases b
    · simpa using hc.1
    · simpa using hc.2
  · refine ⟨true,?_⟩
    intro b
    cases b
    · simpa using hc.1
    · simpa using hc.2
 choose o ho using horient
 refine ⟨r,o,hpin,?_⟩
 intro i
 rcases i with i | i
 · exact hr i.1 i.2
 · rcases i with j | z
   · have hpj:p (qG v e (j.val,false))=qG v e (j.val,true):=by
      by_contra h
      exact j.property ((hactive j.val).mpr h)
     have hne:p (qG v e (j.val,false))≠qG v e (j.val,false):=by
      rw [hpj]
      simp [qG]
     have hh:=y7 p hp (qG v e (j.val,false)) hne
     simpa [ze,zb,hpj] using hh
   · have hpz:p (qG v e (z.1.val,z.2))=vm wire S o z:=ho z.1 z.2
     have hne:p (qG v e (z.1.val,z.2))≠qG v e (z.1.val,z.2):=by
      rw [hpz]
      have hl:=vF wire (z.1.val,Bool.xor z.2 (o z.1))
      have hh:=zw v e (z.1.val,z.2)
      dsimp only [vm]
      omega
     have hh:=y7 p hp (qG v e (z.1.val,z.2)) hne
     simpa [ze,q9,hpz] using hh
theorem v7 (p:Nat→Nat) (δ:Nat) (A:Finset Nat)
 (h:q8 p (A.image (fun y=>δ+y))):q8 (vf p δ) A:=by
 intro x hx
 have hh:=h (δ+x) (mem_image.mpr ⟨x,hx,rfl⟩)
 obtain ⟨y,hy,hyx⟩:=mem_image.mp hh.1
 have hs:=k2 p δ x y hyx.symm
 exact ⟨by rw [hs]; exact hy,by rw [hs]; have:=hh.2; omega⟩
theorem uP {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m))
 (p:Nat→Nat) (r s:Fin v→Fin (2*e+1)) (o u:S→Bool)
 (hr:∀ i:zu v e m S,q8 p (ze wire S r o i))
 (hs:∀ i:zu v e m S,q8 p (ze wire S s u i)):r=s∧o=u:=by
 have hrs:r=s:=by
  funext i
  apply Fin.ext
  apply kF e (r i).val (s i).val
   (by have:=(r i).isLt; omega) (by have:=(s i).isLt; omega) (vf p (i.val*(2*e+1)))
  · intro t ht
    exact v7 p _ _ (hr (Sum.inl (i,⟨t,ht⟩)))
  · intro t ht
    exact v7 p _ _ (hs (Sum.inl (i,⟨t,ht⟩)))
 refine ⟨hrs,?_⟩
 funext j
 have hro:=hr (Sum.inr (Sum.inr (j,false)))
 have hsu:=hs (Sum.inr (Sum.inr (j,false)))
 have get (o:S→Bool) (hh:q8 p (q9 wire S o (j,false))):
  p (qG v e (j.val,false))=qx wire (j.val,o j):=by
  have ha:=hh (qG v e (j.val,false)) (by simp [q9])
  simp only [q9,mem_insert,mem_singleton] at ha
  rcases ha.1 with h | h
  · exact (ha.2 h).elim
  · simpa [vm] using h
 have hpo:=get o hro
 have hpu:=get u hsu
 have hz:=qO.yu he wire (hpo.symm.trans hpu)
 exact congrArg Prod.snd hz
end vv
namespace vw
open Finset
noncomputable def uy {X Y:Type*} [DecidableEq X]
 (C:Finset X) (g:X→Y):
 {r:X→Y // ∀ i∈C,r i=g i} ≃ ({i:X // i∉C}→Y):=by
 classical
 exact {
  toFun:=fun r i=>r.val i.val
  invFun:=fun f=>⟨fun i=>if hi:i∈C then g i else f ⟨i,hi⟩,
   by intro i hi; simp [hi]⟩
  left_inv:=by
   intro r
   apply Subtype.ext
   funext i
   by_cases hi:i∈C
   · simp only [dif_pos hi]
     exact (r.property i hi).symm
   · simp [hi]
  right_inv:=by
   intro f
   funext i
   simp [i.property]
 }
theorem yl {X Y:Type*} [Fintype X] [Fintype Y] [DecidableEq X]
 (C:Finset X) (g:X→Y):
 Nat.card {r:X→Y // ∀ i∈C,r i=g i}=
  Nat.card Y ^ (Fintype.card X - C.card):=by
 classical
 rw [Nat.card_congr (uy C g)]
 rw [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_subtype_compl,
  Fintype.card_coe,Nat.card_eq_fintype_card]
theorem wJ {v m:Nat} (S:Finset (Fin m)) (wire:Fin m×Bool→Fin v)
 (hcard:((S ×ˢ (univ:Finset Bool)).image wire).card=2*S.card):
 Set.InjOn wire (↑(S ×ˢ (univ:Finset Bool)):Set (Fin m×Bool)):=by
 apply (card_image_iff).mp
 rw [card_product,card_univ,Fintype.card_bool]
 omega
theorem j7 {v m:Nat} (S:Finset (Fin m)) (wire:Fin m×Bool→Fin v)
 (h:Set.InjOn wire (↑(S ×ˢ (univ:Finset Bool)):Set (Fin m×Bool))):
 ((S ×ˢ (univ:Finset Bool)).image wire).card=2*S.card:=by
 rw [card_image_of_injOn h,card_product,card_univ,Fintype.card_bool]
 omega
theorem qa1 {v q:Nat} (C:Finset (Fin v)) (g:Fin v→Fin q):
 Nat.card {r:Fin v→Fin q // ∀ i∈C,r i=g i}=q^(v-C.card):=by
 simpa using yl C g
theorem yR {A X Y:Type*} [Fintype X] [Fintype Y]
 [DecidableEq A] [DecidableEq X] (T:Finset A) (f:A→X) (h:A→Y)
 (hf:Set.InjOn f (↑T:Set A)) (y0:Y):
 Nat.card {r:X→Y // ∀ a∈T,r (f a)=h a}=
  Nat.card Y ^ (Fintype.card X - T.card):=by
 classical
 let f':T→X:=fun a=>f a.val
 have hf':Function.Injective f':=by
  intro a b hab
  exact Subtype.ext (hf a.property b.property hab)
 let h':T→Y:=fun a=>h a.val
 let g:X→Y:=Function.extend f' h' (fun _=>y0)
 have hg (a:A) (ha:a∈T):g (f a)=h a:=hf'.extend_apply h' _ ⟨a,ha⟩
 have heq (r:X→Y):(∀ a∈T,r (f a)=h a)↔
  (∀ x∈T.image f,r x=g x):=by
  constructor
  · intro hr x hx
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hx
    rw [hr a ha,hg a ha]
  · intro hr a ha
    rw [hr (f a) (mem_image.mpr ⟨a,ha,rfl⟩),hg a ha]
 rw [Nat.card_congr (Equiv.subtypeEquivRight heq),yl,
  card_image_of_injOn hf]
theorem ky {v m q:Nat} (hq:0 < q) (S:Finset (Fin m))
 (endpt:Fin m×Bool→Fin v) (qx:Fin m×Bool→Fin q)
 (hc:((S ×ˢ (univ:Finset Bool)).image endpt).card=2*S.card):
 Nat.card ((S→Bool)×{r:Fin v→Fin q //
  ∀ z∈S ×ˢ (univ:Finset Bool),r (endpt z)=qx z})=
  2^S.card * q^(v-2*S.card):=by
 classical
 rw [Nat.card_prod]
 have hh:=yR (S ×ˢ (univ:Finset Bool)) endpt qx
  (wJ S endpt hc) (⟨0,hq⟩:Fin q)
 simp only [Nat.card_eq_fintype_card,Fintype.card_fin,card_product,
  card_univ,Fintype.card_bool] at hh
 simp only [Nat.card_eq_fintype_card]
 rw [hh]
 simp [Nat.card_eq_fintype_card,Fintype.card_fun,Nat.mul_comm]
theorem kz {A X Y:Type*} [DecidableEq A]
 (T:Finset A) (endpt:A→X) (qx:A→Y)
 (hp:Function.Injective (fun a=>(endpt a,qx a)))
 (r:X→Y) (hr:∀ a∈T,r (endpt a)=qx a):
 Set.InjOn endpt (↑T:Set A):=by
 intro a ha b hb hab
 apply hp
 refine Prod.ext hab ?_
 dsimp only
 rw [← hr a ha,← hr b hb,hab]
theorem ks {v m q:Nat} (S:Finset (Fin m))
 (endpt:Fin m×Bool→Fin v) (qx:Fin m×Bool→Fin q)
 (hp:Function.Injective (fun a=>(endpt a,qx a)))
 (r:Fin v→Fin q) (hr:∀ a∈S ×ˢ (univ:Finset Bool),r (endpt a)=qx a):
 ((S ×ˢ (univ:Finset Bool)).image endpt).card=2*S.card:=
 j7 S endpt (kz _ endpt qx hp r hr)
end vw
namespace z8
open Finset qO
def vK (p:Nat→Nat) (A:Finset Nat):Prop:=∃ x,x∈A∧p x∈A∧p x≠x
theorem jL (p:Nat→Nat) (A B:Finset Nat)
 (hc:A.card=2) (hp:qr.q8 p A) (hs:A⊆B):vK p B:=by
 have hne:A.Nonempty:=Finset.card_pos.mp (by omega)
 obtain ⟨x,hx⟩:=hne
 exact ⟨x,hs hx,hs (hp x hx).1,(hp x hx).2⟩
theorem jv {v e:Nat} (r:Fin v→Fin (2*e+1)) (it:Fin v×Fin e):
 z5 r it⊆LoosePathStructure.qF e (it.1.val,it.2.val):=by
 intro x hx
 obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
 have hh:=qr.zR _ _ hy
 simp only [qr.qT,Finset.mem_insert,Finset.mem_singleton] at hh
 rcases hh with rfl|rfl|rfl <;> simp [LoosePathStructure.qF,Nat.add_assoc]
theorem uB (p:Nat→Nat) (a b:Nat)
 (hp:qr.q8 p {a,b}):p a=b:=by
 have hh:=hp a (by simp)
 simp only [Finset.mem_insert,Finset.mem_singleton] at hh
 exact hh.1.resolve_left hh.2
theorem k9 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (p:Nat→Nat)
 (hp:∀ i,qr.q8 p (ze wire S r o i))
 (j:Fin m) (hj:j∈S) (b:Bool):
 p (qG v e (j,b))=qx wire (j,Bool.xor b (o ⟨j,hj⟩)):=by
 exact uB p _ _ (hp (Sum.inr (Sum.inr (⟨j,hj⟩,b))))
theorem kC {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (p:Nat→Nat)
 (hp:∀ i,qr.q8 p (ze wire S r o i))
 (j:Fin m) (hj:j∉S):p (qG v e (j,false))=qG v e (j,true):=by
 exact uB p _ _ (hp (Sum.inr (Sum.inl ⟨j,hj⟩)))
theorem kL {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (p:Nat→Nat)
 (hp:∀ i,qr.q8 p (ze wire S r o i)) (j:Fin m):
 j∈S↔p (qG v e (j,false))≠qG v e (j,true):=by
 constructor
 · intro hj
   rw [k9 wire S r o p hp j hj false]
   have hlo:=vF wire (j,Bool.xor false (o ⟨j,hj⟩))
   have hhi:=zw v e (j,true)
   omega
 · intro hh
   by_contra hj
   exact hh (kC wire S r o p hp j hj)
theorem qaS {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (p:Nat→Nat)
 (hp:∀ i,qr.q8 p (ze wire S r o i)) (it:Fin v×Fin e):
 vK p (LoosePathStructure.qF e (it.1.val,it.2.val)):=
 jL p _ _ (k1 r it) (hp (Sum.inl it)) (jv r it)
theorem qaq {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool) (p:Nat→Nat)
 (hp:∀ i,qr.q8 p (ze wire S r o i)) (z:Fin m×Bool):
 vK p (LoosePathStructure.qn v e m wire z):=by
 classical
 rcases z with ⟨j,c⟩
 by_cases hj:j∈S
 · let b:=Bool.xor c (o ⟨j,hj⟩)
   have hb:Bool.xor b (o ⟨j,hj⟩)=c:=by
    dsimp [b]
    cases c <;> cases o ⟨j,hj⟩ <;> rfl
   have he:=k9 wire S r o p hp j hj b
   rw [hb] at he
   refine ⟨qG v e (j,b),?_,?_,?_⟩
   · cases b <;> simp [qG,LoosePathStructure.qn]
   · rw [he]
     simp [qx,LoosePathStructure.qn]
   · rw [he]
     have hlo:=vF wire (j,c)
     have hhi:=zw v e (j,b)
     omega
 · have he:=kC wire S r o p hp j hj
   refine ⟨qG v e (j,false),?_,?_,?_⟩
   · simp [qG,LoosePathStructure.qn]
   · rw [he]
     simp [qG,LoosePathStructure.qn]
   · rw [he]
     simp [qG]
end z8
namespace z7
open Finset qX z2 qO
theorem u5 {k:Nat} (P:Equiv.Perm (Fin k)) (R:Finset Nat)
 (hb:∀ x∈R,x<k):
 (∃ i:Fin k,i.val∈R∧(P i).val∈R∧P i≠i)↔vK (zF P) R:=by
 constructor
 · rintro ⟨i,hi,hpi,hne⟩
   refine ⟨i.val,hi,?_,?_⟩
   · rw [zZ]; exact hpi
   · rw [zZ]
     exact fun h=>hne (Fin.ext h)
 · rintro ⟨x,hx,hpx,hne⟩
   let i:Fin k:=⟨x,hb x hx⟩
   have heq:zF P x=(P i).val:=zZ P i
   refine ⟨i,hx,?_,?_⟩
   · rw [←heq]; exact hpx
   · intro h
     apply hne
     rw [heq,h]
 theorem kL {v e m:Nat} (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))) (j:Fin m):
  (¬ ∃ i:Fin (v*(2*e+1)+2*m),i.val=v*(2*e+1)+2*j.val∧
    (P i).val=v*(2*e+1)+2*j.val+1)↔
  zF P (qG v e (j,false))≠qG v e (j,true):=by
  have hfalse:qG v e (j,false)=v*(2*e+1)+2*j.val:=by simp [qG]
  have htrue:qG v e (j,true)=v*(2*e+1)+2*j.val+1:=by simp [qG]
  constructor
  · intro h hn
    let i:Fin (v*(2*e+1)+2*m):=⟨qG v e (j,false),yV v e (j,false)⟩
    apply h
    refine ⟨i,hfalse,?_⟩
    have hn':zF P i.val=qG v e (j,true):=hn
    rw [zZ,htrue] at hn'
    exact hn'
  · intro h ⟨i,hi,hpi⟩
    apply h
    have hii:i.val=qG v e (j,false):=hi.trans hfalse.symm
    rw [←hii,zZ,hpi,htrue]
end z7
namespace y3
noncomputable def qam {α β:Type*} (W:α→Prop) (R:β→α→Prop)
 (exists_unique:∀ a,W a→∃! b,R b a)
 (sound:∀ b a,R b a→W a):
 {a // W a} ≃ (b:β)×{a // R b a}:=by
 let forget:((b:β)×{a // R b a})→{a // W a}:=
  fun x=>⟨x.2.val,sound x.1 x.2.val x.2.property⟩
 have hi:Function.Injective forget:=by
  rintro ⟨b,⟨a,ha⟩⟩ ⟨c,⟨a',ha'⟩⟩ he
  have haa:a=a':=congrArg Subtype.val he
  subst a'
  have hbc:b=c:=(exists_unique a (sound b a ha)).unique ha ha'
  subst c
  rfl
 have hs:Function.Surjective forget:=by
  intro a
  obtain ⟨b,hb,huniq⟩:=exists_unique a a.property
  exact ⟨⟨b,⟨a.val,hb⟩⟩,rfl⟩
 exact (Equiv.ofBijective forget ⟨hi,hs⟩).symm
theorem j1 {α β:Type*} (W:α→Prop) (R:β→α→Prop)
 (exists_unique:∀ a,W a→∃! b,R b a)
 (sound:∀ b a,R b a→W a):
 Nat.card {a // W a}=Nat.card ((b:β)×{a // R b a}):=
 Nat.card_congr (qam W R exists_unique sound)
theorem qae {α β:Type*} [Fintype β] (W:α→Prop) (R:β→α→Prop)
 [∀ b,Finite {a // R b a}]
 (exists_unique:∀ a,W a→∃! b,R b a)
 (sound:∀ b a,R b a→W a):
 Nat.card {a // W a}=∑ b,Nat.card {a // R b a}:=by
 rw [j1 W R exists_unique sound,Nat.card_sigma]
end y3
namespace zT
open Finset qO qX z2
def zY {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)):=(S→Bool)×{r:Fin v→Fin (2*e+1) // y2 wire S r}
def yJ {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (z:Fin m×Bool):Fin (2*e+1):=
 ⟨LoosePathStructure.leaf e (wire z).2.val,LoosePathStructure.vt (wire z).2.isLt⟩
theorem jx {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)):
 y2 wire S r↔∀ z∈S ×ˢ (Finset.univ:Finset Bool),r (wire z).1=yJ wire z:=by
 constructor
 · intro hp z hz
   apply Fin.ext
   exact Nat.add_left_cancel (hp z (Finset.mem_product.mp hz).1)
 · intro hp z hz
   have hh:=congrArg Fin.val (hp z (Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩))
   exact congrArg (fun x=>(wire z).1.val*(2*e+1)+x) hh
theorem k6 {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):
 Function.Injective (fun z=>((wire z).1,yJ wire z)):=by
 intro x y hh
 apply wire.injective
 apply Prod.ext
 · exact congrArg (fun z:Fin v×Fin (2*e+1)=>z.1) hh
 · apply LoosePathStructure.kO he
   exact congrArg (fun z:Fin v×Fin (2*e+1)=>z.2.val) hh
noncomputable def jQ {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)):zY wire S ≃
   ((S→Bool)×{r:Fin v→Fin (2*e+1) //
     ∀ z∈S ×ˢ (Finset.univ:Finset Bool),r (wire z).1=yJ wire z}):=
 Equiv.prodCongr (Equiv.refl _) (Equiv.subtypeEquivRight (jx wire S))
theorem jR {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m)):
 Nat.card (zY wire S)=
  if ((S ×ˢ (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)).card=2*S.card
  then 2^S.card * (2*e+1)^(v-2*S.card) else 0:=by
 classical
 by_cases hc:((S ×ˢ (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)).card=2*S.card
 · rw [if_pos hc,Nat.card_congr (jQ wire S)]
   exact vw.ky (by omega) S (fun z=>(wire z).1) (yJ wire) hc
 · rw [if_neg hc]
   haveI:IsEmpty (zY wire S):=⟨fun b=>hc
    (vw.ks S (fun z=>(wire z).1) (yJ wire)
      (k6 he wire) b.2.val ((jx wire S b.2.val).mp b.2.property))⟩
   simp
def wx {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):Prop:=
 Function.Involutive P∧
 (∀ i:Fin v,∀ t:Fin e,vK (zF P) (LoosePathStructure.qF e (i.val,t.val)))∧
 (∀ z:Fin m×Bool,vK (zF P) (LoosePathStructure.qn v e m wire z))∧
 ∀ j:Fin m,j∈S↔zF P (qG v e (j,false))≠qG v e (j,true)
def qZ {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (S:Finset (Fin m)) (b:zY wire S)
    (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):Prop:=
 Function.Involutive P∧∀ i:zu v e m S,
  qr.q8 (zF P) (ze wire S b.2.val b.1 i)
theorem qan {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m))
 (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))) (hP:wx wire S P):
 ∃! b:zY wire S,qZ wire S b P:=by
 obtain ⟨hInv,hpath,hswitch,hactive⟩:=hP
 obtain ⟨r,o,hpin,hpairs⟩:=vv.uI he wire S (zF P)
  (jt P hInv) hpath hswitch hactive
 refine ⟨⟨o,⟨r,hpin⟩⟩,⟨hInv,hpairs⟩,?_⟩
 intro b hb
 obtain ⟨hr,ho⟩:=vv.uP he wire S (zF P)
  b.2.val r b.1 o hb.2 hpairs
 exact Prod.ext ho (Subtype.ext hr)
theorem wR {v e m:Nat}
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m))
 (b:zY wire S) (P:Equiv.Perm (Fin (v*(2*e+1)+2*m)))
 (hP:qZ wire S b P):wx wire S P:=by
 refine ⟨hP.1,?_,?_,?_⟩
 · intro i t
   exact z8.qaS wire S b.2.val b.1 (zF P) hP.2 (i,t)
 · intro z
   exact z8.qaq wire S b.2.val b.1 (zF P) hP.2 z
 · intro j
   exact z8.kL wire S b.2.val b.1 (zF P) hP.2 j
end zT
namespace qC
open Finset
variable {ι α:Type*} [DecidableEq α]
def zv (I:Finset ι) (f:ι→Finset α):Finset α:=I.biUnion f
def jC (I:Finset ι) (f:ι→Finset α) (x y:α):Prop:=
 ∃ i∈I,x∈f i∧y∈f i∧y≠x
theorem yP (I:Finset ι) (f:ι→Finset α)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 {i j:ι} (hi:i∈I) (hj:j∈I) {x:α} (hx:x∈f i) (hy:x∈f j):i=j:=by
 by_contra h
 exact Finset.disjoint_left.mp (hd i hi j hj h) hx hy
theorem wW (A:Finset α) (hc:A.card=2) (x:α) (hx:x∈A):
 ∃! y,y∈A∧y≠x:=by
 obtain ⟨a,b,hab,rfl⟩:=Finset.card_eq_two.mp hc
 simp only [mem_insert,mem_singleton] at hx
 rcases hx with rfl|rfl
 · refine ⟨b,⟨by simp,Ne.symm hab⟩,?_⟩
   intro y hy
   simp only [mem_insert,mem_singleton] at hy
   exact hy.1.resolve_left hy.2
 · refine ⟨a,⟨by simp,hab⟩,?_⟩
   intro y hy
   simp only [mem_insert,mem_singleton] at hy
   exact hy.1.resolve_right hy.2
theorem yw (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:α) (hx:x∈zv I f):∃! y,jC I f x y:=by
 obtain ⟨i,hi,hxi⟩:=Finset.mem_biUnion.mp hx
 obtain ⟨y,hy,huniq⟩:=wW (f i) (hc i hi) x hxi
 refine ⟨y,⟨i,hi,hxi,hy⟩,?_⟩
 intro z hz
 obtain ⟨j,hj,hxj,hzj,hne⟩:=hz
 have hji:j=i:=(yP I f hd hi hj hxi hxj).symm
 subst j
 exact huniq z ⟨hzj,hne⟩
noncomputable def qo (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f):α:=Classical.choose (yw I f hc hd x x.property)
theorem kj (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f):jC I f x (qo I f hc hd x):=
 (Classical.choose_spec (yw I f hc hd x x.property)).1
theorem qa4 (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f):qo I f hc hd x∈zv I f:=by
 obtain ⟨i,hi,hxi,hyi,hne⟩:=kj I f hc hd x
 exact Finset.mem_biUnion.mpr ⟨i,hi,hyi⟩
theorem qbc (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f):qo I f hc hd x≠x:=by
 obtain ⟨i,hi,hxi,hyi,hne⟩:=kj I f hc hd x
 exact hne
theorem jN (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f) (y:α) (hy:jC I f x y):qo I f hc hd x=y:=by
 exact ((Classical.choose_spec (yw I f hc hd x x.property)).2 y hy).symm
noncomputable def map (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):zv I f→zv I f:=
 fun x=>⟨qo I f hc hd x,qa4 I f hc hd x⟩
theorem kE (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):
 Function.Involutive (map I f hc hd):=by
 intro x
 apply Subtype.ext
 change qo I f hc hd (map I f hc hd x)=x.val
 apply jN
 obtain ⟨i,hi,hxi,hyi,hne⟩:=kj I f hc hd x
 exact ⟨i,hi,hyi,hxi,Ne.symm hne⟩
noncomputable def wZ (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):Equiv.Perm (zv I f):=
 (kE I f hc hd).toPerm
theorem jw (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):
 Function.Involutive (wZ I f hc hd):=kE I f hc hd
theorem wj (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (x:zv I f):wZ I f hc hd x≠x:=by
 intro h
 exact qbc I f hc hd x (congrArg Subtype.val h)
theorem qch (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (i:ι) (hi:i∈I) (x y:α) (hx:x∈f i) (hy:y∈f i) (hne:y≠x):
 (wZ I f hc hd ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩).val=y:=
 jN I f hc hd _ y ⟨i,hi,hx,hy,hne⟩
theorem uE (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):
 (zv I f).card=2*I.card:=by
 rw [zv,Finset.card_biUnion hd]
 calc
  (∑ i∈I,(f i).card)=∑ i∈I,2:=Finset.sum_congr rfl hc
  _=2*I.card:=by simp [Nat.mul_comm]
theorem qa8 [Fintype α] (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):
 Fintype.card {x // x∉zv I f}=Fintype.card α - 2*I.card:=by
 rw [Fintype.card_subtype_compl]
 simp only [Fintype.card_coe,uE I f hc hd]
theorem kp [Fintype α] (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j)):
 (Finset.univ \ zv I f).card=Fintype.card α - 2*I.card:=by
 rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,uE I f hc hd]
end qC
namespace zi
open Finset
def lift (k:Nat) (A:Finset Nat):Finset (Fin k):=
 Finset.univ.filter (fun x=>x.val∈A)
@[simp] theorem zJ {k:Nat} {A:Finset Nat} {x:Fin k}:
 x∈lift k A↔x.val∈A:=by simp [lift]
@[simp] theorem qb6 (k:Nat):lift k ∅=∅:=by ext x; simp
@[simp] theorem qb9 (k:Nat) (A B:Finset Nat):
 lift k (A ∪ B)=lift k A ∪ lift k B:=by ext x; simp
@[simp] theorem qb7 (k:Nat) (A B:Finset Nat):
 lift k (A ∩ B)=lift k A ∩ lift k B:=by ext x; simp
@[simp] theorem qb8 (k:Nat) (A B:Finset Nat):
 lift k (A \ B)=lift k A \ lift k B:=by ext x; simp
theorem qb0 {k:Nat} {A B:Finset Nat} (h:A⊆B):
 lift k A⊆lift k B:=fun _ hx=>zJ.mpr (h (zJ.mp hx))
@[simp] theorem qbF {ι:Type*} (k:Nat) (I:Finset ι) (f:ι→Finset Nat):
 lift k (I.biUnion f)=I.biUnion (fun i=>lift k (f i)):=by ext x; simp
theorem ys (k:Nat) (A:Finset Nat) (hA:∀ x∈A,x<k):
 (lift k A).image Fin.val=A:=by
 ext x
 constructor
 · intro hx
   obtain ⟨y,hy,rfl⟩:=mem_image.mp hx
   exact zJ.mp hy
 · intro hx
   exact mem_image.mpr ⟨⟨x,hA x hx⟩,zJ.mpr hx,rfl⟩
@[simp] theorem qba (k:Nat) (A:Finset (Fin k)):
 lift k (A.image Fin.val)=A:=by
 ext x
 simp only [zJ,mem_image]
 constructor
 · rintro ⟨y,hy,he⟩
   exact (Fin.ext he) ▸ hy
 · intro hx
   exact ⟨x,hx,rfl⟩
theorem qaR (k:Nat) (A:Finset Nat) (hA:∀ x∈A,x<k):
 (lift k A).card=A.card:=by
 calc
  (lift k A).card=((lift k A).image Fin.val).card:=
   (Finset.card_image_of_injective _ Fin.val_injective).symm
  _=A.card:=congrArg Finset.card (ys k A hA)
theorem k0 (k:Nat) (A B:Finset Nat) (h:Disjoint A B):
 Disjoint (lift k A) (lift k B):=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 exact Finset.disjoint_left.mp h (zJ.mp hx) (zJ.mp hy)
theorem u2 (k:Nat) (A B:Finset Nat) (hA:∀x∈A,x<k)
 (h:Disjoint (lift k A) (lift k B)):Disjoint A B:=by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 have hx':(⟨x,hA x hx⟩:Fin k)∈lift k A:=zJ.mpr hx
 have hy':(⟨x,hA x hx⟩:Fin k)∈lift k B:=zJ.mpr hy
 exact Finset.disjoint_left.mp h hx' hy'
theorem qaX (k:Nat) (A B:Finset Nat) (hA:∀x∈A,x<k):
 Disjoint (lift k A) (lift k B)↔Disjoint A B:=
 ⟨u2 k A B hA,k0 k A B⟩
theorem j8 (k:Nat) (A B:Finset Nat)
 (hA:∀x∈A,x<k) (hB:∀x∈B,x<k) (h:lift k A=lift k B):A=B:=by
 rw [←ys k A hA,←ys k B hB,h]
theorem qbZ (k:Nat) (A B:Finset Nat)
 (hA:∀x∈A,x<k) (hB:∀x∈B,x<k):lift k A=lift k B↔A=B:=
 ⟨j8 k A B hA hB,congrArg (lift k)⟩
end zi
namespace zH
abbrev Inv (α:Type*):={P:Equiv.Perm α // Function.Involutive P}
variable {α:Type*} (p:α→Prop) [DecidablePred p]
def vB (q:Inv {x // p x}) (Q:Inv {x // ¬p x}) (x:α):α:=
 if h:p x then q.1 ⟨x,h⟩ else Q.1 ⟨x,h⟩
@[simp] theorem yT (q:Inv {x // p x}) (Q:Inv {x // ¬p x})
 (x:α) (hx:p x):vB p q Q x=(q.1 ⟨x,hx⟩).val:=by
 simp [vB,hx]
@[simp] theorem vI (q:Inv {x // p x}) (Q:Inv {x // ¬p x})
 (x:α) (hx:¬p x):vB p q Q x=(Q.1 ⟨x,hx⟩).val:=by
 simp [vB,hx]
theorem yO (q:Inv {x // p x}) (Q:Inv {x // ¬p x}):
 Function.Involutive (vB p q Q):=by
 intro x
 by_cases hx:p x
 · rw [yT _ _ _ _ hx,yT _ _ _ _ (q.1 ⟨x,hx⟩).property]
   exact congrArg Subtype.val (q.2 ⟨x,hx⟩)
 · rw [vI _ _ _ _ hx,vI _ _ _ _ (Q.1 ⟨x,hx⟩).property]
   exact congrArg Subtype.val (Q.2 ⟨x,hx⟩)
def vG (q:Inv {x // p x}):=
 {P:Equiv.Perm α // Function.Involutive P∧∀ x:{x // p x},P x=(q.1 x).val}
theorem jy (q:Inv {x // p x}) (P:vG p q)
 (x:α) (hx:¬p x):¬p (P.1 x):=by
 intro h
 have he:=P.2.2 ⟨P.1 x,h⟩
 have hz:x=(q.1 ⟨P.1 x,h⟩).val:=(P.2.1 x).symm.trans he
 exact hx (hz.symm ▸ (q.1 ⟨P.1 x,h⟩).property)
def uI (q:Inv {x // p x}) (P:vG p q):Inv {x // ¬p x}:=
 let f:{x // ¬p x}→{x // ¬p x}:=fun x=>⟨P.1 x,jy p q P x x.property⟩
 have hf:Function.Involutive f:=fun x=>Subtype.ext (P.2.1 x)
 ⟨hf.toPerm,hf⟩
def extend (q:Inv {x // p x}) (Q:Inv {x // ¬p x}):vG p q:=
 ⟨(yO p q Q).toPerm,yO p q Q,
  fun x=>yT p q Q x x.property⟩
def jJ (q:Inv {x // p x}):vG p q ≃ Inv {x // ¬p x} where
 toFun:=uI p q
 invFun:=extend p q
 left_inv P:=by
  apply Subtype.ext
  ext x
  change vB p q (uI p q P) x=P.1 x
  by_cases hx:p x
  · rw [yT _ _ _ _ hx]
    exact (P.2.2 ⟨x,hx⟩).symm
  · rw [vI _ _ _ _ hx]
    rfl
 right_inv Q:=by
  apply Subtype.ext
  ext x
  change vB p q Q x=(Q.1 x).val
  exact vI p q Q x x.property
def jr {β:Type*} (e:α ≃ β):Inv α ≃ Inv β where
 toFun P:=⟨e.symm.trans (P.1.trans e),fun y=>by
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [P.2,Equiv.apply_symm_apply]⟩
 invFun Q:=⟨e.trans (Q.1.trans e.symm),fun x=>by
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  rw [Q.2,Equiv.symm_apply_apply]⟩
 left_inv P:=by
  apply Subtype.ext
  ext x
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
 right_inv Q:=by
  apply Subtype.ext
  ext x
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
theorem je [Fintype α] (q:Inv {x // p x}):
 Nat.card (vG p q)=Nat.card (Inv (Fin (Fintype.card {x // ¬p x}))):=by
 rw [Nat.card_congr (jJ p q)]
 exact Nat.card_congr (jr (Fintype.equivFin {x // ¬p x}))
end zH
namespace qC
open Finset
theorem wh {ι α:Type*} [DecidableEq α]
 (I:Finset ι) (f:ι→Finset α)
 (hc:∀ i∈I,(f i).card=2)
 (hd:∀ i∈I,∀ j∈I,i≠j→Disjoint (f i) (f j))
 (i:ι) (hi:i∈I) (x:zv I f) (hx:x.val∈f i):
 (wZ I f hc hd x).val∈f i:=by
 obtain ⟨j,hj,hxj,hyj,hne⟩:=kj I f hc hd x
 have hij:=yP I f hd hi hj hx hxj
 subst j
 exact hyj
end qC
namespace vY
open Finset
variable {ι:Type*} [Fintype ι]
def zn (k:Nat) (f:ι→Finset Nat) (i:ι):Finset (Fin k):=
 zi.lift k (f i)
def vu (k:Nat) (f:ι→Finset Nat):Finset (Fin k):=
 Finset.univ.biUnion (zn k f)
theorem yr (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hb:∀i,∀x∈f i,x<k) (i:ι):
 (zn k f i).card=2:=by
 rw [zn,zi.qaR k (f i) (hb i),hc]
theorem vh (k:Nat) (f:ι→Finset Nat)
 (hd:∀i j,i≠j→Disjoint (f i) (f j)) (i j:ι) (hij:i≠j):
 Disjoint (zn k f i) (zn k f j):=
 zi.k0 k (f i) (f j) (hd i j hij)
noncomputable def vx (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hd:∀i j,i≠j→Disjoint (f i) (f j))
 (hb:∀i,∀x∈f i,x<k):zH.Inv {x //x∈vu k f}:=by
 classical
 exact ⟨qC.wZ Finset.univ (zn k f)
  (fun i _=>yr k f hc hb i) (fun i _ j _ h=>vh k f hd i j h),
  qC.jw Finset.univ (zn k f)
  (fun i _=>yr k f hc hb i) (fun i _ j _ h=>vh k f hd i j h)⟩
theorem qaO (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hd:∀i j,i≠j→Disjoint (f i) (f j))
 (hb:∀i,∀x∈f i,x<k) (i:ι) (x:{x //x∈vu k f})
 (hx:x.val∈zn k f i):
 ((vx k f hc hd hb).1 x).val∈zn k f i:=by
 classical
 exact qC.wh Finset.univ (zn k f)
  (fun i _=>yr k f hc hb i) (fun i _ j _ h=>vh k f hd i j h)
  i (mem_univ _) x hx
theorem qa2 (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hd:∀i j,i≠j→Disjoint (f i) (f j))
 (hb:∀i,∀x∈f i,x<k) (x:{x //x∈vu k f}):
 ((vx k f hc hd hb).1 x).val≠x.val:=by
 intro h
 exact qC.wj Finset.univ (zn k f)
  (fun i _=>yr k f hc hb i) (fun i _ j _ h=>vh k f hd i j h)
  x (Subtype.ext h)
theorem qat (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hd:∀i j,i≠j→Disjoint (f i) (f j))
 (hb:∀i,∀x∈f i,x<k) (P:Equiv.Perm (Fin k)):
 (∀x:{x //x∈vu k f},P x=((vx k f hc hd hb).1 x).val)↔
 ∀i,qr.q8 (qX.zF P) (f i):=by
 classical
 constructor
 · intro h i n hn
   let x:Fin k:=⟨n,hb i n hn⟩
   have hx:x∈zn k f i:=zi.zJ.mpr hn
   have hxS:x∈vu k f:=mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
   have he:=h ⟨x,hxS⟩
   have hm:=qaO k f hc hd hb i ⟨x,hxS⟩ hx
   have hne:=qa2 k f hc hd hb ⟨x,hxS⟩
   change qX.zF P x.val∈f i∧qX.zF P x.val≠x.val
   rw [qX.zZ,he]
   exact ⟨zi.zJ.mp hm,fun hh=>hne (Fin.ext hh)⟩
 · intro h x
   obtain ⟨i,hi,hxi⟩:=mem_biUnion.mp x.property
   have hh:=h i x.val.val (zi.zJ.mp hxi)
   rw [qX.zZ] at hh
   change P x=qC.qo Finset.univ (zn k f)
    (fun i _=>yr k f hc hb i) (fun i _ j _ hh=>vh k f hd i j hh) x
   symm
   apply qC.jN
   refine ⟨i,hi,hxi,zi.zJ.mpr hh.1,?_⟩
   intro he
   exact hh.2 (congrArg Fin.val he)
theorem jh (k:Nat) (f:ι→Finset Nat)
 (hc:∀i,(f i).card=2) (hd:∀i j,i≠j→Disjoint (f i) (f j))
 (hb:∀i,∀x∈f i,x<k):
 Nat.card {P:Equiv.Perm (Fin k) // Function.Involutive P∧
  ∀i,qr.q8 (qX.zF P) (f i)}=
 Nat.card (zH.Inv (Fin (k-2*Fintype.card ι))):=by
 classical
 let q:=vx k f hc hd hb
 let e:{P:Equiv.Perm (Fin k) // Function.Involutive P∧
  ∀i,qr.q8 (qX.zF P) (f i)} ≃
  zH.vG (fun x=>x∈vu k f) q:=
  Equiv.subtypeEquivRight (fun P=>and_congr Iff.rfl (qat k f hc hd hb P).symm)
 rw [Nat.card_congr e,zH.je]
 have hn:Fintype.card {x //x∉vu k f}=k-2*Fintype.card ι:=by
  calc
   Fintype.card {x //x∉vu k f}=(Finset.univ \ vu k f).card:=
    Fintype.card_of_subtype _ (fun x=>by simp)
   _=k-2*Fintype.card ι:=by
    have hh:=qC.kp Finset.univ (zn k f)
     (fun i _=>yr k f hc hb i) (fun i _ j _ h=>vh k f hd i j h)
    simpa only [vu,qC.zv,Fintype.card_fin,Finset.card_univ] using hh
 rw [hn]
end vY
namespace yk
open qO
theorem kA {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (r:Fin v→Fin (2*e+1)) (o:S→Bool)
 (hpin:y2 wire S r):
 Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // Function.Involutive P∧
  ∀i:zu v e m S,
   qr.q8 (qX.zF P) (ze wire S r o i)}=
 Nat.card {Q:Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q}:=by
 have h:=vY.jh (v*(2*e+1)+2*m) (ze wire S r o)
  (jK wire S r o) (uA he wire S r o hpin)
  (fun i x hx=>jn wire S r o i hx)
 simpa only [qaw] using h
end yk
namespace zT
open Finset
theorem qaP {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m)):
 Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // wx wire S P}=
  if ((S ×ˢ (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)).card=2*S.card
  then 2^S.card*(2*e+1)^(v-2*S.card)*
   Nat.card {Q:Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0:=by
 classical
 letI:Fintype (zY wire S):=by unfold zY; infer_instance
 rw [y3.qae (wx wire S) (qZ wire S)
  (qan he wire S) (wR wire S)]
 have hf (b:zY wire S):
  Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // qZ wire S b P}=
  Nat.card {Q:Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q}:=
  yk.kA he wire S b.2.val b.1 b.2.property
 simp_rw [hf]
 rw [Finset.sum_const,smul_eq_mul,Finset.card_univ,← Nat.card_eq_fintype_card,jR he]
 split_ifs <;> simp
end zT
namespace vL
theorem ki (n:Nat):
 0 < Nat.card {P:Equiv.Perm (Fin n) // Function.Involutive P}:=by
 letI:Nonempty {P:Equiv.Perm (Fin n) // Function.Involutive P}:=
  ⟨⟨Equiv.refl _,fun _=>rfl⟩⟩
 exact Nat.card_pos
theorem wS {α:Type*} [Finite α] (W T:α→Prop)
 (h:0 < Nat.card {a // W a∧T a}):0 < Nat.card {a // W a}:=by
 obtain ⟨⟨a,ha⟩⟩:=(Nat.card_pos_iff.mp h).1
 letI:Nonempty {a // W a}:=⟨⟨a,ha.1⟩⟩
 exact Nat.card_pos
theorem qbe {α:Type*} [Finite α] (W T:α→Prop) (q v:Nat)
 (hq:0 < q)
 (hc:Nat.card {a // W a∧T a}=
   q^v * Nat.card {P:Equiv.Perm (Fin v) // Function.Involutive P}):
 0 < Nat.card {a // W a}:=by
 apply wS W T
 rw [hc]
 exact Nat.mul_pos (Nat.pow_pos hq) (ki v)
end vL
namespace qS
open Finset LoosePathStructure qO qX z2
def kT {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):Finset (Finset Nat):=
 ((Finset.range v ×ˢ Finset.range e).image (qF e)) ∪
   Finset.univ.image (qn v e m wire)
def kb {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
    (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):Prop:=
 Function.Involutive P∧∀ R∈kT wire,
  ∃ i:Fin (v*(2*e+1)+2*m),i.val∈R∧(P i).val∈R∧P i≠i
noncomputable def vA {v e m:Nat} (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):Finset (Fin m):=by
 classical
 exact Finset.univ.filter (fun j=>¬∃ i:Fin (v*(2*e+1)+2*m),
  i.val=v*(2*e+1)+2*j.val∧(P i).val=v*(2*e+1)+2*j.val+1)
theorem kv {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (R:Finset Nat) (hR:R∈kT wire) (x:Nat) (hx:x∈R):x<v*(2*e+1)+2*m:=by
 rcases Finset.mem_union.mp hR with hR|hR
 · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hR
   have:=yC hz hx
   omega
 · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hR
   have hp:=yX wire z
   have hz:=z.1.isLt
   simp only [qn,Finset.mem_insert,Finset.mem_singleton] at hx
   omega
theorem jT {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (i:Fin v) (t:Fin e):qF e (i.val,t.val)∈kT wire:=by
 apply Finset.mem_union_left
 exact Finset.mem_image.mpr ⟨(i.val,t.val),Finset.mem_product.mpr
  ⟨Finset.mem_range.mpr i.isLt,Finset.mem_range.mpr t.isLt⟩,rfl⟩
theorem u9 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (z:Fin m×Bool):qn v e m wire z∈kT wire:=
 Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)
theorem qa6 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):kb wire P↔
 Function.Involutive P∧
 (∀ i:Fin v,∀ t:Fin e,vK (zF P) (qF e (i.val,t.val)))∧
 ∀ z:Fin m×Bool,vK (zF P) (qn v e m wire z):=by
 constructor
 · rintro ⟨hInv,hw⟩
   refine ⟨hInv,?_,?_⟩
   · intro i t
     have hm:=jT wire i t
     exact (z7.u5 P _ (kv wire _ hm)).mp (hw _ hm)
   · intro z
     have hm:=u9 wire z
     exact (z7.u5 P _ (kv wire _ hm)).mp (hw _ hm)
 · rintro ⟨hInv,hpath,hswitch⟩
   refine ⟨hInv,?_⟩
   intro R hR
   apply (z7.u5 P R (kv wire R hR)).mpr
   rcases Finset.mem_union.mp hR with hh|hh
   · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hh
     have hz:=Finset.mem_product.mp hz
     exact hpath ⟨z.1,Finset.mem_range.mp hz.1⟩ ⟨z.2,Finset.mem_range.mp hz.2⟩
   · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hh
     exact hswitch z
theorem js {v e m:Nat} (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))) (j:Fin m):
 j∈vA (v:=v) (e:=e) (m:=m) P↔zF P (qG v e (j,false))≠qG v e (j,true):=by
 classical
 simp only [vA,Finset.mem_filter,Finset.mem_univ,true_and]
 exact z7.kL P j
theorem qa3 {v e m:Nat} (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)))
 (S:Finset (Fin m)) (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):
 (kb wire P∧vA (v:=v) (e:=e) (m:=m) P=S)↔zT.wx wire S P:=by
 rw [qa6]
 constructor
 · rintro ⟨⟨hInv,hpath,hswitch⟩,ha⟩
   refine ⟨hInv,hpath,hswitch,?_⟩
   intro j
   rw [← ha]
   exact js P j
 · rintro ⟨hInv,hpath,hswitch,ha⟩
   refine ⟨⟨hInv,hpath,hswitch⟩,?_⟩
   apply Finset.ext
   intro j
   exact (js P j).trans (ha j).symm
theorem jm {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))) (S:Finset (Fin m)):
 Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // kb wire P∧vA (v:=v) (e:=e) (m:=m) P=S}=
  if ((S ×ˢ (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)).card=2*S.card
  then 2^S.card*(2*e+1)^(v-2*S.card)*
   Nat.card {Q:Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0:=by
 rw [Nat.card_congr (Equiv.subtypeEquivRight (qa3 wire S))]
 exact zT.qaP he wire S
theorem wt {v e m:Nat} (he:0<e)
 (wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2))):
 0<Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // kb wire P}:=by
 have hc:=jm he wire ∅
 have hp:0<Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) //
  kb wire P∧vA (v:=v) (e:=e) (m:=m) P=∅}:=by
  rw [hc]
  simp only [Finset.card_empty,Finset.empty_product,Finset.image_empty,Nat.mul_zero,
   Nat.sub_zero,pow_zero,one_mul,ite_true,eq_self_iff_true]
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (vL.ki v)
 exact vL.wS (kb wire) (fun P=>vA (v:=v) (e:=e) (m:=m) P=∅) hp
end qS
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem wy:∀ (v e m:Nat),0 < e→∀ wire:(Fin m×Bool) ≃ (Fin v×Fin (e+2)),
 let q:=2*e+1
 let k:=v*q+2*m
 let leaf:=fun j:Nat=>if j=0 then 0 else if j=e+1 then 2*e else 2*j-1
 let atPort:=fun z:Fin m×Bool=>(wire z).1.val*q + leaf (wire z).2.val
 let path:=((Finset.range v).product (Finset.range e)).image (fun z=>
  let b:=z.1*q+2*z.2
  ({b,b+1,b+2}:Finset Nat))
 let switches:=Finset.univ.image (fun z:Fin m×Bool=>
  let b:=v*q+2*z.1.val
  ({b,b+1,atPort z}:Finset Nat))
 let H:=path ∪ switches
 let kb:=fun P:Equiv.Perm (Fin k)=>Function.Involutive P∧
  ∀ R∈H,∃ i:Fin k,i.val∈R∧(P i).val∈R∧P i≠i
 let vA:=fun P:Equiv.Perm (Fin k)=>Finset.univ.filter (fun j:Fin m=>
  ¬ ∃ i:Fin k,i.val=v*q+2*j.val∧(P i).val=v*q+2*j.val+1)
 let ends:=fun S:Finset (Fin m)=>
  (S.product (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)
 let I:=fun u:Nat=>Nat.card {P:Equiv.Perm (Fin u) // Function.Involutive P}
 H.card=v*e+2*m∧(∀ R∈H,R.card=3)∧
 (∀ i:Fin k,(H.filter (fun R=>i.val∈R)).card=2)∧
 0 < Nat.card {P:Equiv.Perm (Fin k) // kb P}∧
 ∀ S:Finset (Fin m),Nat.card {P:Equiv.Perm (Fin k) // kb P∧vA P=S}=
   if (ends S).card=2*S.card then
    2^S.card * q^(v-2*S.card) * I (v-2*S.card) else 0:=by
 classical
 intro v e m he wire
 dsimp only
 have ha (P:Equiv.Perm (Fin (v*(2*e+1)+2*m))):
  (Finset.univ:Finset (Fin m)).filter (fun j=>
    ¬∃ i:Fin (v*(2*e+1)+2*m),i.val=v*(2*e+1)+2*j.val∧
      (P i).val=v*(2*e+1)+2*j.val+1)=
  qS.vA (v:=v) (e:=e) (m:=m) P:=by
  ext j
  simp [qS.vA]
 simp_rw [ha]
 change (qS.kT wire).card=v*e+2*m∧
  (∀ R∈qS.kT wire,R.card=3)∧
  (∀ i:Fin (v*(2*e+1)+2*m),((qS.kT wire).filter (fun R=>i.val∈R)).card=2)∧
  (0<Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) // qS.kb wire P})∧
  ∀ S:Finset (Fin m),Nat.card {P:Equiv.Perm (Fin (v*(2*e+1)+2*m)) //
    qS.kb wire P∧qS.vA (v:=v) (e:=e) (m:=m) P=S}=
    if ((S ×ˢ (Finset.univ:Finset Bool)).image (fun z=>(wire z).1)).card=2*S.card then
    2^S.card*(2*e+1)^(v-2*S.card)*Nat.card {Q:Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0
 exact ⟨(LoosePathStructure.qa7 he wire).1,(LoosePathStructure.qa7 he wire).2,
  LoosePathStructure.qbj he wire,qS.wt he wire,
  qS.jm he wire⟩
end qaZ
end
namespace qg
open scoped BigOperators
lemma qV {α β:Type*} (L:List α) (f:α→List β) (k:ℕ)
 (hf:∀ a∈L,(f a).length=k):(L.flatMap f).length=L.length * k:=by
 induction L with
 | nil=>simp
 | cons a r ih=>
   rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
    ih (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
lemma zQ {α β:Type*} (L:List α) (f:α→List β) (k:ℕ)
 (hf:∀ a∈L,(f a).length=k):
 ∀ (i j:ℕ) (hi:i < L.length) (hj:j < k),
   (L.flatMap f)[i * k + j]'(by
     rw [qV L f k hf]
     have:(i + 1) * k≤L.length * k:=Nat.mul_le_mul_right k (by omega)
     rw [Nat.succ_mul] at this; omega)=
   (f (L[i]))[j]'(by rw [hf _ (List.getElem_mem hi)]; exact hj):=by
 induction L with
 | nil=>intro i _ hi; simp at hi
 | cons a r ih=>
   intro i j hi hj
   cases i with
   | zero=>
     simp only [Nat.zero_mul,zero_add,List.flatMap_cons,List.getElem_cons_zero]
     rw [List.getElem_append_left (by rw [hf a (List.mem_cons_self ..)]; exact hj)]
   | succ i=>
     simp only [List.flatMap_cons,List.getElem_cons_succ]
     have hlen:(f a).length=k:=hf a (List.mem_cons_self ..)
     rw [List.getElem_append_right (by rw [hlen,Nat.succ_mul]; omega)]
     have hidx:(i + 1) * k + j - (f a).length=i * k + j:=by rw [hlen,Nat.succ_mul]; omega
     simp only [hidx]
     exact ih (fun x hx=>hf x (List.mem_cons_of_mem a hx)) i j (by simpa using hi) hj
lemma z4 {α:Type*} [DecidableEq α] (L:List α)
 (h:L.toFinset.card=L.length):L.Nodup:=by
 induction L with
 | nil=>exact List.nodup_nil
 | cons a r ih=>
   simp only [List.toFinset_cons,List.length_cons] at h
   have hle:r.toFinset.card≤r.length:=List.toFinset_card_le r
   by_cases ha:a∈r
   · have hmem:a∈r.toFinset:=List.mem_toFinset.mpr ha
     rw [Finset.insert_eq_of_mem hmem] at h
     omega
   · have hmem:a∉r.toFinset:=fun hm=>ha (List.mem_toFinset.mp hm)
     rw [Finset.card_insert_of_notMem hmem] at h
     exact List.nodup_cons.mpr ⟨ha,ih (by omega)⟩
lemma zD {a b n:ℕ} (hn:0 < n) (hb:b < n):(a * n + b) / n=a:=by
 rw [mul_comm,Nat.mul_add_div hn,Nat.div_eq_of_lt hb,add_zero]
lemma zE {a b n:ℕ} (hb:b < n):(a * n + b) % n=b:=by
 rw [mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt hb]
def zO (n:ℕ):List (Fin n×Fin n):=
 (List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
lemma vH (n:ℕ):(zO n).length=n * n:=by
 dsimp only [zO]
 rw [qV (List.finRange n) _ n (fun _ _=>by simp),List.length_finRange]
lemma jf {n:ℕ} (hn:0 < n) (c:ℕ) (hc:c < n * n):
 (zO n)[c]'(by rw [vH]; exact hc)=
   (⟨c / n,Nat.div_lt_of_lt_mul (by omega)⟩,⟨c % n,Nat.mod_lt c hn⟩):=by
 have hq:c / n < (List.finRange n).length:=by
  rw [List.length_finRange]; exact Nat.div_lt_of_lt_mul (by omega)
 have hm:c % n < n:=Nat.mod_lt c hn
 have hdm:c / n * n + c % n=c:=by have:=Nat.div_add_mod c n; linarith
 have hget:=zQ (List.finRange n)
  (fun i=>(List.finRange n).map (fun j=>(i,j))) n (fun _ _=>by simp) (c / n) (c % n) hq hm
 simp only [hdm,List.getElem_map,List.getElem_finRange] at hget
 exact hget
lemma uZ (n:ℕ) (z:Fin n×Fin n):z∈zO n:=by
 simp [zO,List.mem_flatMap,List.mem_map]
def zl (n h:ℕ):ℕ:=2 * (n + h)
def qL (n h:ℕ):ℕ:=2 * zl n h + 1
def qA (n h block j:ℕ):ℕ:=
 block * qL n h + (if j=0 then 0 else if j=zl n h + 1 then 2 * zl n h else 2 * j - 1)
def zC {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ):List (ℕ×ℕ):=
 (zO n).flatMap (fun z=>
   let l:=qA n h z.1.val (2 * z.2.val)
   let l':=qA n h z.1.val (2 * z.2.val + 1)
   let r:=qA n h (n + z.2.val) (2 * z.1.val)
   let r':=qA n h (n + z.2.val) (2 * z.1.val + 1)
   if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])++
 (List.range (2 * n)).flatMap (fun u=>(List.range (h + 1)).map (fun j=>
   (qA n h u (2 * n + 2 * j),qA n h u (2 * n + 2 * j + 1))))
def zf (n h:ℕ):ℕ:=2 * (n * n) + 2 * n * (h + 1)
lemma zk {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ):
 (zC A h).length=zf n h:=by
 dsimp only [zC,zf]
 rw [List.length_append]
 have h1:((zO n).flatMap (fun z=>
  let l:=qA n h z.1.val (2 * z.2.val)
  let l':=qA n h z.1.val (2 * z.2.val + 1)
  let r:=qA n h (n + z.2.val) (2 * z.1.val)
  let r':=qA n h (n + z.2.val) (2 * z.1.val + 1)
  if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])).length=2 * (n * n):=by
  rw [qV (zO n) _ 2 (fun z _=>by split_ifs <;> rfl),
   vH,mul_comm]
 have h2:((List.range (2 * n)).flatMap (fun u=>(List.range (h + 1)).map (fun j=>
  (qA n h u (2 * n + 2 * j),qA n h u (2 * n + 2 * j + 1))))).length=
  2 * n * (h + 1):=by
  rw [qV (List.range (2 * n)) _ (h + 1) (fun _ _=>by simp),
   List.length_range]
 rw [h1,h2]
def qQ (n h:ℕ):ℕ:=2 * n * qL n h + 2 * zf n h
def zX {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ):List (List ℕ):=
 (List.range (2 * n)).flatMap (fun u=>(List.range (zl n h)).map (fun j=>
   let b:=u * qL n h + 2 * j
   [b,b + 1,b + 2]))++(zC A h).zipIdx.flatMap (fun z=>
     let b:=2 * n * qL n h + 2 * z.2
     [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])
lemma wk {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ):
 (zX A h).length=2 * n * zl n h + 2 * zf n h:=by
 dsimp only [zX]
 rw [List.length_append]
 have h1:((List.range (2 * n)).flatMap (fun u=>(List.range (zl n h)).map (fun j=>
  let b:=u * qL n h + 2 * j; [b,b + 1,b + 2]))).length=2 * n * zl n h:=by
  rw [qV (List.range (2 * n)) _ (zl n h) (fun _ _=>by simp),
   List.length_range]
 have h2:((zC A h).zipIdx.flatMap (fun z=>
  let b:=2 * n * qL n h + 2 * z.2; [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])).length=
  2 * zf n h:=by
  rw [qV (zC A h).zipIdx _ 2 (fun _ _=>rfl),
   List.length_zipIdx,zk,mul_comm]
 rw [h1,h2]
def zx {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ)
    (z:Fin (zf n h)×Bool):Fin (2 * n)×Fin (zl n h + 2):=
 if ht:z.1.val < 2 * (n * n) then
  let c:=z.1.val / 2
  let s:=z.1.val % 2
  let i:Fin n:=⟨c / n,Nat.div_lt_of_lt_mul (by omega)⟩
  let j:Fin n:=⟨c % n,Nat.mod_lt c hn⟩
  if A i j then
   if z.2 then (⟨n + j.val,by omega⟩,⟨2 * i.val + s,by dsimp [zl]; omega⟩)
   else (⟨i.val,by omega⟩,⟨2 * j.val + s,by dsimp [zl]; omega⟩)
  else
   if s=0 then
    (⟨i.val,by omega⟩,⟨2 * j.val + z.2.toNat,by dsimp [zl]; cases z.2 <;> simp <;> omega⟩)
   else
    (⟨n + j.val,by omega⟩,⟨2 * i.val + z.2.toNat,by dsimp [zl]; cases z.2 <;> simp <;> omega⟩)
 else
  let w:=z.1.val - 2 * (n * n)
  let u:=w / (h + 1)
  let j:=w % (h + 1)
  have hlt:z.1.val < zf n h:=z.1.isLt
  have hw:w < 2 * n * (h + 1):=by dsimp [zf] at hlt; omega
  have hu:u < 2 * n:=Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hw)
  have hj:j < h + 1:=Nat.mod_lt w (Nat.succ_pos h)
  (⟨u,hu⟩,⟨2 * n + 2 * j + z.2.toNat,by dsimp [zl]; cases z.2 <;> simp <;> omega⟩)
def z0 {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ)
    (p:Fin (2 * n)×Fin (zl n h + 2)):Fin (zf n h)×Bool:=
 if hp:p.2.val < 2 * n then
  let q2:=p.2.val / 2
  let r2:=p.2.val % 2
  if hu:p.1.val < n then
   let i:Fin n:=⟨p.1.val,hu⟩
   let j:Fin n:=⟨q2,by omega⟩
   let c:=i.val * n + j.val
   have hc:c < n * n:=by
    have h1:(i.val + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   if A i j then
    (⟨2 * c + r2,by dsimp [zf]; omega⟩,false)
   else
    (⟨2 * c,by dsimp [zf]; omega⟩,decide (r2=1))
  else
   let i:Fin n:=⟨q2,by omega⟩
   let j:Fin n:=⟨p.1.val - n,by omega⟩
   let c:=i.val * n + j.val
   have hc:c < n * n:=by
    have h1:(i.val + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   if A i j then
    (⟨2 * c + r2,by dsimp [zf]; omega⟩,true)
   else
    (⟨2 * c + 1,by dsimp [zf]; omega⟩,decide (r2=1))
 else
  let d:=p.2.val - 2 * n
  let j:=d / 2
  let r2:=d % 2
  have hpe:p.2.val < 2 * (n + h) + 2:=p.2.isLt
  have hj:j < h + 1:=by omega
  have hu:p.1.val < 2 * n:=p.1.isLt
  have ht:2 * (n * n) + (p.1.val * (h + 1) + j) < zf n h:=by
   dsimp [zf]
   have h1:(p.1.val + 1) * (h + 1)≤2 * n * (h + 1):=Nat.mul_le_mul_right (h + 1) (by omega)
   rw [Nat.succ_mul] at h1; omega
  (⟨2 * (n * n) + (p.1.val * (h + 1) + j),ht⟩,decide (r2=1))
lemma wu {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ)
 (z:Fin (zf n h)×Bool):
 z0 A h (zx hn A h z)=z:=by
 rcases z with ⟨⟨t,htM⟩,side⟩
 dsimp only [zx]
 split_ifs with ht hA hside hs
 · subst hside
   have hdiv:(t / 2) / n * n + (t / 2) % n=t / 2:=by
    have:=Nat.div_add_mod (t / 2) n; linarith
   have h2:(2 * ((t / 2) / n) + t % 2) / 2=(t / 2) / n:=by omega
   have h2m:(2 * ((t / 2) / n) + t % 2) % 2=t % 2:=by omega
   have hlt2n:2 * ((t / 2) / n) + t % 2 < 2 * n:=by
    have:(t / 2) / n < n:=Nat.div_lt_of_lt_mul (by omega)
    omega
   have hmodn:(t / 2) % n < n:=Nat.mod_lt (t / 2) hn
   have hsubn:n + (t / 2) % n - n=(t / 2) % n:=by omega
   have hnotn:¬ (n + (t / 2) % n < n):=by omega
   dsimp only [z0]
   simp only [hlt2n,hnotn,↓reduceDIte]
   have hi:(⟨(2 * ((t / 2) / n) + t % 2) / 2,by omega⟩:Fin n)=
    ⟨(t / 2) / n,Nat.div_lt_of_lt_mul (by omega)⟩:=Fin.ext h2
   have hj:(⟨n + (t / 2) % n - n,by omega⟩:Fin n)=
    ⟨(t / 2) % n,hmodn⟩:=Fin.ext hsubn
   rw [hi,hj]
   simp only [hA,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) rfl
   simp only [h2,h2m,hsubn,hdiv]; omega
 · have hsf:side=false:=Bool.eq_false_iff.mpr hside
   subst hsf
   have hdiv:(t / 2) / n * n + (t / 2) % n=t / 2:=by
    have:=Nat.div_add_mod (t / 2) n; linarith
   have h2:(2 * ((t / 2) % n) + t % 2) / 2=(t / 2) % n:=by omega
   have h2m:(2 * ((t / 2) % n) + t % 2) % 2=t % 2:=by omega
   have hlt2n:2 * ((t / 2) % n) + t % 2 < 2 * n:=by
    have:(t / 2) % n < n:=Nat.mod_lt (t / 2) hn
    omega
   have hltn:(t / 2) / n < n:=Nat.div_lt_of_lt_mul (by omega)
   dsimp only [z0]
   simp only [hlt2n,hltn,↓reduceDIte]
   have hj:(⟨(2 * ((t / 2) % n) + t % 2) / 2,by omega⟩:Fin n)=
    ⟨(t / 2) % n,Nat.mod_lt (t / 2) hn⟩:=Fin.ext h2
   rw [hj]
   simp only [hA,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) rfl
   simp only [h2,h2m,hdiv]; omega
 · have hdiv:(t / 2) / n * n + (t / 2) % n=t / 2:=by
    have:=Nat.div_add_mod (t / 2) n; linarith
   have h2:(2 * ((t / 2) % n) + side.toNat) / 2=(t / 2) % n:=by
    cases side <;> simp <;> omega
   have hlt2n:2 * ((t / 2) % n) + side.toNat < 2 * n:=by
    have:(t / 2) % n < n:=Nat.mod_lt (t / 2) hn
    cases side <;> simp <;> omega
   have hltn:(t / 2) / n < n:=Nat.div_lt_of_lt_mul (by omega)
   dsimp only [z0]
   simp only [hlt2n,hltn,↓reduceDIte]
   have hj:(⟨(2 * ((t / 2) % n) + side.toNat) / 2,by omega⟩:Fin n)=
    ⟨(t / 2) % n,Nat.mod_lt (t / 2) hn⟩:=Fin.ext h2
   rw [hj]
   simp only [hA,Bool.false_eq_true,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) ?_
   · simp only [h2,hdiv]; omega
   · cases side <;> simp <;> omega
 · have hdiv:(t / 2) / n * n + (t / 2) % n=t / 2:=by
    have:=Nat.div_add_mod (t / 2) n; linarith
   have h2:(2 * ((t / 2) / n) + side.toNat) / 2=(t / 2) / n:=by
    cases side <;> simp <;> omega
   have hlt2n:2 * ((t / 2) / n) + side.toNat < 2 * n:=by
    have:(t / 2) / n < n:=Nat.div_lt_of_lt_mul (by omega)
    cases side <;> simp <;> omega
   have hmodn:(t / 2) % n < n:=Nat.mod_lt (t / 2) hn
   have hsubn:n + (t / 2) % n - n=(t / 2) % n:=by omega
   have hnotn:¬ (n + (t / 2) % n < n):=by omega
   dsimp only [z0]
   simp only [hlt2n,hnotn,↓reduceDIte]
   have hi:(⟨(2 * ((t / 2) / n) + side.toNat) / 2,by omega⟩:Fin n)=
    ⟨(t / 2) / n,Nat.div_lt_of_lt_mul (by omega)⟩:=Fin.ext h2
   have hj:(⟨n + (t / 2) % n - n,by omega⟩:Fin n)=
    ⟨(t / 2) % n,hmodn⟩:=Fin.ext hsubn
   rw [hi,hj]
   simp only [hA,Bool.false_eq_true,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) ?_
   · simp only [h2,hsubn,hdiv]; omega
   · cases side <;> simp <;> omega
 · have hnot2n:¬ (2 * n + 2 * ((t - 2 * (n * n)) % (h + 1)) + side.toNat < 2 * n):=by omega
   dsimp only [z0]
   simp only [hnot2n,↓reduceDIte]
   have hw:(t - 2 * (n * n)) / (h + 1) * (h + 1) + (t - 2 * (n * n)) % (h + 1)=
    t - 2 * (n * n):=by
    have:=Nat.div_add_mod (t - 2 * (n * n)) (h + 1); linarith
   have hsub:2 * n + 2 * ((t - 2 * (n * n)) % (h + 1)) + side.toNat - 2 * n=
    2 * ((t - 2 * (n * n)) % (h + 1)) + side.toNat:=by omega
   have hdiv2:(2 * ((t - 2 * (n * n)) % (h + 1)) + side.toNat) / 2=
    (t - 2 * (n * n)) % (h + 1):=by cases side <;> simp <;> omega
   refine Prod.ext (Fin.ext ?_) ?_
   · simp only [hsub,hdiv2,hw]; omega
   · simp only [hsub]
     cases side <;> simp <;> omega
lemma jX {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ)
 (p:Fin (2 * n)×Fin (zl n h + 2)):
 zx hn A h (z0 A h p)=p:=by
 rcases p with ⟨⟨u,hu2n⟩,⟨v,hve⟩⟩
 dsimp only [z0]
 split_ifs with hp hu hA hA2
 · dsimp only [zx]
   have hlt:2 * (u * n + v / 2) + v % 2 < 2 * (n * n):=by
    have h1:(u + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   simp only [hlt,↓reduceDIte]
   have hc:(2 * (u * n + v / 2) + v % 2) / 2=u * n + v / 2:=by omega
   have hs:(2 * (u * n + v / 2) + v % 2) % 2=v % 2:=by omega
   have hci:(2 * (u * n + v / 2) + v % 2) / 2 / n=u:=by
    rw [hc,zD hn (by omega)]
   have hcj:(2 * (u * n + v / 2) + v % 2) / 2 % n=v / 2:=by
    rw [hc,zE (by omega)]
   have hi:(⟨(2 * (u * n + v / 2) + v % 2) / 2 / n,
    Nat.div_lt_of_lt_mul (by omega)⟩:Fin n)=⟨u,hu⟩:=Fin.ext hci
   have hj:(⟨(2 * (u * n + v / 2) + v % 2) / 2 % n,
    Nat.mod_lt _ hn⟩:Fin n)=⟨v / 2,by omega⟩:=Fin.ext hcj
   rw [hi,hj]
   simp only [hA,Bool.false_eq_true,↓reduceIte]
   exact Prod.ext (Fin.ext hci) (Fin.ext (by dsimp only; rw [hcj,hs]; omega))
 · dsimp only [zx]
   have hlt:2 * (u * n + v / 2) < 2 * (n * n):=by
    have h1:(u + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   simp only [hlt,↓reduceDIte]
   have hc:2 * (u * n + v / 2) / 2=u * n + v / 2:=by omega
   have hs:2 * (u * n + v / 2) % 2=0:=by omega
   have hci:2 * (u * n + v / 2) / 2 / n=u:=by
    rw [hc,zD hn (by omega)]
   have hcj:2 * (u * n + v / 2) / 2 % n=v / 2:=by
    rw [hc,zE (by omega)]
   have hi:(⟨2 * (u * n + v / 2) / 2 / n,
    Nat.div_lt_of_lt_mul (by omega)⟩:Fin n)=⟨u,hu⟩:=Fin.ext hci
   have hj:(⟨2 * (u * n + v / 2) / 2 % n,
    Nat.mod_lt _ hn⟩:Fin n)=⟨v / 2,by omega⟩:=Fin.ext hcj
   rw [hi,hj]
   simp only [hA,Bool.false_eq_true,hs,↓reduceIte]
   refine Prod.ext (Fin.ext hci) (Fin.ext ?_)
   dsimp only; rw [hcj]
   by_cases hr:v % 2=1 <;> simp [hr] <;> omega
 · dsimp only [zx]
   have hlt:2 * (v / 2 * n + (u - n)) + v % 2 < 2 * (n * n):=by
    have h1:(v / 2 + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   simp only [hlt,↓reduceDIte]
   have hc:(2 * (v / 2 * n + (u - n)) + v % 2) / 2=v / 2 * n + (u - n):=by omega
   have hs:(2 * (v / 2 * n + (u - n)) + v % 2) % 2=v % 2:=by omega
   have hci:(2 * (v / 2 * n + (u - n)) + v % 2) / 2 / n=v / 2:=by
    rw [hc,zD hn (by omega)]
   have hcj:(2 * (v / 2 * n + (u - n)) + v % 2) / 2 % n=u - n:=by
    rw [hc,zE (by omega)]
   have hi:(⟨(2 * (v / 2 * n + (u - n)) + v % 2) / 2 / n,
    Nat.div_lt_of_lt_mul (by omega)⟩:Fin n)=⟨v / 2,by omega⟩:=Fin.ext hci
   have hj:(⟨(2 * (v / 2 * n + (u - n)) + v % 2) / 2 % n,
    Nat.mod_lt _ hn⟩:Fin n)=⟨u - n,by omega⟩:=Fin.ext hcj
   rw [hi,hj]
   simp only [hA2,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
   · dsimp only; rw [hcj]; omega
   · dsimp only; rw [hci,hs]; omega
 · dsimp only [zx]
   have hlt:2 * (v / 2 * n + (u - n)) + 1 < 2 * (n * n):=by
    have h1:(v / 2 + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1; omega
   simp only [hlt,↓reduceDIte]
   have hc:(2 * (v / 2 * n + (u - n)) + 1) / 2=v / 2 * n + (u - n):=by omega
   have hs:¬ ((2 * (v / 2 * n + (u - n)) + 1) % 2=0):=by omega
   have hci:(2 * (v / 2 * n + (u - n)) + 1) / 2 / n=v / 2:=by
    rw [hc,zD hn (by omega)]
   have hcj:(2 * (v / 2 * n + (u - n)) + 1) / 2 % n=u - n:=by
    rw [hc,zE (by omega)]
   have hi:(⟨(2 * (v / 2 * n + (u - n)) + 1) / 2 / n,
    Nat.div_lt_of_lt_mul (by omega)⟩:Fin n)=⟨v / 2,by omega⟩:=Fin.ext hci
   have hj:(⟨(2 * (v / 2 * n + (u - n)) + 1) / 2 % n,
    Nat.mod_lt _ hn⟩:Fin n)=⟨u - n,by omega⟩:=Fin.ext hcj
   rw [hi,hj]
   simp only [hA2,Bool.false_eq_true,hs,↓reduceIte]
   refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
   · dsimp only; rw [hcj]; omega
   · dsimp only; rw [hci]
     by_cases hr:v % 2=1 <;> simp [hr] <;> omega
 · dsimp only [zx]
   have hnot:¬ (2 * (n * n) + (u * (h + 1) + (v - 2 * n) / 2) < 2 * (n * n)):=by omega
   simp only [hnot,↓reduceDIte]
   have hsub:2 * (n * n) + (u * (h + 1) + (v - 2 * n) / 2) - 2 * (n * n)=
    u * (h + 1) + (v - 2 * n) / 2:=by omega
   have hjlt:(v - 2 * n) / 2 < h + 1:=by dsimp [zl] at hve; omega
   have hqu:(u * (h + 1) + (v - 2 * n) / 2) / (h + 1)=u:=
    zD (Nat.succ_pos h) hjlt
   have hrm:(u * (h + 1) + (v - 2 * n) / 2) % (h + 1)=(v - 2 * n) / 2:=
    zE hjlt
   refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
   · dsimp only; rw [hsub,hqu]
   · dsimp only; rw [hsub,hrm]
     by_cases hr:(v - 2 * n) % 2=1 <;> simp [hr] <;> omega
def qB {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
    (Fin (zf n h)×Bool) ≃ (Fin (2 * n)×Fin (zl n h + 2)) where
 toFun:=zx hn A h
 invFun:=z0 A h
 left_inv:=wu hn A h
 right_inv:=jX hn A h
lemma vy {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ)
 (t:Fin (zf n h)):
 let e:=(zC A h)[t.val]'(by rw [zk]; exact t.isLt)
 e.1=qA n h (qB hn A h (t,false)).1.val (qB hn A h (t,false)).2.val∧
 e.2=qA n h (qB hn A h (t,true)).1.val (qB hn A h (t,true)).2.val:=by
 have hlen1:((zO n).flatMap (fun z=>
  let l:=qA n h z.1.val (2 * z.2.val)
  let l':=qA n h z.1.val (2 * z.2.val + 1)
  let r:=qA n h (n + z.2.val) (2 * z.1.val)
  let r':=qA n h (n + z.2.val) (2 * z.1.val + 1)
  if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])).length=2 * (n * n):=by
  rw [qV (zO n) _ 2 (fun z _=>by split_ifs <;> rfl),
   vH,mul_comm]
 have hgetE:(zC A h)[t.val]'(by rw [zk]; exact t.isLt)=
  (qA n h (qB hn A h (t,false)).1.val (qB hn A h (t,false)).2.val,
   qA n h (qB hn A h (t,true)).1.val (qB hn A h (t,true)).2.val):=by
  let L1:=(zO n).flatMap (fun z=>
   let l:=qA n h z.1.val (2 * z.2.val)
   let l':=qA n h z.1.val (2 * z.2.val + 1)
   let r:=qA n h (n + z.2.val) (2 * z.1.val)
   let r':=qA n h (n + z.2.val) (2 * z.1.val + 1)
   if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])
  let L2:=(List.range (2 * n)).flatMap (fun u=>(List.range (h + 1)).map (fun j=>
   (qA n h u (2 * n + 2 * j),qA n h u (2 * n + 2 * j + 1))))
  have hL1:L1.length=2 * (n * n):=hlen1
  have hltApp:t.val < (L1++L2).length:=by
   change t.val < (zC A h).length; rw [zk]; exact t.isLt
  have hEqApp:(zC A h)[t.val]'(by rw [zk]; exact t.isLt)=(L1++L2)[t.val]'hltApp:=rfl
  rw [hEqApp]
  dsimp only [qB,Equiv.coe_fn_mk,zx]
  by_cases ht:t.val < 2 * (n * n)
  · rw [List.getElem_append_left (by rw [hL1]; exact ht)]
    have hc:t.val / 2 < (zO n).length:=by rw [vH]; omega
    have hs:t.val % 2 < 2:=Nat.mod_lt t.val (by omega)
    have hdm:t.val / 2 * 2 + t.val % 2=t.val:=by omega
    have hget:=zQ (zO n) (fun z=>
     let l:=qA n h z.1.val (2 * z.2.val)
     let l':=qA n h z.1.val (2 * z.2.val + 1)
     let r:=qA n h (n + z.2.val) (2 * z.1.val)
     let r':=qA n h (n + z.2.val) (2 * z.1.val + 1)
     if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')]) 2
     (fun z _=>by split_ifs <;> rfl) (t.val / 2) (t.val % 2) hc hs
    simp only [hdm] at hget
    change L1[t.val]'_=_
    dsimp only [L1]
    rw [hget,jf hn (t.val / 2) (by omega)]
    simp only [ht,↓reduceDIte]
    cases hA:A ⟨t.val / 2 / n,Nat.div_lt_of_lt_mul (by omega)⟩ ⟨t.val / 2 % n,Nat.mod_lt _ hn⟩
    · simp only [Bool.false_eq_true,↓reduceIte]
      have hmod:t.val % 2=0∨t.val % 2=1:=by omega
      rcases hmod with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp only [↓reduceIte]
      have hmod:t.val % 2=0∨t.val % 2=1:=by omega
      rcases hmod with h0 | h1
      · simp [h0]
      · simp [h1]
  · rw [List.getElem_append_right (by rw [hL1]; omega)]
    simp only [hL1,ht,↓reduceDIte]
    set w:=t.val - 2 * (n * n)
    have hw:w < 2 * n * (h + 1):=by have:=t.isLt; dsimp [zf] at this; omega
    have hu:w / (h + 1) < (List.range (2 * n)).length:=by
     rw [List.length_range]; exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hw)
    have hj:w % (h + 1) < h + 1:=Nat.mod_lt w (Nat.succ_pos h)
    have hdm:w / (h + 1) * (h + 1) + w % (h + 1)=w:=by
     have:=Nat.div_add_mod w (h + 1); linarith
    have hget:=zQ (List.range (2 * n))
     (fun u=>(List.range (h + 1)).map (fun j=>
       (qA n h u (2 * n + 2 * j),qA n h u (2 * n + 2 * j + 1))))
     (h + 1) (fun _ _=>by simp) (w / (h + 1)) (w % (h + 1)) hu hj
    simp only [hdm,List.getElem_map,List.getElem_range] at hget
    change L2[w]'_=_
    dsimp only [L2]
    rw [hget]
    simp only [w,Bool.toNat_false,Bool.toNat_true,add_zero]
 exact ⟨congrArg Prod.fst hgetE,congrArg Prod.snd hgetE⟩
def HOf {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):Finset (Finset ℕ):=
 let v:=2 * n
 let e:=zl n h
 let q:=qL n h
 let leaf:=fun j:ℕ=>if j=0 then 0 else if j=e + 1 then 2 * e else 2 * j - 1
 let atPort:=fun z:Fin (zf n h)×Bool=>
  (qB hn A h z).1.val * q + leaf (qB hn A h z).2.val
 let path:=((Finset.range v).product (Finset.range e)).image (fun z=>
  let b:=z.1 * q + 2 * z.2
  ({b,b + 1,b + 2}:Finset ℕ))
 let switches:=Finset.univ.image (fun z:Fin (zf n h)×Bool=>
  let b:=v * q + 2 * z.1.val
  ({b,b + 1,atPort z}:Finset ℕ))
 path ∪ switches
lemma vQ {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
 ((zX A h).map List.toFinset).toFinset=HOf hn A h:=by
 ext T
 simp only [List.mem_toFinset,List.mem_map,zX,List.mem_append,List.mem_flatMap,
  List.mem_range,HOf,Finset.mem_union,Finset.mem_image,Finset.product_eq_sprod,
  Finset.mem_product,Finset.mem_range,Finset.mem_univ,true_and]
 constructor
 · rintro ⟨R,⟨u,hu,j,hj,rfl⟩ | ⟨z,hz,hRz⟩,rfl⟩
   · left
     refine ⟨(u,j),⟨hu,hj⟩,?_⟩
     ext x; simp [or_assoc]
   · right
     rw [List.mem_iff_getElem] at hz
     rcases hz with ⟨idx,hidxZ,hzEq⟩
     rw [List.length_zipIdx,zk] at hidxZ
     rw [List.getElem_zipIdx] at hzEq
     have hz1:z.1=(zC A h)[idx]'(by rw [zk]; exact hidxZ):=by
      rw [← hzEq]
     have hz2:z.2=idx:=by rw [← hzEq]; simp
     have hport:=vy hn A h ⟨idx,hidxZ⟩
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hRz
     rcases hRz with hR1 | hR2
     · subst hR1
       refine ⟨(⟨idx,hidxZ⟩,false),?_⟩
       rw [hz1,hz2,hport.1]; ext x; simp [qA,or_assoc]
     · subst hR2
       refine ⟨(⟨idx,hidxZ⟩,true),?_⟩
       rw [hz1,hz2,hport.2]; ext x; simp [qA,or_assoc]
 · rintro (⟨⟨u,j⟩,⟨hu,hj⟩,rfl⟩ | ⟨⟨t,side⟩,rfl⟩)
   · refine ⟨[u * qL n h + 2 * j,u * qL n h + 2 * j + 1,u * qL n h + 2 * j + 2],
      Or.inl ⟨u,hu,j,hj,rfl⟩,?_⟩
     ext x; simp [or_assoc]
   · have hlt:t.val < (zC A h).length:=by rw [zk]; exact t.isLt
     have hmem:((zC A h)[t.val]'hlt,t.val)∈(zC A h).zipIdx:=by
      rw [List.mem_iff_getElem]
      exact ⟨t.val,by rw [List.length_zipIdx]; exact hlt,by simp [List.getElem_zipIdx]⟩
     have hport:=vy hn A h t
     cases side with
     | false=>
       refine ⟨[2 * n * qL n h + 2 * t.val,2 * n * qL n h + 2 * t.val + 1,
        ((zC A h)[t.val]'hlt).1],Or.inr ⟨_,hmem,by simp⟩,?_⟩
       rw [hport.1]; ext x; simp [qA,or_assoc]
     | true=>
       refine ⟨[2 * n * qL n h + 2 * t.val,2 * n * qL n h + 2 * t.val + 1,
        ((zC A h)[t.val]'hlt).2],Or.inr ⟨_,hmem,by simp⟩,?_⟩
       rw [hport.2]; ext x; simp [qA,or_assoc]
lemma qaA {n h block j:ℕ} (hb:block < 2 * n) (hj:j < zl n h + 2):
 qA n h block j < 2 * n * qL n h:=by
 dsimp only [qA,qL]
 have h1:(block + 1) * (2 * zl n h + 1)≤2 * n * (2 * zl n h + 1):=
  Nat.mul_le_mul_right _ (by omega)
 rw [Nat.succ_mul] at h1
 split_ifs <;> omega
lemma w4 {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
 ((zX A h).map List.toFinset).Nodup∧
 (∀ R∈zX A h,R.length=3∧R.Nodup∧∀ u∈R,u < qQ n h)∧
 (∀ u:Fin (qQ n h),((zX A h).filter (fun R=>decide (u.val∈R))).length=2):=by
 have he:0 < zl n h:=by dsimp [zl]; omega
 have h930:=qaZ.wy (2 * n) (zl n h) (zf n h) he (qB hn A h)
 dsimp only at h930
 obtain ⟨hHcard,hH3,hHdeg,_,_⟩:=h930
 have htoF:=vQ hn A h
 have hnodup:((zX A h).map List.toFinset).Nodup:=by
  apply z4
  rw [htoF,List.length_map,wk]
  exact hHcard
 refine ⟨hnodup,?_,?_⟩
 · intro R hR
   have hRlen:R.length=3:=by
    dsimp only [zX] at hR
    simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range] at hR
    rcases hR with ⟨_,_,_,_,rfl⟩ | ⟨_,_,hR2⟩
    · rfl
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hR2
      rcases hR2 with rfl | rfl <;> rfl
   have hRmemH:R.toFinset∈HOf hn A h:=by
    rw [← htoF,List.mem_toFinset]
    exact List.mem_map.mpr ⟨R,hR,rfl⟩
   have hRnodup:R.Nodup:=by
    apply z4
    rw [hRlen]
    exact hH3 R.toFinset hRmemH
   have hRlt:∀ u∈R,u < qQ n h:=by
    intro u hu
    have huT:u∈R.toFinset:=List.mem_toFinset.mpr hu
    dsimp only [HOf] at hRmemH
    simp only [Finset.mem_union,Finset.mem_image,Finset.product_eq_sprod,Finset.mem_product,
     Finset.mem_range,Finset.mem_univ,true_and] at hRmemH
    rcases hRmemH with ⟨⟨blk,j⟩,⟨hblk,hj⟩,hEq⟩ | ⟨z,hEq⟩
    · rw [← hEq] at huT
      simp only [Finset.mem_insert,Finset.mem_singleton] at huT
      have h1:(blk + 1) * qL n h≤2 * n * qL n h:=Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h1
      dsimp only [qQ,qL] at h1 huT ⊢
      rcases huT with rfl | rfl | rfl <;> omega
    · rw [← hEq] at huT
      simp only [Finset.mem_insert,Finset.mem_singleton] at huT
      have hz1:z.1.val < zf n h:=z.1.isLt
      rcases huT with rfl | rfl | rfl
      · dsimp only [qQ]; omega
      · dsimp only [qQ]; omega
      · have hp:=qaA (n:=n) (h:=h) (qB hn A h z).1.isLt (qB hn A h z).2.isLt
        dsimp only [qQ,qA] at hp ⊢; omega
   exact ⟨hRlen,hRnodup,hRlt⟩
 · intro u
   have hfilt:((zX A h).filter (fun R=>decide (u.val∈R))).length=
    (((zX A h).map List.toFinset).filter (fun T=>decide (u.val∈T))).length:=by
    rw [List.filter_map,List.length_map]
    congr 1
    apply List.filter_congr
    intro R _
    simp [List.mem_toFinset]
   rw [hfilt]
   have hfnodup:(((zX A h).map List.toFinset).filter (fun T=>decide (u.val∈T))).Nodup:=
    hnodup.filter _
   rw [← List.toFinset_card_of_nodup hfnodup]
   have hfeq:(((zX A h).map List.toFinset).filter (fun T=>decide (u.val∈T))).toFinset=
    (HOf hn A h).filter (fun T=>u.val∈T):=by
    ext T
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter,← htoF]
   rw [hfeq]
   exact hHdeg u
def vi {k:ℕ} (p:Equiv.Perm (Fin k)):(Fin k→Bool)→(Fin k→Bool)→Bool:=
 fun x y=>decide (∃ i:Fin k,
  (x i=true∧y i=true)∨
  (p i≠i∧((x i=true∧x (p i)=true)∨(y i=true∧y (p i)=true))))
lemma wL {k:ℕ} {p₁ p₂:Equiv.Perm (Fin k)}
 (hp₁:Function.Involutive p₁) (hp₂:Function.Involutive p₂)
 (heq:vi p₁=vi p₂):p₁=p₂:=by
 apply Equiv.ext
 intro u
 have hfn:∀ x y,vi p₁ x y=vi p₂ x y:=fun x y=>congrFun (congrFun heq x) y
 by_cases h1:p₁ u=u
 · by_contra hne
   have h2:p₂ u≠u:=fun h=>hne (by rw [h1,h])
   let x:Fin k→Bool:=fun i=>decide (i=u∨i=p₂ u)
   have htrue2:vi p₂ x (fun _=>false)=true:=by
    simp only [vi,decide_eq_true_eq]
    exact ⟨u,Or.inr ⟨h2,Or.inl ⟨by simp [x],by simp [x]⟩⟩⟩
   have htrue1:vi p₁ x (fun _=>false)=true:=(hfn x (fun _=>false)).trans htrue2
   simp only [vi,decide_eq_true_eq] at htrue1
   rcases htrue1 with ⟨i,⟨_,hf⟩ | ⟨hpi,⟨hxi,hxpi⟩ | ⟨hf,_⟩⟩⟩
   · exact Bool.false_ne_true hf
   · simp only [x,decide_eq_true_eq] at hxi hxpi
     rcases hxi with rfl | rfl
     · exact hpi h1
     · rcases hxpi with hpu | hpp
       · exact h2 (p₁.injective (hpu.trans h1.symm))
       · exact hpi hpp
   · exact Bool.false_ne_true hf
 · let x:Fin k→Bool:=fun i=>decide (i=u∨i=p₁ u)
   have htrue1:vi p₁ x (fun _=>false)=true:=by
    simp only [vi,decide_eq_true_eq]
    exact ⟨u,Or.inr ⟨h1,Or.inl ⟨by simp [x],by simp [x]⟩⟩⟩
   have htrue2:vi p₂ x (fun _=>false)=true:=(hfn x (fun _=>false)).symm.trans htrue1
   simp only [vi,decide_eq_true_eq] at htrue2
   rcases htrue2 with ⟨i,⟨_,hf⟩ | ⟨hpi,⟨hxi,hxpi⟩ | ⟨hf,_⟩⟩⟩
   · exact (Bool.false_ne_true hf).elim
   · simp only [x,decide_eq_true_eq] at hxi hxpi
     rcases hxi with rfl | rfl
     · rcases hxpi with hpu | hpp
       · exact (hpi hpu).elim
       · exact hpp.symm
     · rcases hxpi with hpu | hpp
       · have h2:p₂ u=p₁ u:=by calc p₂ u=p₂ (p₂ (p₁ u)):=by rw [hpu]
          _=p₁ u:=hp₂ (p₁ u)
         exact h2.symm
       · exact (hpi hpp).elim
   · exact (Bool.false_ne_true hf).elim
noncomputable def ZOf {n:ℕ} (A:Fin n→Fin n→Bool) (h:ℕ):ℕ:=
 let k:=qQ n h
 let Fn:=(Fin k→Bool)→(Fin k→Bool)→Bool
 Nat.card {f:Fn // (∃ C:PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C∧C.size + 1≤2 * k∧
  PEqualNP.Represents.Represents (fun i j:Fin k=>decide (i=j)) C∧
  ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y))∧
  ∀ R∈zX A h,f (fun i=>decide (i.val∈R)) (fun _=>false)=true}
def vo {n:ℕ} (A:Fin n→Fin n→Bool):Finset (Finset (Fin n×Fin n)):=
 (zO n).toFinset.powerset.filter (fun S=>
   (∀ z∈S,A z.1 z.2=true)∧(S.image Prod.fst).card=S.card∧
   (S.image Prod.snd).card=S.card)
def ye {n:ℕ} (A:Fin n→Fin n→Bool) (r:ℕ):ℕ:=
 ((vo A).filter (fun S=>S.card=r)).card
noncomputable def qY (j:ℕ):ℕ:=Nat.card {P:Equiv.Perm (Fin j) // Function.Involutive P}
lemma kZ:qY 0=1:=by
 dsimp only [qY]
 let e:{P:Equiv.Perm (Fin 0) // Function.Involutive P} ≃ Unit:=
  { toFun:=fun _=>()
    invFun:=fun _=>⟨1,fun x=>Fin.elim0 x⟩
    left_inv:=fun ⟨_,_⟩=>Subtype.ext (Equiv.ext fun x=>Fin.elim0 x)
    right_inv:=fun _=>rfl }
 rw [Nat.card_congr e]; simp
lemma u1 {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
 ZOf A h=Nat.card {P:Equiv.Perm (Fin (qQ n h)) //
  Function.Involutive P∧∀ T∈HOf hn A h,
   ∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i}:=by
 classical
 have hk2:2≤qQ n h:=by
  have hnn:1≤n * n:=Nat.mul_pos hn hn
  dsimp [qQ,qL,zl,zf]; nlinarith
 have htoF:=vQ hn A h
 have hprobe:∀ (P:Equiv.Perm (Fin (qQ n h))),
  (∀ R∈zX A h,vi P (fun i=>decide (i.val∈R)) (fun _=>false)=true)↔
  (∀ T∈HOf hn A h,∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i):=by
  intro P
  constructor
  · intro hR T hT
    rw [← htoF,List.mem_toFinset,List.mem_map] at hT
    rcases hT with ⟨R,hRm,rfl⟩
    have h1:=hR R hRm
    simp only [vi,decide_eq_true_eq,Bool.false_eq_true,and_false,or_false,false_or] at h1
    rcases h1 with ⟨i,hne,hi,hpi⟩
    exact ⟨i,List.mem_toFinset.mpr hi,List.mem_toFinset.mpr hpi,hne⟩
  · intro hT R hRm
    have hTm:R.toFinset∈HOf hn A h:=by
     rw [← htoF,List.mem_toFinset]; exact List.mem_map.mpr ⟨R,hRm,rfl⟩
    rcases hT R.toFinset hTm with ⟨i,hi,hpi,hne⟩
    simp only [List.mem_toFinset] at hi hpi
    simp only [vi,decide_eq_true_eq]
    exact ⟨i,Or.inr ⟨hne,Or.inl ⟨hi,hpi⟩⟩⟩
 let toF:{P:Equiv.Perm (Fin (qQ n h)) //
     Function.Involutive P∧∀ T∈HOf hn A h,
      ∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i}→
     {f:(Fin (qQ n h)→Bool)→(Fin (qQ n h)→Bool)→Bool //
       (∃ C:PEqualNP.CircuitLowerBounds.Circuit,
         PEqualNP.MetaComplexity.Monotone2 C∧C.size + 1≤2 * qQ n h∧
         PEqualNP.Represents.Represents (fun i j:Fin (qQ n h)=>decide (i=j)) C∧
         ∀ x y,f x y=C.eval (List.ofFn x++List.ofFn y))∧
       ∀ R∈zX A h,f (fun i=>decide (i.val∈R)) (fun _=>false)=true}:=
  fun ⟨P,hInv,hW⟩=>
   ⟨vi P,⟨(qaJ (qQ n h) hk2 (vi P)).2 ⟨P,⟨hInv,fun _ _=>rfl⟩,fun Q ⟨hQI,hQf⟩=>
     (wL hInv hQI (funext fun x=>funext fun y=>hQf x y)).symm⟩,
     (hprobe P).2 hW⟩⟩
 have hbij:Function.Bijective toF:=by
  constructor
  · rintro ⟨P₁,hI₁,_⟩ ⟨P₂,hI₂,_⟩ heq
    have hfeq:vi P₁=vi P₂:=congrArg Subtype.val heq
    exact Subtype.ext (wL hI₁ hI₂ hfeq)
  · rintro ⟨f,hC,hR⟩
    obtain ⟨P,⟨hInv,hfeq⟩,_⟩:=(qaJ (qQ n h) hk2 f).1 hC
    have hfP:f=vi P:=funext fun x=>funext fun y=>hfeq x y
    have hW:∀ T∈HOf hn A h,∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i:=
     (hprobe P).1 (by rwa [← hfP])
    refine ⟨⟨P,hInv,hW⟩,Subtype.ext hfP.symm⟩
 exact (Nat.card_congr (Equiv.ofBijective toF hbij)).symm
def qw {n:ℕ} (hn:0 < n) (t:ℕ):Fin n×Fin n:=
 if h:t < 2 * (n * n) then
  (⟨t / 2 / n,Nat.div_lt_of_lt_mul (by omega)⟩,⟨t / 2 % n,Nat.mod_lt _ hn⟩)
 else
  (⟨0,hn⟩,⟨0,hn⟩)
lemma yL {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ)
 (S:Finset (Fin (zf n h))):
 ((S.product (Finset.univ:Finset Bool)).image (fun z=>(qB hn A h z).1)).card=
   2 * S.card↔
 (∀ t∈S,t.val < 2 * (n * n)∧A (qw hn t.val).1 (qw hn t.val).2=true)∧
 (∀ t₁∈S,∀ t₂∈S,t₁≠t₂→
   (qw hn t₁.val).1≠(qw hn t₂.val).1∧
   (qw hn t₁.val).2≠(qw hn t₂.val).2):=by
 have hcard:(S.product (Finset.univ:Finset Bool)).card=2 * S.card:=by
  rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_bool,mul_comm]
 rw [← hcard,Finset.card_image_iff]
 have hwF:∀ t (hlt:t.val < 2 * (n * n)),
  A (qw hn t.val).1 (qw hn t.val).2=true→
  (qB hn A h (t,false)).1.val=(qw hn t.val).1.val∧
  (qB hn A h (t,true)).1.val=n + (qw hn t.val).2.val:=by
  intro t hlt hA
  dsimp only [qw] at hA ⊢
  simp only [hlt,↓reduceDIte] at hA ⊢
  dsimp only [qB,Equiv.coe_fn_mk,zx]
  simp only [hlt,↓reduceDIte,hA,↓reduceIte,Bool.false_eq_true,and_self]
 constructor
 · intro hinj
   have hgood1:∀ t∈S,t.val < 2 * (n * n)∧
    A (qw hn t.val).1 (qw hn t.val).2=true:=by
    intro t htS
    have hne:(qB hn A h (t,false)).1≠(qB hn A h (t,true)).1:=by
     intro heq
     have hm1:(t,false)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨htS,Finset.mem_univ false⟩
     have hm2:(t,true)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨htS,Finset.mem_univ true⟩
     have hpair:=hinj hm1 hm2 heq
     simp at hpair
    by_cases hlt:t.val < 2 * (n * n)
    · refine ⟨hlt,?_⟩
      dsimp only [qw]; simp only [hlt,↓reduceDIte]
      dsimp only [qB,Equiv.coe_fn_mk,zx] at hne
      simp only [hlt,↓reduceDIte] at hne
      cases hA:A ⟨t.val / 2 / n,Nat.div_lt_of_lt_mul (by omega)⟩ ⟨t.val / 2 % n,Nat.mod_lt _ hn⟩
      · simp only [hA,Bool.false_eq_true,↓reduceIte] at hne
        split_ifs at hne <;> exact (hne rfl).elim
      · rfl
    · dsimp only [qB,Equiv.coe_fn_mk,zx] at hne
      simp only [hlt,↓reduceDIte] at hne
      exact (hne rfl).elim
   refine ⟨hgood1,?_⟩
   intro t₁ ht₁ t₂ ht₂ hne
   obtain ⟨hlt₁,hA₁⟩:=hgood1 t₁ ht₁
   obtain ⟨hlt₂,hA₂⟩:=hgood1 t₂ ht₂
   obtain ⟨hf₁,ht₁v⟩:=hwF t₁ hlt₁ hA₁
   obtain ⟨hf₂,ht₂v⟩:=hwF t₂ hlt₂ hA₂
   constructor
   · intro heq
     have hw:(qB hn A h (t₁,false)).1=(qB hn A h (t₂,false)).1:=
      Fin.ext (by rw [hf₁,hf₂,heq])
     have hm1:(t₁,false)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨ht₁,Finset.mem_univ false⟩
     have hm2:(t₂,false)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨ht₂,Finset.mem_univ false⟩
     have hp:=hinj hm1 hm2 hw
     exact hne (Prod.mk.inj hp).1
   · intro heq
     have hw:(qB hn A h (t₁,true)).1=(qB hn A h (t₂,true)).1:=
      Fin.ext (by rw [ht₁v,ht₂v,heq])
     have hm1:(t₁,true)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨ht₁,Finset.mem_univ true⟩
     have hm2:(t₂,true)∈S.product (Finset.univ:Finset Bool):=by
      rw [Finset.product_eq_sprod]; exact Finset.mem_product.mpr ⟨ht₂,Finset.mem_univ true⟩
     have hp:=hinj hm1 hm2 hw
     exact hne (Prod.mk.inj hp).1
 · rintro ⟨hgood1,hgood2⟩ ⟨t₁,b₁⟩ h1 ⟨t₂,b₂⟩ h2 heq
   rw [Finset.mem_coe,Finset.product_eq_sprod,Finset.mem_product] at h1 h2
   obtain ⟨hlt₁,hA₁⟩:=hgood1 t₁ h1.1
   obtain ⟨hlt₂,hA₂⟩:=hgood1 t₂ h2.1
   obtain ⟨hf₁,ht₁v⟩:=hwF t₁ hlt₁ hA₁
   obtain ⟨hf₂,ht₂v⟩:=hwF t₂ hlt₂ hA₂
   have heqv:=congrArg Fin.val heq
   cases b₁ <;> cases b₂
   · rw [hf₁,hf₂] at heqv
     by_cases ht:t₁=t₂
     · exact Prod.ext ht rfl
     · exact ((hgood2 t₁ h1.1 t₂ h2.1 ht).1 (Fin.ext heqv)).elim
   · rw [hf₁,ht₂v] at heqv
     have:=(qw hn t₁.val).1.isLt; omega
   · rw [ht₁v,hf₂] at heqv
     have:=(qw hn t₂.val).1.isLt; omega
   · rw [ht₁v,ht₂v] at heqv
     by_cases ht:t₁=t₂
     · exact Prod.ext ht rfl
     · exact ((hgood2 t₁ h1.1 t₂ h2.1 ht).2 (Fin.ext (by omega))).elim
lemma ko {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
 0 < ZOf A h∧
 ZOf A h=(Finset.range (n + 1)).sum (fun r=>
  4 ^ r * ye A r * (qL n h) ^ (2 * n - 2 * r) * qY (2 * n - 2 * r)):=by
 classical
 have he:0 < zl n h:=by dsimp [zl]; omega
 have h930:=qaZ.wy (2 * n) (zl n h) (zf n h) he (qB hn A h)
 dsimp only at h930
 obtain ⟨_,_,_,hpos,hfib⟩:=h930
 rw [u1 hn A h]
 refine ⟨hpos,?_⟩
 let act:Equiv.Perm (Fin (qQ n h))→Finset (Fin (zf n h)):=fun P=>
  Finset.univ.filter (fun j:Fin (zf n h)=>
   ¬ ∃ i:Fin (qQ n h),i.val=2 * n * qL n h + 2 * j.val∧
     (P i).val=2 * n * qL n h + 2 * j.val + 1)
 let ePart:{P:Equiv.Perm (Fin (qQ n h)) //
     Function.Involutive P∧∀ T∈HOf hn A h,
      ∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i} ≃
     Σ S:Finset (Fin (zf n h)),
       {P:Equiv.Perm (Fin (qQ n h)) //
         (Function.Involutive P∧∀ T∈HOf hn A h,
           ∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i)∧act P=S}:=
  { toFun:=fun ⟨P,hW⟩=>⟨act P,⟨P,hW,rfl⟩⟩
    invFun:=fun ⟨_,⟨P,hW,_⟩⟩=>⟨P,hW⟩
    left_inv:=fun ⟨_,_⟩=>rfl
    right_inv:=fun ⟨_,⟨_,_,hA⟩⟩=>by subst hA; rfl }
 rw [Nat.card_congr ePart,Nat.card_sigma]
 have hsum1:(∑ S:Finset (Fin (zf n h)),
  Nat.card {P:Equiv.Perm (Fin (qQ n h)) //
   (Function.Involutive P∧∀ T∈HOf hn A h,
     ∃ i:Fin (qQ n h),i.val∈T∧(P i).val∈T∧P i≠i)∧act P=S})=
  ∑ S∈(Finset.univ:Finset (Finset (Fin (zf n h)))).filter
    (fun S=>((S.product (Finset.univ:Finset Bool)).image
      (fun z=>(qB hn A h z).1)).card=2 * S.card),
    2 ^ S.card * (qL n h) ^ (2 * n - 2 * S.card) * qY (2 * n - 2 * S.card):=by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _=>hfib S
 rw [hsum1]
 let GoodS:=(Finset.univ:Finset (Finset (Fin (zf n h)))).filter
  (fun S=>((S.product (Finset.univ:Finset Bool)).image
    (fun z=>(qB hn A h z).1)).card=2 * S.card)
 let proj:Finset (Fin (zf n h))→Finset (Fin n×Fin n):=
  fun S=>S.image (fun t=>qw hn t.val)
 have hproj_mem:∀ S∈GoodS,proj S∈vo A∧(proj S).card=S.card:=by
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨hg1,hg2⟩:=(yL hn A h S).1 hS.2
  have hinjC:Set.InjOn (fun t:Fin (zf n h)=>qw hn t.val) S:=by
   intro t₁ ht₁ t₂ ht₂ heq
   by_contra hne
   exact (hg2 t₁ ht₁ t₂ ht₂ hne).1 (congrArg Prod.fst heq)
  have hcardP:(proj S).card=S.card:=Finset.card_image_of_injOn hinjC
  refine ⟨?_,hcardP⟩
  dsimp only [vo]
  rw [Finset.mem_filter,Finset.mem_powerset]
  refine ⟨fun z _=>List.mem_toFinset.mpr (uZ n z),?_,?_,?_⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨t,htS,rfl⟩
    exact (hg1 t htS).2
  · exact Finset.card_image_of_injOn fun z₁ hz₁ z₂ hz₂ heq=>by
     rcases Finset.mem_image.mp hz₁ with ⟨t₁,ht₁,rfl⟩
     rcases Finset.mem_image.mp hz₂ with ⟨t₂,ht₂,rfl⟩
     by_cases ht:t₁=t₂
     · rw [ht]
     · exact ((hg2 t₁ ht₁ t₂ ht₂ ht).1 heq).elim
  · exact Finset.card_image_of_injOn fun z₁ hz₁ z₂ hz₂ heq=>by
     rcases Finset.mem_image.mp hz₁ with ⟨t₁,ht₁,rfl⟩
     rcases Finset.mem_image.mp hz₂ with ⟨t₂,ht₂,rfl⟩
     by_cases ht:t₁=t₂
     · rw [ht]
     · exact ((hg2 t₁ ht₁ t₂ ht₂ ht).2 heq).elim
 have hfiber_card:∀ T∈vo A,(GoodS.filter (fun S=>proj S=T)).card=2 ^ T.card:=by
  intro T hT
  dsimp only [vo] at hT
  rw [Finset.mem_filter,Finset.mem_powerset] at hT
  obtain ⟨_,hAT,hfst,hsnd⟩:=hT
  have hinjF:Set.InjOn Prod.fst (T:Set (Fin n×Fin n)):=
   Finset.card_image_iff.mp hfst
  have hinjS:Set.InjOn Prod.snd (T:Set (Fin n×Fin n)):=
   Finset.card_image_iff.mp hsnd
  let linkOf (z:Fin n×Fin n) (b:Bool):Fin (zf n h):=
   ⟨2 * (z.1.val * n + z.2.val) + b.toNat,by
     dsimp [zf]
     have h1:(z.1.val + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
     rw [Nat.succ_mul] at h1
     have:=z.2.isLt
     cases b <;> simp <;> omega⟩
  have hcell_link:∀ z b,qw hn (linkOf z b).val=z:=by
   intro z b
   dsimp only [qw,linkOf]
   have hlt:2 * (z.1.val * n + z.2.val) + b.toNat < 2 * (n * n):=by
    have h1:(z.1.val + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
    rw [Nat.succ_mul] at h1
    have:=z.2.isLt
    cases b <;> simp <;> omega
   simp only [hlt,↓reduceDIte]
   have hdiv2:(2 * (z.1.val * n + z.2.val) + b.toNat) / 2=z.1.val * n + z.2.val:=by
    cases b <;> simp <;> omega
   have hq:(2 * (z.1.val * n + z.2.val) + b.toNat) / 2 / n=z.1.val:=by
    rw [hdiv2,zD hn z.2.isLt]
   have hr:(2 * (z.1.val * n + z.2.val) + b.toNat) / 2 % n=z.2.val:=by
    rw [hdiv2,zE z.2.isLt]
   exact Prod.ext (Fin.ext hq) (Fin.ext hr)
  let mkS:(T→Bool)→Finset (Fin (zf n h)):=
   fun c=>Finset.univ.image (fun x:T=>linkOf x.1 (c x))
  have hmkS_mem:∀ c:T→Bool,mkS c∈GoodS.filter (fun S=>proj S=T):=by
   intro c
   rw [Finset.mem_filter,Finset.mem_filter]
   have hproj_eq:proj (mkS c)=T:=by
    ext z
    simp only [proj,mkS,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩; rw [hcell_link]; exact x.2
    · intro hz; exact ⟨linkOf z (c ⟨z,hz⟩),⟨⟨z,hz⟩,rfl⟩,hcell_link z _⟩
   refine ⟨⟨Finset.mem_univ _,(yL hn A h (mkS c)).2 ⟨?_,?_⟩⟩,hproj_eq⟩
   · intro t ht
     rcases Finset.mem_image.mp ht with ⟨x,_,rfl⟩
     rw [hcell_link]
     refine ⟨?_,hAT x.1 x.2⟩
     dsimp only [linkOf]
     have h1:(x.1.1.val + 1) * n≤n * n:=Nat.mul_le_mul_right n (by omega)
     rw [Nat.succ_mul] at h1
     have:=x.1.2.isLt
     cases c x <;> simp <;> omega
   · intro t₁ ht₁ t₂ ht₂ hne
     rcases Finset.mem_image.mp ht₁ with ⟨x₁,_,rfl⟩
     rcases Finset.mem_image.mp ht₂ with ⟨x₂,_,rfl⟩
     rw [hcell_link,hcell_link]
     have hxne:x₁.1≠x₂.1:=fun heq=>by
      have hsub:x₁=x₂:=Subtype.ext heq
      subst hsub; exact hne rfl
     exact ⟨fun hf=>hxne (hinjF x₁.2 x₂.2 hf),fun hs=>hxne (hinjS x₁.2 x₂.2 hs)⟩
  have hmkS_inj:Function.Injective mkS:=by
   intro c₁ c₂ heq
   funext x
   have hmem:linkOf x.1 (c₁ x)∈mkS c₂:=by
    rw [← heq]; exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
   rcases Finset.mem_image.mp hmem with ⟨y,_,hy⟩
   have hxy:y=x:=Subtype.ext (by
    have:=congrArg (fun t:Fin (zf n h)=>qw hn t.val) hy
    rwa [hcell_link,hcell_link] at this)
   subst hxy
   have hv:=congrArg Fin.val hy
   dsimp only [linkOf] at hv
   cases hc1:c₁ y <;> cases hc2:c₂ y <;> simp [hc1,hc2] at hv ⊢
  have hmkS_surj:∀ S∈GoodS.filter (fun S=>proj S=T),∃ c:T→Bool,mkS c=S:=by
   intro S hS
   rw [Finset.mem_filter,Finset.mem_filter] at hS
   obtain ⟨⟨_,hgood⟩,hproj⟩:=hS
   obtain ⟨hg1,hg2⟩:=(yL hn A h S).1 hgood
   have hex:∀ x:T,∃ t∈S,qw hn t.val=x.1:=by
    intro x
    have hx:x.1∈proj S:=by rw [hproj]; exact x.2
    exact Finset.mem_image.mp hx
   let pick (x:T):Fin (zf n h):=(hex x).choose
   have hpick_mem:∀ x,pick x∈S:=fun x=>(hex x).choose_spec.1
   have hpick_cell:∀ x,qw hn (pick x).val=x.1:=fun x=>(hex x).choose_spec.2
   refine ⟨fun x=>decide ((pick x).val % 2=1),?_⟩
   ext t
   simp only [mkS,Finset.mem_image,Finset.mem_univ,true_and]
   constructor
   · rintro ⟨x,rfl⟩
     have hlt:=(hg1 (pick x) (hpick_mem x)).1
     have hce:=hpick_cell x
     dsimp only [qw] at hce
     simp only [hlt,↓reduceDIte] at hce
     have hval:(linkOf x.1 (decide ((pick x).val % 2=1))).val=(pick x).val:=by
      dsimp only [linkOf]
      have h1:x.1.1.val=(pick x).val / 2 / n:=(congrArg (fun p=>p.1.val) hce).symm
      have h2:x.1.2.val=(pick x).val / 2 % n:=(congrArg (fun p=>p.2.val) hce).symm
      rw [h1,h2]
      have hdm:(pick x).val / 2 / n * n + (pick x).val / 2 % n=(pick x).val / 2:=by
       have:=Nat.div_add_mod ((pick x).val / 2) n; linarith
      rw [hdm]
      by_cases hm:(pick x).val % 2=1 <;> simp [hm] <;> omega
     rw [Fin.ext hval]
     exact hpick_mem x
   · intro htS
     have hmemT:qw hn t.val∈T:=by
      rw [← hproj]; exact Finset.mem_image.mpr ⟨t,htS,rfl⟩
     refine ⟨⟨qw hn t.val,hmemT⟩,?_⟩
     have hteq:pick ⟨qw hn t.val,hmemT⟩=t:=by
      by_contra hne
      have h1:=(hg2 _ (hpick_mem ⟨qw hn t.val,hmemT⟩) _ htS hne).1
      exact h1 (congrArg Prod.fst (hpick_cell ⟨qw hn t.val,hmemT⟩))
     apply Fin.ext
     dsimp only [linkOf]
     rw [hteq]
     have hlt:=(hg1 t htS).1
     dsimp only [qw]; simp only [hlt,↓reduceDIte]
     have hdm:t.val / 2 / n * n + t.val / 2 % n=t.val / 2:=by
      have:=Nat.div_add_mod (t.val / 2) n; linarith
     rw [hdm]
     by_cases hm:t.val % 2=1 <;> simp [hm] <;> omega
  have hcardE:(GoodS.filter (fun S=>proj S=T)).card=
   (Finset.univ:Finset (T→Bool)).card:=by
   symm
   exact Finset.card_nbij mkS (fun c _=>hmkS_mem c) (fun c₁ _ c₂ _ heq=>hmkS_inj heq)
    (fun S hS=>by
      rw [Finset.mem_coe] at hS
      rcases hmkS_surj S hS with ⟨c,rfl⟩
      exact ⟨c,Finset.mem_coe.mpr (Finset.mem_univ c),rfl⟩)
  rw [hcardE,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]
 have hstep1:∑ S∈GoodS,2 ^ S.card * (qL n h) ^ (2 * n - 2 * S.card) * qY (2 * n - 2 * S.card)=
  ∑ T∈vo A,∑ S∈GoodS.filter (fun S=>proj S=T),
    2 ^ S.card * (qL n h) ^ (2 * n - 2 * S.card) * qY (2 * n - 2 * S.card):=by
  rw [← Finset.sum_fiberwise_of_maps_to (fun S hS=>(hproj_mem S hS).1)]
 have hstep2:∑ T∈vo A,∑ S∈GoodS.filter (fun S=>proj S=T),
       2 ^ S.card * (qL n h) ^ (2 * n - 2 * S.card) * qY (2 * n - 2 * S.card)=
  ∑ T∈vo A,4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card):=by
  refine Finset.sum_congr rfl fun T hT=>?_
  have hconst:∀ S∈GoodS.filter (fun S=>proj S=T),
   2 ^ S.card * (qL n h) ^ (2 * n - 2 * S.card) * qY (2 * n - 2 * S.card)=
   2 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card):=by
   intro S hS
   rw [Finset.mem_filter] at hS
   have hc:S.card=T.card:=by rw [← hS.2,(hproj_mem S hS.1).2]
   rw [hc]
  rw [Finset.sum_congr rfl hconst,Finset.sum_const,hfiber_card T hT,smul_eq_mul]
  have h4:2 ^ T.card * 2 ^ T.card=4 ^ T.card:=by
   rw [← mul_pow]; norm_num
  linarith [show 2 ^ T.card * (2 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) *
   qY (2 * n - 2 * T.card))=
   (2 ^ T.card * 2 ^ T.card) * (qL n h) ^ (2 * n - 2 * T.card) *
     qY (2 * n - 2 * T.card) by ring,
   show (2 ^ T.card * 2 ^ T.card) * (qL n h) ^ (2 * n - 2 * T.card) *
    qY (2 * n - 2 * T.card)=
   4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) *
     qY (2 * n - 2 * T.card) by rw [h4]]
 have hstep3:∑ T∈vo A,4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card)=
  ∑ r∈Finset.range (n + 1),∑ T∈(vo A).filter (fun T=>T.card=r),
    4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card):=by
  rw [← Finset.sum_fiberwise_of_maps_to (g:=Finset.card)]
  intro T hT
  rw [Finset.mem_range]
  dsimp only [vo] at hT
  rw [Finset.mem_filter] at hT
  have hle:(T.image Prod.fst).card≤Fintype.card (Fin n):=Finset.card_le_univ _
  rw [hT.2.2.1,Fintype.card_fin] at hle
  omega
 have hstep4:∑ r∈Finset.range (n + 1),∑ T∈(vo A).filter (fun T=>T.card=r),
       4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card)=
  ∑ r∈Finset.range (n + 1),
    4 ^ r * ye A r * (qL n h) ^ (2 * n - 2 * r) * qY (2 * n - 2 * r):=by
  refine Finset.sum_congr rfl fun r _=>?_
  have hconst:∀ T∈(vo A).filter (fun T=>T.card=r),
   4 ^ T.card * (qL n h) ^ (2 * n - 2 * T.card) * qY (2 * n - 2 * T.card)=
   4 ^ r * (qL n h) ^ (2 * n - 2 * r) * qY (2 * n - 2 * r):=by
   intro T hT; rw [Finset.mem_filter] at hT; rw [hT.2]
  rw [Finset.sum_congr rfl hconst,Finset.sum_const,smul_eq_mul]
  dsimp only [ye]; ring
 exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
lemma v5 {n:ℕ} (A:Fin n→Fin n→Bool):
 ye A n=(Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:=by
 classical
 let B:Matrix (Fin n) (Fin n) ℕ:=fun i j=>(A i j).toNat
 have hperm:B.permanent=
  (Finset.univ.filter (fun σ:Equiv.Perm (Fin n)=>∀ i,A i (σ i)=true)).card:=by
  rw [Matrix.permanent]
  have hsym:∑ σ:Equiv.Perm (Fin n),∏ i:Fin n,B (σ i) i=
   ∑ σ:Equiv.Perm (Fin n),∏ i:Fin n,B i (σ i):=by
   rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
   refine Finset.sum_congr rfl fun σ _=>?_
   simp only [Equiv.inv_apply]
   have h1:∏ i:Fin n,B (σ⁻¹ i) i=∏ i:Fin n,B (σ⁻¹ (σ i)) (σ i):=
    (Equiv.prod_comp σ (fun i=>B (σ⁻¹ i) i)).symm
   rw [h1]
   refine Finset.prod_congr rfl fun i _=>by simp
  rw [hsym,Finset.card_eq_sum_ones,Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _=>?_
  by_cases h:∀ i:Fin n,A i (σ i)=true
  · rw [ite_eq_left_iff.2 (fun hn=>(hn h).elim)]
    exact Finset.prod_eq_one fun i _=>by simp [B,h i]
  · rw [ite_eq_right_iff.2 (fun hp=>(h hp).elim)]
    have ⟨i,hi⟩:∃ i,A i (σ i)≠true:=by
     by_contra hall; exact h fun i=>by by_contra hi'; exact hall ⟨i,hi'⟩
    have hfalse:A i (σ i)=false:=by cases hA:A i (σ i) <;> simp_all
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [B,hfalse])
 change ye A n=B.permanent
 rw [hperm]
 let graph:Equiv.Perm (Fin n)→Finset (Fin n×Fin n):=
  fun σ=>Finset.univ.image (fun i:Fin n=>(i,σ i))
 symm
 refine Finset.card_nbij graph ?_ ?_ ?_
 · intro σ hσ
   rw [Finset.mem_coe,Finset.mem_filter] at hσ
   dsimp only [ye,vo]
   rw [Finset.mem_coe,Finset.mem_filter,Finset.mem_filter,Finset.mem_powerset]
   have hcard:(graph σ).card=n:=by
    rw [Finset.card_image_of_injective _ (fun _ _ h=>(Prod.mk.inj h).1),
     Finset.card_univ,Fintype.card_fin]
   refine ⟨⟨fun z _=>List.mem_toFinset.mpr (uZ n z),?_,?_,?_⟩,hcard⟩
   · intro z hz
     rcases Finset.mem_image.mp hz with ⟨i,_,rfl⟩
     exact hσ.2 i
   · rw [hcard]
     have:(graph σ).image Prod.fst=Finset.univ:=by
      ext i; simp [graph]
     rw [this,Finset.card_univ,Fintype.card_fin]
   · rw [hcard]
     have:(graph σ).image Prod.snd=Finset.univ:=by
      ext j; simp only [graph,Finset.mem_image,Finset.mem_univ,true_and,iff_true]
      exact ⟨(σ.symm j,j),⟨σ.symm j,by simp⟩,rfl⟩
     rw [this,Finset.card_univ,Fintype.card_fin]
 · intro σ₁ _ σ₂ _ heq
   apply Equiv.ext
   intro i
   have hmem:(i,σ₁ i)∈graph σ₂:=by
    rw [← heq]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
   rcases Finset.mem_image.mp hmem with ⟨j,_,hj⟩
   rcases Prod.mk.inj hj with ⟨rfl,h2⟩
   exact h2.symm
 · intro S hS
   dsimp only [ye,vo] at hS
   rw [Finset.mem_coe,Finset.mem_filter,Finset.mem_filter] at hS
   obtain ⟨⟨_,hAS,hfst,hsnd⟩,hcard⟩:=hS
   have hbijF:Function.Bijective (fun x:S=>x.1.1):=by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_,by rw [Fintype.card_coe,hcard,Fintype.card_fin]⟩
    have hinj:=Finset.card_image_iff.mp hfst
    intro x₁ x₂ heq; exact Subtype.ext (hinj x₁.2 x₂.2 heq)
   have hbijS:Function.Bijective (fun x:S=>x.1.2):=by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_,by rw [Fintype.card_coe,hcard,Fintype.card_fin]⟩
    have hinj:=Finset.card_image_iff.mp hsnd
    intro x₁ x₂ heq; exact Subtype.ext (hinj x₁.2 x₂.2 heq)
   let eF:S ≃ Fin n:=Equiv.ofBijective _ hbijF
   let eS:S ≃ Fin n:=Equiv.ofBijective _ hbijS
   let σ:Equiv.Perm (Fin n):=eF.symm.trans eS
   refine ⟨σ,Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i=>?_⟩),?_⟩
   · have hpair:(eF.symm i).1=(i,σ i):=Prod.ext (eF.apply_symm_apply i) rfl
     have hmem:=(eF.symm i).2
     rw [hpair] at hmem
     exact hAS (i,σ i) hmem
   · ext z
     simp only [graph,Finset.mem_image,Finset.mem_univ,true_and]
     constructor
     · rintro ⟨i,rfl⟩
       have hpair:(eF.symm i).1=(i,σ i):=Prod.ext (eF.apply_symm_apply i) rfl
       rw [← hpair]; exact (eF.symm i).2
     · intro hz
       refine ⟨z.1,?_⟩
       have h1:eF ⟨z,hz⟩=z.1:=rfl
       have h2:eF.symm z.1=⟨z,hz⟩:=by rw [← h1,Equiv.symm_apply_apply]
       have h3:σ z.1=z.2:=by dsimp [σ]; rw [h2]; rfl
       exact Prod.ext rfl h3
lemma qao {n d:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool) (_hd:1 < d) (hodd:Odd d):
 let h:=(4 * n + 1) * (d ^ 2 - 1) / 4
 qL n h=(4 * n + 1) * d ^ 2∧
 ZOf A h % (d ^ 2)=(4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent) % (d ^ 2):=by
 intro h
 rcases hodd with ⟨t,rfl⟩
 have hd2:(2 * t + 1) ^ 2 - 1=4 * (t * (t + 1)):=by
  have:(2 * t + 1) ^ 2=4 * (t * (t + 1)) + 1:=by ring
  omega
 have hh4:4 * h=(4 * n + 1) * ((2 * t + 1) ^ 2 - 1):=by
  dsimp only [h]
  rw [hd2,show (4 * n + 1) * (4 * (t * (t + 1)))=4 * ((4 * n + 1) * (t * (t + 1))) by ring,
   Nat.mul_div_cancel_left _ (by omega)]
 have hq:qL n h=(4 * n + 1) * (2 * t + 1) ^ 2:=by
  dsimp only [qL,zl]
  have hge1:1≤(2 * t + 1) ^ 2:=by nlinarith
  have h1:(4 * n + 1) + (4 * n + 1) * ((2 * t + 1) ^ 2 - 1)=(4 * n + 1) * (2 * t + 1) ^ 2:=by
   have:(2 * t + 1) ^ 2=((2 * t + 1) ^ 2 - 1) + 1:=by omega
   conv_rhs=>rw [this]
   ring
  omega
 refine ⟨hq,?_⟩
 rw [(ko hn A h).2,Finset.sum_range_succ]
 have h0:2 * n - 2 * n=0:=by omega
 rw [h0,pow_zero,mul_one,kZ,mul_one,v5 A]
 have hdvd:(2 * t + 1) ^ 2 ∣ ∑ r∈Finset.range n,
  4 ^ r * ye A r * (qL n h) ^ (2 * n - 2 * r) * qY (2 * n - 2 * r):=by
  apply Finset.dvd_sum
  intro r hr
  rw [Finset.mem_range] at hr
  have hpos:0 < 2 * n - 2 * r:=by omega
  have h1:(2 * t + 1) ^ 2 ∣ qL n h:=⟨4 * n + 1,by rw [hq,mul_comm]⟩
  have h2:(2 * t + 1) ^ 2 ∣ (qL n h) ^ (2 * n - 2 * r):=
   dvd_trans h1 (dvd_pow_self _ (by omega))
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _
 rcases hdvd with ⟨K,hK⟩
 rw [hK,add_comm,Nat.add_mul_mod_self_left]
def qk (n h:ℕ):ℕ:=(qL n h) ^ 2
lemma zg (n:ℕ):StrictMono (qk n):=by
 intro a b hab
 dsimp only [qk,qL,zl]
 have:2 * (2 * (n + a)) + 1 < 2 * (2 * (n + b)) + 1:=by omega
 nlinarith
def vz (n:ℕ):ℕ:=
 ∏ i∈Finset.range (n + 1),∏ j∈(Finset.range (n + 1)).filter (fun j=>i < j),
   (qk n j - qk n i)
def qR (n h:ℕ):ℕ:=
 ∏ k∈(Finset.range (n + 1)).erase h,qk n k
def qI (n h:ℕ):ℕ:=
 ∏ i∈(Finset.range (n + 1)).erase h,
   ∏ j∈((Finset.range (n + 1)).erase h).filter (fun j=>i < j),
     (qk n j - qk n i)
def ya (n h:ℕ):ℕ:=
 (∏ i∈(Finset.range (n + 1)).filter (fun i=>i < h),(qk n h - qk n i)) *
 (∏ j∈(Finset.range (n + 1)).filter (fun j=>h < j),(qk n j - qk n h))
lemma jY (n h:ℕ):0 < ya n h:=by
 dsimp only [ya]
 refine Nat.mul_pos (Finset.prod_pos fun i hi=>?_) (Finset.prod_pos fun j hj=>?_)
 · rw [Finset.mem_filter] at hi; have:=zg n hi.2; omega
 · rw [Finset.mem_filter] at hj; have:=zg n hj.2; omega
lemma ke (n h:ℕ) (hh:h < n + 1):ya n h * qI n h=vz n:=by
 let R:=Finset.range (n + 1)
 let P:=(R ×ˢ R).filter (fun p:ℕ×ℕ=>p.1 < p.2)
 have hDAll:vz n=∏ p∈P,(qk n p.2 - qk n p.1):=by
  dsimp only [vz,P,R]
  rw [Finset.prod_filter,Finset.prod_product]
  refine Finset.prod_congr rfl fun i _=>?_
  rw [Finset.prod_filter]
 let P1:=P.filter (fun p=>p.2=h)
 let P2:=P.filter (fun p=>p.1=h)
 let P3:=P.filter (fun p=>p.1≠h∧p.2≠h)
 have hdisj12:Disjoint P1 P2:=by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [P1,P2,P,Finset.mem_filter] at hp1 hp2
  omega
 have hdisj123:Disjoint (P1 ∪ P2) P3:=by
  rw [Finset.disjoint_left]
  intro p hp12 hp3
  simp only [P1,P2,P3,Finset.mem_union,Finset.mem_filter] at hp12 hp3
  rcases hp12 with ⟨_,h2⟩ | ⟨_,h1⟩
  · exact hp3.2.2 h2
  · exact hp3.2.1 h1
 have hunion:P=(P1 ∪ P2) ∪ P3:=by
  ext p
  simp only [P1,P2,P3,Finset.mem_union,Finset.mem_filter]
  by_cases h1:p.1=h <;> by_cases h2:p.2=h <;> tauto
 have hP1:∏ p∈P1,(qk n p.2 - qk n p.1)=
  ∏ i∈R.filter (fun i=>i < h),(qk n h - qk n i):=by
  refine Finset.prod_nbij Prod.fst ?_ ?_ ?_ ?_
  · intro p hp
    simp only [P1,P,Finset.mem_filter,Finset.mem_product] at hp
    rw [Finset.mem_filter]; exact ⟨hp.1.1.1,by omega⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_coe] at hp₁ hp₂
    simp only [P1,Finset.mem_filter] at hp₁ hp₂
    exact Prod.ext heq (hp₁.2.trans hp₂.2.symm)
  · intro i hi
    rw [Finset.mem_coe,Finset.mem_filter] at hi
    refine ⟨(i,h),Finset.mem_coe.mpr ?_,rfl⟩
    simp only [P1,P,Finset.mem_filter,Finset.mem_product]
    exact ⟨⟨⟨hi.1,Finset.mem_range.mpr hh⟩,hi.2⟩,trivial⟩
  · intro p hp
    simp only [P1,Finset.mem_filter] at hp
    rw [hp.2]
 have hP2:∏ p∈P2,(qk n p.2 - qk n p.1)=
  ∏ j∈R.filter (fun j=>h < j),(qk n j - qk n h):=by
  refine Finset.prod_nbij Prod.snd ?_ ?_ ?_ ?_
  · intro p hp
    simp only [P2,P,Finset.mem_filter,Finset.mem_product] at hp
    rw [Finset.mem_filter]; exact ⟨hp.1.1.2,by omega⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_coe] at hp₁ hp₂
    simp only [P2,Finset.mem_filter] at hp₁ hp₂
    exact Prod.ext (hp₁.2.trans hp₂.2.symm) heq
  · intro j hj
    rw [Finset.mem_coe,Finset.mem_filter] at hj
    refine ⟨(h,j),Finset.mem_coe.mpr ?_,rfl⟩
    simp only [P2,P,Finset.mem_filter,Finset.mem_product]
    exact ⟨⟨⟨Finset.mem_range.mpr hh,hj.1⟩,hj.2⟩,trivial⟩
  · intro p hp
    simp only [P2,Finset.mem_filter] at hp
    rw [hp.2]
 have hP3:∏ p∈P3,(qk n p.2 - qk n p.1)=qI n h:=by
  have hP3eq:P3=((R.erase h) ×ˢ (R.erase h)).filter (fun p:ℕ×ℕ=>p.1 < p.2):=by
   ext ⟨i,j⟩
   simp only [P3,P,Finset.mem_filter,Finset.mem_product,Finset.mem_erase]
   tauto
  rw [hP3eq,Finset.prod_filter,Finset.prod_product]
  dsimp only [qI,R]
  refine Finset.prod_congr rfl fun i _=>?_
  rw [Finset.prod_filter]
 rw [hDAll,hunion,Finset.prod_union hdisj123,Finset.prod_union hdisj12,hP1,hP2,hP3]
 rfl
lemma u0 (n:ℕ):0 < vz n:=by
 have:=ke n 0 (Nat.succ_pos n)
 rw [← this]
 refine Nat.mul_pos (jY n 0) ?_
 dsimp only [qI]
 refine Finset.prod_pos fun i _=>Finset.prod_pos fun j hj=>?_
 rw [Finset.mem_filter] at hj
 have:=zg n hj.2; omega
lemma vS {ι:Type*} (s:Finset ι) (f:ι→Polynomial ℚ) (x:ℚ):
 (∑ i∈s,f i).eval x=∑ i∈s,(f i).eval x:=
 map_sum (Polynomial.evalRingHom x) f s
lemma uO {n:ℕ} (hn:0 < n) (A:Fin n→Fin n→Bool):
 ((Finset.range (n + 1)).filter (fun h=>h % 2=0)).sum
   (fun h=>ZOf A h * qR n h * qI n h)=
 ((Finset.range (n + 1)).filter (fun h=>h % 2=1)).sum
   (fun h=>ZOf A h * qR n h * qI n h) +
 vz n * 4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:=by
 classical
 let P:Polynomial ℚ:=∑ r∈Finset.range (n + 1),
  Polynomial.C ((4 ^ r * ye A r * qY (2 * n - 2 * r):ℕ):ℚ) *
   Polynomial.X ^ (n - r)
 have hPdeg:P.natDegree≤n:=by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le n,fun r _=>?_⟩
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le n r)
 have hPeval:∀ h:ℕ,P.eval (qk n h:ℚ)=(ZOf A h:ℚ):=by
  intro h
  rw [(ko hn A h).2]
  dsimp only [P]
  rw [vS,Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr=>?_
  rw [Finset.mem_range] at hr
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have h2:2 * n - 2 * r=2 * (n - r):=by omega
  rw [h2,pow_mul]
  push_cast [qk]
  ring
 have hP0:P.eval 0=((4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:ℕ):ℚ):=by
  dsimp only [P]
  rw [vS]
  rw [Finset.sum_eq_single n]
  · simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    have h0:2 * n - 2 * n=0:=by omega
    rw [Nat.sub_self n,pow_zero,mul_one,h0,kZ,mul_one,v5 A]
  · intro r hr hrn
    rw [Finset.mem_range] at hr
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    rw [zero_pow (by omega:n - r≠0),mul_zero]
  · intro hn'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn'
 let L:ℕ→Polynomial ℚ:=fun h=>
  ∏ k∈(Finset.range (n + 1)).erase h,
    Polynomial.C (((qk n h:ℚ) - (qk n k:ℚ))⁻¹) *
     (Polynomial.X - Polynomial.C (qk n k:ℚ))
 let Q:Polynomial ℚ:=∑ h∈Finset.range (n + 1),Polynomial.C (ZOf A h:ℚ) * L h
 have hLdeg:∀ h∈Finset.range (n + 1),(L h).natDegree≤n:=by
  intro h hh
  let g:ℕ→Polynomial ℚ:=fun k=>
   Polynomial.C (((qk n h:ℚ) - (qk n k:ℚ))⁻¹) *
    (Polynomial.X - Polynomial.C (qk n k:ℚ))
  have h1:∀ k∈(Finset.range (n + 1)).erase h,(g k).natDegree≤1:=by
   intro k _
   exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le _)
  have h2:(∏ k∈(Finset.range (n + 1)).erase h,g k).natDegree≤
   ∑ k∈(Finset.range (n + 1)).erase h,(g k).natDegree:=
   Polynomial.natDegree_prod_le _ g
  have h3:∑ k∈(Finset.range (n + 1)).erase h,(g k).natDegree≤
   ∑ _k∈(Finset.range (n + 1)).erase h,(1:ℕ):=
   Finset.sum_le_sum h1
  have h4:∑ _k∈(Finset.range (n + 1)).erase h,(1:ℕ)=n:=by
   rw [Finset.sum_const,smul_eq_mul,mul_one,Finset.card_erase_of_mem hh,Finset.card_range]
   omega
  exact (h2.trans h3).trans h4.le
 have hQdeg:Q.natDegree≤n:=by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  exact ⟨Nat.zero_le n,fun h hh=>(Polynomial.natDegree_C_mul_le _ _).trans (hLdeg h hh)⟩
 have hQeval:∀ j∈Finset.range (n + 1),Q.eval (qk n j:ℚ)=(ZOf A j:ℚ):=by
  intro j hj
  dsimp only [Q]
  rw [vS]
  rw [Finset.sum_eq_single j]
  · simp only [Polynomial.eval_mul,Polynomial.eval_C]
    have hL1:(L j).eval (qk n j:ℚ)=1:=by
     simp only [L,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_X]
     refine Finset.prod_eq_one fun k hk=>?_
     have hne:k≠j:=Finset.ne_of_mem_erase hk
     have hsub:(qk n j:ℚ) - (qk n k:ℚ)≠0:=by
      intro heq
      have:qk n j=qk n k:=by exact_mod_cast sub_eq_zero.mp heq
      exact hne ((zg n).injective this).symm
     exact inv_mul_cancel₀ hsub
    rw [hL1,mul_one]
  · intro h _ hhj
    simp only [Polynomial.eval_mul,Polynomial.eval_C]
    have hL0:(L h).eval (qk n j:ℚ)=0:=by
     simp only [L,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_X]
     exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hhj.symm,hj⟩) (by ring)
    rw [hL0,mul_zero]
  · intro hnj; exact absurd hj hnj
 have hPQ:P=Q:=by
  by_contra hne
  have hdiff_ne:P - Q≠0:=sub_ne_zero.mpr hne
  have hdiff_deg:(P - Q).natDegree≤n:=(Polynomial.natDegree_sub_le P Q).trans (max_le hPdeg hQdeg)
  let rootsSet:=(Finset.range (n + 1)).image (fun j=>(qk n j:ℚ))
  have hsub:rootsSet⊆(P - Q).roots.toFinset:=by
   intro x hx
   rcases Finset.mem_image.mp hx with ⟨j,hj,rfl⟩
   rw [Multiset.mem_toFinset,Polynomial.mem_roots hdiff_ne,Polynomial.IsRoot.def,
    Polynomial.eval_sub,hPeval j,hQeval j hj,sub_self]
  have hcardR:rootsSet.card=n + 1:=by
   rw [Finset.card_image_of_injective _ (fun a b hab=>
    (zg n).injective (by exact_mod_cast hab)),Finset.card_range]
  have hle1:rootsSet.card≤(P - Q).roots.toFinset.card:=Finset.card_le_card hsub
  have hle2:(P - Q).roots.toFinset.card≤(P - Q).roots.card:=Multiset.toFinset_card_le _
  have hle3:(P - Q).roots.card≤(P - Q).natDegree:=Polynomial.card_roots' (P - Q)
  omega
 have hL0:∀ h∈Finset.range (n + 1),
  (L h).eval 0 * (vz n:ℚ)=(-1:ℚ) ^ h * ((qR n h * qI n h:ℕ):ℚ):=by
  intro h hh
  have hhh:h < n + 1:=Finset.mem_range.mp hh
  have hLval:(L h).eval 0=
   ((-1:ℚ) ^ n * (qR n h:ℚ)) /
   ((-1:ℚ) ^ (n - h) * (ya n h:ℚ)):=by
   simp only [L,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_X,zero_sub]
   rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
   have hnum:∏ k∈(Finset.range (n + 1)).erase h,(-(qk n k:ℚ))=
    (-1:ℚ) ^ n * (qR n h:ℚ):=by
    have hcardE:((Finset.range (n + 1)).erase h).card=n:=by
     rw [Finset.card_erase_of_mem hh,Finset.card_range]; omega
    have h1:∏ k∈(Finset.range (n + 1)).erase h,(-(qk n k:ℚ))=
     ∏ k∈(Finset.range (n + 1)).erase h,((-1:ℚ) * (qk n k:ℚ)):=
     Finset.prod_congr rfl fun k _=>by ring
    rw [h1,Finset.prod_mul_distrib,Finset.prod_const,hcardE]
    dsimp only [qR]; push_cast; rfl
   have hden:∏ k∈(Finset.range (n + 1)).erase h,((qk n h:ℚ) - (qk n k:ℚ))=
    (-1:ℚ) ^ (n - h) * (ya n h:ℚ):=by
    let E1:=(Finset.range (n + 1)).filter (fun k=>k < h)
    let E2:=(Finset.range (n + 1)).filter (fun k=>h < k)
    have hdisj:Disjoint E1 E2:=by
     rw [Finset.disjoint_left]; intro k hk1 hk2
     simp only [E1,E2,Finset.mem_filter] at hk1 hk2; omega
    have hun:(Finset.range (n + 1)).erase h=E1 ∪ E2:=by
     ext k
     simp only [E1,E2,Finset.mem_erase,Finset.mem_union,Finset.mem_filter,Finset.mem_range]
     omega
    have hE2card:E2.card=n - h:=by
     have hE2eq:E2=(Finset.range (n - h)).image (fun t=>h + 1 + t):=by
      ext k
      simp only [E2,Finset.mem_filter,Finset.mem_range,Finset.mem_image]
      constructor
      · rintro ⟨hk1,hk2⟩; exact ⟨k - (h + 1),by omega,by omega⟩
      · rintro ⟨t,ht,rfl⟩; exact ⟨by omega,by omega⟩
     rw [hE2eq,Finset.card_image_of_injective _ (fun _ _ hab=>by omega),Finset.card_range]
    rw [hun,Finset.prod_union hdisj]
    have h1:∏ k∈E1,((qk n h:ℚ) - (qk n k:ℚ))=
     ((∏ i∈E1,(qk n h - qk n i):ℕ):ℚ):=by
     rw [Nat.cast_prod]
     refine Finset.prod_congr rfl fun i hi=>?_
     rw [Finset.mem_filter] at hi
     have hlt:=zg n hi.2
     rw [Nat.cast_sub (le_of_lt hlt)]
    have h2:∏ k∈E2,((qk n h:ℚ) - (qk n k:ℚ))=
     (-1:ℚ) ^ (n - h) * ((∏ j∈E2,(qk n j - qk n h):ℕ):ℚ):=by
     calc ∏ k∈E2,((qk n h:ℚ) - (qk n k:ℚ))
      =∏ k∈E2,((-1:ℚ) * ((qk n k:ℚ) - (qk n h:ℚ))):=
       Finset.prod_congr rfl fun k _=>by ring
      _=(-1:ℚ) ^ (n - h) * ∏ k∈E2,((qk n k:ℚ) - (qk n h:ℚ)):=by
        rw [Finset.prod_mul_distrib,Finset.prod_const,hE2card]
      _=(-1:ℚ) ^ (n - h) * ((∏ j∈E2,(qk n j - qk n h):ℕ):ℚ):=by
        congr 1
        rw [Nat.cast_prod]
        refine Finset.prod_congr rfl fun j hj=>?_
        rw [Finset.mem_filter] at hj
        have hlt:=zg n hj.2
        rw [Nat.cast_sub (le_of_lt hlt)]
    rw [h1,h2]
    dsimp only [ya,E1,E2]
    push_cast; ring
   rw [hnum,hden,div_eq_inv_mul]
  rw [hLval,← ke n h hhh]
  have hDne:(ya n h:ℚ)≠0:=by exact_mod_cast (jY n h).ne'
  have hsign:(-1:ℚ) ^ n / (-1:ℚ) ^ (n - h)=(-1:ℚ) ^ h:=by
   have hne1:(-1:ℚ) ^ (n - h)≠0:=pow_ne_zero _ (by norm_num)
   have hpow:(-1:ℚ) ^ n=(-1:ℚ) ^ (n - h) * (-1:ℚ) ^ h:=by
    rw [← pow_add,show n - h + h=n by omega]
   rw [hpow,mul_div_cancel_left₀ _ hne1]
  push_cast
  calc ((-1:ℚ) ^ n * (qR n h:ℚ)) / ((-1:ℚ) ^ (n - h) * (ya n h:ℚ)) *
        ((ya n h:ℚ) * (qI n h:ℚ))
   =((-1:ℚ) ^ n / (-1:ℚ) ^ (n - h)) *
    ((ya n h:ℚ) / (ya n h:ℚ)) * (qR n h:ℚ) * (qI n h:ℚ):=by ring
   _=(-1:ℚ) ^ h * ((qR n h:ℚ) * (qI n h:ℚ)):=by
     rw [hsign,div_self hDne]; ring
 have hQ0:(Q.eval 0) * (vz n:ℚ)=
  ∑ h∈Finset.range (n + 1),(-1:ℚ) ^ h * ((ZOf A h * qR n h * qI n h:ℕ):ℚ):=by
  dsimp only [Q]
  rw [vS,Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh=>?_
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  rw [mul_assoc,hL0 h hh]
  push_cast; ring
 have hEqQ:((vz n * 4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:ℕ):ℚ)=
  ∑ h∈Finset.range (n + 1),(-1:ℚ) ^ h * ((ZOf A h * qR n h * qI n h:ℕ):ℚ):=by
  rw [← hQ0,← hPQ,hP0]; push_cast; ring
 have hsplit:∑ h∈Finset.range (n + 1),
       (-1:ℚ) ^ h * ((ZOf A h * qR n h * qI n h:ℕ):ℚ)=
  ((((Finset.range (n + 1)).filter (fun h=>h % 2=0)).sum
    (fun h=>ZOf A h * qR n h * qI n h):ℕ):ℚ) -
  ((((Finset.range (n + 1)).filter (fun h=>h % 2=1)).sum
    (fun h=>ZOf A h * qR n h * qI n h):ℕ):ℚ):=by
  have hdisj:Disjoint ((Finset.range (n + 1)).filter (fun h=>h % 2=0))
   ((Finset.range (n + 1)).filter (fun h=>h % 2=1)):=by
   rw [Finset.disjoint_left]; intro h h1 h2
   simp only [Finset.mem_filter] at h1 h2; omega
  have hun:Finset.range (n + 1)=
   (Finset.range (n + 1)).filter (fun h=>h % 2=0) ∪
   (Finset.range (n + 1)).filter (fun h=>h % 2=1):=by
   ext h; simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_range]; omega
  conv_lhs=>rw [hun]
  rw [Finset.sum_union hdisj,Nat.cast_sum,Nat.cast_sum,sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun h hh=>?_
    rw [Finset.mem_filter] at hh
    have hev:Even h:=Nat.even_iff.mpr hh.2
    rw [hev.neg_one_pow,one_mul]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h hh=>?_
    rw [Finset.mem_filter] at hh
    have hodd:Odd h:=Nat.odd_iff.mpr hh.2
    rw [hodd.neg_one_pow]; ring
 rw [hsplit] at hEqQ
 have hQeq:((((Finset.range (n + 1)).filter (fun h=>h % 2=0)).sum
  (fun h=>ZOf A h * qR n h * qI n h):ℕ):ℚ)=
  ((((Finset.range (n + 1)).filter (fun h=>h % 2=1)).sum
    (fun h=>ZOf A h * qR n h * qI n h) +
  vz n * 4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:ℕ):ℚ):=by
  rw [Nat.cast_add]; linarith
 exact_mod_cast hQeq
def vs (m x:ℕ):ℕ:=if x % 2=0 then x / 2 else (x + m) / 2
lemma wO {m x:ℕ} (hodd:Odd m) (hx:x < m):
 vs m x < m∧2 * vs m x ≡ x [MOD m]:=by
 dsimp only [vs]
 have hm1:m % 2=1:=Nat.odd_iff.mp hodd
 split_ifs with he
 · refine ⟨by omega,?_⟩
   rw [show 2 * (x / 2)=x by omega]
 · refine ⟨by omega,?_⟩
   rw [show 2 * ((x + m) / 2)=x + m by omega]
   exact Nat.ModEq.symm (by rw [Nat.ModEq,Nat.add_mod_right])
lemma wN {m x:ℕ} (hodd:Odd m) (hx:x < m) (k:ℕ):
 (vs m)^[k] x < m∧2 ^ k * (vs m)^[k] x ≡ x [MOD m]:=by
 induction k with
 | zero=>exact ⟨hx,by simp; rfl⟩
 | succ k ih=>
   rw [Function.iterate_succ_apply']
   obtain ⟨hlt,hmod⟩:=wO hodd ih.1
   refine ⟨hlt,?_⟩
   rw [pow_succ,mul_assoc]
   exact (Nat.ModEq.mul_left (2 ^ k) hmod).trans ih.2
lemma jq {n d P:ℕ} (hd:1 < d) (hodd:Odd d):
 (vs (d ^ 2))^[2 * n] ((4 ^ n * P) % (d ^ 2))=P % (d ^ 2):=by
 have hodd2:Odd (d ^ 2):=hodd.pow
 have hmpos:0 < d ^ 2:=by nlinarith
 obtain ⟨hlt,hmod⟩:=wN hodd2 (Nat.mod_lt _ hmpos) (2 * n)
 have h2pow:2 ^ (2 * n)=4 ^ n:=by rw [pow_mul]; norm_num
 rw [h2pow] at hmod
 have hmod2:4 ^ n * (vs (d ^ 2))^[2 * n] ((4 ^ n * P) % (d ^ 2)) ≡ 4 ^ n * P [MOD d ^ 2]:=
  hmod.trans (Nat.mod_modEq _ _)
 have hcop2:Nat.Coprime 2 (d ^ 2):=by
  rw [Nat.coprime_two_left]; exact hodd2
 have hcop4:Nat.Coprime (4 ^ n) (d ^ 2):=by
  rw [← h2pow]; exact hcop2.pow_left _
 have hcancel:=Nat.ModEq.cancel_left_of_coprime hcop4.symm hmod2
 rw [Nat.ModEq,Nat.mod_eq_of_lt hlt] at hcancel
 exact hcancel
end qg
noncomputable section
open Classical
open PEqualNP.Library Lib.qz Lib.z9 Lib.qz.Rev
abbrev qe (f:List Bool→List Bool):Prop:=
 ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
def q22 {K:Type} {Γ:K→Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→Set (Σ k,Γ k)
 | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k)) ∪ q22 q
 | .peek _ _ q=>q22 q
 | .pop _ _ q=>q22 q
 | .load _ q=>q22 q
 | .branch _ q₁ q₂=>q22 q₁ ∪ q22 q₂
 | .goto _=>∅
 | .halt=>∅
lemma qdC {K:Type} {Γ:K→Type} {Λ σ:Type} [Finite σ]
 (q:Turing.TM2.Stmt Γ Λ σ):(q22 q).Finite:=by
 induction q with
 | push _ _ _ ih=>exact (Set.finite_range _).union ih
 | peek _ _ _ ih=>exact ih
 | pop _ _ _ ih=>exact ih
 | load _ _ ih=>exact ih
 | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
 | goto _=>exact Set.finite_empty
 | halt=>exact Set.finite_empty
def q29 {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
    (T:∀ k,Set (Γ k)):
    ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→s∈T k)→
    Turing.TM2.Stmt (fun k=>{s:Γ k // s∈T k}) Λ σ
 | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
     (q29 T q (fun j s hs=>h j s (Or.inr hs)))
 | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
 | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (q29 T q h)
 | .load a q,h=>.load a (q29 T q h)
 | .branch f q₁ q₂,h=>.branch f
     (q29 T q₁ (fun j s hs=>h j s (Or.inl hs)))
     (q29 T q₂ (fun j s hs=>h j s (Or.inr hs)))
 | .goto f,_=>.goto f
 | .halt,_=>.halt
def q67 {K:Type} {Γ:K→Type} {Λ σ:Type} (T:∀ k,Set (Γ k))
    (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ:=
 ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
lemma qdR {K:Type} {Γ:K→Type} {Λ σ:Type} (T:∀ k,Set (Γ k)):
 Function.Injective (q67 (Λ:=Λ) (σ:=σ) T):=by
 rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
 simp only [q67,Turing.TM2.Cfg.mk.injEq] at h
 obtain ⟨rfl,rfl,hS⟩:=h
 congr 1
 funext k
 exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
lemma q84 {K:Type} [DecidableEq K] {Γ:K→Type} (T:∀ k,Set (Γ k))
 (S:∀ k,List {s:Γ k // s∈T k}) (k:K) (l:List {s:Γ k // s∈T k}):
 (fun j=>(Function.update S k l j).map Subtype.val)=
   Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
 funext j
 by_cases h:j=k
 · subst h;simp
 · simp [h]
lemma qdF {K:Type} [DecidableEq K] {Γ:K→Type} {Λ σ:Type}
 (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
 (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈q22 q→s∈T k)
 (v:σ) (S:∀ k,List {s:Γ k // s∈T k}):
 q67 T (Turing.TM2.stepAux (q29 T q hq) v S)=
  Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
 induction q generalizing v S with
 | push k g q ih=>
   simp only [q29,Turing.TM2.stepAux]
   rw [ih,q84];rfl
 | peek k f q ih=>
   simp only [q29,Turing.TM2.stepAux]
   exact (ih hq _ _).trans (by rw [List.head?_map])
 | pop k f q ih=>
   simp only [q29,Turing.TM2.stepAux]
   exact (ih hq _ _).trans (by rw [q84,List.head?_map,List.map_tail])
 | load a q ih=>
   simp only [q29,Turing.TM2.stepAux]
   exact ih hq (a v) S
 | branch f q₁ q₂ ih₁ ih₂=>
   simp only [q29,Turing.TM2.stepAux]
   cases f v
   · exact ih₂ _ v S
   · exact ih₁ _ v S
 | goto f=>rfl
 | halt=>rfl
lemma kr {f:List Bool→List Bool} (hf:qe f):
 ∃ M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f,
   ∀ i,Finite (M.tm.Γ i):=by
 classical
 obtain ⟨c⟩:=hf
 let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
 let _:Fintype c.tm.K:=c.tm.kFin
 let _:Fintype c.tm.Λ:=c.tm.ΛFin
 let _:Fintype c.tm.σ:=c.tm.σFin
 let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
 let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k=>
  {s | k=c.tm.k₀∨k=c.tm.k₁∨(⟨k,s⟩:Σ j,c.tm.Γ j)∈⋃ l:c.tm.Λ,q22 (c.tm.m l)}
 let e₀:{s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀:=
  { toFun:=Subtype.val
    invFun:=fun s=>⟨s,Or.inl rfl⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
 let e₁:{s:c.tm.Γ c.tm.k₁ // s∈T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁:=
  { toFun:=Subtype.val
    invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
 let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s∈T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
 let tm':Turing.FinTM2:=
  { K:=c.tm.K
    kDecidableEq:=c.tm.kDecidableEq
    kFin:=c.tm.kFin
    k₀:=c.tm.k₀
    k₁:=c.tm.k₁
    Γ:=fun k=>{s:c.tm.Γ k // s∈T k}
    Λ:=c.tm.Λ
    main:=c.tm.main
    ΛFin:=c.tm.ΛFin
    σ:=c.tm.σ
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
    · have hUfin:(⋃ l:c.tm.Λ,q22 (c.tm.m l)).Finite:=
       Set.finite_iUnion fun l=>qdC (c.tm.m l)
      have:Finite ↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)):=hUfin.to_subtype
      refine Finite.of_injective (f:=fun x:tm'.Γ j=>
       (⟨⟨j,x.1⟩,by
         rcases x.2 with h | h | h
         · exact (h0 h).elim
         · exact (h1 h).elim
         · exact h⟩:↥(⋃ l:c.tm.Λ,q22 (c.tm.m l)))) ?_
      intro x y hxy
      have h1':=congrArg (fun z=>z.1) hxy
      exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
 have hstep:∀ cfg:tm'.Cfg,Option.map (q67 T) (tm'.step cfg)=c.tm.step (q67 T cfg):=by
  rintro ⟨l,v,S⟩
  cases l with
  | none=>rfl
  | some l=>
    change some (q67 T (Turing.TM2.stepAux (q29 T (c.tm.m l) _) v S))=
     some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
    exact congrArg some (qdF T (c.tm.m l) _ v S)
 have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
  Option.map (q67 T) ((flip bind tm'.step)^[steps] (some cfg))=
   (flip bind c.tm.step)^[steps] (some (q67 T cfg)):=by
  intro steps
  induction steps with
  | zero=>intro cfg;rfl
  | succ steps ih=>
    intro cfg
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
    | none=>
      have hih:=ih cfg
      rw [hcur] at hih
      rw [← hih];rfl
    | some cfg'=>
      have hih:=ih cfg
      rw [hcur] at hih
      rw [← hih]
      exact hstep cfg'
 let M:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f:=
  { tm:=tm'
    inputAlphabet:=e₀.trans c.inputAlphabet
    outputAlphabet:=e₁.trans c.outputAlphabet
    time:=c.time
    outputsFun:=fun a=>
     { steps:=(c.outputsFun a).steps
       evals_in_steps:=by
        have horig:=(c.outputsFun a).evals_in_steps
        have hinit:q67 T (Turing.initList tm' (a.map (e₀.trans c.inputAlphabet).invFun))=
         Turing.initList c.tm (a.map c.inputAlphabet.invFun):=by
         simp only [q67,Turing.initList]
         congr 1;funext k
         by_cases hk:k=c.tm.k₀
         · subst hk;dsimp only [tm']
           simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
         · dsimp only [tm']
           simp only [hk,↓reduceDIte,List.map_nil]
        have hhalt:q67 T (Turing.haltList tm' ((f a).map (e₁.trans c.outputAlphabet).invFun))=
         Turing.haltList c.tm ((f a).map c.outputAlphabet.invFun):=by
         simp only [q67,Turing.haltList]
         congr 1;funext k
         by_cases hk:k=c.tm.k₁
         · subst hk;dsimp only [tm']
           simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map];rfl
         · dsimp only [tm']
           simp only [hk,↓reduceDIte,List.map_nil]
        apply Option.map_injective (qdR T)
        rw [hiter,hinit,horig]
        exact (congrArg some hhalt).symm
       steps_le_m:=(c.outputsFun a).steps_le_m } }
 exact ⟨M,hFin⟩
lemma q39 {f g:List Bool→List Bool} (hf:qe f) (h:∀ x,f x=g x):qe g:=by
 have:f=g:=funext h
 rwa [← this]
lemma w2:qe (fun s:List Bool=>s.reverse):=⟨Rev.uR⟩
lemma qbK {g cnt arg:List Bool→List Bool} (k:ℕ)
 (hg:qe g) (hgl:∀ s,(g s).length≤ s.length+k)
 (hcnt:qe cnt) (harg:qe arg):
 qe (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>g^[p.2.length] p.1):=
  y1.vT g c k hgl
 exact q39 (qa (vn harg hcnt) hI) (fun _=>rfl)
lemma qd4 {g cnt arg:List Bool→List Bool}
 (m:List Bool→ℕ) (a:ℕ)
 (hg:qe g)
 (hm:∀ y,m (g y)≤ m y)
 (hgl:∀ y,(g y).length≤y.length+m y)
 (ha:∀ y,m y≤a * y.length+a)
 (hcnt:qe cnt) (harg:qe arg):
 qe (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
  (fun p:List Bool×List Bool=>g^[p.2.length] p.1):=
  y1.vj g c m a hm hgl ha
 exact q39 (qa (vn harg hcnt) hI) (fun _=>rfl)
lemma q7 (a b:List Bool):(qc a b).length=2 * a.length+b.length+1:=by
 simp [qc,un];omega
lemma q0 (y:List Bool):
 2 * (unpairB y).1.length+(unpairB y).2.length≤y.length:=by
 dsimp only [unpairB]
 have hsplit:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
 have hylen:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
  conv_lhs=>rw [hsplit]
  exact List.length_append
 set a:=(y.takeWhile id).length
 set t:=(y.dropWhile id).tail
 have htlen:t.length≤(y.dropWhile id).length:=by
  dsimp only [t];cases y.dropWhile id <;> simp
 have htake:(t.take a).length=min a t.length:=List.length_take
 have hdrop:(t.drop a).length=t.length - a:=List.length_drop
 omega
lemma q18 {g cnt arg:List Bool→List Bool} (c:ℕ)
 (hg:qe g)
 (hw:∀ y,(unpairB (g y)).1=(unpairB y).1)
 (hgl:∀ y,(g y).length≤y.length+c * (unpairB y).1.length+c)
 (hcnt:qe cnt) (harg:qe arg):
 qe (fun s=>g^[(cnt s).length] (arg s)):=by
 refine qd4 (fun y=>c * (unpairB y).1.length+c) c hg
  (fun y=>by rw [hw y])
  (fun y=>by have:=hgl y;omega)
  (fun y=>by
    have h1:(unpairB y).1.length≤y.length:=by have:=q0 y;omega
    have h2:=Nat.mul_le_mul_left c h1
    omega)
  hcnt harg
def q47 (s:List Bool):List Bool:=List.replicate s.length true
lemma qbO (s:List Bool):(q47 s).length=s.length:=List.length_replicate
lemma q89:qe q47:=
 qK _ _ _ (fun (_:Unit) (_:Bool)=>((),some true)) (fun _=>none) () (fun s=>by
  induction s with
  | nil=>rfl
  | cons b l ih=>simp only [ql,q47,List.length_cons,List.replicate_succ];exact congrArg (true::·) ih)
def q79 (s:List Bool):List Bool:=
 qc (unpairB s).1 ((unpairB s).2++(unpairB s).1)
lemma qdN:qe q79:=
 qd qf (qi qb qf)
lemma q99 (a:List Bool):∀ k b,q79^[k] (qc (q47 a) b)=qc (q47 a) (b++un (k * a.length))
 | 0,b=>by simp [un]
 | k+1,b=>by
   rw [Function.iterate_succ_apply,q79,qj,q99 a k (b++q47 a)]
   congr 1
   simp [q47,un,List.append_assoc,← List.replicate_add,Nat.succ_mul,Nat.add_comm]
lemma q42 {u v:List Bool→List Bool} (hu:qe u) (hv:qe v):
 qe (fun s=>qJ (u s) (v s)):=by
 have h1:qe (fun s=>q79^[(u s).length] (qc (q47 (v s)) [])):=
  q18 1 qdN (fun y=>by rw [q79,qj])
   (fun y=>by
     rw [q79,q7,List.length_append]
     have:=q0 y
     omega)
   hu (qd (qa hv q89) (qh []))
 have h2:=qa h1 qb
 have heq:(fun s=>(unpairB (q79^[(u s).length] (qc (q47 (v s)) []))).2)=(fun s=>qJ (u s) (v s)):=by
  funext s
  rw [q99,qj,List.nil_append];rfl
 rwa [heq] at h2
def q17 (s:List Bool):List Bool:=
 match s with
 | true::_=>[true]
 | _=>[]
lemma q35:qe q17:=
 qK _ _ _
  (fun (st:Bool) (b:Bool)=>if st then (false,if b then some true else none) else (false,none))
  (fun _=>none) true (fun s=>by
    have hfalse:∀ l,ql (fun (st:Bool) (b:Bool)=>
     if st then (false,if b then some true else none) else (false,none))
     (fun _=>none) false l=[]:=by
     intro l;induction l with | nil=>rfl | cons b l ih=>simp [ql,ih]
    cases s with
    | nil=>rfl
    | cons b l=>cases b <;> simp [ql,q17,hfalse])
def q133 (s:List Bool):List Bool:=sel s [true] []
lemma qbL:qe q133:=
 zh wD (qh [true]) (qh [])
def zj (lenU xs:List Bool):List Bool:=
 (unpairB (q47 lenU++false::xs)).1
def vN (lenU xs:List Bool):List Bool:=
 (unpairB (q47 lenU++false::xs)).2
lemma q12 (lenU xs:List Bool):zj lenU xs=xs.take lenU.length:=by
 have h1:(q47 lenU++false::xs).takeWhile id=q47 lenU:=by
  simp [q47]
 have h2:(q47 lenU++false::xs).dropWhile id=false::xs:=by
  simp [q47]
 simp [zj,unpairB,h1,h2,qbO]
lemma q40 (lenU xs:List Bool):vN lenU xs=xs.drop lenU.length:=by
 have h1:(q47 lenU++false::xs).takeWhile id=q47 lenU:=by
  simp [q47]
 have h2:(q47 lenU++false::xs).dropWhile id=false::xs:=by
  simp [q47]
 simp [vN,unpairB,h1,h2,qbO]
lemma q24 {u v:List Bool→List Bool} (hu:qe u) (hv:qe v):
 qe (fun s=>zj (u s) (v s)):=
 q39 (qa (qi (qa hu q89) (qi (qh [false]) hv)) qf) (fun _=>rfl)
lemma yS {u v:List Bool→List Bool} (hu:qe u) (hv:qe v):
 qe (fun s=>vN (u s) (v s)):=
 q39 (qa (qi (qa hu q89) (qi (qh [false]) hv)) qb) (fun _=>rfl)
def q23 (xs:List Bool):List Bool:=
 xs.flatMap (fun b=>[true,b])++[false]
lemma qex:qe q23:=
 yM _ _ _ (fun (_:Unit) (b:Bool)=>((),some true,some b))
  (fun _=>some false) () (fun s=>by
    induction s with
    | nil=>rfl
    | cons b l ih=>simp [zB,q23] at ih ⊢;exact ih)
def q15:Option Bool→List Bool→List Bool
 | none,_=>[]
 | some false,true::r=>q15 (some true) r
 | some false,false::_=>[]
 | some false,[]=>[]
 | some true,b::r=>b::q15 (some false) r
 | some true,[]=>[]
def q75 (s:List Bool):List Bool:=q15 (some false) s
def q10:Option Bool→List Bool→List Bool
 | none,r=>r
 | some false,true::r=>q10 (some true) r
 | some false,false::r=>r
 | some false,[]=>[]
 | some true,_::r=>q10 (some false) r
 | some true,[]=>[]
def q43 (s:List Bool):List Bool:=q10 (some false) s
lemma qbI (xs rest:List Bool):
 q75 (q23 xs++rest)=xs:=by
 dsimp only [q75,q23]
 induction xs with
 | nil=>rfl
 | cons b l ih=>simp only [List.flatMap_cons,List.cons_append,List.nil_append,q15];exact congrArg (b::·) ih
lemma qdy (xs rest:List Bool):
 q43 (q23 xs++rest)=rest:=by
 dsimp only [q43,q23]
 induction xs with
 | nil=>rfl
 | cons b l ih=>simp only [List.flatMap_cons,List.cons_append,List.nil_append,q10];exact ih
lemma q91 (s:List Bool):(q43 s).length≤ s.length:=by
 have h:∀ st l,(q10 st l).length≤l.length:=by
  intro st l
  induction l generalizing st with
  | nil=>
    cases st with
    | none=>simp [q10]
    | some f=>cases f <;> simp [q10]
  | cons b r ih=>
    cases st with
    | none=>simp [q10]
    | some f=>
      cases f with
      | false=>
        cases b <;> simp only [q10,List.length_cons]
        · omega
        · have:=ih (some true);omega
      | true=>
        simp only [q10,List.length_cons]
        have:=ih (some false);omega
 exact h (some false) s
lemma qdH:qe q75:=by
 let δ:Option Bool→Bool→Option Bool×Option Bool:=fun st b=>
  match st,b with
  | none,_=>(none,none)
  | some false,true=>(some true,none)
  | some false,false=>(none,none)
  | some true,b=>(some false,some b)
 refine qK _ _ _ δ (fun _=>none) (some false) fun s=>?_
 have hnone:∀ l,ql δ (fun _=>none) none l=[]:=by
  intro l;induction l with | nil=>rfl | cons b l ih=>simp [ql,δ,ih]
 have haux:∀ st l,ql δ (fun _=>none) st l=q15 st l:=by
  intro st l
  induction l generalizing st with
  | nil=>cases st with | none=>rfl | some f=>cases f <;> rfl
  | cons b r ih=>
    cases st with
    | none=>simp [ql,δ,hnone,q15]
    | some f=>
      cases f with
      | false=>cases b <;> simp [ql,δ,q15,ih]
      | true=>simp [ql,δ,q15,ih]
 exact (haux (some false) s).symm
lemma qdG:qe q43:=by
 let δ:Option Bool→Bool→Option Bool×Option Bool:=fun st b=>
  match st,b with
  | none,b=>(none,some b)
  | some false,true=>(some true,none)
  | some false,false=>(none,none)
  | some true,_=>(some false,none)
 refine qK _ _ _ δ (fun _=>none) (some false) fun s=>?_
 have hnone:∀ l,ql δ (fun _=>none) none l=l:=by
  intro l;induction l with | nil=>rfl | cons b l ih=>simp [ql,δ,ih]
 have haux:∀ st l,ql δ (fun _=>none) st l=q10 st l:=by
  intro st l
  induction l generalizing st with
  | nil=>cases st with | none=>rfl | some f=>cases f <;> rfl
  | cons b r ih=>
    cases st with
    | none=>simp [ql,δ,hnone,q10]
    | some f=>
      cases f with
      | false=>cases b <;> simp [ql,δ,q10,ih]
      | true=>simp [ql,δ,q10,ih]
 exact (haux (some false) s).symm
def val:List Bool→ℕ
 | []=>0
 | b::l=>b.toNat+2 * val l
lemma kQ (l:List Bool):val l < 2 ^ l.length:=by
 induction l with
 | nil=>simp [val]
 | cons b l ih=>
   simp only [val,List.length_cons,pow_succ]
   cases b <;> simp <;> omega
lemma q58 (a b:List Bool):val (a++b)=val a+2 ^ a.length * val b:=by
 induction a with
 | nil=>simp [val]
 | cons x l ih=>
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
lemma qaB (k:ℕ) (l:List Bool):val (l.take k)=val l % 2 ^ k:=by
 induction k generalizing l with
 | zero=>simp [val,Nat.mod_one]
 | succ k ih=>
   cases l with
   | nil=>simp [val]
   | cons b r=>
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
lemma w3 (n:ℕ):val n.bits=n:=by
 induction n using Nat.binaryRec with
 | zero=>simp [val]
 | bit b m ih=>
   by_cases h:b=false∧m=0
   · rcases h with ⟨rfl,rfl⟩;simp [val]
   · rw [Nat.bits_append_bit m b (fun hm=>by subst hm;cases b <;> simp_all)]
     simp only [val,ih,Nat.bit]
     cases b <;> simp <;> omega
lemma qdP (k:ℕ) (hk:0 < k):k.bits.length=k.log2+1:=by
 induction k using Nat.strong_induction_on with
 | ind k ih=>
   by_cases h2:k < 2
   · have hk1:k=1:=by omega
     subst hk1;decide
   · have hdiv_pos:0 < k / 2:=by omega
     have hdiv_lt:k / 2 < k:=Nat.div_lt_self hk (by omega)
     have hlog:k.log2=(k / 2).log2+1:=by
      rw [Nat.log2_def];simp [show 2≤k by omega]
     have hbits:k.bits=(decide (k % 2=1))::(k / 2).bits:=by
      have hdecomp:k=Nat.bit (decide (k % 2=1)) (k / 2):=by
       cases hmod:k % 2 with
       | zero=>simp [Nat.bit];omega
       | succ r=>
         have hr:r=0:=by omega
         subst hr;simp [Nat.bit];omega
      conv_lhs=>rw [hdecomp]
      rw [Nat.bits_append_bit (k / 2) (decide (k % 2=1)) (fun h0=>by omega)]
     rw [hbits,List.length_cons,ih (k / 2) hdiv_lt hdiv_pos,hlog]
lemma q78 (z h:ℕ):z.testBit h=z.bits.getD h false:=by
 induction h generalizing z with
 | zero=>
   by_cases hz:z=0
   · subst hz;simp
   · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
      cases hmod:z % 2 with
      | zero=>simp [Nat.bit];omega
      | succ r=>
        have hr:r=0:=by omega
        subst hr;simp [Nat.bit];omega
     have hbits:z.bits=(decide (z % 2=1))::(z / 2).bits:=by
      conv_lhs=>rw [hdecomp]
      refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0=>?_
      have hmod1:z % 2=1:=by omega
      simp [hmod1]
     rw [hbits]
     simp [Nat.testBit_zero]
 | succ h ih=>
   by_cases hz:z=0
   · subst hz;simp
   · have hdecomp:z=Nat.bit (decide (z % 2=1)) (z / 2):=by
      cases hmod:z % 2 with
      | zero=>simp [Nat.bit];omega
      | succ r=>
        have hr:r=0:=by omega
        subst hr;simp [Nat.bit];omega
     have hbits:z.bits=(decide (z % 2=1))::(z / 2).bits:=by
      conv_lhs=>rw [hdecomp]
      refine Nat.bits_append_bit (z / 2) (decide (z % 2=1)) fun h0=>?_
      have hmod1:z % 2=1:=by omega
      simp [hmod1]
     rw [hbits,List.getD_cons_succ,← ih (z / 2),Nat.testBit_succ]
def q28:List Bool→List Bool
 | []=>[true]
 | false::l=>true::l
 | true::l=>false::q28 l
lemma qdS (l:List Bool):val (q28 l)=val l+1:=by
 induction l with
 | nil=>simp [q28,val]
 | cons b l ih=>cases b <;> simp [q28,val,ih] <;> omega
lemma qdT (l:List Bool):(q28 l).length≤l.length+1:=by
 induction l with
 | nil=>simp [q28]
 | cons b l ih=>cases b <;> simp [q28] <;> omega
lemma qdM (n:ℕ):q28 n.bits=(n+1).bits:=by
 induction n using Nat.binaryRec with
 | zero=>decide
 | bit b m ih=>
   cases b with
   | false=>
     by_cases hm:m=0
     · subst hm;decide
     · have h1:(Nat.bit false m).bits=false::m.bits:=
        Nat.bits_append_bit m false (fun h=>(hm h).elim)
       have h2:Nat.bit false m+1=Nat.bit true m:=by simp [Nat.bit]
       have h3:(Nat.bit true m).bits=true::m.bits:=
        Nat.bits_append_bit m true (fun _=>by simp)
       rw [h1,h2,h3,q28]
   | true=>
     have h1:(Nat.bit true m).bits=true::m.bits:=
      Nat.bits_append_bit m true (fun _=>by simp)
     have h2:Nat.bit true m+1=Nat.bit false (m+1):=by simp [Nat.bit];omega
     have h3:(Nat.bit false (m+1)).bits=false::(m+1).bits:=
      Nat.bits_append_bit (m+1) false (fun h=>by omega)
     rw [h1,h2,h3,q28,ih]
lemma qbM:qe q28:=by
 let δ:Bool→Bool→Bool×Option Bool:=fun c b=>
  match c,b with
  | false,b=>(false,some b)
  | true,false=>(false,some true)
  | true,true=>(true,some false)
 let fin:Bool→Option Bool:=fun c=>if c then some true else none
 refine qK _ _ _ δ fin true fun s=>?_
 have hfalse:∀ l,ql δ fin false l=l:=by
  intro l;induction l with | nil=>rfl | cons b r ih=>simp [ql,δ,fin,ih]
 have htrue:∀ l,ql δ fin true l=q28 l:=by
  intro l
  induction l with
  | nil=>rfl
  | cons b r ih=>cases b <;> simp [ql,δ,fin,q28,hfalse,ih]
 exact (htrue s).symm
def q48 (u:List Bool):List Bool:=q28^[u.length] []
lemma q71 (u:List Bool):q48 u=u.length.bits:=by
 dsimp only [q48]
 have h:∀ k,q28^[k] []=k.bits:=by
  intro k
  induction k with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply',ih,qdM]
 exact h u.length
lemma q41:qe q48:=
 qbK 1 qbM qdT wD (qh [])
def z6 (kU zU:List Bool):List Bool:=
 zj (q48 kU) (q48 zU++blank (q48 kU))
lemma q61 {uk uz:List Bool→List Bool} (hk:qe uk) (hz:qe uz):
 qe (fun s=>z6 (uk s) (uz s)):=
 q24 (qa hk q41)
  (qi (qa hz q41) (qa (qa hk q41) kh))
lemma q86 (k z:ℕ) (hk:0 < k):
 z6 (un k) (un z)=(List.range (k.log2+1)).map (fun h=>z.testBit h):=by
 dsimp only [z6]
 rw [q12,q71,q71,qN,qN]
 have hlen:k.bits.length=k.log2+1:=qdP k hk
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
      | cons _ r ih=>
        intro i hi
        cases i with
        | zero=>rfl
        | succ i=>exact ih i (by simpa [blank] using hi)
     rw [hbl,List.getD_eq_default _ _ (by omega)]
def qy (wU x:List Bool):List Bool:=zj wU (x++blank wU)
lemma q19 (wU x:List Bool):(qy wU x).length=wU.length:=by
 dsimp only [qy]
 rw [q12,List.length_take,List.length_append,q33]
 omega
lemma q26 (wU x:List Bool):val (qy wU x)=val x % 2 ^ wU.length:=by
 dsimp only [qy]
 rw [q12,qaB,q58,q37,mul_zero,add_zero]
lemma q30 (wU x:List Bool) (h:x.length≤wU.length):val (qy wU x)=val x:=by
 rw [q26]
 exact Nat.mod_eq_of_lt (lt_of_lt_of_le (kQ x) (Nat.pow_le_pow_right (by omega) h))
lemma q13 {uw ux:List Bool→List Bool} (hw:qe uw) (hx:qe ux):
 qe (fun s=>qy (uw s) (ux s)):=
 q24 hw (qi hx (qa hw kh))
def zz (wU u:List Bool):List Bool:=qy wU (q48 u)
lemma q54 (wU u:List Bool):(zz wU u).length=wU.length:=q19 wU _
lemma kP (wU u:List Bool):val (zz wU u)=u.length % 2 ^ wU.length:=by
 dsimp only [zz];rw [q26,q71,w3]
lemma q70 (wU u:List Bool):
 ((val (zz wU u):ℤ) ≡ (u.length:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 rw [kP]
 exact_mod_cast (Nat.mod_modEq u.length (2 ^ wU.length))
lemma q50 {uw uu:List Bool→List Bool} (hw:qe uw) (hu:qe uu):
 qe (fun s=>zz (uw s) (uu s)):=
 q13 hw (qa hu q41)
def q77 (x:List Bool):List Bool:=x.map (!·)
lemma qb2 (x:List Bool):(q77 x).length=x.length:=by simp [q77]
lemma qdZ (x:List Bool):val (q77 x)+val x+1=2 ^ x.length:=by
 induction x with
 | nil=>simp [q77,val]
 | cons b l ih=>
   simp only [q77,List.map_cons,val,List.length_cons,pow_succ] at ih ⊢
   cases b <;> simp <;> omega
lemma qd1:qe q77:=
 qK _ _ _ (fun (_:Unit) (b:Bool)=>((),some (!b))) (fun _=>none) () fun s=>by
  induction s with
  | nil=>rfl
  | cons b l ih=>simp only [ql,q77,List.map_cons];exact congrArg ((!b)::·) ih
def jM (wU x:List Bool):List Bool:=zj wU (q28 (qy wU x))
lemma qd6 (wU x:List Bool):(jM wU x).length=wU.length:=by
 dsimp only [jM];rw [q12,List.length_take]
 have h1:(qy wU x).length≤(q28 (qy wU x)).length:=by
  have:∀ l,l.length≤(q28 l).length:=by
   intro l;induction l with | nil=>simp [q28] | cons b r ih=>cases b <;> simp [q28] <;> omega
  exact this _
 rw [q19] at h1;omega
lemma qd5 (wU x:List Bool):val (jM wU x)=(val x+1) % 2 ^ wU.length:=by
 dsimp only [jM]
 rw [q12,qaB,qdS,q26,Nat.mod_add_mod]
lemma qd9 {uw ux:List Bool→List Bool} (hw:qe uw) (hx:qe ux):
 qe (fun s=>jM (uw s) (ux s)):=
 q24 hw (qa (q13 hw hx) qbM)
def jO (wU x:List Bool):List Bool:=jM wU (q77 (qy wU x))
lemma qey (wU x:List Bool):(jO wU x).length=wU.length:=qd6 wU _
lemma qdD (wU x:List Bool):
 ((val (jO wU x):ℤ) ≡ -(val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 dsimp only [jO]
 rw [qd5]
 have hnot:=qdZ (qy wU x)
 rw [q19] at hnot
 have h1:val (q77 (qy wU x))+1=2 ^ wU.length - val (qy wU x):=by omega
 have h2:((val (q77 (qy wU x))+1) % 2 ^ wU.length:ℤ) ≡
  ((val (q77 (qy wU x))+1:ℕ):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  exact_mod_cast (Nat.mod_modEq (val (q77 (qy wU x))+1) (2 ^ wU.length))
 have h3:((val (q77 (qy wU x))+1:ℕ):ℤ)+(val (qy wU x):ℤ)=(2:ℤ) ^ wU.length:=by
  exact_mod_cast (by omega:val (q77 (qy wU x))+1+val (qy wU x)=2 ^ wU.length)
 have h4:((val (qy wU x):ℕ):ℤ) ≡ (val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  rw [q26];exact_mod_cast (Nat.mod_modEq (val x) (2 ^ wU.length))
 have h5:((val (q77 (qy wU x))+1:ℕ):ℤ) ≡ -(val (qy wU x):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  rw [Int.modEq_iff_dvd]
  have:-(val (qy wU x):ℤ) - ((val (q77 (qy wU x))+1:ℕ):ℤ)=-((2:ℤ) ^ wU.length):=by linarith
  rw [this];exact dvd_neg.2 (dvd_refl _)
 exact h2.trans (h5.trans h4.neg)
lemma qdE {uw ux:List Bool→List Bool} (hw:qe uw) (hx:qe ux):
 qe (fun s=>jO (uw s) (ux s)):=
 qd9 hw (qa (q13 hw hx) qd1)
def kl (wU x:List Bool):List Bool:=zj wU (false::qy wU x)
lemma qbQ (wU x:List Bool):(kl wU x).length=wU.length:=by
 dsimp only [kl];rw [q12,List.length_take,List.length_cons,q19];omega
lemma qd2 (wU x:List Bool):val (kl wU x)=(2 * val x) % 2 ^ wU.length:=by
 dsimp only [kl]
 rw [q12,qaB,val,Bool.toNat_false,zero_add,q26,Nat.mul_mod_mod]
lemma qd3 {uw ux:List Bool→List Bool} (hw:qe uw) (hx:qe ux):
 qe (fun s=>kl (uw s) (ux s)):=
 q24 hw (qi (qh [false]) (q13 hw hx))
def q16 (f:List Bool):List Bool:=sel f [false] [true]
lemma q73 {uf:List Bool→List Bool} (hf:qe uf):
 qe (fun s=>q16 (uf s)):=
 zh hf (qh [false]) (qh [true])
def qab (a b:List Bool):List Bool:=sel a (sel b [] [true]) (sel b [true] [])
def qax (a b c:List Bool):List Bool:=
 sel a (sel b [] (sel c [] [true])) (sel b (sel c [] [true]) [true])
lemma qbT {ua ub:List Bool→List Bool} (ha:qe ua) (hb:qe ub):
 qe (fun s=>qab (ua s) (ub s)):=
 zh ha (zh hb (qh []) (qh [true])) (zh hb (qh [true]) (qh []))
lemma qd8 {ua ub uc:List Bool→List Bool} (ha:qe ua) (hb:qe ub) (hc:qe uc):
 qe (fun s=>qax (ua s) (ub s) (uc s)):=
 zh ha (zh hb (qh []) (zh hc (qh []) (qh [true])))
  (zh hb (zh hc (qh []) (qh [true])) (qh [true]))
def q123 (y:List Bool):List Bool:=
 let a:=(unpairB y).1
 let r1:=(unpairB y).2
 let b:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let c:=(unpairB r2).1
 let acc:=(unpairB r2).2
 let ba:=q17 a
 let bb:=q17 b
 let bc:=q17 c
 let sBit:=q16 (qab (qab ba bb) bc)
 let c':=qax ba bb bc
 qc a.tail (qc b.tail (qc c' (sBit++acc)))
lemma qdY (y:List Bool):(q123 y).length≤y.length+6:=by
 dsimp only [q123]
 have h1:=q0 y
 have h2:=q0 (unpairB y).2
 have h3:=q0 (unpairB (unpairB y).2).2
 rw [q7,q7,q7,List.length_append]
 have ha:(unpairB y).1.tail.length≤(unpairB y).1.length:=by cases (unpairB y).1 <;> simp
 have hb:(unpairB (unpairB y).2).1.tail.length≤(unpairB (unpairB y).2).1.length:=by
  cases (unpairB (unpairB y).2).1 <;> simp
 have hs:(q16 (qab (qab (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1))
  (q17 (unpairB (unpairB (unpairB y).2).2).1))).length=1:=by
  unfold q16 sel;split_ifs <;> rfl
 have hc:(qax (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1)
  (q17 (unpairB (unpairB (unpairB y).2).2).1)).length≤1:=by
  unfold qax sel;split_ifs <;> simp
 omega
lemma qdX:qe q123:=by
 have hA:qe (fun y=>(unpairB y).1):=qf
 have hR1:qe (fun y=>(unpairB y).2):=qb
 have hB:qe (fun y=>(unpairB (unpairB y).2).1):=q39 (qa hR1 qf) (fun _=>rfl)
 have hR2:qe (fun y=>(unpairB (unpairB y).2).2):=q39 (qa hR1 qb) (fun _=>rfl)
 have hC:qe (fun y=>(unpairB (unpairB (unpairB y).2).2).1):=q39 (qa hR2 qf) (fun _=>rfl)
 have hAcc:qe (fun y=>(unpairB (unpairB (unpairB y).2).2).2):=q39 (qa hR2 qb) (fun _=>rfl)
 have hba:=qa hA q35
 have hbb:=qa hB q35
 have hbc:=qa hC q35
 have hs:=q73 (qbT (qbT hba hbb) hbc)
 have hc':=qd8 hba hbb hbc
 exact q39 (qd (qa hA vW)
  (qd (qa hB vW) (qd hc' (qi hs hAcc)))) (fun _=>rfl)
def zM (wU a b:List Bool):List Bool:=
 let fin:=q123^[wU.length] (qc (qy wU a) (qc (qy wU b) (qc [] [])))
 (unpairB (unpairB (unpairB fin).2).2).2.reverse
lemma qdB (k:ℕ):∀ (a b:List Bool) (c:Bool) (acc:List Bool),
 a.length=k→b.length=k→
 ∃ (acc':List Bool) (c':Bool),
   q123^[k] (qc a (qc b (qc (if c then [true] else []) acc)))=
    qc [] (qc [] (qc (if c' then [true] else []) (acc'.reverse++acc)))∧
   acc'.length=k∧
   val acc'+2 ^ k * c'.toNat=val a+val b+c.toNat:=by
 induction k with
 | zero=>
   intro a b c acc ha hb
   cases a;cases b
   · exact ⟨[],c,by simp,rfl,by simp [val]⟩
   · simp at hb
   · simp at ha
 | succ k ih=>
   intro a b c acc ha hb
   cases a with
   | nil=>simp at ha
   | cons ba ar=>
     cases b with
     | nil=>simp at hb
     | cons bb br=>
       rw [Function.iterate_succ_apply]
       have hstep:q123 (qc (ba::ar) (qc (bb::br) (qc (if c then [true] else []) acc)))=
        qc ar (qc br (qc (if ((ba&&bb)||(c&&(ba||bb))) then [true] else [])
         (((xor (xor ba bb) c)::acc)))):=by
        dsimp only [q123]
        simp only [qj,List.tail_cons]
        cases ba <;> cases bb <;> cases c <;> rfl
       rw [hstep]
       obtain ⟨acc',c',hiter,hlen,hval⟩:=ih ar br ((ba&&bb)||(c&&(ba||bb)))
        ((xor (xor ba bb) c)::acc) (by simpa using ha) (by simpa using hb)
       refine ⟨(xor (xor ba bb) c)::acc',c',?_,by simp [hlen],?_⟩
       · rw [hiter];simp
       · simp only [val,pow_succ']
         have hbit:(xor (xor ba bb) c).toNat+2 * ((ba&&bb)||(c&&(ba||bb))).toNat=
          ba.toNat+bb.toNat+c.toNat:=by
          cases ba <;> cases bb <;> cases c <;> decide
         linarith
lemma qbS (wU a b:List Bool):
 (zM wU a b).length=wU.length∧val (zM wU a b)=(val a+val b) % 2 ^ wU.length:=by
 dsimp only [zM]
 obtain ⟨acc',c',hiter,hlen,hval⟩:=
  qdB wU.length (qy wU a) (qy wU b) false [] (q19 wU a) (q19 wU b)
 simp only [Bool.false_eq_true,↓reduceIte,List.append_nil,Bool.toNat_false,add_zero] at hiter hval
 rw [hiter]
 simp only [qj,List.reverse_reverse]
 refine ⟨hlen,?_⟩
 have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact kQ acc'
 have hmod1:val acc'=(val (qy wU a)+val (qy wU b)) % 2 ^ wU.length:=by
  have:val (qy wU a)+val (qy wU b)=2 ^ wU.length * c'.toNat+val acc':=by linarith
  rw [this,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt]
 rw [hmod1,q26,q26,Nat.mod_add_mod,Nat.add_mod_mod]
lemma q36 (wU a b:List Bool):(zM wU a b).length=wU.length:=(qbS wU a b).1
lemma jV (wU a b:List Bool):val (zM wU a b)=(val a+val b) % 2 ^ wU.length:=
 (qbS wU a b).2
lemma q98 (wU a b:List Bool):
 ((val (zM wU a b):ℤ) ≡ (val a:ℤ)+(val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 rw [jV];exact_mod_cast (Nat.mod_modEq (val a+val b) (2 ^ wU.length))
lemma q82 {uw ua ub:List Bool→List Bool} (hw:qe uw) (ha:qe ua) (hb:qe ub):
 qe (fun s=>zM (uw s) (ua s) (ub s)):=by
 have hfin:=qbK 6 qdX qdY hw
  (qd (q13 hw ha) (qd (q13 hw hb) (qh (qc [] []))))
 exact qa (qa (qa (qa hfin qb) qb) qb) w2
def vk (wU a b:List Bool):List Bool:=zM wU a (jO wU b)
lemma q63 (wU a b:List Bool):(vk wU a b).length=wU.length:=q36 wU _ _
lemma qbN (wU a b:List Bool):
 ((val (vk wU a b):ℤ) ≡ (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 dsimp only [vk]
 have h1:=q98 wU a (jO wU b)
 have h2:=qdD wU b
 simpa only [sub_eq_add_neg] using h1.trans (Int.ModEq.add_left _ h2)
lemma q83 (wU a b:List Bool) (ha:val a < 2 ^ wU.length) (hge:val b≤val a):
 val (vk wU a b)=val a - val b:=by
 have hmod:=qbN wU a b
 have hlt1:val (vk wU a b) < 2 ^ wU.length:=by rw [← q63 wU a b];exact kQ _
 have hlt2:val a - val b < 2 ^ wU.length:=by omega
 have hcast:((val a - val b:ℕ):ℤ)=(val a:ℤ) - (val b:ℤ):=by omega
 rw [← hcast] at hmod
 have hnat:val (vk wU a b) ≡ val a - val b [MOD 2 ^ wU.length]:=by exact_mod_cast hmod
 rw [Nat.ModEq,Nat.mod_eq_of_lt hlt1,Nat.mod_eq_of_lt hlt2] at hnat
 exact hnat
lemma qaC {uw ua ub:List Bool→List Bool} (hw:qe uw) (ha:qe ua) (hb:qe ub):
 qe (fun s=>vk (uw s) (ua s) (ub s)):=
 q82 hw ha (qdE hw hb)
def q116 (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let bRem:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let aSh:=(unpairB r2).1
 let acc:=(unpairB r2).2
 let acc':=sel (q17 bRem) (qy wU acc) (zM wU acc aSh)
 let aSh':=kl wU aSh
 qc wU (qc bRem.tail (qc aSh' acc'))
lemma qdV:qe q116:=by
 have hw:=qf
 have hr1:=qb
 have hb:=qa hr1 qf
 have hr2:=qa hr1 qb
 have ha:=qa hr2 qf
 have hacc:=qa hr2 qb
 have hacc':=zh (qa hb q35) (q13 hw hacc) (q82 hw hacc ha)
 have ha':=qd3 hw ha
 exact qd hw (qd (qa hb vW) (qd ha' hacc'))
def zy (wU a b:List Bool):List Bool:=
 let fin:=q116^[wU.length] (qc wU (qc (qy wU b) (qc (qy wU a) (blank wU))))
 (unpairB (unpairB (unpairB fin).2).2).2
lemma q32 {uw ua ub:List Bool→List Bool} (hw:qe uw) (ha:qe ua) (hb:qe ub):
 qe (fun s=>zy (uw s) (ua s) (ub s)):=by
 have hfin:=q18 4 qdV
  (fun y=>by dsimp only [q116];rw [qj])
  (fun y=>by
    dsimp only [q116]
    set wU:=(unpairB y).1;set r1:=(unpairB y).2
    set bRem:=(unpairB r1).1;set r2:=(unpairB r1).2
    set aSh:=(unpairB r2).1;set acc:=(unpairB r2).2
    have h1:2 * wU.length+r1.length≤y.length:=q0 y
    have h2:2 * bRem.length+r2.length≤r1.length:=q0 r1
    have h3:2 * aSh.length+acc.length≤r2.length:=q0 r2
    rw [q7,q7,q7,qbQ]
    have hbt:bRem.tail.length≤bRem.length:=by cases bRem <;> simp
    have hacc:(sel (q17 bRem) (qy wU acc) (zM wU acc aSh)).length=wU.length:=by
     unfold sel;split_ifs
     · exact q19 _ _
     · exact q36 _ _ _
    omega)
  hw (qd hw (qd (q13 hw hb) (qd (q13 hw ha) (qa hw kh))))
 exact q39 (qa (qa (qa hfin qb) qb) qb) (fun _=>rfl)
lemma qdz (wU:List Bool) (k:ℕ):∀ (bRem aSh acc:List Bool),
 bRem.length=k→aSh.length=wU.length→acc.length=wU.length→
 ∃ aSh' acc',
   q116^[k] (qc wU (qc bRem (qc aSh acc)))=
    qc wU (qc [] (qc aSh' acc'))∧
   acc'.length=wU.length∧
   val acc' % 2 ^ wU.length=(val acc+val aSh * val bRem) % 2 ^ wU.length:=by
 induction k with
 | zero=>
   intro bRem aSh acc hb _ hacc
   cases bRem
   · exact ⟨aSh,acc,rfl,hacc,by simp [val]⟩
   · simp at hb
 | succ k ih=>
   intro bRem aSh acc hb ha hacc
   cases bRem with
   | nil=>simp at hb
   | cons bb br=>
     rw [Function.iterate_succ_apply]
     have hstep:q116 (qc wU (qc (bb::br) (qc aSh acc)))=
      qc wU (qc br (qc (kl wU aSh) (if bb then zM wU acc aSh else qy wU acc))):=by
      dsimp only [q116]
      simp only [qj,List.tail_cons]
      cases bb <;> rfl
     rw [hstep]
     have hacc1_len:(if bb then zM wU acc aSh else qy wU acc).length=wU.length:=by
      cases bb <;> simp [q36,q19]
     obtain ⟨aSh',acc',hiter,hlen',hval'⟩:=
      ih br (kl wU aSh) (if bb then zM wU acc aSh else qy wU acc)
       (by simpa using hb) (qbQ wU aSh) hacc1_len
     refine ⟨aSh',acc',hiter,hlen',?_⟩
     rw [hval',qd2]
     have hmod1:val (if bb then zM wU acc aSh else qy wU acc) ≡
      val acc+val aSh * bb.toNat [MOD 2 ^ wU.length]:=by
      cases bb with
      | false=>
        simp only [Bool.false_eq_true,↓reduceIte,Bool.toNat_false,mul_zero,add_zero,q26]
        exact Nat.mod_modEq _ _
      | true=>
        simp only [↓reduceIte,Bool.toNat_true,mul_one,jV]
        exact Nat.mod_modEq _ _
     have hmod2:((2 * val aSh) % 2 ^ wU.length) * val br ≡ (2 * val aSh) * val br [MOD 2 ^ wU.length]:=
      (Nat.mod_modEq _ _).mul_right _
     have hcomb:=hmod1.add hmod2
     have hrew:val acc+val aSh * bb.toNat+2 * val aSh * val br=
      val acc+val aSh * (bb.toNat+2 * val br):=by ring
     rw [hrew] at hcomb
     simpa only [Nat.ModEq,val] using hcomb
lemma qbR (wU a b:List Bool):
 (zy wU a b).length=wU.length∧val (zy wU a b)=(val a * val b) % 2 ^ wU.length:=by
 dsimp only [zy]
 obtain ⟨aSh',acc',hiter,hlen,hval⟩:=
  qdz wU wU.length (qy wU b) (qy wU a) (blank wU)
   (q19 wU b) (q19 wU a) (q33 wU)
 rw [hiter]
 simp only [qj]
 refine ⟨hlen,?_⟩
 rw [q37,zero_add,q26,q26] at hval
 have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact kQ acc'
 rw [Nat.mod_eq_of_lt hlt] at hval
 rw [hval,Nat.mod_mul_mod,Nat.mul_mod_mod]
lemma q93 (wU a b:List Bool):(zy wU a b).length=wU.length:=(qbR wU a b).1
lemma kt (wU a b:List Bool):val (zy wU a b)=(val a * val b) % 2 ^ wU.length:=
 (qbR wU a b).2
lemma q55 (wU a b:List Bool):
 ((val (zy wU a b):ℤ) ≡ (val a:ℤ) * (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 rw [kt];exact_mod_cast (Nat.mod_modEq (val a * val b) (2 ^ wU.length))
def geW (wU a b:List Bool):List Bool:=
 let w1:=true::wU
 q133 (q17 (vk w1 (qy w1 (qy wU a)) (qy w1 (qy wU b))).reverse)
lemma qeb {uw ua ub:List Bool→List Bool} (hw:qe uw) (ha:qe ua) (hb:qe ub):
 qe (fun s=>geW (uw s) (ua s) (ub s)):=by
 have hw1:=qi (qh [true]) hw
 exact qa (qa (qa (qaC hw1 (q13 hw1 (q13 hw ha))
  (q13 hw1 (q13 hw hb))) w2) q35) qbL
lemma qdJ (l:List Bool) (n:ℕ) (hlen:l.length=n+1):
 q17 l.reverse=if 2 ^ n≤val l then [true] else []:=by
 have hsplit:∃ pref lastB,l=pref++[lastB]∧pref.length=n:=by
  cases hrev:l.reverse with
  | nil=>
    have:=congrArg List.length hrev
    simp [hlen] at this
  | cons b r=>
    refine ⟨r.reverse,b,?_,?_⟩
    · have:=congrArg List.reverse hrev
      simpa using this
    · have h1:=congrArg List.length hrev
      rw [List.length_reverse,hlen,List.length_cons] at h1
      rw [List.length_reverse];omega
 rcases hsplit with ⟨pref,lastB,rfl,hplen⟩
 simp only [List.reverse_append,List.reverse_singleton,List.singleton_append]
 rw [q58,hplen]
 have hplt:val pref < 2 ^ n:=by rw [← hplen];exact kQ pref
 cases lastB with
 | false=>
   simp only [q17,val,Bool.toNat_false,mul_zero,add_zero]
   rw [ite_eq_right_iff.2 (fun h=>by omega)]
 | true=>
   simp only [q17,val,Bool.toNat_true,mul_zero,add_zero,mul_one]
   rw [ite_eq_left_iff.2 (fun h=>by omega)]
lemma qd7 (wU a b:List Bool) (ha:val a < 2 ^ wU.length) (hb:val b < 2 ^ wU.length):
 geW wU a b=if val b≤val a then [true] else []:=by
 dsimp only [geW]
 set w1:=true::wU
 set a1:=qy w1 (qy wU a)
 set b1:=qy w1 (qy wU b)
 set d:=vk w1 a1 b1
 have ha1:val a1=val a:=by
  rw [q30 w1 (qy wU a) (by rw [q19];simp [w1]),
   q26,Nat.mod_eq_of_lt ha]
 have hb1:val b1=val b:=by
  rw [q30 w1 (qy wU b) (by rw [q19];simp [w1]),
   q26,Nat.mod_eq_of_lt hb]
 have hdlen:d.length=wU.length+1:=q63 w1 a1 b1
 have hdlt:val d < 2 ^ (wU.length+1):=by rw [← hdlen];exact kQ d
 have hmod:((val d:ℤ) ≡ (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ (wU.length+1)]):=by
  have hsm:=qbN w1 a1 b1
  rw [ha1,hb1] at hsm
  simpa only [w1,List.length_cons] using hsm
 rw [qdJ d wU.length hdlen]
 by_cases hle:val b≤val a
 · have hdeq:val d=val a - val b:=by
    have:=q83 w1 a1 b1 (by rw [ha1];simp [w1,pow_succ];omega) (by rw [ha1,hb1];exact hle)
    rw [ha1,hb1] at this;exact this
   have hltW:val d < 2 ^ wU.length:=by omega
   simp [hle,not_le.2 hltW,q133,sel]
 · have hlt:val a < val b:=by omega
   have hdeq:val d=2 ^ (wU.length+1)+val a - val b:=by
    have htarget:2 ^ (wU.length+1)+val a - val b < 2 ^ (wU.length+1):=by omega
    have hcast:((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ) ≡
     (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ (wU.length+1)]:=by
     rw [Int.modEq_iff_dvd]
     have hsub:((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ)=
      (2:ℤ) ^ (wU.length+1)+(val a:ℤ) - (val b:ℤ):=by
      have hge:val b≤2 ^ (wU.length+1)+val a:=by rw [pow_succ];omega
      rw [Nat.cast_sub hge,Nat.cast_add,Nat.cast_pow];norm_num
     have:(val a:ℤ) - (val b:ℤ) - ((2 ^ (wU.length+1)+val a - val b:ℕ):ℤ)=
         -((2:ℤ) ^ (wU.length+1)):=by linarith
     rw [this];exact dvd_neg.2 (dvd_refl _)
    have hnat:val d ≡ 2 ^ (wU.length+1)+val a - val b [MOD 2 ^ (wU.length+1)]:=by
     exact_mod_cast (hmod.trans hcast.symm)
    rw [Nat.ModEq,Nat.mod_eq_of_lt hdlt,Nat.mod_eq_of_lt htarget] at hnat
    exact hnat
   have hgeW:2 ^ wU.length≤val d:=by rw [hdeq,pow_succ];omega
   simp [hle,hgeW,q133,sel]
def q118 (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let b:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let aRev:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let rem:=(unpairB r3).1
 let qAcc:=(unpairB r3).2
 let rem1:=zj wU (q16 (q17 aRev)++qy wU rem)
 let ok:=geW wU rem1 b
 let rem':=sel ok rem1 (vk wU rem1 b)
 let qAcc':=q16 ok++qAcc
 qc wU (qc b (qc aRev.tail (qc rem' qAcc')))
lemma qdW:qe q118:=by
 have hw:=qf
 have hr1:=qb
 have hb:=qa hr1 qf
 have hr2:=qa hr1 qb
 have haRev:=qa hr2 qf
 have hr3:=qa hr2 qb
 have hrem:=qa hr3 qf
 have hqAcc:=qa hr3 qb
 have hrem1:=q24 hw (qi (q73 (qa haRev q35)) (q13 hw hrem))
 have hok:=qeb hw hrem1 hb
 have hrem':=zh hok hrem1 (qaC hw hrem1 hb)
 have hqAcc':=qi (q73 hok) hqAcc
 exact qd hw (qd hb (qd (qa haRev vW) (qd hrem' hqAcc')))
def wI (wU a b:List Bool):List Bool:=
 let fin:=q118^[wU.length] (qc wU (qc (qy wU b) (qc (qy wU a).reverse (qc (blank wU) []))))
 (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma qdO {uw ua ub:List Bool→List Bool} (hw:qe uw) (ha:qe ua) (hb:qe ub):
 qe (fun s=>wI (uw s) (ua s) (ub s)):=by
 have hfin:=q18 10 qdW
  (fun y=>by dsimp only [q118];rw [qj])
  (fun y=>by
    dsimp only [q118]
    set wU:=(unpairB y).1;set r1:=(unpairB y).2
    set b:=(unpairB r1).1;set r2:=(unpairB r1).2
    set aRev:=(unpairB r2).1;set r3:=(unpairB r2).2
    set rem:=(unpairB r3).1;set qAcc:=(unpairB r3).2
    set rem1:=zj wU (q16 (q17 aRev)++qy wU rem)
    set ok:=geW wU rem1 b
    have h1:2 * wU.length+r1.length≤y.length:=q0 y
    have h2:2 * b.length+r2.length≤r1.length:=q0 r1
    have h3:2 * aRev.length+r3.length≤r2.length:=q0 r2
    have h4:2 * rem.length+qAcc.length≤r3.length:=q0 r3
    rw [q7,q7,q7,q7,List.length_append]
    have hat:aRev.tail.length≤aRev.length:=by cases aRev <;> simp
    have hrem1_len:rem1.length≤wU.length:=by
     dsimp only [rem1];rw [q12,List.length_take];exact Nat.min_le_left _ _
    have hrem':(sel ok rem1 (vk wU rem1 b)).length≤wU.length:=by
     unfold sel;split_ifs
     · exact hrem1_len
     · rw [q63]
    have hqb:(q16 ok).length=1:=by unfold q16 sel;split_ifs <;> rfl
    omega)
  hw (qd hw (qd (q13 hw hb)
   (qd (qa (q13 hw ha) w2) (qd (qa hw kh) (qh [])))))
 exact q39 (qa (qa (qa (qa hfin qb) qb) qb) qb) (fun _=>rfl)
lemma qdA (wU b:List Bool) (hb_len:b.length=wU.length)
 (hb_pos:0 < val b) (hb_2:2 * val b < 2 ^ wU.length):
 ∀ (k:ℕ) (aRev rem qAcc:List Bool),
   aRev.length=k→ rem.length=wU.length→val rem < val b→
   ∃ rem' qAcc',
     q118^[k] (qc wU (qc b (qc aRev (qc rem qAcc))))=
      qc wU (qc b (qc [] (qc rem' qAcc')))∧
     qAcc'.length=qAcc.length+k∧
     val qAcc'=(val qAcc * 2 ^ k+(val rem * 2 ^ k+val aRev.reverse) / val b)∧
     val rem'=(val rem * 2 ^ k+val aRev.reverse) % val b:=by
 intro k
 induction k with
 | zero=>
   intro aRev rem qAcc ha _ hrem_lt
   cases aRev
   · refine ⟨rem,qAcc,rfl,by simp,?_,?_⟩
     · simp [val,Nat.div_eq_of_lt hrem_lt]
     · simp [val,Nat.mod_eq_of_lt hrem_lt]
   · simp at ha
 | succ k ih=>
   intro aRev rem qAcc ha hrem_len hrem_lt
   cases aRev with
   | nil=>simp at ha
   | cons bit ar=>
     rw [Function.iterate_succ_apply]
     have hrem1_val:val (zj wU (q16 (q17 (bit::ar))++qy wU rem))=
      bit.toNat+2 * val rem:=by
      have hbf:q16 (q17 (bit::ar))=[bit]:=by cases bit <;> rfl
      rw [hbf,q12,qaB,List.singleton_append,val,q30 wU rem (by omega)]
      have hltW:bit.toNat+2 * val rem < 2 ^ wU.length:=by
       have:bit.toNat≤1:=by cases bit <;> decide
       omega
      exact Nat.mod_eq_of_lt hltW
     have hrem1_len:(zj wU (q16 (q17 (bit::ar))++qy wU rem)).length=wU.length:=by
      rw [q12,List.length_take,List.length_append,q19]
      have:(q16 (q17 (bit::ar))).length=1:=by cases bit <;> rfl
      omega
     set rem1:=zj wU (q16 (q17 (bit::ar))++qy wU rem)
     have hrem1_ltW:val rem1 < 2 ^ wU.length:=by rw [← hrem1_len];exact kQ rem1
     have hb_ltW:val b < 2 ^ wU.length:=by rw [← hb_len];exact kQ b
     have hok:geW wU rem1 b=if val b≤val rem1 then [true] else []:=
      qd7 wU rem1 b hrem1_ltW hb_ltW
     have hstep:q118 (qc wU (qc b (qc (bit::ar) (qc rem qAcc))))=
      qc wU (qc b (qc ar (qc (if val b≤val rem1 then vk wU rem1 b else rem1)
       ((decide (val b≤val rem1))::qAcc)))):=by
      dsimp only [q118]
      simp only [qj,List.tail_cons]
      change qc wU (qc b (qc ar (qc (sel (geW wU rem1 b) rem1 (vk wU rem1 b))
       (q16 (geW wU rem1 b)++qAcc))))=_
      rw [hok]
      by_cases hge:val b≤val rem1
      · simp [hge,sel,q16]
      · simp [hge,sel,q16]
     rw [hstep]
     set rem'1:=if val b≤val rem1 then vk wU rem1 b else rem1
     set q'1:=(decide (val b≤val rem1))::qAcc
     have hrem'1_len:rem'1.length=wU.length:=by
      dsimp only [rem'1];split_ifs <;> simp [q63,hrem1_len]
     have hrem'1_eq:val rem'1=val rem1 % val b∧val q'1=2 * val qAcc+val rem1 / val b:=by
      have hrem1_lt2b:val rem1 < 2 * val b:=by
       have:bit.toNat≤1:=by cases bit <;> decide
       omega
      by_cases hge:val b≤val rem1
      · have hsub:val rem'1=val rem1 - val b:=by
         dsimp only [rem'1];rw [if_pos hge];exact q83 wU rem1 b hrem1_ltW hge
        have hdiv1:val rem1 / val b=1:=by
         have h1:1 * val b≤val rem1:=by omega
         have h2:val rem1 < 2 * val b:=hrem1_lt2b
         have h3:=Nat.div_add_mod (val rem1) (val b)
         have h4:val rem1 % val b < val b:=Nat.mod_lt _ hb_pos
         have hge1:1≤val rem1 / val b:=(Nat.le_div_iff_mul_le hb_pos).2 (by omega)
         have hlt2:val rem1 / val b < 2:=(Nat.div_lt_iff_lt_mul hb_pos).2 (by omega)
         omega
        have hmod1:val rem1 % val b=val rem1 - val b:=by
         have:=Nat.div_add_mod (val rem1) (val b)
         rw [hdiv1] at this;omega
        refine ⟨by omega,?_⟩
        dsimp only [q'1];simp [val,hge,hdiv1];omega
      · have hltb:val rem1 < val b:=by omega
        have hsub:val rem'1=val rem1:=by dsimp only [rem'1];rw [if_neg hge]
        refine ⟨by rw [hsub,Nat.mod_eq_of_lt hltb],?_⟩
        dsimp only [q'1];simp [val,hge,Nat.div_eq_of_lt hltb]
     have hrem'1_lt:val rem'1 < val b:=by rw [hrem'1_eq.1];exact Nat.mod_lt _ hb_pos
     obtain ⟨rem',qAcc',hiter,hlen',hq',hr'⟩:=
      ih ar rem'1 q'1 (by simpa using ha) hrem'1_len hrem'1_lt
     refine ⟨rem',qAcc',hiter,by simp [hlen',q'1];omega,?_,?_⟩
     · rw [hq',hrem'1_eq.2,hrem'1_eq.1]
       have har:val (bit::ar).reverse=val ar.reverse+2 ^ k * bit.toNat:=by
        rw [List.reverse_cons,q58,List.length_reverse,show ar.length=k by simpa using ha]
        simp [val]
       rw [har]
       have htot:val rem * 2 ^ (k+1)+(val ar.reverse+2 ^ k * bit.toNat)=
        val rem1 * 2 ^ k+val ar.reverse:=by
        rw [hrem1_val,pow_succ'];ring
       rw [htot]
       have hdm:=Nat.div_add_mod (val rem1) (val b)
       have hsplit:val rem1 * 2 ^ k+val ar.reverse=
        val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by
        calc val rem1 * 2 ^ k+val ar.reverse
         =(val b * (val rem1 / val b)+val rem1 % val b) * 2 ^ k+val ar.reverse:=by rw [hdm]
         _=val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by ring
       rw [hsplit,Nat.mul_add_div hb_pos]
       rw [pow_succ'];ring
     · rw [hr',hrem'1_eq.1]
       have har:val (bit::ar).reverse=val ar.reverse+2 ^ k * bit.toNat:=by
        rw [List.reverse_cons,q58,List.length_reverse,show ar.length=k by simpa using ha]
        simp [val]
       rw [har]
       have htot:val rem * 2 ^ (k+1)+(val ar.reverse+2 ^ k * bit.toNat)=
        val rem1 * 2 ^ k+val ar.reverse:=by
        rw [hrem1_val,pow_succ'];ring
       rw [htot]
       have hdm:=Nat.div_add_mod (val rem1) (val b)
       have hsplit:val rem1 * 2 ^ k+val ar.reverse=
        val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by
        calc val rem1 * 2 ^ k+val ar.reverse
         =(val b * (val rem1 / val b)+val rem1 % val b) * 2 ^ k+val ar.reverse:=by rw [hdm]
         _=val b * (val rem1 / val b * 2 ^ k)+(val rem1 % val b * 2 ^ k+val ar.reverse):=by ring
       rw [hsplit,Nat.mul_add_mod]
lemma qdK (wU a b:List Bool) (ha:val a < 2 ^ wU.length)
 (hb_pos:0 < val b) (hb_2:2 * val b < 2 ^ wU.length):
 (wI wU a b).length=wU.length∧val (wI wU a b)=val a / val b:=by
 dsimp only [wI]
 have hb_val:val (qy wU b)=val b:=by
  rw [q26,Nat.mod_eq_of_lt (by omega)]
 have ha_val:val (qy wU a)=val a:=by
  rw [q26,Nat.mod_eq_of_lt ha]
 obtain ⟨rem',qAcc',hiter,hlen',hq',_⟩:=
  qdA wU (qy wU b) (q19 wU b) (by rw [hb_val];exact hb_pos)
   (by rw [hb_val];exact hb_2) wU.length (qy wU a).reverse (blank wU) []
   (by rw [List.length_reverse,q19]) (q33 wU) (by rw [q37,hb_val];exact hb_pos)
 rw [hiter]
 simp only [qj]
 rw [List.reverse_reverse,ha_val,hb_val,q37] at hq'
 simp only [val,zero_mul,zero_add,List.length_nil] at hlen' hq'
 exact ⟨hlen',hq'⟩
def q87 (l:List Bool):List Bool:=l.dropWhile (fun b=>!b)
lemma qdL:qe q87:=by
 let δ:Bool→Bool→Bool×Option Bool:=fun st b=>
  match st,b with
  | true,b=>(true,some b)
  | false,false=>(false,none)
  | false,true=>(true,some true)
 refine qK _ _ _ δ (fun _=>none) false fun s=>?_
 have htrue:∀ l,ql δ (fun _=>none) true l=l:=by
  intro l;induction l with | nil=>rfl | cons b r ih=>simp [ql,δ,ih]
 have hfalse:∀ l,ql δ (fun _=>none) false l=q87 l:=by
  intro l
  induction l with
  | nil=>rfl
  | cons b r ih=>cases b <;> simp [ql,δ,q87,htrue,ih]
 exact (hfalse s).symm
def q141 (x:List Bool):List Bool:=(q87 x.reverse).reverse
lemma qbP:qe q141:=
 q39 (qa (qa w2 qdL) w2) (fun _=>rfl)
lemma qbJ (x:List Bool):q141 x=(val x).bits:=by
 induction x using List.reverseRecOn with
 | nil=>rfl
 | append_singleton l b ih=>
   dsimp only [q141,q87] at ih ⊢
   rw [List.reverse_append,List.reverse_singleton,List.singleton_append]
   cases b with
   | false=>
     simp only [List.dropWhile_cons,Bool.not_false,↓reduceIte]
     rw [ih,q58]
     simp [val]
   | true=>
     simp only [List.dropWhile_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      List.reverse_cons,List.reverse_reverse]
     have hpos:∀ r:List Bool,(val (r++[true])).bits=r++[true]:=by
      intro r
      induction r with
      | nil=>decide
      | cons c r ihr=>
        have hval:val ((c::r)++[true])=Nat.bit c (val (r++[true])):=by
         simp only [List.cons_append,val,Nat.bit]
         cases c <;> simp <;> omega
        have hne:val (r++[true])≠0:=by
         rw [q58];simp [val]
        rw [hval,Nat.bits_append_bit _ c (fun h0=>(hne h0).elim),ihr]
        rfl
     exact (hpos l).symm
def q49 (s:List Bool):List Bool:=s.filter id
lemma qew:qe q49:=
 qK _ _ _ (fun (_:Unit) (b:Bool)=>((),if b then some true else none))
  (fun _=>none) () fun s=>by
    induction s with
    | nil=>rfl
    | cons b r ih=>cases b <;> simp [ql,q49] at ih ⊢ <;> exact ih
def q21 (kU pU uU:List Bool):List Bool:=
 z6 kU pU++z6 kU (true::pU)++z6 kU uU
def q112 (u:List Bool):List Bool:=if u.length % 2=1 then [true] else []
lemma qdI:qe q112:=by
 let δ:Bool→Bool→Bool×Option Bool:=fun st _=>(!st,none)
 let fin:Bool→Option Bool:=fun st=>if st then some true else none
 refine qK _ _ _ δ fin false fun s=>?_
 have hrun:∀ (st:Bool) (l:List Bool),
  ql δ fin st l=if (xor st (decide (l.length % 2=1))) then [true] else []:=by
  intro st l
  induction l generalizing st with
  | nil=>cases st <;> rfl
  | cons _ r ih=>
    simp only [ql,δ,List.length_cons,ih]
    cases st <;> by_cases h:r.length % 2=1 <;> simp [h] <;> omega
 simpa [q112] using (hrun false s).symm
def ku (a b:List Bool):List Bool:=q133 (vN a b++vN b a)
lemma qaE (a b:List Bool):ku a b=if a.length=b.length then [true] else []:=by
 dsimp only [ku,q133,sel]
 rw [q40,q40]
 by_cases h:a.length=b.length
 · simp [h]
 · have hne:b.drop a.length++a.drop b.length≠[]:=by
    intro he
    have hl:=congrArg List.length he
    simp only [List.length_append,List.length_drop,List.length_nil] at hl
    omega
   simp [h,hne]
lemma qaD {ua ub:List Bool→List Bool} (ha:qe ua) (hb:qe ub):
 qe (fun s=>ku (ua s) (ub s)):=
 qa (qi (yS ha hb) (yS hb ha)) qbL
def q132 (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let base:=(unpairB r1).1
 let acc:=(unpairB r1).2
 qc wU (qc base (zy wU acc base))
lemma qdU:qe q132:=by
 have hw:=qf
 have hr1:=qb
 have hb:=qa hr1 qf
 have hacc:=qa hr1 qb
 exact qd hw (qd hb (q32 hw hacc hb))
def uD (wU baseW eU:List Bool):List Bool:=
 let fin:=q132^[eU.length] (qc wU (qc (qy wU baseW) (zz wU [true])))
 (unpairB (unpairB fin).2).2
lemma qd0 {uw ub ue:List Bool→List Bool} (hw:qe uw) (hb:qe ub) (he:qe ue):
 qe (fun s=>uD (uw s) (ub s) (ue s)):=by
 have hfin:=q18 6 qdU
  (fun y=>by dsimp only [q132];rw [qj])
  (fun y=>by
    dsimp only [q132]
    have h1:=q0 y
    have h2:=q0 (unpairB y).2
    rw [q7,q7,q93]
    omega)
  he (qd hw (qd (q13 hw hb) (q50 hw (qh [true]))))
 exact q39 (qa (qa hfin qb) qb) (fun _=>rfl)
lemma qdQ (wU baseW eU:List Bool):
 (uD wU baseW eU).length=wU.length∧val (uD wU baseW eU)=(val baseW) ^ eU.length % 2 ^ wU.length:=by
 dsimp only [uD]
 have hiter:∀ k,
  ∃ acc,q132^[k] (qc wU (qc (qy wU baseW) (zz wU [true])))=
     qc wU (qc (qy wU baseW) acc)∧
    acc.length=wU.length∧val acc=(val baseW) ^ k % 2 ^ wU.length:=by
  intro k
  induction k with
  | zero=>
    refine ⟨zz wU [true],rfl,q54 _ _,by simp [kP]⟩
  | succ k ih=>
    obtain ⟨acc,h1,hlen,hval⟩:=ih
    rw [Function.iterate_succ_apply',h1]
    dsimp only [q132]
    simp only [qj]
    refine ⟨zy wU acc (qy wU baseW),rfl,q93 _ _ _,?_⟩
    rw [kt,hval,q26,Nat.mod_mul_mod,Nat.mul_mod_mod,pow_succ]
 obtain ⟨acc,h1,hlen,hval⟩:=hiter eU.length
 rw [h1];simp only [qj];exact ⟨hlen,hval⟩
def yN (wU rest tU:List Bool):List Bool:=
 qy wU (q75 (q43^[tU.length] rest))
lemma qea {uw ur ut:List Bool→List Bool} (hw:qe uw) (hr:qe ur) (ht:qe ut):
 qe (fun s=>yN (uw s) (ur s) (ut s)):=
 q13 hw (qa (qai qdG q91 ht hr) qdH)
lemma q62 {α:Type*} (L:List α) (f:α→List Bool):
 ∀ (t:ℕ) (ht:t < L.length),
   q43^[t] (L.flatMap (fun a=>q23 (f a)))=
    (L.drop t).flatMap (fun a=>q23 (f a)):=by
 intro t
 induction t generalizing L with
 | zero=>intro _;simp
 | succ t ih=>
   intro ht
   cases L with
   | nil=>simp at ht
   | cons a r=>
     rw [Function.iterate_succ_apply,List.flatMap_cons,qdy]
     exact ih r (by simpa using ht)
lemma qez (n:ℕ) (wU:List Bool) (Z:Fin (n+1)→ℕ)
 (hZlen:∀ t:Fin (n+1),(Z t).bits.length≤wU.length)
 (t:ℕ) (ht:t < n+1):
 val (yN wU ((List.finRange (n+1)).flatMap (fun u=>q23 (Z u).bits)) (un t))=Z ⟨t,ht⟩:=by
 dsimp only [yN]
 rw [qN,q62 (List.finRange (n+1)) (fun u=>(Z u).bits) t (by simp;omega)]
 have hdrop:(List.finRange (n+1)).drop t=⟨t,ht⟩::(List.finRange (n+1)).drop (t+1):=by
  rw [List.drop_eq_getElem_cons (by simp;omega)];simp
 rw [hdrop,List.flatMap_cons,qbI,q30 wU _ (hZlen ⟨t,ht⟩),w3]
end
noncomputable section
open PEqualNP.Library Lib.qz Lib.z9 Lib.qz.Rev
namespace kg
lemma zK {α β:Type*} (f:α→List β) (l:List α):
 l.flatMap f=(l.map f).flatten:=by
 induction l with
 | nil=>rfl
 | cons a r ih=>simp [ih]
def qm (k z:ℕ):List Bool:=(List.range (k.log2 + 1)).map (fun i=>z.testBit i)
lemma zS (kU zU:List Bool) (hk:0 < kU.length):
 z6 kU zU=qm kU.length zU.length:=by
 have h1:z6 kU zU=z6 (un kU.length) (un zU.length):=by
  dsimp only [z6]
  rw [q12,q12,q71,q71,q71,q71,qN,qN]
 rw [h1]
 exact q86 kU.length zU.length hk
lemma yv (kU zU:List Bool) (hk:0 < kU.length):
 (z6 kU zU).length=kU.length.log2 + 1:=by
 rw [zS kU zU hk]
 simp [qm]
lemma zt (kU pU uU:List Bool) (hk:0 < kU.length):
 q21 kU pU uU=
  qm kU.length pU.length++qm kU.length (pU.length + 1)++qm kU.length uU.length:=by
 dsimp only [q21]
 rw [zS kU pU hk,zS kU (true::pU) hk,zS kU uU hk,
  List.length_cons]
lemma yY (kU pU uU:List Bool) (hk:0 < kU.length):
 (q21 kU pU uU).length=3 * (kU.length.log2 + 1):=by
 dsimp only [q21]
 rw [List.length_append,List.length_append,yv kU pU hk,yv kU (true::pU) hk,
  yv kU uU hk]
 omega
def ve (qU eU blockU jU:List Bool):List Bool:=
 qJ blockU qU++sel jU [] (sel (ku jU (true::eU)) (jU++jU).tail (eU++eU))
lemma v3 {uq ue ub uj:List Bool→List Bool}
 (hq:qe uq) (he:qe ue) (hb:qe ub) (hj:qe uj):
 qe (fun s=>ve (uq s) (ue s) (ub s) (uj s)):=
 qi (q42 hb hq)
  (zh hj (qh [])
    (zh (qaD hj (qi (qh [true]) he))
      (qa (qi hj hj) vW)
      (qi he he)))
lemma y9 (qU eU blockU jU:List Bool):
 (ve qU eU blockU jU).length=
   blockU.length * qU.length +
   (if jU.length=0 then 0 else if jU.length=eU.length + 1 then 2 * eU.length else 2 * jU.length - 1):=by
 dsimp only [ve]
 rw [List.length_append]
 have hm:(qJ blockU qU).length=blockU.length * qU.length:=by simp [qJ]
 rw [hm]
 congr 1
 cases jU with
 | nil=>simp [sel]
 | cons b r=>
   simp only [sel,List.cons_ne_nil,↓reduceIte,List.length_cons,Nat.add_one_ne_zero]
   rw [qaE]
   simp only [List.length_cons]
   by_cases h:r.length=eU.length
   · simp [h]; omega
   · simp [h]; omega
def pathStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let bU:=(unpairB r2).1
 let acc:=(unpairB r2).2
 let chunk:=zj boundU (z6 kU bU++z6 kU (true::bU)++z6 kU (true::true::bU))
 qc boundU (qc kU (qc (true::true::bU) (acc++chunk)))
lemma wF:qe pathStep:=by
 have hb:=qf
 have hr1:=qb
 have hk:=qa hr1 qf
 have hr2:=qa hr1 qb
 have hbu:=qa hr2 qf
 have hacc:=qa hr2 qb
 have hb1:=qi (qh [true]) hbu
 have hb2:=qi (qh [true,true]) hbu
 have hchunk:=q24 hb (qi (qi (q61 hk hbu) (q61 hk hb1)) (q61 hk hb2))
 exact qd hb (qd hk (qd hb2 (qi hacc hchunk)))
def v8 (kU qU eU uU:List Bool):List Bool:=
 let boundU:=qJ (List.replicate 3 true) (true::kU)
 let fin:=pathStep^[eU.length] (qc boundU (qc kU (qc (qJ uU qU) [])))
 (unpairB (unpairB (unpairB fin).2).2).2
lemma j3 {uk uq ue uu:List Bool→List Bool}
 (hk:qe uk) (hq:qe uq) (he:qe ue) (hu:qe uu):
 qe (fun s=>v8 (uk s) (uq s) (ue s) (uu s)):=by
 have hbound:=q42 (qh (List.replicate 3 true)) (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd (q42 hu hq) (qh [])))
 have hfin:=q18 10 wF
  (fun y=>by dsimp only [pathStep]; rw [qj])
  (fun y=>by
    dsimp only [pathStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set bU:=(unpairB r2).1; set acc:=(unpairB r2).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * bU.length + acc.length≤r2.length:=q0 r2
    rw [q7,q7,q7,List.length_append,List.length_cons,List.length_cons]
    have hc:(zj boundU (z6 kU bU++z6 kU (true::bU)++z6 kU (true::true::bU))).length≤
     boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    omega)
  he hinit
 exact q39 (qa (qa (qa hfin qb) qb) qb) (fun _=>rfl)
lemma jS (kU qU eU uU:List Bool) (hk:0 < kU.length):
 v8 kU qU eU uU=
  (List.range eU.length).flatMap (fun j=>
    let b:=uU.length * qU.length + 2 * j
    qm kU.length b++qm kU.length (b + 1)++qm kU.length (b + 2)):=by
 dsimp only [v8]
 set boundU:=qJ (List.replicate 3 true) (true::kU)
 have hblen:boundU.length=3 * (kU.length + 1):=by simp [boundU,qJ]
 have hiter:∀ t:ℕ,∃ bU:List Bool,
  pathStep^[t] (qc boundU (qc kU (qc (qJ uU qU) [])))=
   qc boundU (qc kU (qc bU
    ((List.range t).flatMap (fun j=>
      let b:=uU.length * qU.length + 2 * j
      qm kU.length b++qm kU.length (b + 1)++qm kU.length (b + 2)))))∧
  bU.length=uU.length * qU.length + 2 * t:=by
  intro t
  induction t with
  | zero=>exact ⟨qJ uU qU,by simp,by simp [qJ]⟩
  | succ t ih=>
    obtain ⟨bU,hstep,hbl⟩:=ih
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [pathStep]
    simp only [qj]
    have hchunk:z6 kU bU++z6 kU (true::bU)++z6 kU (true::true::bU)=
     qm kU.length (uU.length * qU.length + 2 * t)++
     qm kU.length (uU.length * qU.length + 2 * t + 1)++
     qm kU.length (uU.length * qU.length + 2 * t + 2):=by
     rw [zS kU bU hk,zS kU (true::bU) hk,
      zS kU (true::true::bU) hk]
     simp only [List.length_cons,hbl]
    have hle:(z6 kU bU++z6 kU (true::bU)++z6 kU (true::true::bU)).length≤boundU.length:=by
     rw [List.length_append,List.length_append,yv kU bU hk,yv kU (true::bU) hk,
      yv kU (true::true::bU) hk,hblen]
     have:=Nat.log2_le_self kU.length; omega
    rw [q12,List.take_of_length_le hle,hchunk]
    refine ⟨true::true::bU,?_,by simp [hbl]; omega⟩
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
 obtain ⟨bU,hfin,_⟩:=hiter eU.length
 rw [hfin]; simp only [qj]
def pathOuterStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let qU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let eU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let uU:=(unpairB r4).1
 let acc:=(unpairB r4).2
 let chunk:=zj boundU (v8 kU qU eU uU)
 qc boundU (qc kU (qc qU (qc eU (qc (true::uU) (acc++chunk)))))
lemma uM:qe pathOuterStep:=by
 have hb:=qf
 have hr1:=qb
 have hk:=qa hr1 qf
 have hr2:=qa hr1 qb
 have hq:=qa hr2 qf
 have hr3:=qa hr2 qb
 have he:=qa hr3 qf
 have hr4:=qa hr3 qb
 have hu:=qa hr4 qf
 have hacc:=qa hr4 qb
 have hchunk:=q24 hb (j3 hk hq he hu)
 exact qd hb (qd hk (qd hq (qd he
  (qd (qi (qh [true]) hu) (qi hacc hchunk)))))
def uK (kU vU qU eU:List Bool):List Bool:=
 let boundU:=qJ (qJ (List.replicate 3 true) eU) (true::kU)
 let fin:=pathOuterStep^[vU.length] (qc boundU (qc kU (qc qU (qc eU (qc [] [])))))
 (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2
lemma qaj {uk uv uq ue:List Bool→List Bool}
 (hk:qe uk) (hv:qe uv) (hq:qe uq) (he:qe ue):
 qe (fun s=>uK (uk s) (uv s) (uq s) (ue s)):=by
 have hbound:=q42 (q42 (qh (List.replicate 3 true)) he) (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd hq (qd he (qd (qh []) (qh [])))))
 have hfin:=q18 14 uM
  (fun y=>by dsimp only [pathOuterStep]; rw [qj])
  (fun y=>by
    dsimp only [pathOuterStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set qU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set eU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set uU:=(unpairB r4).1; set acc:=(unpairB r4).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * qU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * eU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * uU.length + acc.length≤r4.length:=q0 r4
    rw [q7,q7,q7,q7,q7,List.length_append,List.length_cons]
    have hc:(zj boundU (v8 kU qU eU uU)).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    omega)
  hv hinit
 exact q39 (qa (qa (qa (qa (qa hfin qb) qb)
  qb) qb) qb) (fun _=>rfl)
lemma wX (kU vU qU eU:List Bool) (hk:0 < kU.length):
 uK kU vU qU eU=
  (List.range vU.length).flatMap (fun u=>
    (List.range eU.length).flatMap (fun j=>
      let b:=u * qU.length + 2 * j
      qm kU.length b++qm kU.length (b + 1)++qm kU.length (b + 2))):=by
 dsimp only [uK]
 set boundU:=qJ (qJ (List.replicate 3 true) eU) (true::kU)
 have hblen:boundU.length=3 * eU.length * (kU.length + 1):=by simp [boundU,qJ]
 have hiter:∀ t:ℕ,∃ uU:List Bool,
  pathOuterStep^[t] (qc boundU (qc kU (qc qU (qc eU (qc [] [])))))=
   qc boundU (qc kU (qc qU (qc eU (qc uU
    ((List.range t).flatMap (fun u=>
      (List.range eU.length).flatMap (fun j=>
        let b:=u * qU.length + 2 * j
        qm kU.length b++qm kU.length (b + 1)++qm kU.length (b + 2))))))))∧
  uU.length=t:=by
  intro t
  induction t with
  | zero=>exact ⟨[],by simp,rfl⟩
  | succ t ih=>
    obtain ⟨uU,hstep,hul⟩:=ih
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [pathOuterStep]
    simp only [qj]
    have hpb:=jS kU qU eU uU hk
    rw [hul] at hpb
    have hle:(v8 kU qU eU uU).length≤boundU.length:=by
     rw [hpb,hblen]
     have hlen1:∀ j∈List.range eU.length,
      (qm kU.length (t * qU.length + 2 * j)++
       qm kU.length (t * qU.length + 2 * j + 1)++
       qm kU.length (t * qU.length + 2 * j + 2)).length=3 * (kU.length.log2 + 1):=by
      intro j _; simp only [List.length_append,qm,List.length_map,List.length_range]; omega
     have hfm:∀ (L:List ℕ) (f:ℕ→List Bool) (c:ℕ),(∀ a∈L,(f a).length=c)→
      (L.flatMap f).length=L.length * c:=by
      intro L f c hf
      induction L with
      | nil=>simp
      | cons a r ihL=>
        rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
         ihL (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
     rw [hfm _ _ _ hlen1,List.length_range]
     have hlog:kU.length.log2≤kU.length:=Nat.log2_le_self kU.length
     calc eU.length * (3 * (kU.length.log2 + 1))
      =3 * eU.length * (kU.length.log2 + 1):=by ring
      _≤3 * eU.length * (kU.length + 1):=Nat.mul_le_mul_left _ (by omega)
    rw [q12,List.take_of_length_le hle,hpb]
    refine ⟨true::uU,?_,by simp [hul]⟩
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
 obtain ⟨uU,hfin,_⟩:=hiter vU.length
 rw [hfin]; simp only [qj]
def yG (kU nU qU eU iU jU bU remBits:List Bool):List Bool:=
 let lU:=ve qU eU iU (jU++jU)
 let l'U:=ve qU eU iU (true::(jU++jU))
 let rU:=ve qU eU (nU++jU) (iU++iU)
 let r'U:=ve qU eU (nU++jU) (true::(iU++iU))
 let b2U:=true::true::bU
 let cTrue:=q21 kU bU lU++q21 kU bU rU++q21 kU b2U l'U++q21 kU b2U r'U
 let cFalse:=q21 kU bU lU++q21 kU bU l'U++q21 kU b2U rU++q21 kU b2U r'U
 sel (q17 remBits) cFalse cTrue
lemma vr {uk up uu:List Bool→List Bool} (hk:qe uk) (hp:qe up) (hu:qe uu):
 qe (fun s=>q21 (uk s) (up s) (uu s)):=
 qi (qi (q61 hk hp) (q61 hk (qi (qh [true]) hp))) (q61 hk hu)
lemma j2 {uk unU uq ue ui uj ub urem:List Bool→List Bool}
 (hk:qe uk) (hn:qe unU) (hq:qe uq) (he:qe ue)
 (hi:qe ui) (hj:qe uj) (hbu:qe ub) (hrem:qe urem):
 qe (fun s=>yG (uk s) (unU s) (uq s) (ue s) (ui s) (uj s) (ub s) (urem s)):=by
 have h2j:=qi hj hj
 have h2i:=qi hi hi
 have hl:=v3 hq he hi h2j
 have hl':=v3 hq he hi (qi (qh [true]) h2j)
 have hr:=v3 hq he (qi hn hj) h2i
 have hr':=v3 hq he (qi hn hj) (qi (qh [true]) h2i)
 have hb2:=qi (qh [true,true]) hbu
 have hcT:=qi (qi (qi (vr hk hbu hl) (vr hk hbu hr))
  (vr hk hb2 hl')) (vr hk hb2 hr')
 have hcF:=qi (qi (qi (vr hk hbu hl) (vr hk hbu hl'))
  (vr hk hb2 hr)) (vr hk hb2 hr')
 exact zh (qa hrem q35) hcF hcT
def cellStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let nU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let qU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let eU:=(unpairB r4).1
 let r5:=(unpairB r4).2
 let iU:=(unpairB r5).1
 let r6:=(unpairB r5).2
 let jU:=(unpairB r6).1
 let r7:=(unpairB r6).2
 let bU:=(unpairB r7).1
 let r8:=(unpairB r7).2
 let remBits:=(unpairB r8).1
 let acc:=(unpairB r8).2
 let chunk:=zj boundU (yG kU nU qU eU iU jU bU remBits)
 qc boundU (qc kU (qc nU (qc qU (qc eU (qc iU (qc (true::jU)
  (qc (true::true::true::true::bU) (qc remBits.tail (acc++chunk)))))))))
lemma wC:qe cellStep:=by
 have hb:=qf; have hr1:=qb
 have hk:=qa hr1 qf; have hr2:=qa hr1 qb
 have hn:=qa hr2 qf; have hr3:=qa hr2 qb
 have hq:=qa hr3 qf; have hr4:=qa hr3 qb
 have he:=qa hr4 qf; have hr5:=qa hr4 qb
 have hi:=qa hr5 qf; have hr6:=qa hr5 qb
 have hj:=qa hr6 qf; have hr7:=qa hr6 qb
 have hbu:=qa hr7 qf; have hr8:=qa hr7 qb
 have hrem:=qa hr8 qf; have hacc:=qa hr8 qb
 have hchunk:=q24 hb (j2 hk hn hq he hi hj hbu hrem)
 exact q39 (qd hb (qd hk (qd hn (qd hq (qd he (qd hi
  (qd (qi (qh [true]) hj)
    (qd (qi (qh [true,true,true,true]) hbu)
      (qd (qa hrem vW) (qi hacc hchunk)))))))))) (fun _=>rfl)
def yW (kU nU qU eU iU bStart rowBits:List Bool):List Bool:=
 let boundU:=qJ (List.replicate 12 true) (true::kU)
 let init:=qc boundU (qc kU (qc nU (qc qU (qc eU (qc iU
  (qc [] (qc bStart (qc rowBits []))))))))
 let fin:=cellStep^[nU.length] init
 (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2).2).2).2).2
lemma qah {uk unU uq ue ui ub ur:List Bool→List Bool}
 (hk:qe uk) (hn:qe unU) (hq:qe uq) (he:qe ue) (hi:qe ui) (hb:qe ub) (hr:qe ur):
 qe (fun s=>yW (uk s) (unU s) (uq s) (ue s) (ui s) (ub s) (ur s)):=by
 have hbound:=q42 (qh (List.replicate 12 true)) (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd hn (qd hq (qd he (qd hi
  (qd (qh []) (qd hb (qd hr (qh [])))))))))
 have hfin:=q18 25 wC
  (fun y=>by dsimp only [cellStep]; rw [qj])
  (fun y=>by
    dsimp only [cellStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set nU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set qU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set eU:=(unpairB r4).1; set r5:=(unpairB r4).2
    set iU:=(unpairB r5).1; set r6:=(unpairB r5).2
    set jU:=(unpairB r6).1; set r7:=(unpairB r6).2
    set bU:=(unpairB r7).1; set r8:=(unpairB r7).2
    set remBits:=(unpairB r8).1; set acc:=(unpairB r8).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * nU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * qU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * eU.length + r5.length≤r4.length:=q0 r4
    have h6:2 * iU.length + r6.length≤r5.length:=q0 r5
    have h7:2 * jU.length + r7.length≤r6.length:=q0 r6
    have h8:2 * bU.length + r8.length≤r7.length:=q0 r7
    have h9:2 * remBits.length + acc.length≤r8.length:=q0 r8
    rw [q7,q7,q7,q7,q7,q7,q7,q7,q7,List.length_append]
    simp only [List.length_cons]
    have hc:(zj boundU (yG kU nU qU eU iU jU bU remBits)).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    have hrt:remBits.tail.length≤remBits.length:=by cases remBits <;> simp
    omega)
  hn hinit
 exact q39 (qa (qa (qa (qa (qa (qa (qa (qa (qa hfin
  qb) qb) qb) qb) qb) qb) qb)
  qb) qb) (fun _=>rfl)
def qH (k q e n b i j:ℕ) (a:Bool):List Bool:=
 let qx:=fun block t=>block * q + (if t=0 then 0 else if t=e + 1 then 2 * e else 2 * t - 1)
 let l:=qx i (2 * j)
 let l':=qx i (2 * j + 1)
 let r:=qx (n + j) (2 * i)
 let r':=qx (n + j) (2 * i + 1)
 let f:=fun p u=>qm k p++qm k (p + 1)++qm k u
 if a then f b l++f b r++f (b + 2) l'++f (b + 2) r'
 else f b l++f b l'++f (b + 2) r++f (b + 2) r'
lemma wB {n:ℕ} (kU nU qU eU iU bStart:List Bool) (hk:0 < kU.length)
 (hn:nU.length=n) (rowFn:ℕ→Bool) (tailBits:List Bool):
 yW kU nU qU eU iU bStart ((List.range n).map rowFn++tailBits)=
  (List.range n).flatMap (fun j=>
    qH kU.length qU.length eU.length n (bStart.length + 4 * j) iU.length j (rowFn j)):=by
 dsimp only [yW]
 set boundU:=qJ (List.replicate 12 true) (true::kU)
 have hblen:boundU.length=12 * (kU.length + 1):=by simp [boundU,qJ]
 have hiter:∀ t≤n,∃ (jU bU:List Bool),
  cellStep^[t] (qc boundU (qc kU (qc nU (qc qU (qc eU (qc iU
   (qc [] (qc bStart (qc ((List.range n).map rowFn++tailBits) [])))))))))=
   qc boundU (qc kU (qc nU (qc qU (qc eU (qc iU
    (qc jU (qc bU (qc (((List.range n).drop t).map rowFn++tailBits)
      ((List.range t).flatMap (fun j=>
        qH kU.length qU.length eU.length n (bStart.length + 4 * j) iU.length j (rowFn j)))))))))))∧
  jU.length=t∧bU.length=bStart.length + 4 * t:=by
  intro t ht
  induction t with
  | zero=>exact ⟨[],bStart,by simp,rfl,by omega⟩
  | succ t ih=>
    obtain ⟨jU,bU,hstep,hjl,hbl⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [cellStep]
    simp only [qj]
    have hdrop:(List.range n).drop t=t::(List.range n).drop (t + 1):=by
     rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hdrop,List.map_cons,List.cons_append,List.tail_cons]
    have hport:∀ (blkU argU:List Bool),(ve qU eU blkU argU).length=
     blkU.length * qU.length +
     (if argU.length=0 then 0 else if argU.length=eU.length + 1 then 2 * eU.length else 2 * argU.length - 1):=
     fun blkU argU=>y9 qU eU blkU argU
    have h2j:(jU++jU).length=2 * t:=by rw [List.length_append,hjl]; omega
    have h2j1:(true::(jU++jU)).length=2 * t + 1:=by rw [List.length_cons,h2j]
    have h2i:(iU++iU).length=2 * iU.length:=by rw [List.length_append]; omega
    have h2i1:(true::(iU++iU)).length=2 * iU.length + 1:=by rw [List.length_cons,h2i]
    have hnj:(nU++jU).length=n + t:=by rw [List.length_append,hn,hjl]
    have hle:∀ (a b c d:List Bool),
     (q21 kU bU a++q21 kU bU b++q21 kU (true::true::bU) c++q21 kU (true::true::bU) d).length≤
       boundU.length:=by
     intro a b c d
     rw [List.length_append,List.length_append,List.length_append,
      yY _ _ _ hk,yY _ _ _ hk,yY _ _ _ hk,yY _ _ _ hk,hblen]
     have:=Nat.log2_le_self kU.length; omega
    have hchunk:zj boundU (yG kU nU qU eU iU jU bU
     (rowFn t::(((List.range n).drop (t + 1)).map rowFn++tailBits)))=
     qH kU.length qU.length eU.length n (bStart.length + 4 * t) iU.length t (rowFn t):=by
     dsimp only [yG,qH]
     cases hrt:rowFn t
     · simp only [q17,sel,↓reduceIte,Bool.false_eq_true]
       rw [q12,List.take_of_length_le (hle _ _ _ _)]
       rw [zt _ _ _ hk,zt _ _ _ hk,zt _ _ _ hk,zt _ _ _ hk]
       simp only [List.length_cons,hbl,hport,h2j,h2j1,h2i,h2i1,hnj]
     · simp only [q17,sel,List.cons_ne_nil,↓reduceIte]
       rw [q12,List.take_of_length_le (hle _ _ _ _)]
       rw [zt _ _ _ hk,zt _ _ _ hk,zt _ _ _ hk,zt _ _ _ hk]
       simp only [List.length_cons,hbl,hport,h2j,h2j1,h2i,h2i1,hnj]
    rw [hchunk]
    refine ⟨true::jU,true::true::true::true::bU,?_,by simp [hjl],by simp [hbl]; omega⟩
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
 obtain ⟨jU,bU,hfin,_,_⟩:=hiter n le_rfl
 rw [hn,hfin]; simp only [qj]
def cellOuterStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let nU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let qU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let eU:=(unpairB r4).1
 let r5:=(unpairB r4).2
 let iU:=(unpairB r5).1
 let r6:=(unpairB r5).2
 let bU:=(unpairB r6).1
 let r7:=(unpairB r6).2
 let remBits:=(unpairB r7).1
 let acc:=(unpairB r7).2
 let chunk:=zj boundU (yW kU nU qU eU iU bU remBits)
 let stepB:=zj boundU (qJ (List.replicate 4 true) nU)
 qc boundU (qc kU (qc nU (qc qU (qc eU (qc (true::iU)
  (qc (bU++stepB) (qc (vN nU remBits) (acc++chunk))))))))
lemma uL:qe cellOuterStep:=by
 have hb:=qf; have hr1:=qb
 have hk:=qa hr1 qf; have hr2:=qa hr1 qb
 have hn:=qa hr2 qf; have hr3:=qa hr2 qb
 have hq:=qa hr3 qf; have hr4:=qa hr3 qb
 have he:=qa hr4 qf; have hr5:=qa hr4 qb
 have hi:=qa hr5 qf; have hr6:=qa hr5 qb
 have hbu:=qa hr6 qf; have hr7:=qa hr6 qb
 have hrem:=qa hr7 qf; have hacc:=qa hr7 qb
 have hchunk:=q24 hb (qah hk hn hq he hi hbu hrem)
 have hstepB:=q24 hb (q42 (qh (List.replicate 4 true)) hn)
 exact qd hb (qd hk (qd hn (qd hq (qd he
  (qd (qi (qh [true]) hi)
    (qd (qi hbu hstepB) (qd (yS hn hrem) (qi hacc hchunk))))))))
def uH (kU nU qU eU vqU bits:List Bool):List Bool:=
 let boundU:=qJ (qJ (List.replicate 12 true) nU) (true::kU)
 let init:=qc boundU (qc kU (qc nU (qc qU (qc eU
  (qc [] (qc vqU (qc bits [])))))))
 let fin:=cellOuterStep^[nU.length] init
 (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2).2).2).2
lemma qag {uk unU uq ue uvq ub:List Bool→List Bool}
 (hk:qe uk) (hn:qe unU) (hq:qe uq) (he:qe ue) (hvq:qe uvq) (hb:qe ub):
 qe (fun s=>uH (uk s) (unU s) (uq s) (ue s) (uvq s) (ub s)):=by
 have hbound:=q42 (q42 (qh (List.replicate 12 true)) hn) (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd hn (qd hq (qd he
  (qd (qh []) (qd hvq (qd hb (qh []))))))))
 have hfin:=q18 25 uL
  (fun y=>by dsimp only [cellOuterStep]; rw [qj])
  (fun y=>by
    dsimp only [cellOuterStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set nU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set qU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set eU:=(unpairB r4).1; set r5:=(unpairB r4).2
    set iU:=(unpairB r5).1; set r6:=(unpairB r5).2
    set bU:=(unpairB r6).1; set r7:=(unpairB r6).2
    set remBits:=(unpairB r7).1; set acc:=(unpairB r7).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * nU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * qU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * eU.length + r5.length≤r4.length:=q0 r4
    have h6:2 * iU.length + r6.length≤r5.length:=q0 r5
    have h7:2 * bU.length + r7.length≤r6.length:=q0 r6
    have h8:2 * remBits.length + acc.length≤r7.length:=q0 r7
    rw [q7,q7,q7,q7,q7,q7,q7,q7,List.length_append,List.length_append,List.length_cons]
    have hc:(zj boundU (yW kU nU qU eU iU bU remBits)).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    have hs:(zj boundU (qJ (List.replicate 4 true) nU)).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    have hd:(vN nU remBits).length≤remBits.length:=by
     rw [q40,List.length_drop]; omega
    omega)
  hn hinit
 exact q39 (qa (qa (qa (qa (qa (qa (qa (qa hfin
  qb) qb) qb) qb) qb) qb)
  qb) qb) (fun _=>rfl)
lemma wA {n:ℕ} (kU nU qU eU vqU:List Bool) (hk:0 < kU.length)
 (hn:nU.length=n) (A:Fin n→Fin n→Bool):
 let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
 uH kU nU qU eU vqU (cells.map (fun z=>A z.1 z.2))=
  (List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>
    qH kU.length qU.length eU.length n
     (vqU.length + 4 * (i * n + j)) i j
     (if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false))):=by
 intro cells
 dsimp only [uH]
 set boundU:=qJ (qJ (List.replicate 12 true) nU) (true::kU)
 have hblen:boundU.length=12 * n * (kU.length + 1):=by simp [boundU,qJ,hn]
 have hbits_eq:cells.map (fun z=>A z.1 z.2)=
  (List.range n).flatMap (fun i=>(List.range n).map (fun j=>
    if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false)):=by
  dsimp only [cells]
  rw [List.map_flatMap,zK,zK]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi1 _
    simp only [List.length_map,List.length_finRange] at hi1
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    apply List.ext_getElem
    · simp
    · intro j hj1 _
      simp only [List.length_map,List.length_finRange] at hj1
      simp [hi1,hj1]
 rw [hbits_eq]
 let rowFn (i:ℕ) (j:ℕ):Bool:=
  if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false
 have hiter:∀ t≤n,∃ (iU bU:List Bool),
  cellOuterStep^[t] (qc boundU (qc kU (qc nU (qc qU (qc eU
   (qc [] (qc vqU (qc ((List.range n).flatMap (fun i=>(List.range n).map (rowFn i))) []))))))))=
   qc boundU (qc kU (qc nU (qc qU (qc eU (qc iU (qc bU
    (qc (((List.range n).drop t).flatMap (fun i=>(List.range n).map (rowFn i)))
      ((List.range t).flatMap (fun i=>(List.range n).flatMap (fun j=>
        qH kU.length qU.length eU.length n (vqU.length + 4 * (i * n + j)) i j (rowFn i j)))))))))))∧
  iU.length=t∧bU.length=vqU.length + 4 * (t * n):=by
  intro t ht
  induction t with
  | zero=>exact ⟨[],vqU,by simp,rfl,by omega⟩
  | succ t ih=>
    obtain ⟨iU,bU,hstep,hil,hbl⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [cellOuterStep]
    simp only [qj]
    have hdrop:(List.range n).drop t=t::(List.range n).drop (t + 1):=by
     rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hdrop,List.flatMap_cons]
    have hdropN:vN nU ((List.range n).map (rowFn t)++
     ((List.range n).drop (t + 1)).flatMap (fun i=>(List.range n).map (rowFn i)))=
     ((List.range n).drop (t + 1)).flatMap (fun i=>(List.range n).map (rowFn i)):=by
     rw [q40,hn,List.drop_append_of_le_length (by simp),List.drop_eq_nil_of_le (by simp),
      List.nil_append]
    have hcr:=wB kU nU qU eU iU bU hk hn (rowFn t)
     (((List.range n).drop (t + 1)).flatMap (fun i=>(List.range n).map (rowFn i)))
    rw [hil,hbl] at hcr
    have hcr2:∀ j,bU.length + 4 * j=vqU.length + 4 * (t * n + j):=fun j=>by
     rw [hbl]; ring
    have hcrLen:(yW kU nU qU eU iU bU ((List.range n).map (rowFn t)++
     ((List.range n).drop (t + 1)).flatMap (fun i=>(List.range n).map (rowFn i)))).length≤
     boundU.length:=by
     rw [hcr,hblen]
     have h1:∀ j∈List.range n,
      (qH kU.length qU.length eU.length n (vqU.length + 4 * (t * n) + 4 * j) t j
        (rowFn t j)).length=12 * (kU.length.log2 + 1):=by
      intro j _
      dsimp only [qH]
      split_ifs <;> simp only [List.length_append,qm,List.length_map,List.length_range] <;> omega
     have hfm:∀ (L:List ℕ) (f:ℕ→List Bool) (c:ℕ),(∀ a∈L,(f a).length=c)→
      (L.flatMap f).length=L.length * c:=by
      intro L f c hf
      induction L with
      | nil=>simp
      | cons a r ihL=>
        rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
         ihL (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
     rw [hfm _ _ _ h1,List.length_range]
     have hlog:kU.length.log2≤kU.length:=Nat.log2_le_self kU.length
     calc n * (12 * (kU.length.log2 + 1))
      =12 * n * (kU.length.log2 + 1):=by ring
      _≤12 * n * (kU.length + 1):=Nat.mul_le_mul_left _ (by omega)
    have hstepBle:(qJ (List.replicate 4 true) nU).length≤boundU.length:=by
     rw [hblen]; simp only [qJ,qN,List.length_replicate,hn]; nlinarith
    rw [q12,List.take_of_length_le hstepBle,q12,List.take_of_length_le hcrLen,hdropN,hcr]
    have haccEq:
     (List.range t).flatMap (fun i=>(List.range n).flatMap (fun j=>
       qH kU.length qU.length eU.length n (vqU.length + 4 * (i * n + j)) i j (rowFn i j)))++
     (List.range n).flatMap (fun j=>
       qH kU.length qU.length eU.length n (vqU.length + 4 * (t * n) + 4 * j) t j (rowFn t j))=
     (List.range (t + 1)).flatMap (fun i=>(List.range n).flatMap (fun j=>
       qH kU.length qU.length eU.length n (vqU.length + 4 * (i * n + j)) i j (rowFn i j))):=by
     rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
     apply congrArg (List.append _)
     apply List.flatMap_congr; intro j _
     exact congrArg (fun b=>qH kU.length qU.length eU.length n b t j (rowFn t j)) (by ring)
    refine ⟨true::iU,bU++qJ (List.replicate 4 true) nU,
     congrArg (fun acc=>qc boundU (qc kU (qc nU (qc qU (qc eU
      (qc (true::iU) (qc (bU++qJ (List.replicate 4 true) nU)
        (qc (((List.range n).drop (t + 1)).flatMap (fun i=>(List.range n).map (rowFn i))) acc))))))))
      haccEq,
     by simp [hil],?_⟩
    simp only [List.length_append,qJ,qN,List.length_replicate,hn,hbl]; ring
 obtain ⟨iU,bU,hfin,_,_⟩:=hiter n le_rfl
 rw [hn,hfin]; simp only [qj]; rfl
def spareStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let nU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let qU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let eU:=(unpairB r4).1
 let r5:=(unpairB r4).2
 let uU:=(unpairB r5).1
 let r6:=(unpairB r5).2
 let jU:=(unpairB r6).1
 let r7:=(unpairB r6).2
 let bU:=(unpairB r7).1
 let acc:=(unpairB r7).2
 let p1:=ve qU eU uU (nU++nU++jU++jU)
 let p2:=ve qU eU uU (true::(nU++nU++jU++jU))
 let chunk:=zj boundU (q21 kU bU p1++q21 kU bU p2)
 qc boundU (qc kU (qc nU (qc qU (qc eU (qc uU (qc (true::jU)
  (qc (true::true::bU) (acc++chunk))))))))
lemma j5:qe spareStep:=by
 have hb:=qf; have hr1:=qb
 have hk:=qa hr1 qf; have hr2:=qa hr1 qb
 have hn:=qa hr2 qf; have hr3:=qa hr2 qb
 have hq:=qa hr3 qf; have hr4:=qa hr3 qb
 have he:=qa hr4 qf; have hr5:=qa hr4 qb
 have hu:=qa hr5 qf; have hr6:=qa hr5 qb
 have hj:=qa hr6 qf; have hr7:=qa hr6 qb
 have hbu:=qa hr7 qf; have hacc:=qa hr7 qb
 have harg:=qi (qi (qi hn hn) hj) hj
 have hp1:=v3 hq he hu harg
 have hp2:=v3 hq he hu (qi (qh [true]) harg)
 have hchunk:=q24 hb (qi (vr hk hbu hp1) (vr hk hbu hp2))
 exact qd hb (qd hk (qd hn (qd hq (qd he (qd hu
  (qd (qi (qh [true]) hj)
    (qd (qi (qh [true,true]) hbu) (qi hacc hchunk))))))))
def yx (kU nU qU eU hU uU bStart:List Bool):List Bool:=
 let boundU:=qJ (List.replicate 6 true) (true::kU)
 let init:=qc boundU (qc kU (qc nU (qc qU (qc eU (qc uU
  (qc [] (qc bStart [])))))))
 let fin:=spareStep^[(true::hU).length] init
 (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2).2).2).2
lemma wH {uk unU uq ue uh uu ub:List Bool→List Bool}
 (hk:qe uk) (hn:qe unU) (hq:qe uq) (he:qe ue) (hh:qe uh) (hu:qe uu) (hb:qe ub):
 qe (fun s=>yx (uk s) (unU s) (uq s) (ue s) (uh s) (uu s) (ub s)):=by
 have hbound:=q42 (qh (List.replicate 6 true)) (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd hn (qd hq (qd he (qd hu
  (qd (qh []) (qd hb (qh []))))))))
 have hfin:=q18 22 j5
  (fun y=>by dsimp only [spareStep]; rw [qj])
  (fun y=>by
    dsimp only [spareStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set nU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set qU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set eU:=(unpairB r4).1; set r5:=(unpairB r4).2
    set uU:=(unpairB r5).1; set r6:=(unpairB r5).2
    set jU:=(unpairB r6).1; set r7:=(unpairB r6).2
    set bU:=(unpairB r7).1; set acc:=(unpairB r7).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * nU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * qU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * eU.length + r5.length≤r4.length:=q0 r4
    have h6:2 * uU.length + r6.length≤r5.length:=q0 r5
    have h7:2 * jU.length + r7.length≤r6.length:=q0 r6
    have h8:2 * bU.length + acc.length≤r7.length:=q0 r7
    rw [q7,q7,q7,q7,q7,q7,q7,q7,List.length_append]
    simp only [List.length_cons]
    have hc:(zj boundU (q21 kU bU (ve qU eU uU (nU++nU++jU++jU))++
     q21 kU bU (ve qU eU uU (true::(nU++nU++jU++jU))))).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    omega)
  (qi (qh [true]) hh) hinit
 exact q39 (qa (qa (qa (qa (qa (qa (qa (qa hfin
  qb) qb) qb) qb) qb) qb)
  qb) qb) (fun _=>rfl)
def qD (k q e n b u j:ℕ):List Bool:=
 let qx:=fun block t=>block * q + (if t=0 then 0 else if t=e + 1 then 2 * e else 2 * t - 1)
 let p1:=qx u (2 * n + 2 * j)
 let p2:=qx u (2 * n + 2 * j + 1)
 let f:=fun p w=>qm k p++qm k (p + 1)++qm k w
 f b p1++f b p2
lemma wq (kU nU qU eU hU uU bStart:List Bool) (hk:0 < kU.length):
 yx kU nU qU eU hU uU bStart=
  (List.range (hU.length + 1)).flatMap (fun j=>
    qD kU.length qU.length eU.length nU.length (bStart.length + 2 * j) uU.length j):=by
 dsimp only [yx]
 set boundU:=qJ (List.replicate 6 true) (true::kU)
 have hblen:boundU.length=6 * (kU.length + 1):=by simp [boundU,qJ]
 have hiter:∀ t:ℕ,∃ (jU bU:List Bool),
  spareStep^[t] (qc boundU (qc kU (qc nU (qc qU (qc eU (qc uU
   (qc [] (qc bStart []))))))))=
   qc boundU (qc kU (qc nU (qc qU (qc eU (qc uU (qc jU (qc bU
    ((List.range t).flatMap (fun j=>
      qD kU.length qU.length eU.length nU.length (bStart.length + 2 * j) uU.length j)))))))))∧
  jU.length=t∧bU.length=bStart.length + 2 * t:=by
  intro t
  induction t with
  | zero=>exact ⟨[],bStart,by simp,rfl,by omega⟩
  | succ t ih=>
    obtain ⟨jU,bU,hstep,hjl,hbl⟩:=ih
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [spareStep]
    simp only [qj]
    have harg:(nU++nU++jU++jU).length=2 * nU.length + 2 * t:=by
     simp only [List.length_append,hjl]; omega
    have harg1:(true::(nU++nU++jU++jU)).length=2 * nU.length + 2 * t + 1:=by
     rw [List.length_cons,harg]
    have hle:(q21 kU bU (ve qU eU uU (nU++nU++jU++jU))++
     q21 kU bU (ve qU eU uU (true::(nU++nU++jU++jU)))).length≤boundU.length:=by
     rw [List.length_append,yY _ _ _ hk,yY _ _ _ hk,hblen]
     have:=Nat.log2_le_self kU.length; omega
    rw [q12,List.take_of_length_le hle,zt _ _ _ hk,zt _ _ _ hk]
    have hchunk:
     qm kU.length bU.length++qm kU.length (bU.length + 1)++
      qm kU.length (ve qU eU uU (nU++nU++jU++jU)).length++
     (qm kU.length bU.length++qm kU.length (bU.length + 1)++
       qm kU.length (ve qU eU uU (true::(nU++nU++jU++jU))).length)=
     qD kU.length qU.length eU.length nU.length (bStart.length + 2 * t) uU.length t:=by
     dsimp only [qD]
     rw [y9,y9,harg,harg1,hbl]
    rw [hchunk]
    refine ⟨true::jU,true::true::bU,?_,by simp [hjl],by simp [hbl]; omega⟩
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
 obtain ⟨jU,bU,hfin,_,_⟩:=hiter (hU.length + 1)
 rw [List.length_cons,hfin]; simp only [qj]
def spareOuterStep (y:List Bool):List Bool:=
 let boundU:=(unpairB y).1
 let r1:=(unpairB y).2
 let kU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let nU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let qU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let eU:=(unpairB r4).1
 let r5:=(unpairB r4).2
 let hU:=(unpairB r5).1
 let r6:=(unpairB r5).2
 let uU:=(unpairB r6).1
 let r7:=(unpairB r6).2
 let bU:=(unpairB r7).1
 let acc:=(unpairB r7).2
 let chunk:=zj boundU (yx kU nU qU eU hU uU bU)
 let stepB:=zj boundU ((true::hU)++(true::hU))
 qc boundU (qc kU (qc nU (qc qU (qc eU (qc hU (qc (true::uU)
  (qc (bU++stepB) (acc++chunk))))))))
lemma ug:qe spareOuterStep:=by
 have hb:=qf; have hr1:=qb
 have hk:=qa hr1 qf; have hr2:=qa hr1 qb
 have hn:=qa hr2 qf; have hr3:=qa hr2 qb
 have hq:=qa hr3 qf; have hr4:=qa hr3 qb
 have he:=qa hr4 qf; have hr5:=qa hr4 qb
 have hh:=qa hr5 qf; have hr6:=qa hr5 qb
 have hu:=qa hr6 qf; have hr7:=qa hr6 qb
 have hbu:=qa hr7 qf; have hacc:=qa hr7 qb
 have hchunk:=q24 hb (wH hk hn hq he hh hu hbu)
 have hh1:=qi (qh [true]) hh
 have hstepB:=q24 hb (qi hh1 hh1)
 exact qd hb (qd hk (qd hn (qd hq (qd he (qd hh
  (qd (qi (qh [true]) hu) (qd (qi hbu hstepB) (qi hacc hchunk))))))))
def kR (kU nU vU qU eU hU bStart:List Bool):List Bool:=
 let boundU:=qJ (qJ (List.replicate 6 true) (true::hU)) (true::kU)
 let init:=qc boundU (qc kU (qc nU (qc qU (qc eU (qc hU
  (qc [] (qc bStart [])))))))
 let fin:=spareOuterStep^[vU.length] init
 (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2).2).2).2
lemma wG {uk unU uv uq ue uh ub:List Bool→List Bool}
 (hk:qe uk) (hn:qe unU) (hv:qe uv) (hq:qe uq) (he:qe ue) (hh:qe uh) (hb:qe ub):
 qe (fun s=>kR (uk s) (unU s) (uv s) (uq s) (ue s) (uh s) (ub s)):=by
 have hbound:=q42 (q42 (qh (List.replicate 6 true)) (qi (qh [true]) hh))
  (qi (qh [true]) hk)
 have hinit:=qd hbound (qd hk (qd hn (qd hq (qd he (qd hh
  (qd (qh []) (qd hb (qh []))))))))
 have hfin:=q18 22 ug
  (fun y=>by dsimp only [spareOuterStep]; rw [qj])
  (fun y=>by
    dsimp only [spareOuterStep]
    set boundU:=(unpairB y).1; set r1:=(unpairB y).2
    set kU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set nU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set qU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set eU:=(unpairB r4).1; set r5:=(unpairB r4).2
    set hU:=(unpairB r5).1; set r6:=(unpairB r5).2
    set uU:=(unpairB r6).1; set r7:=(unpairB r6).2
    set bU:=(unpairB r7).1; set acc:=(unpairB r7).2
    have h1:2 * boundU.length + r1.length≤y.length:=q0 y
    have h2:2 * kU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * nU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * qU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * eU.length + r5.length≤r4.length:=q0 r4
    have h6:2 * hU.length + r6.length≤r5.length:=q0 r5
    have h7:2 * uU.length + r7.length≤r6.length:=q0 r6
    have h8:2 * bU.length + acc.length≤r7.length:=q0 r7
    rw [q7,q7,q7,q7,q7,q7,q7,q7,List.length_append,List.length_append,List.length_cons]
    have hc:(zj boundU (yx kU nU qU eU hU uU bU)).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    have hs:(zj boundU ((true::hU)++(true::hU))).length≤boundU.length:=by
     rw [q12,List.length_take]; exact Nat.min_le_left _ _
    omega)
  hv hinit
 exact q39 (qa (qa (qa (qa (qa (qa (qa (qa hfin
  qb) qb) qb) qb) qb) qb)
  qb) qb) (fun _=>rfl)
lemma wm (kU nU vU qU eU hU bStart:List Bool) (hk:0 < kU.length):
 kR kU nU vU qU eU hU bStart=
  (List.range vU.length).flatMap (fun u=>(List.range (hU.length + 1)).flatMap (fun j=>
    qD kU.length qU.length eU.length nU.length
     (bStart.length + 2 * (u * (hU.length + 1) + j)) u j)):=by
 dsimp only [kR]
 set boundU:=qJ (qJ (List.replicate 6 true) (true::hU)) (true::kU)
 have hblen:boundU.length=6 * (hU.length + 1) * (kU.length + 1):=by simp [boundU,qJ]
 have hiter:∀ t:ℕ,∃ (uU bU:List Bool),
  spareOuterStep^[t] (qc boundU (qc kU (qc nU (qc qU (qc eU (qc hU
   (qc [] (qc bStart []))))))))=
   qc boundU (qc kU (qc nU (qc qU (qc eU (qc hU (qc uU (qc bU
    ((List.range t).flatMap (fun u=>(List.range (hU.length + 1)).flatMap (fun j=>
      qD kU.length qU.length eU.length nU.length
       (bStart.length + 2 * (u * (hU.length + 1) + j)) u j))))))))))∧
  uU.length=t∧bU.length=bStart.length + 2 * (t * (hU.length + 1)):=by
  intro t
  induction t with
  | zero=>exact ⟨[],bStart,by simp,rfl,by omega⟩
  | succ t ih=>
    obtain ⟨uU,bU,hstep,hul,hbl⟩:=ih
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [spareOuterStep]
    simp only [qj]
    have hsr:=wq kU nU qU eU hU uU bU hk
    rw [hul,hbl] at hsr
    have hsrLen:(yx kU nU qU eU hU uU bU).length≤boundU.length:=by
     rw [hsr,hblen]
     have h1:∀ j∈List.range (hU.length + 1),
      (qD kU.length qU.length eU.length nU.length
        (bStart.length + 2 * (t * (hU.length + 1)) + 2 * j) t j).length=
      6 * (kU.length.log2 + 1):=by
      intro j _
      dsimp only [qD]
      simp only [List.length_append,qm,List.length_map,List.length_range]; omega
     have hfm:∀ (L:List ℕ) (f:ℕ→List Bool) (c:ℕ),(∀ a∈L,(f a).length=c)→
      (L.flatMap f).length=L.length * c:=by
      intro L f c hf
      induction L with
      | nil=>simp
      | cons a r ihL=>
        rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
         ihL (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
     rw [hfm _ _ _ h1,List.length_range]
     have hlog:kU.length.log2≤kU.length:=Nat.log2_le_self kU.length
     calc (hU.length + 1) * (6 * (kU.length.log2 + 1))
      =6 * (hU.length + 1) * (kU.length.log2 + 1):=by ring
      _≤6 * (hU.length + 1) * (kU.length + 1):=Nat.mul_le_mul_left _ (by omega)
    have hstepBle:((true::hU)++(true::hU)).length≤boundU.length:=by
     rw [hblen]; simp only [List.length_append,List.length_cons]; nlinarith
    rw [q12,List.take_of_length_le hstepBle,q12,List.take_of_length_le hsrLen,hsr]
    have haccEq:
     (List.range t).flatMap (fun u=>(List.range (hU.length + 1)).flatMap (fun j=>
       qD kU.length qU.length eU.length nU.length
        (bStart.length + 2 * (u * (hU.length + 1) + j)) u j))++
     (List.range (hU.length + 1)).flatMap (fun j=>
       qD kU.length qU.length eU.length nU.length
        (bStart.length + 2 * (t * (hU.length + 1)) + 2 * j) t j)=
     (List.range (t + 1)).flatMap (fun u=>(List.range (hU.length + 1)).flatMap (fun j=>
       qD kU.length qU.length eU.length nU.length
        (bStart.length + 2 * (u * (hU.length + 1) + j)) u j)):=by
     rw [List.range_succ (n:=t),List.flatMap_append,List.flatMap_singleton]
     apply congrArg (List.append _)
     apply List.flatMap_congr; intro j _
     exact congrArg (fun b=>qD kU.length qU.length eU.length nU.length b t j) (by ring)
    refine ⟨true::uU,bU++((true::hU)++(true::hU)),
     congrArg (fun acc=>qc boundU (qc kU (qc nU (qc qU (qc eU (qc hU
      (qc (true::uU) (qc (bU++((true::hU)++(true::hU))) acc))))))))
      haccEq,
     by simp [hul],?_⟩
    simp only [List.length_append,List.length_cons,hbl]; ring
 obtain ⟨uU,bU,hfin,_,_⟩:=hiter vU.length
 rw [hfin]; simp only [qj]
def wV (s:List Bool):List Bool:=hd s++hd s
def wE (s:List Bool):List Bool:=wV s++hd (dropN s)++hd (dropN s)
def wQ (s:List Bool):List Bool:=true::(wE s++wE s)
def wM (s:List Bool):List Bool:=qJ (wV s) (true::(hd s++hd (dropN s)))
def wVQ (s:List Bool):List Bool:=qJ (wV s) (wQ s)
def wK (s:List Bool):List Bool:=wVQ s++wM s++wM s
def wBSpare (s:List Bool):List Bool:=wVQ s++qJ (List.replicate 4 true) (qJ (hd s) (hd s))
def writeFn (s:List Bool):List Bool:=
 (q47 (wK s)++[false])++
 uK (wK s) (wV s) (wQ s) (wE s)++
 uH (wK s) (hd s) (wQ s) (wE s) (wVQ s) (dropN (dropN s))++
 kR (wK s) (hd s) (wV s) (wQ s) (wE s) (hd (dropN s)) (wBSpare s)
lemma uo:qe wV:=qi vb vb
lemma um:qe wE:=qi (qi uo (qa va vb)) (qa va vb)
lemma jk:qe wQ:=qi (qh [true]) (qi um um)
lemma qaN:qe wM:=q42 uo (qi (qh [true]) (qi vb (qa va vb)))
lemma jF:qe wVQ:=q42 uo jk
lemma jj:qe wK:=qi (qi jF qaN) qaN
lemma qak:qe wBSpare:=qi jF (q42 (qh (List.replicate 4 true)) (q42 vb vb))
lemma qal:qe writeFn:=
 qi
  (qi
    (qi
      (qi (qa jj q89) (qh [false]))
      (qaj jj uo jk um))
    (qag jj vb jk um jF (qa va va)))
  (wG jj vb uo jk um (qa va vb) qak)
lemma y6 (n:ℕ) (rest:List Bool):
 hd (List.replicate n true++[false]++rest)=un n:=by
 simp [hd,un,List.append_assoc]
lemma ym (n:ℕ) (rest:List Bool):
 dropN (List.replicate n true++[false]++rest)=rest:=by
 simp [dropN,List.append_assoc]
lemma zV {α β:Type*} (L:List α) (f:α→List β) (c:ℕ)
 (hf:∀ a∈L,(f a).length=c):(L.flatMap f).length=L.length * c:=by
 induction L with
 | nil=>simp
 | cons a r ih=>
   rw [List.flatMap_cons,List.length_append,hf a (List.mem_cons_self ..),
    ih (fun x hx=>hf x (List.mem_cons_of_mem a hx)),List.length_cons,Nat.succ_mul,add_comm]
lemma yo {α β:Type*} (a b:ℕ) (f:ℕ→ℕ→α) (F:α→ℕ→List β) (off:ℕ):
 (((List.range a).flatMap (fun i=>(List.range b).map (fun j=>f i j))).zipIdx off).flatMap
   (fun z=>F z.1 z.2)=
 (List.range a).flatMap (fun i=>(List.range b).flatMap (fun j=>F (f i j) (off + i * b + j))):=by
 induction a generalizing off with
 | zero=>simp
 | succ a ih=>
   rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.zipIdx_append,
    List.flatMap_append,ih off,List.flatMap_append,List.flatMap_singleton]
   congr 1
   have hlenL:((List.range a).flatMap (fun i=>(List.range b).map (fun j=>f i j))).length=a * b:=by
    rw [zV (List.range a) _ b (fun _ _=>by simp),List.length_range]
   rw [hlenL]
   have hrow:∀ (m:ℕ) (g:ℕ→α) (s:ℕ),
    (((List.range m).map g).zipIdx s).flatMap (fun z=>F z.1 z.2)=
    (List.range m).flatMap (fun j=>F (g j) (s + j)):=by
    intro m g s
    induction m with
    | zero=>simp
    | succ m ihm=>
      rw [List.range_succ,List.map_append,List.map_singleton,List.zipIdx_append,
       List.flatMap_append,ihm,List.length_map,List.length_range,List.zipIdx_cons,
       List.zipIdx_nil,List.flatMap_singleton,List.flatMap_append,List.flatMap_singleton]
   rw [hrow b (f a) (off + a * b)]
lemma qac {α:Type*} (M:List α) (s:ℕ):
 M.zipIdx s=M.zipIdx.map (fun z=>(z.1,z.2 + s)):=by
 induction M generalizing s with
 | nil=>rfl
 | cons x xs ih=>
   simp only [List.zipIdx_cons,List.map_cons,Nat.zero_add]
   congr 1
   rw [ih (s + 1),ih 1,List.map_map]
   apply List.map_congr_left
   intro z _
   simp only [Function.comp_apply,Prod.mk.injEq,true_and]
   omega
lemma k5 {α β:Type*} (L:List α) (g:α→β×β) (f:ℕ→β→List Bool) (off:ℕ):
 ((L.flatMap (fun a=>[(g a).1,(g a).2])).zipIdx off).flatMap (fun z=>f z.2 z.1)=
 (L.zipIdx).flatMap (fun z=>f (off + 2 * z.2) (g z.1).1++f (off + 2 * z.2 + 1) (g z.1).2):=by
 induction L generalizing off with
 | nil=>simp
 | cons a r ih=>
   simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.zipIdx_cons,
    Nat.mul_zero,add_zero,List.append_assoc]
   congr 1; congr 1
   rw [ih (off + 2),qac r 1,List.flatMap_map]
   apply List.flatMap_congr; intro z _
   have h1:off + 2 + 2 * z.2=off + 2 * (z.2 + 1):=by omega
   simp only [h1]
lemma w8 (n h:ℕ) (bits:List Bool):
 let s:=(List.replicate n true++[false])++(List.replicate h true++[false])++bits
 let v:=2 * n
 let e:=2 * (n + h)
 let q:=2 * e + 1
 let m:=2 * (n * n) + 2 * n * (h + 1)
 (hd s).length=n∧(hd (dropN s)).length=h∧dropN (dropN s)=bits∧
 (wV s).length=v∧(wE s).length=e∧(wQ s).length=q∧
 (wM s).length=m∧(wVQ s).length=v * q∧
 (wK s).length=v * q + 2 * m∧(wBSpare s).length=v * q + 4 * (n * n):=by
 intro s v e q m
 have h1:hd s=un n:=by
  dsimp only [s]; rw [List.append_assoc]; exact y6 n _
 have h2:dropN s=(List.replicate h true++[false])++bits:=by
  dsimp only [s]; rw [List.append_assoc]; exact ym n _
 have h3:hd (dropN s)=un h:=by rw [h2]; exact y6 h bits
 have h4:dropN (dropN s)=bits:=by rw [h2]; exact ym h bits
 have hnL:(hd s).length=n:=by rw [h1,qN]
 have hhL:(hd (dropN s)).length=h:=by rw [h3,qN]
 have hvL:(wV s).length=v:=by simp [wV,v,hnL]; omega
 have heL:(wE s).length=e:=by simp [wE,e,hvL,hhL]; omega
 have hqL:(wQ s).length=q:=by simp [wQ,q,heL]; omega
 have hmL:(wM s).length=m:=by
  simp only [wM,qJ,qN,List.length_cons,List.length_append,hvL,hnL,hhL,v,m]
  ring
 have hvqL:(wVQ s).length=v * q:=by simp [wVQ,qJ,hvL,hqL]
 have hkL:(wK s).length=v * q + 2 * m:=by
  simp only [wK,List.length_append,hvqL,hmL]; omega
 have hbL:(wBSpare s).length=v * q + 4 * (n * n):=by
  simp only [wBSpare,List.length_append,qJ,qN,List.length_replicate,hvqL,hnL]
 exact ⟨hnL,hhL,h4,hvL,heL,hqL,hmL,hvqL,hkL,hbL⟩
lemma vD {α β γ:Type*} (l:List α) (f:α→List β) (g:β→List γ):
 (l.flatMap f).flatMap g=l.flatMap (fun a=>(f a).flatMap g):=by
 induction l with
 | nil=>rfl
 | cons a r ih=>simp [ih]
lemma uX (n h k:ℕ) (hn:0 < n) (A:Fin n→Fin n→Bool):
 let v:=2 * n
 let e:=2 * (n + h)
 let q:=2 * e + 1
 let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
 let qx:=fun (block j:Nat)=>block * q +
  (if j=0 then 0 else if j=e + 1 then 2 * e else 2 * j - 1)
 let L1:=cells.flatMap (fun z=>
  let l:=qx z.1.val (2 * z.2.val)
  let l':=qx z.1.val (2 * z.2.val + 1)
  let r:=qx (n + z.2.val) (2 * z.1.val)
  let r':=qx (n + z.2.val) (2 * z.1.val + 1)
  if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])
 (L1.zipIdx.flatMap (fun z=>let b:=v * q + 2 * z.2; [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])).flatMap
   (fun R=>R.flatMap (qm k))=
 (List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>
   qH k q e n (v * q + 4 * (i * n + j)) i j
    (if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false))):=by
 intro v e q cells qx L1
 rw [vD]
 let gCell:Fin n×Fin n→(ℕ×ℕ)×(ℕ×ℕ):=fun z=>
  let l:=qx z.1.val (2 * z.2.val)
  let l':=qx z.1.val (2 * z.2.val + 1)
  let r:=qx (n + z.2.val) (2 * z.1.val)
  let r':=qx (n + z.2.val) (2 * z.1.val + 1)
  if A z.1 z.2 then ((l,r),(l',r')) else ((l,l'),(r,r'))
 have hL1eq:L1=cells.flatMap (fun z=>[(gCell z).1,(gCell z).2]):=by
  dsimp only [L1,gCell]
  apply List.flatMap_congr; intro z _; split_ifs <;> rfl
 let encLink:ℕ→ℕ×ℕ→List Bool:=fun idx pr=>
  let b:=v * q + 2 * idx
  ([[b,b + 1,pr.1],[b,b + 1,pr.2]]:List (List ℕ)).flatMap (fun R=>R.flatMap (qm k))
 have hstep1:(L1.zipIdx.flatMap (fun z=>encLink z.2 z.1))=
  cells.zipIdx.flatMap (fun z=>encLink (0 + 2 * z.2) (gCell z.1).1++encLink (0 + 2 * z.2 + 1) (gCell z.1).2):=by
  rw [hL1eq]; exact k5 cells gCell encLink 0
 change L1.zipIdx.flatMap (fun z=>encLink z.2 z.1)=_
 rw [hstep1]
 let cellOpt (i j:ℕ):Fin n×Fin n:=
  (⟨if hi:i < n then i else 0,by split_ifs <;> assumption⟩,
   ⟨if hj:j < n then j else 0,by split_ifs <;> assumption⟩)
 have hcellsEq:cells=(List.range n).flatMap (fun i=>(List.range n).map (fun j=>cellOpt i j)):=by
  dsimp only [cells]
  have h1:∀ (a:Fin n),(List.finRange n).map (fun j=>(a,j))=
   (List.range n).map (fun j=>(a,⟨if hj:j < n then j else 0,by split_ifs <;> assumption⟩)):=by
   intro a
   apply List.ext_getElem
   · simp
   · intro j hj1 _
     simp only [List.length_map,List.length_finRange] at hj1
     simp [hj1]
  have h2:(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))=
   ((List.finRange n).map (fun i=>(List.range n).map (fun j=>cellOpt i.val j))).flatten:=by
   rw [zK]
   congr 1
   apply List.map_congr_left; intro i _
   rw [h1 i]
   apply List.map_congr_left; intro j _
   simp [cellOpt,i.isLt]
  rw [h2,zK]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi1 _
    simp only [List.length_map,List.length_finRange] at hi1
    simp
 rw [hcellsEq,yo n n cellOpt
  (fun c idx=>encLink (0 + 2 * idx) (gCell c).1++encLink (0 + 2 * idx + 1) (gCell c).2) 0]
 apply List.flatMap_congr; intro i hi
 rw [List.mem_range] at hi
 apply List.flatMap_congr; intro j hj
 rw [List.mem_range] at hj
 dsimp only [cellOpt,gCell,encLink,qH,qx]
 simp only [hi,hj,↓reduceDIte,zero_add,List.flatMap_cons,List.flatMap_nil,List.append_nil]
 have hb1:v * q + 2 * (2 * (i * n + j))=v * q + 4 * (i * n + j):=by ring
 have hb2:v * q + 2 * (2 * (i * n + j) + 1)=v * q + 4 * (i * n + j) + 2:=by ring
 rw [hb1,hb2]
 cases A ⟨i,hi⟩ ⟨j,hj⟩ <;> simp only [Bool.false_eq_true,↓reduceIte,List.append_assoc]
lemma uF (n h k:ℕ):
 let v:=2 * n
 let e:=2 * (n + h)
 let q:=2 * e + 1
 let qx:=fun (block j:Nat)=>block * q +
  (if j=0 then 0 else if j=e + 1 then 2 * e else 2 * j - 1)
 let L2:=(List.range v).flatMap (fun u=>(List.range (h + 1)).map (fun j=>
  (qx u (2 * n + 2 * j),qx u (2 * n + 2 * j + 1))))
 ((L2.zipIdx (2 * (n * n))).flatMap (fun z=>let b:=v * q + 2 * z.2; [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])).flatMap
   (fun R=>R.flatMap (qm k))=
 (List.range v).flatMap (fun u=>(List.range (h + 1)).flatMap (fun j=>
   qD k q e n (v * q + 4 * (n * n) + 2 * (u * (h + 1) + j)) u j)):=by
 intro v e q qx L2
 rw [vD]
 let encRow:(ℕ×ℕ)→ℕ→List Bool:=fun pr idx=>
  let b:=v * q + 2 * idx
  ([[b,b + 1,pr.1],[b,b + 1,pr.2]]:List (List ℕ)).flatMap (fun R=>R.flatMap (qm k))
 change (L2.zipIdx (2 * (n * n))).flatMap (fun z=>encRow z.1 z.2)=_
 dsimp only [L2]
 rw [yo v (h + 1)
  (fun u j=>(qx u (2 * n + 2 * j),qx u (2 * n + 2 * j + 1)))
  encRow (2 * (n * n))]
 apply List.flatMap_congr; intro u _
 apply List.flatMap_congr; intro j _
 dsimp only [encRow,qD,qx]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
 have hb:v * q + 2 * (2 * (n * n) + u * (h + 1) + j)=
  v * q + 4 * (n * n) + 2 * (u * (h + 1) + j):=by ring
 rw [hb]
lemma qaa (n:ℕ) (hn:0 < n) (A:Fin n→Fin n→Bool) (h:ℕ):
 let header:=fun k:Nat=>List.replicate k true++[false]
 let field:=fun (k z:Nat)=>(List.range (k.log2 + 1)).map (fun i=>z.testBit i)
 let v:=2 * n
 let e:=2 * (n + h)
 let q:=2 * e + 1
 let cells:=(List.finRange n).flatMap (fun i=>(List.finRange n).map (fun j=>(i,j)))
 let links:=
  let qx:=fun (block j:Nat)=>block * q +
   (if j=0 then 0 else if j=e + 1 then 2 * e else 2 * j - 1)
  cells.flatMap (fun z=>
   let l:=qx z.1.val (2 * z.2.val)
   let l':=qx z.1.val (2 * z.2.val + 1)
   let r:=qx (n + z.2.val) (2 * z.1.val)
   let r':=qx (n + z.2.val) (2 * z.1.val + 1)
   if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])++
  (List.range v).flatMap (fun u=>(List.range (h + 1)).map (fun j=>
    (qx u (2 * n + 2 * j),qx u (2 * n + 2 * j + 1))))
 let size:=v * q + 2 * links.length
 let rows:=
  (List.range v).flatMap (fun u=>(List.range e).map (fun j=>
    let b:=u * q + 2 * j
    [b,b + 1,b + 2]))++links.zipIdx.flatMap (fun z=>
      let b:=v * q + 2 * z.2
      [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])
 writeFn (header n++header h++cells.map (fun z=>A z.1 z.2))=
  header size++rows.flatMap (fun R=>R.flatMap (field size)):=by
 intro header field v e q cells links size rows
 set s:=header n++header h++cells.map (fun z=>A z.1 z.2)
 obtain ⟨hnL,hhL,hbits,hvL,heL,hqL,hmL,hvqL,hkL0,hbSpareL⟩:=
  w8 n h (cells.map (fun z=>A z.1 z.2))
 have hcells_len:cells.length=n * n:=by
  dsimp only [cells]
  rw [zV (List.finRange n) _ n (fun _ _=>by simp),List.length_finRange]
 have hlinks_len:links.length=2 * (n * n) + 2 * n * (h + 1):=by
  dsimp only [links]
  rw [List.length_append,
   zV cells _ 2 (fun z _=>by split_ifs <;> rfl),hcells_len,
   zV (List.range v) _ (h + 1) (fun _ _=>by simp),List.length_range]
  dsimp only [v]; ring
 have hkL:(wK s).length=size:=by rw [hkL0,← hlinks_len]
 have hkpos:0 < (wK s).length:=by
  rw [hkL]; dsimp only [size,v,q,e]; nlinarith
 have hhead:q47 (wK s)++[false]=header size:=by
  simp [q47,header,hkL]
 have hpath:=wX (wK s) (wV s) (wQ s) (wE s) hkpos
 rw [hvL,heL,hqL,hkL] at hpath
 have hcell:=wA (wK s) (hd s) (wQ s) (wE s) (wVQ s) hkpos hnL A
 rw [hkL,hqL,heL,hvqL] at hcell
 have hspare:=wm (wK s) (hd s) (wV s) (wQ s) (wE s) (hd (dropN s)) (wBSpare s) hkpos
 rw [hkL,hqL,heL,hnL,hvL,hhL,hbSpareL] at hspare
 have hpathRow:
  (((List.range v).flatMap (fun u=>(List.range e).map (fun j=>
    let b:=u * q + 2 * j; [b,b + 1,b + 2]))).flatMap (fun R=>R.flatMap (field size)))=
  (List.range v).flatMap (fun u=>(List.range e).flatMap (fun j=>
    let b:=u * q + 2 * j; qm size b++qm size (b + 1)++qm size (b + 2))):=by
  rw [vD]
  apply List.flatMap_congr; intro u _
  rw [List.flatMap_map]
  apply List.flatMap_congr; intro j _
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,qm,field]
 have hL1len:(cells.flatMap (fun z=>
  let qx:=fun (block j:Nat)=>block * q +
   (if j=0 then 0 else if j=e + 1 then 2 * e else 2 * j - 1)
  let l:=qx z.1.val (2 * z.2.val)
  let l':=qx z.1.val (2 * z.2.val + 1)
  let r:=qx (n + z.2.val) (2 * z.1.val)
  let r':=qx (n + z.2.val) (2 * z.1.val + 1)
  if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')])).length=2 * (n * n):=by
  rw [zV cells _ 2 (fun z _=>by split_ifs <;> rfl),hcells_len]; ring
 have hswitchRow:
  ((links.zipIdx.flatMap (fun z=>let b:=v * q + 2 * z.2; [[b,b + 1,z.1.1],[b,b + 1,z.1.2]])).flatMap
    (fun R=>R.flatMap (field size)))=
  (List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>
    qH size q e n (v * q + 4 * (i * n + j)) i j
     (if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false)))++
  (List.range v).flatMap (fun u=>(List.range (h + 1)).flatMap (fun j=>
    qD size q e n (v * q + 4 * (n * n) + 2 * (u * (h + 1) + j)) u j)):=by
  dsimp only [links]
  rw [List.zipIdx_append,List.flatMap_append,List.flatMap_append,hL1len,Nat.zero_add]
  exact congrArg₂ (·++·) (uX n h size hn A) (uF n h size)
 have hrows:rows.flatMap (fun R=>R.flatMap (field size))=
  (List.range v).flatMap (fun u=>(List.range e).flatMap (fun j=>
    let b:=u * q + 2 * j; qm size b++qm size (b + 1)++qm size (b + 2)))++
  ((List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>
    qH size q e n (v * q + 4 * (i * n + j)) i j
     (if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false)))++
  (List.range v).flatMap (fun u=>(List.range (h + 1)).flatMap (fun j=>
    qD size q e n (v * q + 4 * (n * n) + 2 * (u * (h + 1) + j)) u j))):=by
  dsimp only [rows]
  rw [List.flatMap_append,hpathRow,hswitchRow]
 have hwrite:writeFn s=
  header size++
  (List.range v).flatMap (fun u=>(List.range e).flatMap (fun j=>
    let b:=u * q + 2 * j; qm size b++qm size (b + 1)++qm size (b + 2)))++
  (List.range n).flatMap (fun i=>(List.range n).flatMap (fun j=>
    qH size q e n (v * q + 4 * (i * n + j)) i j
     (if hi:i < n then if hj:j < n then A ⟨i,hi⟩ ⟨j,hj⟩ else false else false)))++
  (List.range v).flatMap (fun u=>(List.range (h + 1)).flatMap (fun j=>
    qD size q e n (v * q + 4 * (n * n) + 2 * (u * (h + 1) + j)) u j)):=by
  dsimp only [writeFn]
  rw [hbits,hhead,hpath,hcell,hspare]
 rw [hwrite,hrows,List.append_assoc,List.append_assoc]
end kg
namespace kI
open scoped BigOperators
def qaT (nU hU:List Bool):List Bool:=
 let s:=nU++hU
 true::(s++s++s++s)
def zI (wU nU hU:List Bool):List Bool:=
 let qW:=zz wU (qaT nU hU)
 zy wU qW qW
lemma kN {uw unU uh:List Bool→List Bool} (hw:qe uw) (hn:qe unU) (hh:qe uh):
 qe (fun s=>zI (uw s) (unU s) (uh s)):=by
 have hs:=qi hn hh
 have hqU:=qi (qh [true]) (qi (qi (qi hs hs) hs) hs)
 have hqW:=q50 hw hqU
 exact q32 hw hqW hqW
lemma kw (wU nU hU:List Bool) (hlt:qg.qk nU.length hU.length < 2 ^ wU.length):
 (zI wU nU hU).length=wU.length∧val (zI wU nU hU)=qg.qk nU.length hU.length:=by
 dsimp only [zI,qaT]
 have hqlen:(true::(nU++hU++(nU++hU)++(nU++hU)++(nU++hU))).length=
  qg.qL nU.length hU.length:=by
  simp only [List.length_cons,List.length_append,qg.qL,qg.zl]; omega
 have hqlt:qg.qL nU.length hU.length < 2 ^ wU.length:=by
  have:qg.qL nU.length hU.length≤qg.qk nU.length hU.length:=by
   dsimp only [qg.qk]; nlinarith
  omega
 refine ⟨q93 _ _ _,?_⟩
 rw [kt,kP,hqlen,Nat.mod_eq_of_lt hqlt,← sq]
 exact Nat.mod_eq_of_lt hlt
def aStep (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let nU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let hU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let kU:=(unpairB r3).1
 let acc:=(unpairB r3).2
 let acc':=sel (ku kU hU) (zy wU acc (zI wU nU kU)) acc
 qc wU (qc nU (qc hU (qc (true::kU) acc')))
lemma qaM:qe aStep:=by
 have hw:=qf; have hr1:=qb
 have hn:=qa hr1 qf; have hr2:=qa hr1 qb
 have hh:=qa hr2 qf; have hr3:=qa hr2 qb
 have hk:=qa hr3 qf; have hacc:=qa hr3 qb
 have hacc':=zh (qaD hk hh) (q32 hw hacc (kN hw hn hk)) hacc
 exact qd hw (qd hn (qd hh (qd (qi (qh [true]) hk) hacc')))
def y4 (wU nU hU:List Bool):List Bool:=
 let fin:=aStep^[(true::nU).length] (qc wU (qc nU (qc hU (qc [] (zz wU [true])))))
 (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma qau {uw unU uh:List Bool→List Bool} (hw:qe uw) (hn:qe unU) (hh:qe uh):
 qe (fun s=>y4 (uw s) (unU s) (uh s)):=by
 have hinit:=qd hw (qd hn (qd hh (qd (qh [])
  (q50 hw (qh [true])))))
 have hfin:=q18 12 qaM
  (fun y=>by dsimp only [aStep]; rw [qj])
  (fun y=>by
    dsimp only [aStep]
    set wU:=(unpairB y).1; set r1:=(unpairB y).2
    set nU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set hU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set kU:=(unpairB r3).1; set acc:=(unpairB r3).2
    have h1:2 * wU.length + r1.length≤y.length:=q0 y
    have h2:2 * nU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * hU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * kU.length + acc.length≤r3.length:=q0 r3
    rw [q7,q7,q7,q7,List.length_cons]
    have ha:(sel (ku kU hU) (zy wU acc (zI wU nU kU)) acc).length≤wU.length + acc.length:=by
     unfold sel; split_ifs
     · rw [q93]; omega
     · omega
    omega)
  (qi (qh [true]) hn) hinit
 exact q39 (qa (qa (qa (qa hfin qb) qb)
  qb) qb) (fun _=>rfl)
lemma qad (wU nU hU:List Bool) (_hw1:1 < 2 ^ wU.length)
 (hxlt:∀ k≤nU.length,qg.qk nU.length k < 2 ^ wU.length):
 (y4 wU nU hU).length=wU.length∧
 val (y4 wU nU hU)=qg.qR nU.length hU.length % 2 ^ wU.length:=by
 dsimp only [y4]
 have hiter:∀ t≤nU.length + 1,∃ (kU acc:List Bool),
  aStep^[t] (qc wU (qc nU (qc hU (qc [] (zz wU [true])))))=
   qc wU (qc nU (qc hU (qc kU acc)))∧
  kU.length=t∧acc.length=wU.length∧
  val acc=(∏ k∈(Finset.range t).erase hU.length,qg.qk nU.length k) % 2 ^ wU.length:=by
  intro t ht
  induction t with
  | zero=>
    refine ⟨[],zz wU [true],rfl,rfl,q54 _ _,?_⟩
    simp [kP]
  | succ t ih=>
    obtain ⟨kU,acc,hstep,hkl,hal,hav⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [aStep]
    simp only [qj]
    rw [qaE,hkl]
    by_cases hth:t=hU.length
    · simp only [hth,sel,List.cons_ne_nil,↓reduceIte]
      refine ⟨true::kU,acc,rfl,by simp [hkl,hth],hal,?_⟩
      have heq:(Finset.range (hU.length + 1)).erase hU.length=
       (Finset.range hU.length).erase hU.length:=by
       ext k; simp only [Finset.mem_erase,Finset.mem_range]; omega
      rw [hav,hth,heq]
    · simp only [hth,sel,↓reduceIte]
      refine ⟨true::kU,zy wU acc (zI wU nU kU),rfl,by simp [hkl],q93 _ _ _,?_⟩
      have hxw:=(kw wU nU kU (by rw [hkl]; exact hxlt t (by omega))).2
      rw [kt,hav,hxw,hkl,Nat.mod_mul_mod]
      have heq:(Finset.range (t + 1)).erase hU.length=
       insert t ((Finset.range t).erase hU.length):=by
       ext k; simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_insert]; omega
      have hnot:t∉(Finset.range t).erase hU.length:=by simp
      rw [heq,Finset.prod_insert hnot,mul_comm]
 obtain ⟨kU,acc,hfin,_,hal,hav⟩:=hiter (nU.length + 1) le_rfl
 rw [List.length_cons,hfin]; simp only [qj]
 exact ⟨hal,hav⟩
def bInnerStep (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let nU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let hU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let xI:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let jU:=(unpairB r4).1
 let acc:=(unpairB r4).2
 let diff:=vk wU (zI wU nU jU) xI
 let acc':=sel (ku jU hU) (zy wU acc diff) acc
 qc wU (qc nU (qc hU (qc xI (qc (true::jU) acc'))))
lemma jD:qe bInnerStep:=by
 have hw:=qf; have hr1:=qb
 have hn:=qa hr1 qf; have hr2:=qa hr1 qb
 have hh:=qa hr2 qf; have hr3:=qa hr2 qb
 have hxI:=qa hr3 qf; have hr4:=qa hr3 qb
 have hj:=qa hr4 qf; have hacc:=qa hr4 qb
 have hdiff:=qaC hw (kN hw hn hj) hxI
 have hacc':=zh (qaD hj hh) (q32 hw hacc hdiff) hacc
 exact qd hw (qd hn (qd hh (qd hxI
  (qd (qi (qh [true]) hj) hacc'))))
def yp (wU nU hU iU:List Bool):List Bool:=
 let xI:=zI wU nU iU
 let init:=qc wU (qc nU (qc hU (qc xI (qc (true::iU) (zz wU [true])))))
 let fin:=bInnerStep^[(vN iU nU).length] init
 (unpairB (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2).2
lemma qaf {uw unU uh ui:List Bool→List Bool}
 (hw:qe uw) (hn:qe unU) (hh:qe uh) (hi:qe ui):
 qe (fun s=>yp (uw s) (unU s) (uh s) (ui s)):=by
 have hxI:=kN hw hn hi
 have hinit:=qd hw (qd hn (qd hh (qd hxI
  (qd (qi (qh [true]) hi) (q50 hw (qh [true]))))))
 have hfin:=q18 14 jD
  (fun y=>by dsimp only [bInnerStep]; rw [qj])
  (fun y=>by
    dsimp only [bInnerStep]
    set wU:=(unpairB y).1; set r1:=(unpairB y).2
    set nU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set hU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set xI:=(unpairB r3).1; set r4:=(unpairB r3).2
    set jU:=(unpairB r4).1; set acc:=(unpairB r4).2
    have h1:2 * wU.length + r1.length≤y.length:=q0 y
    have h2:2 * nU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * hU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * xI.length + r4.length≤r3.length:=q0 r3
    have h5:2 * jU.length + acc.length≤r4.length:=q0 r4
    rw [q7,q7,q7,q7,q7,List.length_cons]
    have ha:(sel (ku jU hU) (zy wU acc (vk wU (zI wU nU jU) xI)) acc).length≤
     wU.length + acc.length:=by
     unfold sel; split_ifs
     · rw [q93]; omega
     · omega
    omega)
  (yS hi hn) hinit
 exact q39 (qa (qa (qa (qa (qa hfin qb) qb)
  qb) qb) qb) (fun _=>rfl)
lemma wz (wU nU hU iU:List Bool) (hi:iU.length≤nU.length)
 (hxlt:∀ k≤nU.length,qg.qk nU.length k < 2 ^ wU.length):
 (yp wU nU hU iU).length=wU.length∧
 val (yp wU nU hU iU)=
  (∏ j∈((Finset.range (nU.length + 1)).erase hU.length).filter (fun j=>iU.length < j),
    (qg.qk nU.length j - qg.qk nU.length iU.length)) % 2 ^ wU.length:=by
 dsimp only [yp]
 have hxI:=(kw wU nU iU (hxlt iU.length hi)).2
 have hiter:∀ t≤nU.length - iU.length,∃ (jU acc:List Bool),
  bInnerStep^[t] (qc wU (qc nU (qc hU (qc (zI wU nU iU)
   (qc (true::iU) (zz wU [true]))))))=
   qc wU (qc nU (qc hU (qc (zI wU nU iU) (qc jU acc))))∧
  jU.length=iU.length + 1 + t∧acc.length=wU.length∧
  val acc=(∏ j∈((Finset.range (iU.length + 1 + t)).erase hU.length).filter (fun j=>iU.length < j),
   (qg.qk nU.length j - qg.qk nU.length iU.length)) % 2 ^ wU.length:=by
  intro t ht
  induction t with
  | zero=>
    refine ⟨true::iU,zz wU [true],rfl,by simp,q54 _ _,?_⟩
    have hemp:((Finset.range (iU.length + 1 + 0)).erase hU.length).filter (fun j=>iU.length < j)=∅:=by
     ext j; simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_range,Finset.notMem_empty,iff_false]
     omega
    rw [hemp,Finset.prod_empty,kP]; simp
  | succ t ih=>
    obtain ⟨jU,acc,hstep,hjl,hal,hav⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [bInnerStep]
    simp only [qj]
    rw [qaE,hjl]
    by_cases hjeq:iU.length + 1 + t=hU.length
    · simp only [hjeq,sel,List.cons_ne_nil,↓reduceIte]
      refine ⟨true::jU,acc,rfl,by simp [hjl]; omega,hal,?_⟩
      rw [hav]
      have heq:((Finset.range (iU.length + 1 + (t + 1))).erase hU.length).filter (fun j=>iU.length < j)=
       ((Finset.range (iU.length + 1 + t)).erase hU.length).filter (fun j=>iU.length < j):=by
       ext j; simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_range]; omega
      rw [heq]
    · simp only [hjeq,sel,↓reduceIte]
      refine ⟨true::jU,zy wU acc (vk wU (zI wU nU jU) (zI wU nU iU)),rfl,
       by simp [hjl]; omega,q93 _ _ _,?_⟩
      have hxjlt:qg.qk nU.length jU.length < 2 ^ wU.length:=by
       rw [hjl]; exact hxlt _ (by omega)
      have hxj:=(kw wU nU jU hxjlt).2
      have hge:val (zI wU nU iU)≤val (zI wU nU jU):=by
       rw [hxI,hxj]; exact le_of_lt (qg.zg nU.length (by omega))
      have hsub:=q83 wU (zI wU nU jU) (zI wU nU iU) (by rw [hxj]; exact hxjlt) hge
      rw [kt,hav,hsub,hxj,hxI,hjl,Nat.mod_mul_mod]
      have heq:((Finset.range (iU.length + 1 + (t + 1))).erase hU.length).filter (fun j=>iU.length < j)=
       insert (iU.length + 1 + t)
        (((Finset.range (iU.length + 1 + t)).erase hU.length).filter (fun j=>iU.length < j)):=by
       ext j; simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_range,Finset.mem_insert]; omega
      have hnot:iU.length + 1 + t∉
       ((Finset.range (iU.length + 1 + t)).erase hU.length).filter (fun j=>iU.length < j):=by
       simp
      rw [heq,Finset.prod_insert hnot,mul_comm]
 have hdl:(vN iU nU).length=nU.length - iU.length:=by rw [q40,List.length_drop]
 obtain ⟨jU,acc,hfin,_,hal,hav⟩:=hiter (nU.length - iU.length) le_rfl
 rw [hdl,hfin]; simp only [qj]
 rw [show iU.length + 1 + (nU.length - iU.length)=nU.length + 1 by omega] at hav
 exact ⟨hal,hav⟩
def bOuterStep (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let nU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let hU:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let iU:=(unpairB r3).1
 let acc:=(unpairB r3).2
 let acc':=sel (ku iU hU) (zy wU acc (yp wU nU hU iU)) acc
 qc wU (qc nU (qc hU (qc (true::iU) acc')))
lemma jE:qe bOuterStep:=by
 have hw:=qf; have hr1:=qb
 have hn:=qa hr1 qf; have hr2:=qa hr1 qb
 have hh:=qa hr2 qf; have hr3:=qa hr2 qb
 have hi:=qa hr3 qf; have hacc:=qa hr3 qb
 have hacc':=zh (qaD hi hh) (q32 hw hacc (qaf hw hn hh hi)) hacc
 exact qd hw (qd hn (qd hh (qd (qi (qh [true]) hi) hacc')))
def yb (wU nU hU:List Bool):List Bool:=
 let fin:=bOuterStep^[(true::nU).length] (qc wU (qc nU (qc hU (qc [] (zz wU [true])))))
 (unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
lemma jZ {uw unU uh:List Bool→List Bool} (hw:qe uw) (hn:qe unU) (hh:qe uh):
 qe (fun s=>yb (uw s) (unU s) (uh s)):=by
 have hinit:=qd hw (qd hn (qd hh (qd (qh [])
  (q50 hw (qh [true])))))
 have hfin:=q18 12 jE
  (fun y=>by dsimp only [bOuterStep]; rw [qj])
  (fun y=>by
    dsimp only [bOuterStep]
    set wU:=(unpairB y).1; set r1:=(unpairB y).2
    set nU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set hU:=(unpairB r2).1; set r3:=(unpairB r2).2
    set iU:=(unpairB r3).1; set acc:=(unpairB r3).2
    have h1:2 * wU.length + r1.length≤y.length:=q0 y
    have h2:2 * nU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * hU.length + r3.length≤r2.length:=q0 r2
    have h4:2 * iU.length + acc.length≤r3.length:=q0 r3
    rw [q7,q7,q7,q7,List.length_cons]
    have ha:(sel (ku iU hU) (zy wU acc (yp wU nU hU iU)) acc).length≤
     wU.length + acc.length:=by
     unfold sel; split_ifs
     · rw [q93]; omega
     · omega
    omega)
  (qi (qh [true]) hn) hinit
 exact q39 (qa (qa (qa (qa hfin qb) qb)
  qb) qb) (fun _=>rfl)
lemma jd (wU nU hU:List Bool)
 (hxlt:∀ k≤nU.length,qg.qk nU.length k < 2 ^ wU.length):
 (yb wU nU hU).length=wU.length∧
 val (yb wU nU hU)=qg.qI nU.length hU.length % 2 ^ wU.length:=by
 dsimp only [yb]
 have hiter:∀ t≤nU.length + 1,∃ (iU acc:List Bool),
  bOuterStep^[t] (qc wU (qc nU (qc hU (qc [] (zz wU [true])))))=
   qc wU (qc nU (qc hU (qc iU acc)))∧
  iU.length=t∧acc.length=wU.length∧
  val acc=(∏ i∈(Finset.range t).erase hU.length,
   ∏ j∈((Finset.range (nU.length + 1)).erase hU.length).filter (fun j=>i < j),
     (qg.qk nU.length j - qg.qk nU.length i)) % 2 ^ wU.length:=by
  intro t ht
  induction t with
  | zero=>
    refine ⟨[],zz wU [true],rfl,rfl,q54 _ _,?_⟩
    simp [kP]
  | succ t ih=>
    obtain ⟨iU,acc,hstep,hil,hal,hav⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [bOuterStep]
    simp only [qj]
    rw [qaE,hil]
    by_cases hth:t=hU.length
    · simp only [hth,sel,List.cons_ne_nil,↓reduceIte]
      refine ⟨true::iU,acc,rfl,by simp [hil,hth],hal,?_⟩
      have heq:(Finset.range (hU.length + 1)).erase hU.length=
       (Finset.range hU.length).erase hU.length:=by
       ext k; simp only [Finset.mem_erase,Finset.mem_range]; omega
      rw [hav,hth,heq]
    · simp only [hth,sel,↓reduceIte]
      refine ⟨true::iU,zy wU acc (yp wU nU hU iU),rfl,by simp [hil],q93 _ _ _,?_⟩
      have hbi:=(wz wU nU hU iU (by omega) hxlt).2
      rw [kt,hav,hbi,hil,Nat.mod_mul_mod,Nat.mul_mod_mod]
      have heq:(Finset.range (t + 1)).erase hU.length=
       insert t ((Finset.range t).erase hU.length):=by
       ext k; simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_insert]; omega
      have hnot:t∉(Finset.range t).erase hU.length:=by simp
      rw [heq,Finset.prod_insert hnot,mul_comm]
 obtain ⟨iU,acc,hfin,_,hal,hav⟩:=hiter (nU.length + 1) le_rfl
 rw [List.length_cons,hfin]; simp only [qj]
 exact ⟨hal,hav⟩
lemma yF (n:ℕ):qg.qI n (n + 1)=qg.vz n:=by
 dsimp only [qg.qI,qg.vz]
 have her:(Finset.range (n + 1)).erase (n + 1)=Finset.range (n + 1):=
  Finset.erase_eq_of_notMem (by simp)
 rw [her]
def sumEOStep (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let nU:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let rest:=(unpairB r2).1
 let r3:=(unpairB r2).2
 let hU:=(unpairB r3).1
 let r4:=(unpairB r3).2
 let sE:=(unpairB r4).1
 let sO:=(unpairB r4).2
 let zW:=yN wU rest hU
 let term:=zy wU (zy wU zW (y4 wU nU hU)) (yb wU nU hU)
 let sE':=sel (q112 hU) (zM wU sE term) sE
 let sO':=sel (q112 hU) sO (zM wU sO term)
 qc wU (qc nU (qc rest (qc (true::hU) (qc sE' sO'))))
lemma j6:qe sumEOStep:=by
 have hw:=qf; have hr1:=qb
 have hn:=qa hr1 qf; have hr2:=qa hr1 qb
 have hrest:=qa hr2 qf; have hr3:=qa hr2 qb
 have hh:=qa hr3 qf; have hr4:=qa hr3 qb
 have hsE:=qa hr4 qf; have hsO:=qa hr4 qb
 have hz:=qea hw hrest hh
 have hterm:=q32 hw (q32 hw hz (qau hw hn hh)) (jZ hw hn hh)
 have hpar:=qa hh qdI
 have hsE':=zh hpar (q82 hw hsE hterm) hsE
 have hsO':=zh hpar hsO (q82 hw hsO hterm)
 exact qd hw (qd hn (qd hrest (qd (qi (qh [true]) hh)
  (qd hsE' hsO'))))
def readFn (s:List Bool):List Bool:=
 let nU:=hd s
 let rest:=dropN s
 let n2:=true::true::nU
 let wU:=rest++qJ (List.replicate 6 true) (qJ n2 (qJ n2 n2))
 let init:=qc wU (qc nU (qc rest (qc [] (qc (zz wU []) (zz wU [])))))
 let fin:=sumEOStep^[(true::nU).length] init
 let eo:=(unpairB (unpairB (unpairB (unpairB fin).2).2).2).2
 let sE:=(unpairB eo).1
 let sO:=(unpairB eo).2
 let dW:=yb wU nU (true::nU)
 let p4W:=uD wU (zz wU (List.replicate 4 true)) nU
 let denom:=zy wU dW p4W
 q141 (wI wU (vk wU sE sO) denom)
lemma qav:qe readFn:=by
 have hn:=vb
 have hrest:=va
 have hn2:=qi (qh [true,true]) hn
 have hw:=qi hrest (q42 (qh (List.replicate 6 true)) (q42 hn2 (q42 hn2 hn2)))
 have hzero:=q50 hw (qh [])
 have hinit:=qd hw (qd hn (qd hrest
  (qd (qh []) (qd hzero hzero))))
 have hfin:=q18 16 j6
  (fun y=>by dsimp only [sumEOStep]; rw [qj])
  (fun y=>by
    dsimp only [sumEOStep]
    set wU:=(unpairB y).1; set r1:=(unpairB y).2
    set nU:=(unpairB r1).1; set r2:=(unpairB r1).2
    set rest:=(unpairB r2).1; set r3:=(unpairB r2).2
    set hU:=(unpairB r3).1; set r4:=(unpairB r3).2
    set sE:=(unpairB r4).1; set sO:=(unpairB r4).2
    have h1:2 * wU.length + r1.length≤y.length:=q0 y
    have h2:2 * nU.length + r2.length≤r1.length:=q0 r1
    have h3:2 * rest.length + r3.length≤r2.length:=q0 r2
    have h4:2 * hU.length + r4.length≤r3.length:=q0 r3
    have h5:2 * sE.length + sO.length≤r4.length:=q0 r4
    rw [q7,q7,q7,q7,q7,List.length_cons]
    set term:=zy wU (zy wU (yN wU rest hU) (y4 wU nU hU)) (yb wU nU hU)
    have hE:(sel (q112 hU) (zM wU sE term) sE).length≤wU.length + sE.length:=by
     unfold sel; split_ifs
     · rw [q36]; omega
     · omega
    have hO:(sel (q112 hU) sO (zM wU sO term)).length≤wU.length + sO.length:=by
     unfold sel; split_ifs
     · omega
     · rw [q36]; omega
    omega)
  (qi (qh [true]) hn) hinit
 have heo:=qa (qa (qa (qa hfin qb) qb)
  qb) qb
 have hsE:=qa heo qf
 have hsO:=qa heo qb
 have hdW:=jZ hw hn (qi (qh [true]) hn)
 have hp4W:=qd0 hw (q50 hw (qh (List.replicate 4 true))) hn
 have hdenom:=q32 hw hdW hp4W
 exact q39 (qa (qdO hw (qaC hw hsE hsO) hdenom) qbP) (fun _=>rfl)
lemma y5 (n:ℕ):8 * n + 1 < 2 ^ (n + 4):=by
 induction n with
 | zero=>decide
 | succ n ih=>
   rw [show n + 1 + 4=(n + 4) + 1 by omega,pow_succ]
   have:8≤2 ^ (n + 4):=by
    calc 8=2 ^ 3:=by decide
     _≤2 ^ (n + 4):=Nat.pow_le_pow_right (by omega) (by omega)
   omega
lemma kc (n h:ℕ) (hh:h≤n):qg.qk n h < 2 ^ (2 * n + 8):=by
 dsimp only [qg.qk,qg.qL,qg.zl]
 have h1:2 * (2 * (n + h)) + 1≤8 * n + 1:=by omega
 have h2:=y5 n
 calc (2 * (2 * (n + h)) + 1) ^ 2≤(8 * n + 1) ^ 2:=Nat.pow_le_pow_left h1 2
  _ < (2 ^ (n + 4)) ^ 2:=Nat.pow_lt_pow_left h2 (by omega)
  _=2 ^ (2 * n + 8):=by rw [← pow_mul,show (n + 4) * 2=2 * n + 8 by omega]
lemma vX {ι:Type*} (s:Finset ι) (f g:ι→ℕ) (h:∀ i∈s,f i≤g i):
 ∏ i∈s,f i≤∏ i∈s,g i:=by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | insert a s ha ih=>
   rw [Finset.prod_insert ha,Finset.prod_insert ha]
   exact Nat.mul_le_mul (h a (Finset.mem_insert_self a s))
    (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
lemma k7 (n h:ℕ):qg.qR n h≤2 ^ ((n + 1) * (2 * n + 8)):=by
 dsimp only [qg.qR]
 have h1:∏ k∈(Finset.range (n + 1)).erase h,qg.qk n k≤
  ∏ _k∈(Finset.range (n + 1)).erase h,2 ^ (2 * n + 8):=by
  refine vX _ _ _ fun k hk=>?_
  have hkn:k≤n:=by have:=Finset.mem_range.mp (Finset.mem_of_mem_erase hk); omega
  exact le_of_lt (kc n k hkn)
 rw [Finset.prod_const] at h1
 have h2:(2 ^ (2 * n + 8)) ^ ((Finset.range (n + 1)).erase h).card≤(2 ^ (2 * n + 8)) ^ (n + 1):=
  Nat.pow_le_pow_right (by positivity) ((Finset.card_erase_le).trans (by rw [Finset.card_range]))
 have h3:(2 ^ (2 * n + 8)) ^ (n + 1)=2 ^ ((n + 1) * (2 * n + 8)):=by rw [← pow_mul,mul_comm]
 exact h1.trans (h2.trans h3.le)
lemma yZ (n h:ℕ):qg.qI n h≤2 ^ ((n + 1) * (n + 1) * (2 * n + 8)):=by
 dsimp only [qg.qI]
 have hinner:∀ i∈(Finset.range (n + 1)).erase h,
  ∏ j∈((Finset.range (n + 1)).erase h).filter (fun j=>i < j),
    (qg.qk n j - qg.qk n i)≤2 ^ ((n + 1) * (2 * n + 8)):=by
  intro i _
  have h1:∏ j∈((Finset.range (n + 1)).erase h).filter (fun j=>i < j),
        (qg.qk n j - qg.qk n i)≤
   ∏ _j∈((Finset.range (n + 1)).erase h).filter (fun j=>i < j),2 ^ (2 * n + 8):=by
   refine vX _ _ _ fun j hj=>?_
   have hjn:j≤n:=by
    have:=Finset.mem_range.mp (Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1); omega
   exact (Nat.sub_le _ _).trans (le_of_lt (kc n j hjn))
  rw [Finset.prod_const] at h1
  have h2:(2 ^ (2 * n + 8)) ^ (((Finset.range (n + 1)).erase h).filter (fun j=>i < j)).card≤
   (2 ^ (2 * n + 8)) ^ (n + 1):=
   Nat.pow_le_pow_right (by positivity)
    (((Finset.card_filter_le _ _).trans Finset.card_erase_le).trans (by rw [Finset.card_range]))
  have h3:(2 ^ (2 * n + 8)) ^ (n + 1)=2 ^ ((n + 1) * (2 * n + 8)):=by rw [← pow_mul,mul_comm]
  exact h1.trans (h2.trans h3.le)
 have h1:∏ i∈(Finset.range (n + 1)).erase h,
       ∏ j∈((Finset.range (n + 1)).erase h).filter (fun j=>i < j),
         (qg.qk n j - qg.qk n i)≤
  ∏ _i∈(Finset.range (n + 1)).erase h,2 ^ ((n + 1) * (2 * n + 8)):=
  vX _ _ _ hinner
 rw [Finset.prod_const] at h1
 have h2:(2 ^ ((n + 1) * (2 * n + 8))) ^ ((Finset.range (n + 1)).erase h).card≤
  (2 ^ ((n + 1) * (2 * n + 8))) ^ (n + 1):=
  Nat.pow_le_pow_right (by positivity) (Finset.card_erase_le.trans (by rw [Finset.card_range]))
 have h3:(2 ^ ((n + 1) * (2 * n + 8))) ^ (n + 1)=2 ^ ((n + 1) * (n + 1) * (2 * n + 8)):=by
  rw [← pow_mul]; congr 1; ring
 exact h1.trans (h2.trans h3.le)
lemma jo (n:ℕ) (wU:List Bool) (Z:ℕ→ℕ)
 (hZlen:∀ h < n + 1,(Z h).bits.length≤wU.length)
 (h:ℕ) (hh:h < n + 1):
 val (yN wU ((List.range (n + 1)).flatMap (fun u=>q23 (Z u).bits)) (un h))=Z h:=by
 dsimp only [yN]
 rw [qN,q62 (List.range (n + 1)) (fun u=>(Z u).bits) h (by simp; omega)]
 have hdrop:(List.range (n + 1)).drop h=h::(List.range (n + 1)).drop (h + 1):=by
  rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
 rw [hdrop,List.flatMap_cons,qbI,q30 wU _ (hZlen h hh),w3]
lemma kD {α β:Type*} {L:List α} {f:α→List β} {a:α} (ha:a∈L):
 (f a).length≤(L.flatMap f).length:=by
 induction L with
 | nil=>simp at ha
 | cons x r ih=>
   rw [List.flatMap_cons,List.length_append]
   rcases List.mem_cons.mp ha with rfl | hr
   · exact Nat.le_add_right _ _
   · exact (ih hr).trans (Nat.le_add_left _ _)
lemma yQ (n:ℕ) (Z:ℕ→ℕ) (h:ℕ) (hh:h < n + 1):
 (Z h).bits.length≤((List.range (n + 1)).flatMap (fun u=>q23 (Z u).bits)).length:=by
 have hmem:h∈List.range (n + 1):=List.mem_range.mpr hh
 have hle:(q23 (Z h).bits).length≤((List.range (n + 1)).flatMap (fun u=>q23 (Z u).bits)).length:=
  kD (f:=fun u=>q23 (Z u).bits) hmem
 have hq23:(Z h).bits.length≤(q23 (Z h).bits).length:=by
  dsimp only [q23]
  have h1:∀ l:List Bool,(l.flatMap (fun b=>[true,b])).length=2 * l.length:=by
   intro l; induction l with | nil=>simp | cons _ r ih=>simp [ih]; omega
  rw [List.length_append,h1]; omega
 omega
lemma qap (n:ℕ) (hn:0 < n) (A:Fin n→Fin n→Bool):
 let header:=fun k:Nat=>List.replicate k true++[false]
 let frame:=fun xs:List Bool=>xs.flatMap (fun b=>[true,b])++[false]
 readFn (header n++(List.range (n + 1)).flatMap (fun h=>frame (qg.ZOf A h).bits))=
  (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent.bits:=by
 intro header frame
 dsimp only [readFn]
 have hhd:hd (header n++(List.range (n + 1)).flatMap (fun h=>frame (qg.ZOf A h).bits))=un n:=by
  simp [header,hd,un,List.append_assoc]
 have hdn:dropN (header n++(List.range (n + 1)).flatMap (fun h=>frame (qg.ZOf A h).bits))=
  (List.range (n + 1)).flatMap (fun h=>frame (qg.ZOf A h).bits):=by
  simp [header,dropN,List.append_assoc]
 rw [hhd,hdn]
 set rest:=(List.range (n + 1)).flatMap (fun h=>frame (qg.ZOf A h).bits)
 set n2:=true::true::un n
 set wU:=rest++qJ (List.replicate 6 true) (qJ n2 (qJ n2 n2))
 have hwlen:wU.length=rest.length + 6 * (n + 2) ^ 3:=by
  simp only [wU,n2,List.length_append,qJ,qN,List.length_replicate,List.length_cons]
  ring
 have hZlen:∀ h < n + 1,(qg.ZOf A h).bits.length≤rest.length:=
  fun h hh=>yQ n (qg.ZOf A) h hh
 have hZlt:∀ h < n + 1,qg.ZOf A h < 2 ^ rest.length:=by
  intro h hh
  calc qg.ZOf A h=val (qg.ZOf A h).bits:=(w3 _).symm
   _ < 2 ^ (qg.ZOf A h).bits.length:=kQ _
   _≤2 ^ rest.length:=Nat.pow_le_pow_right (by omega) (hZlen h hh)
 have hcube:6 * (n + 2) ^ 3=6 * n * n * n + 36 * n * n + 72 * n + 48:=by ring
 have hxlt:∀ k≤n,qg.qk n k < 2 ^ wU.length:=by
  intro k hk
  calc qg.qk n k < 2 ^ (2 * n + 8):=kc n k hk
   _≤2 ^ wU.length:=Nat.pow_le_pow_right (by omega) (by rw [hwlen,hcube]; omega)
 have hw1:1 < 2 ^ wU.length:=by
  calc 1 < 2 ^ 1:=by decide
   _≤2 ^ wU.length:=Nat.pow_le_pow_right (by omega) (by rw [hwlen,hcube]; omega)
 have hDlt:2 * (qg.vz n * 4 ^ n) < 2 ^ wU.length:=by
  have hDle:qg.vz n≤2 ^ ((n + 1) * (n + 1) * (2 * n + 8)):=by
   rw [← yF]; exact yZ n (n + 1)
  have h4eq:4 ^ n=2 ^ (2 * n):=by rw [pow_mul]; norm_num
  have hexp:(n + 1) * (n + 1) * (2 * n + 8) + 2 * n + 1 < 6 * (n + 2) ^ 3:=by
   rw [hcube]
   have:(n + 1) * (n + 1) * (2 * n + 8) + 2 * n + 1=2 * n * n * n + 12 * n * n + 20 * n + 9:=by ring
   rw [this]; nlinarith
  have h1:2 * (qg.vz n * 4 ^ n)≤2 * (2 ^ ((n + 1) * (n + 1) * (2 * n + 8)) * 2 ^ (2 * n)):=by
   rw [h4eq]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hDle)
  have h2:2 * (2 ^ ((n + 1) * (n + 1) * (2 * n + 8)) * 2 ^ (2 * n))=
   2 ^ ((n + 1) * (n + 1) * (2 * n + 8) + 2 * n + 1):=by
   rw [← pow_add,mul_comm 2,← pow_succ]
  exact lt_of_le_of_lt (h2 ▸ h1) (Nat.pow_lt_pow_right (by omega) (by rw [hwlen]; omega))
 have hSbound:∀ t≤n + 1,
  ((Finset.range t).sum (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h)) < 2 ^ wU.length:=by
  intro t ht
  have hterm:∀ h∈Finset.range t,
   qg.ZOf A h * qg.qR n h * qg.qI n h≤
    2 ^ (rest.length + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)):=by
   intro h hh
   have hhn:h < n + 1:=by have:=Finset.mem_range.mp hh; omega
   calc qg.ZOf A h * qg.qR n h * qg.qI n h
    ≤2 ^ rest.length * 2 ^ ((n + 1) * (2 * n + 8)) * 2 ^ ((n + 1) * (n + 1) * (2 * n + 8)):=
     Nat.mul_le_mul (Nat.mul_le_mul (le_of_lt (hZlt h hhn)) (k7 n h)) (yZ n h)
    _=2 ^ (rest.length + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)):=by
      rw [pow_add,pow_add]
  have htlt:t < 2 ^ (n + 1):=lt_of_le_of_lt ht (Nat.lt_pow_self (by omega))
  have hexp2:(n + 1) + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)≤6 * (n + 2) ^ 3:=by
   rw [hcube]
   have:(n + 1) + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)=
    2 * n * n * n + 14 * n * n + 29 * n + 17:=by ring
   rw [this]; nlinarith
  calc (Finset.range t).sum (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h)
   ≤(Finset.range t).sum (fun _=>
      2 ^ (rest.length + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8))):=
    Finset.sum_le_sum hterm
   _=t * 2 ^ (rest.length + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)):=by
     rw [Finset.sum_const,Finset.card_range,smul_eq_mul]
   _ < 2 ^ (n + 1) * 2 ^ (rest.length + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8)):=
       Nat.mul_lt_mul_of_pos_right htlt (by positivity)
   _=2 ^ (rest.length + ((n + 1) + (n + 1) * (2 * n + 8) + (n + 1) * (n + 1) * (2 * n + 8))):=by
     rw [← pow_add]; congr 1; ring
   _≤2 ^ wU.length:=Nat.pow_le_pow_right (by omega) (by rw [hwlen]; omega)
 have hiter:∀ t≤n + 1,∃ (hU sE sO:List Bool),
  sumEOStep^[t] (qc wU (qc (un n) (qc rest (qc [] (qc (zz wU []) (zz wU []))))))=
   qc wU (qc (un n) (qc rest (qc hU (qc sE sO))))∧
  hU.length=t∧sE.length=wU.length∧sO.length=wU.length∧
  val sE=((Finset.range t).filter (fun h=>h % 2=0)).sum
   (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h)∧
  val sO=((Finset.range t).filter (fun h=>h % 2=1)).sum
   (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h):=by
  intro t ht
  induction t with
  | zero=>
    refine ⟨[],zz wU [],zz wU [],rfl,rfl,q54 _ _,q54 _ _,?_,?_⟩ <;> simp [kP]
  | succ t ih=>
    obtain ⟨hU,sE,sO,hstep,hhl,hsEl,hsOl,hsEv,hsOv⟩:=ih (by omega)
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [sumEOStep]
    simp only [qj]
    have htermVal:val (zy wU (zy wU (yN wU rest hU) (y4 wU (un n) hU)) (yb wU (un n) hU))=
     qg.ZOf A t * qg.qR n t * qg.qI n t:=by
     have hgz:val (yN wU rest hU)=qg.ZOf A t:=by
      have h1:yN wU rest hU=yN wU rest (un t):=by
       dsimp only [yN]; rw [hhl,qN]
      rw [h1]
      exact jo n wU (qg.ZOf A)
       (fun h hh=>(hZlen h hh).trans (by rw [hwlen]; omega)) t (by omega)
     have ha:=(qad wU (un n) hU hw1 (by simpa [qN] using hxlt)).2
     have hb:=(jd wU (un n) hU (by simpa [qN] using hxlt)).2
     rw [qN,hhl] at ha hb
     have hprodlt:qg.ZOf A t * qg.qR n t * qg.qI n t < 2 ^ wU.length:=by
      have hle:qg.ZOf A t * qg.qR n t * qg.qI n t≤
       (Finset.range (t + 1)).sum (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h):=
       Finset.single_le_sum (f:=fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h)
        (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self t))
      exact lt_of_le_of_lt hle (hSbound (t + 1) ht)
     have hAlt:qg.qR n t < 2 ^ wU.length:=by
      have hexpA:(n + 1) * (2 * n + 8) < 6 * (n + 2) ^ 3:=by
       have h1:(n + 1) * (2 * n + 8)=2 * (n * n) + 10 * n + 8:=by ring
       have h2:6 * (n + 2) ^ 3=6 * (n * n * n) + 36 * (n * n) + 72 * n + 48:=by ring
       omega
      exact lt_of_le_of_lt (k7 n t) (Nat.pow_lt_pow_right (by omega) (by rw [hwlen]; omega))
     have hBlt:qg.qI n t < 2 ^ wU.length:=by
      have hexpB:(n + 1) * (n + 1) * (2 * n + 8) < 6 * (n + 2) ^ 3:=by
       have h1:(n + 1) * (n + 1) * (2 * n + 8)=2 * (n * n * n) + 12 * (n * n) + 18 * n + 8:=by ring
       have h2:6 * (n + 2) ^ 3=6 * (n * n * n) + 36 * (n * n) + 72 * n + 48:=by ring
       omega
      exact lt_of_le_of_lt (yZ n t) (Nat.pow_lt_pow_right (by omega) (by rw [hwlen]; omega))
     rw [Nat.mod_eq_of_lt hAlt] at ha
     rw [Nat.mod_eq_of_lt hBlt] at hb
     have hZA:qg.ZOf A t * qg.qR n t < 2 ^ wU.length:=by
      have hBpos:0 < qg.qI n t:=by
       dsimp only [qg.qI]
       exact Finset.prod_pos fun i _=>Finset.prod_pos fun j hj=>by
        rw [Finset.mem_filter] at hj; have:=qg.zg n hj.2; omega
      nlinarith
     rw [kt,kt,hgz,ha,hb,Nat.mod_eq_of_lt hZA,Nat.mod_eq_of_lt hprodlt]
    have hpar:q112 hU=if t % 2=1 then [true] else []:=by
     dsimp only [q112]; rw [hhl]
    rw [hpar]
    have hsumLtE:((Finset.range (t + 1)).filter (fun h=>h % 2=0)).sum
     (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h) < 2 ^ wU.length:=
     lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (hSbound (t + 1) ht)
    have hsumLtO:((Finset.range (t + 1)).filter (fun h=>h % 2=1)).sum
     (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h) < 2 ^ wU.length:=
     lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (hSbound (t + 1) ht)
    by_cases hoddT:t % 2=1
    · simp only [hoddT,sel,List.cons_ne_nil,↓reduceIte]
      refine ⟨true::hU,sE,zM wU sO _,rfl,by simp [hhl],hsEl,q36 _ _ _,?_,?_⟩
      · rw [hsEv]
        have heq:(Finset.range (t + 1)).filter (fun h=>h % 2=0)=
         (Finset.range t).filter (fun h=>h % 2=0):=by
         ext h; simp only [Finset.mem_filter,Finset.mem_range]; omega
        rw [heq]
      · rw [jV,hsOv,htermVal]
        have heq:(Finset.range (t + 1)).filter (fun h=>h % 2=1)=
         insert t ((Finset.range t).filter (fun h=>h % 2=1)):=by
         ext h; simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert]; omega
        have hnot:t∉(Finset.range t).filter (fun h=>h % 2=1):=by simp
        have hsumEq:((Finset.range t).filter (fun h=>h % 2=1)).sum
         (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h) +
         qg.ZOf A t * qg.qR n t * qg.qI n t=
         ((Finset.range (t + 1)).filter (fun h=>h % 2=1)).sum
           (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h):=by
         rw [heq,Finset.sum_insert hnot,add_comm]
        rw [hsumEq,Nat.mod_eq_of_lt hsumLtO]
    · simp only [hoddT,sel,↓reduceIte]
      refine ⟨true::hU,zM wU sE _,sO,rfl,by simp [hhl],q36 _ _ _,hsOl,?_,?_⟩
      · rw [jV,hsEv,htermVal]
        have heq:(Finset.range (t + 1)).filter (fun h=>h % 2=0)=
         insert t ((Finset.range t).filter (fun h=>h % 2=0)):=by
         ext h; simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert]; omega
        have hnot:t∉(Finset.range t).filter (fun h=>h % 2=0):=by simp
        have hsumEq:((Finset.range t).filter (fun h=>h % 2=0)).sum
         (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h) +
         qg.ZOf A t * qg.qR n t * qg.qI n t=
         ((Finset.range (t + 1)).filter (fun h=>h % 2=0)).sum
           (fun h=>qg.ZOf A h * qg.qR n h * qg.qI n h):=by
         rw [heq,Finset.sum_insert hnot,add_comm]
        rw [hsumEq,Nat.mod_eq_of_lt hsumLtE]
      · rw [hsOv]
        have heq:(Finset.range (t + 1)).filter (fun h=>h % 2=1)=
         (Finset.range t).filter (fun h=>h % 2=1):=by
         ext h; simp only [Finset.mem_filter,Finset.mem_range]; omega
        rw [heq]
 obtain ⟨hU,sE,sO,hfin,_,_,_,hsEv,hsOv⟩:=hiter (n + 1) le_rfl
 have hlenN:(true::un n).length=n + 1:=by simp [un]
 rw [hlenN,hfin]; simp only [qj]
 have hdW:val (yb wU (un n) (true::un n))=qg.vz n:=by
  have hb:=(jd wU (un n) (true::un n) (by simpa [qN] using hxlt)).2
  rw [qN,List.length_cons,qN,yF] at hb
  rw [hb,Nat.mod_eq_of_lt]
  have h4pos:1≤4 ^ n:=Nat.one_le_pow _ _ (by omega)
  nlinarith
 have hp4W:val (uD wU (zz wU (List.replicate 4 true)) (un n))=4 ^ n:=by
  have h4lt:4 < 2 ^ wU.length:=by
   calc 4=2 ^ 2:=by decide
    _ < 2 ^ wU.length:=Nat.pow_lt_pow_right (by omega) (by rw [hwlen,hcube]; omega)
  have h4nlt:4 ^ n < 2 ^ wU.length:=by
   have hDp:=qg.u0 n; nlinarith
  rw [(qdQ wU _ _).2,kP,List.length_replicate,Nat.mod_eq_of_lt h4lt,qN,
   Nat.mod_eq_of_lt h4nlt]
 have hdenom:val (zy wU (yb wU (un n) (true::un n))
  (uD wU (zz wU (List.replicate 4 true)) (un n)))=qg.vz n * 4 ^ n:=by
  rw [kt,hdW,hp4W,Nat.mod_eq_of_lt (by omega)]
 have hlag:=qg.uO hn A
 have hsElt:val sE < 2 ^ wU.length:=by
  rw [hsEv]
  exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (hSbound (n + 1) le_rfl)
 have hsub:val (vk wU sE sO)=
  qg.vz n * 4 ^ n * (Matrix.of (fun i j:Fin n=>(A i j).toNat)).permanent:=by
  rw [q83 wU sE sO hsElt (by rw [hsEv,hsOv,hlag]; omega),hsEv,hsOv,hlag]
  omega
 have hdiv:=(qdK wU (vk wU sE sO)
  (zy wU (yb wU (un n) (true::un n)) (uD wU (zz wU (List.replicate 4 true)) (un n)))
  (by rw [hsub]; omega)
  (by rw [hdenom]; exact Nat.mul_pos (qg.u0 n) (by positivity))
  (by rw [hdenom]; exact hDlt)).2
 rw [qbJ,hdiv,hsub,hdenom,
  Nat.mul_div_cancel_left _ (Nat.mul_pos (qg.u0 n) (by positivity))]
end kI
namespace yA
def halfModStep (y:List Bool):List Bool:=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let mW:=(unpairB r1).1
 let xW:=(unpairB r1).2
 let x':=sel (q17 xW) xW (zM wU xW mW)
 let x'':=qy wU x'.tail
 qc wU (qc mW x'')
lemma ji:qe halfModStep:=by
 have hw:=qf
 have hr1:=qb
 have hm:=qa hr1 qf
 have hx:=qa hr1 qb
 have hx':=zh (qa hx q35) hx (q82 hw hx hm)
 have hx'':=q13 hw (qa hx' vW)
 exact qd hw (qd hm hx'')
def residueFn (s:List Bool):List Bool:=
 let nU:=hd s
 let r1:=dropN s
 let dU:=hd r1
 let rBits:=dropN r1
 let wU:=true::true::true::(dU++dU++rBits)
 let dW:=zz wU dU
 let mW:=zy wU dW dW
 let x0:=qy wU rBits
 let fin:=halfModStep^[(nU++nU).length] (qc wU (qc mW x0))
 q141 (unpairB (unpairB fin).2).2
lemma j4:qe residueFn:=by
 have hn:=vb
 have hr1:=va
 have hdU:=qa hr1 vb
 have hrBits:=qa hr1 va
 have hw:=qi (qh [true,true,true]) (qi (qi hdU hdU) hrBits)
 have hdW:=q50 hw hdU
 have hmW:=q32 hw hdW hdW
 have hx0:=q13 hw hrBits
 have hfin:=q18 6 ji
  (fun y=>by dsimp only [halfModStep]; rw [qj])
  (fun y=>by
    dsimp only [halfModStep]
    have h1:=q0 y
    have h2:=q0 (unpairB y).2
    rw [q7,q7,q19]
    omega)
  (qi hn hn) (qd hw (qd hmW hx0))
 exact q39 (qa (qa (qa hfin qb) qb) qbP) (fun _=>rfl)
lemma uW (d:ℕ):2 * d ^ 2 < 2 ^ (2 * d + 3):=by
 induction d with
 | zero=>decide
 | succ d ih=>
   have h1:2 ^ (2 * (d + 1) + 3)=4 * 2 ^ (2 * d + 3):=by
    rw [show 2 * (d + 1) + 3=(2 * d + 3) + 2 by omega,pow_add]; ring
   rw [h1]
   rcases d with _ | d'
   · decide
   · nlinarith
lemma w7 (l:List Bool):val l.tail=val l / 2:=by
 cases l with
 | nil=>simp [val]
 | cons b r=>
   simp only [List.tail_cons,val]
   cases b <;> simp <;> omega
lemma jW (n d P:ℕ) (hd1:1 < d) (hodd:Odd d):
 let header:=fun k:Nat=>List.replicate k true++[false]
 residueFn (header n++header d++((4 ^ n * P) % (d ^ 2)).bits)=(P % (d ^ 2)).bits:=by
 intro header
 dsimp only [residueFn]
 have h1:hd (header n++header d++((4 ^ n * P) % (d ^ 2)).bits)=un n:=by
  simp [header,hd,un,List.append_assoc]
 have h2:dropN (header n++header d++((4 ^ n * P) % (d ^ 2)).bits)=
  header d++((4 ^ n * P) % (d ^ 2)).bits:=by
  simp [header,dropN,List.append_assoc]
 have h3:hd (header d++((4 ^ n * P) % (d ^ 2)).bits)=un d:=by
  simp [header,hd,un,List.append_assoc]
 have h4:dropN (header d++((4 ^ n * P) % (d ^ 2)).bits)=((4 ^ n * P) % (d ^ 2)).bits:=by
  simp [header,dropN,List.append_assoc]
 rw [h1,h2,h3,h4]
 set rBits:=((4 ^ n * P) % (d ^ 2)).bits
 set wU:=true::true::true::(un d++un d++rBits)
 have hwlen:wU.length=2 * d + rBits.length + 3:=by
  simp only [wU,List.length_cons,List.length_append,qN]; omega
 have hbound:2 * d ^ 2 < 2 ^ wU.length:=by
  calc 2 * d ^ 2 < 2 ^ (2 * d + 3):=uW d
   _≤2 ^ wU.length:=Nat.pow_le_pow_right (by omega) (by omega)
 have hdlt:d < 2 ^ wU.length:=by nlinarith
 have hd2lt:d ^ 2 < 2 ^ wU.length:=by nlinarith
 set dW:=zz wU (un d)
 set mW:=zy wU dW dW
 set x0:=qy wU rBits
 have hdW:val dW=d:=by
  dsimp only [dW]; rw [kP,qN,Nat.mod_eq_of_lt hdlt]
 have hmW:val mW=d ^ 2:=by
  dsimp only [mW]; rw [kt,hdW,← sq,Nat.mod_eq_of_lt hd2lt]
 have hx0_len:x0.length=wU.length:=q19 wU rBits
 have hx0_val:val x0=(4 ^ n * P) % (d ^ 2):=by
  dsimp only [x0]
  rw [q30 wU rBits (by omega),w3]
 have hodd2:Odd (d ^ 2):=hodd.pow
 have hmpos:0 < d ^ 2:=by nlinarith
 have hiter:∀ k:ℕ,∃ xW:List Bool,
  halfModStep^[k] (qc wU (qc mW x0))=qc wU (qc mW xW)∧
  xW.length=wU.length∧
  val xW=(qg.vs (d ^ 2))^[k] ((4 ^ n * P) % (d ^ 2))∧
  val xW < d ^ 2:=by
  intro k
  induction k with
  | zero=>exact ⟨x0,rfl,hx0_len,hx0_val,by rw [hx0_val]; exact Nat.mod_lt _ hmpos⟩
  | succ k ih=>
    obtain ⟨xW,hstep,hxl,hxv,hxlt⟩:=ih
    rw [Function.iterate_succ_apply',hstep]
    dsimp only [halfModStep]
    simp only [qj]
    refine ⟨qy wU (sel (q17 xW) xW (zM wU xW mW)).tail,rfl,q19 _ _,?_,?_⟩
    · rw [Function.iterate_succ_apply',← hxv]
      have htail_le:(sel (q17 xW) xW (zM wU xW mW)).tail.length≤wU.length:=by
       unfold sel; split_ifs
       · cases xW <;> simp at hxl ⊢ <;> omega
       · have ha:=q36 wU xW mW
         cases hadd:zM wU xW mW <;> simp [hadd] at ha ⊢ <;> omega
      rw [q30 wU _ htail_le,w7]
      cases hx:xW with
      | nil=>rw [hx] at hxl; simp only [List.length_nil] at hxl; omega
      | cons b r=>
        cases b with
        | false=>
          have heven:val (false::r) % 2=0:=by simp [val]
          simp only [q17,sel,↓reduceIte,qg.vs,heven]
        | true=>
          have hoddX:val (true::r) % 2≠0:=by simp [val]
          simp only [q17,sel,List.cons_ne_nil,↓reduceIte,qg.vs,hoddX]
          rw [jV,hmW,Nat.mod_eq_of_lt (by rw [← hx]; omega)]
    · have htail_le:(sel (q17 xW) xW (zM wU xW mW)).tail.length≤wU.length:=by
       unfold sel; split_ifs
       · cases xW <;> simp at hxl ⊢ <;> omega
       · have ha:=q36 wU xW mW
         cases hadd:zM wU xW mW <;> simp [hadd] at ha ⊢ <;> omega
      rw [q30 wU _ htail_le,w7]
      cases hx:xW with
      | nil=>rw [hx] at hxl; simp only [List.length_nil] at hxl; omega
      | cons b r=>
        cases b with
        | false=>
          simp only [q17,sel,↓reduceIte]
          rw [← hx]; omega
        | true=>
          simp only [q17,sel,List.cons_ne_nil,↓reduceIte]
          rw [jV,hmW,Nat.mod_eq_of_lt (by rw [← hx]; omega),← hx]
          omega
 have h2n:(un n++un n).length=2 * n:=by simp [un]; omega
 obtain ⟨xFin,hfin,_,hvalFin,_⟩:=hiter (2 * n)
 rw [h2n,hfin]
 simp only [qj]
 rw [qbJ,hvalFin,qg.jq hd1 hodd]
end yA
end
end PEqualNP.Outside.L_meta_32567
theorem PEqualNP.Outside.L_meta_32567 :
let header := fun n : Nat => List.replicate n true ++ [false]
let frame := fun xs : List Bool => xs.flatMap (fun b => [true,b]) ++ [false]
let field := fun (k z : Nat) => (List.range (k.log2+1)).map (fun i => z.testBit i)
let fast := fun f : List Bool → List Bool =>
  ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    ∀ i, Finite (M.tm.Γ i)
∃ write read residue : List Bool → List Bool, fast write ∧ fast read ∧ fast residue ∧
  ∀ (n : Nat), 0 < n → ∀ A : Fin n → Fin n → Bool,
    let v := 2*n
    let e := fun h : Nat => 2*(n+h)
    let q := fun h : Nat => 2*e h+1
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))
    let B : Matrix (Fin n) (Fin n) Nat := fun i j => (A i j).toNat
    let mat := cells.toFinset.powerset.filter (fun S =>
      (∀ z ∈ S, A z.1 z.2 = true) ∧ (S.image Prod.fst).card = S.card ∧
      (S.image Prod.snd).card = S.card)
    let m := fun r : Nat => (mat.filter (fun S => S.card = r)).card
    let I := fun j : Nat => Nat.card {P : Equiv.Perm (Fin j) // Function.Involutive P}
    let links := fun h : Nat =>
      let port := fun (block j : Nat) => block*q h +
        (if j = 0 then 0 else if j = e h+1 then 2*e h else 2*j-1)
      cells.flatMap (fun z =>
        let l := port z.1.val (2*z.2.val)
        let l' := port z.1.val (2*z.2.val+1)
        let r := port (n+z.2.val) (2*z.1.val)
        let r' := port (n+z.2.val) (2*z.1.val+1)
        if A z.1 z.2 then [(l,r),(l',r')] else [(l,l'),(r,r')]) ++
      (List.range v).flatMap (fun u => (List.range (h+1)).map (fun j =>
        (port u (2*n+2*j),port u (2*n+2*j+1))))
    let size := fun h : Nat => v*q h+2*(links h).length
    let rows := fun h : Nat =>
      (List.range v).flatMap (fun u => (List.range (e h)).map (fun j =>
        let b := u*q h+2*j
        [b,b+1,b+2])) ++ (links h).zipIdx.flatMap (fun z =>
          let b := v*q h+2*z.2
          [[b,b+1,z.1.1],[b,b+1,z.1.2]])
    let Z := fun h : Nat => let k := size h
      let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
      Nat.card {f : Fn // (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k ∧
        PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
        ∀ R ∈ rows h, f (fun i => decide (i.val ∈ R)) (fun _ => false) = true}
    (∀ h : Nat, write (header n ++ header h ++ cells.map (fun z => A z.1 z.2)) =
      header (size h) ++ (rows h).flatMap (fun R => R.flatMap (field (size h))) ∧
      ((rows h).map List.toFinset).Nodup ∧
      (∀ R ∈ rows h, R.length = 3 ∧ R.Nodup ∧ ∀ u ∈ R, u < size h) ∧
      (∀ u : Fin (size h), ((rows h).filter (fun R => decide (u.val ∈ R))).length = 2) ∧
      0 < Z h ∧ Z h = (Finset.range (n+1)).sum (fun r =>
        4^r*m r*(q h)^(2*n-2*r)*I (2*n-2*r))) ∧
    read (header n ++ (List.range (n+1)).flatMap (fun h => frame (Z h).bits)) = B.permanent.bits ∧
    ∀ d : Nat, 1 < d → Odd d →
      let h := (4*n+1)*(d^2-1)/4
      q h = (4*n+1)*d^2 ∧
      Z h % (d^2) = (4^n*B.permanent) % (d^2) ∧
      residue (header n ++ header d ++ (Z h % (d^2)).bits) = (B.permanent % (d^2)).bits := by
  intro header frame field fast
  refine ⟨PEqualNP.Outside.L_meta_32567.kg.writeFn,
   PEqualNP.Outside.L_meta_32567.kI.readFn,
   PEqualNP.Outside.L_meta_32567.yA.residueFn,
   PEqualNP.Outside.L_meta_32567.kr PEqualNP.Outside.L_meta_32567.kg.qal,
   PEqualNP.Outside.L_meta_32567.kr PEqualNP.Outside.L_meta_32567.kI.qav,
   PEqualNP.Outside.L_meta_32567.kr PEqualNP.Outside.L_meta_32567.yA.j4,
   ?_⟩
  intro n hn A v e q cells B mat m I links size rows Z
  have hsize:∀ h,size h=PEqualNP.Outside.L_meta_32567.qg.qQ n h:=by
   intro h
   dsimp only [size,v,PEqualNP.Outside.L_meta_32567.qg.qQ]
   rw [show links h=PEqualNP.Outside.L_meta_32567.qg.zC A h from rfl,
    PEqualNP.Outside.L_meta_32567.qg.zk A h]
   rfl
  have hZeq:∀ h,Z h=PEqualNP.Outside.L_meta_32567.qg.ZOf A h:=by
   intro h
   have hs:size h=PEqualNP.Outside.L_meta_32567.qg.qQ n h:=hsize h
   dsimp only [Z,PEqualNP.Outside.L_meta_32567.qg.ZOf]
   generalize size h=k at hs ⊢
   subst hs
   rfl
  refine ⟨?_,?_,?_⟩
  · intro h
    have hp:=PEqualNP.Outside.L_meta_32567.qg.w4 hn A h
    have hzf:=PEqualNP.Outside.L_meta_32567.qg.ko hn A h
    refine ⟨PEqualNP.Outside.L_meta_32567.kg.qaa n hn A h,
     hp.1,?_,?_,?_,?_⟩
    · intro R hR
      obtain ⟨hl,hnd,hlt⟩:=hp.2.1 R hR
      exact ⟨hl,hnd,fun u hu=>by rw [hsize h]; exact hlt u hu⟩
    · intro u
      exact hp.2.2 ⟨u.val,by rw [← hsize h]; exact u.isLt⟩
    · rw [hZeq h]; exact hzf.1
    · rw [hZeq h]; exact hzf.2
  · simp_rw [hZeq]
    exact PEqualNP.Outside.L_meta_32567.kI.qap n hn A
  · intro d hd hodd h
    have hop:=PEqualNP.Outside.L_meta_32567.qg.qao hn A hd hodd
    have hzq:Z h % (d ^ 2)=(4 ^ n * B.permanent) % (d ^ 2):=by
     rw [hZeq h]; exact hop.2
    refine ⟨hop.1,hzq,?_⟩
    rw [hzq]
    exact PEqualNP.Outside.L_meta_32567.yA.jW n d B.permanent hd hodd
