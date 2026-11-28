import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_17987
open Finset
abbrev O:=Fin 14
abbrev o:=Finset O
abbrev _d:=Bool
abbrev _F:=List
lemma V{p:Prop}[Decidable p](h:decide p=true:=by decide):p:=of_decide_eq_true h
abbrev _ep:=@Equiv.Perm
abbrev _of{α:Type u_1}{n:Nat}(f:Fin n->α):=List.ofFn f
abbrev _mg:=@mem_image
abbrev _mss:=@mem_singleton_self
abbrev _ms:=@mem_singleton
abbrev _mf:=@mem_filter
abbrev _mi:=@mem_insert
abbrev _cl:=@card_le_card
abbrev _cp:=@card_pos
abbrev _c1:=@card_eq_one
abbrev _ct2:=@card_eq_two
abbrev _c2:=@card_pair
lemma _fs{α:Type u_1}(p:α->Prop)[DecidablePred p](s:Finset α):s.filter p⊆s:=filter_subset p s
abbrev _eqc:=@eq_of_subset_of_card_le
abbrev _dl:=@disjoint_left
abbrev _mu:=@mem_union
abbrev _mn:=@mem_inter
abbrev _md:=@mem_sdiff
abbrev _me:=@mem_erase
abbrev _mv:=@mem_univ
abbrev _cs:=@card_singleton
abbrev _ce:=@card_empty
abbrev _nt:=Nat.lt_trichotomy
abbrev _nr:=Nat.lt_irrefl
abbrev _fe:=@Fin.ext
abbrev _fnt:=Bool.false_ne_true
abbrev _lge:=@List.getD_eq_getElem
abbrev _cfl:=@card_filter_le
lemma _cin{α:Type u_1}[DecidableEq α]{a:α}{s:Finset α}(h:a∉s):(insert a s).card=s.card+1:=card_insert_of_notMem h
lemma _cii{α:Type u_1}{β:Type u_2}[DecidableEq β]{s:Finset α}(f:α->β)(hf:Function.Injective f):(s.image f).card=s.card:=card_image_of_injective s hf
lemma _cij{α:Type u_1}{β:Type u_2}[DecidableEq β]{s:Finset α}{f:α->β}(hf:Set.InjOn f s):(s.image f).card=s.card:=card_image_of_injOn hf
lemma _cud{α:Type u_1}[DecidableEq α]{s t:Finset α}(h:Disjoint s t):(s∪t).card=s.card+t.card:=card_union_of_disjoint h
abbrev _nf:=Bool.not_eq_false
namespace _0
abbrev RT:=@Relation.ReflTransGen
abbrev RTh:=@Relation.ReflTransGen.head
abbrev RTch:=@Relation.ReflTransGen.cases_head
abbrev RTct:=@Relation.ReflTransGen.cases_tail
abbrev RThi:=@Relation.ReflTransGen.head_induction_on
abbrev SI:=@Nat.strong_induction_on
abbrev Fn (n:ℕ):=Finset (Fin n)
abbrev FF (n:ℕ):=Finset (Fn n)
abbrev Fd (n:ℕ):=Fin n->_d
abbrev Fv (n:ℕ):=Fin n->ℕ
abbrev Gr (n:ℕ):=Fin n->Fin n->Prop
abbrev Ed:=ℕ×_d
abbrev Sg:=Σ _:ℕ,ℕ
abbrev L0:=@List.getD_eq_getElem?_getD
abbrev L1:=@List.getElem?_append_left
abbrev L2:=@List.getElem?_eq_getElem
abbrev L3:=@List.length_take
abbrev LP:=@List.length_pos_iff
abbrev MR:=@mem_range
abbrev IL:=@inter_subset_left
abbrev IR:=@inter_subset_right
abbrev SS:=@singleton_subset_iff
abbrev NE:=@Finset.not_nonempty_empty
abbrev NM:=@notMem_empty
abbrev NN:=@nonempty_iff_ne_empty
abbrev N0:=@not_nonempty_iff_eq_empty
abbrev EE:=@eq_empty_of_forall_notMem
abbrev O1:=@one_lt_card
abbrev O2:=@two_lt_card
abbrev CU:=@card_union_add_card_inter
abbrev CS:=@card_sdiff_add_card_eq_card
abbrev CE:=@card_erase_of_mem
abbrev C0:=@card_eq_zero
abbrev CL:=@card_lt_card
abbrev FE:=@filter_eq_empty_iff
abbrev SL:=@single_le_sum
abbrev SU:=@sum_le_sum_of_subset
abbrev SC:=@sum_congr
abbrev CF:=@card_filter
abbrev UL:=@card_union_le
abbrev US:=@union_subset
abbrev SG:=@singleton_injective
abbrev MP:=@mem_product
abbrev BO:=@Bool.or_eq_true
abbrev BA:=@Bool.and_eq_true
abbrev Bnt:=@Bool.not_eq_true
abbrev DE:=@decide_eq_true_eq
abbrev SN:=@Finset.ssubset_iff_subset_ne
abbrev AB:=@absurd
abbrev CG:=@congrArg
abbrev AR:=@Nat.le_add_right
abbrev AC:=@Nat.add_sub_cancel_left
abbrev Zl:=@Nat.zero_le
end _0
def kF:_d->_d->_d->_d
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[simp] lemma gop_true (a b:_d):kF true a b=(a&&b):=rfl
@[simp] lemma gop_false (a b:_d):kF false a b=(a||b):=rfl
abbrev Dag:=_F (_d×ℕ×ℕ)
def cR (D:Dag) (j:ℕ):_d:=(D.getD j (false,0,0)).1
def cj (D:Dag) (j:ℕ):ℕ:=(D.getD j (false,0,0)).2.1
def ck (D:Dag) (j:ℕ):ℕ:=(D.getD j (false,0,0)).2.2
def gl (w:_F _d) (g:_d×ℕ×ℕ):_F _d:=w ++ [kF g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
def kD (D:Dag) (w:_F _d):_F _d:=D.foldl gl w
def val (D:Dag) {n:ℕ} (x:Fin n->_d) (w:ℕ):_d:=(kD D (_of x)).getD w false
def au (n:ℕ) (D:Dag):Prop:=∀ j,j<D.length->cj D j<n+j/\ck D j<n+j/\cj D j≠ck D j
def bV (D:Dag) (w:ℕ):Finset ℕ:=(range D.length).filter (fun j=>cj D j=w\/ck D j=w)
def aF (D:Dag) (w:ℕ):ℕ:=(bV D w).card
def o7 (n:ℕ) (D:Dag):Prop:=∀ w,w+1<n+D.length->1<=aF D w
def ai (n:ℕ) (D:Dag):Prop:=au n D/\o7 n D/\D≠[]
def bH (n:ℕ) (D:Dag):ℕ:=n+D.length - 1
def cl {n:ℕ} (v:Fin n):Fin n->_d:=fun i=>decide (i=v)
def ag (n:ℕ) (D:Dag) (w:ℕ):Finset (Fin n):=univ.filter (fun v=>val D (cl v) w=true)
def bn (D:Dag) (K:Finset ℕ):ℕ:=∑ w∈K,(aF D w - 1)
def cD (n:ℕ) (D:Dag):Finset ℕ:=range (n+D.length - 1)
def ap (n:ℕ) (D:Dag):ℕ:=bn D (cD n D)
def bd (n:ℕ) (D:Dag):ℕ:=bn D ((cD n D).filter (fun w=>(ag n D w).Nonempty))
def bL (n:ℕ) (D:Dag):ℕ:=bn D ((cD n D).filter (fun w=>¬ (ag n D w).Nonempty))
def m5 (n:ℕ) (D:Dag):Finset ℕ:=(range (n+D.length)).filter (fun w=>2<=aF D w)
def al (n:ℕ) (D:Dag):Finset (Fin n):=(m5 n D).biUnion (ag n D)
def aa (n:ℕ) (D:Dag):Finset (Fin n):=univ\al n D
def dq (n:ℕ) (D:Dag):Finset (Σ _:ℕ,ℕ):=(cD n D).sigma (fun w=>range (aF D w - 1))
def da (n:ℕ) (D:Dag):Finset (Σ _:ℕ,ℕ):=(dq n D).filter (fun u=>(ag n D u.1).Nonempty)
def eK (D:Dag):Finset (ℕ×_d):=range D.length×ˢ univ
def aw (D:Dag) (e:ℕ×_d):ℕ:=if e.2=true then ck D e.1 else cj D e.1
def aE (n:ℕ) (D:Dag) (K:Finset ℕ):Finset (ℕ×_d):=(eK D).filter (fun e=>aw D e∈K/\n+e.1∉K)
def aW (n:ℕ) (D:Dag) (K:Finset ℕ):Finset ℕ:=(range D.length).filter (fun j=>n+j∈K/\cj D j∈K/\ck D j∈K)
def gb (n:ℕ) (K:Finset ℕ):Finset ℕ:=K.filter (fun w=>w<n)
def ao (n:ℕ) (D:Dag) (T:Finset (Fin n)):Finset ℕ:=(range (n+D.length)).filter (fun w=>(ag n D w∩T).Nonempty)
def aR (n:ℕ) (D:Dag) (x y:Fin n):Finset ℕ:=(range (n+D.length)).filter (fun w=>x∈ag n D w/\y∉ag n D w)
def aM (n:ℕ) (D:Dag) (b:Fin n->ℕ):Prop:=∀ v∈al n D,2<=aF D (b v)/\ag n D (b v)={v}
def cz (n:ℕ) (D:Dag) (b:Fin n->ℕ):Finset (Σ _:ℕ,ℕ):=(al n D).image (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ))
def aj (n:ℕ) (D:Dag) (b:Fin n->ℕ):Finset (Σ _:ℕ,ℕ):=da n D\cz n D b
namespace _0
lemma k4 (D E:Dag) (w:_F _d):kD (D++E) w=kD E (kD D w):=List.foldl_append
lemma jr (D:Dag):∀ w:_F _d,(kD D w).length=w.length+D.length:=by induction D with | nil=>intro _;simp[kD] | cons g D q=>intro w;change (kD D (gl w g)).length=_;rw[q];simp[gl];omega
lemma j3 (D:Dag):∀ (w:_F _d) (i:ℕ),i<w.length->(kD D w).getD i false=w.getD i false:=by induction D with | nil=>intro _ _ _;rfl | cons g D q=>intro w i h;exact(q (gl w g) i (by simp[gl];omega)).trans (by simp[gl,L1 h])
lemma iS (D:Dag) (w:_F _d) (j i:ℕ) (c:i<w.length+j) (d:j<=D.length):(kD (D.take j) w).getD i false=(kD D w).getD i false:=by
 conv_rhs=>rw[<-List.take_append_drop j D,k4]
 exact(j3 (D.drop j) _ i (by rw[jr,L3];omega)).symm
end _0
section
open _0
lemma bY (D:Dag) {n:ℕ} (x:Fd n) (i:ℕ) (h:i<n):val D x i=x ⟨i,h⟩:=by unfold val;rw[j3 _ _ _ (by simpa using h)];simp[h]
lemma fs (D:Dag) {n:ℕ} (x:Fd n) (w:ℕ) (h:n+D.length<=w):val D x w=false:=by have l:(kD D (_of x)).length<=w:=by {rw[jr];simpa using h};simp[val,List.getElem?_eq_none l]
lemma oe (D:Dag) {n:ℕ} (x:Fd n) (k w:ℕ) (a:w<n+k) (b:k<=D.length):val (D.take k) x w=val D x w:=iS D _ k w (by simpa using a) b
lemma cS {n:ℕ} {D:Dag} (b:au n D) (x:Fd n) (j:ℕ) (a:j<D.length):val D x (n+j)=kF (cR D j) (val D x (cj D j)) (val D x (ck D j)):=by
 obtain⟨c,d,-⟩:=b j a;unfold val
 have L:(kD (D.take j) (_of x)).length=n+j:=by {rw[jr,List.length_ofFn,L3];omega}
 conv_lhs=>rw[show D=D.take j++D[j]::D.drop (j+1) by simp,k4,show kD (D[j]::D.drop (j+1)) _=kD (D.drop (j+1)) (gl _ D[j]) from rfl,j3 _ _ _ (by simp[gl,L]),<-L]
 simp only[gl,L0,List.getElem?_append_right (le_refl _),Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
 rw[show D[j].1=cR D j by simp[cR,L2 a],show D[j].2.1=cj D j by simp[cj,L2 a],show D[j].2.2=ck D j by simp[ck,L2 a],<-L0,<-L0,iS D _ j _ (by simpa using c) a.le,iS D _ j _ (by simpa using d) a.le];simp only[L0]
lemma _0.iA {n:ℕ} {D:Dag} (c:au n D) (x:Fd n) (f:ℕ->_d) (a:∀ i (h:i<n),f i=x ⟨i,h⟩) (e:∀ j,j<D.length->f (n+j)=kF (cR D j) (f (cj D j)) (f (ck D j))):∀ w,w<n+D.length->val D x w=f w:=fun w=>
 w.strong_induction_on fun w q l=>if d:w<n then (bY D x w d).trans (a w d).symm else by
  obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have b:j<D.length:=by {omega};obtain⟨g,k,-⟩:=c j b;rw[cS c x j b,e j b,q _ g (by omega),q _ k (by omega)]
lemma gM (D E:Dag) (k:ℕ) (h:k<D.length):(D ++ E).getD k (false,0,0)=D.getD k (false,0,0):=by simp[L1 h]
lemma f9 (D:Dag) (g:_d×ℕ×ℕ):(D ++ [g]).getD D.length (false,0,0)=g:=by simp
lemma jG {n:ℕ} {D:Dag} (d:au n D) (t:_d) (i j:ℕ) (e:i<n+D.length) (f:j<n+D.length) (b:i≠j):au n (D ++ [(t,i,j)]):=fun k g=>by
 simp only[List.length_append,List.length_singleton] at g;by_cases h:k<D.length
 · simp only[cj,ck,gM D _ k h];exact d k h
 · obtain rfl:k=D.length:=by {omega};simp only[cj,ck,f9];exact⟨e,f,b⟩
end
namespace _0
abbrev js:=_d⊕ℕ
def db (W:_F _d):js->_d | .inl b=>b | .inr k=>W.getD k false
def eP (m:_F js) (i:ℕ):js:=m.getD i (.inl false)
def dQ:GateOp->_d | .and=>true | _=>false
def iT (B:ℕ):js->Prop | .inl _=>True | .inr k=>k<B
def j4 (n:ℕ) (a:_F js×Dag):Prop:=au n a.2/\∀ r∈a.1,iT (n+a.2.length) r
def evM {n:ℕ} (l:_F js×Dag) (x:Fd n):_F _d:=l.1.map (db (kD l.2 (_of x)))
def stp (w:_F _d) (g:Gate):_F _d:=w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def mG (g:Gate):Prop:=g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2
def c2 (n:ℕ) (c:_F js×Dag) (t:_d):js->js->_F js×Dag
 | .inl u,r=>(c.1++[if u=t then r else .inl u],c.2)
 | .inr i,.inl u=>(c.1++[if u=t then .inr i else .inl u],c.2)
 | .inr i,.inr j=>if i=j then (c.1++[.inr i],c.2) else (c.1++[.inr (n+c.2.length)],c.2++[(t,i,j)])
def cH (n:ℕ) (c:_F js×Dag) (g:Gate):_F js×Dag:=match g.inputs with
 | []=>(c.1++[.inl (dQ g.op)],c.2) | [a]=>(c.1++[eP c.1 a],c.2) | a::b::_=>c2 n c (dQ g.op) (eP c.1 a) (eP c.1 b)
lemma fD (W:_F _d) (m:_F js) (i:ℕ):db W (eP m i)=(m.map (db W)).getD i false:=by simp only[eP,L0,List.getElem?_map];cases m[i]? <;> rfl
lemma iB (B:ℕ) (m:_F js) (a:∀ r∈m,iT B r) (i:ℕ):iT B (eP m i):=by simp only[eP,L0];rcases h:m[i]? with _|r;{trivial};{exact a r (List.mem_of_getElem? h)}
lemma nL (n:ℕ) (l:_F js×Dag) (g:Gate) (C:mG g) (h:j4 n l):j4 n (cH n l g)/\(cH n l g).2.length<=l.2.length+1/\∀ x:Fd n,evM (cH n l g) x=stp (evM l x) g:=by
 obtain⟨m,D⟩:=l;obtain⟨o,s⟩:=g;obtain⟨f,q⟩:=C;obtain⟨v,e⟩:=h;let W (x:Fd n):=kD D (_of x);let M (x:Fd n):=m.map (db (W x))
 have S:∀ r,iT (n+D.length) r->(∀ x:Fd n,db (W x) r=o.eval (s.map fun i=>(M x).getD i false))->j4 n (m++[r],D)/\(m++[r],D).2.length<=D.length+1/\∀ x:Fd n,evM (m++[r],D) x=stp (M x) ⟨o,s⟩:=
  fun r u w=>⟨⟨v,fun z y=>(List.mem_append.1 y).elim (e z) fun h=>(List.mem_singleton.1 h)▸u⟩,Nat.le_succ _,fun x=>by simp[evM,stp,M,W,w]⟩
 rcases s with _|⟨a,_|⟨b,_|⟨c,z⟩⟩⟩
 · exact S _ trivial fun _=>by rcases f with rfl|rfl <;> rfl
 · exact S _ (iB _ m e a) fun _=>by simp only[M,List.map_singleton,fD];rcases f with rfl|rfl <;> simp[GateOp.eval]
 · have A:=iB _ m e a;have B:=iB _ m e b;dsimp only[cH]
   have F:∀ x:Fd n,o.eval ([a,b].map fun i=>(M x).getD i false)=kF (dQ o) (db (W x) (eP m a)) (db (W x) (eP m b)):=fun x=>by rw[List.map_cons,List.map_singleton,<-fD,<-fD];rcases f with rfl|rfl <;> simp[GateOp.eval,dQ]
   generalize dQ o=t at F⊢;generalize eP m a=p at A F⊢;generalize eP m b=r at B F⊢
   rcases p with u|i;{exact S _ (by split_ifs;{exact B};{trivial}) fun x=>by rw[F];cases t <;> cases u <;> simp[db]}
   rcases r with u|j;{exact S _ (by split_ifs;{exact A};{trivial}) fun x=>by rw[F];cases t <;> cases u <;> simp[db]}
   dsimp only[c2];split_ifs with E;{exact S _ A fun x=>by rw[F,E];cases t <;> simp[db]}
   refine⟨⟨jG v t i j A B E,fun z y=>?_⟩,by simp,fun x=>?_⟩
   · rcases List.mem_append.1 y with y|y;{rcases z with _|k;{trivial};{have:=e _ y;simp[iT] at this⊢;omega}};{rw[List.mem_singleton.1 y];simp[iT]}
   · have K:(W x).length=n+D.length:=by {rw[jr,List.length_ofFn]}
     have H:m.map (db (gl (W x) (t,i,j)))=M x:=List.map_congr_left fun z y=>by rcases z with _|k;{rfl};{simp[db,gl,L1 (show k<(W x).length by rw[K];exact e _ y)]}
     change (m++[Sum.inr (n+D.length)]).map (db (kD (D++[(t,i,j)]) (_of x)))=M x++[o.eval ([a,b].map fun i=>(M x).getD i false)]
     rw[show kD (D++[(t,i,j)]) (_of x)=gl (W x) (t,i,j) from k4 D _ _,List.map_append,H,List.map_singleton,F];simp[db,<-K,gl]
 · simp at q
lemma nM (n:ℕ) (b:_F Gate) (c:∀ g∈b,mG g):∀ a:_F js×Dag,j4 n a->j4 n (b.foldl (cH n) a)/\(b.foldl (cH n) a).2.length<=a.2.length+b.length/\∀ x:Fd n,evM (b.foldl (cH n) a) x=b.foldl stp (evM a x):=by
 induction b with | nil=>intro a h;exact⟨h,by simp,fun _=>rfl⟩ | cons g b q=>intro a h;obtain⟨f,l,j⟩:=nL n a g (c g (by simp)) h;obtain⟨x,y,z⟩:=q (fun u v=>c u (by simp[v])) _ f;exact⟨x,by simp only[List.foldl_cons,List.length_cons];omega,fun w=>by simp only[List.foldl_cons];rw[z w,j w]⟩
lemma iU {D:Dag} {w:ℕ} (f:aF D w=0) (k:ℕ) (a:k<D.length):cj D k≠w/\ck D k≠w:=by unfold aF bV at f;rw[C0,FE] at f;have:=f (MR.2 a);tauto
def jt (c a:ℕ):ℕ:=if c<a then a-1 else a
def cX (c w:ℕ):ℕ:=if w<c then w else w+1
def eL (n j:ℕ) (D:Dag):Dag:=(D.eraseIdx j).map fun g=>(g.1,jt (n+j) g.2.1,jt (n+j) g.2.2)
lemma eLok {n:ℕ} {D:Dag} (d:au n D) (j:ℕ) (c:j<D.length) (f:aF D (n+j)=0):(eL n j D).length=D.length-1/\au n (eL n j D)/\∀ (x:Fd n) (w:ℕ),w<n+(D.length-1)->val (eL n j D) x w=val D x (cX (n+j) w):=by
 let E:=eL n j D;let X:=cX (n+j);let J:=jt (n+j)
 have L:E.length=D.length-1:=by {simp[E,eL,List.length_eraseIdx,c]}
 have G:∀ k,cX j k<D.length->cR E k=cR D (cX j k)/\cj E k=J (cj D (cX j k))/\ck E k=J (ck D (cX j k)):=fun k a=>by
  have e:E.getD k (false,0,0)=((D.getD (cX j k) (false,0,0)).1,J (D.getD (cX j k) (false,0,0)).2.1,J (D.getD (cX j k) (false,0,0)).2.2):=by simp only[E,eL,J,L0,List.getElem?_map,List.getElem?_eraseIdx];unfold cX at a⊢;split_ifs at a⊢ <;> simp[L2 a]
  unfold cR cj ck;rw[e];exact⟨rfl,rfl,rfl⟩
 have A:au n E:=fun k g=>by
  rw[L] at g;have p:cX j k<D.length:=by {unfold cX;split_ifs <;> omega}
  have h:(k<j/\cX j k=k)\/(j<=k/\cX j k=k+1):=by {unfold cX;split_ifs <;> omega}
  obtain⟨l,m,i⟩:=d _ p;obtain⟨r,s⟩:=iU f _ p;obtain⟨-,u,v⟩:=G k p;rw[u,v];generalize cX j k=y at *;generalize cj D y=a at *;generalize ck D y=b at *;refine⟨?_,?_,?_⟩ <;> unfold J jt <;> split_ifs <;> omega
 refine⟨L,A,fun x w l=>iA A x (fun u=>val D x (X u)) (fun i g=>by rw[show X i=i by unfold X cX;split_ifs <;> omega];exact bY D x i g) (fun k m=>?_) w (by rw[L];exact l)⟩
 rw[L] at m;have p:cX j k<D.length:=by {unfold cX;split_ifs <;> omega};obtain⟨t,u,v⟩:=G k p;obtain⟨r,s⟩:=iU f _ p
 have I:∀ a,a≠n+j->X (J a)=a:=fun a q=>by unfold X J cX jt;split_ifs <;> omega
 rw[show X (n+k)=n+cX j k by unfold X cX;split_ifs <;> omega,t,u,v,I _ r,I _ s];exact cS d x _ p
end _0
section
open _0
lemma fV {n:ℕ} (C:Circuit) (a:Monotone2 C) (d:∀ b:_d,∃ x:Fd n,C.eval (_of x)≠b) (e:∀ i:Fin n,∃ x:Fd n,C.eval (_of x)≠x i) (c:∀ i:Fin n,∃ x y:Fd n,(∀ k,k≠i->x k=y k)/\C.eval (_of x)≠C.eval (_of y)):∃ D:Dag,ai n D/\D.length<=C.size/\∀ x:Fd n,val D x (bH n D)=C.eval (_of x):=by
 obtain⟨⟨s,f⟩,A,B⟩:=nM n C.gates a _ (show j4 n ((List.range n).map Sum.inr,[]) from ⟨fun _ u=>AB u (by simp),fun r h=>by obtain⟨k,p,rfl⟩:=List.mem_map.1 h;simpa[iT] using List.mem_range.1 p⟩)
 generalize C.gates.foldl (cH n) ((List.range n).map Sum.inr,([]:Dag))=z at s f A B;obtain⟨m,D⟩:=z;dsimp only[evM,stp] at s f A B
 have g:∀ x:Fd n,C.eval (_of x)=db (kD D (_of x)) (eP m C.output):=fun x=>by rw[fD,B x,show ((List.range n).map Sum.inr).map (db (kD [] (_of x)))=_of x from List.ext_getElem (by simp) fun i h _=>by simp[db,kD,show i<n by simpa using h]];rfl
 have p:=iB _ m f C.output;rcases O:eP m C.output with b|k;{obtain⟨x,h⟩:=d b;exact AB (by rw[g x,O];rfl) h}
 rw[O] at p;by_cases l:k<n;{obtain⟨x,h⟩:=e ⟨k,l⟩;exact AB (by rw[g x,O];exact bY D x k l) h}
 have P:k<n+D.length:=p;let E:=D.take (k-n+1);have q:E.length=k-n+1:=by {rw[L3];omega}
 have U:au n E:=fun j h=>by have r:j<k-n+1/\j<D.length:=by {rw[L3] at h;omega};have u:E.getD j (false,0,0)=D.getD j (false,0,0):=by {simp[E,r.1]};simpa only[cj,ck,u] using s j r.2
 have N:E≠[]:=fun h=>by rw[h] at q;simp at q
 have F:∀ x:Fd n,val E x (bH n E)=C.eval (_of x):=fun x=>by rw[show bH n E=k by unfold bH;rw[q];omega,oe D x (k-n+1) k (by omega) (by omega),g x,O];rfl
 have S:E.length<=C.size:=by {simp only[List.length_nil,Nat.zero_add] at A;unfold Circuit.size;omega}
 clear_value E;clear q;generalize K:E.length=t;induction t using SI generalizing E with
 | _ t I=>
  have Q:0<E.length:=LP.2 N;by_cases o:o7 n E;{exact⟨E,⟨U,o,N⟩,S,F⟩}
  obtain⟨w,W,Z⟩:∃ w,w+1<n+E.length/\aF E w=0:=by by_contra M;exact o fun w r=>by by_contra y;exact M ⟨w,r,by omega⟩
  by_cases v:w<n
  · exfalso;obtain⟨x,y,G,H⟩:=c ⟨w,v⟩;apply H;rw[<-F x,<-F y]
    have J:=iA U y (fun u=>if u=w then y ⟨w,v⟩ else val E x u) (fun i r=>by by_cases h:i=w;{subst h;simp};{simp only[h,ite_false];rw[bY E x i r];exact G ⟨i,r⟩ fun u=>h (CG Fin.val u)}) (fun j r=>by obtain⟨u,h⟩:=iU Z j r;have b:n+j≠w:=by {omega};simp only[b,u,h,ite_false];exact cS U x j r) (bH n E) (by unfold bH;omega)
    simp only[show bH n E≠w by unfold bH;omega,ite_false] at J;exact J.symm
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have r:j<E.length:=by {omega};obtain⟨L,R,V⟩:=eLok U j r Z
    exact I (E.length-1) (by omega) (eL n j E) R (fun h=>by rw[h] at L;simp at L;omega) (fun x=>by rw[show bH n (eL n j E)=n+(E.length-1)-1 by unfold bH;rw[L],V x _ (by omega),show cX (n+j) (n+(E.length-1)-1)=bH n E by unfold cX bH;split_ifs <;> omega];exact F x) (by omega) L
end
section SurplusFlow
open _0
variable {n:ℕ} {D:Dag}
lemma bP {w:ℕ}:w∈cD n D<->w+1<n+D.length:=by unfold cD;rw[MR];omega
lemma aX (j:ℕ):aw D (j,false)=cj D j:=rfl
lemma bh (j:ℕ):aw D (j,true)=ck D j:=rfl
lemma d0 (b:au n D) (w:ℕ) (h:n+D.length<=w+1):aF D w=0:=by unfold aF bV;rw[C0,FE];intro j c;have d:=MR.1 c;have:=b j d;omega
lemma dc (a:au n D) {w:ℕ} (h:1<=aF D w):w+1<n+D.length:=by by_contra b;have:=d0 a w (by omega);omega
lemma d8 (P:Ed->Prop) [DecidablePred P]:((eK D).filter P).card=∑ j∈range D.length,((if P (j,false) then 1 else 0)+(if P (j,true) then 1 else 0)):=by rw[CF,eK,sum_product];exact SC rfl fun j _=>by rw[Fintype.sum_bool,add_comm]
lemma _0.fF (b:au n D) (K:Finset ℕ):∑ w∈K,aF D w=((eK D).filter (fun e=>aw D e∈K)).card:=by
 rw[card_eq_sum_card_fiberwise (f:=aw D) (s:=(eK D).filter (fun e=>aw D e∈K)) (t:=K) (fun e a=>(_mf.1 a).2)]
 refine SC rfl fun w c=>?_
 have h:aF D w=((eK D).filter (fun e=>aw D e=w)).card:=by rw[d8,aF,bV,CF];exact SC rfl fun j d=>by have:=(b j (MR.1 d)).2.2;rw[aX,bh];split_ifs <;> omega
 rw[h,filter_filter];congr 1;ext e;simp only[_mf];exact⟨fun ⟨a,f⟩=>⟨a,f▸c,f⟩,fun ⟨a,_,f⟩=>⟨a,f⟩⟩
lemma _0.eQ {K:Finset ℕ} (a:∀ w∈K,1<=aF D w):bn D K+K.card=∑ w∈K,aF D w:=by rw[bn,card_eq_sum_ones,<-sum_add_distrib];exact SC rfl fun w b=>Nat.sub_add_cancel (a w b)
lemma iC (h:ai n D):ap n D+n=D.length+1:=by
 obtain⟨b,d,a⟩:=h;have c:0<D.length:=LP.2 a;have:=eQ (D:=D) (K:=cD n D) fun w f=>d w (bP.1 f)
 have j:∑ w∈cD n D,aF D w=2*D.length:=by rw[fF b,filter_true_of_mem (fun ⟨j,s⟩ g=>by have f:j<D.length:=by {simpa[eK] using g};have:=b j f;cases s <;> {rw[bP];simp[aw];omega})];simp[eK,card_product,Nat.mul_comm]
 have:(cD n D).card=n+D.length-1:=card_range _;unfold ap;omega
lemma bg (n:ℕ) (D:Dag):ap n D=bd n D+bL n D:=by unfold ap bd bL bn;exact(sum_filter_add_sum_filter_not _ _ _).symm
lemma dC (n:ℕ) (D:Dag):bd n D<=ap n D:=by rw[bg];omega
lemma iD (h:ai n D) (w:ℕ) (i:w<n+D.length):RT (fun a b=>b<n+D.length/\n<=b/\(cj D (b-n)=a\/ck D (b-n)=a)) w (bH n D):=by
 obtain⟨f,g,-⟩:=h;generalize l:n+D.length-w=k;induction k using SI generalizing w with
 | _ k q=>
  by_cases c:w+1=n+D.length;{rw[show w=bH n D by unfold bH;omega]}
  obtain⟨j,e⟩:=_cp.1 (g w (by omega));simp only[bV,_mf,MR] at e;have:=f j e.1
  exact RTh (b:=n+j) ⟨by omega,by omega,by simpa using e.2⟩ (q (n+D.length-(n+j)) (by omega) (n+j) (by omega) rfl)
lemma ee {v:Fin n} {w:ℕ}:v∈ag n D w<->val D (cl v) w=true:=by simp[ag]
lemma gJ (a:au n D) (x y:Fd n) (b:∀ i,x i=true->y i=true) (w:ℕ):val D x w=true->val D y w=true:=by
 induction w using SI with
 | _ w q=>
  by_cases d:w<n;{rw[bY D x w d,bY D y w d];exact b _}
  by_cases g:w<n+D.length
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have c:j<D.length:=by {omega};obtain⟨e,f,-⟩:=a j c;rw[cS a x j c,cS a y j c];have:=q _ e;have:=q _ f;cases cR D j <;> simp only[gop_true,gop_false,BA,BO] <;> tauto
  · rw[fs D x w (by omega)];simp
lemma qN (a:au n D) (w:ℕ):val D (fun _:Fin n=>false) w=false:=if b:w<n+D.length then iA a _ (fun _=>false) (fun _ _=>rfl) (fun j _=>by cases cR D j <;> rfl) w b else fs D _ w (by omega)
lemma dr (D:Dag) (i:Fin n):ag n D i.val={i}:=by ext v;rw[ee,bY D (cl v) i.val i.isLt];simp[cl,eq_comm]
lemma _0.pc (D:Dag) (w:ℕ) (h:n+D.length<=w):ag n D w=∅:=by ext v;simp[ee,fs D (cl v) w h]
lemma fY (a:au n D) (j:ℕ) (b:j<D.length):ag n D (n+j)=if cR D j=true then ag n D (cj D j)∩ag n D (ck D j) else ag n D (cj D j)∪ag n D (ck D j):=by ext v;rw[ee,cS a _ j b];cases cR D j <;> simp[ee]
lemma _0.ro (h:ai n D) (K:Finset ℕ) (f:K⊆cD n D):(aE n D K).card+(aW n D K).card=(K.filter (fun w=>w<n\/(cj D (w-n)∉K/\ck D (w-n)∉K))).card+bn D K:=by
 let P (w:ℕ):=w<n\/(cj D (w-n)∉K/\ck D (w-n)∉K);let Q:=(range D.length).filter fun j=>n+j∈K/\(cj D j∈K\/ck D j∈K)
 obtain⟨g,i,-⟩:=h;have a:∀ w∈K,w+1<n+D.length:=fun w b=>bP.1 (f b)
 have r:bn D K+K.card=((eK D).filter (fun e=>aw D e∈K)).card:=by rw[<-fF g,eQ fun w b=>i w (a w b)]
 have k:=card_filter_add_card_filter_not (s:=(eK D).filter (fun e=>aw D e∈K)) (fun e:Ed=>n+e.1∈K);rw[filter_filter,filter_filter] at k
 have t:((eK D).filter (fun e=>aw D e∈K/\n+e.1∈K)).card=Q.card+(aW n D K).card:=by rw[d8,aW,CF,CF,<-sum_add_distrib];exact SC rfl fun j _=>by rw[aX,bh];by_cases l:n+j∈K <;> by_cases u:cj D j∈K <;> by_cases v:ck D j∈K <;> simp_all
 have x:K.card=(K.filter P).card+Q.card:=by
  rw[<-card_filter_add_card_filter_not (s:=K) P];congr 1
  have c:K.filter (fun w=>¬P w)=Q.image (fun j=>n+j):=by ext w;simp only[P,Q,_mf,_mg,MR];exact⟨fun ⟨b,m⟩=>by have:=a w b;rw[not_or] at m;exact⟨w-n,⟨by omega,by rwa[Nat.add_sub_cancel' (by omega)],by tauto⟩,by omega⟩,fun ⟨j,⟨_,p,q⟩,e⟩=>by subst e;refine⟨p,?_⟩;rw[AC];rintro (d|d);{omega};{tauto}⟩
  rw[c,_cii _ (add_right_injective n)]
 unfold aE;dsimp only[P] at x;omega
lemma _0.kN (h:ai n D) (K:Finset ℕ) (g:K⊆cD n D) (b:∀ j,j<D.length->n+j∈K->cj D j∈K\/ck D j∈K):(aE n D K).card+(aW n D K).card=(gb n K).card+bn D K:=by
 rw[ro h K g];congr 2;ext w;simp only[gb,_mf];exact⟨fun ⟨c,d⟩=>d.elim (fun d=>⟨c,d⟩) fun d=>if u:w<n then ⟨c,u⟩ else by have:=bP.1 (g c);have:=b (w-n) (by omega) (by rwa[Nat.add_sub_cancel' (by omega)]);tauto,fun ⟨c,d⟩=>⟨c,.inl d⟩⟩
lemma co (h:ai n D) (T:Fn n) (b:ag n D (bH n D)∩T=∅):(aE n D (ao n D T)).card+(aW n D (ao n D T)).card=T.card+bn D (ao n D T):=by
 have f:gb n (ao n D T)=T.image Fin.val:=by ext w;simp only[gb,ao,_mf,MR,_mg];exact⟨fun ⟨⟨_,v,c⟩,d⟩=>by rw[dr D ⟨w,d⟩,_mn,_ms] at c;exact⟨v,c.2,by rw[c.1]⟩,fun ⟨v,c,e⟩=>by subst e;exact⟨⟨by have:=v.isLt;omega,v,by rw[dr];simp[c]⟩,v.isLt⟩⟩
 rw[<-_cii Fin.val Fin.val_injective (s:=T),<-f]
 refine kN h _ (fun w c=>by simp only[ao,_mf,MR] at c;rw[bP];by_contra d;rw[show w=bH n D by unfold bH;omega,b] at c;exact NE c.2) fun j d e=>?_
 obtain⟨p,g,-⟩:=h.1 j d;simp only[ao,_mf,MR] at e⊢;obtain⟨v,a⟩:=e.2;rw[_mn,fY h.1 j d] at a;split_ifs at a
 · rw[_mn] at a;exact .inl ⟨by omega,v,_mn.2 ⟨a.1.1,a.2⟩⟩
 · rw[_mu] at a;rcases a.1 with c|c;{exact .inl ⟨by omega,v,_mn.2 ⟨c,a.2⟩⟩};{exact .inr ⟨by omega,v,_mn.2 ⟨c,a.2⟩⟩}
lemma gN (h:ai n D) (x y:Fin n) (l:x≠y) (e:x∉ag n D (bH n D)):(aE n D (aR n D x y)).card+(aW n D (aR n D x y)).card=1+bn D (aR n D x y):=by
 have g:gb n (aR n D x y)={x.val}:=by ext w;simp only[gb,aR,_mf,MR,_ms];exact⟨fun ⟨⟨_,a,_⟩,d⟩=>by rw[dr D ⟨w,d⟩,_ms] at a;rw[a],fun h=>by subst h;exact⟨⟨by have:=x.isLt;omega,by rw[dr];exact _mss x,by rw[dr,_ms];exact fun b=>l b.symm⟩,x.isLt⟩⟩
 rw[<-_cs x.val,<-g]
 refine kN h _ (fun w d=>by simp only[aR,_mf,MR] at d;rw[bP];by_contra b;rw[show w=bH n D by unfold bH;omega] at d;exact e d.2.1) fun j q r=>?_
 obtain⟨t,u,-⟩:=h.1 j q;simp only[aR,_mf,MR] at r⊢;obtain⟨-,a,c⟩:=r;rw[fY h.1 j q] at a c;split_ifs at a c
 · rw[_mn] at a c;by_cases k:y∈ag n D (cj D j);{exact .inr ⟨by omega,a.2,fun b=>c ⟨k,b⟩⟩};{exact .inl ⟨by omega,a.1,k⟩}
 · rw[_mu] at a c;rcases a with p|p;{exact .inl ⟨by omega,p,fun b=>c (.inl b)⟩};{exact .inr ⟨by omega,p,fun b=>c (.inr b)⟩}
lemma dW {u:Sg}:u∈dq n D<->u.1∈cD n D/\u.2+1<aF D u.1:=by rw[dq,mem_sigma,MR];exact⟨fun ⟨a,b⟩=>⟨a,by omega⟩,fun ⟨a,b⟩=>⟨a,by omega⟩⟩
lemma eI (n:ℕ) (D:Dag) (p:ℕ->Prop) [DecidablePred p]:((dq n D).filter (fun u=>p u.1)).card=bn D ((cD n D).filter p):=by have a:(dq n D).filter (fun u=>p u.1)=((cD n D).filter p).sigma (fun w=>range (aF D w-1)):=by {ext u;simp only[dq,_mf,mem_sigma];tauto};rw[a,card_sigma,bn];simp
lemma mv (n:ℕ) (D:Dag):(dq n D).card=ap n D:=by rw[dq,card_sigma,ap,bn];simp
lemma jH (n:ℕ) (D:Dag):(da n D).card=bd n D:=by unfold da bd;exact eI n D fun w=>(ag n D w).Nonempty
lemma eX {v:Fin n}:v∈al n D<->∃ w,2<=aF D w/\v∈ag n D w:=by simp only[al,m5,mem_biUnion,_mf,MR];exact⟨fun ⟨w,⟨_,b⟩,a⟩=>⟨w,b,a⟩,fun ⟨w,b,a⟩=>⟨w,⟨by by_contra c;rw[pc D w (by omega)] at a;exact NM v a,b⟩,a⟩⟩
lemma fG {v:Fin n}:v∈aa n D<->∀ w,v∈ag n D w->aF D w<=1:=by rw[aa,_md,eX];exact⟨fun ⟨_,h⟩ w a=>by by_contra c;exact h ⟨w,by omega,a⟩,fun h=>⟨_mv v,fun ⟨w,a,b⟩=>by have:=h w b;omega⟩⟩
lemma _0.je (b:Fv n) (d:aM n D b):Set.InjOn (fun v=>(⟨b v,0⟩:Sg)) (al n D:Set (Fin n)):=fun v g e a h=>by have c:b v=b e:=CG Sigma.fst h;have f:=(d v g).2;rw[c,(d e a).2] at f;exact(SG f).symm
lemma _0.eY (a:au n D) (b:Fv n) (c:aM n D b):cz n D b⊆da n D:=fun u d=>by obtain⟨v,e,rfl⟩:=_mg.1 d;obtain⟨h,f⟩:=c v e;rw[da,_mf,dW];exact⟨⟨bP.2 (dc a (show 1<=aF D (b v) by omega)),by show 0+1<aF D (b v);omega⟩,by show (ag n D (b v)).Nonempty;rw[f];exact singleton_nonempty v⟩
lemma dX (c:au n D) (b:Fv n) (a:aM n D b):(al n D).card<=bd n D:=by rw[<-_cij (je b a),<-jH];exact _cl (eY c b a)
lemma bS (c:au n D) (b:Fv n) (a:aM n D b):(aj n D b).card+(al n D).card=bd n D:=by rw[<-_cij (je b a),<-jH];exact CS (eY c b a)
lemma _0.bnF (j:au n D) (b:Fv n) (h:aM n D b) (P:ℕ->Prop) [DecidablePred P] (q:∀ w,P w->(ag n D w).Nonempty):bn D ((range (n+D.length)).filter P)=((al n D).filter (fun v=>P (b v))).card+((aj n D b).filter (fun u=>P u.1)).card:=by
 let F (s:Finset Sg):=s.filter fun u=>P u.1
 have l:bn D ((range (n+D.length)).filter P)=(F (dq n D)).card:=by rw[eI n D P];symm;refine sum_subset (fun w c=>by rw[_mf] at c;have:=bP.1 c.1;exact _mf.2 ⟨MR.2 (by omega),c.2⟩) fun w c d=>by rw[_mf] at c;have i:w∉cD n D:=fun m=>d (_mf.2 ⟨m,c.2⟩);rw[bP] at i;simp[d0 j w (by omega)]
 have p:F (dq n D)=F (cz n D b)∪F (aj n D b):=by ext u;have e:=eY j b h;simp only[F,aj,da,_mu,_mf,_md];exact⟨fun a=>if k:u∈cz n D b then .inl ⟨k,a.2⟩ else .inr ⟨⟨⟨a.1,q u.1 a.2⟩,k⟩,a.2⟩,fun a=>a.elim (fun a=>⟨(_mf.1 (e a.1)).1,a.2⟩) fun a=>⟨a.1.1.1,a.2⟩⟩
 have d:Disjoint ((cz n D b).filter fun u=>P u.1) ((aj n D b).filter fun u=>P u.1):=disjoint_filter_filter disjoint_sdiff
 rw[l,p];dsimp only[F];rw[_cud d,cz,filter_image,_cij ((je b h).mono (coe_subset.2 (_fs _ _)))]
lemma d9 (j:au n D) (b:Fv n) (h:aM n D b) (T:Fn n):bn D (ao n D T)=(T∩al n D).card+((aj n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)).card:=by
 rw[ao,bnF j b h _ fun _ c=>c.mono IL];congr 2;ext v;simp only[_mf,_mn];exact⟨fun ⟨a,u,d⟩=>⟨by rw[(h v a).2,_mn,_ms] at d;exact d.1▸d.2,a⟩,fun ⟨c,a⟩=>⟨a,v,by rw[(h v a).2];exact _mn.2 ⟨_mss v,c⟩⟩⟩
lemma cZ (a:au n D) (b:Fv n) (c:aM n D b) (T:Fn n):bn D (ao n D T)+(al n D).card<=(T∩al n D).card+bd n D:=by have:=d9 a b c T;have:=bS a b c;have:=_cfl (aj n D b) (fun u=>(ag n D u.1∩T).Nonempty);omega
end SurplusFlow
def cG {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):ℕ:=if h:w<n then (σ ⟨w,h⟩).val else w
def bo {n:ℕ} (σ:_ep (Fin n)) (D:Dag):Dag:=D.map (fun g=>(g.1,cG σ g.2.1,cG σ g.2.2))
section
open _0
lemma _0.c9 {n:ℕ} (σ:_ep (Fin n)) {m:ℕ} (a:n<=m) (w:ℕ):cG σ w<m<->w<m:=by unfold cG;split_ifs with h;{have:=(σ ⟨w,h⟩).isLt;exact⟨fun _=>by omega,fun _=>by omega⟩};rfl
lemma _0.fx {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):cG σ⁻¹ (cG σ w)=w:=by by_cases h:w<n;{simp[cG,h,(σ ⟨w,h⟩).isLt]};{simp[cG,h]}
lemma _0.fx' {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):cG σ (cG σ⁻¹ w)=w:=by simpa using fx σ⁻¹ w
lemma _0.iV {n:ℕ} (σ:_ep (Fin n)) {a b:ℕ}:cG σ a=cG σ b<->a=b:=⟨fun h=>by have:=CG (cG σ⁻¹) h;rwa[fx,fx] at this,CG _⟩
lemma cc {n:ℕ} (σ:_ep (Fin n)) (D:Dag):(bo σ D).length=D.length:=by simp[bo]
lemma _0.boG {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (j:ℕ) (a:j<D.length):cR (bo σ D) j=cR D j/\cj (bo σ D) j=cG σ (cj D j)/\ck (bo σ D) j=cG σ (ck D j):=by simp[cR,cj,ck,bo,L2 a]
lemma _0.jI {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (c:au n D):au n (bo σ D):=fun j a=>by rw[cc] at a;obtain⟨d,e,b⟩:=c j a;obtain⟨-,u,v⟩:=boG σ D j a;rw[u,v];exact⟨(c9 σ (AR n j) _).2 d,(c9 σ (AR n j) _).2 e,fun h=>b ((iV σ).1 h)⟩
lemma _0.lj {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (d:au n D) (x:Fd n) (w:ℕ):val (bo σ D) x (cG σ w)=val D (fun i=>x (σ i)) w:=by
 by_cases e:w<n+D.length
 · refine(iA (jI σ d) x (fun u=>val D (fun i=>x (σ i)) (cG σ⁻¹ u)) (fun i c=>by rw[show cG σ⁻¹ i=(σ⁻¹ ⟨i,c⟩).val by simp[cG,c],bY D _ _ (σ⁻¹ ⟨i,c⟩).isLt];simp) (fun j b=>?_) (cG σ w) (by rw[cc];exact(c9 σ (AR _ _) w).2 e)).trans (by rw[fx])
   rw[cc] at b;obtain⟨t,u,v⟩:=boG σ D j b;simp only[show cG σ⁻¹ (n+j)=n+j by simp[cG],t,u,v,fx];exact cS d _ j b
 · have f:=Nat.not_lt.1 e;rw[show cG σ w=w by simp[cG,show ¬w<n by omega],fs _ _ _ (by rw[cc];exact f),fs _ _ _ f]
lemma _0.ft {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (w:ℕ):aF (bo σ D) (cG σ w)=aF D w:=by unfold aF bV;rw[cc];congr 1;exact filter_congr fun j b=>by obtain⟨-,u,v⟩:=boG σ D j (MR.1 b);rw[u,v,iV,iV]
lemma fd {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (h:ai n D):ai n (bo σ D):=⟨jI σ h.1,by
 rcases eq_or_ne D [] with rfl|b;{exact h.2.1}
 intro w q;rw[cc] at q;have:=LP.2 b;rw[<-fx' σ w,ft];apply h.2.1
 by_cases p:w<n;{have:=(c9 σ⁻¹ le_rfl w).2 p;omega};{rw[show cG σ⁻¹ w=w by simp[cG,p]];exact q},by simpa[bo] using h.2.2⟩
lemma fI {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (c:au n D) (a:D≠[]) (x:Fd n):val (bo σ D) x (bH n (bo σ D))=val D (fun i=>x (σ i)) (bH n D):=by have:=LP.2 a;rw[show bH n (bo σ D)=cG σ (bH n D) by simp[cG,bH,cc,show ¬n+D.length-1<n by omega],lj σ c]
lemma fh {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (b:au n D) (w:ℕ):ag n (bo σ D) (cG σ w)=(ag n D w).image σ:=by ext v;simp only[ag,_mf,_mv,true_and,_mg];rw[lj σ b,show (fun i=>cl v (σ i))=cl (σ⁻¹ v) by funext i;simp[cl,Equiv.eq_symm_apply]];exact⟨fun h=>⟨σ⁻¹ v,h,by simp⟩,fun ⟨a,c,e⟩=>by subst e;simpa using c⟩
lemma eo {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (P Q:ℕ->Prop) [DecidablePred P] [DecidablePred Q] (a:∀ w,Q (cG σ w)<->P w):bn (bo σ D) ((cD n (bo σ D)).filter Q)=bn D ((cD n D).filter P):=by
 rcases eq_or_ne D [] with rfl|b;{simp[bn,bo,aF,bV]}
 have c:=LP.2 b;have d:n<=n+D.length-1:=by {omega};unfold bn cD;rw[cc]
 exact(sum_nbij' (s:=(range (n+D.length-1)).filter fun w=>Q (cG σ w)) (cG σ) (cG σ⁻¹) (fun x h=>by simp only[_mf,MR] at h⊢;exact⟨(c9 σ d x).2 h.1,h.2⟩) (fun x h=>by simp only[_mf,MR] at h⊢;exact⟨(c9 σ⁻¹ d x).2 h.1,by rw[fx'];exact h.2⟩) (fun x _=>fx σ x) (fun x _=>fx' σ x) (fun _ _=>rfl)).symm.trans (SC (filter_congr fun w _=>a w) fun w _=>by rw[ft])
lemma eJ {n:ℕ} (σ:_ep (Fin n)) (D:Dag):ap n (bo σ D)=ap n D:=by simpa[ap] using eo σ D (fun _=>True) (fun _=>True) fun _=>Iff.rfl
lemma j8 {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (a:au n D):bd n (bo σ D)=bd n D:=eo σ D _ _ fun w=>by rw[fh σ a];simp
lemma j9 {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (a:au n D):bL n (bo σ D)=bL n D:=eo σ D _ _ fun w=>by rw[fh σ a];simp
lemma fZ {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (e:au n D):al n (bo σ D)=(al n D).image σ:=by
 ext v;simp only[al,mem_biUnion,_mg,m5,_mf,MR];constructor
 · rintro⟨u,⟨g,c⟩,f⟩;obtain⟨w,rfl⟩:∃ w,u=cG σ w:=⟨cG σ⁻¹ u,(fx' σ u).symm⟩
   rw[fh σ e,_mg] at f;obtain⟨a,d,rfl⟩:=f;rw[ft] at c;rw[cc,c9 σ (AR _ _)] at g;exact⟨a,⟨w,⟨g,c⟩,d⟩,rfl⟩
 · rintro⟨a,⟨w,⟨g,c⟩,d⟩,rfl⟩;exact⟨cG σ w,⟨by rw[cc];exact(c9 σ (AR _ _) w).2 g,by rw[ft];exact c⟩,by rw[fh σ e];exact mem_image_of_mem _ d⟩
lemma ep {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (d:au n D):aa n (bo σ D)=(aa n D).image σ:=by ext v;simp only[aa,fZ σ d,_md,_mv,true_and,_mg];exact⟨fun h=>⟨σ⁻¹ v,fun e=>h ⟨σ⁻¹ v,e,by simp⟩,by simp⟩,fun ⟨a,f,e⟩ ⟨b,g,c⟩=>by subst e;exact f (σ.injective c▸g)⟩
lemma aV (n:ℕ) (D:Dag):(aa n D).card+(al n D).card=n:=by have h:=CS (subset_univ (al n D));rwa[card_univ,Fintype.card_fin] at h
end
def cN {n:ℕ} (G:Fin n->Fin n->Prop) (x:Fin n->_d):Prop:=∃ u v:Fin n,G u v/\x u=true/\x v=true
def bJ {n:ℕ} (G:Fin n->Fin n->Prop):Prop:=(∀ u v,G u v->G v u)/\(∀ u,¬ G u u)/\(∀ v w,v≠w->∃ z,G v z/\¬ G w z)/\(∀ u v,∃ a,G u a/\a≠v)
def bk (n:ℕ) (D:Dag) (a b:ℕ):Prop:=b<n+D.length/\n<=b/\(cj D (b-n)=a\/ck D (b-n)=a)
def b4 {n:ℕ} (u z:Fin n):Fin n->_d:=fun i=>decide (i=u)||decide (i=z)
def sem_Umbrella (n:ℕ) (G H:Fin n->Fin n->Prop) (D:Dag):Prop:=bJ H/\(∀ u v,G u v->H u v)/\(∀ x:Fin n->_d,cN G x->val D x (bH n D)=true)/\(∀ x:Fin n->_d,val D x (bH n D)=true->cN H x)/\(∀ u v:Fin n,¬ G u v->val D (b4 u v) (bH n D)=false)
abbrev dg (n:ℕ) (G:Fin n->Fin n->Prop) (D:Dag):Prop:=sem_Umbrella n G G D
lemma kO {n:ℕ} {G:Fin n->Fin n->Prop} {D:Dag} (a:dg n G D) (x:Fin n->_d):val D x (bH n D)=true<->cN G x:=⟨a.2.2.2.1 x,a.2.2.1 x⟩
lemma ju {n:ℕ} {G:Fin n->Fin n->Prop} {D:Dag} (d:bJ G) (h:∀ x:Fin n->_d,val D x (bH n D)=true<->cN G x):dg n G D:=⟨d,fun _ _ k=>k,fun x e=>(h x).2 e,fun x e=>(h x).1 e,fun u v f=>by by_contra g;rw[_nf] at g;obtain⟨a,b,c,i,j⟩:=(h _).1 g;simp only[b4,Bool.or_eq_true,decide_eq_true_eq] at i j;rcases i with rfl|rfl <;> rcases j with rfl|rfl;{exact d.2.1 _ c};{exact f c};{exact f (d.1 _ _ c)};{exact d.2.1 _ c}⟩
def bB {n:ℕ} (v:Fin n) (x:Fin n->_d):Fin n->_d:=fun i=>decide (i=v)||x i
def bM {n:ℕ} (A:Finset (Fin n)):Fin n->_d:=fun i=>decide (i∈A)
section
open _0
lemma eG {α:Type} {r p:α->α->Prop} (h:∀ a b,r a b->p a b) {a b:α} (c:RT r a b):RT p a b:=c.rec .refl fun _ d q=>q.tail (h _ _ d)
end
namespace _0
abbrev U {n:ℕ} (G H:Gr n) (D:Dag):=sem_Umbrella n G H D
end _0
section SemCore
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma dd (v:Fin n) (x:Fd n):∀ k,k≠v->x k=bB v x k:=fun k a=>by simp[bB,a]
lemma dm (v:Fin n) (x:Fd n):bB v x v=true:=by simp[bB]
lemma iE (v:Fin n) (x:Fd n):∀ i,x i=true->bB v x i=true:=fun i a=>by simp[bB,a]
lemma cO (a:au n D) {u:Fin n} {w:ℕ} (b:u∈ag n D w) {x:Fd n} (c:x u=true):val D x w=true:=gJ a (cl u) x (fun i h=>by simp only[cl,DE] at h;exact h▸c) w (ee.1 b)
lemma cP {v:Fin n} {w:ℕ} (a:v∈ag n D w):w<n+D.length:=by by_contra b;rw[pc D w (by omega)] at a;exact NM v a
lemma cB (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=true):ag n D (n+j)=ag n D (cj D j)∩ag n D (ck D j):=by rw[fY a j b,c];rfl
lemma de (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=false):ag n D (n+j)=ag n D (cj D j)∪ag n D (ck D j):=by rw[fY a j b,c];rfl
lemma cr (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=true) (s:_d):ag n D (n+j)⊆ag n D (aw D (j,s)):=by rw[cB a b c];cases s;{exact IL};{exact IR}
lemma dh (a:au n D) {j:ℕ} (b:j<D.length) (s:_d):aw D (j,s)<n+j:=by obtain⟨c,d,-⟩:=a j b;cases s;{exact c};{exact d}
lemma cM {j:ℕ} (a:j<D.length) (s:_d):bk n D (aw D (j,s)) (n+j):=⟨by omega,by omega,by rw[AC];cases s;{exact .inl rfl};{exact .inr rfl}⟩
lemma fj {a b:ℕ}:bk n D a b<->∃ j s,j<D.length/\b=n+j/\aw D (j,s)=a:=⟨fun ⟨d,e,c⟩=>c.elim (fun c=>⟨b-n,false,by omega,by omega,c⟩) (fun c=>⟨b-n,true,by omega,by omega,c⟩),fun ⟨j,s,f,u,v⟩=>u▸v▸cM f s⟩
lemma dR {a c:ℕ} (h:bk n D a c):c-n∈bV D a:=_mf.2 ⟨MR.2 (by have:=h.1;have:=h.2.1;omega),h.2.2⟩
lemma ef {a c:ℕ} (h:bk n D a c):1<=aF D a:=_cp.2 ⟨_,dR h⟩
lemma dS {a c d:ℕ} (b:bk n D a c) (g:bk n D a d) (e:aF D a=1):c=d:=by obtain⟨r,h⟩:=_c1.1 e;have f:=dR b;have i:=dR g;rw[h,_ms] at f i;have:=b.2.1;have:=g.2.1;omega
lemma d_ (e:au n D) (x y:Fd n) (v:Fin n) (f:∀ k,k≠v->x k=y k) (w:ℕ) (c:val D x w≠val D y w):RT (fun a b=>bk n D a b/\val D x b≠val D y b) v.val w:=by
 induction w using SI with
 | _ w q=>
  by_cases g:w<n;{rw[bY D x w g,bY D y w g] at c;have h:(⟨w,g⟩:Fin n)=v:=by {by_contra u;exact c (f _ u)};rw[<-h]}
  by_cases d:w<n+D.length
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have i:j<D.length:=by {omega};obtain⟨r,s,-⟩:=e j i;have m:=c;rw[cS e x j i,cS e y j i] at m
    by_cases p:val D x (cj D j)=val D y (cj D j);{exact(q _ s fun l=>m (by rw[p,l])).tail ⟨cM i true,c⟩};{exact(q _ r p).tail ⟨cM i false,c⟩}
  · exact AB (by rw[fs D x w (by omega),fs D y w (by omega)]) c
def j_ (n:ℕ) (D:Dag) (b v:ℕ):Prop:=b=v\/¬ Relation.ReflTransGen (fun a c=>bk n D a c/\c≠b) v (bH n D)
def bz (n:ℕ) (D:Dag) (a b:ℕ):Prop:=Relation.ReflTransGen (fun a c=>bk n D a c/\aF D a=1) a b
lemma dt (d:au n D) {R:ℕ->ℕ->Prop} (e:∀ a b,R a b->bk n D a b) {a b:ℕ} (h:RT R a b):a<=b:=by induction h with | refl=>exact le_refl _ | @tail x y _ c q=>obtain⟨u,v,w⟩:=e _ _ c;have:=d (y-n) (by omega);omega
lemma iH (k:au n D) {v b t:ℕ} (h:bz n D v b) (m:b<=t):b=v\/¬ RT (fun a c=>bk n D a c/\c≠b) v t:=by
 induction h using RThi with
 | refl=>exact .inl rfl
 | @head a c d f q=>
  by_cases g:b=a;{exact .inl g}
  right;intro p;rcases RTch p with r|⟨e,l,u⟩
  · have:=d.1.2.1;have:=k (c-n) (by have:=d.1.1;omega);have:=dt k (fun _ _ i=>i.1) f;rcases d.1.2.2 with z|z <;> omega
  · obtain rfl:c=e:=dS d.1 l.1 d.2;rcases q with rfl|q;{exact l.2 rfl};{exact q u}
lemma kc (l:au n D) (x y:Fd n) (v:Fin n) (e:∀ k,k≠v->x k=y k) (b t:ℕ) (d:b=v.val\/¬ RT (fun a c=>bk n D a c/\c≠b) v.val t) (i:val D x b=val D y b):val D x t=val D y t:=by
 by_contra f;rcases d with rfl|d;{rw[bY D x _ v.isLt,bY D y _ v.isLt] at i;exact f (by rw[show x=y from funext fun k=>if j:k=v then j▸i else e k j])};{exact d (eG (fun _ _ h=>⟨h.1,fun m=>h.2 (m▸i)⟩) (d_ l x y v e _ f))}
lemma mw (l:au n D) (x y:Fd n) (v:Fin n) (e:∀ k,k≠v->x k=y k) (b:ℕ) (d:j_ n D b v.val) (i:val D x b=val D y b):val D x (bH n D)=val D y (bH n D):=kc l x y v e b (bH n D) d i
lemma ds (k:au n D) {v b:ℕ} (h:bz n D v b):j_ n D b v:=by rcases RTct h with rfl|⟨_,_,s⟩;{exact .inl rfl};exact iH k h (by have:=s.1.1;unfold bH;omega)
lemma fy (i:au n D) (v:Fin n):∀ w,v∈ag n D w->(∀ u,u<w->v∈ag n D u->aF D u<=1)->bz n D v.val w:=fun w=>
 w.strong_induction_on fun w q d b=>if k:w<n then by rw[dr D ⟨w,k⟩,_ms] at d;rw[d];exact .refl else by
  have:=cP d;obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have h:j<D.length:=by {omega}
  have e:∀ s:_d,v∈ag n D (aw D (j,s))->bz n D v.val (n+j):=fun s f=>by have a:bk n D (aw D (j,s)) (n+j):=cM h s;have m:=dh i h s;have:=ef a;have:=b _ m f;exact(q _ m f fun u r=>b u (by omega)).tail ⟨a,by omega⟩
  rw[fY i j h] at d;split_ifs at d;{exact e false (_mn.1 d).1};rcases _mu.1 d with g|g;{exact e false g};{exact e true g}
lemma dF (f:bJ G) (v:Fin n):¬ cN G (cl v):=fun ⟨_,_,b,d,e⟩=>by simp only[cl,DE] at d e;exact f.2.1 _ (d▸e▸b)
lemma cs (_:bJ G) (a:U G H D):ag n D (bH n D)=∅:=EE fun v b=>dF a.1 v (a.2.2.2.1 _ (ee.1 b))
lemma _0.fk (r:bJ G) (e:au n D) (k:U G H D) (v:Fin n) (b:ℕ) (a:j_ n D b v.val):ag n D b⊆{v}:=fun u l=>_ms.2 <| by
 by_contra f;obtain⟨z,g,h⟩:=r.2.2.1 v u fun c=>f c.symm
 have i:val D (b4 u z) b=true:=cO e l (by simp[b4]);have j:val D (bB v (b4 u z)) b=true:=cO e l (by simp[bB,b4])
 have d:=mw e _ _ v (dd v (b4 u z)) b a (i.trans j.symm);have q:=k.2.2.1 (bB v (b4 u z)) ⟨v,z,g,dm v _,by simp[bB,b4]⟩;rw[<-d,k.2.2.2.2 u z h] at q;exact _fnt q
def cU (n:ℕ) (D:Dag) (b:Fin n->ℕ):Prop:=∀ v∈al n D,2<=aF D (b v)/\ag n D (b v)={v}/\bz n D v.val (b v)/\∀ w,2<=aF D w->v∈ag n D w->b v<=w
lemma b_ (k:bJ G) (e:au n D) (l:U G H D):∃ b:Fv n,cU n D b:=by
 classical
 have h:∀ v:Fin n,∃ b,v∈al n D->2<=aF D b/\ag n D b={v}/\bz n D v.val b/\∀ w,2<=aF D w->v∈ag n D w->b<=w:=fun v=>if d:v∈al n D then by
  have a:=eX.1 d;obtain⟨m,j⟩:=Nat.find_spec a;have c:=fy e v _ j fun u p f=>by by_contra r;exact Nat.find_min a p ⟨by omega,f⟩
  exact⟨Nat.find a,fun _=>⟨m,Subset.antisymm (fk k e l v _ (ds e c)) (SS.2 j),c,fun w g i=>Nat.find_min' a ⟨g,i⟩⟩⟩
 else ⟨0,fun h=>AB h d⟩
 choose b q using h;exact⟨b,q⟩
lemma bD {b:Fv n} (a:cU n D b):aM n D b:=fun v c=>⟨(a v c).1,(a v c).2.1⟩
lemma dK (a:bJ G) (c:au n D) (d:U G H D):∃ b:Fv n,aM n D b:=let ⟨b,h⟩:=b_ a c d;⟨b,bD h⟩
lemma aN {v:Fin n}:v∈aa n D<->v∉al n D:=by simp[aa]
lemma iF (a:au n D) {v:Fin n} (b:v∈aa n D) {w:ℕ} (c:v∈ag n D w):bz n D v.val w:=fy a v w c fun u _ d=>fG.1 b u d
lemma jh (c:bJ G) (a:au n D) (d:U G H D) {v:Fin n} (e:v∈aa n D) {w:ℕ} (b:v∈ag n D w):ag n D w={v}:=Subset.antisymm (fk c a d v w (ds a (iF a e b))) (SS.2 b)
lemma b7 {v:Fin n} {w:ℕ}:w∈ao n D {v}<->v∈ag n D w:=⟨fun h=>by obtain⟨-,u,a⟩:=_mf.1 h;rw[_mn,_ms] at a;exact a.2▸a.1,fun h=>_mf.2 ⟨MR.2 (cP h),v,_mn.2 ⟨h,_mss v⟩⟩⟩
lemma df {v:Fin n} {e:Ed}:e∈aE n D (ao n D {v})<->e.1<D.length/\v∈ag n D (aw D e)/\v∉ag n D (n+e.1):=by simp only[aE,eK,_mf,MP,MR,_mv,and_true,b7]
lemma kG {v:Fin n} (a:v∈aa n D):bn D (ao n D {v})=0:=sum_eq_zero fun w b=>by have:=fG.1 a w (b7.1 b);omega
lemma _0.eq (I:bJ G) (y:au n D) (B:U G H D) {u v:Fin n} (C:G u v):∃ j,j<D.length/\cR D j=true/\val D (b4 u v) (n+j)=true/\u∉ag n D (n+j)/\v∉ag n D (n+j)/\∃ s:_d,u∈ag n D (aw D (j,s))/\v∉ag n D (aw D (j,s))/\v∈ag n D (aw D (j,!s))/\u∉ag n D (aw D (j,!s)):=by
 classical
 let f:=ag n D;have g:∃ w,val D (b4 u v) w=true/\u∉f w/\v∉f w:=⟨bH n D,B.2.2.1 _ ⟨u,v,C,by simp[b4],by simp[b4]⟩,by simp[f,cs I B],by simp[f,cs I B]⟩
 obtain⟨b,c,d⟩:=Nat.find_spec g;have e:∀ a,a<Nat.find g->val D (b4 u v) a=true->u∈f a\/v∈f a:=fun a z E=>by by_contra l;rw[not_or] at l;exact Nat.find_min g z ⟨E,l.1,l.2⟩
 generalize Nat.find g=w at b c d e
 have J:w<n+D.length:=by {by_contra l;rw[fs D _ w (by omega)] at b;exact _fnt b}
 have L:n<=w:=by {by_contra l;have k:w<n:=by {omega};rw[bY D _ w k] at b;rw[show f w={⟨w,k⟩} from dr D ⟨w,k⟩,_ms] at c d;simp only[b4,BO,DE] at b;rcases b with h|h;{exact c h.symm};{exact d h.symm}}
 obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have m:j<D.length:=by {omega};obtain⟨z,F,-⟩:=y j m;have p:=b;rw[cS y _ j m] at b
 cases A:cR D j
 · exfalso;rw[show f (n+j)=f (cj D j)∪f (ck D j) from de y m A,_mu,not_or] at c d;rw[A,gop_false,BO] at b
   rcases b with h|h;{rcases e _ z h with h|h;{exact c.1 h};{exact d.1 h}};{rcases e _ F h with h|h;{exact c.2 h};{exact d.2 h}}
 · rw[A,gop_true,BA] at b;refine⟨j,m,A,p,c,d,?_⟩;rw[show f (n+j)=f (cj D j)∩f (ck D j) from cB y m A,_mn,not_and] at c d
   rcases e _ z b.1 with q|q;{have r:=c q;have t:=(e _ F b.2).resolve_left r;exact⟨false,q,fun h=>d h t,t,r⟩};{have r:=d q;have x:=(e _ F b.2).resolve_right r;exact⟨true,x,r,q,fun h=>c h x⟩}
lemma ci (r:bJ G) (h:ai n D) (t:U G H D) {v:Fin n} (B:v∈aa n D):∃ e:Ed,e.1<D.length/\cR D e.1=true/\ag n D (aw D e)={v}/\ag n D (n+e.1)=∅/\(∀ a,G v a->a∈ag n D (aw D (e.1,!e.2)))/\aE n D (ao n D {v})={e}/\aW n D (ao n D {v})=∅:=by
 have u:=h.1;have w:=co h {v} (by rw[cs r t];simp);rw[kG B,_cs] at w
 have b:∀ a,G v a->∃ j s,j<D.length/\cR D j=true/\(j,s)∈aE n D (ao n D {v})/\a∈ag n D (aw D (j,!s)):=fun a d=>by obtain⟨j,C,F,-,y,-,s,I,-,J,-⟩:=eq r u t d;exact⟨j,s,C,F,df.2 ⟨C,I,y⟩,J⟩
 obtain⟨q,z,-⟩:=r.2.2.2 v v;obtain⟨j,s,i,k,f,-⟩:=b q z
 have l:aW n D (ao n D {v})=∅:=C0.1 (by have:=_cp.2 ⟨_,f⟩;omega)
 obtain⟨e,m⟩:=_c1.1 (show (aE n D (ao n D {v})).card=1 by have:=_cp.2 ⟨_,f⟩;omega)
 rw[m,_ms] at f;subst f;have p:=df.1 (m▸_mss _);have c:=jh r u t B p.2.1
 refine⟨(j,s),i,k,c,EE fun x E=>p.2.2 ((_ms.1 (c▸cr u i k s E))▸E),fun a d=>?_,m,l⟩
 obtain⟨x,y,-,-,A,K⟩:=b a d;rw[m,_ms,Prod.mk.injEq] at A;obtain⟨rfl,rfl⟩:=A;exact K
lemma fu (b:bJ G) (h:ai n D) (c:U G H D) {u v:Fin n} (d:G u v):u∈al n D\/v∈al n D:=by
 by_contra e;rw[not_or] at e;obtain⟨x,-,-,-,-,f,g,-⟩:=ci b h c (aN.2 e.1);obtain⟨y,-,-,i,-,-,k,-⟩:=ci b h c (aN.2 e.2)
 obtain⟨j,r,-,-,l,m,s,o,-,z,-⟩:=eq b h.1 c d
 have t:=(df.2 ⟨r,o,l⟩:((j,s):Ed)∈aE n D (ao n D {u}));have w:=(df.2 ⟨r,z,m⟩:((j,!s):Ed)∈aE n D (ao n D {v}))
 rw[g,_ms] at t;rw[k,_ms] at w;subst t;subst w;obtain⟨a,p,q⟩:=b.2.2.2 u v;exact q (_ms.1 (i▸f a p))
lemma _0.gO (I:bJ G) (g:au n D) (E:U G H D) (A:Fn n) (v:val D (bM A) (bH n D)=false) (x:Fin n) (y:∃ a∈A,G x a):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s))/\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) A:=by
 by_contra i;let z:=bM A;let o:=bB x z
 have c:∀ j s,j<D.length->cR D j=true->x∈ag n D (aw D (j,s))->x∉ag n D (n+j)->val D z (aw D (j,s))=true/\val D o (aw D (j,s))=true:=fun j s d h e f=>by obtain⟨a,l,m⟩:=not_disjoint_iff.1 fun J=>i ⟨j,s,d,h,e,f,J⟩;exact⟨cO g l (by simp[z,bM,m]),cO g l (by simp[o,z,bB,bM,m])⟩
 have B:∀ w,x∉ag n D w->val D z w=val D o w:=fun w=>w.strong_induction_on fun w q f=>by
  by_cases u:w<n;{rw[bY D _ w u,bY D _ w u];rw[dr D ⟨w,u⟩,_ms] at f;exact dd x _ _ fun L=>f L.symm}
  by_cases M:w<n+D.length
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have d:j<D.length:=by {omega};obtain⟨p,C,-⟩:=g j d
    rw[cS g _ j d,cS g _ j d];cases h:cR D j
    · rw[de g d h,_mu,not_or] at f;rw[q _ p f.1,q _ C f.2]
    · have k:=f;rw[cB g d h,_mn,not_and] at k
      by_cases b:x∈ag n D (cj D j);{have e:=c j false d h b f;rw[aX] at e;rw[q _ C (k b),e.1,e.2]}
      by_cases r:x∈ag n D (ck D j);{have e:=c j true d h r f;rw[bh] at e;rw[q _ p b,e.1,e.2]};rw[q _ p b,q _ C r]
  · rw[fs D _ w (by omega),fs D _ w (by omega)]
 obtain⟨a,p,b⟩:=y;have F:=E.2.2.1 o ⟨x,a,b,dm x _,by simp[o,z,bB,bM,p]⟩;rw[<-B (bH n D) (by rw[cs I E];exact NM x),v] at F;exact _fnt F
lemma fm (f:bJ G) (g:au n D) (e:U G H D) (A:Fn n) (h:∀ a∈A,∀ b∈A,¬ H a b) (x:Fin n) (d:∃ a∈A,G x a):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s))/\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) A:=gO f g e A (by by_contra c;rw[_nf] at c;obtain⟨a,b,q,u,v⟩:=e.2.2.2.1 _ c;simp only[bM,DE] at u v;exact h a u b v q) x d
lemma _0.gP (f:bJ G) (g:au n D) (e:U G H D) {a z x:Fin n} (c:¬ G a z) (d:G x z):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s))/\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) {a,z}:=gO f g e {a,z} (by rw[show bM ({a,z}:Fn n)=b4 a z by ext i;simp[bM,b4]];exact e.2.2.2.2 a z c) x ⟨z,by simp,d⟩
lemma ew (q:au n D) (T M:Fn n) (G:2<=M.card) (w:ℕ) (z:ag n D w∩T=M):∃ j,j<D.length/\n+j<=w/\ag n D (n+j)∩T=M/\j∈aW n D (ao n D T)/\(∀ u,u<n+j->ag n D u∩T≠M)/\((cR D j=true/\M⊂ag n D (cj D j)∩T/\M⊂ag n D (ck D j)∩T)\/(cR D j=false/\ag n D (cj D j)∩T⊂M/\ag n D (ck D j)∩T⊂M/\(ag n D (cj D j)∩T)∪(ag n D (ck D j)∩T)=M/\(ag n D (cj D j)∩T).Nonempty/\(ag n D (ck D j)∩T).Nonempty)):=by
 classical
 let F u:=ag n D u∩T;have d:∃ u,F u=M:=⟨w,z⟩;have r:Nat.find d<=w:=Nat.find_min' d z;have c:∀ u,u<Nat.find d->F u≠M:=fun u y=>Nat.find_min d y;have a:=Nat.find_spec d
 generalize Nat.find d=f at r c a;have e:M.Nonempty:=_cp.1 (by omega);have g:∀ {u:ℕ},(F u).Nonempty->u∈ao n D T:=fun ⟨v,b⟩=>_mf.2 ⟨MR.2 (cP (_mn.1 b).1),v,b⟩
 have A:f<n+D.length:=by {obtain⟨v,b⟩:=e;rw[<-a] at b;exact cP (_mn.1 b).1}
 have B:n<=f:=by {by_contra H;have C:=dr (n:=n) D ⟨f,by omega⟩;have:M.card<=1:=by {rw[<-a];exact(_cl IL).trans (by simp[C])};omega}
 obtain⟨j,rfl⟩:∃ j,f=n+j:=⟨f-n,by omega⟩;have k:j<D.length:=by {omega};obtain⟨E,J,-⟩:=q j k;have h:=c _ E;have i:=c _ J
 cases x:cR D j
 · have o:F (cj D j)∪F (ck D j)=M:=by simpa only[F,de q k x,union_inter_distrib_right] using a
   have u:(F (cj D j)).Nonempty:=NN.2 fun l=>i (by rwa[l,empty_union] at o)
   have v:(F (ck D j)).Nonempty:=NN.2 fun l=>h (by rwa[l,union_empty] at o)
   exact⟨j,k,r,a,_mf.2 ⟨MR.2 k,g (a.symm▸e),g u,g v⟩,c,.inr ⟨x,SN.2 ⟨o▸subset_union_left,h⟩,SN.2 ⟨o▸subset_union_right,i⟩,o,u,v⟩⟩
 · have u:M⊆F (cj D j):=fun v b=>by rw[<-a] at b;simp only[F,cB q k x,_mn] at b⊢;exact⟨b.1.1,b.2⟩
   have v:M⊆F (ck D j):=fun v b=>by rw[<-a] at b;simp only[F,cB q k x,_mn] at b⊢;exact⟨b.1.2,b.2⟩
   exact⟨j,k,r,a,_mf.2 ⟨MR.2 k,g (a.symm▸e),g (e.mono u),g (e.mono v)⟩,c,.inl ⟨x,SN.2 ⟨u,Ne.symm h⟩,SN.2 ⟨v,Ne.symm i⟩⟩⟩
end SemCore
def af (n:ℕ) (D:Dag) (x:Fin n):Finset (ℕ×_d):=aE n D (ao n D {x})
def am (e:ℕ×_d):ℕ×_d:=(e.1,!e.2)
section SemCodes
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma ak {x:Fin n} {e:Ed}:e∈af n D x<->e.1<D.length/\x∈ag n D (aw D e)/\x∉ag n D (n+e.1):=df
lemma aB (e:Ed):am (am e)=e:=by simp[am]
lemma ka {e f:Ed} (h:e.1=f.1):f=e\/f=am e:=by obtain⟨j,s⟩:=e;obtain⟨k,t⟩:=f;subst h;cases s <;> cases t <;> simp[am]
lemma cY (c:au n D) {x:Fin n} {e:Ed} (d:e∈af n D x):cR D e.1=true:=by obtain⟨f,a,g⟩:=ak.1 d;by_contra b;rw[Bnt] at b;apply g;rw[de c f b,_mu];obtain⟨j,s⟩:=e;cases s;{exact .inl a};{exact .inr a}
lemma m9 (a:bJ G) (h:ai n D) (b:U G H D) (x:Fin n):(af n D x).card+(aW n D (ao n D {x})).card=1+bn D (ao n D {x}):=by have c:=co h {x} (by rw[cs a b];simp);rwa[_cs] at c
lemma cg (g:bJ G) (h:au n D) (i:U G H D) {x y:Fin n} (b:G x y):∃ e,e∈af n D x/\am e∈af n D y/\y∉ag n D (aw D e)/\x∉ag n D (aw D (am e))/\val D (b4 x y) (n+e.1)=true:=by obtain⟨j,f,-,a,c,d,s,k,l,m,p⟩:=eq g h i b;exact⟨(j,s),ak.2 ⟨f,k,c⟩,ak.2 ⟨f,m,d⟩,l,p,a⟩
lemma jJ (r:bJ G) (t:au n D) (m:U G H D) {x a b y:Fin n} (i:¬ H a b) (p:G x y) (k:¬ H y a) (l:¬ H y b):∃ e,e∈af n D x/\a∉ag n D (aw D e)/\b∉ag n D (aw D e):=by
 have w:∀ u∈({a,b,y}:Fn n),∀ v∈({a,b,y}:Fn n),¬ H u v:=fun u f v g=>by simp only[_mi,_ms] at f g;have c:=m.1.1;have d:=m.1.2.1;rcases f with rfl|rfl|rfl <;> rcases g with rfl|rfl|rfl <;> first | exact d _ | exact i | exact k | exact l | exact fun h=>i (c _ _ h) | exact fun h=>k (c _ _ h) | exact fun h=>l (c _ _ h)
 obtain⟨j,s,z,-,A,B,q⟩:=fm r t m {a,b,y} w x ⟨y,by simp,p⟩;exact⟨(j,s),ak.2 ⟨z,A,B⟩,fun h=>_dl.1 q h (by simp),fun h=>_dl.1 q h (by simp)⟩
lemma kb (f:bJ G) (g:au n D) (i:U G H D) {x a:Fin n} (b:x≠a):∃ e,e∈af n D x/\a∉ag n D (aw D e):=by obtain⟨z,c,d⟩:=f.2.2.1 x a b;obtain⟨j,s,k,-,l,m,p⟩:=gP f g i d c;exact⟨(j,s),ak.2 ⟨k,l,m⟩,fun h=>_dl.1 p h (by simp)⟩
end SemCodes
section
open _0
lemma gq {α:Type} {R:α->α->Prop} (e:∀ a b c,R a c->R b c->a=b) {u v c:α} (m:RT R u c) (l:RT R v c):RT R u v\/RT R v u:=by induction m with | refl=>exact .inr l | tail i f q=>rcases RTct l with h|⟨b,d,g⟩;{exact .inl (h▸i.tail f)};{rw[e _ _ _ g f] at d;exact q d}
end
section SemArms
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma dL (g:au n D) {x:Fin n} (h:aW n D (ao n D {x})=∅) {j:ℕ} (c:j<D.length) (b:x∈ag n D (n+j)):cR D j=false/\¬(x∈ag n D (cj D j)/\x∈ag n D (ck D j)):=by
 have a:¬(x∈ag n D (cj D j)/\x∈ag n D (ck D j)):=fun d=>by have e:j∈aW n D (ao n D {x}):=_mf.2 ⟨MR.2 c,b7.2 b,b7.2 d.1,b7.2 d.2⟩;rw[h] at e;exact NM _ e
 exact⟨by by_contra f;rw[_nf] at f;rw[cB g c f,_mn] at b;exact a b,a⟩
lemma ez (c:bJ G) (h:ai n D) (d:U G H D) (b:Fv n) (e:aM n D b) (x:Fin n):(af n D x).card+(aW n D (ao n D {x})).card=1+(({x}:Fn n)∩al n D).card+((aj n D b).filter (fun u=>x∈ag n D u.1)).card:=by
 have:=m9 c h d x;have f:=d9 h.1 b e {x};rw[show (aj n D b).filter (fun u=>(ag n D u.1∩{x}).Nonempty)=(aj n D b).filter (fun u=>x∈ag n D u.1) from filter_congr fun u _=>⟨fun ⟨y,a⟩=>by rw[_mn,_ms] at a;exact a.2▸a.1,fun i=>⟨x,_mn.2 ⟨i,_mss x⟩⟩⟩] at f;omega
lemma _0.kP (Y:bJ G) (h:ai n D) (Z:U G H D) (X:Fn n) (N:X.Nonempty) (K:∀ x∈X,aW n D (ao n D {x})=∅) {r:ℕ} (R:∀ x∈X,x∈ag n D r) (T:2<=aF D r):∃ P Q:Ed,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=by
 classical
 obtain⟨x,z⟩:=N;let g:=ag n D;let Q:=(range (n+D.length)).filter fun w=>∀ y∈X,y∈g w
 have c:∀ {w},w∈Q<->∀ y∈X,y∈g w:=fun {w}=>⟨fun a=>(_mf.1 a).2,fun a=>_mf.2 ⟨MR.2 (cP (a x z)),a⟩⟩
 have m:Q⊆cD n D:=fun w a=>by rw[c] at a;have:=cP (a x z);rw[bP];by_contra e;have u:=a x z;rw[show w=bH n D by unfold bH;omega,show g (bH n D)=∅ from cs Y Z] at u;exact NM x u
 have p:r∈Q:=c.2 R;have F:=ro h Q m
 have M:aW n D Q=∅:=EE fun j b=>by rw[aW,_mf,MR] at b;have e:j∈aW n D (ao n D {x}):=_mf.2 ⟨MR.2 b.1,b7.2 (c.1 b.2.1 x z),b7.2 (c.1 b.2.2.1 x z),b7.2 (c.1 b.2.2.2 x z)⟩;rw[K x z] at e;exact NM j e
 have P:1<=(Q.filter fun w=>w<n\/(cj D (w-n)∉Q/\ck D (w-n)∉Q)).card:=by
  have U:=min'_mem Q ⟨r,p⟩;refine _cp.2 ⟨_,_mf.2 ⟨U,?_⟩⟩;by_cases q:Q.min' ⟨r,p⟩<n;{exact .inl q}
  have:=cP (c.1 U x z);have:=h.1 (Q.min' ⟨r,p⟩-n) (by omega);exact .inr ⟨fun e=>by have:=min'_le Q _ e;omega,fun e=>by have:=min'_le Q _ e;omega⟩
 have:1<=bn D Q:=le_trans (by omega) (SL (f:=fun w=>aF D w-1) (fun _ _=>Zl _) p);rw[M,_ce] at F;obtain⟨i,q,k,s,d⟩:=O1.1 (by omega:1<(aE n D Q).card)
 have a:∀ e∈aE n D Q,∀ y∈X,e∈af n D y:=fun e w y o=>by
  simp only[aE,eK,_mf,MP,MR,_mv,and_true,c] at w;obtain⟨b,v,l⟩:=w
  refine ak.2 ⟨b,v y o,fun u=>l fun t f=>?_⟩;rw[show g (n+e.1)=g (cj D e.1)∪g (ck D e.1) from de h.1 b (dL h.1 (K y o) b u).1,_mu];obtain⟨j,B⟩:=e;cases B;{exact .inl (v t f)};{exact .inr (v t f)}
 refine⟨i,k,fun e=>?_,fun y o=>⟨a i q y o,a k s y o⟩⟩
 rcases ka e with f|f;{exact d f.symm};obtain⟨b,v,w⟩:=ak.1 (a i q x z);have L:=(ak.1 (a k s x z)).2.1;rw[f] at L;apply w;rw[cB h.1 b (cY h.1 (a i q x z)),_mn];obtain⟨j,B⟩:=i;cases B;{exact⟨v,L⟩};{exact⟨L,v⟩}
lemma pi (z:bJ G) (h:ai n D) (A:U G H D) (b:Fv n) (_:cU n D b) {c:Sg} (r:c∈aj n D b) (X:Fn n) (B:X.Nonempty) (a:∀ x∈X,aW n D (ao n D {x})=∅/\x∈ag n D c.1/\∀ u∈aj n D b,x∈ag n D u.1->u=c):∃ P Q:Ed,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=kP z h A X B (fun x i=>(a x i).1) (fun x i=>(a x i).2.1) (by have:=(dW.1 (_mf.1 (_md.1 r).1).1).2;omega)
lemma fW (s:bJ G) (h:ai n D) (t:U G H D) (b:Fv n) (u:cU n D b) (C:bd n D=(al n D).card+1) (X:Fn n) (F:X.Nonempty) (c:∀ x∈X,3<=(af n D x).card):∃ P Q:Ed,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=by
 have e:=bD u;obtain⟨w,a⟩:=_c1.1 (show (aj n D b).card=1 by have:=bS h.1 b e;omega)
 refine pi s h t b u (a.symm▸_mss _) X F fun x k=>?_
 have g:=ez s h t b e x;have:(({x}:Fn n)∩al n D).card<=1:=(_cl IL).trans (by simp)
 have l:=_cfl (aj n D b) (fun u=>x∈ag n D u.1);rw[a,_cs] at l;have:=c x k
 have o:0<((aj n D b).filter (fun u=>x∈ag n D u.1)).card:=by {omega};rw[a] at o g;obtain⟨v,p⟩:=_cp.1 o
 rw[_mf,_ms] at p;exact⟨C0.1 (by omega),p.1▸p.2,fun y z _=>_ms.1 (a▸z)⟩
end SemArms
section SemPaths
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma gn (a:Fin n):bM ({a}:Fn n)=cl a:=funext fun _=>by simp[bM,cl]
lemma dz (a:au n D) (x:Fd n) {j:ℕ} (b:j<D.length) (s:_d):val D x (n+j)=kF (cR D j) (val D x (aw D (j,s))) (val D x (aw D (j,!s))):=by rw[cS a x j b];cases s;{simp[aw]};{cases cR D j <;> simp[aw,Bool.and_comm,Bool.or_comm]}
lemma _0.iG (f:bJ G) {i:Fin n} {S:Fn n} (h:cN G (bB i (bM S))):(∃ a∈S,G i a)\/∃ a∈S,∃ b∈S,G a b:=by obtain⟨u,v,c,d,e⟩:=h;simp only[bB,bM,BO,DE] at d e;rcases d with rfl|d <;> rcases e with rfl|e;{exact AB c (f.2.1 _)};{exact .inl ⟨v,e,c⟩};{exact .inl ⟨u,d,f.1 _ _ c⟩};{exact .inr ⟨u,d,v,e,c⟩}
lemma _0.mH (j:au n D) {a c q:ℕ} (k:bz n D a c) (f:RT (bk n D) a q):RT (bk n D) c q\/(bz n D q c/\q≠c):=by revert f;induction k using RThi with | refl=>exact fun f=>.inl f | @head a e b d u=>intro f;rcases RTch f with rfl|⟨w,l,v⟩;{have:=b.1.2.1;have:=j (e-n) (by have:=b.1.1;omega);have:=dt j (fun _ _ h=>h.1) d;exact .inr ⟨RTh b d,by rcases b.1.2.2 with z|z <;> omega⟩};{obtain rfl:e=w:=dS b.1 l b.2;exact u v}
lemma gR (d:au n D) (v:Fin n) {j:ℕ} (g:j<D.length) (s:_d) (l:bz n D v.val (aw D (j,!s))) (u:aF D (aw D (j,!s))=1) (x y:Fd n) (m:∀ k,k≠v->x k=y k):val D x (aw D (j,s))=val D y (aw D (j,s)):=by
 by_contra p;have w:=eG (fun _ _ h=>h.1) (d_ d x y v m _ p)
 have b:bk n D (aw D (j,!s)) (n+j):=cM g (!s);have c:bk n D (aw D (j,s)) (n+j):=cM g s;have:=dh d g s;have:=dh d g (!s)
 rcases mH d l w with q|⟨q,z⟩
 · rcases RTch q with e|⟨t,i,a⟩;{have k:=(d j g).2.2;cases s <;> {simp[aw] at e;exact AB e.symm (by first | exact k | exact k.symm)}};{obtain rfl:t=n+j:=(dS b i u).symm;have:=dt d (fun _ _ h=>h) a;omega}
 · rcases RTch q with e|⟨t,i,a⟩;{exact z e};obtain rfl:t=n+j:=(dS c i.1 i.2).symm;have:=dt d (fun _ _ h=>h.1) a;omega
lemma _0.kd (g:au n D) (h:U G H D) (x:Fd n) (v:Fin n) (b:ℕ) (c:j_ n D b v.val) (i:¬ cN H x) (j:cN G (bB v x)):val D x b=false/\val D (bB v x) b=true:=by
 have d:val D x b≠val D (bB v x) b:=fun e=>i (h.2.2.2.1 x ((mw g x _ v (dd v x) b c e).symm▸h.2.2.1 _ j));have a:=gJ g x (bB v x) (iE v x) b
 cases f:val D x b;{cases l:val D (bB v x) b;{exact AB (f.trans l.symm) d};{exact⟨rfl,rfl⟩}};{exact AB (f.trans (a f).symm) d}
lemma _0.bv (l:au n D) {i a:Fin n} {j w:ℕ} {s:_d} (f:j<D.length) (k:cR D j=true) (h:n+j<=w) (p:bz n D i.val (aw D (j,!s))) (J:aF D (aw D (j,!s))=1) (y:val D (bB i (cl a)) w=true) (z:val D (cl a) w=false):a∈ag n D (aw D (j,s)):=by
 have t:val D (bB i (cl a)) (n+j)=true:=by by_contra b;rw[Bnt] at b;have u:val D (cl a) (n+j)=false:=by {by_contra c;rw[_nf] at c;rw[gJ l _ _ (iE i _) _ c] at b;exact _fnt b.symm};have K:=kc l _ _ i (dd i (cl a)) (n+j) w (iH l (p.tail ⟨cM f (!s),J⟩) h) (u.trans b.symm);rw[y,z] at K;exact _fnt K
 rw[dz l _ f s,k,gop_true,BA] at t;exact ee.2 (t.1▸gR l i f s p J _ _ (dd i (cl a)))
lemma kQ (l:au n D) (i:Fin n) (w:ℕ) (f:bz n D i.val w) (d:Fn n) (m:∀ S:Fn n,S⊆d->(∀ a∈S,¬ G i a)->val D (bB i (bM S)) w=false) (k:∀ a∈d,G i a->val D (bB i (bM {a})) w=true/\val D (bM {a}) w=false):∃ j s,j<D.length/\cR D j=true/\n+j<=w/\bz n D i.val (aw D (j,!s))/\∀ a∈d,(a∈ag n D (aw D (j,s))<->G i a):=by
 classical
 let Q:=d.filter (fun a=>G i a);let x:=bM (d\Q);let y:=bB i x
 have M:val D y w=false:=m _ sdiff_subset fun a b e=>by rw[_md,_mf] at b;exact b.2 ⟨b.1,e⟩
 have R:∀ c,bz n D i.val c->val D y c=true\/∃ j s,j<D.length/\cR D j=true/\n+j<=c/\bz n D i.val (aw D (j,!s))/\aF D (aw D (j,!s))=1/\val D x (aw D (j,s))=false:=fun c h=>by
  induction h with
  | refl=>exact .inl (by rw[bY D _ _ i.isLt];exact dm i _)
  | tail z u q=>
   obtain⟨j,s,a,rfl,rfl⟩:=fj.1 u.1;have:=dh l a s
   rcases q with p|⟨j',s',a',k',h,p',J',T'⟩
   · cases o:cR D j;{exact .inl (by rw[dz l _ a s,o,gop_false,p];rfl)}
     by_cases I:val D y (aw D (j,!s))=true;{exact .inl (by rw[dz l _ a s,o,gop_true,p,I];rfl)}
     exact .inr ⟨j,!s,a,o,le_refl _,by rw[Bool.not_not];exact z,by rw[Bool.not_not];exact u.2,by by_contra b;rw[_nf] at b;exact I (gJ l _ _ (iE i _) _ b)⟩
   · exact .inr ⟨j',s',a',k',by omega,p',J',T'⟩
 rcases R w f with p|⟨j,s,a,o,h,p,J,T⟩;{exact AB (M▸p) _fnt}
 exact⟨j,s,a,o,h,p,fun u v=>⟨fun q=>by by_contra r;have:=cO l q (x:=x) (by simp[x,bM,Q,v,r]);rw[T] at this;exact _fnt this,fun q=>bv l a o h p J (gn u▸(k u v q).1) (gn u▸(k u v q).2)⟩⟩
lemma eM (g:bJ G) (d:au n D) (h:U G H D) {i:Fin n} (j:i∈aa n D) {b:ℕ} (c:bz n D i.val b) (k:2<=aF D b):ag n D b=∅:=EE fun x e=>by have:=_ms.1 (fk g d h i b (ds d c) e);have:=fG.1 j b (this▸e);omega
lemma jK {a t:ℕ} (f:RT (bk n D) a t):bz n D a t\/∃ b,bz n D a b/\2<=aF D b:=by induction f using RThi with | refl=>exact .inl .refl | @head a c e _ q=>by_cases u:aF D a=1;{rcases q with d|⟨b,d,g⟩;{exact .inl (RTh ⟨e,u⟩ d)};{exact .inr ⟨b,RTh ⟨e,u⟩ d,g⟩}};{have:=ef e;exact .inr ⟨a,.refl,by omega⟩}
lemma iI (e:bJ G) (h:ai n D) (f:U G H D) {i:Fin n} (g:i∈aa n D):bz n D i.val (bH n D)\/∃ b,bz n D i.val b/\2<=aF D b/\ag n D b=∅:=(jK (iD h i.val (by have:=i.isLt;omega))).imp_right fun ⟨b,a,d⟩=>⟨b,a,d,eM e h.1 f g a d⟩
lemma _0.ke (a:au n D) {b:ℕ} (d:2<=aF D b) (c:ag n D b=∅):b∈(cD n D).filter (fun w=>¬(ag n D w).Nonempty):=_mf.2 ⟨bP.2 (dc a (w:=b) (by omega)),by rw[c];exact NE⟩
lemma fJ (d:au n D) (c:bL n D=0) {b:ℕ} (e:2<=aF D b):(ag n D b).Nonempty:=by by_contra a;have:=SL (f:=fun w=>aF D w-1) (fun _ _=>Zl _) (ke d e (N0.1 a));unfold bL bn at c;omega
lemma gr (f:bJ G) (h:ai n D) (g:U G H D) (a:bL n D=0) {i:Fin n} (j:i∈aa n D) {w:ℕ} (k:RT (bk n D) i.val w):bz n D i.val w:=(jK k).resolve_right fun ⟨_,c,d⟩=>NE ((eM f h.1 g j c d)▸fJ h.1 a d)
lemma jL (_:bJ G) (t:au n D) (g:U G H D) (h:Fn n) (l:∀ a∈h,∀ b∈h,¬ H a b) {i:Fin n} (m:∀ a∈h,H i a->G i a) (p:bz n D i.val (bH n D)):∃ j s,j<D.length/\cR D j=true/\bz n D i.val (aw D (j,!s))/\∀ a∈h,(a∈ag n D (aw D (j,s))<->G i a):=by
 obtain⟨j,s,u,v,-,c,d⟩:=kQ (G:=G) t i (bH n D) p h (fun S e q=>by by_contra c;rw[_nf] at c;rcases iG g.1 (g.2.2.2.1 _ c) with ⟨a,k,f⟩|⟨a,k,b,w,r⟩;{exact q a k (m a (e k) f)};{exact l a (e k) b (e w) r}) (fun a _ f=>⟨g.2.2.1 _ ⟨i,a,f,dm i _,by simp[bB,bM]⟩,by by_contra c;rw[_nf,gn] at c;exact dF g.1 a (g.2.2.2.1 _ c)⟩)
 exact⟨j,s,u,v,c,d⟩
lemma iJ (_:bJ G) (h:au n D) (q:U G H D) (d:Fn n) (u:∀ a∈d,∀ b∈d,¬ H a b) {i j:Fin n} {w:ℕ} (v:∀ a∈d,H i a->G i a) (l:bz n D i.val w) (x:j_ n D w j.val) (e:∃ a∈d,G j a/\¬ G i a):∃ k s,k<D.length/\cR D k=true/\n+k<=w/\bz n D i.val (aw D (k,!s))/\∀ a∈d,(a∈ag n D (aw D (k,s))<->G i a):=by
 classical
 let F:=d.filter (fun a=>¬ G i a);have y:¬ cN H (bB i (bM F)):=fun r=>by rcases iG q.1 r with ⟨a,t,f⟩|⟨a,t,b,J,z⟩;{exact(_mf.1 t).2 (v a (_mf.1 t).1 f)};{exact u a (_mf.1 t).1 b (_mf.1 J).1 z}
 obtain⟨a,A,m,p⟩:=e;have C:=(kd h q _ j w x y ⟨j,a,m,dm j _,by simp[bB,bM,F,A,p]⟩).1
 refine kQ h i w l d (fun S E K=>by by_contra r;rw[_nf] at r;rw[gJ h _ _ (fun k g=>by simp only[bB,bM,BO,DE] at g⊢;exact g.imp_right fun g=>_mf.2 ⟨E g,K k g⟩) w r] at C;exact _fnt C.symm) fun a _ f=>?_
 have I:=kd h q (bM {a}) i w (ds h l) (by rw[gn];exact dF q.1 a) ⟨i,a,f,dm i _,by simp[bB,bM]⟩;exact⟨I.2,I.1⟩
end SemPaths
section SemDiff
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma f_ {x y:Fin n} {w:ℕ}:w∈aR n D x y<->x∈ag n D w/\y∉ag n D w:=⟨fun h=>(_mf.1 h).2,fun h=>_mf.2 ⟨MR.2 (cP h.1),h⟩⟩
lemma dY {x y:Fin n} {e:Ed}:e∈aE n D (aR n D x y)<->e.1<D.length/\(x∈ag n D (aw D e)/\y∉ag n D (aw D e))/\¬(x∈ag n D (n+e.1)/\y∉ag n D (n+e.1)):=by simp only[aE,eK,_mf,MP,MR,_mv,and_true,f_]
lemma iK (m:au n D) (b:Fv n) (i:aM n D b) {x y:Fin n} (j:x≠y) (k:x∈al n D):bn D (aR n D x y)=1+((aj n D b).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1)).card:=by rw[aR,bnF m b i _ fun _ c=>⟨x,c.1⟩,show (al n D).filter (fun v=>x∈ag n D (b v)/\y∉ag n D (b v))={x} by ext v;simp only[_mf,_ms];exact⟨fun ⟨a,c,_⟩=>(_ms.1 ((i v a).2▸c)).symm,fun h=>by rw[h,(i x k).2];exact⟨k,_mss x,fun c=>j (_ms.1 c).symm⟩⟩,_cs]
lemma ji (v:au n D) {x y:Fin n} (z:x≠y) {w:ℕ} (A:x∈ag n D w/\y∈ag n D w):∃ j s,j<D.length/\cR D j=false/\x∈ag n D (n+j)/\y∈ag n D (n+j)/\x∈ag n D (aw D (j,s))/\y∉ag n D (aw D (j,s))/\y∈ag n D (aw D (j,!s))/\x∉ag n D (aw D (j,!s)):=by
 classical
 have d:∃ u,x∈ag n D u/\y∈ag n D u:=⟨w,A⟩;obtain⟨e,g⟩:=Nat.find_spec d;have a:∀ u,u<Nat.find d->¬(x∈ag n D u/\y∈ag n D u):=fun u B=>Nat.find_min d B
 generalize Nat.find d=f at e g a;have:=cP e;have H:n<=f:=by {by_contra h;rw[dr D ⟨f,by omega⟩,_ms] at e g;exact z (e.trans g.symm)}
 obtain⟨j,rfl⟩:∃ j,f=n+j:=⟨f-n,by omega⟩;have l:j<D.length:=by {omega};obtain⟨F,G,-⟩:=v j l;have i:=a _ F;have m:=a _ G
 cases t:cR D j
 · have o:=e;have p:=g;rw[de v l t,_mu] at o p
   rcases o with q|r;{have b:y∉ag n D (cj D j):=fun h=>i ⟨q,h⟩;have c:=p.resolve_left b;exact⟨j,false,l,t,e,g,q,b,c,fun h=>m ⟨h,c⟩⟩};{have c:y∉ag n D (ck D j):=fun h=>m ⟨r,h⟩;have b:=p.resolve_right c;exact⟨j,true,l,t,e,g,r,c,b,fun h=>i ⟨h,b⟩⟩}
 · rw[cB v l t,_mn] at e g;exact AB ⟨e.1,g.1⟩ i
lemma gt (J:bJ G) (h:ai n D) (K:U G H D) (b:Fv n) (L:aM n D b) {x c z:Fin n} (f:x≠c) (M:x∈al n D) (g:∀ u∈aj n D b,x∈ag n D u.1->c∈ag n D u.1) {w:ℕ} (N:x∈ag n D w/\c∈ag n D w) (q:G x z) (r:¬ G c z):bn D (aR n D x c)=1/\aW n D (aR n D x c)=∅/\(aE n D (aR n D x c)).card=2/\∃ e∈aE n D (aR n D x c),cR D e.1=false/\c∈ag n D (n+e.1):=by
 have a:bn D (aR n D x c)=1:=by rw[iK h.1 b L f M,FE.2 fun u P d=>d.2 (g u P d.1),_ce]
 have t:=gN h x c f (by rw[cs J K];exact NM x);rw[a] at t
 obtain⟨j,s,v,y,A,i,o,k,-,-⟩:=ji h.1 f N;have l:(j,s)∈aE n D (aR n D x c):=dY.2 ⟨v,⟨o,k⟩,fun d=>d.2 i⟩
 obtain⟨d,u,B,-,C,m,E⟩:=gP J h.1 K r q;have F:(d,u)∈aE n D (aR n D x c):=dY.2 ⟨B,⟨C,fun e=>_dl.1 E e (by simp)⟩,fun e=>m e.1⟩
 have:2<=(aE n D (aR n D x c)).card:=O1.2 ⟨_,l,_,F,fun p=>m ((show j=d from CG Prod.fst p)▸A)⟩
 exact⟨a,C0.1 (by omega),by omega,(j,s),l,y,i⟩
end SemDiff
def aQ (n:ℕ) (D:Dag) (P M:Finset (Fin n)):Prop:=∃ w,ag n D w∩P=M
def du (n:ℕ) (D:Dag) (P:Finset (Fin n)):Finset ℕ:=(aW n D (ao n D P)).filter (fun j=>2<=(ag n D (n+j)∩P).card)
def dG (n:ℕ) (D:Dag) (P U:Finset (Fin n)) (f:Fin n) (e:ℕ×_d):Prop:=e.1<D.length/\cR D e.1=true/\f∈P/\f∈ag n D (aw D e)/\f∉ag n D (n+e.1)/\ag n D (aw D e)∩P⊆U/\(ag n D (aw D e)∩P).card<=2
def ch (n:ℕ) (D:Dag) (P:Finset (Fin n)) (e:ℕ×_d):(ℕ×_d)⊕ℕ:=if ag n D (n+e.1)∩P=∅ then Sum.inl e else Sum.inr e.1
def kf (n:ℕ) (D:Dag) (P:Finset (Fin n)) (c:(ℕ×_d)⊕ℕ):Prop:=Sum.elim (fun e=>e∈aE n D (ao n D P)/\(ag n D (aw D e)∩P).card<=2) (fun j=>j∈aW n D (ao n D P)/\(ag n D (n+j)∩P).card=1) c
def bA (n:ℕ) (G:Fin n->Fin n->Prop) (D:Dag) (pos:Fin n->ℕ×_d):Prop:=(∀ i∈aa n D,(pos i).1<D.length/\ag n D (n+(pos i).1)=∅/\(∀ a,G i a->a∈ag n D (aw D (pos i)))/\ag n D (aw D ((pos i).1,!(pos i).2))={i})/\∀ i∈aa n D,∀ i'∈aa n D,pos i=pos i'->i=i'
section
open _0
lemma bQ {n:ℕ} {G H:Gr n} {D:Dag} (j:bJ G) (h:ai n D) (k:U G H D):∃ p:Fin n->Ed,bA n G D p:=by
 classical
 have f:∀ i:Fin n,∃ e:Ed,i∈aa n D->e.1<D.length/\ag n D (n+e.1)=∅/\(∀ a,G i a->a∈ag n D (aw D e))/\ag n D (aw D (e.1,!e.2))={i}:=fun i=>if c:i∈aa n D then by obtain⟨e,d,-,l,m,p,-,-⟩:=ci j h k c;exact⟨(e.1,!e.2),fun _=>⟨d,m,p,by simpa using l⟩⟩ else ⟨(0,false),fun q=>AB q c⟩
 choose p b using f;exact⟨p,b,fun i c t r s=>by have d:=(b i c).2.2.2;rw[s,(b t r).2.2.2] at d;exact(SG d).symm⟩
end
section SupMask
open _0
variable {n:ℕ} {D:Dag}
lemma iW (P:Fn n) (w:ℕ):aQ n D P (ag n D w∩P):=⟨w,rfl⟩
lemma jw {P M:Fn n} (h:aQ n D P M):M⊆P:=let ⟨_,e⟩:=h;e▸IR
lemma cC {P:Fn n} {w:ℕ}:w∈ao n D P<->(ag n D w∩P).Nonempty:=⟨fun h=>(_mf.1 h).2,fun ⟨v,a⟩=>_mf.2 ⟨MR.2 (cP (_mn.1 a).1),v,a⟩⟩
lemma fL {T:Fn n} {e:Ed}:e∈aE n D (ao n D T)<->e.1<D.length/\(ag n D (aw D e)∩T).Nonempty/\¬(ag n D (n+e.1)∩T).Nonempty:=by simp only[aE,eK,_mf,MP,MR,_mv,and_true,cC]
lemma lp (d:au n D) {P M:Fn n} (b:2<=M.card) (h:aQ n D P M):∃ j∈du n D P,ag n D (n+j)∩P=M:=by obtain⟨w,e⟩:=h;obtain⟨j,-,-,c,a,-,-⟩:=ew d P M b w e;exact⟨j,_mf.2 ⟨a,c.symm▸b⟩,c⟩
lemma eZ (e:au n D) (P:Fn n) (F:FF n) (c:∀ M∈F,2<=M.card/\aQ n D P M):F.card<=(du n D P).card:=(_cl fun M d=>by obtain⟨j,f,b⟩:=lp e (c M d).1 (c M d).2;exact _mg.2 ⟨j,f,b⟩).trans card_image_le
lemma k5 (r:au n D) {P T:Fn n} (s:P.card<=7) (E:T.card=3) (h:aQ n D P T):(∃ A,aQ n D P A/\A.card=2/\A⊆T)\/(∃ A,aQ n D P A/\A.card=4/\T⊆A)\/(∃ A B,A≠B/\aQ n D P A/\aQ n D P B/\A.card=5/\B.card=5/\T⊆A/\T⊆B/\A∩B=T):=by
 obtain⟨w,t⟩:=h;obtain⟨j,u,-,k,-,-,g⟩:=ew r P T (by omega) w t;have a:=iW (D:=D) P (cj D j);have b:=iW (D:=D) P (ck D j)
 rcases g with ⟨x,d,e⟩|⟨-,d,e,f,-,-⟩
 · have c:(ag n D (cj D j)∩P)∩(ag n D (ck D j)∩P)=T:=by {rw[<-k,cB r u x];ext v;simp only[_mn];tauto}
   generalize ag n D (cj D j)∩P=A at a d c;generalize ag n D (ck D j)∩P=B at b e c
   have:=CL d;have i:=CL e;have:=(_cl (US (jw a) (jw b))).trans s;have:=CU A B;rw[c] at this
   by_cases y:A.card=4;{exact .inr (.inl ⟨A,a,y,d.subset⟩)};by_cases z:B.card=4;{exact .inr (.inl ⟨B,b,z,e.subset⟩)}
   exact .inr (.inr ⟨A,B,fun q=>by rw[q,inter_self] at c;rw[c] at i;omega,a,b,by omega,by omega,d.subset,e.subset,c⟩)
 · generalize ag n D (cj D j)∩P=A at a d f;generalize ag n D (ck D j)∩P=B at b e f;have:=CL d;have:=CL e;have:=UL A B;rw[f] at this
   by_cases C:A.card=2;{exact .inl ⟨A,a,C,d.subset⟩};{exact .inl ⟨B,b,by omega,e.subset⟩}
lemma lX {T S A:Fn n} (f:T.card=3) (g:S.card=3) (h:A.card=4) (d:T⊆A) (e:S⊆A) (a:T≠S->(T∩S).card<=1):T=S:=by by_contra b;have:=_cl (US d e);have:=CU T S;have:=a b;omega
lemma nS {a b c A:Fn n} (g:a.card=3) (h:b.card=3) (i:c.card=3) (j:A.card<=5) (d:a⊆A) (e:b⊆A) (f:c⊆A) (x:(a∩b).card<=1) (y:(a∩c).card<=1) (z:(b∩c).card<=1):False:=by have:=_cl (US (US d e) f);have:=CU a b;have:=CU (a∪b) c;have:((a∪b)∩c).card<=(a∩c).card+(b∩c).card:=by {rw[union_inter_distrib_right];exact UL _ _};omega
lemma jM {G H:Gr n} (r:bJ G) (t:au n D) (u:U G H D) {P U X:Fn n} (g:U⊆P) (i:U.card<=2\/(U.card=3/\¬ aQ n D P U)) (w:∀ a∈X,∀ b∈X,¬ H a b) (k:P\U⊆X) {f:Fin n} (x:f∈U) (l:∃ a∈X,G f a):∃ e,dG n D P U f e:=by
 obtain⟨j,s,y,z,A,B,C⟩:=fm r t u X w f l;have c:ag n D (aw D (j,s))∩P⊆U:=fun v m=>by rw[_mn] at m;by_contra p;exact _dl.1 C m.1 (k (_md.2 ⟨m.2,p⟩))
 refine⟨(j,s),y,z,g x,A,B,c,?_⟩;rcases i with i|⟨E,d⟩;{exact(_cl c).trans i};have:=CL (SN.2 ⟨c,fun h=>d ⟨_,h⟩⟩);omega
lemma _0.gB (c:au n D) {P U:Fn n} {f:Fin n} {e:Ed} (h:dG n D P U f e):ag n D (n+e.1)∩P⊆(ag n D (aw D e)∩P).erase f:=fun v a=>by rw[_mn] at a;exact _me.2 ⟨fun b=>h.2.2.2.2.1 (b▸a.1),_mn.2 ⟨cr c h.1 h.2.1 e.2 a.1,a.2⟩⟩
lemma jN {P U:Fn n} {f:Fin n} {e:Ed} (h:dG n D P U f e) (c:∀ M,M⊆U->M.card=2->f∈M->¬ aQ n D P M):ag n D (aw D e)∩P={f}:=by have b:=_mn.2 ⟨h.2.2.2.1,h.2.2.1⟩;have i:(ag n D (aw D e)∩P).card≠2:=fun j=>c _ h.2.2.2.2.2.1 j b (iW P _);have:=h.2.2.2.2.2.2;exact(_eqc (SS.2 b) (by rw[_cs];omega)).symm
lemma iX {P:Fn n} {e d:Ed} (h:ch n D P e=.inl d):e=d/\ag n D (n+e.1)∩P=∅:=by unfold ch at h;split_ifs at h with a;exact⟨Sum.inl.inj h,a⟩
lemma lq (i:au n D) {P U:Fn n} {f:Fin n} {e:Ed} (h:dG n D P U f e):kf n D P (ch n D P e):=by
 have b:=gB i h;obtain⟨g,l,j,s,-,-,t⟩:=h;have c:=_mn.2 ⟨s,j⟩;unfold ch;split_ifs with m
 · exact⟨_mf.2 ⟨MP.2 ⟨MR.2 g,_mv _⟩,cC.2 ⟨f,c⟩,by rw[cC,m];exact NE⟩,t⟩
 · have d:=NN.2 m;have k:=_cl b;rw[CE c] at k;have:=_cp.2 d;obtain⟨v,a⟩:=d;rw[_mn] at a
   exact⟨_mf.2 ⟨MR.2 g,cC.2 ⟨v,_mn.2 a⟩,cC.2 ⟨v,_mn.2 ⟨cr i g l false a.1,a.2⟩⟩,cC.2 ⟨v,_mn.2 ⟨cr i g l true a.1,a.2⟩⟩⟩,by omega⟩
lemma nT (v:au n D) {P:Fn n} (e:Fn n) (U:Fin n->Fn n) (a:Fin n->Ed) (b:∀ f∈e,dG n D P (U f) f (a f)) (c:Ed⊕ℕ):(e.filter (fun f=>ch n D P (a f)=c)).card<=2:=by
 let C f:=ch n D P (a f);rcases c with d|j
 · by_cases g:(e.filter (fun f=>C f=.inl d)).Nonempty;{obtain⟨f,h⟩:=g;rw[_mf] at h;have t:=(b f h.1).2.2.2.2.2.2;rw[(iX h.2).1] at t;exact le_trans (_cl fun u i=>by rw[_mf] at i;have m:=b u i.1;rw[(iX i.2).1] at m;exact _mn.2 ⟨m.2.2.2.1,m.2.2.1⟩) t};{rw[N0.1 g];simp}
 · have k:Set.InjOn (fun f=>(a f).2) (e.filter (fun f=>C f=.inr j):Set (Fin n)):=fun f i u o w=>by
    rw[mem_coe,_mf] at i o;have R:∀ {x:Ed},ch n D P x=.inr j->x.1=j/\(ag n D (n+x.1)∩P).Nonempty:=fun h=>by unfold ch at h;split_ifs at h with y;exact⟨Sum.inr.inj h,NN.2 y⟩
    obtain⟨x,p⟩:=R i.2;obtain⟨y,-⟩:=R o.2;have r:a f=a u:=Prod.ext (x.trans y.symm) w;have h:=b f i.1;have t:=b u o.1;rw[<-r] at t
    by_contra g;obtain⟨q,l⟩:=p;have s:=_me.1 (gB v h l);have m:=_me.1 (gB v t l)
    have:=_cl (show ({q,f,u}:Fn n)⊆ag n D (aw D (a f))∩P from fun z y=>by simp only[_mi,_ms] at y;rcases y with rfl|rfl|rfl;{exact s.2};{exact _mn.2 ⟨h.2.2.2.1,h.2.2.1⟩};{exact _mn.2 ⟨t.2.2.2.1,t.2.2.1⟩})
    rw[_cin (by simp[s.1,m.1]),_c2 g] at this;have:=h.2.2.2.2.2.2;omega
   simpa using card_le_card_of_injOn (t:=(univ:Finset _d)) (fun f=>(a f).2) (fun _ _=>_mv _) k
lemma _0.gc (k:au n D) {P:Fn n} (L S:Fn n) (U:Fin n->Fn n) (a:Fin n->Ed) (b:∀ f∈L,dG n D P (U f) f (a f)) (g:S⊆L) (d:∀ f∈S,ag n D (aw D (a f))∩P={f}):2*S.card+(L\S).card<=2*(L.image (fun f=>ch n D P (a f))).card:=by
 let C f:=ch n D P (a f)
 have K:∀ {f t:Fin n},f∈S->t∈L->f≠t->C f≠C t:=fun {f t} o p q e=>by
  have z:ag n D (n+(a f).1)∩P=∅:=subset_empty.1 (by have:=gB k (b f (g o));rwa[d f o,erase_singleton] at this)
  have l:C f=.inl (a f):=by {simp[C,ch,z]};rw[l] at e;have m:=(iX e.symm).1;have i:=_mn.2 ⟨(b t p).2.2.2.1,(b t p).2.2.1⟩;rw[m,d f o,_ms] at i;exact q i.symm
 have r:(S.image C).card=S.card:=_cij fun f i t o j=>by by_contra m;exact K i (g o) m j
 have u:=card_le_mul_card_image (L\S) 2 fun c _=>nT k (L\S) U a (fun f i=>b f (_md.1 i).1) c
 have s:Disjoint (S.image C) ((L\S).image C):=_dl.2 fun c p q=>by obtain⟨f,i,rfl⟩:=_mg.1 p;obtain⟨t,o,j⟩:=_mg.1 q;rw[_md] at o;exact K i o.1 (fun h=>o.2 (h▸i)) j.symm
 have t:=_cl (US (image_subset_image (f:=C) g) (image_subset_image (f:=C) (sdiff_subset (t:=S))));rw[_cud s,r] at t;dsimp only[C] at t;omega
lemma _0.lY (P:Fn n) (E:Finset Ed) (p:∀ e∈E,e∈aE n D (ao n D P)) (C:Finset (Ed⊕ℕ)) (i:∀ c∈C,kf n D P c) (d:Disjoint E C.toLeft):(du n D P).card+E.card+C.card<=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 have l:E.card+C.toLeft.card<=(aE n D (ao n D P)).card:=by {rw[<-_cud d];exact _cl fun e f=>(_mu.1 f).elim (p e) fun h=>(i _ (mem_toLeft.1 h)).1}
 have m:(du n D P).card+C.toRight.card<=(aW n D (ao n D P)).card:=by rw[<-_cud (_dl.2 fun j l m=>by have:=(_mf.1 l).2;have:=(i _ (mem_toRight.1 m)).2;omega)];exact _cl fun j g=>(_mu.1 g).elim (fun h=>(_mf.1 h).1) fun h=>(i _ (mem_toRight.1 h)).1
 have:=card_toLeft_add_card_toRight (u:=C);omega
lemma mJ (m:au n D) (P:Fn n) (E:Finset Ed) (q:∀ e∈E,e∈aE n D (ao n D P)) (L S:Fn n) (U:Fin n->Fn n) (a:Fin n->Ed) (d:∀ f∈L,dG n D P (U f) f (a f)) (j:S⊆L) (g:∀ f∈S,ag n D (aw D (a f))∩P={f}) (i:∀ e∈E,∀ f∈L,e≠a f):2*((du n D P).card+E.card)+2*S.card+(L\S).card<=2*((aE n D (ao n D P)).card+(aW n D (ao n D P)).card):=by have:=gc m L S U a d j g;have:=lY P E q (L.image fun f=>ch n D P (a f)) (fun c s=>by obtain⟨f,k,rfl⟩:=_mg.1 s;exact lq m (d f k)) (_dl.2 fun e r p=>by obtain⟨f,k,b⟩:=_mg.1 (mem_toLeft.1 p);exact i e r f k (iX b).1.symm);omega
lemma pg (P:Fn n) (E:Finset Ed) (k:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (C:Finset (Ed⊕ℕ)) (l:∀ c∈C,kf n D P c):(du n D P).card+E.card+C.card<=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=lY P E (fun e h=>(k e h).1) C l (_dl.2 fun e d f=>by have:=(k e d).2;have:=(l _ (mem_toLeft.1 f)).2;omega)
lemma pW (h:au n D) (P:Fn n) (E:Finset Ed) (i:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (L S:Fn n) (U:Fin n->Fn n) (a:Fin n->Ed) (b:∀ f∈L,dG n D P (U f) f (a f)) (g:S⊆L) (d:∀ f∈S,ag n D (aw D (a f))∩P={f}):2*((du n D P).card+E.card)+2*S.card+(L\S).card<=2*((aE n D (ao n D P)).card+(aW n D (ao n D P)).card):=by have:=gc h L S U a b g d;have:=pg P E i (L.image fun f=>ch n D P (a f)) (fun c j=>by obtain⟨f,k,rfl⟩:=_mg.1 j;exact lq h (b f k));omega
lemma kH {G H:Gr n} (x:bJ G) (h:ai n D) (y:U G H D) (P I:Fn n) (t:∀ i∈I,i∈aa n D/\∃ N:Fn n,N⊆P/\3<=N.card/\∀ a∈N,G i a):∃ E:Finset Ed,E.card=I.card/\∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card:=by
 obtain⟨p,l⟩:=bQ x h y;refine⟨I.image p,_cij fun i b j c=>l.2 i (t i b).1 j (t j c).1,fun e q=>?_⟩
 obtain⟨i,b,rfl⟩:=_mg.1 q;obtain⟨C,d,f,-⟩:=l.1 i (t i b).1;obtain⟨M,r,F,s⟩:=(t i b).2
 have:=_cl (fun a w=>_mn.2 ⟨f a (s a w),r w⟩:M⊆ag n D (aw D (p i))∩P)
 exact⟨fL.2 ⟨C,_cp.1 (by omega),by rw[d,empty_inter];exact NE⟩,by omega⟩
end SupMask
section K4Generic
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma _0.gC {p:Fin n->Ed} (b:bA n G D p) {i a:Fin n} {T:Fn n} (e:i∈aa n D) (c:G i a) (d:a∈T):p i∈aE n D (ao n D T):=by obtain⟨f,g,h,-⟩:=b.1 i e;exact fL.2 ⟨f,⟨a,_mn.2 ⟨h a c,d⟩⟩,by rw[g,empty_inter];exact NE⟩
lemma e6 {p:Fin n->Ed} (b:bA n G D p) (T J:Fn n) (c:∀ i∈J,i∈aa n D/\∃ a∈T,G i a):J.image p⊆aE n D (ao n D T)/\(J.image p).card=J.card:=⟨fun e d=>by obtain⟨i,f,rfl⟩:=_mg.1 d;obtain⟨g,a,h,j⟩:=c i f;exact gC b g j h,_cij fun i f t g d=>b.2 i (c i f).1 t (c t g).1 d⟩
lemma gS (a:bJ G) (h:ai n D) (c:U G H D) (b:Fv n) (d:aM n D b) (T:Fn n):(aE n D (ao n D T)).card+(aW n D (ao n D T)).card+(al n D).card<=2*T.card+bd n D:=by have:=co h T (by rw[cs a c,empty_inter]);have:=cZ h.1 b d T;have:=_cl (IL:T∩al n D⊆T);omega
lemma eH (a:au n D) (T:Fn n) (w:ℕ) (b:2<=(ag n D w∩T).card):∃ j∈aW n D (ao n D T),ag n D (n+j)∩T=ag n D w∩T:=by obtain⟨j,-,-,c,d,-,-⟩:=ew a T _ b w rfl;exact⟨j,d,c⟩
lemma eA (r:au n D) {T:Fn n} (G:T.card=3) {a b c:Fin n} (H:a∈T) (J:b∈T) (K:c∈T) (h:a≠b) (i:a≠c) (s:b≠c) {w v:ℕ} (t:a∈ag n D w) (u:b∈ag n D w) (y:a∈ag n D v) (x:c∈ag n D v):2<=(aW n D (ao n D T)).card:=by
 let F w:=ag n D w∩T;have k:=_mn.2 ⟨t,H⟩;have l:=_mn.2 ⟨u,J⟩;have m:=_mn.2 ⟨x,K⟩;obtain⟨j,z,e⟩:=eH r T w (O1.2 ⟨a,k,b,l,h⟩)
 by_cases p:F w=F v
 · have d:F w=T:=_eqc IR (by rw[G];exact O2.2 ⟨a,k,b,l,c,p▸m,h,i,s⟩);obtain⟨o,-,-,I,N,-,q⟩:=ew r T T (by omega) w d
   rcases q with ⟨-,A,-⟩|⟨-,A,P,Q,-,-⟩;{exact AB rfl (Finset.ssubset_of_ssubset_of_subset A IR).ne}
   have:=UL (F (cj D o)) (F (ck D o));rw[Q,G] at this
   have g:∀ u,F u⊂T->2<=(F u).card->2<=(aW n D (ao n D T)).card:=fun u C f=>by obtain⟨d,E,B⟩:=eH r T u f;exact O1.2 ⟨o,N,d,E,fun g=>C.ne (B.symm.trans (g▸I))⟩
   by_cases f:2<=(F (cj D o)).card;{exact g _ A f};{exact g _ P (by omega)}
 · obtain⟨d,E,B⟩:=eH r T v (O1.2 ⟨a,_mn.2 ⟨y,H⟩,c,m,i⟩);exact O1.2 ⟨j,z,d,E,fun g=>p (e.symm.trans (g▸B))⟩
lemma m_ (g:bJ G) (h:ai n D) (y:U G H D) {p:Fin n->Ed} (a:bA n G D p) {u i j k:Fin n} (q:i∈aa n D) (l:j∈aa n D) (m:i≠j) (d:i≠k) (e:j≠k) (z:G u i) (A:G u j) (v:G u k):3<=(aE n D (ao n D {u})).card:=by
 have w:=gC a q (g.1 _ _ z) (_mss u);have x:=gC a l (g.1 _ _ A) (_mss u);have b:p i≠p j:=fun c=>m (a.2 i q j l c)
 by_cases o:k∈aa n D;{exact O2.2 ⟨_,w,_,x,_,gC a o (g.1 _ _ v) (_mss u),b,fun c=>d (a.2 i q k o c),fun c=>e (a.2 j l k o c)⟩}
 obtain⟨t,B,-,-,r,-,s,C,-,E,-⟩:=eq g h.1 y v;have f:∀ x∈aa n D,x≠k->p x≠(t,s):=fun x F K c=>K (_ms.1 ((c▸(a.1 x F).2.2.2)▸E)).symm;exact O2.2 ⟨_,w,_,x,_,df.2 ⟨B,C,r⟩,b,f i q d,f j l e⟩
lemma mM (Y:bJ G) (h:ai n D) (Z:U G H D) {u t:Fin n} (S:aW n D (ao n D {u})=∅) (M:aW n D (ao n D {t})=∅) {r:ℕ} (I:u∈ag n D r) (J:t∈ag n D r) (T:2<=aF D r):∃ i k:Ed,i≠k/\i∈aE n D (ao n D {u})/\i∈aE n D (ao n D {t})/\k∈aE n D (ao n D {u})/\k∈aE n D (ao n D {t}):=by
 obtain⟨i,k,e,f⟩:=kP Y h Z {u,t} ⟨u,by simp⟩ (fun x a=>by rcases _mi.1 a with rfl|a;{exact S};{rw[_ms.1 a];exact M}) (fun x a=>by rcases _mi.1 a with rfl|a;{exact I};{rw[_ms.1 a];exact J}) T
 exact⟨i,k,fun a=>e (a▸rfl),(f u (by simp)).1,(f t (by simp)).1,(f u (by simp)).2,(f t (by simp)).2⟩
end K4Generic
section L3Gen
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma qO (t:au n D) {P:Fn n} (y:P.card<=7) (L:FF n) (u:∀ T∈L,T.card=3/\aQ n D P T) (i:∀ T∈L,∀ S∈L,T≠S->(T∩S).card<=1) (E:Finset Ed) (z:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (a:Fn n) (U:Fin n->Fn n) (A:∀ f∈a,∃ e,dG n D P (U f) f e) (l:∀ f∈a,∀ T∈L,(U f∩T).card<=1):2*L.card+E.card+a.card<=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 classical
 choose! w c using A;let S:=a.filter fun f=>∀ M,M⊆U f->M.card=2->f∈M->¬ aQ n D P M;have d:S⊆a:=_fs _ _
 have m:∀ f∈a\S,∃ M,M⊆U f/\M.card=2/\f∈M/\aQ n D P M:=fun f b=>by rw[_md,_mf] at b;by_contra B;exact b.2 ⟨b.1,fun M p v q C=>B ⟨M,p,v,q,C⟩⟩
 choose! o h using m;let X:=(a\S).image o
 have dx:∀ M∈X,aQ n D P M/\2<=M.card/\M∉L/\M.card≠4/\M.card≠5/\(M.card=2->∀ T∈L,¬ M⊆T):=fun M F=>by obtain⟨f,b,rfl⟩:=_mg.1 F;obtain⟨p,v,-,q⟩:=h f b;exact⟨q,by omega,fun G=>by have:=(u _ G).1;omega,by omega,by omega,fun _ T H j=>by have:=_cl (subset_inter p j);have:=l f (_md.1 b).1 T H;omega⟩
 have K:2*L.card+X.card<=(du n D P).card:=by
  let Q:=aQ n D P;let s:=P.powerset.filter fun A=>Q A/\((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5)
  have g:∀ A,Q A->((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5)->A∈s:=fun A m p=>_mf.2 ⟨mem_powerset.2 (jw m),m,p⟩
  let W (A T:Fn n):ℕ:=if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0)
  have q:∀ T∈L,2<=∑ A∈s,W A T:=fun T f=>by
   rcases k5 t y (u T f).1 (u T f).2 with ⟨A,z,r,w⟩|⟨A,z,r,w⟩|⟨A,B,C,E,F,j,k,G,H,-⟩
   · exact le_trans (by simp[W,r,w]) (SL (fun _ _=>Zl _) (g A z (.inl ⟨r,T,f,w⟩)))
   · exact le_trans (by simp[W,r,w]) (SL (fun _ _=>Zl _) (g A z (.inr (.inl r))))
   · refine le_trans ?_ (SU (show ({A,B}:FF n)⊆s from fun x M=>by rcases _mi.1 M with rfl|M;{exact g _ E (.inr (.inr j))};{rw[_ms.1 M];exact g _ F (.inr (.inr k))}));rw[sum_pair C];simp[W,j,k,G,H]
  have v:∀ A∈s,∑ T∈L,W A T<=2:=fun A f=>by
   by_cases e:A.card=5
   · rw[show ∑ T∈L,W A T=(L.filter (fun T=>T⊆A)).card by rw[CF];exact SC rfl fun T _=>by simp[W,e]]
     by_contra R;obtain⟨b,c,d,j,k,l,p,q,r⟩:=two_lt_card_iff.1 (show 2<(L.filter (fun T=>T⊆A)).card by omega)
     rw[_mf] at j k l;exact nS (u _ j.1).1 (u _ k.1).1 (u _ l.1).1 e.le j.2 k.2 l.2 (i _ j.1 _ k.1 p) (i _ j.1 _ l.1 q) (i _ k.1 _ l.1 r)
   · rw[show ∑ T∈L,W A T=2*(L.filter (fun T=>A⊆T\/T⊆A)).card by rw[CF,mul_sum];exact SC rfl fun T _=>by simp[W,e]]
     have M:(L.filter (fun T=>A⊆T\/T⊆A)).card<=1:=card_le_one.2 fun T j S k=>by
      rw[_mf] at j k;have B:=(u T j.1).1;have C:=(u S k.1).1
      rcases (_mf.1 f).2.2 with ⟨p,-⟩|r|q
      · by_contra b;have:=_cl (subset_inter (j.2.resolve_right fun h=>by have:=_cl h;omega) (k.2.resolve_right fun h=>by have:=_cl h;omega));have:=i T j.1 S k.1 b;omega
      · exact lX B C r (j.2.resolve_left fun h=>by have:=_cl h;omega) (k.2.resolve_left fun h=>by have:=_cl h;omega) (i T j.1 S k.1)
      · exact AB q e
     omega
  have m:=card_nsmul_le_sum L _ 2 q;have p:=sum_le_card_nsmul s _ 2 v;rw[sum_comm] at m;simp only[smul_eq_mul] at m p
  have f:Disjoint L s:=_dl.2 fun T g k=>by have:=(u T g).1;rcases (_mf.1 k).2.2 with ⟨h,-⟩|h|h <;> omega
  have r:Disjoint (L∪s) X:=_dl.2 fun M k l=>by obtain⟨-,-,m,p,q,r⟩:=dx M l;rcases _mu.1 k with h|h;{exact m h};rcases (_mf.1 h).2.2 with ⟨v,T,g,w⟩|x|y;{exact r v T g w};{exact p x};{exact q y}
  have j:=eZ t P ((L∪s)∪X) fun M k=>by rcases _mu.1 k with h|h;{rcases _mu.1 h with h|h;{exact⟨by have:=(u M h).1;omega,(u M h).2⟩};{exact⟨by rcases (_mf.1 h).2.2 with ⟨h,-⟩|h|h <;> omega,(_mf.1 h).2.1⟩}};{exact⟨(dx M h).2.1,(dx M h).1⟩}
  rw[_cud r,_cud f] at j;omega
 have:=pW t P E z a S U w c d fun f b=>jN (c f (d b)) (_mf.1 b).2
 have:(a\S).card<=2*X.card:=card_le_mul_card_image _ 2 fun M _=>by
  by_cases k:((a\S).filter (fun f=>o f=M)).Nonempty;{obtain⟨g,r⟩:=k;rw[_mf] at r;rw[<-show M.card=2 from r.2▸(h g r.1).2.1];exact _cl fun f b=>by rw[_mf] at b;exact b.2▸(h f b.1).2.2.1};{rw[N0.1 k];simp}
 have:=CS d;omega
lemma ph (e:au n D) (Z:Finset ℕ) (c:∀ b∈Z,2<=aF D b/\ag n D b=∅):Z.card<=bL n D:=(show Z.card=∑ _w∈Z,1 by simp)▸(sum_le_sum fun w f=>by have:=(c w f).1;omega).trans (SU fun b d=>ke e (c b d).1 (c b d).2)
lemma _0.naW (S:bJ G) (h:ai n D) (U:U G H D) (b:Fv n) (r:aM n D b) {p:Fin n->Ed} (d:bA n G D p) (T J:Fn n) (A:Fin n->Fn n) (u:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (v:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a):∃ w:Fin n->Ed,(∀ f∈T,(w f).1<D.length/\cR D (w f).1=true/\f∈ag n D (aw D (w f))/\f∉ag n D (n+(w f).1)/\Disjoint (ag n D (aw D (w f))) (A f))/\J.image p∪T.image w⊆aE n D (ao n D T)/\(J.image p∪T.image w).card=J.card+T.card/\J.card+(aW n D (ao n D T)).card+(al n D).card<=T.card+bd n D:=by
 classical
 obtain⟨q,k⟩:=e6 d T J fun i c=>⟨(u i c).1,(u i c).2.1⟩
 have z:∀ f∈T,∃ e:Ed,e.1<D.length/\cR D e.1=true/\f∈ag n D (aw D e)/\f∉ag n D (n+e.1)/\Disjoint (ag n D (aw D e)) (A f):=fun f c=>by obtain⟨j,s,x,B,C,E,F⟩:=fm S h.1 U (A f) (v f c).1 f (v f c).2.2;exact⟨(j,s),x,B,C,E,F⟩
 choose! w y using z
 have I:Set.InjOn w T:=fun f c g l e=>by by_contra K;exact _dl.1 (y f c).2.2.2.2 (e▸(y g l).2.2.1) ((v f c).2.1 (_me.2 ⟨fun h=>K h.symm,l⟩))
 have M:Disjoint (J.image p) (T.image w):=_dl.2 fun e L O=>by obtain⟨i,c,rfl⟩:=_mg.1 L;obtain⟨f,g,N⟩:=_mg.1 O;obtain⟨a,W,P⟩:=(u i c).2.2 f g;exact _dl.1 (y f g).2.2.2.2 (N▸(d.1 i (u i c).1).2.2.1 a P) W
 have K:T.image w⊆aE n D (ao n D T):=fun e X=>by obtain⟨f,c,rfl⟩:=_mg.1 X;obtain⟨x,B,C,E,F⟩:=y f c;exact fL.2 ⟨x,⟨f,_mn.2 ⟨C,c⟩⟩,fun ⟨g,l⟩=>by rw[_mn] at l;exact _dl.1 F (cr h.1 x B (w f).2 l.1) ((v f c).2.1 (_me.2 ⟨fun h=>E (h▸l.1),l.2⟩))⟩
 have s:=US q K;have c:(J.image p∪T.image w).card=J.card+T.card:=by rw[_cud M,k,_cij I]
 have:=_cl s;have:=co h T (by rw[cs S U];simp);have:=cZ h.1 b r T;have:=_cl (IL:T∩al n D⊆T)
 exact⟨w,y,s,c,by omega⟩
lemma nb (p:bJ G) (h:ai n D) (q:U G H D) (b:Fv n) (r:aM n D b) {P:Fin n->Ed} (d:bA n G D P) (T J:Fn n) (A:Fin n->Fn n) (s:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (t:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a) {x y z:Fin n} (k:T={x,y,z}) (e:x≠y) (g:x≠z) (j:y≠z) {w v:ℕ} (u:x∈ag n D w) (B:y∈ag n D w) (o:x∈ag n D v) (C:z∈ag n D v):J.card+2+(al n D).card<=3+bd n D:=by obtain⟨-,-,-,-,M⟩:=naW p h q b r d T J A s t;have m:T.card=3:=by {rw[k,_cin (by simp[e,g]),_cin (by simp[j]),_cs]};have:=eA h.1 m (a:=x) (b:=y) (c:=z) (by simp[k]) (by simp[k]) (by simp[k]) e g j u B o C;omega
end L3Gen
section L3bGen
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma jx (s:bJ G) (h:ai n D) (y:U G H D) (b:Fv n) (A:aM n D b) {x c:Fin n} (a:x≠c) (B:x∈al n D) (d:∀ u∈aj n D b,x∈ag n D u.1->c∈ag n D u.1) {w:ℕ} (C:x∈ag n D w/\c∈ag n D w):∃ f,∀ e∈af n D x,e≠f->c∈ag n D (aw D e):=by
 classical
 obtain⟨z,g,i⟩:=s.2.2.1 x c a;obtain⟨-,-,E,o,j,k,-⟩:=gt s h y b A a B d C g i;obtain⟨f,m⟩:=_c1.1 (show ((aE n D (aR n D x c)).erase o).card=1 by rw[CE j,E])
 exact⟨f,fun e t p=>by by_contra q;obtain⟨F,I,J⟩:=ak.1 t;exact p (_ms.1 (m▸_me.2 ⟨fun r=>_fnt (k▸r▸cY h.1 t),dY.2 ⟨F,⟨I,q⟩,fun K=>J K.1⟩⟩))⟩
lemma gD (d:au n D) {c:Fin n} (f:aW n D (ao n D {c})=∅) {e:Ed} (b:e.1<D.length) (g:cR D e.1=true) (h:c∈ag n D (aw D e)):e∈af n D c:=ak.2 ⟨b,h,fun a=>Bool.noConfusion (g▸(dL d f b a).1)⟩
lemma oh (r:bJ G) (h:ai n D) (u:U G H D) (x:bL n D=0) {i v:Fin n} (B:i∈aa n D) {e:Ed} (M:af n D i={e}) (y:G i v) (R:∀ p∈af n D v,p.1≠e.1->¬ ag n D (aw D (am p))⊆{i}):∀ t,t∈ag n D (aw D (am e))<->G i t:=by
 have g:=h.1;obtain⟨o,a,b,d,_,k,w,-⟩:=ci r h u B;obtain rfl:e=o:=SG (M.symm.trans w);obtain⟨j,s⟩:=e
 have Q:∀ c,RT (bk n D) (n+j) (n+c)->c≠j->cR D c=false:=fun c p N=>by
  by_contra C;rw[_nf] at C;rcases RTct p with S|⟨q,E,z⟩;{exact N (by omega)}
  obtain⟨m,t,F,P,l⟩:=fj.1 z;obtain rfl:c=m:=by {omega};obtain⟨J,K,-⟩:=ak.1 (M.symm▸_mss (j,s))
  have L:=gr r h u x B (((eG (fun _ _ A=>A.1) (iF g B K)).tail (cM J s)).trans E)
  have T:aF D q=1:=by {have:=ef z;by_contra U;exact NE ((eM r g u B L (by omega))▸fJ g x (b:=q) (by omega))}
  have f:=fk r g u i q (ds g L);have Z:v≠i:=fun Z=>r.2.1 i (Z▸y);have W:aw D (c,!(!t))=q:=by {rw[Bool.not_not];exact l}
  exact R (c,!t) (ak.2 ⟨F,bv g F C (by unfold bH;omega) (W▸L) (W▸T) (u.2.2.1 _ ⟨i,v,y,dm i _,by simp[bB,cl]⟩) (by by_contra A;rw[_nf] at A;exact NM v (cs r u▸ee.2 A)),fun Y=>Z (_ms.1 (f (l▸cr g F C t Y)))⟩) N (by rw[show am (c,!t)=(c,!(!t)) from rfl,W];exact f)
 intro t;refine⟨fun q=>?_,k t⟩;by_contra z
 have f:val D (b4 i t) (n+j)=true:=by {rw[dz g _ a s,b,gop_true,BA];exact⟨cO g (d.symm▸_mss i) (by simp[b4]),cO g q (by simp[b4])⟩}
 have l:∀ c,RT (bk n D) (n+j) c->val D (b4 i t) c=true:=fun c J=>by induction J with | refl=>exact f | tail m p q=>obtain⟨c,o,C,rfl,rfl⟩:=fj.1 p;have:=dt g (fun _ _ h=>h) m;have:=dh g C o;rw[dz g _ C o,Q c (m.tail p) (by omega),gop_false,q];rfl
 have m:=l _ (iD h (n+j) (by omega));rw[u.2.2.2.2 i t z] at m;exact _fnt m
lemma pj (d:bJ G) (h:ai n D) (e:U G H D) (b:Fv n) (g:aM n D b) {p:Fin n->Ed} (c:bA n G D p) (T J:Fn n) (A:Fin n->Fn n) (j:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (k:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a) (F:FF n) (l:∀ M∈F,2<=M.card/\aQ n D T M):J.card+F.card+(al n D).card<=T.card+bd n D:=by obtain⟨-,-,-,-,M⟩:=naW d h e b g c T J A j k;have:=eZ h.1 T F l;have:(du n D T).card<=(aW n D (ao n D T)).card:=_cl (_fs _ _);omega
end L3bGen
section L3bTri
open _0
variable {n:ℕ} {G H:Gr n} {D:Dag}
lemma pk (g:bJ G) (h:ai n D) (u:U G H D) (b:Fv n) (B:aM n D b) {P:Fin n->Ed} (C:bA n G D P) (T J:Fn n) (A:Fin n->Fn n) (j:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (a:∀ f∈T,(∀ x∈A f,∀ y∈A f,¬ H x y)/\T.erase f⊆A f/\∃ x∈A f,G f x) (F:FF n) (f:∀ M∈F,M.card=2/\aQ n D T M) (t3:T.card=3) (k:T.card+bd n D<=J.card+F.card+(al n D).card):(∀ w,¬ T⊆ag n D w)/\(∀ t∈T,aW n D (ao n D {t})=∅/\∃ e1,∀ e∈af n D t,e=e1\/e∈J.image P)/\∀ x∈aj n D b,(ag n D x.1∩T).Nonempty:=by
 classical
 have p:=h.1;obtain⟨w,o,s,q,M⟩:=naW g h u b B C T J A j a
 have Z:∀ M∈F,2<=M.card/\aQ n D T M:=fun M y=>⟨by rw[(f M y).1],(f M y).2⟩
 have:=eZ p T F Z;have:(du n D T).card<=(aW n D (ao n D T)).card:=_cl (_fs _ _);have:=co h T (by rw[cs g u];simp);have:=cZ p b B T;have:=_cl (IL:T∩al n D⊆T);have:=_cl s
 have H:J.image P∪T.image w=aE n D (ao n D T):=_eqc s (by omega)
 have W:du n D T=aW n D (ao n D T):=_eqc (_fs _ _) (by omega)
 have d:∀ v,¬ T⊆ag n D v:=fun v m=>by have r:T∉F:=fun z=>by {have:=(f T z).1;omega};have:=eZ p T (insert T F) (fun M y=>by rcases _mi.1 y with rfl|y;{exact⟨by omega,⟨v,inter_eq_right.2 m⟩⟩};{exact Z M y});rw[_cin r] at this;omega
 have E:∀ x∈aj n D b,(ag n D x.1∩T).Nonempty:=by have:=d9 p b B T;have:=bS p b B;have r:((aj n D b).filter fun x=>(ag n D x.1∩T).Nonempty)=aj n D b:=_eqc (_fs _ _) (by omega);exact fun x y=>by rw[<-r] at y;exact(_mf.1 y).2
 have N:Set.InjOn (fun j=>ag n D (n+j)∩T) (du n D T):=by have:=_cl (show F⊆(du n D T).image fun j=>ag n D (n+j)∩T from fun M y=>by obtain⟨i,l,z⟩:=lp p (Z M y).1 (f M y).2;exact _mg.2 ⟨i,l,z⟩);exact card_image_iff.1 (le_antisymm card_image_le (by omega))
 have c:∀ {t:Fin n} {v:ℕ},t∈T->t∈ag n D v->v∈ao n D T:=fun z y=>cC.2 ⟨_,_mn.2 ⟨y,z⟩⟩
 refine⟨d,fun t z=>⟨EE fun i l=>?_,w t,fun e y=>?_⟩,E⟩
 · rw[aW,_mf,MR] at l;obtain⟨m,r,v,x⟩:=l;rw[b7] at r v x
   have I:i∈du n D T:=W.symm▸_mf.2 ⟨MR.2 m,c z r,c z v,c z x⟩
   have K:2<=(ag n D (n+i)∩T).card:=(_mf.1 I).2;obtain⟨S,-,-,X,L,-,U⟩:=ew p T _ K (n+i) rfl
   obtain rfl:S=i:=N (_mf.2 ⟨L,X.symm▸K⟩) I X
   have Q:∀ v,(ag n D v∩T).card<3:=fun v=>by by_contra m;exact d v (inter_eq_right.1 (_eqc IR (by omega)))
   rcases U with ⟨-,V,-⟩|⟨-,V,Y,O,-,-⟩;{have:=CL V;have:=Q (cj D S);omega}
   have:=CL V;have:=CL Y;have:=Q (n+S)
   have R:({t}:Fn n)=ag n D (cj D S)∩T:=_eqc (SS.2 (_mn.2 ⟨v,z⟩)) (by rw[_cs];omega)
   have J:({t}:Fn n)=ag n D (ck D S)∩T:=_eqc (SS.2 (_mn.2 ⟨x,z⟩)) (by rw[_cs];omega);rw[<-O,<-R,<-J,union_self,_cs] at K;omega
 · obtain⟨m,r,v⟩:=ak.1 y;have Y:=cY p y
   have x:e∈aE n D (ao n D T):=fL.2 ⟨m,⟨t,_mn.2 ⟨r,z⟩⟩,fun ⟨x,l⟩=>by
    rw[_mn] at l;have S:∀ s,x∈ag n D (aw D (e.1,s)):=fun s=>cr p m Y s l.1
    have I:e.1∈du n D T:=W.symm▸_mf.2 ⟨MR.2 m,c l.2 l.1,c l.2 (S false),c l.2 (S true)⟩
    have K:2<=(ag n D (n+e.1)∩T).card:=(_mf.1 I).2;have Q:=_eqc (show ag n D (n+e.1)∩T⊆T.erase t from fun q i=>_me.2 ⟨fun L=>v (L▸(_mn.1 i).1),(_mn.1 i).2⟩) (by rw[CE z,t3];omega)
    exact d (aw D e) fun q i=>if L:q=t then L▸r else cr p m Y e.2 (_mn.1 (Q.symm▸_me.2 ⟨L,i⟩)).1⟩
   rcases _mu.1 (H.symm▸x) with R|R;{exact .inr R}
   obtain⟨v,l,i⟩:=_mg.1 R;by_cases q:v=t;{exact .inl (q▸i.symm)}
   exact False.elim (_dl.1 (o v l).2.2.2.2 (i▸r) ((a v l).2.1 (_me.2 ⟨fun h=>q h.symm,z⟩)))
end L3bTri
namespace _B
def e8:_F (ℕ×ℕ):=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def bw (x:O->_d):Prop:=∃u v:O,(u.val,v.val)∈e8/\x u=true/\x v=true
abbrev aO (u v:O):Prop:=(u.val,v.val)∈e8\/(v.val,u.val)∈e8
def ab (u v:O):_d:=(([1408,8832,12544,6272,11264,5632,2816,11,69,98,49,88,44,22]:_F ℕ).getD u.val 0).testBit v.val
lemma Z {p:Prop}[Decidable p](h:decide p=true:=by decide +kernel):p:=of_decide_eq_true h
lemma ad:∀u v:O,ab u v=true↔aO u v:=Z
lemma bl {u v:O}:aO u v->aO v u:=Or.symm
lemma dv (u:O):¬aO u u:=by revert u;decide +kernel
lemma ce (x:O->_d):bw x↔∃u v:O,aO u v/\x u=true/\x v=true:=⟨λ⟨u,v,h,a,b⟩=>⟨u,v,.inl h,a,b⟩,λ⟨u,v,h,a,b⟩=>h.elim (λh=>⟨u,v,h,a,b⟩) λh=>⟨v,u,h,b,a⟩⟩
abbrev E:=ℕ×_d
abbrev U:=Σ_:ℕ,ℕ
abbrev T:=Fin 10
abbrev Tf:=Finset T
abbrev RT {a}(r:a->a->Prop):=Relation.ReflTransGen r
abbrev H:=@_mf
abbrev I (u v:O):=ab u v=true
abbrev B0 (u v:O):=ab u v=false
lemma N {u v:O}(h:I u v):aO u v:=(ad u v).1 h
lemma D2 {u v:O}(h:aO u v):I u v:=(ad u v).2 h
lemma aG {u v:O}:B0 u v↔¬aO u v:=by rw[<-ad,Bool.not_eq_true]
abbrev D1:=@_mss
abbrev D3:=@_ms
abbrev D4:=@_mi
abbrev E0:=@card_inter_add_card_sdiff
abbrev E2:=@card_le_card_of_injOn
abbrev E3:=@Nat.add_sub_cancel'
abbrev A0:=@mem_range
abbrev A1:=@mem_coe
abbrev A2:=@card_erase_of_mem
abbrev A3:=@card_eq_zero
abbrev A4:=@card_le_one
abbrev A5:=@card_filter_add_card_filter_not
abbrev A6:=@mem_image_of_mem
abbrev A7:=@singleton_subset_iff
abbrev A8:=@insert_subset_iff
abbrev A9:=@filter_eq_empty_iff
abbrev B1:=@union_subset
abbrev B2:=@sum_congr
abbrev B3:=@not_or
abbrev B4:=@not_not
abbrev B5:=@eq_empty_iff_forall_notMem
abbrev B6:=@inter_eq_left
abbrev B7:=@inter_eq_right
abbrev B8:=@mem_insert_of_mem
abbrev B9:=@mem_insert_self
abbrev HI:=@Relation.ReflTransGen.head_induction_on
abbrev NM:=@notMem_empty
abbrev SR:=@Subset.rfl
abbrev AB:=@absurd
lemma C {p:Prop}(h:¬p->False):p:=Classical.byContradiction h
lemma C8 {a b:E}(h:am a=am b):a=b:=by rw[<-aB a,h,aB]
lemma C9 {a b:E}(h:am a=b):a=am b:=h▸(aB a).symm
lemma nS {a}{x y:a}(h:x≠y):y≠x:=h.symm
lemma C1 {a}(s:Finset a)(h:0<s.card:=by omega):s.Nonempty:=_cp.1 h
lemma C2 {a}{s t:Finset a}(h:s⊆t)(p:t.card<=s.card:=by omega):s=t:=_eqc h p
lemma C3 {a}{s:Finset a}(h:s.card=0:=by omega):s=∅:=A3.1 h
lemma fi {a b}[DecidableEq b]{s:Finset a}{f:a->b}{p:b->Prop}(g:∀x∈s,p (f x)):∀y∈s.image f,p y:=forall_mem_image.2 g
lemma f1 {a}{x:a}{p:a->Prop}(u:p x):∀z∈({x}:Finset a),p z:=λ_ h=>D3.1 h▸u
lemma f2 {a}[DecidableEq a]{x y:a}{p:a->Prop}(u:p x)(v:p y):∀z∈({x,y}:Finset a),p z:=λ_ h=>by rcases D4.1 h with rfl|h;exacts[u,D3.1 h▸v]
lemma f3 {a}[DecidableEq a]{x y w:a}{p:a->Prop}(u:p x)(v:p y)(t:p w):∀z∈({x,y,w}:Finset a),p z:=λ_ h=>by rcases D4.1 h with rfl|h;exacts[u,f2 v t _ h]
lemma iY (v:O):(univ.filter λu=>aO v u).card=3:=by rw[filter_congr λu _=>(ad v u).symm];revert v;decide +kernel
lemma dT (v w:O)(h:v≠w):∃z,aO v z/\¬aO w z:=let⟨z,b,c⟩:=(Z:∀v w:O,v≠w->∃z,I v z/\B0 w z) v w h;⟨z,N b,aG.1 c⟩
def k6 (n:ℕ)(v:O):O:=Fin.ofNat 14 ((n>>>(4*v.1))&&&15)
def cp:O->O:=k6 0x13456209abc8d7
lemma gU:∀v,I v (cp v)/\cp (cp v)=v:=Z
lemma eR (a:o)(h:∀u v:O,aO u v->u∈a\/v∈a):7<=a.card:=by let c:=_cl (λv _=>(h v (cp v) (N (gU v).1)).elim (mem_union_left _) λb=>mem_union_right _ (_mg.2 ⟨_,b,(gU v).2⟩):(univ:o)⊆a∪a.image cp);have:=card_union_le a (a.image cp);have:=card_image_le (s:=a) (f:=cp);simp[Fintype.card_fin]at c;omega
def cI (s:_ep O):Prop:=∀u v:O,aO (s u) (s v)↔aO u v
lemma lt {s:_ep O}(h:∀u v:O,ab (s u) (s v)=ab u v):cI s:=λu v=>by rw[<-ad,<-ad u v,h]
def d3:_F o:=[{0,1,2,3,4,5,6},{0,1,2,3,4,5},{0,1,2,3,4},{0,1,2,5,11},{0,1,2,3},{0,1,2,5},{0,1,2,11},{0,1,11,12},{0,1,2},{0,1,3},{0,1,11},{0,1},{0,9},{0}]
def bT (n:Fin 15):o:=((∅:o)::d3).getD n.1 ∅
def sh:_F ℕ:=[0xdcba9876543210,0xabc98d72653401,0xcd9ab876451230,0x9cb8da74263510,0xd9bac783546120,0xdb97ca85316420,0xcb9ad781456320,0xca8db976420531,0xcab789d6034521,0x8acdb793425061,0x8ca7bd94305261,0x205316497ca8db,0x2506134798acdb,0x1256043a89cd7b,0xcba987d0654321,0x79bcad84536102,0x3546129bac78d,0x1356402ab9c7d8,0x1530462ba7c9d8,0x1456320cb9ad78]
def kg (k:Fin 20):O->O:=k6 (sh.getD k.1 0)
lemma p9:∀k:Fin 20,∀a b:O,(kg k a=kg k b->a=b)/\ab (kg k a) (kg k b)=ab a b:=Z
def qc:_F ℕ:=[0x20b649b19b90a3a420,0,0,0x40000000,0,0x44000000,0x180510000,0,0,0x100f00000,0x46700000,0x6000000,0x1000000046500000,0x1ab600000000a12400,0x64100000190511000]
def qA (n:Fin 15)(w:O):Fin 20:=Fin.ofNat 20 ((qc.getD n.1 0>>>(5*w.1))&&&31)
lemma jW (f:o)(b:∀u∈f,∀v∈f,¬aO u v)(a:f.Nonempty):∃s:_ep O,cI s/\f.image s∈d3:=by suffices f=∅\/∃s:_ep O,cI s/\f.image s∈d3 from this.resolve_left a.ne_empty;clear a;induction f using Finset.induction_on with
|empty=>exact .inl rfl
|insert v J e c=>
  let⟨s,j,n,l⟩:∃s:_ep O,cI s/\∃n:Fin 15,J.image s=bT n:=by rcases c (λu g w i=>b u (B8 g) w (B8 i)) with rfl|⟨s,j,m⟩;{exact⟨1,λ_ _=>Iff.rfl,0,by simp[bT]⟩};obtain⟨i,k,c⟩:=List.mem_iff_getElem.1 m;let k':i<14:=k;exact⟨s,j,⟨i+1,by omega⟩,by show _=((∅:o)::d3).getD (i+1) ∅;rw[List.getD_cons_succ,<-c];exact(_lge _ _ k).symm⟩
  let d:(insert v J).image s=insert (s v) (bT n):=by rw[image_insert,l]
  let⟨t,i,g⟩:∃t:_ep O,cI t/\⇑t=kg (qA n (s v)):=let c:Function.Injective (kg (qA n (s v))):=λx y h=>(p9 _ x y).1 h;⟨Equiv.ofBijective _ ⟨c,Finite.injective_iff_surjective.1 c⟩,lt λu w=>(p9 _ u w).2,rfl⟩;refine .inr ⟨t*s,λx y=>(i (s x) (s y)).trans (j x y),?_⟩;rw[Equiv.Perm.coe_mul,<-image_image,d,g];exact(Z:∀n:Fin 15,∀w:O,w∉bT n->(∀u∈insert w (bT n),∀v∈insert w (bT n),B0 u v)->(insert w (bT n)).image (kg (qA n w))∈d3) n (s v) (by rw[<-l];simpa using e) (d▸fi λx' k'=>fi λy' m'=>aG.2 ((j x' y').not.2 (b x' k' y' m')))
lemma fe (v:O):¬bw (λi=>decide (i=v)):=by rw[ce];rintro⟨a,b,c,d,e⟩;simp at d e;exact dv _ (d▸e▸c)
def aq (D:Dag):Prop:=∀x:O->_d,val D x (bH 14 D)=true↔bw x
lemma fN {D:Dag}(a:aq D):ag 14 D (bH 14 D)=∅:=B5.2 λv b=>fe v ((a _).1 (ee.1 b))
lemma jj (s:_ep O)(c:cI s){D:Dag}(h:ai 14 D)(a:aq D):ai 14 (bo s D)/\aq (bo s D)/\(bo s D).length=D.length/\ap 14 (bo s D)=ap 14 D/\aa 14 (bo s D)=(aa 14 D).image s:=⟨fd s h,λx=>by rw[fI s h.1 h.2.2 x,a,ce,ce];exact⟨λ⟨u,v,h,a,b⟩=>⟨s u,s v,(c u v).2 h,a,b⟩,λ⟨u,v,h,a,b⟩=>⟨s.symm u,s.symm v,(c _ _).1 (by simpa using h),by simpa using a,by simpa using b⟩⟩,cc s D,eJ s D,ep s h.1⟩
lemma aK:bJ aO:=⟨λ_ _=>bl,dv,dT,λu v=>let⟨a,b,c⟩:=(Z:∀u v:O,∃a,I u a/\a≠v) u v;⟨a,N b,c⟩⟩
lemma aC {D:Dag}(a:aq D):dg 14 aO D:=ju aK λx=>(a x).trans (ce x)
lemma kh:∀r s t i:O,r≠s->I i r->I i s->I t r->I t s->t=i:=Z
lemma sI:∀i k t:O,I i k->t≠i->∃q,I i q/\q≠k/\q≠t/\B0 t q:=Z
def aU (i:O):o:=univ.filter λa=>decide (a.1<7)≠decide (i.1<7)
def S (i:O):o:=univ.filter λa=>aO i a
lemma cJ {i a:O}:a∈S i↔aO i a:=by simp[S]
lemma kS:∀a b,I a b->decide (a.1<7)≠decide (b.1<7):=Z
lemma dB (i:O):∀a∈aU i,∀b∈aU i,¬aO a b:=λa d b e c=>by simp[aU]at d e;have:=kS a b (D2 c);simp[ne_eq,decide_eq_decide]at *;tauto
lemma dM (u v:O)(h:u≠v)(P:o):((univ.filter (λz=>aO u z)∩P)∩(univ.filter (λz=>aO v z)∩P)).card<=1:=le_trans (_cl (t:=univ.filter λz=>aO u z/\aO v z) λz a=>by simp only[_mn,H,_mv,true_and]at a;exact H.2 ⟨_mv z,a.1.1,a.2.1⟩) (by rw[filter_congr λz _=>and_congr (ad u z).symm (ad v z).symm];revert u v h;decide +kernel)
lemma gL {a:Type}[DecidableEq a]{b:Finset a}{x y z:a}(k:x∈b)(l:y∈b)(m:z∈b)(f:x≠y)(g:x≠z)(h:y≠z):3<=b.card/\(b.card<=3->∀e∈b,e=x\/e=y\/e=z):=by let d:({x,y,z}:Finset a)⊆b:=by{simp[A8,k,l,m]};let i:({x,y,z}:Finset a).card=3:=by{rw[_cin (by simp[f,g]),_c2 h]};exact⟨i▸_cl d,λn e j=>by rw[<-_eqc d (i▸n)]at j;simpa using j⟩
lemma d5 {a:Type}[DecidableEq a]{s:Finset a}{x y z:a}(j:x∈s)(k:y∈s)(l:z∈s)(f:x≠y)(g:x≠z)(h:y≠z):3<=s.card:=(gL j k l f g h).1
lemma aS {a:Type}[DecidableEq a]{s:Finset a}{x y z:a}(i:x∈s)(j:y∈s)(k:z∈s)(f:x≠y)(g:x≠z)(h:y≠z)(m:s.card<=3):∀e∈s,e=x\/e=y\/e=z:=(gL i j k f g h).2 m
lemma gF {a:Type}[DecidableEq a]{s:Finset a}{x y:a}(f:x∈s)(g:y∈s)(d:x≠y)(i:s.card<=2):∀e∈s,e=x\/e=y:=λe h=>C λc=>by rw[B3]at c;have:=d5 h f g c.1 c.2 d;omega
lemma fB {n:ℕ}{D:Dag}{b:Fin n->ℕ}{u:U}(a:u∈aj n D b){x:Fin n}(c:x∈ag n D u.1):x∈al n D:=eX.2 ⟨u.1,by have:=(dW.1 (H.1 (_md.1 a).1).1).2;omega,c⟩
lemma eh {n:ℕ}{D:Dag}(b:au n D){x:Fin n}{e:E}(c:e∈af n D x):am e∉af n D x:=λf=>by let⟨g,d,h⟩:=ak.1 c;apply h;rw[cB b g (cY b c),_mn];let⟨j,s⟩:=e;cases s;exacts[⟨by simpa[aw] using d,by simpa[aw,am] using (ak.1 f).2.1⟩,⟨by simpa[aw,am] using (ak.1 f).2.1,by simpa[aw] using d⟩]
def gV (u v:T):_d:=(([112,400,672,832,3,5,9,6,10,12]:_F ℕ).getD u.1 0).testBit v.1
abbrev bI (u v:T):Prop:=gV u v=true
lemma eS:bJ bI:=⟨Z,Z,Z,Z⟩
lemma jO {D:Dag}(h:ai 10 D)(g:dg 10 bI D):6<=bd 10 D:=by
 by_contra s;let⟨b,m⟩:=dK eS h.1 g;let⟨a,p⟩:=bQ eS h g;have:=dX h.1 b m;have:=aV 10 D;let c:∀u∈aa 10 D,∀v∈aa 10 D,gV u v=false:=λu d v e=>C λq=>by rw[_nf]at q;exact(fu eS h g q).elim (aN.1 d) (aN.1 e)
 let⟨l,d⟩:=(Z:∀a:Tf,(∀u∈a,∀v∈a,gV u v=false)->5<=a.card->(∀q∈a,4<=q.1)/\((4∈a/\5∈a)\/(4∈a/\7∈a)\/(5∈a/\7∈a))) _ c (by omega);let c:∀i:T,4<=i.1->∃a∈({0,1,2}:Tf),bI i a:=Z;have:=gS eS h g b m ({0,1,2}:Tf);let e:({0,1,2}:Tf).card=3:=V;let⟨f,_⟩:=e6 p ({0,1,2}:Tf) (aa 10 D) λi j=>⟨j,c i (l i j)⟩;have:=_cl f;let q:=λi j=>(p.1 i j).2.2.1;have:2<=(aW 10 D (ao 10 D ({0,1,2}:Tf))).card:=by rcases d with ⟨a,b⟩|⟨a,c⟩|⟨b,c⟩;exacts[eA h.1 e (a:=0) (b:=1) (c:=2) V V V V V V (q 4 a 0 V) (q 4 a 1 V) (q 5 b 0 V) (q 5 b 2 V),eA h.1 e (a:=1) (b:=0) (c:=2) V V V V V V (q 4 a 1 V) (q 4 a 0 V) (q 7 c 1 V) (q 7 c 2 V),eA h.1 e (a:=2) (b:=0) (c:=1) V V V V V V (q 5 b 2 V) (q 5 b 0 V) (q 7 c 2 V) (q 7 c 1 V)]
 omega
class K (q:outParam Prop) where
 D:Dag
 b0:O->ℕ
 z:O->E
 R:ai 14 D
 kq:aq D
 ku:cU 14 D b0
 kp:bA 14 aO D z
 k3:ap 14 D<=13
section KS
open K
variable {q0:Prop} [K q0]
abbrev F:=af 14 D
abbrev G:=ag 14 D
abbrev A:=aa 14 D
abbrev L:=al 14 D
abbrev J:=aj 14 D b0
abbrev P:=ap 14 D
abbrev B:=bd 14 D
abbrev M:=bL 14 D
abbrev Q:=aQ 14 D
abbrev W (x:O):=aW 14 D (ao 14 D {x})
abbrev Y (x:O):Finset U:=J.filter λu=>x∈G u.1
abbrev w:=aw D
abbrev v (i:O):=w (z i)
def O0:o:={0,1}
def O8:o:={8,9,10,13}
lemma kC:dg 14 aO D:=aC kq
lemma kM:aM 14 D b0:=bD ku
lemma ar:A.card+L.card=14/\P=B+M/\J.card+L.card=B/\B<=P/\P<=13:=⟨aV 14 D,bg 14 D,bS R.1 b0 kM,dC 14 D,k3⟩
lemma C7 {a:o}(h:A=a)(k:ℕ)(b:a.card=k:=by rfl):k+L.card=14/\P=B+M/\J.card+L.card=B/\B<=P/\P<=13:=by have:=ar;rwa[h,b]at this
lemma ha {x:O}:x∈A↔x∉L:=aN
lemma nL {x:O}(h:x∉A):x∈L:=B4.1 λa=>h (ha.2 a)
lemma yM {x:O}{u:U}(h:u∈Y x):u∈J/\x∈G u.1:=H.1 h
lemma go {i a:O}(d:i∈A)(h:aO i a):a∈G (v i):=(kp.1 i d).2.2.1 a h
abbrev kG {x y:O}(h:aO x y):=cg aK R.1 kC h
lemma eW {x:O}{e:E}(h:e∈F x):x∈G (w e):=(ak.1 h).2.1
lemma zI {i j:O}(a:i∈A)(b:j∈A)(e:i≠j):z i≠z j:=λh=>e (kp.2 i a j b h)
lemma bi (x:O):(F x).card+(W x).card<=2+(Y x).card:=by let h:=ez aK R kC b0 kM x;let d:=_cl (inter_subset_left:({x}:o)∩L⊆{x});rw[_cs]at d;change (F x).card+(W x).card=1+(({x}:o)∩L).card+(Y x).card at h;omega
lemma me {x:O}(d:x∈L):(F x).card+(W x).card=2+(Y x).card:=by let h:=ez aK R kC b0 kM x;rw[B6.2 (A7.2 d),_cs]at h;change (F x).card+(W x).card=1+1+(Y x).card at h;omega
lemma jX {x y:O}(a:x≠y)(b:x∈L)(d:∀u∈J,x∈G u.1->y∈G u.1){r:ℕ}(h:x∈G r/\y∈G r):∃e,∀f∈F x,f≠e->y∈G (w f):=jx aK R kC b0 kM a b d h
lemma bR {x a b:O}(d:x≠a)(f:x≠b)(g:¬aO a b):∃e∈F x,a∉G (w e)/\b∉G (w e):=let⟨_,i,j,k⟩:=(Z:∀x a b:O,x≠a->x≠b->B0 a b->∃y,I x y/\B0 y a/\B0 y b) x a b d f (aG.2 g);jJ aK R.1 kC g (N i) (aG.1 j) (aG.1 k)
lemma oN {x a b:O}(d:x≠a)(f:x≠b)(g:¬aO a b)(h:∀e∈F x,e∈F a\/e∈F b):False:=let⟨e,k,l,m⟩:=bR d f g;(h e k).elim (λi=>l (eW i)) λi=>m (eW i)
lemma aI {i a:O}(d:i∈A)(e:aO i a):z i∈F a:=let⟨b,f,g,_⟩:=kp.1 i d;ak.2 ⟨b,g a e,by rw[f];exact NM a⟩
lemma zA {i:O}(d:i∈A):i∈ag 14 D (aw D (am (z i))):=by rw[show aw D (am (z i))=aw D ((z i).1,!(z i).2) from rfl,(kp.1 i d).2.2.2];exact D1 i
lemma ei {i t:O}(d:i∈A)(e:am (z i)∈F t):t=i:=D3.1 ((kp.1 i d).2.2.2▸(eW e:t∈ag 14 D (aw D ((z i).1,!(z i).2))))
lemma lH {i x:O}{e:E}(d:i∈A)(f:x∈L)(g:am e∈F x):e≠z i:=λb=>ha.1 d (ei d (b▸g)▸f)
lemma m0 {i x:O}{e:E}(d:i∈A)(f:x∈L)(g:e∈F x):am e≠z i:=lH d f ((aB e).symm▸g)
lemma lI {i t:O}(d:i∈A)(f:t∈G (v i)):z i∈F t:=ak.2 ⟨(kp.1 i d).1,f,by rw[(kp.1 i d).2.1];exact NM t⟩
lemma pn {i:O}(d:i∈A):F i={am (z i)}:=by let⟨e,_,_,_,_,_,f,_⟩:=ci aK R kC d;let⟨g,j,_,k⟩:=kp.1 i d;let h:am (z i)∈F i:=ak.2 ⟨g,zA d,by rw[show (am (z i)).1=(z i).1 from rfl,j];exact NM i⟩;let f':F i={e}:=f;rw[f']at h⊢;rw[D3.1 h]
lemma sF {i x:O}(d:i∈A)(b:x≠i)(g:z i∈F x)(j:(F x).card<=2:=by omega):∃e,e≠z i/\F x={z i,e}/\∀t,t≠x->e∉F t:=by let⟨r,s,a,n,l,m,y⟩:=(Z:∀i x:O,∃r s,r≠s/\I i r/\I i s/\r≠x/\s≠x) i x;let⟨e,p,h⟩:=kb aK R.1 kC (x:=x) (a:=r) m.symm;let f:e≠z i:=λk=>h (k▸go d (N n));let u:F x={z i,e}:=(_eqc (f2 g p) (by rw[_c2 f.symm];exact j)).symm;refine⟨e,f,u,λt h8 c=>?_⟩;let k:∀q,q≠x->q∈G (v i)->aO q t:=λq ha hb=>C λq=>let⟨f,h,he,hf⟩:=bR ha.symm h8.symm q;by{rcases D4.1 (u▸h) with rfl|h;exacts[he hb,hf (D3.1 h▸eW c)]};let f:t=i:=kh r s t i a n l (D2 (bl (k r m (go d (N n))))) (D2 (bl (k s y (go d (N l)))));rw[f,pn d,D3]at c;exact b (ei d (c▸p))
lemma be {x y:O}(a:aO x y):∃e∈F x,am e∈F y/\(∀i∈A,e=z i->y=i)/\(∀i∈A,am e=z i->x=i):=let⟨e,f,g,_⟩:=kG a;⟨e,f,g,λ_ d b=>ei d (b▸g),λ_ d b=>ei d (C9 b▸f)⟩
lemma z2 {x y:O}(h:aO x y)(a:x∈L)(b:y∈L):∃e∈F x,am e∈F y/\(∀i∈A,e≠z i/\am e≠z i)/\x∉G (w (am e)):=let⟨e,f,g,_,s,_⟩:=kG h;⟨e,f,g,λ_ d=>⟨lH d b g,m0 d a f⟩,s⟩
lemma kE {x:O}(a:o)(g:∀i∈a,i∈A/\z i∈F x)(f:Finset E)(n:∀e∈f,e∈F x/\∀i∈a,e≠z i):a.card+f.card<=(F x).card:=by have:=_cl (B1 (fi λi h=>(g i h).2) (λe m=>(n e m).1):a.image z∪f⊆F x);rwa[_cud (_dl.2 λ_ k l=>by{obtain⟨i,h,rfl⟩:=_mg.1 k;exact(n _ l).2 i h rfl}),_cij (λi d j p h=>kp.2 i (g i d).1 j (g j p).1 h)]at this
lemma qj (l:M=0){x t:O}(b:o)(g:∀i∈b,i∈A/\z i∈F x){c:E}(s:c∈F x/\∀i∈A,c≠z i)(m:t∈G (w (am c)))(n:(F x).card<=b.card+1){i:O}(y:i∈b)(u:I i x/\t≠i):∀a,a∈G (v i)↔aO i a:=by have:=oh aK R kC l (g i y).1 (pn (g i y).1) (N u.1) λp h q e=>by{by_cases f:∃j∈b,p=z j;{obtain⟨j,d,rfl⟩:=f;exact q (by rw[D3.1 (e (zA (g j d).1))];rfl)};by_cases k:p=c;{exact u.2 (D3.1 (e (k▸m)))};have:=kE b g {c,p} (f2 ⟨s.1,λj d=>s.2 j (g j d).1⟩ ⟨h,λj d r=>f ⟨j,d,r⟩⟩);rw[_c2 (nS k)]at this;omega};rwa[aB]at this
lemma qE {t i x:O}{c h:E}(n:∀e∈F t,e=z i\/e=c\/e=h)(a:∀a,aO i a->a∈G (v i))(d:aO i t)(b:x≠t)(f:x≠i)(p:x∈G (w c))(r:x∈G (w h)):False:=let⟨q,g,j,_,k⟩:=sI i t x (D2 d) f;let⟨e,s,l,u⟩:=bR b.symm j.symm (aG.1 k);by rcases n e s with rfl|rfl|rfl;exacts[u (a q (N g)),l p,l r]
lemma rF {x:O}{a:U}(d:a∈J)(e:x∈G a.1)(h:(Y x).card=1:=by omega):∀u∈J,x∈G u.1->u=a:=λu j k=>by let⟨_,i⟩:=_c1.1 h;exact(D3.1 (by rw[<-i];exact H.2 ⟨j,k⟩)).trans (D3.1 (by rw[<-i];exact H.2 ⟨d,e⟩)).symm
lemma mg {i s d:O}(g:i∈A)(f:aO i s/\aO d s/\s≠i/\d≠i)(n:(F s).card<=2):∃e,(∀t,t≠s->e∉F t)/\e∈F s/\am e∈F d:=by let⟨e,_,m,j⟩:=sF g f.2.2.1 (aI g f.1) n;let⟨e',b,h,_⟩:=kG f.2.1;change am e'∈F s at h;rw[m,D4,D3]at h;rcases h with k|k;exacts[AB (ei g (C9 k▸b)) f.2.2.2,⟨e,j,m▸B8 (D1 _),C9 k▸b⟩]
lemma pr {x i j:O}{u:U}(a:∀t,t∈G (v i)↔aO i t)(b:∀t,t∈G (v j)↔aO j t)(d:∀t,aO i t->aO j t->t=x)(e:∀t,t≠x->t∈G u.1->t∈G (v i)/\t∈G (v j)):∀t∈G u.1,t=x:=λt f=>C λg=>let⟨r,s⟩:=e t g f;g (d t ((a t).1 r) ((b t).1 s))
lemma kn (c:o)(x:∀a∈c,∀b∈c,¬aO a b)(l:o)(g:∀i∈l,i∈A/\S i⊆c/\¬Q c (S i)):l.card<=M:=by
 classical
 let d:∀i∈l,∀q,(∀a∈c,(a∈G q↔aO i a))->False:=λi h q e=>(g i h).2.2 ⟨q,by ext a;rw[_mn,cJ];exact⟨λf=>(e a f.2).1 f.1,λf=>⟨(e a ((g i h).2.1 (cJ.2 f))).2 f,(g i h).2.1 (cJ.2 f)⟩⟩⟩;choose! b p using λi (h:i∈l)=>(iI aK R kC (g i h).1).elim (λt=>let⟨_,_,_,_,_,e⟩:=jL aK R.1 kC c x (λ_ _ h=>h) t;(d i h _ e).elim) id;let m:Set.InjOn b l:=λi h j y u=>C λk=>let⟨a,n,s⟩:=dT j i (nS k);let⟨_,_,_,_,_,_,e⟩:=iJ aK R.1 kC c x (λ_ _ h=>h) (p i h).1 (ds R.1 (u▸(p j y).1)) ⟨a,(g j y).2.1 (cJ.2 n),n,s⟩;d i h _ e;rw[<-_cij m];exact ph R.1 _ (fi λi h=>(p i h).2)
lemma qX (d:M=0){i:O}(e:i∈A){a:o}(f:a⊆aU i):Q a (S i∩a):=C λb=>by have:=kn (aU i) (dB i) {i} (f1 ⟨e,λ_ k=>H.2 ⟨_mv _,(kS i _ (D2 (cJ.1 k))).symm⟩,λ⟨q,l⟩=>b ⟨q,by rw[<-l,inter_assoc,B7.2 f]⟩⟩);rw[_cs]at this;omega
lemma mc (q:o)(l:q⊆aU 0)(y:q⊆L)(Oc Ct t:o)(n:∀i∈Oc,S i⊆q/\Q q (S i))(p:∀u∈Ct,u∉Oc/\((S u∩q).card<=2\/(S u⊆q/\¬Q q (S u))))(hI:∀i∈t,i∈A/\S i⊆q):2*Oc.card+t.card+(Ct.biUnion λu=>S u∩q).card+L.card<=2*q.card+B:=by
 let e:q.card<=7:=(_cl l).trans V
 classical
 let h0:∀a∈q,∀b∈q,¬aO a b:=λa d b g=>dB 0 a (l d) b (l g);let⟨E1,c1,Q1⟩:=kH aK R kC q t λi k=>⟨(hI i k).1,S i,(hI i k).2,(iY i).ge,λ_ d=>cJ.1 d⟩;choose! ct s using λf (r:f∈Ct.biUnion λu=>S u∩q)=>mem_biUnion.1 r;let m:=qO R.1 e (Oc.image S) (fi λi k=>⟨iY i,(n i k).2⟩) (fi λi _=>fi λj _ h=>by simpa[S] using dM i j (λe=>h (e▸rfl)) univ) E1 Q1 (Ct.biUnion λu=>S u∩q) (λf=>S (ct f)∩q) (λf r=>by{let⟨a1,u⟩:=s f r;refine jM aK R.1 kC (X:=insert (ct f) (q\(S (ct f)∩q))) inter_subset_right ?_ ?_ (λ_ d=>B8 d) u ⟨ct f,B9 _ _,bl (cJ.1 (_mn.1 u).1)⟩;{exact(p _ a1).2.elim .inl λ⟨h,x⟩=>by rw[B6.2 h];exact .inr ⟨iY _,x⟩};let x:∀a∈q\(S (ct f)∩q),¬aO (ct f) a:=λa d k=>by{rw[_md,_mn,cJ]at d;exact d.2 ⟨k,d.1⟩};intro a d b g;rcases D4.1 d with rfl|d<;>rcases D4.1 g with rfl|g;exacts[dv _,x b g,λh=>x a d (bl h),h0 a (_md.1 d).1 b (_md.1 g).1]}) (λf r=>fi λi k=>by have:=dM (ct f) i (λe=>(p _ (s f r).1).1 (e▸k)) q;rw[(B6.2 (n i k).1:univ.filter (λx=>aO i x)∩q=S i)]at this;exact this);have:=co R q (by rw[fN kq];simp);let d:=cZ R.1 b0 kM q;rw[B6.2 y]at d;rw[_cii _ (λ(i j:O) (h:S i=S j)=>C λa=>let⟨_,b,c⟩:=dT i j a;c (cJ.1 (h▸cJ.2 b))),c1]at m;dsimp[L,B]at *;omega
lemma C4 (l:0∈A)(hB:B<=L.card:=by omega):False:=by
 have:=ar;let p:J=∅:=C3
 let g:∀x,(F x).card<=2:=λx=>by have:=bi x;have:(Y x).card=0:=A3.2 (by simp[Y,p]);omega
 let i:∀u,aO 0 u->∃e,(∀t,t≠u->e∉F t)/\∀x,aO x u->x≠0->am e∈F x:=λu s=>let⟨e,_,b,q⟩:=sF l (λh2=>by rw[h2]at s;exact dv 0 s) (aI l s) (g u);⟨e,q,λx k j=>let⟨e',f,d,_⟩:=kG k;by change am e'∈F u at d;rw[b,D4,D3]at d;rcases d with k|k;exacts[(j (ei l (C9 k▸f))).elim,C9 k▸f]⟩;let k:∀x x' u:O,I 0 u/\I x u/\I x' u/\x≠0/\x'≠0/\x≠x'/\I x 9/\u≠9->∃r,am r∈F 9/\x∈G (w r)/\∀a,a≠x->¬aO a x'->a∉G (w r):=λx x' u ⟨s,h,q,j,y,h2,n,h3⟩=>by let⟨e,h4,p⟩:=i u (N s);let⟨r,h6,m,_⟩:=kG (N n);let i:r≠am e:=λb=>h4 9 h3.symm (by rw[b,aB]at m;exact m);refine⟨r,m,eW h6,λa ha h8 l=>?_⟩;let⟨f,n,d,c⟩:=bR ha.symm h2 h8;let a:=_eqc (s:={am e,r}) (t:=F x) (f2 (p x (N h) j) h6) (by rw[_c2 i.symm];exact g x);rcases D4.1 (a.symm▸n) with rfl|n;exacts[c (eW (p x' (N q) y)),d (D3.1 n▸l)]
 let⟨d,a,b,c⟩:=k 1 3 7 V;let⟨b,d,f,h⟩:=k 5 4 10 V;let⟨j,e,b,i⟩:=k 6 2 8 V;have:=d5 a d e (λa=>c 5 V V (C8 a▸f)) (λa=>c 6 V V (C8 a▸b)) (λa=>h 6 V V (C8 a▸b));have:=g 9;omega
def X:o:={7,8,13}
def J0:o:={0,1,2}
def kV (b:o)(f:O):o:=b.erase f∪univ.filter λa=>I f a/\∀g∈b.erase f,B0 a g
lemma C5 (k:J0⊆A):(∀i∈J0,i∈A/\(∃a∈X,aO i a)/\∀f∈X,∃a∈kV X f,aO i a)/\∀f∈X,(∀a∈kV X f,∀b∈kV X f,¬aO a b)/\X.erase f⊆kV X f/\∃a∈kV X f,aO f a:=let h:=(Z:(∀i∈J0,(∃a∈X,I i a)/\∀f∈X,∃a∈kV X f,I i a)/\∀f∈X,(∀a∈kV X f,∀b∈kV X f,B0 a b)/\∃a∈kV X f,I f a);⟨λi g=>⟨k g,(h.1 i g).1.imp λ_ d=>⟨d.1,N d.2⟩,λf d=>((h.1 i g).2 f d).imp λ_ e=>⟨e.1,N e.2⟩⟩,λf d=>⟨λa e b l=>aG.1 ((h.2 f d).1 a e b l),subset_union_left,(h.2 f d).2.imp λ_ e=>⟨e.1,N e.2⟩⟩⟩
lemma sl (a:J0⊆A):L.card+2<=B:=by let⟨b,c⟩:=C5 a;have:=nb aK R kC b0 kM kp X J0 (kV X) b c rfl V V V (go (i:=0) (a V) V) (go (i:=0) (a V) V) (go (i:=1) (a V) V) (go (i:=1) (a V) V);rw[(V:J0.card=3)]at this;dsimp[L,B]at *;omega
lemma sk (s:M<=1)(a:J0⊆A):L.card+3<=B:=by
 let d:(∀i∈J0,X⊆aU 0/\S i⊆aU 0/\(S i∩X).card=2)/\∀i∈J0,∀j∈J0,S j∩X⊆S i∩X->j=i:=Z
 classical
 let⟨t',n⟩:=C5 a;let p:∀i∈J0,∃b,Q X b/\S i∩X⊆b/\(Q (aU 0) (S i)->b=S i∩X):=λi h=>if r:Q (aU 0) (S i) then let⟨q,g⟩:=r;let k:G q∩X=S i∩X:=by{rw[<-g,inter_assoc,B7.2 (d.1 i h).1]};⟨_,⟨q,rfl⟩,k▸SR,λ_=>k⟩ else ⟨G (v i)∩X,⟨_,rfl⟩,λ_ f=>by rw[_mn,cJ]at f;exact _mn.2 ⟨go (a h) f.1,f.2⟩,λf=>AB f r⟩;choose! f l using p;let b:=J0.filter λi=>¬Q (aU 0) (S i);have:=kn (aU 0) (dB 0) b λi h=>by rw[H]at h;exact⟨a h.1,(d.1 i h.1).2.1,h.2⟩
 let k:Set.InjOn f J0:=λi c j m g=>C λe=>by let q:∀i∈J0,∀j∈J0,f i=f j->i≠j->¬Q (aU 0) (S i):=λi c j m g e r=>e (d.2 i c j m (by rw[<-(l i c).2.2 r,g];exact(l j m).2.1)).symm;let h:i∈b:=H.2 ⟨c,q i c j m g e⟩;let p:j∈b:=H.2 ⟨m,q j m i c g.symm (nS e)⟩;have:=one_lt_card.2 ⟨i,h,j,p,e⟩;omega
 have:=pj aK R kC b0 kM kp X J0 (kV X) t' n (J0.image f) (fi λi c=>⟨(d.1 i c).2.2▸_cl (l i c).2.1,(l i c).1⟩);rw[_cij k,(V:J0.card=3),(V:X.card=3)]at this;dsimp[L,B]at *;omega
lemma ry (a:J0⊆A)(d:10<=L.card:=by omega):L.card+3<=B:=by have:=sl a;have:=ar;exact sk (by omega) a
lemma pp (x:M=0)(y:J0⊆A)(k:B<=L.card+3:=by omega):(∀t∈X,(F t).card<=3/\W t=∅)/\∀u∈J,(G u.1∩X).Nonempty:=by
 let g:(∀i∈J0,X⊆aU i/\(S i∩X).card=2)/\(∀i∈J0,∀j∈J0,S j∩X⊆S i∩X->j=i)/\∀t∈X,(J0.filter λi=>I i t).card<=2/\∀i∈J0,B0 i t->X.erase t⊆S i:=Z
 classical
 let⟨y',c⟩:=C5 y;let n:Set.InjOn (λi=>S i∩X) J0:=λi h j b f=>g.2.1 j b i h (by rw[show S i∩X=S j∩X from f]);let⟨d,a,b⟩:=pk aK R kC b0 kM kp X J0 (kV X) y' c (J0.image λi=>S i∩X) (fi λi h=>⟨(g.1 i h).2,qX x (y h) (g.1 i h).1⟩) rfl (by rw[_cij n,(V:X.card=3),(V:J0.card=3)];dsimp[B,L]at k;omega);refine⟨λt f=>⟨?_,(a t f).1⟩,b⟩;let⟨j,c⟩:=(a t f).2;let r:F t⊆insert j ((J0.filter λi=>I i t).image z):=λe b=>(c e b).elim (·▸B9 _ _) λa=>by{obtain⟨i,h,rfl⟩:=_mg.1 a;exact B8 (_mg.2 ⟨i,H.2 ⟨h,C λm=>by rw[Bool.not_eq_true]at m;exact d (v i) λa c=>if d:a=t then d▸eW b else go (y h) (cJ.1 ((g.2.2 t f).2 i h m (_me.2 ⟨d,c⟩)))⟩,rfl⟩)};have:=_cl r;have:=card_insert_le j ((J0.filter λi=>I i t).image z);have:=card_image_le (s:=J0.filter λi=>I i t) (f:=z);have:=(g.2.2 t f).1;omega
def dE (k:Fin 7):O:=⟨k.1,by omega⟩
lemma ed:Function.Injective dE:=V
lemma gY {T:o}(q:A=T)(c:Finset (Fin 7))(n:T=c.image dE/\4<=c.card/\J0⊆c.image dE:=by decide):False:=by
 let⟨a,b,l⟩:=n;let r:A=c.image dE:=q.trans a;let e:∀k:Fin 7,S (dE k)⊆aU 0:=Z;let j:∀a:Finset (Fin 7),(if a.card<=3 then 2*a.card else 6)<=((a.image dE).biUnion λu=>S u∩aU 0).card:=Z;let a:(aU 0).card=7:=V;let a:∀k:Fin 7,dE k∉aU 0:=V
 classical
 let g:∀k∈c,dE k∈A:=λk b=>r▸A6 _ b;let u:aU 0⊆L:=λ_ i=>nL λh=>by{obtain⟨k,_,rfl⟩:=_mg.1 (r▸h);exact a k i};let b:=univ.filter λk:Fin 7=>Q (aU 0) (S (dE k));let f:=univ.filter λk:Fin 7=>¬Q (aU 0) (S (dE k));let p:=mc (aU 0) SR u (b.image dE) (f.image dE) (c.image dE) (fi λk d=>⟨e k,(H.1 d).2⟩) (fi λk d=>⟨λa'=>let⟨k',d',i⟩:=_mg.1 a';(H.1 d).2 (ed i▸(H.1 d').2),.inr ⟨e k,(H.1 d).2⟩⟩) (fi λk d=>⟨g k d,e k⟩);let m:=kn (aU 0) (dB 0) ((f∩c).image dE) (fi λk d=>⟨g k (_mn.1 d).2,e k,(H.1 (_mn.1 d).1).2⟩);rw[_cii _ ed]at m;rw[_cii _ ed,_cii _ ed]at p;let e:b.card+f.card=7:=by simpa using A5 (s:=(univ:Finset (Fin 7))) λk:Fin 7=>Q (aU 0) (S (dE k))
 have:=E0 f c;let i:(f\c).card<=(univ\c).card:=_cl (sdiff_subset_sdiff (subset_univ _) SR);rw[card_univ_sdiff,Fintype.card_fin]at i;let a:c.card<=7:=by simpa using card_le_univ c
 let a:=j f;let b:=ar;rw[r,_cii _ ed]at b;have:=sl (r▸l);let b:c.card=4->13<=B:=λh=>by{have:=ry (r▸l);omega};split_ifs at a<;>omega
lemma nm (l:A={0,1,2,5,11}):False:=by
 let c:o:={7,8,9,10,12,13};let g:o:={0,1,2,5};let m:o:={7,8,10};let k (f:O):o:=if f=7 then {3,8,9,10,13} else if f=8 then {6,7,10,12,13} else {4,7,8,9,12};let n:(∀i∈g,(∃a∈m,I i a)/\∀f∈m,∃a∈k f,I i a)/\∀f∈m,(∀a∈k f,∀b∈k f,B0 a b)/\m.erase f⊆k f/\∃a∈k f,I f a:=Z;let h:(∀i∈g,S i⊆c)/\(∀u∈({3,4,6}:o),u∉g/\(S u∩c).card<=2)/\((({3,4,6}:o).biUnion λu=>S u∩c).card=6):=Z;let f:c⊆aU 0:=V;let s:∀a∈c,a∉({0,1,2,5,11}:o):=V;let d:∀i∈g,i∈A:=by{rw[l];decide};have:=nb aK R kC b0 kM kp m g k (λi p=>⟨d i p,(n.1 i p).1.imp λ_ e=>⟨e.1,N e.2⟩,λf j=>((n.1 i p).2 f j).imp λ_ e=>⟨e.1,N e.2⟩⟩) (λf j=>⟨λa e b t=>aG.1 ((n.2 f j).1 a e b t),(n.2 f j).2.1,(n.2 f j).2.2.imp λ_ e=>⟨e.1,N e.2⟩⟩) rfl V V V (go (i:=0) (d 0 V) V) (go (i:=0) (d 0 V) V) (go (i:=0) (d 0 V) V) (go (i:=0) (d 0 V) V)
 classical
 have:=C7 l 5;let p:c⊆L:=λa q=>nL (l.symm▸s a q)
 let j:=g.filter λi=>Q c (S i);let k:=g.filter λi=>¬Q c (S i);have:=mc c f p j {3,4,6} g (λi e=>⟨h.1 i (H.1 e).1,(H.1 e).2⟩) (λu y=>⟨λy'=>(h.2.1 u y).1 (H.1 y').1,.inl (h.2.1 u y).2⟩) (λi e=>⟨d i e,h.1 i e⟩);have:=kn c (λa q b r=>dB 0 a (f q) b (f r)) k λi e=>⟨d i (H.1 e).1,h.1 i (H.1 e).1,(H.1 e).2⟩;let r:j.card+k.card=g.card:=A5 λi=>Q c (S i);rw[h.2.2,(V:g.card=4),(V:c.card=6)]at *;dsimp[L,B]at *;omega
class CR (q1:outParam Prop) where
 r0:O->Option _d
 i0:T->O
 hf:Function.Injective i0/\∀v,r0 v=none↔∃i:T,i0 i=v
lemma kT {j:ℕ}(b:j<D.length)(s:_d)(x:O->_d):val D x (14+j)=kF (cR D j) (val D x (aw D (j,s))) (val D x (aw D (j,!s))):=by rw[cS R.1 x j b];cases s;{simp[aw]};{cases cR D j<;>simp[aw,Bool.and_comm,Bool.or_comm]}
lemma oi (E:Dag)(g:_d×ℕ×ℕ):cj (E++[g]) E.length=g.2.1/\ck (E++[g]) E.length=g.2.2/\cR (E++[g]) E.length=g.1/\∀i<E.length,cj (E++[g]) i=cj E i/\ck (E++[g]) i=ck E i:=⟨by unfold cj;rw[f9],by unfold ck;rw[f9],by unfold cR;rw[f9],λi a=>by unfold cj ck;rw[gM E [g] i a];exact⟨rfl,rfl⟩⟩
noncomputable section CofRestrict
open Classical Function CR
variable {q1:Prop} [CR q1]
def cf (y:T->_d):O->_d:=λv=>(r0 v).getD (decide (∃i:T,i0 i=v/\y i=true))
lemma dN (y:T->_d)(i:T):cf y (i0 i)=y i:=by unfold cf;rw[(hf.2 _).2 ⟨i,rfl⟩,Option.getD_none];by_cases b:y i=true;{rw[b,decide_eq_true_eq];exact⟨i,rfl,b⟩};rw[Bool.not_eq_true]at b;rw[b,decide_eq_false_iff_not];rintro⟨j,d,h⟩;rw[hf.1 d,b]at h;exact _fnt h
lemma dw (y:T->_d){v:O}{b:_d}(h:r0 v=some b):cf y v=b:=by unfold cf;rw[h,Option.getD_some]
def dD (n:ℕ):Prop:=∀y y':T->_d,val D (cf y) n=val D (cf y') n
def aL (n:ℕ):Prop:=¬dD n/\RT (λa b=>bk 14 D a b/\¬dD b) n (bH 14 D)
def cF (n:ℕ):ℕ:=((bV D n).filter λj=>aL (14+j)).card
def kl:ℕ:=∑n∈(cD 14 D).filter aL,(cF n-1)
def eT (t:ℕ->ℕ)(e:ℕ):Finset ℕ:=(range (14+D.length)).filter λn=>aL n/\t n=e
def f5:Finset U:=(dq 14 D).filter λu=>aL u.1/\u.2+1<cF u.1
abbrev eP (k:ℕ)(E:Dag)(t q:ℕ->ℕ)(i:ℕ):Prop:=q i<k/\aL (14+q i)/\t (14+q i)=10+i/\cj E i=t (cj D (q i))/\ck E i=t (ck D (q i))/\aL (cj D (q i))/\aL (ck D (q i))
abbrev eQ (E:Dag)(t q:ℕ->ℕ)(j:ℕ):Prop:=(∃i<E.length,q i=j)\/∀s,aL (aw D (j,s))->t (aw D (j,s))=t (14+j)
def eg (k:ℕ)(E:Dag)(t q:ℕ->ℕ):Prop:=au 10 E/\(∀n<14+k,aL n->t n<10+E.length/\∀y,val E y (t n)=val D (cf y) n)/\(∀i<E.length,eP k E t q i)/\(∀j<k,aL (14+j)->eQ E t q j)/\(∀i:T,t (i0 i).1=i.1)
lemma e9 {n:ℕ}(h:aL n):n<14+D.length:=C λa=>h.1 λy y'=>by rw[fs D _ n (by omega),fs D _ n (by omega)]
lemma fO {a b:ℕ}(d:bk 14 D a b)(e:¬dD a)(h:aL b):aL a:=⟨e,.head ⟨d,h.1⟩ h.2⟩
lemma jn {n:ℕ}(h:aL n)(b:n≠bH 14 D):∃z,bk 14 D n z/\aL z:=by rcases h.2.cases_head with d|⟨z,e,a⟩;exacts[AB d b,⟨z,e.1,e.2,a⟩]
lemma fX {v:O}(b:r0 v=some true){n:ℕ}(d:v∈ag 14 D n):¬aL n:=λh=>h.1 λy y'=>by rw[cO R.1 d (dw y b),cO R.1 d (dw y' b)]
lemma eC {n:ℕ}(b:n<14)(e:aL n):∃i:T,(i0 i).1=n:=by cases d:r0 ⟨n,b⟩ with|some v=>exact AB (λy y'=>by rw[bY D _ n b,bY D _ n b,dw y d,dw y' d]) e.1|none=>let⟨i,g⟩:=(hf.2 _).1 d;exact⟨i,g▸rfl⟩
lemma lx {j:ℕ}(a:j<D.length)(b:aL (14+j)):∃s,aL (aw D (j,s)):=by by_cases c:dD (cj D j);swap;{exact⟨false,fO (cM a false) (by rw[aX];exact c) b⟩};by_cases d:dD (ck D j);{exact AB (λy y'=>by rw[cS R.1 _ j a,cS R.1 _ j a,c y y',d y y']) b.1};exact⟨true,fO (cM a true) (by rw[bh];exact d) b⟩
lemma nZ {k:ℕ}(r:k<D.length){E:Dag}{t q:ℕ->ℕ}(h:eg k E t q):∃E' t' q',eg (k+1) E' t' q':=by
 let⟨m,z,P,Q,x⟩:=h;let⟨Z,B,_⟩:=R.1 k r;by_cases G:aL (14+k);swap;{exact⟨E,t,q,m,λn a8 f=>z n (by have:n≠14+k:=λl=>G (l▸f);omega) f,λi c=>let⟨a,b⟩:=P i c;⟨by omega,b⟩,λj hj g=>Q j (by have:j≠k:=λl=>G (l▸g);omega) g,x⟩};let U:=update t (14+k);let a:=cj D k;let b:=ck D k;let cu:∀v n,n<14+k->U v n=t n:=λv n a8=>update_of_ne (by omega) _ _;let cs:∀v,U v (14+k)=v:=λv=>update_self _ _ _;let kP:∀(E':Dag) v q',(∀i<E.length,q' i=q i/\cj E' i=cj E i/\ck E' i=ck E i)->∀i<E.length,eP (k+1) E' (U v) q' i:=λE' v q' y i c=>by let⟨a1,a2,a3,a4,a5,a6,a7⟩:=P i c;let⟨sa,sb,_⟩:=R.1 (q i) (by omega);let⟨e1,e2,e3⟩:=y i c;unfold eP;rw[e1,e2,e3,cu v _ (by omega),cu v _ (by omega),cu v _ (by omega)];exact⟨by omega,a2,a3,a4,a5,a6,a7⟩
 let kQ:∀(E':Dag) v q',E.length<=E'.length->(∀i<E.length,q' i=q i)->∀j<k,aL (14+j)->eQ E' (U v) q' j:=λE' v q' hl y j hj g=>(Q j hj g).elim (λ⟨i,c,u⟩=>.inl ⟨i,by omega,by rw[y i c,u]⟩) λW=>.inr λs d=>by have:=dh R.1 (j:=j) (by omega) s;rw[cu v _ (by omega),cu v _ (by omega)];exact W s d
 let kR:∀v (i:T),U v (i0 i).1=i.1:=λv i=>by rw[cu v _ (by have:=(i0 i).2;omega)];exact x i
 by_cases l:aL a/\aL b/\t a≠t b;{let⟨L,M,p⟩:=l;let⟨x,va⟩:=z _ Z L;let⟨y,vb⟩:=z _ B M;let g:=(cR D k,t a,t b);let E':=E++[g];let A:au 10 E':=jG m _ _ _ x y p;let⟨e1,e2,e3,e4⟩:=oi E g;let u:E'.length=E.length+1:=by{simp[E']};let a:∀y,(∀n<10+E.length,val E' y n=val E y n)/\val E' y (10+E.length)=kF g.1 (val E y g.2.1) (val E y g.2.2):=λy=>by{let f:∀n<10+E.length,val E' y n=val E y n:=λn h=>by{have:=oe E' y E.length n h (by simp[E']);rw[<-this];simp[E']};refine⟨f,?_⟩;let h:E.length<E'.length:=by{simp[E']};let⟨d,e,_⟩:=A E.length h;rw[cS A y E.length h,e3];rw[e1]at d;rw[e2]at e;rw[e1,e2,f _ d,f _ e]};exact⟨E',U (10+E.length),update q E.length k,A,λn a8 f=>by{rw[u];by_cases h0:n=14+k;{rw[h0,cs];exact⟨by omega,λy=>by rw[(a y).2,va y,vb y,cS R.1 _ k r]⟩};let⟨b,x⟩:=z n (by omega) f;rw[cu _ n (by omega)];exact⟨by omega,λy=>by rw[(a y).1 _ b,x y]⟩},λi c=>by{rw[u]at c;by_cases c':i<E.length;{exact kP _ _ _ (λi c=>⟨update_of_ne (by omega) _ _,e4 i c⟩) i c'};let h0:i=E.length:=by{omega};unfold eP;rw[h0,update_self,cs,cu _ _ Z,cu _ _ B,e1,e2];exact⟨by omega,G,rfl,rfl,rfl,L,M⟩},λj hj g'=>by{by_cases F:j=k;{exact .inl ⟨E.length,by omega,by rw[F,update_self]⟩};exact kQ _ _ _ (by omega) (λi c=>update_of_ne (by omega) _ _) j (by omega) g'},kR _⟩};let⟨a,b⟩:=lx r G;let x:∀s,aL (aw D (k,s))->t (aw D (k,s))=t (aw D (k,a)):=λs d=>by cases s<;>cases a<;>simp[aX,bh]at d b⊢;all_goals by_contra p;first|exact l ⟨d,b,p⟩|exact l ⟨b,d,nS p⟩
 let⟨u,l⟩:=z _ (dh R.1 r a) b;let b:=aw D (k,a);let i:=aw D (k,!a);let K:∀y,val D (cf y) (14+k)=val D (cf y) b:=by by_cases e:dD i;{exact λy=>by let c:∀y',val D (cf y') (14+k)=kF (cR D k) (val D (cf y') b) (val D (cf y) i):=λy'=>by{rw[kT r a,e y' y]};rw[c y];cases f:cR D k<;>cases g:val D (cf y) i;{simp};{exact(G.1 λp q=>by rw[c p,c q,f,g];simp).elim};{exact(G.1 λp q=>by rw[c p,c q,f,g];simp).elim};{simp}};let c:=fO (cM r (!a)) e G;let⟨_,v1⟩:=z _ (dh R.1 r (!a)) c;intro y;rw[kT r a,<-v1 y,x _ c,l y];cases cR D k<;>simp[b]
 exact⟨E,U (t b),q,m,λn a8 f=>by{by_cases h0:n=14+k;{rw[h0,cs];exact⟨u,λy=>by rw[l y,K y]⟩};rw[cu _ n (by omega)];exact z n (by omega) f},kP E _ q λ_ _=>⟨rfl,rfl,rfl⟩,λj hj g'=>by{by_cases F:j=k;{exact .inr λs d=>by rw[F]at d⊢;rw[cu _ _ (dh R.1 r s),cs];exact x s d};exact kQ E _ q le_rfl (λ_ _=>rfl) j (by omega) g'},kR _⟩
lemma km {G:Dag}{t q:ℕ->ℕ}(hI:eg D.length G t q)(e:ℕ):aF G e+(eT t e).card<=∑n∈eT t e,cF n+1:=by
 let⟨_,_,y,h4,M⟩:=hI;let F:=eT t e;let A:=(eK D).filter λa=>aL (14+a.1)/\aL (aw D a)/\t (aw D a)=e;let d:∀n,n∈F↔aL n/\t n=e:=λn=>by simp only[F,eT,H,A0];exact⟨λh=>h.2,λh=>⟨e9 h.1,h⟩⟩
 let hA:∀a,a∈A↔a.1<D.length/\aL (14+a.1)/\aL (aw D a)/\t (aw D a)=e:=λa=>by simp[A,eK]
 let Q:A.card=∑n∈F,cF n:=by
  rw[card_eq_sum_card_fiberwise (f:=aw D) (s:=A) (t:=F) λa u=>A1.2 ((d _).2 ((hA a).1 (A1.1 u)).2.2)];refine B2 rfl λn v=>?_;let x:cF n=((eK D).filter λa=>aw D a=n/\aL (14+a.1)).card:=by rw[d8,cF,bV,filter_filter,card_filter];refine B2 rfl λj f=>?_;let b:=(R.1 j (A0.1 f)).2.2;rw[aX,bh];by_cases p:cj D j=n<;>by_cases r:ck D j=n<;>by_cases s:aL (14+j)<;>simp[p,r,s];exact b (p.trans r.symm)
  rw[x];congr 1;ext a;simp only[A,H,eK,mem_product,A0,_mv,and_true];exact⟨λ⟨⟨u,c,_,_⟩,rfl⟩=>⟨u,rfl,c⟩,λ⟨u,rfl,c⟩=>⟨⟨u,c,(d _).1 v⟩,rfl⟩⟩
 let r (a:E):=∃i<G.length,q i=a.1;let c (n:ℕ):=n<14\/∃i<G.length,14+q i=n;let x:=F.filter c;let s:=F.filter λn=>¬c n;let u:=A.filter λa=>¬r a;have:(A.filter r).card+u.card=A.card:=A5 r;have:x.card+s.card=F.card:=A5 c;have:aF G e<=(A.filter r).card:=E2 (λi=>(q i,decide (ck G i=e))) (λi k=>by rw[A1,bV,H,A0]at k;let⟨j,l⟩:=k;let⟨a1,a2,_,a4,a5,a6,a7⟩:=y i j;rw[A1,H,hA];by_cases c:ck G i=e;{simp only[c,decide_true,bh];exact⟨⟨a1,a2,a7,a5▸c⟩,i,j,rfl⟩};simp only[c,decide_false,aX];exact⟨⟨a1,a2,a6,a4▸l.resolve_right c⟩,i,j,rfl⟩) λi k i' k' B=>by let g:q i=q i':=congrArg Prod.fst B;rw[A1,bV,H,A0]at k k';have:=(y i k.1).2.2.1;have:=(y i' k'.1).2.2.1;rw[g]at *;omega
 let p:∀n∈x,n=if l:e<10 then (i0 ⟨e,l⟩).1 else 14+q (e-10):=λn hw=>by rw[H,d]at hw;let⟨⟨c,tw⟩,cw⟩:=hw;rcases cw with m|⟨i,k,rfl⟩;{obtain⟨i,rfl⟩:=eC m c;have:=M i;have:=i.2;let l:e<10:=by{omega};rw[dite_eq_left l];exact congrArg (λk=>(i0 k).1) (_fe (by show i.1=e;omega))};{have:=(y i k).2.2.1;let l:¬e<10:=by{omega};rw[dite_eq_right l,show e-10=i by omega]}
 have:x.card<=1:=A4.2 λa ha b hb=>by rw[p a ha,p b hb]
 have:s.card<=u.card:=by
  let z:∀n,∃a:E,a.1=n-14/\(n∈s->a∈u):=λn=>by
   by_cases v:n∈s;swap;{exact⟨(n-14,false),rfl,λh=>AB h v⟩};let v':=v;rw[H,d,B3]at v';let⟨⟨c,tw⟩,hwn,K⟩:=v';have:=e9 c;let j:=n-14;let U:j<D.length:=by omega
   let L:14+j=n:=by{omega};let K':¬r (j,false):=λ⟨i,k,g⟩=>K ⟨i,k,by omega⟩;let c':aL (14+j):=L.symm▸c;let⟨s,a⟩:=lx U c';exact⟨(j,s),rfl,λ_=>H.2 ⟨(hA _).2 ⟨U,c',a,by rw[(h4 _ U c').resolve_left K' s a,L];exact tw⟩,K'⟩⟩
  choose f f1 f2 using z;refine E2 f (λn v=>A1.2 (f2 n (A1.1 v))) λn v n' v' B=>?_;have:n-14=n'-14:=by{rw[<-f1 n,<-f1 n',B]};rw[A1,H,B3]at v v';omega
 show aF G e+F.card<=∑n∈F,cF n+1;rw[<-Q];omega
lemma n6 (g:∀i:T,∃y y':T->_d,(∀k,k≠i->y k=y' k)/\val D (cf y) (bH 14 D)≠val D (cf y') (bH 14 D)):∃E:Dag,ai 10 E/\(∀y,val E y (bH 10 E)=val D (cf y) (bH 14 D))/\ap 10 E<=kl:=by
 let nY:∃E t q,eg 0 E t q:=by
  choose t l using show ∀n:ℕ,∃r:ℕ,∀i:T,(i0 i).1=n->r=i.1 from λn=>if h:∃i:T,(i0 i).1=n then let⟨i,a⟩:=h;⟨i.1,λi' a'=>by rw[hf.1 (_fe (a.trans a'.symm))]⟩ else ⟨0,λi a=>AB ⟨i,a⟩ h⟩;refine⟨[],t,λ_=>0,λj g=>AB g (by simp),?_,λi a=>AB a (by simp),λj g=>AB g (by simp),λi=>l _ i rfl⟩;intro n a p;let⟨i,h⟩:=eC a p;let e:=l n i h;exact⟨by rw[e];simp,λy=>by rw[e,bY [] y i.1 i.2,bY D _ n a,(_fe h.symm:(⟨n,a⟩:O)=i0 i),dN]⟩
 let oG:∀k,k<=D.length->∃E t q,eg k E t q:=λk=>by induction k with|zero=>exact λ_=>nY|succ k ih=>exact λd=>let⟨E,t,q,p⟩:=ih (by omega);nZ (by omega) p
 let⟨E,t,q,p⟩:=oG _ le_rfl;let j:∀i:T,aL (i0 i).1:=λi=>by let⟨y,y',f,g⟩:=g i;let kk:∀v,v≠i0 i->cf y v=cf y' v:=λv d=>by{cases e:r0 v with|some b=>rw[dw y e,dw y' e]|none=>obtain⟨k,rfl⟩:=(hf.2 v).1 e;rw[dN,dN];exact f k λg=>d (g▸rfl)};refine⟨λl=>g ?_,eG (λ_ _ h=>⟨h.1,λl=>h.2 (l y y')⟩) (d_ R.1 _ _ (i0 i) kk _ g)⟩;let h:=l y y';rw[bY D _ _ (i0 i).2,bY D _ _ (i0 i).2,Fin.eta,dN,dN]at h;rw[(funext λk=>if q:k=i then q▸h else f k q:y=y')]
 let q:∀{e},e<10+E.length->∃n,aL n/\t n=e:=λ{e} d=>by by_cases b:e<10;{exact⟨_,j ⟨e,b⟩,p.2.2.2.2 ⟨e,b⟩⟩};{let⟨_,c,x,_⟩:=p.2.2.1 (e-10) (by omega);exact⟨_,c,by rw[x];omega⟩}
 let r:aL (bH 14 D):=let⟨y,y',_,d⟩:=g 0;⟨λz=>d (z y y'),.refl⟩;let ni:∀{n},aL n->t n<=t (bH 14 D):=by intro n h;obtain⟨e,i⟩:=h;revert e;induction i using HI with|refl=>exact λ_=>le_rfl|@head a b c d ih=>intro e;obtain⟨j,s,k,rfl,rfl⟩:=fj.1 c.1;refine le_trans ?_ (ih c.2);rcases p.2.2.2.1 j k ⟨c.2,d⟩ with ⟨i,hb,ha⟩|l;{let⟨_,_,x,e2,e3,_,_⟩:=p.2.2.1 i hb;let⟨sa,sb,_⟩:=p.1 i hb;rw[ha]at x e2 e3;cases s;{rw[aX,<-e2,x];omega};{rw[bh,<-e3,x];omega}};exact(l s ⟨e,.head c d⟩).le
 let l:t (bH 14 D)=bH 10 E:=by let⟨n,d,f⟩:=q (e:=10+E.length-1) (by omega);have:=ni d;have:=(p.2.1 _ (e9 r) r).1;show t (bH 14 D)=10+E.length-1;omega
 let⟨_,cv⟩:=p.2.1 _ (e9 r) r;rw[l]at cv;let d:E≠[]:=by rintro rfl;let⟨y,y',A,d⟩:=g 0;apply d;rw[<-cv y,<-cv y',show bH 10 []=9 from rfl,bY [] y 9 V,bY [] y' 9 V];exact A _ V
 let x:∀{n},aL n->t n≠t (bH 14 D)->∃i<E.length,cj E i=t n\/ck E i=t n:=by intro n ⟨g,r⟩ d;revert g d;induction r using HI with|refl=>exact λ_ d=>AB rfl d|@head a b c f ih=>intro g d;obtain⟨j,s,u,rfl,rfl⟩:=fj.1 c.1;rcases p.2.2.2.1 j u ⟨c.2,f⟩ with ⟨i,m,k⟩|v;{let⟨_,_,_,e2,e3,_,_⟩:=p.2.2.1 i m;rw[k]at e2 e3;cases s;{exact⟨i,m,.inl (by rw[aX];exact e2)⟩};{exact⟨i,m,.inr (by rw[bh];exact e3)⟩}};have:=v s ⟨g,.head c f⟩;rw[this]at d⊢;exact ih c.2 d
 let f:o7 10 E:=λe le=>by let⟨n,jw,fw⟩:=q (e:=e) (by omega);let⟨i,k,b⟩:=x jw (by rw[l,fw];unfold bH;omega);exact _cp.2 ⟨i,H.2 ⟨A0.2 k,fw▸b⟩⟩
 refine⟨E,⟨p.1,f,d⟩,cv,?_⟩;unfold ap bn kl;let j:∀e∈cD 10 E,aF E e-1<=∑n∈eT t e,(cF n-1):=λe h=>by have:=km p e;let m:∀n∈eT t e,1<=cF n:=λn a=>let⟨z,b,d⟩:=jn (H.1 a).2.1 λf=>by{have:=bP.1 h;have:=(H.1 a).2.2;rw[f,l]at this;unfold bH at this;omega};_cp.2 ⟨z-14,H.2 ⟨dR b,by rw[E3 b.2.1];exact d⟩⟩;have:∑n∈eT t e,(cF n-1)+(eT t e).card=∑n∈eT t e,cF n:=by{rw[card_eq_sum_ones,<-sum_add_distrib];exact B2 rfl λn a=>Nat.sub_add_cancel (m n a)};omega
 let hf:=sum_fiberwise_of_maps_to (s:=(cD 14 D).filter λn=>aL n/\t n∈cD 10 E) (t:=cD 10 E) (g:=t) (λn a=>(H.1 a).2.2) λn=>cF n-1;let b:(cD 14 D).filter (λn=>aL n/\t n∈cD 10 E)⊆(cD 14 D).filter aL:=λn s=>by rw[H]at s⊢;exact⟨s.1,s.2.1⟩
 refine((sum_le_sum j).trans (le_of_eq ?_)).trans (sum_le_sum_of_subset b);rw[<-hf];refine B2 rfl λe h=>B2 ?_ λ_ _=>rfl;ext n;simp only[eT,H,A0];exact⟨λ⟨a,lw,he⟩=>⟨⟨bP.2 (by let c:=bP.1 h;by_contra f;let b:n=bH 14 D:=by{unfold bH;omega};rw[b,l]at he;rw[<-he]at c;unfold bH at c;omega),lw,he▸h⟩,he⟩,λ⟨⟨a,lw,_⟩,rfl⟩=>⟨by have:=bP.1 a;omega,lw,rfl⟩⟩
lemma lB {x v:O}(m:r0 v=some true){b:ℕ}(l:b∈aR 14 D x v)(p:2<=aF D b)(a:bn D (aR 14 D x v)=1){e:E}(q:e∈aE 14 D (aR 14 D x v))(h:v∈ag 14 D (14+e.1)):cF b<=1:=by
 let K:=aR 14 D x v;let r (a z:ℕ):=bk 14 D a z/\a∈K/\z∈K;have:=add_sum_erase K (λu=>aF D u-1) l;change ∑u∈K,(aF D u-1)=1 at a;let u:∀n∈K,n≠b->aF D n<=1:=λn y i=>by have:=single_le_sum (f:=λu=>aF D u-1) (λ_ _=>Nat.zero_le _) (_me.2 ⟨i,y⟩);omega
 let mQ:∀n∈K,RT r x.1 n:=λn=>by
  induction n using Nat.strong_induction_on with
 |_ n ih=>
   intro y;let⟨z,f,hg⟩:n<14+D.length/\x∈ag 14 D n/\v∉ag 14 D n:=by simpa[K,aR] using y
   by_cases t:n<14;{rw[dr D ⟨n,t⟩,D3]at f;rw[(by rw[f]:x.1=n)]};obtain⟨j,rfl⟩:∃j,n=14+j:=⟨n-14,by omega⟩;let n:j<D.length:=by omega
   let d:∀s:_d,x∈ag 14 D (aw D (j,s))->v∉ag 14 D (aw D (j,s))->RT r x.1 (14+j):=λs i B=>by let hs:=dh R.1 n s;let hK:aw D (j,s)∈K:=by{simpa[K,aR] using ⟨by omega,i,B⟩};exact .tail (ih _ hs hK) ⟨cM n s,hK,y⟩
   cases y:cR D j
   · rw[de R.1 n y,_mu]at f hg;rcases f with i|i;exacts[d false ((aX j).symm▸i) ((aX j).symm▸λh=>hg (.inl h)),d true ((bh j).symm▸i) ((bh j).symm▸λh=>hg (.inr h))]
   · rw[cB R.1 n y,_mn]at f hg;by_cases i:v∈ag 14 D (cj D j);exacts[d true ((bh j).symm▸f.2) ((bh j).symm▸λh=>hg ⟨i,h⟩),d false ((aX j).symm▸f.1) ((aX j).symm▸i)]
 let⟨F,s,G⟩:=H.1 q;let d:e.1<D.length:=by simpa[eK] using F
 let n:∀a z,a∈K->bk 14 D a z->¬aL z->(∀z',z'=z->¬(z'∈K/\RT r z' b))->(∃j∈bV D b,¬aL (14+j))\/(¬aL a/\¬RT r a b):=λa z g J U a1=>by
  by_cases i:a=b;{exact .inl ⟨z-14,i▸dR J,by rw[E3 J.2.1];exact U⟩};let y:aF D a=1:=by have:=u a g i;have:=ef J;omega
  let g:∀z',bk 14 D a z'->z'=z:=λz' J'=>dS J' J y;refine .inr ⟨λL=>by let⟨z',J',U'⟩:=jn L (by have:=dc R.1 (ef J);unfold bH;omega);rw[g z' J']at U';exact U U',λC=>?_⟩;rcases C.cases_head with t|⟨z',J',c'⟩;{exact i t};{exact a1 z' (g z' J'.1) ⟨J'.2.2,c'⟩}
 let B:∀a,RT r a (aw D e)->(∃j∈bV D b,¬aL (14+j))\/(¬aL a/\¬RT r a b):=λa C=>by
  induction C using HI with
 |refl=>exact n _ _ s (cM d e.2) (fX m h) λz' h' ⟨hz,_⟩=>G (h'▸hz)
 |@head a z f c ih=>exact ih.elim .inl λ⟨E,P⟩=>n a z f.2.1 f.1 E λz' h' ⟨_,c'⟩=>P (h'▸c')
 let⟨j,t,k⟩:=(B x.1 (mQ _ s)).resolve_right λ⟨_,h⟩=>h (mQ b l);have:cF b<aF D b:=card_lt_card (filter_ssubset.2 ⟨j,t,k⟩);omega
end CofRestrict
def gE (x u:O):Option _d:=if u=x then some true else if ab x u=true then some false else none
def eD (l:_F ℕ)(k:T):O:=Fin.ofNat 14 (l.getD k.1 0)
abbrev C6 (x:O)(l:_F ℕ):Prop:=(∀a b:T,eD l a=eD l b->a=b)/\(∀u,gE x u=none↔∃i:T,eD l i=u)/\∀u y:T,ab (eD l u) (eD l y)=gV u y
lemma om:C6 7 [2,4,5,6,13,12,8,10,11,9]:=Z
lemma oo:C6 3 [8,9,10,13,6,0,2,5,1,4]:=Z
lemma oM {x:O}{l:_F ℕ}(r:C6 x l)(hx:x∈L)(s0:o)(hX:∀y∈s0,y∈L/\y≠x/\(∀u∈J,y∈G u.1->x∈G u.1)/\∃q,y∈G q/\x∈G q):(Y x).card+s0.card+7<=P:=by
 classical
 let⟨r',hr'⟩:∃r',r'=gE x:=⟨_,rfl⟩;let⟨i',hi'⟩:∃i',i'=eD l:=⟨_,rfl⟩;let _:CR True:=⟨r',i',⟨λa b m=>r.1 a b (by rw[<-hi'];exact m),λu=>by show r' u=none↔∃i,i' i=u;rw[hr',hi'];exact r.2.1 u⟩⟩;let n:CR.r0 x=some true:=by show r' x=some true;rw[hr'];simp[gE]
 let hT:∀d a,r' d=some true->aO d a->r' a=some false:=λd a p t=>by rw[hr']at p⊢;have m:d=x:=C λh0=>by{simp[gE,h0]at p};subst m;simp[gE,show a≠d from λm=>dv d (m▸t),D2 t]
 let qU:∀y:T->_d,cN aO (cf y)↔cN bI y:=λy=>by
  let s:∀u q,aO u q->cf y u=true->cf y q=true->∃i,i' i=u/\y i=true:=λu q d g k=>by cases hl:r' u with|none=>obtain⟨i,rfl⟩:=(CR.hf (q1:=True)).2 u |>.1 hl;rw[dN]at g;exact⟨i,rfl,g⟩|some b=>rw[dw y hl]at g;subst g;rw[dw y (hT u q hl d)]at k;exact AB k _fnt
  let m:∀a b:T,aO (i' a) (i' b)↔bI a b:=λa b=>by rw[hi'];show aO (eD l a) (eD l b)↔gV a b=true;rw[<-r.2.2 a b];exact(ad _ _).symm
  exact⟨λ⟨u,q,d,g,k⟩=>by obtain⟨i,rfl,p⟩:=s u q d g k;obtain⟨j,rfl,p'⟩:=s q _ (bl d) k g;exact⟨i,j,(m i j).1 d,p,p'⟩,λ⟨i,j,d,p,p'⟩=>⟨i' i,i' j,(m i j).2 d,(dN y i).trans p,(dN y j).trans p'⟩⟩
 let hb:∀y,val D (cf y) (bH 14 D)=true↔cN bI y:=λy=>(kO kC _).trans (qU y);let⟨E1,hE,a1,m⟩:=n6 λi=>by let⟨a,s,_⟩:=eS.2.2.2 i i;refine⟨cl a,bB i (cl a),dd i _,λp=>?_⟩;let h:=(hb (bB i (cl a))).2 ⟨i,a,s,dm i _,by simp[bB,cl]⟩;rw[<-p]at h;exact dF eS a ((hb _).1 h)
 let k:∀y∈insert x s0,y∈L:=λy f=>(D4.1 f).elim (·▸hx) λf=>(hX y f).1;let i (y:O):U:=⟨b0 y,0⟩;let p:=Y x∪(insert x s0).image i;let m:Set.InjOn i (insert x s0:o):=λy f y' fy s=>by let h2:b0 y=b0 y':=congrArg Sigma.fst s;let t:=(kM y (k y f)).2;rw[h2,(kM y' (k y' fy)).2]at t;exact(singleton_injective t).symm
 let t:Disjoint (Y x) ((insert x s0).image i):=_dl.2 λ_ s h0=>by{obtain⟨y,f,rfl⟩:=_mg.1 h0;exact(_md.1 (yM s).1).2 (_mg.2 ⟨y,k y f,rfl⟩)};let q:p⊆dq 14 D:=λ_ g=>(_mu.1 g).elim (λg=>(H.1 (_md.1 (yM g).1).1).1) λg=>by{obtain⟨y,f,rfl⟩:=_mg.1 g;have:=(kM y (k y f)).1;exact dW.2 ⟨bP.2 (dc R.1 (w:=b0 y) (by omega)),by show 0+1<aF D (b0 y);omega⟩};let j:∀u∈p,u∉f5:=λ_ g=>(_mu.1 g).elim (λg h=>fX n (yM g).2 (H.1 h).2.1) λg=>by{obtain⟨y,f,rfl⟩:=_mg.1 g;rcases D4.1 f with rfl|f;{exact λh=>fX n (by show y∈ag 14 D (b0 y);rw[(kM y hx).2];exact D1 y) (H.1 h).2.1};let⟨c1,s,c,_,hq⟩:=hX y f;let⟨_,h3,h4⟩:=aK.2.2.1 y x s;let⟨h5,_,_,e,he,_,h6⟩:=gt aK R kC b0 kM s c1 c hq h3 h4;let hl:=lB n (f_.2 (by show y∈ag 14 D (b0 y)/\x∉ag 14 D (b0 y);rw[(kM y c1).2];exact⟨D1 y,λc=>s (D3.1 c).symm⟩)) (kM y c1).1 h5 he h6;exact λh=>by{have:=(H.1 h).2.2;dsimp[i]at this;omega}};let c:f5=((cD 14 D).filter aL).sigma λn=>range (cF n-1):=by{ext u;have:=_cfl (bV D u.1) (λj=>aL (14+j));change cF u.1<=aF D u.1 at this;simp[f5,dq];exact⟨λ⟨⟨a,_⟩,b,d⟩=>⟨⟨a,b⟩,by omega⟩,λ⟨⟨a,b⟩,d⟩=>⟨⟨a,by omega⟩,b,by omega⟩⟩};let a:kl+p.card<=ap 14 D:=by{let b:kl=f5.card:=by{rw[c,card_sigma];simp[kl]};rw[b,<-mv,<-_cud (_dl.2 λu s h2=>j u h2 s)];exact _cl (B1 (_fs _ _) q)};dsimp[p]at a;rw[_cud t,_cij m,_cin λb=>(hX x b).2.1 rfl]at a;have:=jO hE (ju eS λy=>by rw[a1 y];exact hb y);have:=dC 10 E1;dsimp[P]at *;omega
def iP (a b:E):Prop:=(∀x,(F x).card<=3)/\a≠b/\∀x,3<=(F x).card->a∈F x/\b∈F x
lemma oq (q:0∈A)(s:L.card=12:=by omega):∃e1 e2,iP e1 e2:=by have:=ar;let a:B=13:=C λr=>C4 q;let d:∀x,(F x).card<=3:=λx=>by{have:=bi x;have:(Y x).card<=J.card:=_cfl _ _;omega};by_cases n:(univ.filter λx:O=>3<=(F x).card).Nonempty;{let⟨e1,e2,k,e⟩:=fW aK R kC b0 ku (by show B=L.card+1;rw[a,s]) _ n λx f=>(H.1 f).2;exact⟨e1,e2,d,λl=>k (l▸rfl),λx f=>e x (H.2 ⟨_mv x,f⟩)⟩};exact⟨(0,false),(1,false),d,V,λx f=>(n ⟨x,H.2 ⟨_mv x,f⟩⟩).elim⟩
lemma nn (hA:A={0,1}):False:=by
 let h:=C7 hA 2;let b:0∈A:=hA▸V;let d:1∈A:=hA▸V;let k:∀x,x∉O0->x∉A:=λ_ r=>hA▸r;let u:∀i∈A,aO i 7:=by rw[hA];decide
 let⟨a,f,hB,hW,h3⟩:=oq b;let a:=λi g=>aI g (u i g);let c0:=zI b d V;let⟨c,t,_,n,_⟩:=be (x:=7) (y:=3) V;let⟨f,hY⟩:=h3 7 (d5 (a 0 b) (a 1 d) t c0 (λh=>AB (n 0 b h.symm) V) (λh=>AB (n 1 d h.symm) V));let c:∀t,3<=(F t).card->∀j∈A,z j∈F t:=λt ht j m=>C λn=>let⟨g,s⟩:=h3 t ht;let⟨q,y,a4,_,a3⟩:=sI j 7 t (D2 (u j m)) λu=>by{rw[u,pn m,_cs]at ht;omega};oN (λe:(7:O)=t=>n (e▸a j m)) a4.symm (aG.1 a3) λe h=>by{rcases aS (a j m) f hY (λe=>n (e▸g)) (λe=>n (e▸s)) hW (hB 7) e h with rfl|rfl|rfl;exacts[.inr (aI m (N y)),.inl g,.inl s]};let n:∀l i x:O,i∈A->aO i l->aO l x->x∉A->∃e∈F l,(∀f∈F l,f=e\/∃j∈A,f=z j)/\∀y,aO l y->y∉A->am e∈F y:=λl i x g a1 a2 r=>let⟨e,s,_,h4,_⟩:=be a2;let f:∀j∈A,z j≠e:=λj m h=>r (h4 j m h.symm▸m);let r:∀q∈F l,q=e\/∃j∈A,q=z j:=λq h=>if t:3<=(F l).card then by{rcases aS (c l t 0 b) (c l t 1 d) s c0 (f 0 b) (f 1 d) (hB l) q h with rfl|rfl|rfl;exacts[.inr ⟨0,b,rfl⟩,.inr ⟨1,d,rfl⟩,.inl rfl]} else by{rcases gF (aI g a1) s (f i g) (by omega) q h with rfl|rfl;exacts[.inr ⟨i,g,rfl⟩,.inl rfl]};⟨e,s,r,λy u hy=>let⟨q,h,hb,hf,_⟩:=be u;(r q h).elim (·▸hb) λ⟨j,m,e'⟩=>(hy (hf j m e'▸m)).elim⟩;let f:=k 2 V;let⟨e8,u,r,q⟩:=n 8 0 2 b V V f;let⟨e3,p,_,b3⟩:=n 13 1 2 d V V f;let x:=q 2 V f;let n:=b3 2 V f;let f:am e8≠am e3:=λh=>by let g:e8=e3:=C8 h;exact oN (x:=8) (a:=7) (b:=13) V V V λe h=>(r e h).elim (λe=>.inr (e▸g▸p)) λ⟨j,m,e⟩=>.inl (e▸a j m)
 let r:∀(e:E) (l i:O),e∈F l->i∈A->l∉O0->z i≠am e:=λe l i g s hl h=>k l hl (ei s ((C9 h.symm).symm▸g)▸s);by_cases t:3<=(F 2).card;{rcases aS (c 2 t 0 b) (c 2 t 1 d) x c0 (r e8 8 0 u b V) (r e8 8 1 u d V) (hB 2) _ n with k|k|k;exacts[r e3 13 0 p b V k.symm,r e3 13 1 p d V k.symm,f k.symm]};exact oN (x:=2) (a:=6) (b:=4) V V V λe h=>by{rcases gF x n f (by omega) e h with rfl|rfl;exacts[.inl (q 6 V (k 6 V)),.inr (b3 4 V (k 4 V))]}
lemma dk (x k y h c:O)(b:(∀a∈({h,c}:o),a∈A)/\∀a∈({x,k,y}:o),a∉A)(h1:I h x/\I c k/\I x k/\I x y/\y≠k)(l:(F x).card<=2:=by omega)(m:(F k).card<=2:=by omega):False:=by let⟨j,q,r,s,u⟩:=h1;let d:=b.1 h (by simp);let f:=b.1 c (by simp);let i:=b.2 k (by simp);let⟨dk,_,n,p⟩:=sF f (λe:k=c=>i (e▸f)) (aI f (N q)) m;let⟨e,h2,g,h3,h4⟩:=be (N r);let⟨e',y',g',x',_⟩:=be (N s);rw[n,D4,D3]at g;let n:am e=dk:=g.resolve_left λt=>b.2 x (by simp) (h4 c f t▸f);rcases gF (aI d (N j)) h2 (λt=>i (h3 h d t.symm▸d)) l e' y' with rfl|rfl;exacts[b.2 y (by simp) (x' h d rfl▸d),p y u (n▸g')]
lemma mS (hA:A={0,9}):False:=by
 have:=C7 hA 2;let n:o:={0,9};let hA':A=n:=hA;let rA:=hA'.symm;let⟨e1,e2,h1,h2,g⟩:=oq (hA▸V)
 let no (y:O):=∃e,(e=e1\/e=e2)/\(∀i∈A,e≠z i)/\(∀s,s≠y->am e∉F s)/\am e∈F y/\∃i∈A,z i=e1\/z i=e2;let lD:∀(x y t q ix p xa xb:O),(ix∈n/\p∈n/\x∉n/\y∉n/\q∉n/\I ix x/\I p y/\I x y/\I q y/\I ix t/\ix≠p/\x≠q/\x≠t/\x≠xa/\x≠xb/\B0 q xa/\B0 q xb/\B0 t xa/\B0 t xb)->3<=(F x).card->(3<=(F xa).card\/3<=(F xb).card)->no y:=λx y t q ix p xa xb ⟨gl,gd,u,a8,a7,g1,g2,g3,g4,g5,g0,g6,g7,g8,g9,a3,a4,a5,a6⟩ c k=>by
  let l:ix∈A:=rA▸gl;let d:p∈A:=rA▸gd;let hx:x∉A:=rA▸u;let hy:y∉A:=rA▸a8;let⟨u,hu,a8,a9,b1⟩:∃u,3<=(F u).card/\x≠u/\¬aO q u/\¬aO t u:=k.elim (λh=>⟨xa,h,g8,aG.1 a3,aG.1 a5⟩) λh=>⟨xb,h,g9,aG.1 a4,aG.1 a6⟩;let⟨h3,c1⟩:=g x c;let⟨e,T1,m,hf,hf'⟩:=be (N g3);let⟨e',T',m',_,h4⟩:=be (N g4);let c:∀(a:E) (s:O),a∈F x->a∈F s->x≠s->¬aO s u->a=e1\/a=e2:=λa s r h7 h0 h8=>C λn=>by rw[B3]at n;exact oN h0 a8 h8 λf h=>by{rcases aS h3 c1 r h2 (nS n.1) (nS n.2) (h1 x) f h with rfl|rfl|rfl;exacts[.inr (g u hu).1,.inr (g u hu).2,.inl h7]}
  let k:=c (z ix) t (aI l (N g1)) (aI l (N g5)) g7 b1;let t:(∀a∈F y,a=am e\/∃i∈A,a=z i)->e=e1\/e=e2:=λhA'=>c e q T1 (by rcases hA' _ m' with f|⟨i,r,f⟩;{exact C8 f.symm▸T'};exact((rA▸a7) (h4 i r f▸r)).elim) g6 a9;by_cases r:(F y).card<=2;{let⟨dy,_,j,h7⟩:=sF d (λe:y=p=>hy (e▸d)) (aI d (N g2)) r;let c:am e=dy:=by{rw[j,D4,D3]at m;exact m.resolve_left λr=>hx (hf' p d r▸d)};exact⟨e,t λa ha=>f2 (p:=λa=>a=am e\/∃i∈A,a=z i) (.inr ⟨p,d,rfl⟩) (.inl c.symm) a (j▸ha),λi h8 b2=>hy (hf i h8 b2▸h8),λs h8=>c▸h7 s h8,c▸(j▸B8 (D1 _)),ix,l,k⟩};exfalso;let⟨h7,h8⟩:=g y (by omega);let j:=aS h7 h8 m h2 (λr=>eh R.1 T1 (r▸h3)) (λr=>eh R.1 T1 (r▸c1)) (h1 y);let q:z p=e1\/z p=e2:=by rcases j _ (aI d (N g2)) with f|f|f;exacts[.inl f,.inr f,(hx (hf' p d f.symm▸d)).elim]
  let n:=zI l d g0;let s:∀c,c=e1\/c=e2->∃i∈A,c=z i:=λc u=>by rcases u with rfl|rfl<;>rcases k with f|f<;>rcases q with h0|h0<;>first|exact⟨ix,l,f.symm⟩|exact⟨p,d,h0.symm⟩|exact(n (f.trans h0.symm)).elim
  rcases t λa ha=>(j a ha).elim (λf=>.inr (s a (.inl f))) λf=>f.elim (λh0=>.inr (s a (.inr h0))) .inl with rfl|rfl;exacts[eh R.1 h7 m,eh R.1 h8 m]
 let j:3<=(F 1).card\/3<=(F 7).card:=C λl=>dk 1 7 13 9 0 (by rw[hA];decide) V;let k:3<=(F 6).card\/3<=(F 8).card:=C λl=>dk 6 8 11 9 0 (by rw[hA];decide) V;let c:∀{y1 y2:O},y1≠y2->no y1->no y2->False:=λa ⟨a1,b,h1,d,_,i,l,e⟩ ⟨a2,h2,g',_,h,_⟩=>d _ a.symm ((by rcases b with rfl|rfl<;>rcases h2 with rfl|rfl<;>rcases e with r|r<;>first|rfl|exact AB r.symm (h1 i l)|exact AB r.symm (g' i l):a2=a1)▸h);let m:no 7\/no 1:=j.elim (λe=>.inl (lD 1 7 5 3 9 0 6 8 V e k)) λe=>.inr (lD 7 1 10 13 0 9 6 8 V e k);let n:no 8\/no 6:=k.elim (λe=>.inl (lD 6 8 5 2 9 0 1 7 V e j)) λe=>.inr (lD 8 6 10 11 0 9 1 7 V e j);rcases m with a|a<;>rcases n with b|b<;>exact c V a b
def di (l:_F O)(k:Fin 4):O:=l.getD k.1 0
lemma nq (hA:A={0,1,3}):False:=by
 let np:o:={8,9,10,11,12,13};let S3:o:={0,1,3};let kr:Finset E:=A.image z;let hA':A=S3:=hA;let rA:=hA'.symm;let⟨g1,g2,g3,g4⟩:(∀i∈S3,I i 7)/\(∀t,t∉S3->B0 7 t)/\(∀l∈np,l∉S3/\l≠7/\(∃i∈S3,I i l)/\∃x,I l x/\x∉S3)/\∀t,t∉S3->t≠7->∀i∈S3,∃q,I i q/\q≠7/\B0 q t:=⟨Z,Z,Z,Z⟩;let k7:7∈L:=nL (rA▸V);let hY:∀i∈A,z i∈F 7:=λi h=>aI h (N (g1 i (hA'▸h)));let n:kr⊆F 7:=fi hY;let hW:kr.card=3:=(_cij λ_ h _ hj=>kp.2 _ h _ hj).trans (by change A.card=3;rw[hA];rfl);let h7:=_cl n;rw[hW]at h7;have:=me k7;have:=C7 hA 3;by_cases hG:∀u∈J,7∈G u.1;{have:=oM om k7 np λx y=>let⟨h2,h3,⟨i,h,a5⟩,_⟩:=g3 x y;let hi:i∈A:=rA▸h;⟨nL (rA▸h2),h3,λu d _=>hG u d,v i,go hi (N a5),go hi (N (g1 i h))⟩;rw[(V:np.card=6)]at this;omega};let⟨u2,d⟩:=not_forall.1 hG;let⟨hL,a3⟩:=Classical.not_imp.1 d;let p:Y 7⊆J.erase u2:=λu d=>_me.2 ⟨λm=>a3 (m▸(yM d).2),(yM d).1⟩;let a5:=_cl p;rw[A2 hL]at a5;let⟨u1,a5⟩:=_c1.1 (show (Y 7).card=1 by omega);let c:u1∈Y 7:=a5▸D1 _;let⟨a4,h2⟩:=yM c;let r:∀u∈J,u≠u2->u=u1:=λu d g=>A4.1 (by rw[A2 hL];omega) u (_me.2 ⟨g,d⟩) u1 (p c);let hM:kr=F 7:=C2 n (by rw[hW];omega);let a:∀t,t∈G u1.1->t=7:=λt ht=>C λs=>by let⟨e0,h3⟩:=jX (nS s) k7 (λu d b3=>r u d (λm=>a3 (m▸b3))▸ht) ⟨h2,ht⟩;let⟨i3,h4,h0⟩:∃i3∈A,∀i∈A,i≠i3->t∈G (v i):=if hc:∃i3∈A,z i3=e0 then let⟨i3,h4,m⟩:=hc;⟨i3,h4,λi h g=>h3 _ (hY i h) λhh=>g (kp.2 i h i3 h4 (hh.trans m.symm))⟩ else ⟨0,hA'▸V,λi h _=>h3 _ (hY i h) λhh=>hc ⟨i,h,hh⟩⟩;let⟨q,a7,a9,a8⟩:=g4 t (λhc=>ha.1 (rA▸hc) (fB a4 ht)) s i3 (hA'▸h4);let⟨e,m,h5,h6⟩:=bR (nS s) a9.symm λh8=>aG.1 a8 (bl h8);obtain⟨i,h,rfl⟩:=_mg.1 (hM.symm▸m);exact if h8:i=i3 then by{subst h8;exact h6 (go h (N a7))} else h5 (h0 i h h8)
 let c0:∀x,x≠7->∀u∈Y x,u=u2:=λx y u d=>C λg=>y (a x (r u (yM d).1 g▸(yM d).2));let h3:∀x,x≠7->(F x).card<=3/\(3<=(F x).card->W x=∅/\x∈G u2.1/\∀q∈J,x∈G q.1->q=u2):=λx y=>by have:=bi x;have:(Y x).card<=1:=A4.2 λu d q hq=>(c0 x y u d).trans (c0 x y q hq).symm;refine⟨by omega,λ_=>?_⟩;let⟨u,d⟩:=C1 (Y x);exact⟨C3,c0 x y u d▸(yM d).2,λq hq b6=>c0 x y q (H.2 ⟨hq,b6⟩)⟩
 let mf (l:O):=∃e1 e2,e1∈F l/\e2∈F l/\e1≠e2/\e1∉kr/\e2∉kr;let oO (l:O):=∃e:E,am e∈F l/\(∀t,am e∈F t->t=l)/\∀x,aO l x->x∈L->e∈F x;let hO:∀l∈np,¬mf l->oO l:=λl h4 s=>by
  let⟨_,q,_,x0,hx,b5⟩:=g3 l h4;let d:=nL (rA▸b5);let pt:∀{y:O},y∈L->∀{e:E},am e∈F y->e∉kr:=λ{_} hy {_} he f=>let⟨_,b,k⟩:=_mg.1 f;lH b hy he k.symm;let⟨e,h1,x,_⟩:=kG (N hx);let b:∀f∈F l,f=e\/f∈kr:=λf g=>C λh=>by rw[B3]at h;exact s ⟨e,f,h1,g,nS h.1,pt d x,h.2⟩
  refine⟨am e,(aB e).symm▸h1,λt j=>?_,λx a3 h2=>let⟨f,g,p,_⟩:=kG a3;(b f g).elim (·▸p) λh=>AB h (pt h2 p)⟩;rw[aB]at j;let j:=eW j;by_contra k;by_cases m:t∈A;{let h2:l∈ag 14 D (w e):=eW h1;rw[jh aK R.1 kC m j,D3]at h2;exact k h2.symm};let⟨f,g,c,j'⟩:=bR q (nS k) (aG.1 (g2 t (hA'▸m)));exact(b f g).elim (λh=>j' (h▸j)) λh=>let⟨i,h2,k⟩:=_mg.1 h;c (k▸go h2 (N (g1 i (hA'▸h2))))
 let qi:∀{l t i j:O},l≠7->t≠7->l≠t->t∉A->l∈L->i∈A->j∈A->aO i l->aO j t->mf l->mf t->i=j:=λ{l t i j} q ht hl a hL r hj h1 a1 a2 h2=>by
  let y:∀{x k:O},x≠7->k∈A->aO k x->mf x->3<=(F x).card/\∃e1 e2,e1∉kr/\e2∉kr/\F x={z k,e1,e2}:=λ{x k} h3' hk h4 ⟨e1,e2,h5,h6,h7,f,g⟩=>let hk':z k∈kr:=A6 z hk;let b:z k≠e1:=λe=>f (e▸hk');let h:z k≠e2:=λe=>g (e▸hk');⟨d5 (aI hk h4) h5 h6 b h h7,e1,e2,f,g,(_eqc (by simp[A8,aI hk h4,h5,h6]) (by rw[_cin (by simp[b,h]),_c2 h7];exact(h3 x h3').1)).symm⟩;let⟨a4,e1,e2,f,g,m⟩:=y q r h1 a2;let⟨a',e3,e4,f',g',h3'⟩:=y ht hj a1 h2;let⟨_,h4,a3⟩:=(h3 l q).2 a4;let c:=((h3 t ht).2 a').2.1;let⟨e0,s⟩:=jX hl hL (λu hu h5=>a3 u hu h5▸c) ⟨h4,c⟩;let r':z i∈kr:=A6 z r;by_cases b:z i=e0;{exfalso;let h5:=s e1 (m▸B8 (B9 _ _)) λe=>f (by rw[e,<-b];exact r');let d:=s e2 (m▸B8 (B8 (D1 _))) λe=>g (by rw[e,<-b];exact r');let⟨e,he,h7,ht'⟩:=bR q hl (aG.1 (g2 t (hA'▸a)));rw[m]at he;simp at he;rcases he with rfl|rfl|rfl;exacts[h7 (go r (N (g1 i (hA'▸r)))),ht' h5,ht' d]};let d:=lI r (s (z i) (m▸B9 _ _) b);rw[h3']at d;simp at d;rcases d with d|d|d;exacts[kp.2 i r j hj d,AB (d▸r') f',AB (d▸r') g']
 let⟨i0,f,b1⟩:∃i0∈A,∀l∈np,B0 i0 l->oO l:=by by_cases x:∃b∈np,mf b;swap;{exact⟨0,hA'▸V,λl h4 _=>hO l h4 λa2=>x ⟨l,h4,a2⟩⟩};let⟨b,t,h⟩:=x;let⟨a6,h4,⟨i0,f,h5⟩,_⟩:=g3 b t;refine⟨i0,rA▸f,λl h6 a1=>hO l h6 λa2=>?_⟩;let⟨b2,s,⟨j,hj,h8⟩,_⟩:=g3 l h6;let g:b≠l:=λm=>by{dsimp[I,B0]at h5 a1;rw[m,a1]at h5;exact _fnt h5};let e0:=qi h4 s g (rA▸b2) (nL (rA▸a6)) (rA▸f) (rA▸hj) (N h5) (N h8) h a2;dsimp[I,B0]at h8 a1;rw[e0,h8]at a1;exact _fnt a1.symm
 let b:∀(zl ll:_F O),((∀k:Fin 4,I (di ll k) (di zl k)/\I (di ll k) (di zl (k+1))/\di zl k≠7/\di zl k∉S3)/\∀k m,k≠m->di zl k≠di zl m/\B0 (di zl k) (di zl m)/\di ll k≠di ll m)->(∀k,di ll k∈np/\B0 i0 (di ll k))->False:=λzl ll ⟨g,i⟩ hk=>by
  choose f c hJ r using λk=>b1 _ (hk k).1 (hk k).2;let u:∀k:Fin 4,k-1≠k/\k+1≠k/\k+1≠k-1/\k-1+1=k:=V;let h1:∀k,di zl k∈L:=λk=>nL (rA▸(g k).2.2.2);let j:=λk=>r k _ (N (g k).1) (h1 k);let l:=λk=>r k _ (N (g k).2.1) (h1 _);let h:∀k m:Fin 4,k≠m->f k≠f m:=λk m hK e=>(i k m hK).2.2 (hJ m _ (e▸c k));let n:=λk=>(i _ _ (u k).2.1.symm).1;let hY:∀k,3<=(F (di zl k)).card:=λk=>C λq=>by let h2:f (k-1)∈F (di zl k):=by{have:=l (k-1);rwa[(u k).2.2.2]at this};let⟨e,h3',a,hb'⟩:=bR (n k) (i k (k-1) (u k).1.symm).1 (aG.1 (i _ _ (u k).2.2.1).2.1);rcases gF (j k) h2 (h _ _ (u k).1.symm) (by omega) e h3' with rfl|rfl;exacts[a (eW (l k)),hb' (eW (j (k-1)))]
  let⟨e1,a1,a2,y⟩:=pi aK R kC b0 ku hL (univ.image (di zl)) ⟨_,A6 _ (_mv 0)⟩ (fi λk _=>(h3 _ (g k).2.2.1).2 (hY k));let h2:=λk=>y _ (A6 _ (_mv k));let p:∀k,f k=e1\/f k=a1:=λk=>C λq=>by rw[B3]at q;let⟨e,h4,a,_⟩:=bR (n k) (n k) (dv _);rcases aS (h2 k).1 (h2 k).2 (j k) (λe=>a2 (e▸rfl)) (nS q.1) (nS q.2) (h3 _ (g k).2.2.1).1 e h4 with rfl|rfl|rfl;exacts[a (eW (h2 _).1),a (eW (h2 _).2),a (eW (l k))]
  rcases p 0 with a|a<;>rcases p 1 with h3'|h3'<;>rcases p 2 with d|d<;>first|exact h 0 1 V (a.trans h3'.symm)|exact h 0 2 V (a.trans d.symm)|exact h 1 2 V (h3'.trans d.symm)
 rw[hA]at f;simp at f;rcases f with rfl|rfl|rfl;exacts[b [5,6,4,2] [9,11,13,12] Z Z,b [2,6,4,5] [8,11,10,12] Z Z,b [2,6,5,4] [8,9,10,13] Z Z]
lemma mT (hA:A={0,1,11}):False:=by
 let S1:o:={0,1,11};let i0:0∈A:=hA▸V;let m:1∈A:=hA▸V;let i2:11∈A:=hA▸V;let n:∀x,x∉S1->x∈L:=λ_ h=>nL (hA.symm▸h);let b1:∀x∈L,∀i∈A,x≠i:=λ_ h _ d e=>ha.1 d (e▸h);let e7:=n 7 V;let e3:=n 3 V;let⟨k,hH,h3,a2,_⟩:=z2 (x:=7) (y:=3) V e7 e3;let a0:=aI i0 (a:=7) V;let a1:=aI m (a:=7) V;let a7:=zI i0 m V;let⟨k,t2⟩:=gL a0 a1 hH a7 (a2 0 i0).1.symm (a2 1 m).1.symm;have:=me e7;have:=C7 hA 3;have:(Y 7).card<=J.card:=_cfl _ _;let lw:∀(u:U) (x:O),(∀q∈J,x∈G q.1->q=u)->(F x).card+(W x).card<=3/\(x∉G u.1->(F x).card<=2):=λu x h=>by have:=bi x;have:(Y x).card<=1:=A4.2 λa ha b hb=>(h a (yM ha).1 (yM ha).2).trans (h b (yM hb).1 (yM hb).2).symm;exact⟨by omega,λhn=>by have:(Y x).card=0:=A3.2 (A9.2 λq hq b2=>hn (h q hq b2▸b2));omega⟩
 let a:(Y 7).card≠2:=λa=>by
  let hE:Y 7=J:=C2 (_fs _ _);let a:∀u∈J,7∈G u.1:=λu h=>(yM (hE.symm▸h)).2;let⟨y,b3,q,b5,k⟩:∃y:O,(y=3\/y=12)/\∃q,y∈G q/\7∈G q:=by by_cases h2:∃u∈J,3∈G u.1;{let⟨u,h,r⟩:=h2;exact⟨3,.inl rfl,u.1,r,a u h⟩};have:(Y 3).card=0:=A3.2 (A9.2 λu h r=>h2 ⟨u,h,r⟩);have:=bi 3;let⟨e,_,he,_⟩:=sF i2 V (aI i2 (a:=3) V);let⟨g,hg,a8,c8,_⟩:=z2 (x:=3) (y:=12) V e3 (n 12 V);rw[he,D4,D3]at hg h3;rw[hg.resolve_left (c8 11 i2).1,<-h3.resolve_left (a2 11 i2).2,aB]at a8;exact⟨12,.inr rfl,_,eW a8,eW hH⟩
  let b:∀x∈insert y O8,x∈L/\x≠7/\(∀u∈J,x∈G u.1->7∈G u.1)/\∃q,x∈G q/\7∈G q:=λx hx=>(D4.1 hx).elim (λe=>by subst e;rcases b3 with rfl|rfl;exacts[⟨e3,V,λu h _=>a u h,q,b5,k⟩,⟨n 12 V,V,λu h _=>a u h,q,b5,k⟩]) λhx=>let⟨g1,g2,i,g3,g4,g5⟩:=(V:∀x∈O8,x∉S1/\x≠7/\∃i∈O0,I i x/\I i 7) x hx;let hi:i∈A:=hA.symm▸(V:∀i∈O0,i∈S1) i g3;⟨n x g1,g2,λu h _=>a u h,v i,go hi (N g4),go hi (N g5)⟩;let a:(insert y O8).card=5:=by rcases b3 with rfl|rfl<;>rfl
  have:=oM om e7 _ b;rw[a]at this;omega
 let⟨u1,a⟩:=C1 (Y 7);let⟨b,a8⟩:=yM a;let hU:=rF b a8;let hW:=t2 (by omega);let hW':=λe h=>or_left_comm.1 (hW e h);let hM:∀t,t∈G u1.1->t≠7->t∈G (v 0)/\t∈G (v 1):=λt ht g=>by let b2:=fB b ht;let⟨a,r⟩:=jX g.symm e7 (λq hq k=>hU q hq k▸ht) ⟨a8,ht⟩;by_cases c0:z 0=a;{exact(qE hW (λ_=>go i0) V g (b1 t b2 0 i0) (r _ a1 λk=>a7 (c0.trans k.symm)) (r _ hH λk=>(a2 0 i0).1 (k.trans c0.symm))).elim};let r0:=r _ a0 c0;by_cases c1:z 1=a;{exact(qE hW' (λ_=>go m) V g (b1 t b2 1 m) r0 (r _ hH λk=>(a2 1 m).1 (k.trans c1.symm))).elim};exact⟨r0,r _ a1 c1⟩
 let g:J.card≠1:=λhR=>by
  let g:=λx=>lw u1 x λq hq _=>A4.1 hR.le q hq u1 b;let e4:=n 4 V;let a4:=aI i2 (a:=4) V;let q:=aI i0 (a:=10) V;let⟨p,hN,c,s,_⟩:=z2 (x:=4) (y:=10) V e4 (n 10 V);let⟨j,T1,hJ,s2,_⟩:=z2 (x:=4) (y:=13) V e4 (n 13 V);let n4:4∉G u1.1:=λh4=>by let⟨q0,q1⟩:=hM 4 h4 V;rcases aS (lI i0 q0) (lI m q1) hN a7 (s 0 i0).1.symm (s 1 m).1.symm (by have:=(g 4).1;omega) _ a4 with k|k|k;exacts[AB (kp.2 11 i2 0 i0 k) V,AB (kp.2 11 i2 1 m k) V,(s 11 i2).1 k.symm]
  let hU':p=j:=C λk=>by have:=d5 a4 hN T1 (s 11 i2).1.symm (s2 11 i2).1.symm k;have:=(g 4).2 n4;omega
  rw[<-hU']at hJ;let⟨e,hK,n7,i5⟩:=bR (x:=10) (a:=7) (b:=13) V V V;let d1:am p≠e:=λk=>i5 (k▸eW hJ);let d2:z 0≠e:=λk=>n7 (k▸go i0 V);by_cases j:10∈G u1.1;{rcases aS c q (lI m (hM 10 j V).2) (s 0 i0).2 (s 1 m).2 a7 (by have:=(g 10).1;omega) e hK with k|k|k;exacts[d1 k.symm,d2 k.symm,n7 (k▸go m V)]};have:=d5 c q hK (s 0 i0).2 d1 d2;have:=(g 10).2 j;omega
 let j:M=0:=by{omega};let hJ:∀i∈O0,i∈A/\z i∈F 7:=f2 ⟨i0,a0⟩ ⟨m,a1⟩;let fj:=λ{i} (hi:i∈O0) u=>qj j O0 hJ ⟨hH,λi d=>(a2 i d).1⟩ (eW h3) (by rw[(V:O0.card=2)];omega) hi u;let f0:=fj (i:=0) V V;let f1:=fj (i:=1) V V;let oP:∀t,aO 0 t->aO 1 t->t=7:=Z;let hP:=pr f0 f1 oP λt h ht=>hM t ht h;let j:(J.erase u1).card=1:=by{rw[A2 b];omega};let⟨b,q⟩:=_cp.1 (j▸Nat.one_pos);let a2:=mem_of_mem_erase q;let hO:∀x,x≠7->∀u∈J,x∈G u.1->u=b:=λx h u d a3=>A4.1 j.le u (_me.2 ⟨λk=>h (hP x (k▸a3)),d⟩) b q;let g:=λx h=>lw b x (hO x h);let q:=λ(x y:O) (h:x≠7) (i4:x≠y) (a3:x∈G b.1) (b6:y∈G b.1)=>jX i4 (fB a2 a3) (λu d a3'=>hO x h u d a3'▸b6) ⟨a3,b6⟩;let j:∀i l:O,i∈A->aO i l->l≠7->l∉G b.1->∀e∈F l,e≠z i->∀t,t≠l->e∉F t:=λi l d h a6 hn e he c7=>by let⟨e',_,he',c5⟩:=sF d (λh'=>by rw[h']at h;exact dv i h) (aI d h) ((g l a6).2 hn);rw[he',D4,D3]at he;rw[he.resolve_left c7];exact c5
 let x:∀l1 l2:O,aO 0 l1->aO 1 l2->l1≠7->l2≠7->∀e:E,e∈F l1->e∈F l2->e≠z 0->e≠z 1->False:=λl1 l2 h2 h4 n1 n2 e a5 a9 c6 a5'=>by let h:l1≠l2:=λk=>n1 (oP l1 h2 (k▸h4));let⟨a,r⟩:=q l1 l2 n1 h (C λhn=>j 0 l1 i0 h2 n1 hn e a5 c6 l2 h.symm a9) (C λhn=>j 1 l2 m h4 n2 hn e a9 a5' l1 h a5);let u:z 0=a:=C λk=>n2 (oP l2 ((f0 l2).1 (r _ (aI i0 h2) k)) h4);let⟨f,hK,n7,nl⟩:=bR n1 h ((Z:∀l,aO 1 l->¬aO 7 l) l2 h4);by_cases k:f=a;{exact n7 (by rw[k,<-u];exact go i0 V)};exact nl (r f hK k)
 let cl:∀(d la lb:O),((d∉S1/\la∉S1/\lb∉S1)/\(I 11 d/\I d la/\I d lb/\I 0 la/\I 1 lb)/\(la≠7/\lb≠7/\d≠7/\la≠d/\lb≠d)/\B0 0 d/\B0 1 d)->∃p e2,(∀e∈F d,e=z 11\/e=p\/e=e2)/\p∈F d/\e2∈F d/\p≠z 11/\e2≠z 11/\p≠e2/\am p∈F la/\am e2∈F lb/\(∀t,t≠la->am p∉F t)/\(∀t,t≠lb->am e2∉F t)/\d∈G b.1/\W d=∅:=λd la lb ⟨⟨g1,g2,g3⟩,⟨g4,g5,g6,g7,g8⟩,⟨n1,n2,n3,n4,n5⟩,g9,b8⟩=>by
  let⟨p,hN,c,s,f6⟩:=z2 (N g5) (n d g1) (n la g2);let⟨e2,T1,hJ,s2,f7⟩:=z2 (N g6) (n d g1) (n lb g3);let hU':p≠e2:=λk=>x la lb (N g7) (N g8) n1 n2 (am p) c (k▸hJ) (s 0 i0).2 (s 1 m).2;let⟨f,n⟩:=gL (aI i2 (N g4)) hN T1 (s 11 i2).1.symm (s2 11 i2).1.symm hU';have:=(g d n3).1;let f:d∈G b.1:=C λhn=>by have:=(g d n3).2 hn;omega
  let b:=λ{i l:O} {e:E} d0 h0 a6 d6 hb' hf (hs:d∉G (w (am e))) (fi:∀t,t∈G (v i)↔aO i t) (d4:¬aO i d)=>j i l d0 h0 a6 (λh=>by let⟨a,r⟩:=q l d a6 d6 h f;let hE:am e=a:=C λk=>hs (r _ hb' k);exact d4 ((fi d).1 (r _ (aI d0 h0) λk=>hf (hE.trans k.symm)))) _ hb' hf;exact⟨p,e2,n (by omega),hN,T1,(s 11 i2).1,(s2 11 i2).1,hU',c,hJ,b i0 (N g7) n1 n4 c (s 0 i0).2 f6 f0 (aG.1 g9),b m (N g8) n2 n5 hJ (s2 1 m).2 f7 f1 (aG.1 b8),f,C3⟩
 let⟨p,e2,_,hN,T1,m1,m2,hU',c,hJ,_,_,f8,_⟩:=cl 4 10 13 V;let⟨_,_,c4,_,_,_,_,_,_,_,e5,f4,g0,c3⟩:=cl 6 8 9 V;let⟨a,r⟩:=q 4 6 V V f8 g0;let b:∀(e:E) (l:O),e∈F 4->am e∈F l->l≠8->l≠9->e≠z 11->e≠a->False:=λe l hK hb h8 h9 b9 h0=>by rcases c4 e (gD R.1 c3 (ak.1 hK).1 (cY R.1 hK) (r e hK h0)) with rfl|rfl|rfl;exacts[b9 rfl,e5 l h8 hb,f4 l h9 hb]
 by_cases d:p=a;{exact b e2 13 T1 hJ V V m2 λk=>hU' (d.trans k.symm)};exact b p 10 hN c V V m1 d
lemma lF (hA:A={0,1,2,11}):False:=by
 let a:=C7 hA 4;let g:J0⊆A:=by{rw[hA];decide};have:=ry g;let hM:M=0:=by{omega};let⟨m,m1⟩:=pp hM g;let nr:∀(t i j x:O),(t∈X/\i∈J0/\j∈J0/\i≠j/\I i t/\I j t/\I t x/\x∉({0,1,2,11}:o))->∃e,F t={z i,z j,e}/\(e≠z i/\e≠z j)/\(Y t).card=1/\∀a,a∈G (v i)↔aO i a:=λt i j x ⟨b,h2,h3,c0,d,k,l,hx⟩=>by
  let hi:=g h2;let hj:=g h3;let⟨n,h5⟩:=m t b;let⟨e,c,f,_⟩:=kG (N l);let a1:x∈L:=nL (hA.symm▸hx);let m:e≠z i:=lH hi a1 f;let n:e≠z j:=lH hj a1 f;let p:=zI hi hj c0;let x:({z i,z j,e}:Finset E)⊆F t:=by{simp[A8,aI hi (N d),aI hj (N k),c]};let h3:({z i,z j,e}:Finset E).card=3:=by rw[_cin (by simp[p,m.symm]),_c2 n.symm]
  let r:=C2 x;have:=me ((fu aK R kC (N d)).resolve_left (ha.1 hi));rw[h5,<-r,h3,_ce]at this;exact⟨e,r.symm,⟨m,n⟩,by omega,qj hM {i,j} (f2 ⟨hi,aI hi (N d)⟩ ⟨hj,aI hj (N k)⟩) ⟨c,λ_ hq=>lH hq a1 f⟩ (eW f) (by rw[<-r,h3,_c2 c0]) (i:=i) (B9 _ _) ⟨d,λh=>hx (hA▸h▸hi)⟩⟩
 let⟨c,x7,n7,c7,N7⟩:=nr 7 0 1 3 V;let⟨c,a8,a7,a1,n⟩:=nr 13 1 2 4 V;let⟨e8,x8,n8,c8,N8⟩:=nr 8 2 0 6 V;let x:∀{t i j:O} {e:E},(i∈J0/\j∈J0/\i≠j/\I i t/\I j t)->F t={z i,z j,e}->(e≠z i/\e≠z j)->(∀a,a∈G (v i)↔aO i a)->(∀a,a∈G (v j)↔aO j a)->(Y t).card=1->∀{u:U},u∈J->t∈G u.1->∀{y:O},y∈G u.1->y=t:=λ{t i j e} ⟨a5,a6,a2,a3,a4⟩ ft b hm hn hX {u} hu ht {y} hy=>C λd=>by
  let hi:=g a5;let hj:=g a6;let hp:=fB hu hy;let⟨e0,m⟩:=jX (nS d) (fB hu ht) (λu' hu' ht'=>rF hu ht hX u' hu' ht'▸hy) ⟨ht,hy⟩;let ft':∀f∈F t,f=z i\/f=z j\/f=e:=λf h=>by{rw[ft]at h;simpa using h};let h2:=zI hi hj a2;by_cases c:y∈G (v i);{by_cases p:y∈G (v j);{exact d (kh i j y t a2 (D2 (bl (N a3))) (D2 (bl (N a4))) (D2 (bl ((hm y).1 c))) (D2 (bl ((hn y).1 p))))};let r:z j=e0:=C λq=>p (m _ (ft▸B8 (B9 _ _)) q);exact qE (λf h=>or_left_comm.1 (ft' f h)) (λa q=>(hn a).2 q) (N a4) d (λh=>ha.1 hj (h▸hp)) c (m e (ft▸B8 (B8 (D1 _))) λh=>b.2 (h.trans r.symm))};let r:z i=e0:=C λq=>c (m _ (ft▸B9 _ _) q);exact qE ft' (λa q=>(hm a).2 q) (N a3) d (λh=>ha.1 hi (h▸hp)) (m _ (ft▸B8 (B9 _ _)) λh=>h2 (r.trans h.symm)) (m e (ft▸B8 (B8 (D1 _))) λh=>b.1 (h.trans r.symm))
 let l:∀y:O,y∉X->(F y).card<=2:=λy hy=>by let b:Y y=∅:=B5.2 λu s=>by{let⟨hu,k⟩:=yM s;let⟨a,ha⟩:=m1 u hu;rw[_mn]at ha;let a:=ha.2;simp[X]at a;rcases a with rfl|rfl|rfl;exacts[hy (by rw[x V x7 n7 N7 n c7 hu ha.1 k];decide),hy (by rw[x V x8 n8 N8 N7 c8 hu ha.1 k];decide),hy (by rw[x V a8 a7 n N8 a1 hu ha.1 k];decide)]};have:=bi y;rw[b,_ce]at this;omega
 let⟨b,a,c,d⟩:=mg (i:=0) (g V) (s:=10) (d:=5) V (l 10 V);let⟨h,b,c,f⟩:=mg (i:=1) (g V) (s:=9) (d:=5) V (l 9 V);let⟨e3,_,q3,r3⟩:=mg (i:=2) (g V) (s:=12) (d:=5) V (l 12 V);have:=d5 d f r3 (λe=>a 9 V (C8 e▸c)) (λe=>a 12 V (C8 e▸q3)) (λe=>b 12 V (C8 e▸q3));have:=l 5 V;omega
def ej:o:={0,1,11,12}
def kt (D:Dag)(x:O):ℕ:=bn D ((cD 14 D).filter λw=>x∈ag 14 D w)
lemma pu (hI:A=ej)(l0:kt D 7<=kt D 3):False:=by
 let S1:o:={11,12};let S4:o:={4,6,2,5};let S6:o:={4,6};let⟨c,hC,hE,k2,b9,_⟩:=kG (x:=3) (y:=7) V;let n:∀i,i∈ej->i∈A:=λ_ h=>hI.symm▸h;let hL:∀x,x∉ej->x∈L:=λ_ h=>nL (hI.symm▸h);let i0:=n 0 V;let i1:=n 1 V;let l3:=hL 3 V;let l7:=hL 7 V;have:=C7 hI 4;let sr:∀{x:O} (b:o),(∀i∈b,i∈ej/\I i x)->∀i∈b,i∈A/\z i∈F x:=λ_ h i d=>⟨n _ (h i d).1,aI (n _ (h i d).1) (N (h i d).2)⟩;let b2:=sr (x:=7) O0 V;let b1:=sr (x:=3) S1 V;let b6:∀i∈A,am c≠z i:=λ_ g=>m0 g l3 hC;let b3:∀i∈A,c≠z i:=λ_ g=>lH g l7 hE;let c7:=kE _ b2 {am c} (f1 ⟨hE,λi g=>b6 i (b2 i g).1⟩);let c3:=kE _ b1 {c} (f1 ⟨hC,λi g=>b3 i (b1 i g).1⟩);let hG:O0.card=2/\S1.card=2/\S4.card=4:=⟨rfl,rfl,rfl⟩;rw[_cs,hG.1]at c7;rw[_cs,hG.2.1]at c3;let ot:∀{x:O},x∈L->kt D x=1+(Y x).card:=λ{x} f=>by have:=m9 aK R kC x;have:=me f;let i:(cD 14 D).filter (λr=>x∈G r)=ao 14 D {x}:=by{ext r;rw[H,b7,bP];exact⟨λa=>a.2,λa=>⟨by have:=cP a;let j:r≠bH 14 D:=λe=>by{rw[e,fN kq]at a;exact NM _ a};unfold bH at j;omega,a⟩⟩};unfold kt;rw[i];dsimp[F,W,Y,J,G]at *;omega
 have:=me l7;have:=me l3;have:=ot l7;have:=ot l3;let hW:=eW hC
 let ny:∀{x t j q:O},j∈A->x∈L->(∀u∈J,x∈G u.1->t∈G u.1)->∀{r:ℕ},x∈G r/\t∈G r->(I j x/\I j q/\x≠t/\x≠q/\B0 t q)->t∈G (v j):=λ{_ _ j _} p hx hc {_} y ⟨d,f,g,k,l⟩=>C λh1=>let⟨e0,i⟩:=jX g hx hc y;let c0:z j=e0:=C λm=>h1 (i _ (aI p (N d)) m);let⟨e,h2,h3,h4⟩:=bR g k (aG.1 l);h3 (i e h2 λn=>h4 (by rw[n,<-c0];exact go p (N f)));let hX:∀x∈S4,x∈L/\x≠3/\x≠7/\∃q,x∈G q/\3∈G q:=λx h1=>let⟨g1,g2,g3,i,g,g4,g5⟩:=(V:∀x∈S4,x∉ej/\x≠3/\x≠7/\∃i∈ej,I i x/\I i 3) x h1;⟨hL x g1,g2,g3,v i,go (n i g) (N g4),go (n i g) (N g5)⟩;let hA:¬∀u∈J,7∈G u.1->3∈G u.1:=λhA=>by let⟨u,l⟩:=C1 (Y 7);rw[H]at l;let hw:7∈G u.1/\3∈G u.1:=⟨l.2,hA u l.1 l.2⟩;let p0:=lI i0 (ny i0 l7 hA hw (q:=8) V);let p1:=lI i1 (ny i1 l7 hA hw (q:=9) V);let c5:=kE ej (λi g=>⟨n i g,by simp[ej]at g;rcases g with rfl|rfl|rfl|rfl;exacts[p0,p1,(b1 11 V).2,(b1 12 V).2]⟩) {c} (f1 ⟨hC,λi g=>b3 i (n i g)⟩);rw[(V:ej.card=4),_cs]at c5;let hB:Y 3=J:=C2 (_fs _ _);have:=oM oo l3 S4 λx h1=>⟨(hX x h1).1,(hX x h1).2.1,λ_ l _=>(yM (hB.symm▸l)).2,(hX x h1).2.2.2⟩;rw[hG.2.2]at this;have:=ar;omega
 let⟨uk,a8,e4,f8⟩:∃u∈J,7∈G u.1/\3∉G u.1:=C λd=>hA λu l h7=>C λh3=>d ⟨u,l,h7,h3⟩;let g9:Y 3⊆J.erase uk:=λ_ l=>_me.2 ⟨λe=>f8 (e▸(yM l).2),(yM l).1⟩;let a9:=_cl g9;rw[A2 a8]at a9;let d4:(Y 7).card=1:=C λd4=>by
  have:=card_union_add_card_inter (Y 3) (Y 7);have:=(_cl (B1 (_fs _ _) (_fs _ _)):(Y 3∪Y 7).card<=J.card)
  let⟨uj,h1⟩:=C1 (Y 3∩Y 7);rw[_mn,H,H]at h1;let hw:3∈G uj.1/\7∈G uj.1:=⟨h1.1.2,h1.2.2⟩;let rD:∀{x y:O},x∈L->x≠y->∀{r:ℕ},x∈G r/\y∈G r->(Y x).card<=(Y x∩Y y).card+1->∀{e1 e2 e3:E},e1∈F x->e2∈F x->e3∈F x->(e1≠e2/\e1≠e3/\e2≠e3)->y∉G (w e3)->y∈G (w e1)\/y∈G (w e2):=λ{x y} h1 d {_} c0 h2 {e1 e2 e3} h3 h4 h5 c k=>C λa=>by rw[B3]at a;have:=iK R.1 b0 kM d h1;have:=gN R x y d (by rw[fN kq];exact NM x);let⟨j,s,K1,hL',_,l,m,n',_⟩:=ji R.1 d c0;let f:∀e∈F x,y∉G (w e)->e∈(aE 14 D (aR 14 D x y)).erase (j,s):=λe g r=>_me.2 ⟨λt=>by have:=cY R.1 g;rw[t,hL']at this;exact _fnt this,dY.2 ⟨(ak.1 g).1,⟨eW g,r⟩,λh=>(ak.1 g).2.2 h.1⟩⟩;let h6:=two_lt_card.2 ⟨e1,f _ h3 a.1,e2,f _ h4 a.2,e3,f _ h5 k,c⟩;rw[A2 (dY.2 ⟨K1,⟨m,n'⟩,λh=>h.2 l⟩)]at h6;have:(J.filter λu=>x∈G u.1/\y∉G u.1).card<=(Y x\Y y).card:=_cl λu i=>by{rw[H]at i;exact _md.2 ⟨H.2 ⟨i.1,i.2.1⟩,λf=>i.2.2 (yM f).2⟩};have:=E0 (Y x) (Y y);dsimp[J,G]at *;omega
  let a7:=rD l3 V hw (by omega) (b1 11 V).2 (b1 12 V).2 hC ⟨zI (n 11 V) (n 12 V) V,(b3 11 (n 11 V)).symm,(b3 12 (n 12 V)).symm⟩ k2;let a3:=rD l7 V hw.symm (by rw[inter_comm];omega) (b2 0 V).2 (b2 1 V).2 hE ⟨zI i0 i1 V,(b6 0 i0).symm,(b6 1 i1).symm⟩ b9;let b9:∀j∈S1,7∉G (v j):=λj hj g0=>by let hJ:∀i∈insert j O0,i∈A/\z i∈F 7:=λi g=>(D4.1 g).elim (λg=>g▸⟨(b1 j hj).1,lI (b1 j hj).1 g0⟩) (b2 i);let a9:(insert j O0).card=3:=(V:∀j∈S1,(insert j O0).card=3) j hj;let m0:M=0:=by{omega};let f:∀i∈insert j O0,I i 7/\3≠i->∀t,t∈G (v i)↔aO i t:=λi hi u=>qj m0 (insert j O0) hJ ⟨hE,b6⟩ ((aB c).symm▸hW) (by rw[a9];omega) hi u;exact a3.elim (λa=>AB ((f 0 (by simp[O0]) V 3).1 a) V) λa=>AB ((f 1 (by simp[O0]) V 3).1 a) V
  exact a7.elim (b9 11 V) (b9 12 V)
 let qG:∀{x i j t:O} {u:U},u∈J->x∈G u.1->(∀u'∈J,x∈G u'.1->u'=u)->(i∈ej/\j∈ej/\x∉ej/\I i x/\I j x/\∀t,t∉ej->x≠t->∃h l:O,(I i h/\x≠h/\B0 t h)/\I j l/\x≠l/\B0 t l)->x≠t->t∈G u.1->∀k∈({i,j}:o),z k∈F t:=λ{x i j t u} h1 g n' ⟨h3,h4,y,p,q,h5⟩ f m=>let⟨_,_,⟨a1,a2,a3⟩,a4,a5,a6⟩:=h5 t (λc0=>ha.1 (n _ c0) (fB h1 m)) f;let hc:∀u'∈J,x∈G u'.1->t∈G u'.1:=λu' h7 y'=>n' u' h7 y'▸m;f2 (lI (n _ h3) (ny (n _ h3) (hL _ y) hc ⟨g,m⟩ ⟨p,a1,f,a2,a3⟩)) (lI (n _ h4) (ny (n _ h4) (hL _ y) hc ⟨g,m⟩ ⟨q,a4,f,a5,a6⟩));let b9:=rF a8 e4 d4;let h0:∀t,7≠t->t∈G uk.1->∀k∈O0,z k∈F t:=λ_ ht c4=>qG a8 e4 b9 V ht c4;let f7:=λ(m:M=0) {i} (hi:i∈O0) u=>qj m O0 b2 ⟨hE,b6⟩ ((aB c).symm▸hW) (by rw[hG.1];omega) hi u;let g0:M=0->∀t∈G uk.1,t=7:=λm=>pr (f7 m (i:=0) V V) (f7 m (i:=1) V V) Z λt h ht=>⟨eW (h0 t h.symm ht 0 V),eW (h0 t h.symm ht 1 V)⟩;let d4:(Y 3).card=1:=C λd4=>by
  let m:M=0:=by{omega};let b9:=C2 g9 (by rw[A2 a8];omega);let b6:∀x,x≠7->∀u∈J,x∈G u.1->3∈G u.1:=λx hx u lu b8=>(yM (b9▸_me.2 ⟨λ(e:u=uk)=>hx (g0 m x (e▸b8)),lu⟩)).2;by_cases ex:∃x∈O8,0<(Y x).card;{let⟨x,hx,i5⟩:=ex;let⟨u,hu⟩:=_cp.1 i5;let⟨lu,b8⟩:=yM hu;let⟨k2,b9,k9,i5⟩:=(V:∀x∈O8,x∉S4/\x≠7/\x∉ej/\x≠3) x hx;let g9:=b6 x b9 u lu b8;have:=oM oo l3 (insert x S4) λy hy=>(D4.1 hy).elim (λe=>e▸⟨hL x k9,i5,b6 x b9,u.1,b8,g9⟩) λhy=>let⟨g1,g2,g3,g4⟩:=hX y hy;⟨g1,g2,b6 y g3,g4⟩;rw[_cin k2,hG.2.2]at this;omega};let b8:∀x∈O8,(F x).card<=2:=λx hx=>by have:=bi x;have:(Y x).card=0:=C λhp=>ex ⟨x,hx,Nat.pos_of_ne_zero hp⟩;omega
  let g9:∀{d x:O},d∈S6->x∈O8->I d x->∃e,(∀t,t≠x->e∉F t)/\e∈F x/\am e∈F d/\3∉G (w e):=λ{d x} hd hx h2=>by
   let⟨i,a,hi,c1,h1,h3,h4,h5,h6,h7,h8⟩:=(V:∀x∈O8,∀d∈S6,∃i a,i∈ej/\d∉ej/\I i x/\x≠i/\d≠i/\I i a/\x≠a/\x≠3/\B0 a 3) x hx d hd;let⟨e,hu,b5,f6⟩:=mg (n i hi) ⟨N h1,N h2,h3,h4⟩ (b8 x hx);exact⟨e,hu,b5,f6,by let⟨f,hf,ha',h3'⟩:=bR h6 h7 (aG.1 h8);rcases gF (aI (n i hi) (N h1)) b5 (lH (n i hi) (hL d c1) f6).symm (b8 x hx) f hf with rfl|rfl;exacts[(ha' (go (n i hi) (N h5))).elim,h3']⟩
  let b9:∀(d x1 x2:O),(d∈S6/\d∉ej/\d≠3/\d≠7/\I 11 d/\x1∈O8/\x2∈O8/\x1∉ej/\x2∉ej/\x1≠x2/\I d x1/\I d x2)->∃x∈({x1,x2}:o),∃e,(∀t,t≠x->e∉F t)/\e∈F x/\am e∈F 3:=λd x1 x2 ⟨hd,c1,k0,d6,i4,c6,c8,c6',c8',k7,i8,i9⟩=>by
   let⟨e1,u1,m1,d1,n1⟩:=g9 hd c6 i8;let⟨e2,u2,m2,d2,n2⟩:=g9 hd c8 i9;let b8:am e1≠am e2:=λe=>u1 x2 k7.symm (C8 e▸m2);let f6:=d5 (aI (n 11 V) (N i4)) d1 d2 (m0 (n 11 V) (hL x1 c6') m1).symm (m0 (n 11 V) (hL x2 c8') m2).symm b8;have:=bi d;let⟨u,hu⟩:=C1 (Y d);let⟨lu,e4⟩:=yM hu;let⟨e0,hr⟩:=jX k0 (hL d c1) (b6 d d6) ⟨e4,b6 d d6 u lu e4⟩;let b6:∀{e:E} {x:O},e∈F x->3∉G (w e)->3∈G (w (am e))->am e∈F 3:=λ{e _} b5 i6 i7=>ak.2 ⟨(ak.1 b5).1,i7,λc1=>by rw[show (am e).1=e.1 from rfl,cB R.1 (ak.1 b5).1 (cY R.1 b5),_mn]at c1;exact i6 (by let⟨j,s⟩:=e;cases s;exacts[by simpa[aw] using c1.1,by simpa[aw] using c1.2])⟩;by_cases hc:am e1=e0;{exact⟨x2,B8 (D1 _),e2,u2,m2,b6 m2 n2 (hr _ d2 λe=>b8 (hc.trans e.symm))⟩};exact⟨x1,B9 _ _,e1,u1,m1,b6 m1 n1 (hr _ d1 hc)⟩
  let⟨xA,b6,eA,uA,mA,fA⟩:=b9 4 10 13 V;let⟨xB,k8,eB,uB,mB,fB⟩:=b9 6 8 9 V;let b5:=(V:∀xA∈({10,13}:o),∀xB∈({8,9}:o),xA∉ej/\xB∉ej/\xA≠7/\xB≠7/\xA≠xB) xA b6 xB k8;let b8:am eA≠c:=λe=>uA 7 b5.2.2.1.symm (C9 e▸hE);let b9:am eB≠c:=λe=>uB 7 b5.2.2.2.1.symm (C9 e▸hE);let b6:am eA≠am eB:=λe=>uA xB b5.2.2.2.2.symm (C8 e▸mB);let c5:=kE S1 b1 {c,am eA,am eB} (f3 ⟨hC,λi hi=>b3 i (b1 i hi).1⟩ ⟨fA,λi hi=>m0 (b1 i hi).1 (hL xA b5.1) mA⟩ ⟨fB,λi hi=>m0 (b1 i hi).1 (hL xB b5.2.1) mB⟩);rw[hG.2.1,_cin (by simp[b8.symm,b9.symm]),_c2 b6]at c5;omega
 let⟨uc,s⟩:=C1 (Y 3);rw[H]at s;let c:=rF s.1 s.2 d4;let hJ:uc≠uk:=λe=>f8 (e▸s.2);let b5:∀t,3≠t->t∈G uc.1->∀k∈S1,z k∈F t:=λ_ ht c4=>qG s.1 s.2 c V ht c4;let b6:J.card=2:=C λb6=>by
  let m:M=0:=by{omega};let f3':=λ{i} (hi:i∈S1) u=>qj m S1 b1 ⟨hC,b3⟩ (eW hE) (by rw[hG.2.1];omega) hi u;let c:=pr (f3' (i:=11) V V) (f3' (i:=12) V V) Z λt h ht=>⟨eW (b5 t h.symm ht 11 V),eW (b5 t h.symm ht 12 V)⟩;let a9:((J.erase uc).erase uk).card<=1:=by{rw[A2 (_me.2 ⟨hJ.symm,a8⟩),A2 s.1];omega};let h:∀x,x≠3->x≠7->∀u∈J,x∈G u.1->u∈(J.erase uc).erase uk:=λx a3 a7 _ l h1=>_me.2 ⟨λe=>a7 (g0 m x (e▸h1)),_me.2 ⟨λe=>a3 (c x (e▸h1)),l⟩⟩;let c:∀(x y i a:O),(i∈ej/\x∉ej/\x≠3/\x≠7/\y≠3/\y≠7/\(I i x/\I i a/\x≠y/\x≠a/\B0 y a)/\B0 i y)->(∀t,t∈G (v i)↔aO i t)->(Y x).card≠0->(Y y).card≠0->False:=λx y i a ⟨g1,g2,g3,g4,g5,g6,g7,g8⟩ hf n1 n2=>by let⟨u1,b⟩:=_cp.1 (Nat.pos_of_ne_zero n1);let⟨u2,T1⟩:=_cp.1 (Nat.pos_of_ne_zero n2);rw[H]at b T1;let hB:∀u∈J,x∈G u.1->y∈G u.1:=λu l h1=>A4.1 a9 u (h x g3 g4 u l h1) u2 (h y g5 g6 u2 T1.1 T1.2)▸T1.2;exact aG.1 g8 ((hf y).1 (ny (n i g1) (hL x g2) hB ⟨b.2,hB u1 b.1 b.2⟩ g7))
  let t:(Y 4).card≠0\/(Y 10).card≠0:=C λd=>by rw[B3,B4,B4]at d;exact dk 4 10 13 11 0 (by rw[hI];decide) V (by have:=bi 4;omega) (by have:=bi 10;omega)
  let y:(Y 5).card≠0\/(Y 9).card≠0:=C λd=>by rw[B3,B4,B4]at d;exact dk 5 9 10 12 1 (by rw[hI];decide) V (by have:=bi 5;omega) (by have:=bi 9;omega)
  let d:=f3' (i:=11) V V;let h:=f7 m (i:=0) V V;rcases t with n1|n1<;>rcases y with n2|n2;exacts[c 4 5 11 3 V d n1 n2,c 4 9 11 3 V d n1 n2,c 10 5 0 7 V h n1 n2,c 10 9 0 7 V h n1 n2]
 let c:({uc,uk}:Finset U)=J:=_eqc (f2 s.1 a8) (by rw[_c2 hJ,b6]);let hr:∀x,(Y x).card<=(if x∈G uc.1 then 1 else 0)+if x∈G uk.1 then 1 else 0:=λx=>by have:=card_filter (λu:U=>x∈G u.1) {uc,uk};rw[sum_pair hJ,c]at this;exact this.le
 let m:∀{x i:O} {us uo:U} (Js Jo:o) {e0:E},(Js⊆ej/\Jo⊆ej/\Js.card=2/\Jo.card=2/\Disjoint Js Jo/\i∈Js/\I i x)->(x∈G us.1->∀k∈Js,z k∈F x)->(x∈G uo.1->∀k∈Jo,z k∈F x)->(Y x).card<=(if x∈G us.1 then 1 else 0)+(if x∈G uo.1 then 1 else 0)->(e0∈F x/\∀k∈A,e0≠z k)->∀e∈F x,e=e0\/e∈Js.image z:=λ{x i us uo} Js Jo {e0} ⟨g1,g2,g3,g4,g5,g6,g7⟩ u h2 hr' p=>by
  let hA:=bi x;let l:=aI (n _ (g1 g6)) (N g7);let d:∀(b:o),(∀i∈b,i∈A/\z i∈F x)->b.card+1<=(F x).card:=λb q=>by have:=kE b q {e0} (f1 ⟨p.1,λk a=>p.2 k (q k a).1⟩);rwa[_cs]at this
  by_cases h:x∈G uo.1;{exfalso;by_cases c:x∈G us.1;{have:=d (Js∪Jo) λk a=>(_mu.1 a).elim (λa=>⟨n _ (g1 a),u c k a⟩) λa=>⟨n _ (g2 a),h2 h k a⟩;rw[_cud g5]at this;split_ifs at hr';omega};have:=d (insert i Jo) λk a=>(D4.1 a).elim (λe=>e▸⟨n _ (g1 g6),l⟩) λa=>⟨n _ (g2 a),h2 h k a⟩;rw[_cin (_dl.1 g5 g6)]at this;split_ifs at hr';omega};intro e r;by_contra g;rw[B3]at g
  let d:∀(b:o),b⊆Js->(∀k∈b,z k∈F x)->b.card+2<=(F x).card:=λb j q=>by have:=kE b (λk a=>⟨n _ (g1 (j a)),q k a⟩) {e0,e} (f2 ⟨p.1,λk a=>p.2 k (n _ (g1 (j a)))⟩ ⟨r,λk a s=>g.2 (_mg.2 ⟨k,j a,s.symm⟩)⟩);rwa[_c2 (nS g.1)]at this
  by_cases c:x∈G us.1;{have:=d Js SR (u c);split_ifs at hr';omega};have:=d {i} (A7.2 g6) (f1 l);rw[_cs]at this;split_ifs at hr';omega
 let⟨f,e7,f4,_⟩:=kG (x:=4) (y:=10) V;let b:=m (x:=4) (i:=11) S1 O0 V (b5 4 V) (h0 4 V) (hr 4) ⟨e7,λ_ hk=>lH hk (hL 10 V) f4⟩;let a:=m (x:=10) (i:=0) O0 S1 V (h0 10 V) (b5 10 V) (by rw[Nat.add_comm];exact hr 10) ⟨f4,λ_ hk=>m0 hk (hL 4 V) e7⟩;let⟨e,k1,e5,_⟩:=kG (x:=4) (y:=13) V;rcases b e k1 with rfl|h1;{let⟨e',he',h4,h5⟩:=bR (x:=10) (a:=7) (b:=13) V V V;rcases a e' he' with rfl|h6;{exact h5 (eW e5)};obtain⟨k,hk,rfl⟩:=_mg.1 h6;exact h4 (eW (b2 k hk).2)};obtain⟨k,hk,rfl⟩:=_mg.1 h1;exact lH (b1 k hk).1 (hL 13 V) e5 rfl
end KS
lemma hV (C:Circuit)(e:Monotone2 C)(g:∀x:O->_d,C.eval (_of x)=true↔bw x):27<=C.size:=by
 by_contra hsz;let d:∀{u v:O},aO u v->bw λi=>decide (i=u)||decide (i=v):=λ{u v} h=>(ce _).2 ⟨u,v,h,by simp,by simp⟩;let⟨c,j,d0,l⟩:=fV (n:=14) C e (λb=>by cases b;{exact⟨_,by rw[Ne,_nf];exact(g _).2 (d (u:=0) (v:=7) V)⟩};{exact⟨λ_=>false,λh=>by let⟨_,_,_,a,_⟩:=(g _).1 h;exact _fnt a⟩}) (λi=>⟨λk=>decide (k=i),λh=>fe i ((g _).1 (by rw[h];simp))⟩) (λi=>⟨λk=>decide (k=cp i),λk=>decide (k=i)||decide (k=cp i),λk a=>by simp[a],λh=>fe _ ((g _).1 (by rw[h];exact(g _).2 (d (N (gU i).1))))⟩);let d:aq c:=λx=>by{rw[l x];exact g x};let h:∀u v:O,aO u v->u∈al 14 c\/v∈al 14 c:=λ_ _ a=>fu aK j (aC d) a;let l:∀u∈aa 14 c,∀v∈aa 14 c,¬aO u v:=λu du v dv a=>(h u v a).elim (aN.1 du) (aN.1 dv);let⟨b0,a⟩:=dK aK j.1 (aC d);have:=eR _ h;have:=dX j.1 b0 a;have:=dC 14 c;have:=iC j;have:=aV 14 c;let⟨s,n,m⟩:=jW _ l (C1 _);let⟨h,l,p,q,a⟩:=jj s n j d;set N:=bo s c;let⟨c,j⟩:=b_ aK h.1 (aC l);let⟨n,d⟩:=bQ aK h (aC l);let _:K True:=⟨N,c,n,h,l,j,d,by omega⟩;let d:A∈d3:=by change aa 14 N∈d3;rw[a];exact m
 simp[d3]at d;rcases d with d|d|d|d|d|d|d|d|d|d|d|d|d|d;exacts[gY d {0,1,2,3,4,5,6},gY d {0,1,2,3,4,5},gY d {0,1,2,3,4},nm d,gY d {0,1,2,3},gY d {0,1,2,5},lF d,by{by_cases b:kt N 7<=kt N 3;{exact pu d b};let b:=k6 0x2106543a987dcb;let a:_ep O:=⟨b,b,Z,Z⟩;let⟨e,f,_,g,i⟩:=jj a (lt Z) h l;set D2:=bo a N;let⟨b,l⟩:=b_ aK e.1 (aC f);let⟨z2,c⟩:=bQ aK e (aC f);let j:kt D2 (a 3)=kt N 3:=eo a _ _ _ λw=>by{rw[fh a h.1];simp};let k:kt D2 (a 7)=kt N 7:=eo a _ _ _ λw=>by{rw[fh a h.1];simp};rw[(V:a 3=7)]at j;rw[(V:a 7=3)]at k;exact @pu False ⟨D2,b,z2,e,f,l,c,by omega⟩ (by show aa 14 D2=ej;rw[i,show aa 14 N={0,1,11,12} from d];decide) (by show kt D2 7<=kt D2 3;omega)},by{have:=C7 d 3;have:=ry (d▸SR);omega},nq d,mT d,nn d,mS d,by{have:=C7 d 1;exact C4 (d▸V)}]
def kW:O->O:=λi=>([0,1,2,3,4,5,6,7,13,12,11,10,9,8]:_F O).getD i.val 0
def cE (w:_F _d)(g:Gate):_F _d:=w++[g.op.eval (g.inputs.map λi=>w.getD i false)]
lemma ss:∀a b:Fin 7,(a=b\/a=b+1\/a=b+3)->((kW (Fin.castAdd 7 a)).val,(kW (Fin.natAdd 7 b)).val)∈e8:=Z
lemma sL:∀u v:O,(u.val,v.val)∈e8->∃a b:Fin 7,(a=b\/a=b+1\/a=b+3)/\kW (Fin.castAdd 7 a)=u/\kW (Fin.natAdd 7 b)=v:=Z
abbrev np:o:={8,9,10,11,12,13}
end _B
namespace _U
abbrev aP (u v:O):Prop:=_B.aO u v
def ac (u v:O):_d:=_B.ab u v
lemma ae:∀ u v:O,ac u v=true↔aP u v:=_B.ad
lemma aH {u v:O}:ac u v=false↔¬ aP u v:=by rw[<- ae];cases ac u v <;> decide
lemma bm {u v:O} (h:aP u v):aP v u:=_B.bl h
lemma dx (u:O):¬ aP u u:=_B.dv u
abbrev aP07 (u v:O):Prop:=aP u v/\¬(u=0/\v=7)/\¬(u=7/\v=0)
def az (v:O):o:=univ.filter (fun u=>ac v u=true)
abbrev aD (v:O):o:=az v
lemma cn {i a:O}:a∈aD i↔aP i a:=by simp only[aD,az,_mf,_mv,true_and,ae]
lemma gf:∀ v:O,(az v).card=3:=by decide +kernel
lemma ig:∀ u v:O,u≠v->(az u∩az v).card<=1:=by decide +kernel
def eE07 (S:o):Prop:=∀ u v:O,aP07 u v->u∈S\/v∈S
def dI07 (I:o):Prop:=∀ u∈I,∀ v∈I,¬ aP07 u v
lemma eV07 {S:o} (b:eE07 S):7<=S.card:=by
 let f (u:O):O:=([8,7,12,11,13,10,9,1,0,6,5,3,2,4]:_F O).getD u.val 0
 have g:∀ u:O,aP07 u (f u)/\f (f u)=u:=by decide +kernel
 have a:(univ:o)⊆S∪S.image f:=by intro u _;rcases b u _ (g u).1 with h|h;{exact mem_union_left _ h};{exact mem_union_right _ (_mg.2 ⟨_,h,(g u).2⟩)}
 have c:=_cl a;have:=card_union_le S (S.image f);have:=card_image_le (s:=S) (f:=f);simp only[card_univ,Fintype.card_fin] at c;omega
abbrev dj (u v:O):Prop:=_B.aO u v\/(u=1/\v=8)\/(u=8/\v=1)\/(u=1/\v=10)\/(u=10/\v=1)\/(u=3/\v=8)\/(u=8/\v=3)\/(u=3/\v=10)\/(u=10/\v=3)
def rX (u:O):ℕ:=([1408,10112,12544,7552,11264,5632,2816,11,79,98,59,88,44,22]:_F ℕ).getD u.val 0
def bK (u v:O):_d:=(rX u).testBit v.val
lemma cW:∀ u v:O,bK u v=true↔dj u v:=by decide +kernel
lemma b3 {u v:O}:bK u v=false↔¬ dj u v:=by rw[<- cW];cases bK u v <;> decide
lemma lL {u v:O} (h:dj u v):dj v u:=by
 have:bK v u=true:=by have h':=(cW u v).2 h;revert u v h';decide +kernel
 exact (cW v u).1 this
lemma ij (u:O):¬ dj u u:=by intro h;have:=(cW u u).2 h;revert u this;decide +kernel
def bX (v:O):o:=univ.filter (fun u=>bK v u=true)
lemma cL {i a:O}:a∈bX i↔dj i a:=by simp only[bX,_mf,_mv,true_and,cW]
lemma fQ (i:O):aD i⊆bX i:=fun a b=>cL.2 (Or.inl (cn.1 b))
def bx (x:O->_d):Prop:=∃ u v:O,dj u v/\x u=true/\x v=true
lemma oa:¬ bx (fun _=>false):=by rintro⟨u,v,-,h,-⟩;exact _fnt h
lemma kv (v:O):¬ bx (fun i=>decide (i=v)):=by rintro⟨a,b,c,d,e⟩;simp only[decide_eq_true_eq] at d e;subst d;subst e;exact ij _ c
lemma f8:∀ a b:O,bK a b=true->decide (a.val<7)≠decide (b.val<7):=by decide +kernel
def cK (σ:_ep (O)):Prop:=(∀ u v:O,aP (σ u) (σ v)↔aP u v)/\(∀ u v:O,dj (σ u) (σ v)↔dj u v)
def autTbl:_F (_F ℕ):=[[0,1,2,3,4,5,6,7,8,9,10,11,12,13],[0,1,4,3,2,6,5,7,10,9,8,12,11,13],[0,1,5,3,6,2,4,7,10,13,8,11,12,9],[0,1,6,3,5,4,2,7,8,13,10,12,11,9],[0,3,2,1,5,4,6,7,8,11,10,9,13,12],[0,3,4,1,6,2,5,7,10,12,8,9,13,11],[0,3,5,1,2,6,4,7,10,11,8,13,9,12],[0,3,6,1,4,5,2,7,8,12,10,13,9,11],[7,8,9,10,11,12,13,0,1,2,3,4,5,6],[7,8,11,10,9,13,12,0,3,2,1,5,4,6],[7,8,12,10,13,9,11,0,3,6,1,4,5,2],[7,8,13,10,12,11,9,0,1,6,3,5,4,2],[7,10,9,8,12,11,13,0,1,4,3,2,6,5],[7,10,11,8,13,9,12,0,3,5,1,2,6,4],[7,10,12,8,9,13,11,0,3,4,1,6,2,5],[7,10,13,8,11,12,9,0,1,5,3,6,2,4]]
def autFn (k:Fin 16) (v:O):O:=Fin.ofNat 14 ((autTbl.getD k.val []).getD v.val 0)
lemma autInj:∀ k:Fin 16,∀ a b:O,autFn k a=autFn k b->a=b:=by decide +kernel
lemma autH:∀ k:Fin 16,∀ u v:O,ac (autFn k u) (autFn k v)=ac u v:=by decide +kernel
lemma autHP:∀ k:Fin 16,∀ u v:O,bK (autFn k u) (autFn k v)=bK u v:=by decide +kernel
noncomputable def bN (k:Fin 16):_ep (O):=Equiv.ofBijective (autFn k) ⟨fun a b h=>autInj k a b h,Finite.injective_iff_surjective.mp (fun a b h=>autInj k a b h)⟩
lemma bN_eq (k:Fin 16) (v:O):bN k v=autFn k v:=rfl
lemma oX (k:Fin 16):cK (bN k):=⟨fun u v=>by rw[<- ae,<-ae,bN_eq,bN_eq,autH],fun u v=>by rw[<- cW,<-cW,bN_eq,bN_eq,autHP]⟩
def bU(a:Fin 68):o:=([{0,1},{0,2},{1,2},{1,3},{2,4},{4,5},{0,7},{2,7},{1,8},{4,8},{2,9},{0,1,2},{0,1,3},{1,2,3},{0,2,4},{1,2,4},{2,3,4},{0,4,5},{1,4,5},{2,4,5},{0,2,7},{2,4,7},{4,5,7},{1,3,8},{1,4,8},{4,5,8},{4,7,8},{0,2,9},{2,3,9},{2,4,9},{0,1,2,3},{0,1,2,4},{0,2,3,4},{1,2,3,4},{0,1,4,5},{0,2,4,5},{1,2,4,5},{1,3,4,5},{2,4,5,6},{0,2,4,7},{0,4,5,7},{2,4,5,7},{1,3,4,8},{1,4,5,8},{4,5,7,8},{0,2,3,9},{0,2,4,9},{2,3,4,9},{0,2,7,9},{2,4,7,9},{3,4,8,9},{1,3,8,10},{0,1,2,3,4},{0,1,2,4,5},{0,1,3,4,5},{1,2,3,4,5},{0,2,4,5,6},{1,2,4,5,6},{0,2,4,5,7},{2,4,5,6,7},{1,3,4,5,8},{0,2,3,4,9},{0,2,4,7,9},{0,1,2,3,4,5},{0,1,2,4,5,6},{1,2,3,4,5,6},{0,2,4,5,6,7},{0,1,2,3,4,5,6}]:_F o).getD a.val ∅
def pI (a:Fin 68):ℕ:=([3,5,6,10,20,48,129,132,258,272,516,7,11,14,21,22,28,49,50,52,133,148,176,266,274,304,400,517,524,532,15,23,29,30,51,53,54,58,116,149,177,180,282,306,432,525,533,540,645,660,792,1290,31,55,59,62,117,118,181,244,314,541,661,63,119,126,245,127]:_F ℕ).getD a.val 0
def d4:Finset (o):=univ.image bU
lemma fP {R:o} (h:R∈d4):∃ a:Fin 68,bU a=R:=by obtain⟨a,-,rfl⟩:=_mg.1 h;exact⟨a,rfl⟩
def bZ (S:o):ℕ:=(if (0:O)∈S then 2 ^ 0 else 0)||| (if (1:O)∈S then 2 ^ 1 else 0)||| (if (2:O)∈S then 2 ^ 2 else 0)||| (if (3:O)∈S then 2 ^ 3 else 0)||| (if (4:O)∈S then 2 ^ 4 else 0)||| (if (5:O)∈S then 2 ^ 5 else 0)||| (if (6:O)∈S then 2 ^ 6 else 0)||| (if (7:O)∈S then 2 ^ 7 else 0)||| (if (8:O)∈S then 2 ^ 8 else 0)||| (if (9:O)∈S then 2 ^ 9 else 0)||| (if (10:O)∈S then 2 ^ 10 else 0)||| (if (11:O)∈S then 2 ^ 11 else 0)||| (if (12:O)∈S then 2 ^ 12 else 0)||| (if (13:O)∈S then 2 ^ 13 else 0)
lemma gg (p:Prop) [Decidable p] (k b:ℕ):(if p then 2 ^ k else 0).testBit b=(decide (k=b)&&decide p):=by split_ifs with a <;> simp[Nat.testBit_two_pow,a]
lemma bC (S:o) (i:O):(bZ S).testBit i.val=decide (i∈S):=by fin_cases i <;> (simp only[bZ,Nat.testBit_or,gg];simp)
lemma jR (p:Prop) [Decidable p] (k:ℕ) (a:k<14):(if p then 2 ^ k else 0)<2 ^ 14:=by split_ifs;{exact Nat.pow_lt_pow_right (by omega) a};{omega}
lemma mB (S:o):bZ S<16384:=by
 change bZ S<2 ^ 14;unfold bZ;repeat (apply Nat.or_lt_two_pow)
 all_goals exact jR _ _ (by omega)
lemma oY {S T:o} (h:bZ S=bZ T):S=T:=by ext i;have a:=congrArg (fun m=>m.testBit i.val) h;rw[bC,bC] at a;simpa using a
lemma pJ:∀ a:Fin 68,bZ (bU a)=pI a:=by decide +kernel
def orbS(t:Fin 83):o:=if h:t.val<68 then bU ⟨_,h⟩ else if t.val=82 then ∅ else {Fin.ofNat 14 (t.val-68)}
def orbA(σ:_ep O):Prop:=cK σ/\∀ u v:O,aP07 (σ u) (σ v)↔aP07 u v
lemma orbP (k:Fin 16):orbA (bN k):=by
 refine ⟨oX k,fun u v=>and_congr ((oX k).1 u v) ?_⟩
 let f (u v:O):Prop:=¬(u=0/\v=7)/\¬(u=7/\v=0)
 have z:∀ (k:Fin 16) (u v:O),f (autFn k u) (autFn k v)↔f u v:=by unfold f;decide +kernel
 exact z k u v
lemma orbStep:∀ t:Fin 83,∀ v:O,(∀ u∈orbS t,¬ aP07 u v)->∃ k:Fin 16,∃ j:Fin 83,(insert v (orbS t)).image (autFn k)=orbS j:=by decide +kernel
lemma orbInd (I:o):dI07 I->∃ σ:_ep O,orbA σ/\∃ t:Fin 83,I.image σ=orbS t:=by
 induction I using Finset.induction_on with
 | empty=>exact fun _=>⟨1,⟨⟨fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩,fun _ _=>Iff.rfl⟩,82,by rw[image_empty];rfl⟩
 | insert v J _ ih=>
  intro c;obtain ⟨σ,a,t,b⟩:=ih (fun u hu w hw=>c u (mem_insert_of_mem hu) w (mem_insert_of_mem hw))
  obtain ⟨k,j,g⟩:=orbStep t (σ v) (by rw[<-b];intro u hu;obtain ⟨x,hx,rfl⟩:=_mg.1 hu;exact fun e=>c x (mem_insert_of_mem hx) v (mem_insert_self ..) ((a.2 x v).1 e))
  have d:=orbP k;refine ⟨bN k*σ,⟨⟨fun u v=>(d.1.1 _ _).trans (a.1.1 u v),fun u v=>(d.1.2 _ _).trans (a.1.2 u v)⟩,fun u v=>(d.2 _ _).trans (a.2 u v)⟩,j,?_⟩
  rw[Equiv.Perm.coe_mul,<-image_image,image_insert,b];exact g
lemma lK {I:o} (r:dI07 I) (e:2<=I.card):∃ σ:_ep (O),cK σ/\I.image σ∈d4:=by
 obtain ⟨σ,a,t,b⟩:=orbInd I r;refine ⟨σ,a.1,?_⟩;rw[b];by_cases q:t.val<68
 · rw[orbS,dif_pos q];exact _mg.2 ⟨_,_mv _,rfl⟩
 · have h:2<=(I.image σ).card:=by rwa[_cii _ σ.injective]
   rw[b,orbS,dif_neg q] at h;split at h <;> simp at h
def ar (D:Dag):Prop:=(∀ x:O->_d,cN aP x->val D x (bH 14 D)=true)/\(∀ x:O->_d,val D x (bH 14 D)=true->cN dj x)
lemma ar_pair {D:Dag} (h:ar D) {u v:O} (hn:¬ dj u v):val D (b4 u v) (bH 14 D)=false:=by
 by_contra g;rw[_nf] at g;obtain⟨a,b,c,i,j⟩:=h.2 _ g;simp only[b4,Bool.or_eq_true,decide_eq_true_eq] at i j
 rcases i with rfl|rfl <;> rcases j with rfl|rfl;{exact ij _ c};{exact hn c};{exact hn (lL c)};{exact ij _ c}
lemma oc {D:Dag} (a:ar D):ag 14 D (bH 14 D)=∅:=eq_empty_iff_forall_notMem.2 (fun v b=>kv v (a.2 _ (ee.1 b)))
lemma oZ (σ:_ep (O)) (hσ:cK σ) {D:Dag} (h:ai 14 D) (b:ar D):ai 14 (bo σ D)/\ar (bo σ D)/\ (bo σ D).length=D.length/\ap 14 (bo σ D)=ap 14 D/\bd 14 (bo σ D)=bd 14 D/\bL 14 (bo σ D)=bL 14 D/\al 14 (bo σ D)=(al 14 D).image σ/\aa 14 (bo σ D)=(aa 14 D).image σ:=by
 refine⟨fd σ h,?_,cc σ D,eJ σ D,j8 σ h.1,j9 σ h.1,fZ σ h.1,ep σ h.1⟩;refine⟨?_,?_⟩
 · rintro x ⟨u,v,a,c,d⟩;rw[fI σ h.1 h.2.2 x];exact b.1 _ ⟨σ.symm u,σ.symm v,(hσ.1 _ _).1 (by simpa using a),by simpa using c,by simpa using d⟩
 · intro x e;rw[fI σ h.1 h.2.2 x] at e;obtain⟨u,v,a,c,d⟩:=b.2 _ e;exact⟨σ u,σ v,(hσ.2 u v).2 a,c,d⟩
lemma kw07 (D:Dag):eE07 (al 14 D)↔dI07 (aa 14 D):=by
 constructor;{intro b u e v f a;have g:=_md.mp e;have h:=_md.mp f;exact(b u v a).elim g.2 h.2}
 · intro c u v a;by_contra d;push Not at d;exact c u (_md.mpr ⟨_mv _,d.1⟩) v (_md.mpr ⟨_mv _,d.2⟩) a
def dom (v:O):o:=if v=0 then {0,1,3} else if v=7 then {7,8,10} else {v}
lemma dom_self (v:O):v∈dom v:=by revert v;decide +kernel
lemma dom_anti:∀ u v:O,u∈dom v->v∈dom u->u=v:=by decide +kernel
lemma dom_spec:∀ v u:O,u∉dom v->∃ z:O,ac v z=true/\bK u z=false:=by decide +kernel
lemma dom_eq_self {v:O} (h0:v≠0) (h7:v≠7):dom v={v}:=by simp[dom,h0,h7]
lemma dom_mem_cases:∀ v x:O,x∈dom v->v=x\/(v=0/\(x=1\/x=3))\/(v=7/\(x=8\/x=10)):=by decide +kernel
lemma fk_dom {D:Dag} (e:au 14 D) (k:ar D) (v:O) (b:ℕ) (a:j_ 14 D b v.val):ag 14 D b⊆dom v:=by
 intro u l;by_contra f;obtain⟨z,gz,hz⟩:=dom_spec v u f
 have i:val D (b4 u z) b=true:=cO e l (by simp[b4])
 have j:val D (bB v (b4 u z)) b=true:=cO e l (by simp[bB,b4])
 have d:=mw e _ _ v (dd v (b4 u z)) b a (by rw[i,j])
 have q:=k.1 (bB v (b4 u z)) ⟨v,z,(ae v z).1 gz,dm v (b4 u z),by simp[bB,b4]⟩
 rw[<- d,ar_pair k (b3.1 hz)] at q;exact _fnt q
def cU_dom (D:Dag) (b:O->ℕ):Prop:=∀ v∈al 14 D,2<=aF D (b v)/\v∈ag 14 D (b v)/\ag 14 D (b v)⊆dom v/\bz 14 D v.val (b v)/\∀ w,2<=aF D w->v∈ag 14 D w->b v<=w
lemma b_dom {D:Dag} (e:au 14 D) (l:ar D):∃ b:O->ℕ,cU_dom D b:=by
 classical
 have h:∀ v:O,∃ b,v∈al 14 D->2<=aF D b/\v∈ag 14 D b/\ag 14 D b⊆dom v/\bz 14 D v.val b/\∀ w,2<=aF D w->v∈ag 14 D w->b<=w:=by
  intro v;by_cases d:v∈al 14 D
  · have a:∃ w,2<=aF D w/\v∈ag 14 D w:=eX.mp d;obtain⟨m,j⟩:=Nat.find_spec a
    have c:bz 14 D v.val (Nat.find a):=fy e v _ j (fun u p f=>by have:=Nat.find_min a p;by_contra r;exact this ⟨by omega,f⟩)
    exact⟨Nat.find a,fun _=>⟨m,j,fk_dom e l v _ (ds e c),c,fun w g i=>Nat.find_min' a ⟨g,i⟩⟩⟩
  · exact⟨0,fun h=>absurd h d⟩
 choose b q using h;exact⟨b,fun v d=>q v d⟩
lemma je_dom {D:Dag} {b:O->ℕ} (h:cU_dom D b):Set.InjOn (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ)) (al 14 D:Set O):=by
 intro v hv u hu eq1;have c:b v=b u:=congrArg Sigma.fst eq1
 exact dom_anti v u ((h u hu).2.2.1 (c▸(h v hv).2.1)) ((h v hv).2.2.1 (c.symm▸(h u hu).2.1))
lemma eY_dom {D:Dag} (e:au 14 D) {b:O->ℕ} (h:cU_dom D b):cz 14 D b⊆da 14 D:=by
 intro u d;obtain⟨v,hv,rfl⟩:=_mg.mp d;obtain⟨hf,hmem,-⟩:=h v hv
 rw[da,_mf,dW];exact⟨⟨bP.mpr (dc e (w:=b v) (by omega)),by show 0+1<aF D (b v);omega⟩,⟨v,hmem⟩⟩
lemma j7_dom {D:Dag} {b:O->ℕ} (h:cU_dom D b):(cz 14 D b).card=(al 14 D).card:=_cij (je_dom h)
lemma dX_dom {D:Dag} (e:au 14 D) {b:O->ℕ} (h:cU_dom D b):(al 14 D).card<=bd 14 D:=by rw[<- j7_dom h,<-jH];exact _cl (eY_dom e h)
lemma bS_dom {D:Dag} (e:au 14 D) {b:O->ℕ} (h:cU_dom D b):(aj 14 D b).card+(al 14 D).card=bd 14 D:=by rw[<- j7_dom h,<-jH];exact card_sdiff_add_card_eq_card (eY_dom e h)
lemma d9_dom {D:Dag} (e:au 14 D) {b:O->ℕ} (h:cU_dom D b) (T:o):bn D (ao 14 D T)=((al 14 D).filter (fun v=>(ag 14 D (b v)∩T).Nonempty)).card+((aj 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty)).card:=by
 have l:bn D (ao 14 D T)=((dq 14 D).filter (fun u=>(ag 14 D u.1∩T).Nonempty)).card:=by
  rw[eI 14 D (fun w=>(ag 14 D w∩T).Nonempty)];symm;refine sum_subset (fun w c=>?_) (fun w c d=>?_)
  · rw[_mf] at c;have:=bP.mp c.1;exact _mf.mpr ⟨mem_range.mpr (by omega),c.2⟩
  · rw[ao,_mf] at c;have i:w∉cD 14 D:=fun m=>d (_mf.mpr ⟨m,c.2⟩);rw[bP] at i;simp[d0 e w (by omega)]
 have p:(dq 14 D).filter (fun u=>(ag 14 D u.1∩T).Nonempty)=(cz 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty)∪(aj 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty):=by
  ext u;have he:=eY_dom e h;simp only[aj,da,_mu,_mf,_md];constructor
  · intro a;by_cases k:u∈cz 14 D b;{exact Or.inl ⟨k,a.2⟩};{exact Or.inr ⟨⟨⟨a.1,a.2.mono inter_subset_left⟩,k⟩,a.2⟩}
  · rintro (a|a);{exact⟨(_mf.mp (he a.1)).1,a.2⟩};{exact⟨a.1.1.1,a.2⟩}
 have q:Disjoint ((cz 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty)) ((aj 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty)):=disjoint_filter_filter disjoint_sdiff
 have r:(cz 14 D b).filter (fun u=>(ag 14 D u.1∩T).Nonempty)=((al 14 D).filter (fun v=>(ag 14 D (b v)∩T).Nonempty)).image (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ)):=by rw[cz,filter_image]
 rw[l,p,_cud q,r,_cij ((je_dom h).mono (coe_subset.mpr (_fs _ _)))]
def aZ (D:Dag) (b:O->ℕ) (x:O):Finset (Σ _:ℕ,ℕ):=(aj 14 D b).filter (fun u=>x∈ag 14 D u.1)
lemma ay {D:Dag} {b:O->ℕ} {x:O} {u:Σ _:ℕ,ℕ}:u∈aZ D b x↔u∈aj 14 D b/\x∈ag 14 D u.1:=_mf
lemma fC {D:Dag} {b:O->ℕ} {u:Σ _:ℕ,ℕ} (a:u∈aj 14 D b) {x:O} (c:x∈ag 14 D u.1):x∈al 14 D:=_B.fB a c
lemma m9_dom {D:Dag} (h:ai 14 D) (a:ar D) (x:O):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card=1+bn D (ao 14 D {x}):=by
 have c:=co h {x} (by rw[oc a];simp);rwa[_cs] at c
lemma ez_dom {D:Dag} (h:ai 14 D) (a:ar D) {b:O->ℕ} (c:cU_dom D b) (x:O):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card=1+((al 14 D).filter (fun v=>x∈ag 14 D (b v))).card+(aZ D b x).card:=by
 have j:=m9_dom h a x;have f:=d9_dom h.1 c {x}
 have t:∀ S:o,(S∩{x}).Nonempty↔x∈S:=by intro S;constructor;{rintro ⟨y,hy⟩;rw[_mn,_ms] at hy;exact hy.2▸hy.1};{intro hx;exact ⟨x,_mn.2 ⟨hx,_mss x⟩⟩}
 simp only[t] at f;unfold aZ;omega
abbrev isClean (I:o) (x:O):Prop:=x≠1/\x≠3/\x≠8/\x≠10\/(x=1\/x=3)/\(0:O)∈I\/(x=8\/x=10)/\(7:O)∈I
def leakRoot (x:O):O:=if x=1\/x=3 then 0 else if x=8\/x=10 then 7 else x
lemma leakEq:∀ v x:O,x∈dom v->v=x\/v=leakRoot x:=by decide +kernel
lemma bj_noleak {D:Dag} (h:ai 14 D) (a:ar D) {b:O->ℕ} (c:cU_dom D b) {x:O} (hnl:leakRoot x∈al 14 D->leakRoot x≠x->x∉ag 14 D (b (leakRoot x))):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=2+(aZ D b x).card:=by
 have e:=ez_dom h a c x
 have t:(al 14 D).filter (fun v=>x∈ag 14 D (b v))⊆{x}:=by
  intro v hv;obtain ⟨m,j⟩:=_mf.1 hv;rcases leakEq v x ((c v m).2.2.1 j) with rfl|rfl;{exact _mss _};rw[_ms];by_contra q;exact hnl m q j
 have u:=_cl t;rw[_cs] at u;omega
lemma bj_clean {D:Dag} (h:ai 14 D) (a:ar D) {b:O->ℕ} (c:cU_dom D b) {x:O} (hx:isClean (aa 14 D) x):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=2+(aZ D b x).card:=by
 apply bj_noleak h a c;intro m j;rcases hx with ⟨p,q,r,s⟩|⟨p,t⟩|⟨p,t⟩
 · exact False.elim (j (by simp[leakRoot,p,q,r,s]))
 · rcases p with rfl|rfl <;> exact False.elim ((aN.1 t) m)
 · rcases p with rfl|rfl <;> exact False.elim ((aN.1 t) m)
lemma bj_any {D:Dag} (h:ai 14 D) (a:ar D) {b:O->ℕ} (c:cU_dom D b) (x:O):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=3+(aZ D b x).card:=by
 have e:=ez_dom h a c x
 have t:(al 14 D).filter (fun v=>x∈ag 14 D (b v))⊆{x,leakRoot x}:=by intro v hv;obtain ⟨m,j⟩:=_mf.1 hv;rw[_mi,_ms];exact leakEq v x ((c v m).2.2.1 j)
 have u:=(_cl t).trans card_le_two;omega
lemma cZ_dom {D:Dag} (e:au 14 D) {b:O->ℕ} (c:cU_dom D b) (T:o) (hnl:∀ v∈al 14 D,(dom v∩T).Nonempty->v∈T):bn D (ao 14 D T)+(al 14 D).card<=(T∩al 14 D).card+bd 14 D:=by
 have d:=d9_dom e c T;have hs:=bS_dom e c;have hfl:=_cfl (aj 14 D b) (fun u=>(ag 14 D u.1∩T).Nonempty)
 have hsub:(al 14 D).filter (fun v=>(ag 14 D (b v)∩T).Nonempty)⊆T∩al 14 D:=fun v hv=>by
  rw[_mf] at hv;obtain⟨w,hw⟩:=hv.2;rw[_mn] at hw;exact _mn.2 ⟨hnl v hv.1 ⟨w,_mn.2 ⟨(c v hv.1).2.2.1 hw.1,hw.2⟩⟩,hv.1⟩
 have hle:=_cl hsub;omega
lemma eq_dom {D:Dag} (y:au 14 D) (B:ar D) {u v:O} (C:aP u v):∃ j,j<D.length/\cR D j=true/\val D (b4 u v) (14+j)=true/\u∉ag 14 D (14+j)/\v∉ag 14 D (14+j)/\∃ s:_d,u∈ag 14 D (aw D (j,s))/\v∉ag 14 D (aw D (j,s))/\v∈ag 14 D (aw D (j,!s))/\u∉ag 14 D (aw D (j,!s)):=by
 classical
 have g:∃ w,val D (b4 u v) w=true/\u∉ag 14 D w/\v∉ag 14 D w:=⟨bH 14 D,B.1 _ ⟨u,v,C,by simp[b4],by simp[b4]⟩,by rw[oc B];simp,by rw[oc B];simp⟩
 obtain⟨b,c,d⟩:=Nat.find_spec g
 have e:∀ a,a<Nat.find g->val D (b4 u v) a=true->u∈ag 14 D a\/v∈ag 14 D a:=fun a z E=>by by_contra l;rw[not_or] at l;exact Nat.find_min g z ⟨E,l.1,l.2⟩
 generalize Nat.find g=w at b c d e
 have J:w<14+D.length:=by by_contra l;rw[fs D _ w (by omega)] at b;exact _fnt b
 have L:14<=w:=by by_contra l;have l':w<14:=Nat.lt_of_not_ge l;rw[bY D _ w l'] at b;have K:ag 14 D w={⟨w,l'⟩}:=dr D ⟨w,l'⟩;rw[K,_ms] at c d;simp only[b4,Bool.or_eq_true,decide_eq_true_eq] at b;rcases b with h|h;{exact c h.symm};{exact d h.symm}
 obtain⟨j,rfl⟩:∃ j,w=14+j:=⟨w - 14,by omega⟩;have m:j<D.length:=by{omega};obtain⟨z,F,-⟩:=y j m;have p:=b;rw[cS y _ j m] at b;rw[fY y j m] at c d;cases A:cR D j
 · exfalso;rw[A] at b c d;simp only[gop_false,Bool.or_eq_true] at b;simp only[Bool.false_eq_true,ite_false,_mu,not_or] at c d;rcases b with h|h;{rcases e _ z h with h'|h';{exact c.1 h'};{exact d.1 h'}};{rcases e _ F h with h'|h';{exact c.2 h'};{exact d.2 h'}}
 · rw[A] at b c d;simp only[gop_true,Bool.and_eq_true] at b;simp only[ite_true,_mn,not_and] at c d;have f:u∉ag 14 D (14+j)/\v∉ag 14 D (14+j):=by rw[cB y m A];simp only[_mn,not_and];exact⟨c,d⟩
   refine⟨j,m,A,p,f.1,f.2,?_⟩;rcases e _ z b.1 with q|q
   · have r:u∉ag 14 D (ck D j):=c q;have t:v∈ag 14 D (ck D j):=(e _ F b.2).resolve_left r;exact⟨false,by simpa[aw] using q,by simpa[aw] using fun h=>d h t,by simpa[aw] using t,by simpa[aw] using r⟩
   · have r:v∉ag 14 D (ck D j):=d q;have x:u∈ag 14 D (ck D j):=(e _ F b.2).resolve_right r;exact⟨true,by simpa[aw] using x,by simpa[aw] using r,by simpa[aw] using q,by simpa[aw] using fun h=>c h x⟩
lemma ci_dom {D:Dag} (h:ai 14 D) (t:ar D) {v:O} (B:v∈aa 14 D):∃ e:ℕ×_d,e.1<D.length/\cR D e.1=true/\v∈ag 14 D (aw D e)/\ag 14 D (aw D e)⊆dom v/\ag 14 D (14+e.1)⊆dom v\{v}/\(∀ a,aP v a->a∈ag 14 D (aw D (e.1,!e.2)))/\aE 14 D (ao 14 D {v})={e}/\aW 14 D (ao 14 D {v})=∅:=by
 have u:=h.1;have w:=co h {v} (by rw[oc t];simp);rw[kG B,_cs] at w
 have b:∀ a,aP v a->∃ j s,j<D.length/\cR D j=true/\(j,s)∈aE 14 D (ao 14 D {v})/\a∈ag 14 D (aw D (j,!s)):=by intro a d;obtain⟨j,C,F,-,y,-,s,I,-,J,-⟩:=eq_dom u t d;exact⟨j,s,C,F,df.mpr ⟨C,I,y⟩,J⟩
 have h0:∀ x:O,∃ a0:O,ac x a0=true:=by decide +kernel
 obtain⟨a0,ha0⟩:=h0 v;have z:aP v a0:=(ae v a0).1 ha0
 obtain⟨j0,s0,i,k,f,-⟩:=b a0 z;have g:(aE 14 D (ao 14 D {v})).card=1:=by have:=_cp.mpr ⟨_,f⟩;omega
 have l:aW 14 D (ao 14 D {v})=∅:=card_eq_zero.mp (by omega);obtain⟨e,m⟩:=_c1.mp g;rw[m,_ms] at f;subst f
 have hvmem:v∈ag 14 D (aw D (j0,s0)):=(df.mp (by rw[m];exact _mss _)).2.1
 have c:ag 14 D (aw D (j0,s0))⊆dom v:=fk_dom u t v _ (ds u (iF u B hvmem))
 have p:v∉ag 14 D (14+j0):=(df.mp (by rw[m];exact _mss _)).2.2
 refine⟨(j0,s0),i,k,hvmem,c,?_,?_,m,l⟩
 · intro x hx;exact _md.2 ⟨c (cr u i k s0 hx),fun hxv=>p (_ms.1 hxv▸hx)⟩
 · intro a d;obtain⟨j,s,-,-,A,K⟩:=b a d;rw[m,_ms] at A;rw[Prod.mk.injEq] at A;obtain⟨rfl,rfl⟩:=A;exact K
lemma fu_dom {D:Dag} (h:ai 14 D) (c:ar D) {u v:O} (d:aP07 u v):u∈al 14 D\/v∈al 14 D:=by
 by_contra e;rw[not_or] at e;obtain⟨eu,-,-,-,fsub,-,f,g,-⟩:=ci_dom h c (aN.mpr e.1);obtain⟨ev,-,-,-,gsub,-,-,k,-⟩:=ci_dom h c (aN.mpr e.2)
 obtain⟨j,r,-,-,l,m,s,y,-,z,-⟩:=eq_dom h.1 c d.1;have t:(j,s)∈aE 14 D (ao 14 D {u}):=df.mpr ⟨r,y,l⟩;have w:(j,!s)∈aE 14 D (ao 14 D {v}):=df.mpr ⟨r,z,m⟩
 rw[g,_ms] at t;rw[k,_ms] at w;subst t;subst w
 have hex:∃ a:O,aP u a/\a∉dom v:=by
  have hdec:∀ u v:O,ac u v=true->¬(u=0/\v=7)->¬(u=7/\v=0)->∃ a:O,ac u a=true/\a∉dom v:=by decide +kernel
  obtain⟨a,ha,hna⟩:=hdec u v ((ae u v).2 d.1) d.2.1 d.2.2;exact⟨a,(ae u a).1 ha,hna⟩
 obtain⟨a,pa,hna⟩:=hex;exact hna (gsub (f a pa))
lemma fp07 {D:Dag} (h:ai 14 D) (b:ar D):eE07 (al 14 D):=fun _ _ a=>fu_dom h b a
lemma rl {D:Dag} (h:ai 14 D) (f:ar D) (b:dI07 (aa 14 D)) (d:2<=(aa 14 D).card):∃ D':Dag,ai 14 D'/\ar D'/\D'.length=D.length/\ap 14 D'=ap 14 D/\bd 14 D'=bd 14 D/\bL 14 D'=bL 14 D/\(aa 14 D').card=(aa 14 D).card/\aa 14 D'∈d4:=by
 obtain⟨σ,hσ,c⟩:=lK b d;obtain⟨g,i,j,k,l,m,-,e⟩:=oZ σ hσ h f;refine⟨bo σ D,g,i,j,k,l,m,?_,e▸c⟩;rw[e,_cii _ σ.injective]
lemma mC {D:Dag} (h:ai 14 D) (a:D.length<=25):ap 14 D=D.length - 13/\ap 14 D<=12:=by have:=iC h;exact⟨by omega,by omega⟩
lemma od {D:Dag} (h:ai 14 D) (a:D.length<=25) {b:O->ℕ} (d:cU_dom D b) (c:eE07 (al 14 D)):7<=(al 14 D).card/\(al 14 D).card<=bd 14 D/\bd 14 D<=12/\ap 14 D<=12:=by
 have e:=eV07 c;have f:=dX_dom h.1 d;have i:=dC 14 D;have g:=(mC h a).2;exact⟨e,f,by omega,g⟩
lemma il {D:Dag} (h:ai 14 D) (a:D.length<=25) {b:O->ℕ} (d:cU_dom D b) (c:eE07 (al 14 D)):(aa 14 D).Nonempty/\2<=(aa 14 D).card/\(aa 14 D).card<=7:=by
 obtain⟨f,g,i,e⟩:=od h a d c;have j:=aV 14 D;exact⟨_cp.1 (by omega),by omega,by omega⟩
lemma nF (C:Circuit) (e:Monotone2 C) (f:∀ x:O->_d,_B.bw x->C.eval (_of x)=true) (d:∀ x:O->_d,C.eval (_of x)=true->bx x):∃ D:Dag,ai 14 D/\D.length<=C.size/\ar D:=by
 obtain⟨D,t,l,c⟩:=fV (n:=14) C e (by
  intro b;cases b
  · refine⟨b4 0 7,fun p=>?_⟩;have m:=f (b4 0 7) ((_B.ce (b4 0 7)).2 ⟨0,7,by decide,by simp[b4],by simp[b4]⟩);rw[m] at p;exact Bool.noConfusion p
  · refine⟨fun _=>false,fun p=>oa (d _ p)⟩)
  (by intro i;refine⟨fun k=>decide (k=i),fun h=>kv i (d _ (by rw[h];simp))⟩)
  (by intro i;have hex:∃ a:O,ac i a=true:=by revert i;decide +kernel
      obtain⟨a,ha⟩:=hex;refine⟨cl a,bB i (cl a),dd i _,fun s=>?_⟩
      have m:C.eval (_of (bB i (cl a)))=true:=f (bB i (cl a)) ((_B.ce _).2 ⟨i,a,(ae i a).1 ha,dm i (cl a),by simp[bB,cl]⟩)
      rw[<- s] at m;exact kv a (d _ m))
 exact⟨D,t,l,fun x q=>by rw[c x];exact f x ((_B.ce x).2 q),fun x q=>by rw[c x] at q;exact d x q⟩
lemma mU (C:Circuit) (d:Monotone2 C) (l:∀ x:O->_d,_B.bw x->C.eval (_of x)=true) (m:∀ x:O->_d,C.eval (_of x)=true->bx x) (n:C.size<=25):∃ D:Dag,ai 14 D/\ar D/\D.length<=25/\ap 14 D<=12/\2<=(aa 14 D).card/\aa 14 D∈d4:=by
 obtain⟨D0,k,p,f⟩:=nF C d l m;have h:D0.length<=25:=by omega
 obtain⟨b,s⟩:=b_dom k.1 f;have c:=fp07 k f;obtain⟨-,i,-⟩:=il k h s c
 obtain⟨D,j,q,w,-,-,-,-,t⟩:=rl k f ((kw07 D0).mp c) i;have h':D.length<=25:=by omega
 obtain⟨b',s'⟩:=b_dom j.1 q;obtain⟨-,i',-⟩:=il j h' s' (fp07 j q);exact⟨D,j,q,h',(mC j h').2,i',t⟩
def bA_dom (D:Dag) (pos:O->ℕ×_d):Prop:=(∀ i∈aa 14 D,(pos i).1<D.length/\cR D (pos i).1=true/\ag 14 D (14+(pos i).1)⊆dom i\{i}/\(∀ a,aP i a->a∈ag 14 D (aw D (pos i)))/\i∈ag 14 D (aw D (am (pos i)))/\ag 14 D (aw D (am (pos i)))⊆dom i/\af 14 D i={am (pos i)})/\Set.InjOn pos (aa 14 D)
lemma bQ_dom {D:Dag} (h:ai 14 D) (t:ar D):∃ pos:O->ℕ×_d,bA_dom D pos:=by
 classical
 have hc:∀ i:O,∃ p:ℕ×_d,i∈aa 14 D->p.1<D.length/\cR D p.1=true/\ag 14 D (14+p.1)⊆dom i\{i}/\(∀ a,aP i a->a∈ag 14 D (aw D p))/\i∈ag 14 D (aw D (am p))/\ag 14 D (aw D (am p))⊆dom i/\af 14 D i={am p}:=by
  intro i;by_cases hi:i∈aa 14 D
  · obtain⟨e,h1,h2,h3,h4,h5,h6,h7,-⟩:=ci_dom h t hi
    refine⟨am e,fun _=>⟨h1,h2,h5,fun a ha=>by rw[am];exact h6 a ha,by rw[aB];exact h3,by rw[aB];exact h4,by rw[aB];exact h7⟩⟩
  · exact⟨(0,false),fun h=>absurd h hi⟩
 choose pos hpos using hc;refine⟨pos,hpos,fun i hi j hj eq1=>?_⟩
 have h1:=(hpos j hj).2.2.2.2.2.1 (eq1▸(hpos i hi).2.2.2.2.1)
 have h2:=(hpos i hi).2.2.2.2.2.1 (eq1.symm▸(hpos j hj).2.2.2.2.1)
 exact dom_anti i j h1 h2
lemma aJ {D:Dag} {pos:O->ℕ×_d} (b:bA_dom D pos) {i a:O} (d:i∈aa 14 D) (c:aP i a):pos i∈af 14 D a:=by
 obtain⟨e,-,hsub,g,-⟩:=b.1 i d;refine ak.2 ⟨e,g a c,fun ha=>?_⟩
 have hdm:=(_md.1 (hsub ha)).1;have:∀ u v:O,ac u v=true->v∉dom u:=by decide +kernel
 exact this i a ((ae i a).2 c) hdm
lemma cV_dom {D:Dag} {pos:O->ℕ×_d} (b:bA_dom D pos) {j t:O} (hj:j∈aa 14 D) (ht:t∈ag 14 D (aw D (pos j))) (hnd:t∉dom j):pos j∈af 14 D t:=by
 obtain⟨e,-,hsub,-⟩:=b.1 j hj;exact ak.2 ⟨e,ht,fun h=>hnd (_md.1 (hsub h)).1⟩
lemma em_dom {D:Dag} {pos:O->ℕ×_d} (a:bA_dom D pos) {i t:O} (b:i∈aa 14 D) (c:am (pos i)∈af 14 D t):t∈dom i:=(a.1 i b).2.2.2.2.2.1 (ak.1 c).2.1
lemma cd {D:Dag} {pos:O->ℕ×_d} (a:bA_dom D pos) {i:O} (b:i∈aa 14 D):i∈ag 14 D (aw D (am (pos i))):=(a.1 i b).2.2.2.2.1
lemma el {D:Dag} (b:au 14 D) {x:O} {e:ℕ×_d} (c:e∈af 14 D x):am e∉af 14 D x:=by
 exact _B.eh b c
lemma bf {D:Dag} (h:ai 14 D) (j:ar D) {pos:O->ℕ×_d} (a:bA_dom D pos) {x y:O} (c:aP x y):∃ e∈af 14 D x,am e∈af 14 D y/\(∀ i∈aa 14 D,e=pos i->y∈dom i)/\∀ i∈aa 14 D,am e=pos i->x∈dom i:=by
 obtain⟨g,hg,hcr,-,hx,hy,s,hxs,-,hys,-⟩:=eq_dom h.1 j c
 refine⟨(g,s),ak.2 ⟨hg,hxs,hx⟩,ak.2 ⟨hg,hys,hy⟩,fun i hi he=>em_dom a hi (he▸ak.2 ⟨hg,hys,hy⟩),fun i hi he=>em_dom a hi (by rw[<- he,aB];exact ak.2 ⟨hg,hxs,hx⟩)⟩
abbrev d6:=@_B.d5
lemma mm {α:Type} [DecidableEq α] {s:Finset α} {a b c d:α} (n:a∈s) (p:b∈s) (q:c∈s) (r:d∈s) (g:a≠b) (h:a≠c) (i:a≠d) (j:b≠c) (k:b≠d) (l:c≠d):4<=s.card:=by
 have f:({a,b,c,d}:Finset α)⊆s:=by intro e m;simp only[_mi,_ms] at m;rcases m with rfl|rfl|rfl|rfl <;> assumption
 have:=_cl f;rwa[_cin (by simp[g,h,i]),_cin (by simp[j,k]),_c2 l] at this
lemma mn {α:Type} [DecidableEq α] {s:Finset α} {a b c d e:α} (t:a∈s) (u:b∈s) (v:c∈s) (w:d∈s) (y:e∈s) (g:a≠b) (h:a≠c) (i:a≠d) (j:a≠e) (k:b≠c) (l:b≠d) (m:b≠e) (n:c≠d) (p:c≠e) (q:d≠e):5<=s.card:=by
 have f:({a,b,c,d,e}:Finset α)⊆s:=by intro x r;simp only[_mi,_ms] at r;rcases r with rfl|rfl|rfl|rfl|rfl <;> assumption
 have:=_cl f;rwa[_cin (by simp[g,h,i,j]),_cin (by simp[k,l,m]),_cin (by simp[n,p]),_c2 q] at this
abbrev aT:=@_B.aS
abbrev gG:=@_B.gF
lemma gh {α:Type} [DecidableEq α] {s:Finset α} {a b c d:α} (h1:a∈s) (h2:b∈s) (h3:c∈s) (h4:d∈s) (hab:a≠b) (hac:a≠c) (had:a≠d) (hbc:b≠c) (hbd:b≠d) (hcd:c≠d) (hm:s.card<=4):∀ e∈s,e=a\/e=b\/e=c\/e=d:=by
 intro e he;by_contra hne;simp only[not_or] at hne;have:=mm (s:=s.erase e) (_me.2 ⟨Ne.symm hne.1,h1⟩) (_me.2 ⟨Ne.symm hne.2.1,h2⟩) (_me.2 ⟨Ne.symm hne.2.2.1,h3⟩) (_me.2 ⟨Ne.symm hne.2.2.2,h4⟩) hab hac had hbc hbd hcd;rw[card_erase_of_mem he] at this;omega
lemma dJ {α:Type} [DecidableEq α] {u1 u2:α} (l:u1≠u2) {A B:Finset α} (m:A⊆{u1,u2}) (n:B⊆{u1,u2}) (g:A.Nonempty) (h:B.Nonempty) (d:¬ A⊆B) (e:¬ B⊆A):(A={u1}/\B={u2})\/(A={u2}/\B={u1}):=by
 obtain ⟨x,hx,hn⟩:=Finset.not_subset.1 d;obtain ⟨y,hy,hm⟩:=Finset.not_subset.1 e
 have p:=m hx;have q:=n hy;simp only[_mi,_ms] at p q;rcases p with rfl|rfl <;> rcases q with rfl|rfl
 · exact False.elim (hm hx)
 · left;constructor <;> ext z <;> simp only[_ms];all_goals grind [Finset.subset_iff,Finset.mem_insert,Finset.mem_singleton]
 · right;constructor <;> ext z <;> simp only[_ms];all_goals grind [Finset.subset_iff,Finset.mem_insert,Finset.mem_singleton]
 · exact False.elim (hm hx)
lemma gO_dom {D:Dag} (g:au 14 D) (E:ar D) (A:o) (v:val D (bM A) (bH 14 D)=false) (x:O) (y:∃ a∈A,aP x a):∃ j s,j<D.length/\cR D j=true/\x∈ag 14 D (aw D (j,s))/\x∉ag 14 D (14+j)/\Disjoint (ag 14 D (aw D (j,s))) A:=by
 by_contra i;have c:∀ j s,j<D.length->cR D j=true->x∈ag 14 D (aw D (j,s))->x∉ag 14 D (14+j)->val D (bM A) (aw D (j,s))=true/\val D (bB x (bM A)) (aw D (j,s))=true:=by
  intro j s d h e z;have k:¬ Disjoint (ag 14 D (aw D (j,s))) A:=fun J=>i ⟨j,s,d,h,e,z,J⟩;rw[not_disjoint_iff] at k;obtain⟨a,l,m⟩:=k;exact⟨cO g l (by simp[bM,m]),cO g l (by simp[bB,bM,m])⟩
 have B:∀ w,x∉ag 14 D w->val D (bM A) w=val D (bB x (bM A)) w:=by
  intro w;induction w using Nat.strong_induction_on with
  | _ w ih=>
   intro f;by_cases u:w<14
   · rw[bY D _ w u,bY D _ w u];have K:ag 14 D w={⟨w,u⟩}:=dr D ⟨w,u⟩;rw[K,_ms] at f;exact dd x _ _ (fun L=>f L.symm)
   · by_cases M:w<14+D.length
     · obtain⟨j,rfl⟩:∃ j,w=14+j:=⟨w - 14,by omega⟩;have d:j<D.length:=by{omega};obtain⟨p,C,-⟩:=g j d;rw[cS g _ j d,cS g _ j d];cases h:cR D j
       · rw[de g d h,_mu,not_or] at f;rw[ih _ p f.1,ih _ C f.2]
       · have q:=f;rw[cB g d h,_mn,not_and] at q;by_cases b:x∈ag 14 D (cj D j)
         · have e:=c j false d h (by rw[aX];exact b) f;rw[aX] at e;rw[ih _ C (q b),e.1,e.2]
         · by_cases r:x∈ag 14 D (ck D j)
           · have e:=c j true d h (by rw[bh];exact r) f;rw[bh] at e;rw[ih _ p b,e.1,e.2]
           · rw[ih _ p b,ih _ C r]
     · rw[fs D _ w (by omega),fs D _ w (by omega)]
 have t:=B (bH 14 D) (by rw[oc E];exact notMem_empty x);obtain⟨a,p,b⟩:=y;have F:=E.1 (bB x (bM A)) ⟨x,a,b,dm x (bM A),by simp[bB,bM,p]⟩;rw[<- t,v] at F;exact _fnt F
lemma fm_dom {D:Dag} (g:au 14 D) (e:ar D) (A:o) (h:∀ a∈A,∀ b∈A,¬ dj a b) (x:O) (d:∃ a∈A,aP x a):∃ j s,j<D.length/\cR D j=true/\x∈ag 14 D (aw D (j,s))/\x∉ag 14 D (14+j)/\Disjoint (ag 14 D (aw D (j,s))) A:=by
 refine gO_dom g e A ?_ x d;by_contra c;rw[_nf] at c;obtain⟨a,b,hab,ha,hb⟩:=e.2 _ c;simp only[bM,decide_eq_true_eq] at ha hb;exact h a ha b hb hab
lemma kb_dom {D:Dag} (g:au 14 D) (e:ar D) {x a:O} (h:∃ y:O,ac x y=true/\bK y a=false):∃ f∈af 14 D x,a∉ag 14 D (aw D f):=by
 obtain⟨y,hy,hna⟩:=h
 have hind:∀ u∈({a,y}:o),∀ v∈({a,y}:o),¬ dj u v:=by intro u hu v hv;simp only[_mi,_ms] at hu hv;rcases hu with rfl|rfl <;> rcases hv with rfl|rfl;{exact ij _};{exact fun h=>b3.1 hna (lL h)};{exact b3.1 hna};{exact ij _}
 obtain⟨j,s,hj,-,h1,h2,hd⟩:=fm_dom g e {a,y} hind x ⟨y,by simp,(ae x y).1 hy⟩
 exact⟨(j,s),ak.2 ⟨hj,h1,h2⟩,fun ha=>_dl.1 hd ha (by simp)⟩
def mV (x a b:O):_d:=decide (x≠a)&&decide (x≠b)&&(!bK a b)&&decide (∃ y:O,ac x y=true/\bK y a=false/\bK y b=false)
lemma bE_dom {D:Dag} (g:au 14 D) (e:ar D) {x a b:O} (hm:mV x a b=true):∃ f∈af 14 D x,a∉ag 14 D (aw D f)/\b∉ag 14 D (aw D f):=by
 simp only[mV,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at hm
 obtain⟨⟨⟨-,-⟩,hab⟩,y,hy,ha,hb⟩:=hm
 have hind:∀ u∈({a,b,y}:o),∀ v∈({a,b,y}:o),¬ dj u v:=by intro u hu v hv;simp only[_mi,_ms] at hu hv;rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl;{exact ij _};{exact b3.1 hab};{exact fun h=>b3.1 ha (lL h)};{exact fun h=>b3.1 hab (lL h)};{exact ij _};{exact fun h=>b3.1 hb (lL h)};{exact b3.1 ha};{exact b3.1 hb};{exact ij _}
 obtain⟨j,s,hj,-,h1,h2,hd⟩:=fm_dom g e {a,b,y} hind x ⟨y,by simp,(ae x y).1 hy⟩
 exact⟨(j,s),ak.2 ⟨hj,h1,h2⟩,fun h=>_dl.1 hd h (by simp),fun h=>_dl.1 hd h (by simp)⟩
def cmOk (i x t:O):_d:=decide (ac i x=true/\t≠x/\∃ r:O,ac i r=true/\r≠x/\bK r t=false/\mV x r t=true)
def quOk (i x:O):_d:=decide (∃ r:O,ac i r=true/\∃ y:O,ac x y=true/\bK y r=false)
lemma cmOk_quOk:∀ i x t:O,cmOk i x t=true->quOk i x=true:=by decide +kernel
lemma qu_dom {D:Dag} (h:ai 14 D) (u:ar D) {pos:O->ℕ×_d} (b:bA_dom D pos) {i x:O} (hi:i∈aa 14 D) (hix:aP i x) (hq:quOk i x=true) (hw:(af 14 D x).card<=2):∃ Z,Z≠pos i/\af 14 D x={pos i,Z}/\∀ t,cmOk i x t=true->t∉ag 14 D (aw D Z)/\Z∉af 14 D t:=by
 simp only[quOk,decide_eq_true_eq] at hq;obtain⟨r0,hr0,hy0⟩:=hq;obtain⟨Z,hZx,hr0Z⟩:=kb_dom h.1 u hy0
 have hp:pos i∈af 14 D x:=aJ b hi hix
 have hne:Z≠pos i:=fun eq1=>hr0Z (eq1▸(b.1 i hi).2.2.2.1 r0 ((ae i r0).1 hr0))
 have hW:af 14 D x={pos i,Z}:=symm (_eqc (fun f hf=>by rw[_mi,_ms] at hf;rcases hf with rfl|rfl;{exact hp};{exact hZx}) (by rw[_c2 (Ne.symm hne)];exact hw))
 refine⟨Z,hne,hW,fun t ht=>?_⟩
 simp only[cmOk,decide_eq_true_eq] at ht;obtain⟨-,-,r,hr,-,hrt,hm⟩:=ht
 obtain⟨f,hf,hfr,hft⟩:=bE_dom h.1 u hm;rw[hW,_mi,_ms] at hf
 rcases hf with rfl|rfl;{exact absurd ((b.1 i hi).2.2.2.1 r ((ae i r).1 hr)) hfr}
 · exact⟨hft,fun hZt=>hft (ak.1 hZt).2.1⟩
lemma cx_dom {D:Dag} (h:ai 14 D) (s:ar D) {pos:O->ℕ×_d} (a:bA_dom D pos) {i1 i2 u v:O} (b:i1∈aa 14 D) (c:i2∈aa 14 D) (t:i1≠i2/\ac i1 u=true/\ac i2 u=true/\ac u v=true/\v≠i1/\v≠i2) (hdom:v∈aa 14 D\/(v∉dom i1/\v∉dom i2)):3<=(af 14 D u).card:=by
 obtain⟨g,m,n,i,j,k⟩:=t;rw[ae] at m n i;have p:=aJ a b m;have q:=aJ a c n;have d:pos i1≠pos i2:=fun e=>g (a.2 b c e)
 by_cases f:v∈aa 14 D;{exact d6 p q (aJ a f (bm i)) d (fun e=>j.symm (a.2 b f e)) (fun e=>k.symm (a.2 c f e))}
 · rcases hdom with hv|⟨h1,h2⟩;{exact absurd hv f}
   obtain⟨e,w,-,r,-⟩:=bf h s a i
   exact d6 p q w d (fun l=>h1 (r i1 b l.symm)) (fun l=>h2 (r i2 c l.symm))
lemma dl_dom {D:Dag} (h:ai 14 D) (g:ar D) {pos:O->ℕ×_d} (a:bA_dom D pos) (z k v iz ik:O) (b:iz∈aa 14 D) (c:ik∈aa 14 D) (t:z∉dom ik/\k∉dom iz/\v∉dom iz) (x:ac iz z=true/\ac ik k=true/\ac z k=true/\ac z v=true/\cmOk ik k v=true) (i:(af 14 D z).card<=2) (j:(af 14 D k).card<=2):False:=by
 obtain⟨g1,g2,g3,g4,gcm⟩:=x;rw[ae] at g1 g2 g3 g4;obtain⟨Dk,-,l,m⟩:=qu_dom h g a c g2 (cmOk_quOk ik k v gcm) j
 obtain⟨e,y,d,A,A'⟩:=bf h g a g3;obtain⟨e',y',d',x',-⟩:=bf h g a g4
 rw[l,_mi,_ms] at d;have B:am e=Dk:=d.resolve_left (fun r=>t.1 (A' ik c r))
 rcases gG (aJ a b g1) y (fun r=>t.2.1 (A iz b r.symm)) i e' y' with s|s;{exact t.2.2 (x' iz b s)};{exact (m v gcm).2 (by rw[<- B,<-s];exact d')}
lemma fR_dom {D:Dag} (h:ai 14 D) (k:ar D) {pos:O->ℕ×_d} (a:bA_dom D pos) (u k1 k2 v ik1 ik2:O) (b:ik1∈aa 14 D) (c:ik2∈aa 14 D) (M:u∉dom ik1/\u∉dom ik2) (N:ac u k1=true/\ac u k2=true/\ac u v=true/\ac ik1 k1=true/\ac ik2 k2=true/\cmOk ik1 k1 k2=true/\cmOk ik1 k1 v=true/\cmOk ik2 k2 v=true) (B:(af 14 D u).card<=2) (l:(af 14 D k1).card<=2) (m:(af 14 D k2).card<=2):False:=by
 obtain⟨g1,g2,g3,g4,g5,hc12,hc1v,hc2v⟩:=N;rw[ae] at g1 g2 g3 g4 g5
 obtain⟨D1,-,F,r⟩:=qu_dom h k a b g4 (cmOk_quOk ik1 k1 k2 hc12) l;obtain⟨D2,-,s,G⟩:=qu_dom h k a c g5 (cmOk_quOk ik2 k2 v hc2v) m
 obtain⟨e1,H,f,-,hf1'⟩:=bf h k a g1;obtain⟨e2,I,g,-,hf2'⟩:=bf h k a g2;obtain⟨e3,J,i,-,-⟩:=bf h k a g3
 rw[F,_mi,_ms] at f;have x:am e1=D1:=f.resolve_left (fun K=>M.1 (hf1' ik1 b K))
 rw[s,_mi,_ms] at g;have y:am e2=D2:=g.resolve_left (fun K=>M.2 (hf2' ik2 c K))
 have z:e1≠e2:=fun L=>by have A:D1=D2:=by{rw[<- x,<-y,L]};have j:D2∈af 14 D k2:=by{rw[s];simp};exact (r k2 hc12).2 (A▸j)
 rcases gG H I z B e3 J with rfl|rfl;{exact (r v hc1v).2 (x▸i)};{exact (G v hc2v).2 (y▸i)}
def bk_x (D:Dag) (x:O) (a b:ℕ):Prop:=bk 14 D a b/\x∈ag 14 D a/\x∈ag 14 D b
lemma bk_x_inv {D:Dag} (e:au 14 D) {x:O} (hM:aW 14 D (ao 14 D {x})=∅) {a a' b:ℕ} (h1:bk_x D x a b) (h2:bk_x D x a' b):a=a':=by
 by_contra hne;obtain⟨j,s,hj,rfl,ha⟩:=fj.1 h1.1;obtain⟨j',s',hj',hjEq,ha'⟩:=fj.1 h2.1
 have hjj:j'=j:=by{omega};subst j';have hxv:x∈ag 14 D (14+j):=h1.2.2
 apply (dL e hM hj hxv).2
 cases s <;> cases s'
 · rw[aX] at ha ha';exact absurd (ha.symm.trans ha') hne
 · rw[aX] at ha;rw[bh] at ha';exact⟨ha▸h1.2.1,ha'▸h2.2.1⟩
 · rw[bh] at ha;rw[aX] at ha';exact⟨ha'▸h2.2.1,ha▸h1.2.1⟩
 · rw[bh] at ha ha';exact absurd (ha.symm.trans ha') hne
lemma bk_x_ag {D:Dag} (e:au 14 D) {x:O} (hM:aW 14 D (ao 14 D {x})=∅) {a b:ℕ} (hp:Relation.ReflTransGen (bk_x D x) a b):ag 14 D a⊆ag 14 D b:=by
 induction hp with
 | refl=>exact Subset.refl _
 | @tail u v _ hstep ih=>
  obtain⟨j,s,hj,rfl,hu⟩:=fj.1 hstep.1;have hor:=(dL e hM hj hstep.2.2).1
  refine ih.trans (by rw[de e hj hor];cases s;{rw[aX] at hu;rw[hu];exact subset_union_left};{rw[bh] at hu;rw[hu];exact subset_union_right})
lemma reconv_aW {D:Dag} (e:au 14 D) {x:O} (hM:aW 14 D (ao 14 D {x})=∅) {u1 u2 c:ℕ} (h1:Relation.ReflTransGen (bk_x D x) u1 c) (h2:Relation.ReflTransGen (bk_x D x) u2 c):ag 14 D u1⊆ag 14 D u2\/ag 14 D u2⊆ag 14 D u1:=by
 rcases gq (R:=bk_x D x) (fun a a' b=>bk_x_inv e hM) h1 h2 with p|p;{exact Or.inl (bk_x_ag e hM p)};{exact Or.inr (bk_x_ag e hM p)}
lemma reach_one_leaf {D:Dag} (h:ai 14 D) (hD:ar D) {x:O} (hM:aW 14 D (ao 14 D {x})=∅):∀ c,x∈ag 14 D c->∃ e∈af 14 D x,Relation.ReflTransGen (bk_x D x) c (aw D e):=by
 classical
 intro c;generalize Q:14+D.length - c=k;induction k using Nat.strong_induction_on generalizing c with
 | _ k ih=>
  intro hxc;have hlt:=cP hxc;have hne:c≠bH 14 D:=fun h0=>notMem_empty x (oc hD▸h0▸hxc)
  have hf:1<=aF D c:=h.2.1 c (by unfold bH at hne;omega)
  obtain⟨j,hj⟩:=_cp.1 hf;simp only[bV,_mf,mem_range] at hj;obtain⟨hjlt,hjk⟩:=hj
  obtain⟨s,hs⟩:∃ s:_d,aw D (j,s)=c:=by rcases hjk with l|l;{exact⟨false,by rw[aX];exact l⟩};{exact⟨true,by rw[bh];exact l⟩}
  have hclt:c<14+j:=hs▸dh h.1 hjlt s
  by_cases hxj:x∈ag 14 D (14+j)
  · obtain⟨e,he,hp⟩:=ih (14+D.length - (14+j)) (by omega) (14+j) rfl hxj
    exact⟨e,he,Relation.ReflTransGen.head ⟨hs▸cM hjlt s,hxc,hxj⟩ hp⟩
  · exact⟨(j,s),ak.2 ⟨hjlt,hs▸hxc,hxj⟩,hs▸Relation.ReflTransGen.refl⟩
lemma dV_tree {D:Dag} (h:ai 14 D) (hD:ar D) {x:O} (hM:aW 14 D (ao 14 D {x})=∅) {r:ℕ} (hxr:x∈ag 14 D r) (hfr:2<=aF D r):∃ P Q:ℕ×_d,P.1≠Q.1/\P∈af 14 D x/\Q∈af 14 D x/\Relation.ReflTransGen (bk_x D x) r (aw D P)/\Relation.ReflTransGen (bk_x D x) r (aw D Q):=by
 classical
 have n:=h.1
 have d:∀ j∈bV D r,j<D.length/\r<14+j/\(cj D j=r\/ck D j=r):=fun j J=>by simp only[bV,_mf,mem_range] at J;have:=n j J.1;exact⟨J.1,by omega,J.2⟩
 have rfn:∀ j∈bV D r,∃ e∈af 14 D x,((e.1=j/\aw D e=r)\/Relation.ReflTransGen (bk_x D x) (14+j) (aw D e))/\Relation.ReflTransGen (bk_x D x) r (aw D e):=by
  intro j J;obtain⟨hjlt,hrlt,hjk⟩:=d j J;obtain⟨s,hs⟩:∃ s:_d,aw D (j,s)=r:=by rcases hjk with l|l;{exact⟨false,by rw[aX];exact l⟩};{exact⟨true,by rw[bh];exact l⟩}
  by_cases hxj:x∈ag 14 D (14+j)
  · obtain⟨e,he,hp⟩:=reach_one_leaf h hD hM (14+j) hxj
    exact⟨e,he,Or.inr hp,Relation.ReflTransGen.head ⟨hs▸cM hjlt s,hxr,hxj⟩ hp⟩
  · exact⟨(j,s),ak.2 ⟨hjlt,hs▸hxr,hxj⟩,Or.inl ⟨rfl,hs⟩,hs▸Relation.ReflTransGen.refl⟩
 obtain⟨j1,B,j2,C,L⟩:=one_lt_card.1 (show 1<(bV D r).card from hfr)
 have hl:∀ ja∈bV D r,∀ jb∈bV D r,ja≠jb->¬ Relation.ReflTransGen (bk_x D x) (14+ja) (14+jb):=by
  intro ja hja jb hjb hab hp;obtain⟨-,hlta,-⟩:=d ja hja;obtain⟨hjlb,-,hm⟩:=d jb hjb
  rcases Relation.ReflTransGen.cases_tail hp with heq|⟨u,hu1,M⟩;{exact hab (by omega)}
  · have E:=dt n (fun _ _ s=>s.1) hu1
    have hstep_r:bk_x D x r (14+jb):=⟨by rcases hm with l|l;{exact l▸cM hjlb false};{exact l▸cM hjlb true},hxr,M.2.2⟩
    have hu_eq:=bk_x_inv n hM M hstep_r;omega
 obtain⟨P,hPx,hP2,hPr⟩:=rfn j1 B;obtain⟨Q,hQx,hQ2,hQr⟩:=rfn j2 C
 refine⟨P,Q,fun hPQ=>?_,hPx,hQx,hPr,hQr⟩
 have hQP:Q=P:=by rcases ka hPQ with f|f;{exact f};exfalso;exact el n hPx (f▸hQx)
 rw[hQP] at hQ2;rcases hP2 with ⟨p1,p2⟩|p <;> rcases hQ2 with ⟨q1,q2⟩|q
 · exact L (p1.symm.trans q1)
 · have E:=dt n (fun _ _ s=>s.1) q;have:=(d j2 C).2.1;rw[p2] at E;omega
 · have E:=dt n (fun _ _ s=>s.1) p;have:=(d j1 B).2.1;rw[q2] at E;omega
 · rcases gq (R:=bk_x D x) (fun a a' b=>bk_x_inv n hM) p q with h12|h21;{exact hl j1 B j2 C L h12};{exact hl j2 C j1 B L.symm h21}
lemma aW_ao_r_le_aW_ao_x {D:Dag} (e:au 14 D) {b:O->ℕ} (hb:cU_dom D b) {r x:O} (hr:r∈al 14 D) (hxr:x∈ag 14 D (b r)):aW 14 D (ao 14 D {r})⊆aW 14 D (ao 14 D {x}):=by
 have m:∀ w,w<b r->r∈ag 14 D w->aF D w<=1:=fun w hw hrw=>by by_contra h;have:=(hb r hr).2.2.2.2 w (by omega) hrw;omega
 have above:∀ w,b r<=w->r∈ag 14 D w->x∈ag 14 D w:=by
  intro w hw hm;apply ee.2
  have eq:=kc e _ _ r (dd r (cl x)) (b r) w (iH e (hb r hr).2.2.2.1 hw) ((ee.1 hxr).trans (cO e hxr (x:=bB r (cl x)) (by simp[bB,cl])).symm)
  exact eq.trans (cO e hm (dm r _))
 intro j hj;simp only[aW,_mf,mem_range,b7] at hj⊢;obtain ⟨hj,h0,h1,h2⟩:=hj
 have both:∀ s:_d,r∈ag 14 D (aw D (j,s)):=fun s=>by cases s;{exact h1};{exact h2}
 have bound:∀ s:_d,b r<=aw D (j,!s):=by
  intro s;by_contra! ht;let w:=aw D (j,!s)
  have path:=fy e r w (both _) (fun u hu=>m u (by dsimp[w] at hu;omega))
  have hf:aF D w=1:=le_antisymm (m w ht (both _)) (ef (n:=14) (cM hj (!s)))
  have eq:=gR e r hj s path hf (fun _=>false) (cl r) (by intro k hk;simp[cl,hk])
  rw[qN e,ee.1 (both s)] at eq;exact _fnt eq
 have hc:b r<=cj D j:=bound true;have hd:b r<=ck D j:=bound false
 exact ⟨hj,above _ (by have:=(e j hj).1;omega) h0,above _ hc h1,above _ hd h2⟩
lemma ln_dom {D:Dag} (h:ai 14 D) (B:ar D) {i:O} (F:i∈aa 14 D) {e:ℕ×_d} (I:af 14 D i={e}) (q:∀ j,Relation.ReflTransGen (bk 14 D) (14+e.1) (14+j)->j≠e.1->cR D j=false):∀ t,t∈ag 14 D (aw D (am e))->dj i t:=by
 have f:=h.1;obtain⟨e0,r,u,b,-,v,k,w,-⟩:=ci_dom h B F;have x:e=e0:=singleton_injective (I.symm.trans w);subst x;obtain⟨g,s⟩:=e;intro t y;by_contra z
 have d:val D (b4 i t) (14+g)=true:=by rw[dz f _ r s,u,gop_true,Bool.and_eq_true];exact⟨cO f b (by simp[b4]),cO f y (by simp[b4])⟩
 have l:∀ c,Relation.ReflTransGen (bk 14 D) (14+g) c->val D (b4 i t) c=true:=by
  intro c J;induction J with
  | refl=>exact d
  | tail m p ih=>obtain⟨j,s',C,rfl,rfl⟩:=fj.mp p;have A:j≠g:=by{have:=dt f (fun _ _ h=>h) m;have:=dh f C s';omega};rw[dz f _ C s',q j (Relation.ReflTransGen.tail m p) A,gop_false,ih];rfl
 have a:=l _ (iD h (14+g) (by omega));rw[ar_pair B z] at a;exact _fnt a
lemma eM_dom {D:Dag} (d:au 14 D) (h:ar D) {i:O} (hc:dom i⊆aa 14 D) {b:ℕ} (c:bz 14 D i.val b) (k:2<=aF D b):ag 14 D b=∅:=by
 have a:=fk_dom d h i b (ds d c);refine eq_empty_of_forall_notMem (fun x e=>?_);have l:=fG.mp (hc (a e)) b e;omega
lemma gr_dom {D:Dag} (h:ai 14 D) (g:ar D) (a:bL 14 D=0) {i:O} (hc:dom i⊆aa 14 D) {w:ℕ} (k:Relation.ReflTransGen (bk 14 D) i.val w):bz 14 D i.val w:=by
 rcases jK k with c|⟨b,c,d⟩;{exact c};have e:=fJ h.1 a d;rw[eM_dom h.1 g hc c d] at e;exact absurd e not_nonempty_empty
lemma jV_dom {D:Dag} (d:au 14 D) (e:ar D) {i v:O} {j:ℕ} (k:j<D.length) (s:_d) (f:cR D j=true) (g:bz 14 D i.val (aw D (j,!s))) (c:aF D (aw D (j,!s))=1) (l:14+j<=bH 14 D) (m:aP i v):v∈ag 14 D (aw D (j,s)):=by
 have p:bz 14 D i.val (14+j):=Relation.ReflTransGen.tail g ⟨cM k (!s),c⟩
 have b:val D (b4 i v) (bH 14 D)=true:=e.1 _ ⟨i,v,m,by simp[b4],by simp[b4]⟩
 have b0:val D (cl v) (bH 14 D)=false:=by by_contra q;rw[_nf] at q;exact kv v (e.2 _ q)
 have r:val D (cl v) (14+j)≠val D (bB i (cl v)) (14+j):=by intro H;have K:=kc d _ _ i (dd i (cl v)) (14+j) (bH 14 D) (iH d p l) H;have hb4:bB i (cl v)=b4 i v:=by{funext x;by_cases h:x=i <;> simp[bB,cl,b4,h]};rw[hb4,b0,b] at K;exact _fnt K
 have t:val D (bB i (cl v)) (14+j)=true:=by by_contra h0;rw[Bool.not_eq_true] at h0;apply r;rw[h0];by_contra u;rw[_nf] at u;rw[gJ d _ _ (iE i _) _ u] at h0;exact Bool.noConfusion h0
 rw[dz d _ k s,f,gop_true,Bool.and_eq_true] at t;have eq1:=gR d i k s g c _ _ (dd i (cl v));rw[t.1] at eq1;exact ee.2 eq1
lemma oh_dom {D:Dag} (h:ai 14 D) (u:ar D) (x:bL 14 D=0) {i v:O} (B:i∈aa 14 D) (hc:dom i⊆aa 14 D) {e:ℕ×_d} (M:af 14 D i={e}) (y:aP i v) (R:∀ p∈af 14 D v,p.1≠e.1->¬ ag 14 D (aw D (am p))⊆dom i):∀ t,t∈ag 14 D (aw D (am e))->dj i t:=by
 have g:=h.1;refine ln_dom h u B M (fun j c N=>?_);by_contra C;rw[_nf] at C
 rcases Relation.ReflTransGen.cases_tail c with S|⟨w,E,z⟩;{exact N (by omega)}
 · obtain⟨j',s,N',P,d⟩:=fj.1 z;have F:j'=j:=by{omega};subst j';have I:e∈af 14 D i:=by{rw[M];exact _mss e}
   obtain⟨J,K,-⟩:=ak.1 I;have a:Relation.ReflTransGen (bk 14 D) i.val w:=((eG (fun _ _ L=>L.1) (iF g B K)).tail (cM J e.2)).trans E
   have l:=gr_dom h u x hc a
   have T:aF D w=1:=by have Z:=ef z;by_contra U;have W:=eM_dom g u hc l (by omega);have Q:=fJ g x (b:=w) (by omega);rw[W] at Q;exact not_nonempty_empty Q
   have f:ag 14 D w⊆dom i:=fk_dom g u i w (ds g l)
   have m:v∉dom i:=by{have:∀ a b:O,ac a b=true->b∉dom a:=by{decide +kernel};exact this i v ((ae i v).2 y)}
   have hw':aw D (j,!(!s))=w:=by rw[Bool.not_not];exact d
   have A:v∈ag 14 D (aw D (j,!s)):=jV_dom g u N' (!s) C (hw'▸l) (hw'▸T) (by unfold bH;omega) y
   have X:((j,!s):ℕ×_d)∈af 14 D v:=ak.2 ⟨N',A,fun Y=>m (f (d▸cr g N' C s Y))⟩
   exact R _ X N (by rw[show am (j,!s)=(j,!(!s)) from rfl,hw'];exact f)
lemma cT_dom {D:Dag} (h:ai 14 D) (d:ar D) (b:bL 14 D=0) {pos:O->ℕ×_d} (a:bA_dom D pos) {i v:O} (e:i∈aa 14 D) (hc:dom i⊆aa 14 D) (c:aP i v) (f:∀ p∈af 14 D v,p.1≠(pos i).1->¬ ag 14 D (aw D (am p))⊆dom i):∀ t,t∈ag 14 D (aw D (pos i))->dj i t:=by
 have:=oh_dom h d b e hc (a.1 i e).2.2.2.2.2.2 c f;rwa[aB] at this
lemma no_leak_2nbrs {D:Dag} (h:ai 14 D) (hd:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {x r i1 i2 v3:O} (hr:r∈al 14 D) (hxr:x∈dom r) (hne:x≠r) (hZx:aZ D b x=∅) (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (h12:i1≠i2) (hx1:ac i1 x=true) (hx2:ac i2 x=true) (hxv:ac x v3=true) (hv1:v3≠i1) (hv2:v3≠i2) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (hnr1:bK i1 r=false) (hxnot:x∉ag 14 D (b r)->False):False:=by
 have hle3:(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=3:=by have:=bj_any h hd hb x;rw[hZx,_ce] at this;omega
 have hge3:3<=(af 14 D x).card:=cx_dom h hd hp hi1 hi2 ⟨h12,hx1,hx2,hxv,hv1,hv2⟩ hdomv
 have hMx:aW 14 D (ao 14 D {x})=∅:=card_eq_zero.1 (by omega)
 have hxin:x∈ag 14 D (b r):=by by_contra h0;exact hxnot h0
 have hMr:aW 14 D (ao 14 D {r})=∅:=Finset.subset_empty.1 (hMx▸aW_ao_r_le_aW_ao_x h.1 hb hr hxin)
 obtain⟨P,Q,hPQ,hPr,hQr,hPrP,hQrQ⟩:=dV_tree h hd hMr (hb r hr).2.1 (hb r hr).1
 have hxP:x∈ag 14 D (aw D P):=bk_x_ag h.1 hMr hPrP hxin
 have hxQ:x∈ag 14 D (aw D Q):=bk_x_ag h.1 hMr hQrQ hxin
 have hPx:P∈af 14 D x:=gD h.1 hMx (ak.1 hPr).1 (cY h.1 hPr) hxP
 have hQx:Q∈af 14 D x:=gD h.1 hMx (ak.1 hQr).1 (cY h.1 hQr) hxQ
 have hp1:pos i1∈af 14 D x:=aJ hp hi1 ((ae _ _).1 hx1)
 have hp2:pos i2∈af 14 D x:=aJ hp hi2 ((ae _ _).1 hx2)
 have hp12:pos i1≠pos i2:=fun e=>h12 (hp.2 hi1 hi2 e)
 have hPneQ:P≠Q:=fun e=>hPQ (e▸rfl)
 have hi1ne:i1≠0/\i1≠7:=by have hdec:∀ x r i1:O,x∈dom r->x≠r->ac i1 x=true->bK i1 r=false->i1≠0/\i1≠7:=by{decide +kernel};exact hdec x r i1 hxr hne hx1 hnr1
 have hdom1:dom i1={i1}:=dom_eq_self hi1ne.1 hi1ne.2
 have hc1:dom i1⊆aa 14 D:=by rw[hdom1];exact singleton_subset_iff.2 hi1
 by_cases h1in:pos i1=P\/pos i1=Q
 · have hr_in:r∈ag 14 D (aw D (pos i1)):=by rcases h1in with rfl|rfl;{exact(ak.1 hPr).2.1};{exact(ak.1 hQr).2.1}
   have hWx:∀ e∈af 14 D x,e=pos i1\/e=pos i2\/∃ w:O,w∈ag 14 D (aw D (am e))/\w∉dom i1:=by
    intro e he;by_cases h3:v3∈aa 14 D
    · have hp3:pos v3∈af 14 D x:=aJ hp h3 (bm ((ae _ _).1 hxv))
      have h13:pos i1≠pos v3:=fun eq1=>hv1.symm (hp.2 hi1 h3 eq1)
      have h23:pos i2≠pos v3:=fun eq1=>hv2.symm (hp.2 hi2 h3 eq1)
      rcases aT hp1 hp2 hp3 hp12 h13 h23 (by omega) e he with rfl|rfl|rfl;{exact Or.inl rfl};{exact Or.inr (Or.inl rfl)}
      · exact Or.inr (Or.inr ⟨v3,cd hp h3,by rw[hdom1,_ms];exact hv1⟩)
    · rcases hdomv with hv|⟨hv1',hv2'⟩;{exact absurd hv h3}
      obtain⟨ev,hev,hbv,hfv,-⟩:=bf h hd hp ((ae _ _).1 hxv)
      have h1e:pos i1≠ev:=fun eq1=>hv1' (hfv i1 hi1 eq1.symm)
      have h2e:pos i2≠ev:=fun eq1=>hv2' (hfv i2 hi2 eq1.symm)
      rcases aT hp1 hp2 hev hp12 h1e h2e (by omega) e he with rfl|rfl|rfl;{exact Or.inl rfl};{exact Or.inr (Or.inl rfl)};{exact Or.inr (Or.inr ⟨v3,(ak.1 hbv).2.1,hv1'⟩)}
   have hcT:=cT_dom h hd hb0 hp hi1 hc1 ((ae _ _).1 hx1) (fun p hp' hne1 hsub=>by
    rcases hWx p hp' with rfl|rfl|⟨w,hw,hwn⟩;{exact hne1 rfl}
    · have:=hsub (cd hp hi2);rw[hdom1,_ms] at this;exact h12.symm this
    · exact hwn (hsub hw))
   exact b3.1 hnr1 (hcT r hr_in)
 · rw[not_or] at h1in
   have hq:∃ q:O,ac i1 q=true/\mV x r q=true:=by
    have hdec:∀ x r i1:O,x∈dom r->x≠r->ac i1 x=true->bK i1 r=false->∃ q:O,ac i1 q=true/\mV x r q=true:=by{decide +kernel}
    exact hdec x r i1 hxr hne hx1 hnr1
   obtain⟨q,hq1,hmq⟩:=hq
   obtain⟨f,hf,hfr,hfq⟩:=bE_dom h.1 hd hmq
   rcases aT hPx hQx hp1 hPneQ (Ne.symm h1in.1) (Ne.symm h1in.2) (by omega) f hf with rfl|rfl|rfl
   · exact hfr (ak.1 hPr).2.1
   · exact hfr (ak.1 hQr).2.1
   · exact hfq ((hp.1 i1 hi1).2.2.2.1 q ((ae _ _).1 hq1))
def qI(a:Fin 68):ℕ×O×O×O×O×O×O:=
 let v:=([0x0,0x760283,0x421d0,0x3170,0x142d0,0x7054a3,0x0,0x0,0x18cd21,0x48cd21,0x0,0x421d0,0x31070,0x3170,0x142d0,0x421d0,0x643b0,0x457d912,0x65190,0x352c0,0x62080,0x142d0,0x54a0,0x3170,0x241d0,0x58dc21,0x48cd21,0x297d11,0x532c0,0x142d0,0x31070,0x421d0,0x643b0,0x3170,0x65190,0x352c0,0x65190,0x3170,0x16590,0x62080,0x540a0,0x54a0,0x3170,0x65190,0x54a0,0x532c0,0x142d0,0x643b0,0xd9710,0x142d0,0xb9860,0x7a800,0x31070,0x65190,0x31070,0x3170,0x16590,0x65190,0x62080,0x6280,0x3170,0x643b0,0xd9710,0x31070,0x65190,0x3170,0x62080,0x31070]:_F ℕ).getD a.val 0
 let f (i:ℕ):O:=Fin.ofNat 14 ((v>>>(4*i))%16)
 (v%16,f 1,f 2,f 3,f 4,f 5,f 6)
lemma qv:∀ g:Fin 68,g.val≠0->g.val≠6->g.val≠7->g.val≠10->
 let q:=qI g;let k:=q.1;let a:=q.2.1;let b:=q.2.2.1;let c:=q.2.2.2.1;let d:=q.2.2.2.2.1;let e:=q.2.2.2.2.2.1;let f:=q.2.2.2.2.2.2;let I:=bU g
 (if k=0 then decide (isClean I a/\b∈I/\c∈I/\b≠c/\ac b a=true/\ac c a=true/\ac a d=true/\d≠b/\d≠c/\(d∈I\/(d∉dom b/\d∉dom c))) else
 if k=1 then decide (isClean I a/\isClean I b/\d∈I/\e∈I/\a∉dom e/\b∉dom d/\c∉dom d/\ac d a=true/\ac e b=true/\ac a b=true/\ac a c=true/\cmOk e b c=true) else
 if k=2 then decide (isClean I a/\isClean I b/\isClean I c/\e∈I/\f∈I/\a∉dom e/\a∉dom f/\ac a b=true/\ac a c=true/\ac a d=true/\ac e b=true/\ac f c=true/\cmOk e b c=true/\cmOk e b d=true/\cmOk f c d=true) else
 decide (I.card=2/\e∉I/\a∈dom e/\a≠e/\b∈I/\c∈I/\b≠c/\ac b a=true/\ac c a=true/\ac a d=true/\d≠b/\d≠c/\(d∈I\/(d∉dom b/\d∉dom c))/\bK b e=false/\leakRoot a=e))=true:=by decide +kernel
lemma tightClean {D:Dag} (h:ai 14 D) (n:ar D) {b:O->ℕ} (hb:cU_dom D b) (z:aj 14 D b=∅) (x:O) (hx:isClean (aa 14 D) x):(af 14 D x).card<=2:=by
 have k:=bj_clean h n hb hx;unfold aZ at k;rw[z,filter_empty,_ce] at k;omega
lemma tightLeak {D:Dag} (h:ai 14 D) (n:ar D) {b:O->ℕ} (hb:cU_dom D b) (z:aj 14 D b=∅) (x:O) (hx:3<=(af 14 D x).card):
 (af 14 D x).card<=3/\aW 14 D (ao 14 D {x})=∅/\leakRoot x∈al 14 D/\x∈ag 14 D (b (leakRoot x))/\aW 14 D (ao 14 D {leakRoot x})=∅:=by
 have hz:aZ D b x=∅:=by unfold aZ;rw[z,filter_empty]
 have k:=bj_any h n hb x;rw[hz,_ce] at k;have m:aW 14 D (ao 14 D {x})=∅:=card_eq_zero.1 (by omega)
 have off:¬(leakRoot x∈al 14 D->leakRoot x≠x->x∉ag 14 D (b (leakRoot x))):=fun p=>by have t:=bj_noleak h n hb p;rw[hz,_ce] at t;omega
 have l:leakRoot x∈al 14 D:=by by_contra q;exact off (fun a=>False.elim (q a))
 have t:x∈ag 14 D (b (leakRoot x)):=by by_contra q;exact off (fun _ _=>q)
 exact ⟨by omega,m,l,t,Finset.subset_empty.1 (m▸aW_ao_r_le_aW_ao_x h.1 hb l t)⟩
lemma carryAF {D:Dag} (e:au 14 D) {x r:O} {w:ℕ} {p:ℕ×_d} (hm:aW 14 D (ao 14 D {x})=∅) (hl:aW 14 D (ao 14 D {r})=∅) (hp:p∈af 14 D r) (g:Relation.ReflTransGen (bk_x D r) w (aw D p)) (hw:x∈ag 14 D w):p∈af 14 D x:=gD e hm (ak.1 hp).1 (cY e hp) (bk_x_ag e hl g hw)
lemma dn_0 {D:Dag} (h:ai 14 D) (n:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (hE:aj 14 D b=∅) (hI:aa 14 D={0,1}):False:=by
 have h0:(0:O)∈aa 14 D:=by rw[hI];decide
 have h1:(1:O)∈aa 14 D:=by rw[hI];decide
 have hcl:=tightClean h n hb hE
 have l2:(af 14 D 2).card<=2:=hcl 2 (Or.inl V)
 have l6:(af 14 D 6).card<=2:=hcl 6 (Or.inl V)
 have l7:(af 14 D 7).card<=2:=hcl 7 (Or.inl V)
 have l9:(af 14 D 9).card<=2:=hcl 9 (Or.inl V)
 have l13:(af 14 D 13).card<=2:=hcl 13 (Or.inl V)
 by_cases l8:(af 14 D 8).card<=2
 · exact fR_dom h n hp 2 8 13 12 0 1 h0 h1 V V l2 l8 l13
 · obtain ⟨hle3,hM8,h7al,h8in,hM7⟩:=tightLeak h n hb hE 8 (by omega)
   obtain⟨P,Q,hPQ,hP7,hQ7,hPrP,hQrQ⟩:=dV_tree h n hM7 (hb 7 h7al).2.1 (hb 7 h7al).1
   have hP8:P∈af 14 D 8:=carryAF h.1 hM8 hM7 hP7 hPrP h8in
   have hQ8:Q∈af 14 D 8:=carryAF h.1 hM8 hM7 hQ7 hQrQ h8in
   have hp07:=aJ hp h0 (by decide:aP 0 7);have hp17:=aJ hp h1 (by decide:aP 1 7)
   have hp01:pos 0≠pos 1:=fun eq1=>absurd (hp.2 h0 h1 eq1) V
   have hPneQ:P≠Q:=fun eq1=>hPQ (eq1▸rfl)
   have h08:pos 0∈af 14 D 8:=by rcases gG hp07 hp17 hp01 l7 P hP7 with rfl|rfl;{exact hP8};{rcases gG hp07 hp17 hp01 l7 Q hQ7 with rfl|rfl;{exact hQ8};{exact absurd rfl hPneQ}}
   have h18:pos 1∈af 14 D 8:=by rcases gG hp07 hp17 hp01 l7 P hP7 with rfl|rfl;{rcases gG hp07 hp17 hp01 l7 Q hQ7 with rfl|rfl;{exact absurd rfl hPneQ};{exact hQ8}};{exact hP8}
   obtain⟨e82,h82,h28,hf2,-⟩:=bf h n hp (by decide:aP 8 2);obtain⟨e86,h86,h68,hf6,-⟩:=bf h n hp (by decide:aP 8 6)
   have he20:pos 0≠e82:=fun eq1=>absurd (hf2 0 h0 eq1.symm) V;have he21:pos 1≠e82:=fun eq1=>absurd (hf2 1 h1 eq1.symm) V
   have he60:pos 0≠e86:=fun eq1=>absurd (hf6 0 h0 eq1.symm) V;have he61:pos 1≠e86:=fun eq1=>absurd (hf6 1 h1 eq1.symm) V
   have heq:e86=e82:=by rcases aT h08 h18 h82 hp01 he20 he21 (by omega) e86 h86 with rfl|rfl|rfl;{exact absurd rfl he60};{exact absurd rfl he61};{rfl}
   obtain⟨Z9,-,hW9,hcm9⟩:=qu_dom h n hp h1 (by decide:aP 1 9) V l9
   obtain⟨e95,h95,h59,hf5,-⟩:=bf h n hp (by decide:aP 9 5);obtain⟨e96,h96,h69,hf69,-⟩:=bf h n hp (by decide:aP 9 6)
   have h95':=h95;have h96':=h96;rw[hW9,_mi,_ms] at h95' h96'
   have h95Z:e95=Z9:=h95'.resolve_left (fun eq1=>absurd (hf5 1 h1 eq1) V)
   have h96Z:e96=Z9:=h96'.resolve_left (fun eq1=>absurd (hf69 1 h1 eq1) V)
   have hne6:am e82≠am Z9:=fun eq1=>by have hEZ:e82=Z9:=by{rw[<- aB e82,<-aB Z9,eq1]};exact (hcm9 8 V).2 (hEZ▸h82)
   obtain⟨f,hf,hf2',hf5'⟩:=bE_dom h.1 n (by decide:mV 6 2 5=true)
   rcases gG (heq▸h68) (h96Z▸h69) hne6 l6 f hf with rfl|rfl;{exact hf2' (ak.1 h28).2.1};{exact hf5' (ak.1 (h95Z▸h59)).2.1}
lemma dn_6_07 {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (a:bA_dom D pos) (hE:aj 14 D b=∅) (E:aa 14 D={0,7}):False:=by
 have F:(0:O)∈aa 14 D:=by rw[E];decide
 have K:(7:O)∈aa 14 D:=by rw[E];decide
 have p:∀ x:O,(af 14 D x).card<=2:=fun x=>by
  have hcl:isClean (aa 14 D) x:=by rw[E];revert x;decide +kernel
  have:=bj_clean h r hb hcl;unfold aZ at this;rw[hE,filter_empty,_ce] at this;omega
 obtain⟨Z8,-,P,Q⟩:=qu_dom h r a F (by decide:aP 0 8) V (p 8)
 obtain⟨Z1,-,R,G⟩:=qu_dom h r a K (by decide:aP 7 1) V (p 1)
 obtain⟨e68,u,d,-,hf68'⟩:=bf h r a (by decide:aP 6 8);obtain⟨e28,w,e,-,hf28'⟩:=bf h r a (by decide:aP 2 8)
 obtain⟨e69,g,i,-,-⟩:=bf h r a (by decide:aP 6 9);obtain⟨e91,z,j,-,hf91'⟩:=bf h r a (by decide:aP 9 1)
 obtain⟨e95,B,k,-,-⟩:=bf h r a (by decide:aP 9 5)
 rw[P,_mi,_ms] at d e
 have s:am e68=Z8:=d.resolve_left (fun q=>absurd (hf68' 0 F q) V)
 have H:am e28=Z8:=e.resolve_left (fun q=>absurd (hf28' 0 F q) V)
 have l:e28=e68:=by rw[<- aB e28,<-aB e68,H,s]
 rw[R,_mi,_ms] at j;have t:am e91=Z1:=j.resolve_left (fun q=>absurd (hf91' 7 K q) V)
 have b1:e68≠e69:=fun q=>(Q 9 V).2 (by rw[<- s,q];exact i)
 have c1:e91≠am e69:=fun q=>(G 6 V).2 (by rw[<- t,q,aB];exact g)
 have m:e95=am e69:=by rcases gG z i c1 (p 9) e95 B with C|C;{exact absurd (by rw[<- t,<-C];exact k) (G 5 V).2};{exact C}
 have n1:e69∈af 14 D 5:=by rw[<- aB e69,<-m];exact k
 obtain⟨f,T,I,J⟩:=bE_dom h.1 r (by decide:mV 6 2 5=true)
 rcases gG u g b1 (p 6) f T with rfl|rfl;{exact I (ak.1 (l▸w)).2.1};{exact J (ak.1 n1).2.1}
lemma dn_7 {D:Dag} (h:ai 14 D) (n:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (hE:aj 14 D b=∅) (hI:aa 14 D={2,7}):False:=by
 have h2:(2:O)∈aa 14 D:=by rw[hI];decide
 have h7:(7:O)∈aa 14 D:=by rw[hI];decide
 have hcl:=tightClean h n hb hE
 have l0:(af 14 D 0).card<=2:=hcl 0 (Or.inl V)
 have l12:(af 14 D 12).card<=2:=hcl 12 (Or.inl V)
 have l13:(af 14 D 13).card<=2:=hcl 13 (Or.inl V)
 have h1_3:3<=(af 14 D 1).card:=by by_contra hc;exact dl_dom h n hp 1 13 9 7 2 h7 h2 V V (by omega) l13
 have h3_3:3<=(af 14 D 3).card:=by by_contra hc;exact dl_dom h n hp 3 12 11 7 2 h7 h2 V V (by omega) l12
 have ⟨hle1,hM1,h0al,h1in,hM0⟩:=tightLeak h n hb hE 1 h1_3
 have ⟨hle3,hM3,_,h3in,_⟩:=tightLeak h n hb hE 3 h3_3
 obtain⟨P,Q,hPQ,hP0,hQ0,hPrP,hQrQ⟩:=dV_tree h n hM0 (hb 0 h0al).2.1 (hb 0 h0al).1
 have hPneQ:P≠Q:=fun eq1=>hPQ (eq1▸rfl)
 have hP1:P∈af 14 D 1:=carryAF h.1 hM1 hM0 hP0 hPrP h1in
 have hQ1:Q∈af 14 D 1:=carryAF h.1 hM1 hM0 hQ0 hQrQ h1in
 have hP3:P∈af 14 D 3:=carryAF h.1 hM3 hM0 hP0 hPrP h3in
 have hQ3:Q∈af 14 D 3:=carryAF h.1 hM3 hM0 hQ0 hQrQ h3in
 have hp70:=aJ hp h7 (by decide:aP 7 0)
 have hZ0_ex:∃ Z0,Z0≠pos 7/\Z0∈af 14 D 1/\Z0∈af 14 D 3:=by rcases gG hP0 hQ0 hPneQ l0 (pos 7) hp70 with rfl|rfl;{exact⟨Q,hPneQ.symm,hQ1,hQ3⟩};{exact⟨P,hPneQ,hP1,hP3⟩}
 obtain⟨Z0,hZ0ne,hZ01,hZ03⟩:=hZ0_ex
 have hp71:=aJ hp h7 (by decide:aP 7 1);have hp73:=aJ hp h7 (by decide:aP 7 3)
 obtain⟨Z13,-,hW13,hcm13⟩:=qu_dom h n hp h2 (by decide:aP 2 13) V l13
 obtain⟨Z12,-,hW12,hcm12⟩:=qu_dom h n hp h2 (by decide:aP 2 12) V l12
 obtain⟨e131,h131,h113,hf131,-⟩:=bf h n hp (by decide:aP 13 1);obtain⟨e134,h134,h413,hf134,-⟩:=bf h n hp (by decide:aP 13 4)
 have h131':=h131;have h134':=h134;rw[hW13,_mi,_ms] at h131' h134'
 have h131Z:e131=Z13:=h131'.resolve_left (fun eq1=>absurd (hf131 2 h2 eq1) V)
 have h134Z:e134=Z13:=h134'.resolve_left (fun eq1=>absurd (hf134 2 h2 eq1) V)
 obtain⟨e123,h123,h312,hf123,-⟩:=bf h n hp (by decide:aP 12 3);obtain⟨e125,h125,h512,hf125,-⟩:=bf h n hp (by decide:aP 12 5)
 have h123':=h123;have h125':=h125;rw[hW12,_mi,_ms] at h123' h125'
 have h123Z:e123=Z12:=h123'.resolve_left (fun eq1=>absurd (hf123 2 h2 eq1) V)
 have h125Z:e125=Z12:=h125'.resolve_left (fun eq1=>absurd (hf125 2 h2 eq1) V)
 have h13ne7:pos 7≠am Z13:=fun eq1=>absurd (em_dom hp h7 (by rw[eq1,aB,<-h131Z];exact h131)) V
 have h12ne7:pos 7≠am Z12:=fun eq1=>absurd (em_dom hp h7 (by rw[eq1,aB,<-h123Z];exact h123)) V
 by_cases heq:Z0=am Z13
 · have hZ012:Z0≠am Z12:=by rw[heq];intro eq1;have hZeq:Z13=Z12:=by{rw[<- aB Z13,<-aB Z12,eq1]};exact (hcm12 13 V).2 (hZeq▸h131Z▸h131)
   obtain⟨f,hf,hf1,hf5⟩:=bE_dom h.1 n (by decide:mV 3 1 5=true)
   rcases aT hp73 hZ03 (h123Z▸h312) hZ0ne.symm h12ne7 hZ012 (by omega) f hf with rfl|rfl|rfl
   · exact hf1 (ak.1 hp71).2.1
   · exact hf1 (ak.1 hZ01).2.1
   · exact hf5 (ak.1 (h125Z▸h512)).2.1
 · obtain⟨f,hf,hf3,hf4⟩:=bE_dom h.1 n (by decide:mV 1 3 4=true)
   rcases aT hp71 hZ01 (h131Z▸h113) hZ0ne.symm h13ne7 heq (by omega) f hf with rfl|rfl|rfl
   · exact hf3 (ak.1 hp73).2.1
   · exact hf3 (ak.1 hZ03).2.1
   · exact hf4 (ak.1 (h134Z▸h413)).2.1
lemma dn_10 {D:Dag} (h:ai 14 D) (n:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (hE:aj 14 D b=∅) (hI:aa 14 D={2,9}):False:=by
 have h2:(2:O)∈aa 14 D:=by rw[hI];decide
 have h9:(9:O)∈aa 14 D:=by rw[hI];decide
 have hcl:=tightClean h n hb hE
 have l5:(af 14 D 5).card<=2:=hcl 5 (Or.inl V)
 have l13:(af 14 D 13).card<=2:=hcl 13 (Or.inl V)
 have h1_3:3<=(af 14 D 1).card:=by by_contra hc;exact dl_dom h n hp 1 13 7 9 2 h9 h2 V V (by omega) l13
 have ⟨hle1,hM1,h0al,h1in,hM0⟩:=tightLeak h n hb hE 1 h1_3
 obtain⟨P,Q,hPQ,hP0,hQ0,hPrP,hQrQ⟩:=dV_tree h n hM0 (hb 0 h0al).2.1 (hb 0 h0al).1
 have hPneQ:P≠Q:=fun eq1=>hPQ (eq1▸rfl)
 have hP1:P∈af 14 D 1:=carryAF h.1 hM1 hM0 hP0 hPrP h1in
 have hQ1:Q∈af 14 D 1:=carryAF h.1 hM1 hM0 hQ0 hQrQ h1in
 obtain⟨e510,h510,h105,hf510,-⟩:=bf h n hp (by decide:aP 5 10)
 have hp95:=aJ hp h9 (by decide:aP 9 5)
 have h9ne:pos 9≠e510:=fun eq1=>absurd (hf510 9 h9 eq1.symm) V
 have hdom9:dom 9⊆aa 14 D:=by rw[dom_eq_self V V];exact singleton_subset_iff.2 h9
 have hcT9:=cT_dom h n hb0 hp h9 hdom9 (by decide:aP 9 5) (fun p hp' hnep hsub=>by
  rcases gG hp95 h510 h9ne l5 p hp' with rfl|rfl;{exact hnep rfl}
  · exact absurd (hsub (ak.1 h105).2.1) V)
 have hp91:=aJ hp h9 (by decide:aP 9 1)
 have hP9:P≠pos 9:=fun eq1=>absurd (hcT9 0 (eq1▸(ak.1 hP0).2.1)) (b3.1 V)
 have hQ9:Q≠pos 9:=fun eq1=>absurd (hcT9 0 (eq1▸(ak.1 hQ0).2.1)) (b3.1 V)
 obtain⟨f,hf,hf0,hf5⟩:=bE_dom h.1 n (by decide:mV 1 0 5=true)
 rcases aT hP1 hQ1 hp91 hPneQ hP9 hQ9 (by omega) f hf with rfl|rfl|rfl
 · exact hf0 (ak.1 hP0).2.1
 · exact hf0 (ak.1 hQ0).2.1
 · exact hf5 (ak.1 hp95).2.1
lemma dn {D:Dag} (h:ai 14 D) (n:ar D) (h12:ap 14 D<=12) (I:bd 14 D<=(al 14 D).card) (j:Fin 68) (l:aa 14 D=bU j):False:=by
 classical
 obtain⟨b,v⟩:=b_dom h.1 n;obtain⟨pos,i⟩:=bQ_dom h n
 have p:aj 14 D b=∅:=by have u:=bS_dom h.1 v;have J:=dX_dom h.1 v;exact card_eq_zero.1 (by omega)
 have g:=tightClean h n v p
 by_cases F0:j.val=0
 · have q:aa 14 D={0,1}:=by rw[l,show j=⟨0,V⟩ from _fe F0];decide
   exact dn_0 h n v i p q
 by_cases F6:j.val=6
 · have q:aa 14 D={0,7}:=by rw[l,show j=⟨6,V⟩ from _fe F6];decide
   exact dn_6_07 h n v i p q
 by_cases F7:j.val=7
 · have q:aa 14 D={2,7}:=by rw[l,show j=⟨7,V⟩ from _fe F7];decide
   exact dn_7 h n v i p q
 by_cases F10:j.val=10
 · have q:aa 14 D={2,9}:=by rw[l,show j=⟨10,V⟩ from _fe F10];decide
   have hb0:bL 14 D=0:=by have:=aV 14 D;have:=bg 14 D;have:=dX_dom h.1 v;rw[q,show({2,9}:o).card=2 from V] at *;omega
   exact dn_10 h n hb0 v i p q
 have m:=qv j F0 F6 F7 F10
 rcases w:qI j with ⟨k,a,b',c,d,e,f⟩;rw[w,<-l] at m;dsimp only at m
 split_ifs at m with r t t2 <;> simp only[decide_eq_true_eq] at m
 · obtain ⟨hcl,y,z,t1,t2,t3,t4,t5,t6,hd⟩:=m;have:=cx_dom h n i y z ⟨t1,t2,t3,t4,t5,t6⟩ hd;have:=g a hcl;omega
 · obtain ⟨ca,cb,G,A,hd1,hd2,hd3,g1,g2,g3,g4,cm⟩:=m
   exact dl_dom h n i a b' c d e G A ⟨hd1,hd2,hd3⟩ ⟨g1,g2,g3,g4,cm⟩ (g a ca) (g b' cb)
 · obtain ⟨ca,cb,cc,A,H,hd1,hd2,g1,g2,g3,g4,g5,cm1,cm2,cm3⟩:=m
   exact fR_dom h n i a b' c d e f A H ⟨hd1,hd2⟩ ⟨g1,g2,g3,g4,g5,cm1,cm2,cm3⟩ (g a ca) (g b' cb) (g c cc)
 · obtain ⟨hc,he,hae,hne,B,C,hbc,g1,g2,g3,hd1,hd2,hdom,hbk,hlr⟩:=m
   have h0:bL 14 D=0:=by have:=aV 14 D;have:=bg 14 D;have:=dX_dom h.1 v;omega
   have hal:e∈al 14 D:=by by_contra z;exact he (aN.2 z)
   have hz:aZ D b a=∅:=by unfold aZ;rw[p,filter_empty]
   have h3:=cx_dom h n i B C ⟨hbc,g1,g2,g3,hd1,hd2⟩ hdom
   exact no_leak_2nbrs h n h0 v i hal hae hne hz B C hbc g1 g2 g3 hd1 hd2 hdom hbk (fun hno=>by
    have q:=bj_noleak h n v (x:=a) (fun _ _=>hlr.symm▸hno);rw[hz,_ce] at q;omega)
abbrev Za:=ℕ×_d
abbrev Zg(D:Dag)(z:Za):=ag 14 D (aw D z)
abbrev Zi(D:Dag):=aa 14 D
lemma Zforce {D:Dag}(h:au 14 D)(r:ar D){x y:O}{A B E:Za}(a:A∈af 14 D x)(b:B∈af 14 D x)(ab:A≠B)(ay:A∈af 14 D y)(by':B∈af 14 D y)(c:(af 14 D x).card<=3)(q:O)(hx:E∈af 14 D x)(hq:E∈af 14 D q)(m:mV x y q=true:=by decide):E=A∨E=B:=by
 by_contra n
 rw[not_or] at n
 obtain⟨f,hf,ny,nq⟩:=bE_dom h r m
 rcases aT a b hx ab (Ne.symm n.1) (Ne.symm n.2) c f hf with rfl|rfl|rfl
 · exact ny (ak.1 ay).2.1
 · exact ny (ak.1 by').2.1
 · exact nq (ak.1 hq).2.1
lemma Zx {D:Dag}(h:au 14 D)(r:ar D){p:O->Za}(t:bA_dom D p){x y i:O}(q:O){A B:Za}(iI:i∈Zi D)(hx:p i∈af 14 D x)(a:A∈af 14 D x)(b:B∈af 14 D x)(ab:A≠B)(ay:A∈af 14 D y)(by':B∈af 14 D y)(c:(af 14 D x).card<=3)(iq:aP i q)(m:mV x y q=true):p i=A\/p i=B:=Zforce h r a b ab ay by' c q hx (aJ t iI iq) m
lemma Zthree {D:Dag}{p:O->Za}(t:bA_dom D p){i x y:O}{a b P Q:Za}(hi:i∈Zi D)(wa:a∈af 14 D x)(wb:b∈af 14 D y)(nab:a∉af 14 D y)(h1:am a=P∨am a=Q)(h2:am b=P∨am b=Q)(h3:p i=P∨p i=Q)(dx:x∉dom i:=by decide)(dy:y∉dom i:=by decide):False:=by
 have F:p i≠am a:=fun e=>dx (em_dom t hi (by rw[e,aB];exact wa))
 have G:p i≠am b:=fun e=>dy (em_dom t hi (by rw[e,aB];exact wb))
 have H:am a≠am b:=fun e=>nab (by rwa[←aB a,e,aB])
 grind only
lemma Zp {D:Dag}{p:O->Za}(t:bA_dom D p){i j:O}(a:i∈Zi D)(b:j∈Zi D)(c:i≠j):p i≠p j:=fun e=>c (t.2 a b e)
abbrev Zj {D:Dag}{p:O->Za}(t:bA_dom D p){i:O}(a:i∈Zi D)(v:O)(b:aP i v:=by decide):=aJ t a b
abbrev Zb {D:Dag}(h:ai 14 D)(r:ar D){p:O->Za}(t:bA_dom D p)(x y:O)(m:aP x y:=by decide):=bf h r t m
abbrev Zm {D:Dag}(h:au 14 D)(r:ar D)(x a b:O)(m:mV x a b=true:=by decide):=bE_dom h r m
lemma Zu {D:Dag}{I:o}(h:Zi D=I)(i:O)(q:i∈I:=by decide):i∈Zi D:=h▸q
lemma Zd {D:Dag}{I:o}(h:Zi D=I)(i:O)(q:dom i⊆I:=by decide):dom i⊆Zi D:=h▸q
lemma eq_or_am {p q:ℕ×_d} (h:p.1=q.1):p=q\/p=am q:=by rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩;simp only at h;subst h;cases b <;> cases d <;> simp[am]
lemma shared_PQ_u {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {x:O} (hcl:isClean (aa 14 D) x) (h3:3<=(af 14 D x).card):aZ D b x={u0}/\(af 14 D x).card=3/\aW 14 D (ao 14 D {x})=∅/\∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x/\∀ y:O,y∈ag 14 D u0.1->y∈ag 14 D (aw D P)/\y∈ag 14 D (aw D Q):=by
 have g:=bj_clean h r hb hcl;have c:aZ D b x⊆{u0}:=by rw[<- hR1];exact _fs _ _
 have p:(aZ D b x).card<=1:=by have:=_cl c;rw[_cs] at this;exact this
 have hZ:aZ D b x={u0}:=_eqc c (by rw[_cs];omega)
 have a:aW 14 D (ao 14 D {x})=∅:=card_eq_zero.1 (by rw[hZ,_cs] at g;omega)
 have m:u0∈aZ D b x:=by rw[hZ];exact _mss u0
 obtain⟨n,o⟩:=ay.1 m
 have l:2<=aF D u0.1:=by have:=(dW.1 (_mf.1 (_md.1 n).1).1).2;omega
 obtain⟨P,Q,i,j,k,d,f⟩:=dV_tree h r a o l
 refine⟨hZ,by rw[hZ,_cs] at g;omega,a,P,Q,fun e=>i (e▸rfl),j,k,fun y hy=>⟨bk_x_ag h.1 a d hy,bk_x_ag h.1 a f hy⟩⟩
lemma PQ_in_af {D:Dag} (e:au 14 D) {x y:O} {P:ℕ×_d} (hMy:aW 14 D (ao 14 D {y})=∅) (hPx:P∈af 14 D x) (hyP:y∈ag 14 D (aw D P)):P∈af 14 D y:=
 gD e hMy (ak.1 hPx).1 (cY e hPx) hyP
lemma clean_u0_of_ge3 {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {x:O} (hcl:isClean (aa 14 D) x) (h3:3<=(af 14 D x).card):x∈ag 14 D u0.1:=by
 obtain⟨hZ,-⟩:=shared_PQ_u h r hb hR1 hcl h3;exact(ay.1 (by rw[hZ];exact _mss u0)).2
lemma clean_le2_of_not_u0 {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {x:O} (hcl:isClean (aa 14 D) x) (hno:x∉ag 14 D u0.1):(af 14 D x).card<=2:=by
 by_contra hc;exact hno (clean_u0_of_ge3 h r hb hR1 hcl (by omega))
lemma clean_shared_af {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {x y:O} (hcx:isClean (aa 14 D) x) (hcy:isClean (aa 14 D) y) (hx3:3<=(af 14 D x).card) (hy3:3<=(af 14 D y).card):∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x/\P∈af 14 D y/\Q∈af 14 D y/\∀ z:O,z∈ag 14 D u0.1->z∈ag 14 D (aw D P)/\z∈ag 14 D (aw D Q):=by
 obtain⟨-,-,-,P,Q,f,d,e,a⟩:=shared_PQ_u h r hb hR1 hcx hx3
 obtain⟨g,-,c,-⟩:=shared_PQ_u h r hb hR1 hcy hy3
 have k:y∈ag 14 D u0.1:=(ay.1 (by rw[g];exact _mss u0)).2
 obtain⟨i,j⟩:=a y k
 exact⟨P,Q,f,d,e,PQ_in_af h.1 c d i,PQ_in_af h.1 c e j,a⟩
lemma clean_inter_le1 {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {x y:O} (hcx:isClean (aa 14 D) x) (hcy:isClean (aa 14 D) y) (hx3:3<=(af 14 D x).card) (hy3:3<=(af 14 D y).card) {e1 e2 e3:ℕ×_d} (he1:e1∈af 14 D x) (he2:e2∈af 14 D x) (he3:e3∈af 14 D x) (h12:e1≠e2) (h13:e1≠e3) (h23:e2≠e3) (hn1:e1∉af 14 D y) (hn2:e2∉af 14 D y):False:=by
 obtain⟨-,j,-⟩:=shared_PQ_u h r hb hR1 hcx hx3
 obtain⟨P,Q,e,f,i,a,c,-⟩:=clean_shared_af h r hb hR1 hcx hcy hx3 hy3
 have d:P=e3:=by rcases aT he1 he2 he3 h12 h13 h23 (by omega) P f with rfl|rfl|rfl;{exact absurd a hn1};{exact absurd a hn2};{rfl}
 have g:Q=e3:=by rcases aT he1 he2 he3 h12 h13 h23 (by omega) Q i with rfl|rfl|rfl;{exact absurd c hn1};{exact absurd c hn2};{rfl}
 exact e (d.trans g.symm)
lemma lQ_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {pos:O->ℕ×_d} (hp:bA_dom D pos) {i x y:O} (hi:i∈aa 14 D) (hdom:dom i⊆aa 14 D) (hix:aP i x) (hxy:aP x y) (hy:y∉dom i) (hle:(af 14 D x).card<=2):∀ t,t∈ag 14 D (aw D (pos i))->dj i t:=by
 have hm:=aJ hp hi hix;obtain⟨e,he,a,b,-⟩:=bf h r hp hxy
 have c:pos i≠e:=fun w=>hy (b i hi w.symm)
 exact cT_dom h r hb0 hp hi hdom hix (fun p hp' hnep hsub=>by rcases gG hm he c hle p hp' with rfl|rfl;{exact hnep rfl};{exact hy (hsub (ak.1 a).2.1)})
lemma cT_07 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {pos:O->ℕ×_d} (hp:bA_dom D pos) (h0:(0:O)∈aa 14 D) (h7:(7:O)∈aa 14 D):(∀ t,t∈ag 14 D (aw D (pos 0))->dj 0 t)/\(∀ t,t∈ag 14 D (aw D (pos 7))->dj 7 t):=by
 have h1:pos 7=am (pos 0):=_ms.1 ((hp.1 0 h0).2.2.2.2.2.2▸Zj hp h7 0)
 have d0:∀ u:O,u∈dom 7->dj 0 u:=by decide +kernel
 have d7:∀ u:O,u∈dom 0->dj 7 u:=by decide +kernel
 exact⟨fun t ht=>d0 t ((hp.1 7 h7).2.2.2.2.2.1 (by rwa[h1,aB])),fun t ht=>d7 t ((hp.1 0 h0).2.2.2.2.2.1 (by rwa[<- h1]))⟩
lemma dy_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {pos:O->ℕ×_d} (hp:bA_dom D pos) {i1 i2 a v3:O} (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (hdom1:dom i1⊆aa 14 D) (hg:i1≠i2/\ac i1 a=true/\ac i2 a=true/\ac a v3=true/\v3≠i1/\v3≠i2) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (h21:i2∉dom i1) (hv1:v3∉dom i1) (hle:(af 14 D a).card<=3):∀ t,t∈ag 14 D (aw D (pos i1))->dj i1 t:=by
 obtain⟨k,ga1,ga2,gav,i,j⟩:=hg;rw[ae] at ga1 ga2 gav
 have f:=aJ hp hi1 ga1;have g:=aJ hp hi2 ga2;have b:pos i1≠pos i2:=fun e=>k (hp.2 hi1 hi2 e)
 refine cT_dom h r hb0 hp hi1 hdom1 ga1 (fun p hpa hnep hsub=>?_)
 by_cases hv:v3∈Zi D
 · have o:=aJ hp hv (bm gav)
   rcases aT f g o b (fun e=>i.symm (hp.2 hi1 hv e)) (fun e=>j.symm (hp.2 hi2 hv e)) hle p hpa with rfl|rfl|rfl
   · exact hnep rfl
   · exact h21 (hsub (hp.1 i2 hi2).2.2.2.2.1)
   · exact hv1 (hsub (hp.1 v3 hv).2.2.2.2.1)
 · rcases hdomv with q|⟨l,m⟩;{exact absurd q hv}
   obtain⟨ev,n,c,d,-⟩:=bf h r hp gav
   rcases aT f g n b (fun e=>l (d i1 hi1 e.symm)) (fun e=>m (d i2 hi2 e.symm)) hle p hpa with rfl|rfl|rfl
   · exact hnep rfl
   · exact h21 (hsub (hp.1 i2 hi2).2.2.2.2.1)
   · exact hv1 (hsub (ak.1 c).2.1)
lemma eF_cand_dom {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {a i1 i2 v3:O} (hca:isClean (aa 14 D) a) (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (hg:i1≠i2/\ac i1 a=true/\ac i2 a=true/\ac a v3=true/\v3≠i1/\v3≠i2) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (hc1:∀ t,t∈ag 14 D (aw D (pos i1))->dj i1 t) (hc2:∀ t,t∈ag 14 D (aw D (pos i2))->dj i2 t):∀ y:O,y∈ag 14 D u0.1->(dj i1 y/\dj i2 y)\/(dj i1 y/\∀ q:O,ac i2 q=true->mV a y q=false)\/(dj i2 y/\∀ q:O,ac i1 q=true->mV a y q=false):=by
 have s:=cx_dom h r hp hi1 hi2 hg hdomv
 obtain⟨-,u,-,P,Q,d,g,i,l⟩:=shared_PQ_u h r hb hR1 hca s
 have m:=aJ hp hi1 ((ae _ _).1 hg.2.1);have n:=aJ hp hi2 ((ae _ _).1 hg.2.2.1)
 have k:pos i1≠pos i2:=fun e=>hg.1 (hp.2 hi1 hi2 e)
 intro y hy;obtain⟨o,p⟩:=l y hy
 by_cases h1:pos i1=P\/pos i1=Q
 · by_cases h2:pos i2=P\/pos i2=Q
   · left;exact⟨hc1 y (by rcases h1 with rfl|rfl <;> assumption),hc2 y (by rcases h2 with rfl|rfl <;> assumption)⟩
   · right;left;refine⟨hc1 y (by rcases h1 with rfl|rfl <;> assumption),fun q hq=>?_⟩
     rw[not_or] at h2;by_contra hm;rw[_nf] at hm
     obtain⟨f,hf,c,j⟩:=bE_dom h.1 r hm
     rcases aT g i n d (Ne.symm h2.1) (Ne.symm h2.2) (by omega) f hf with rfl|rfl|rfl;{exact c o};{exact c p};{exact j ((hp.1 i2 hi2).2.2.2.1 q ((ae _ _).1 hq))}
 · right;right;rw[not_or] at h1
   have h2:pos i2=P\/pos i2=Q:=by rcases aT g i m d (Ne.symm h1.1) (Ne.symm h1.2) (by omega) (pos i2) n with e|e|e;{exact Or.inl e};{exact Or.inr e};{exact absurd e k.symm}
   refine⟨hc2 y (by rcases h2 with rfl|rfl <;> assumption),fun q hq=>?_⟩
   by_contra hm;rw[_nf] at hm
   obtain⟨f,hf,c,j⟩:=bE_dom h.1 r hm
   rcases aT g i m d (Ne.symm h1.1) (Ne.symm h1.2) (by omega) f hf with rfl|rfl|rfl;{exact c o};{exact c p};{exact j ((hp.1 i1 hi1).2.2.2.1 q ((ae _ _).1 hq))}
lemma eF_cand_1side {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) {a i1 i2 v3:O} (hca:isClean (aa 14 D) a) (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (hg:i1≠i2/\ac i1 a=true/\ac i2 a=true/\ac a v3=true/\v3≠i1/\v3≠i2) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (hc2:∀ t,t∈ag 14 D (aw D (pos i2))->dj i2 t):∀ y:O,y∈ag 14 D u0.1->dj i2 y\/(∀ q:O,ac i2 q=true->mV a y q=false):=by
 have j:=cx_dom h r hp hi1 hi2 hg hdomv
 obtain⟨-,o,-,P,Q,e,g,i,c⟩:=shared_PQ_u h r hb hR1 hca j
 have l:=aJ hp hi2 ((ae _ _).1 hg.2.2.1)
 intro y hy;obtain⟨m,n⟩:=c y hy
 by_cases h2:pos i2=P\/pos i2=Q
 · exact Or.inl (hc2 y (by rcases h2 with rfl|rfl <;> assumption))
 · right;rw[not_or] at h2;intro q hq;by_contra hm;rw[_nf] at hm
   obtain⟨f,hf,d,k⟩:=bE_dom h.1 r hm
   rcases aT g i l e (Ne.symm h2.1) (Ne.symm h2.2) (by omega) f hf with rfl|rfl|rfl;{exact d m};{exact d n};{exact k ((hp.1 i2 hi2).2.2.2.1 q ((ae _ _).1 hq))}
lemma bz_cap_hp {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {pos:O->ℕ×_d} (hp:bA_dom D pos) {i v:O} {X:ℕ×_d} (hi:i∈aa 14 D) (hdom:dom i⊆aa 14 D) (hiv:aP i v) (hXv:X∈af 14 D v) (hXne:X.1≠(pos i).1) (hother:∀ p∈af 14 D v,p.1≠(pos i).1->p≠X->¬ ag 14 D (aw D (am p))⊆dom i):(∀ t,t∈ag 14 D (aw D (pos i))->dj i t)\/(bz 14 D i.val (aw D (am X))/\(∀ y,aP i y->y∈ag 14 D (aw D X))/\(∀ t,t∈ag 14 D (aw D (pos i))->t∈ag 14 D (aw D X)->dj i t)):=by
 have f:∀ a b:O,b∈dom a->¬ aP a b:=by decide +kernel
 by_cases S:ag 14 D (aw D (am X))⊆dom i
 · have A:∀ j,Relation.ReflTransGen (bk 14 D) (14+(pos i).1) (14+j)->j≠(pos i).1->j≠X.1->cR D j=false:=by
    intro j hj g N;by_contra hc;rw[_nf] at hc
    rcases Relation.ReflTransGen.cases_tail hj with W|⟨w,o,n⟩;{exact g (by omega)}
    obtain⟨j',s,m,H,rfl⟩:=fj.1 n;have l:j'=j:=by omega
    subst j';have he:(am (pos i))∈af 14 D i:=by rw[(hp.1 i hi).2.2.2.2.2.2];exact _mss _
    obtain⟨J,K,-⟩:=ak.1 he
    have ha:Relation.ReflTransGen (bk 14 D) i.val (aw D (j,s)):=((eG (fun _ _ L=>L.1) (iF h.1 hi K)).tail (cM J (am (pos i)).2)).trans o
    have hl:=gr_dom h r hb0 hdom ha
    have hT:aF D (aw D (j,s))=1:=by have hZ:=ef n;by_contra hU;have hW:=eM_dom h.1 r hdom hl (by omega);have hQ:=fJ h.1 hb0 (b:=aw D (j,s)) (by omega);rw[hW] at hQ;exact not_nonempty_empty hQ
    have hf:ag 14 D (aw D (j,s))⊆dom i:=fk_dom h.1 r i _ (ds h.1 hl)
    have a0:v∉dom i:=fun hvi'=>f i v hvi' hiv
    have U:v∈ag 14 D (aw D (j,!s)):=jV_dom h.1 r m (!s) hc (by rw[Bool.not_not];exact hl) (by rw[Bool.not_not];exact hT) (by unfold bH;omega) hiv
    have a1:v∉ag 14 D (14+j):=fun hvn=>a0 (hf (cr h.1 m hc s hvn))
    have Q:(j,!s)∈af 14 D v:=ak.2 ⟨m,U,a1⟩
    have B:(j,!s)≠X:=fun eq1=>N (congrArg Prod.fst eq1)
    exact hother (j,!s) Q g B (by show ag 14 D (aw D (j,!(!s)))⊆dom i;rw[Bool.not_not];exact hf)
   by_cases d:Relation.ReflTransGen (bk 14 D) (14+(pos i).1) (14+X.1)
   · right
     rcases Relation.ReflTransGen.cases_tail d with W|⟨w,o,n⟩;{exact absurd (by omega:X.1=(pos i).1) hXne}
     obtain⟨j',s,m,H,rfl⟩:=fj.1 n;have l:j'=X.1:=by omega
     have F:cR D X.1=true:=cY h.1 hXv
     have he:(am (pos i))∈af 14 D i:=by rw[(hp.1 i hi).2.2.2.2.2.2];exact _mss _
     obtain⟨J,K,-⟩:=ak.1 he
     have ha:Relation.ReflTransGen (bk 14 D) i.val (aw D (j',s)):=((eG (fun _ _ L=>L.1) (iF h.1 hi K)).tail (cM J (am (pos i)).2)).trans o
     have hl:=gr_dom h r hb0 hdom ha
     have hT:aF D (aw D (j',s))=1:=by have hZ:=ef n;by_contra hU;have hW:=eM_dom h.1 r hdom hl (by omega);have hQ:=fJ h.1 hb0 (b:=aw D (j',s)) (by omega);rw[hW] at hQ;exact not_nonempty_empty hQ
     have hf:ag 14 D (aw D (j',s))⊆dom i:=fk_dom h.1 r i _ (ds h.1 hl)
     have C:s=!X.2:=by
      by_contra hns;have R:s=X.2:=by rcases X with ⟨x1,x2⟩;cases s <;> cases x2 <;> simp_all
      have T:v∈ag 14 D (aw D (j',s)):=by rw[show(j',s)=X from Prod.ext l R];exact(ak.1 hXv).2.1
      exact f i v (hf T) hiv
     have e:aw D (j',s)=aw D (am X):=by rw[show(j',s)=am X from Prod.ext l C]
     have u:bz 14 D i.val (aw D (am X)):=e▸hl
     have G:aF D (aw D (am X))=1:=e▸hT
     refine⟨u,fun y hiy=>?_,fun t ht1 ht2=>?_⟩
     · exact jV_dom h.1 r (ak.1 hXv).1 X.2 F u G (by unfold bH;have:=(ak.1 hXv).1;omega) hiy
     · by_contra M
       have h1:val D (b4 i t) (14+(pos i).1)=true:=by rw[dz h.1 _ (hp.1 i hi).1 (pos i).2,(hp.1 i hi).2.1,gop_true,Bool.and_eq_true];exact⟨cO h.1 ht1 (by simp[b4]),cO h.1 (hp.1 i hi).2.2.2.2.1 (by simp[b4])⟩
       have h2:val D (b4 i t) (aw D (am X))=true:=by
        have E:∀ c,Relation.ReflTransGen (bk 14 D) (14+(pos i).1) c->c<14+X.1->val D (b4 i t) c=true:=by
         intro c hc Y;induction hc with
         | refl=>exact h1
         | @tail a b hab hbc ih=>
          obtain⟨k,sk,hk,rfl,rfl⟩:=fj.1 hbc
          have x:k≠(pos i).1:=by have:=dt h.1 (fun _ _ q=>q) hab;have:=dh h.1 hk sk;omega
          have z:k≠X.1:=by omega
          have I:aw D (k,sk)<14+X.1:=lt_trans (dh h.1 hk sk) Y
          rw[dz h.1 _ hk sk,A k (hab.tail hbc) x z,gop_false,ih I];rfl
        rw[<- e];exact E _ o (by have:=dh h.1 m s;omega)
       have h3:val D (b4 i t) (14+X.1)=true:=by rw[dz h.1 _ (ak.1 hXv).1 X.2,F,gop_true,Bool.and_eq_true];exact⟨cO h.1 ht2 (by simp[b4]),h2⟩
       have h4:∀ c,Relation.ReflTransGen (bk 14 D) (14+X.1) c->val D (b4 i t) c=true:=by
        intro c hc;induction hc with
        | refl=>exact h3
        | @tail a b hab hbc ih=>
         obtain⟨k,sk,hk,rfl,rfl⟩:=fj.1 hbc
         have x:k≠(pos i).1:=by have:=dt h.1 (fun _ _ q=>q) (d.trans hab);have:=dh h.1 hk sk;omega
         have z:k≠X.1:=by have:=dt h.1 (fun _ _ q=>q) hab;have:=dh h.1 hk sk;omega
         rw[dz h.1 _ hk sk,A k ((d.trans hab).tail hbc) x z,gop_false,ih];rfl
       have h5:=h4 _ (iD h (14+X.1) (by have:=(ak.1 hXv).1;omega))
       rw[ar_pair r M] at h5;exact Bool.noConfusion h5
   · left;refine fun t ht=>?_;have:=ln_dom h r hi (hp.1 i hi).2.2.2.2.2.2 (fun j hj g=>A j hj g (fun hjeq=>d (hjeq▸hj)));exact this t (by rwa[aB])
 · left;exact cT_dom h r hb0 hp hi hdom hiv (fun p hp' hnep hsub'=>by by_cases P:p=X;{exact S (P▸hsub')};{exact hother p hp' hnep P hsub'})
lemma im_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (x y ix iy vx qx qy:O) (hcx:isClean (aa 14 D) x) (hcy:isClean (aa 14 D) y) (hix:ix∈aa 14 D) (hiy:iy∈aa 14 D) (hdx:dom ix⊆aa 14 D) (hniy:iy∉dom ix) (hvx:vx∉dom ix/\vx∉dom iy) (hg:x≠y/\ix≠iy/\ac ix x=true/\ac iy y=true/\bK ix y=false/\ac x vx=true/\ac ix qx=true/\mV x y qx=true/\ac iy qy=true/\mV y x qy=true) (hx3:3<=(af 14 D x).card) (hy3:3<=(af 14 D y).card):False:=by
 obtain⟨F,s,g1,g2,g3,g4,g5,z,g7,A⟩:=hg
 obtain⟨-,C,-⟩:=shared_PQ_u h r hb hR1 hcx hx3
 obtain⟨-,E,-⟩:=shared_PQ_u h r hb hR1 hcy hy3
 obtain⟨P,Q,n,g,j,i,k,-⟩:=clean_shared_af h r hb hR1 hcx hcy hx3 hy3
 have v:=aJ hp hix ((ae _ _).1 g1);have B:=aJ hp hiy ((ae _ _).1 g2)
 by_cases d:pos ix∈af 14 D y
 · by_cases f:pos iy∈af 14 D x
   · obtain⟨ev,w,o,q,-⟩:=bf h r hp ((ae _ _).1 g4)
     have hu:pos ix≠pos iy:=fun e=>s (hp.2 hix hiy e)
     have hI:pos ix≠ev:=fun e=>hvx.1 (q ix hix e.symm)
     have hJ:pos iy≠ev:=fun e=>hvx.2 (q iy hiy e.symm)
     have hZ:=aT v f w hu hI hJ (by omega)
     have hv:=cT_dom h r hb0 hp hix hdx ((ae _ _).1 g1) (fun p hpa hnep hsub=>by
      rcases hZ p hpa with rfl|rfl|rfl;{exact hnep rfl}
      · have l:iy∈dom ix:=hsub (hp.1 iy hiy).2.2.2.2.1
        exact hniy l
      · exact hvx.1 (hsub (ak.1 o).2.1))
     exact b3.1 g3 (hv y (ak.1 d).2.1)
   · have a:P≠pos iy:=fun e=>f (e▸g);have c:Q≠pos iy:=fun e=>f (e▸j)
     obtain⟨e,he,t,m⟩:=bE_dom h.1 r A
     rcases aT i k B n a c (by omega) e he with rfl|rfl|rfl;{exact t (ak.1 g).2.1};{exact t (ak.1 j).2.1};{exact m ((hp.1 iy hiy).2.2.2.1 qy ((ae _ _).1 g7))}
 · have a:P≠pos ix:=fun e=>d (e▸i);have c:Q≠pos ix:=fun e=>d (e▸k)
   obtain⟨e,he,u,m⟩:=bE_dom h.1 r z
   rcases aT g j v n a c (by omega) e he with rfl|rfl|rfl;{exact u (ak.1 i).2.1};{exact u (ak.1 k).2.1};{exact m ((hp.1 ix hix).2.2.2.1 qx ((ae _ _).1 g5))}
lemma gH_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (x y ix iy:O) (hcx:isClean (aa 14 D) x) (hcy:isClean (aa 14 D) y) (hix:ix∈aa 14 D) (hiy:iy∈aa 14 D) (hdx:dom ix⊆aa 14 D) (hniy:iy∉dom ix) (hnxy:y∉dom ix/\x∉dom iy) (hg:ix≠iy/\ac ix x=true/\ac iy y=true/\ac x y=true/\bK ix y=false) (hx3:3<=(af 14 D x).card) (hy3:3<=(af 14 D y).card):False:=by
 obtain⟨o,g1,g2,g3,g4⟩:=hg;rw[ae] at g1 g2 g3
 obtain⟨-,C,-⟩:=shared_PQ_u h r hb hR1 hcx hx3
 obtain⟨-,E,-⟩:=shared_PQ_u h r hb hR1 hcy hy3
 obtain⟨P,Q,l,f,i,g,j,-⟩:=clean_shared_af h r hb hR1 hcx hcy hx3 hy3
 obtain⟨e,c,d,k,z⟩:=bf h r hp g3
 have v:e≠P:=fun q=>el h.1 (q▸g) d;have w:e≠Q:=fun q=>el h.1 (q▸j) d
 have m:am e≠P:=fun q=>el h.1 f (by rw[<- q,aB];exact c)
 have n:am e≠Q:=fun q=>el h.1 i (by rw[<- q,aB];exact c)
 have s:=aJ hp hix g1;have B:=aJ hp hiy g2
 have hA:pos ix∈af 14 D y:=by rcases aT f i c l v.symm w.symm (by omega) (pos ix) s with q|q|q;{exact q▸g};{exact q▸j};{exact absurd (k ix hix q.symm) hnxy.1}
 have hB:pos iy∈af 14 D x:=by rcases aT g j d l m.symm n.symm (by omega) (pos iy) B with q|q|q;{exact q▸f};{exact q▸i};{exact absurd (z iy hiy q.symm) hnxy.2}
 have hR:pos ix≠pos iy:=fun q=>o (hp.2 hix hiy q)
 have hX:pos ix≠e:=fun q=>hnxy.1 (k ix hix q.symm)
 have t:pos iy≠e:=fun q=>by have A:∀ a b:O,aP a b->b∈dom a->False:=(by decide +kernel);exact A iy y g2 (k iy hiy q.symm)
 have u:=aT s hB c hR hX t (by omega)
 have hS:=cT_dom h r hb0 hp hix hdx g1 (fun p hpa hnep hsub=>by
  rcases u p hpa with rfl|rfl|rfl;{exact hnep rfl};{exact hniy (hsub (hp.1 iy hiy).2.2.2.2.1)};{exact hnxy.1 (hsub (ak.1 d).2.1)})
 exact b3.1 g4 (hS y (ak.1 hA).2.1)
section
variable {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {p:O->Za} (hp:bA_dom D p) {u:Σ _:ℕ,ℕ} (hr:aj 14 D b={u})
include h r hb hr in
lemma leakInfo {x:O} (g:3<=(af 14 D x).card) (n:x∉ag 14 D u.1):(af 14 D x).card<=3/\aW 14 D (ao 14 D {x})=∅/\leakRoot x∈al 14 D/\x∈ag 14 D (b (leakRoot x)):=by
 have E:aZ D b x=∅:=eq_empty_iff_forall_notMem.2 (fun _ m=>n ((_ms.1 (hr▸(ay.1 m).1))▸(ay.1 m).2))
 have A:=bj_any h r hb x;rw[E,_ce] at A
 refine⟨by omega,card_eq_zero.1 (by omega),?_⟩
 by_contra k
 have B:=bj_noleak h r hb (x:=x) (fun t _ q=>k ⟨t,q⟩);rw[E,_ce] at B;omega
include h r hb in
lemma leakPair {v:O} (t:v∈al 14 D) (a:aW 14 D (ao 14 D {v})=∅):∃ P Q:Za,P≠Q/\P∈af 14 D v/\Q∈af 14 D v/\∀ x:O,x∈ag 14 D (b v)->aW 14 D (ao 14 D {x})=∅->P∈af 14 D x/\Q∈af 14 D x:=by
 obtain⟨P,Q,l,c,d,m,n⟩:=dV_tree h r a (hb v t).2.1 (hb v t).1
 exact⟨P,Q,fun e=>l (e▸rfl),c,d,fun _ j s=>⟨PQ_in_af h.1 s c (bk_x_ag h.1 a m j),PQ_in_af h.1 s d (bk_x_ag h.1 a n j)⟩⟩
include h r hb hp hr in
lemma leakIn {x i:O} (q:O) (t:i∈Zi D) (c:∀ y,y∈Zg D (p i)->dj i y) (g:3<=(af 14 D x).card) (f:aP i x:=by decide) (s:aP i q:=by decide) (m:mV x (leakRoot x) q=true:=by decide) (k:¬dj i (leakRoot x):=by decide):x∈ag 14 D u.1:=by
 by_contra n
 obtain⟨z,e,l,a⟩:=leakInfo h r hb hr g n
 obtain⟨P,Q,v,b1,b2,A⟩:=leakPair h r hb l (Finset.subset_empty.1 (e▸aW_ao_r_le_aW_ao_x h.1 hb l a))
 obtain⟨c1,c2⟩:=A x a e
 rcases Zx h.1 r hp q t (aJ hp t f) c1 c2 v b1 b2 z s m with j|j
 · exact k (c _ (j▸(ak.1 b1).2.1))
 · exact k (c _ (j▸(ak.1 b2).2.1))
include h r hb hp hr in
lemma both24 (z:bL 14 D=0) (t:(2:O)∈Zi D) (w:(4:O)∈Zi D):False:=by
 have l:=cx_dom h r hp (u:=13) (v:=1) t w V (Or.inr V)
 obtain⟨-,le,-,P,Q,pq,p13,q13,A⟩:=shared_PQ_u h r hb hr (Or.inl V) l
 have c:=dy_dom h r z hp (a:=13) (v3:=1) t w (by simpa[dom] using t) V (Or.inr V) V V le.le
 have d:=dy_dom h r z hp (a:=13) (v3:=1) w t (by simpa[dom] using w) V (Or.inr V) V V le.le
 have F:=eF_cand_dom h r hb hp hr (a:=13) (v3:=1) (Or.inl V) t w V (Or.inr V) c d
 simp only[←cW] at F
 have L (x:O) (k:x∈({5,6,11,12}:o)):=clean_le2_of_not_u0 h r hb hr (x:=x) (Or.inl (by revert x k;decide)) (fun n=>((by decide +kernel):∀ y:O,y∈({5,6,11,12}:o)->¬((bK 2 y=true/\bK 4 y=true)\/(bK 2 y=true/\∀ q:O,ac 4 q=true->mV 13 y q=false)\/(bK 4 y=true/\∀ q:O,ac 2 q=true->mV 13 y q=false))) x k (F x n))
 have g:3<=(af 14 D 10).card:=by by_contra n;exact fR_dom h r hp 5 10 12 9 4 2 w t V V (L 5 V) (by omega) (L 12 V)
 have f:3<=(af 14 D 8).card:=by by_contra n;exact fR_dom h r hp 6 8 11 9 2 4 t w V V (L 6 V) (by omega) (L 11 V)
 obtain⟨a,b'⟩:=A 10 (leakIn h r hb hp hr 11 w d g)
 obtain⟨y,v⟩:=A 8 (leakIn h r hb hp hr 12 t c f)
 have n:P≠p 2:=fun e=>b3.1 (by decide:bK 2 10=false) (c 10 (e▸a))
 have m:Q≠p 2:=fun e=>b3.1 (by decide:bK 2 10=false) (c 10 (e▸b'))
 rcases aT p13 q13 (Zj hp t 13) pq n m le.le _ (Zj hp w 13) with j|j|j
 · exact b3.1 (by decide:bK 4 8=false) (d 8 (j▸y))
 · exact b3.1 (by decide:bK 4 8=false) (d 8 (j▸v))
 · exact (Zp hp w t V) j
end
lemma small_ports {D:Dag} (h:ai 14 D) (r:ar D) {pos:O->ℕ×_d} (hp:bA_dom D pos) {i v:O} (hi:i∈aa 14 D) (hiv:aP i v) (hq:quOk i v=true) (lv:(af 14 D v).card<=2):∃ Z,af 14 D v={pos i,Z}/\(∀ t,cmOk i v t=true->t∉ag 14 D (aw D Z)/\Z∉af 14 D t)/\∀ t,aP v t->t∉dom i->am Z∈af 14 D t:=by
 obtain⟨Z,-,hw,hc⟩:=qu_dom h r hp hi hiv hq lv
 refine⟨Z,hw,hc,?_⟩
 intro t hv ht
 obtain⟨e,he,ha,hf,-⟩:=bf h r hp hv
 rw[hw,_mi,_ms] at he
 exact (he.resolve_left (fun q=>ht (hf i hi q)))▸ha
lemma dp_22 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (hI:aa 14 D={4,5,7}):False:=by
 have h4:=Zu hI 4
 have h5:=Zu hI 5
 have h7:=Zu hI 7
 have S:=cx_dom h r hp (u:=10) (v:=0) h4 h5 V (Or.inr V)
 obtain⟨-,d5,-⟩:=shared_PQ_u h r hb hR1 (Or.inr (by rw[hI];decide)) S
 have d0:=dy_dom h r hb0 hp (a:=10) (v3:=0) h4 h5 (by rw[hI];decide) V (Or.inr V) V V (by omega)
 have d1:=dy_dom h r hb0 hp (a:=10) (v3:=0) h5 h4 (by rw[hI];decide) V (Or.inr V) V V (by omega)
 have Y:=eF_cand_dom h r hb hp hR1 (a:=10) (v3:=0) (Or.inr (by rw[hI];decide)) h4 h5 V (Or.inr V) d0 d1
 have i:∀ x:O,x≠10->x∉ag 14 D u0.1:=fun x hx hxu=>by have g:∀ z:O,z≠10->((bK 4 z=true/\bK 5 z=true)\/(bK 4 z=true/\∀ q:O,ac 5 q=true->mV 10 z q=false)\/(bK 5 z=true/\∀ q:O,ac 4 q=true->mV 10 z q=false))->False:=(by decide +kernel);rcases Y x hxu with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩;{exact g x hx (Or.inl ⟨(cW 4 x).2 a,(cW 5 x).2 b⟩)};{exact g x hx (Or.inr (Or.inl ⟨(cW 4 x).2 a,b⟩))};{exact g x hx (Or.inr (Or.inr ⟨(cW 5 x).2 a,b⟩))}
 have E:∀ x:O,x∈({0,9,11,12,13}:o)->(af 14 D x).card<=2:=fun x hx=>clean_le2_of_not_u0 h r hb hR1 (Or.inl (by revert x hx;decide)) (i x (by revert x hx;decide))
 have d6:3<=(af 14 D 1).card:=by by_contra hc;exact dl_dom h r hp 1 9 13 7 5 h7 h5 V V (by omega) (E 9 V)
 have d7:3<=(af 14 D 3).card:=by by_contra hc;exact dl_dom h r hp 3 11 12 7 4 h7 h4 V V (by omega) (E 11 V)
 obtain⟨l,e,t,a⟩:=leakInfo h r hb hR1 d6 (i 1 V)
 obtain⟨k,f,-,b'⟩:=leakInfo h r hb hR1 d7 (i 3 V)
 obtain⟨P,Q,n,-,-,F⟩:=leakPair h r hb t (Finset.subset_empty.1 (e▸aW_ao_r_le_aW_ao_x h.1 hb t a))
 obtain⟨p1,q1⟩:=F 1 a e;obtain⟨p3,q3⟩:=F 3 b' f
 obtain⟨X,A,C,T⟩:=small_ports h r hp h4 (by decide:aP 4 13) V (E 13 V)
 obtain⟨Y,B,N,U⟩:=small_ports h r hp h4 (by decide:aP 4 11) V (E 11 V)
 have Z:=Zforce h.1 r p1 q1 n p3 q3 l 2 (T 1 V V) (T 2 V V)
 have W:=Zforce h.1 r p3 q3 n p1 q1 k 6 (U 3 V V) (U 6 V V)
 have H:=Zx h.1 r hp 0 h7 (Zj hp h7 1) p1 q1 n p3 q3 l V V
 exact Zthree (x:=13) (y:=11) hp h7 (by rw[A];simp) (by rw[B];simp) (C 11 V).2 Z W H
lemma dp_25 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (hI:aa 14 D={4,5,8}):False:=by
 have h4:=Zu hI 4
 have h5:=Zu hI 5
 have h8:=Zu hI 8
 have b1:=Zd hI 4
 have b2:=Zd hI 5
 have k:=Zd hI 8
 have a:3<=(af 14 D 2).card:=by
  by_contra hc
  have a2:3<=(af 14 D 12).card:=by by_contra hc1;exact dl_dom h r hp 2 12 13 8 5 h8 h5 V V (by omega) (by omega)
  have a3:3<=(af 14 D 13).card:=by by_contra hc1;exact dl_dom h r hp 2 13 12 8 4 h8 h4 V V (by omega) (by omega)
  exact im_dom h r hb0 hb hp hR1 12 13 5 4 3 9 11 (Or.inl V) (Or.inl V) h5 h4 b2 V V V a2 a3
 have c:3<=(af 14 D 6).card:=by
  by_contra hc
  have a1:3<=(af 14 D 11).card:=by by_contra hc1;exact dl_dom h r hp 6 11 9 8 4 h8 h4 V V (by omega) (by omega)
  have h9:3<=(af 14 D 9).card:=by by_contra hc1;exact dl_dom h r hp 6 9 11 8 5 h8 h5 V V (by omega) (by omega)
  exact im_dom h r hb0 hb hp hR1 11 9 4 5 3 13 12 (Or.inl V) (Or.inl V) h4 h5 b1 V V V a1 h9
 have b6:(af 14 D 12).card<=2:=by by_contra hc;exact gH_dom h r hb0 hb hp hR1 2 12 8 5 (Or.inl V) (Or.inl V) h8 h5 k V V V a (by omega)
 have b7:(af 14 D 13).card<=2:=by by_contra hc;exact gH_dom h r hb0 hb hp hR1 2 13 8 4 (Or.inl V) (Or.inl V) h8 h4 k V V V a (by omega)
 obtain⟨-,k,-⟩:=shared_PQ_u h r hb hR1 (Or.inl V) a
 obtain⟨P,Q,n,p2,q2,p6,q6,-⟩:=clean_shared_af h r hb hR1 (Or.inl V) (Or.inl V) a c
 obtain⟨X,A,C,T⟩:=small_ports h r hp h5 (by decide:aP 5 12) V b6
 obtain⟨Y,B,N,U⟩:=small_ports h r hp h4 (by decide:aP 4 13) V b7
 have Z:=Zforce h.1 r p2 q2 n p6 q6 k.le 3 (T 2 V V) (T 3 V V)
 have W:=Zforce h.1 r p2 q2 n p6 q6 k.le 1 (U 2 V V) (U 1 V V)
 have H:=Zx h.1 r hp 0 h8 (Zj hp h8 2) p2 q2 n p6 q6 k.le V V
 exact Zthree (x:=12) (y:=13) hp h8 (by rw[A];simp) (by rw[B];simp) (C 13 V).2 Z W H
lemma restrict_ports {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hr:aj 14 D b={u0}) {i v t n:O} (hi:i∈aa 14 D) (hd:dom i⊆aa 14 D) (hv:aP i v) (hn:aP i n) (hw:∃ w:O,aP v w/\w∉dom i) (hc:isClean (aa 14 D) v) (h3:3<=(af 14 D v).card) (ht:t∈ag 14 D u0.1) (hs:∃ f∈af 14 D v,t∉ag 14 D (aw D f)/\n∉ag 14 D (aw D f)):∀ x,x∈ag 14 D u0.1->dj i x:=by
 obtain⟨f,hf,ft,fn⟩:=hs
 obtain⟨-,he,-,P,Q,c,g,j,ha⟩:=shared_PQ_u h r hb hr hc h3
 obtain⟨tp,tq⟩:=ha t ht
 have pf:P≠f:=fun e=>ft (e▸tp)
 have qf:Q≠f:=fun e=>ft (e▸tq)
 have all:=aT g j hf c pf qf (by omega)
 have fi:pos i≠f:=fun e=>fn (e▸(hp.1 i hi).2.2.2.1 n hn)
 have hQ:∃ A,A∈af 14 D v/\A≠pos i/\(∀ x,x∈ag 14 D u0.1->x∈ag 14 D (aw D (pos i))/\x∈ag 14 D (aw D A))/\∀ p∈af 14 D v,p=pos i\/p=A\/p=f:=by
  rcases all (pos i) (aJ hp hi hv) with e|e|e
  · subst P;exact⟨Q,j,c.symm,ha,all⟩
  · subst Q;exact⟨P,g,c,fun x hx=>⟨(ha x hx).2,(ha x hx).1⟩,fun p hp''=>by rcases all p hp'' with a|a|a;{exact Or.inr (Or.inl a)};{exact Or.inl a};{exact Or.inr (Or.inr a)}⟩
  · exact False.elim (fi e)
 obtain⟨A,hA,k,H,T⟩:=hQ
 have N {p:ℕ×_d} (hm:p∈af 14 D v) (hne:p≠pos i):p.1≠(pos i).1:=by
  intro e
  rcases eq_or_am e with q|q;{exact hne q}
  have L:∀ a b:O,aP a b->b∈dom a->False:=by decide +kernel
  exact L i v hv ((hp.1 i hi).2.2.2.2.2.1 (q▸(ak.1 hm).2.1))
 intro x hx
 obtain⟨xi,xa⟩:=H x hx
 by_cases sa:ag 14 D (aw D (am A))⊆dom i
 · have sf:¬ag 14 D (aw D (am f))⊆dom i:=by
    intro s
    obtain⟨w,vw,nw⟩:=hw
    obtain⟨e,ee,ae,de,-⟩:=bf h r hp vw
    rcases T e ee with q|q|q;{exact nw (de i hi q)};{exact nw (sa (q▸(ak.1 ae).2.1))};{exact nw (s (q▸(ak.1 ae).2.1))}
   rcases bz_cap_hp h r hb0 hp hi hd hv hA (N hA k) (fun p hm ni na=>by rcases T p hm with rfl|rfl|rfl;{exact absurd rfl ni};{exact absurd rfl na};{exact sf}) with d|⟨-,-,d⟩
   · exact d x xi
   · exact d x xi xa
 · rcases bz_cap_hp h r hb0 hp hi hd hv hf (N hf fi.symm) (fun p hm ni nf=>by rcases T p hm with rfl|rfl|rfl;{exact absurd rfl ni};{exact sa};{exact absurd rfl nf}) with d|⟨-,d,-⟩
   · exact d x xi
   · exact False.elim (fn (d n hn))
lemma dp_26 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (hI:aa 14 D={4,7,8}):False:=by
 have h4:(4:O)∈aa 14 D:=by rw[hI];decide
 have h7:(7:O)∈aa 14 D:=by rw[hI];decide
 have h8:(8:O)∈aa 14 D:=by rw[hI];decide
 have T:dom 4⊆aa 14 D:=by rw[hI];decide
 have K:dom 8⊆aa 14 D:=by rw[hI];decide
 have d:isClean (aa 14 D) 10:=Or.inr (by rw[hI];decide)
 have cuts:=dl_dom h r hp 0 10 7 8 4 h8 h4 V V
 by_cases k:3<=(af 14 D 2).card
 · have l13:(af 14 D 13).card<=2:=by by_contra hc;exact gH_dom h r hb0 hb hp hR1 2 13 8 4 (Or.inl V) (Or.inl V) h8 h4 K V V V k (by omega)
   have l10:(af 14 D 10).card<=2:=by by_contra hc;exact im_dom h r hb0 hb hp hR1 2 10 8 4 12 6 11 (Or.inl V) d h8 h4 K V V V k (by omega)
   have hi:3<=(af 14 D 0).card:=by by_contra hc;exact cuts (by omega) l10
   obtain⟨-,n,-⟩:=shared_PQ_u h r hb hR1 (Or.inl V) hi
   obtain⟨Z,W,C,M⟩:=small_ports h r hp h4 (by decide:aP 4 10) V l10
   have p:=Zj hp h7 0;have q:=Zj hp h8 0
   have nz (i:O) (a:i∈aa 14 D) (c:cmOk 4 10 i=true):pos i≠am Z:=fun E=>(C i c).1 (by have H:=cd hp a;rwa[E,aB] at H)
   have three:=aT p q (M 0 V V) (fun E=>absurd (hp.2 h7 h8 E) V) (nz 7 h7 V) (nz 8 h8 V) (by omega)
   have out {t:O} {e:ℕ×_d} (m:am e∈af 14 D t) (a:t∉dom 7) (b':t∉dom 8) (c:cmOk 4 10 t=true):e∉af 14 D 0:=by
    intro he;rcases three e he with rfl|rfl|rfl
    · exact a (em_dom hp h7 m)
    · exact b' (em_dom hp h8 m)
    · rw[aB] at m;exact (C t c).2 m
   obtain⟨Y,S,F,G⟩:=small_ports h r hp h4 (by decide:aP 4 13) V l13
   obtain⟨e,he,hm,-⟩:=Zb h r hp 2 12
   have y:am (am Y)∈af 14 D 13:=by rw[aB,S];simp
   have ny:=out y V V V;have ne':=out hm V V V
   exact clean_inter_le1 h r hb hR1 (Or.inl V) (Or.inl V) k hi (G 2 V V) he (Zj hp h8 2) (fun E=>(F 12 V).2 (by rw[<- aB Y,E];exact hm)) (fun E=>ny (E.symm▸q)) (fun E=>ne' (E.symm▸q)) ny ne'
 · have l2:(af 14 D 2).card<=2:=by omega
   have j:3<=(af 14 D 13).card:=by by_contra hc;exact dl_dom h r hp 2 13 12 8 4 h8 h4 V V l2 (by omega)
   have l0:(af 14 D 0).card<=2:=by by_contra hc;exact im_dom h r hb0 hb hp hR1 13 0 4 8 1 11 6 (Or.inl V) (Or.inl V) h4 h8 T V V V j (by omega)
   have g:3<=(af 14 D 10).card:=by by_contra hc;exact cuts l0 (by omega)
   obtain⟨-,X,a0,-⟩:=shared_PQ_u h r hb hR1 d g
   obtain⟨P,Q,R,l,o,B,I,-⟩:=clean_shared_af h r hb hR1 (Or.inl V) d j g
   obtain⟨e010,z,A,x,-⟩:=Zb h r hp 0 10
   have L:=Zj hp h7 0;have N:=Zj hp h8 0
   have w:e010=pos 7:=by rcases gG L N (Zp hp h7 h8 V) l0 e010 z with q|q;{exact q};{exact absurd (x 8 h8 q) V}
   have J:am (pos 7)∈af 14 D 10:=w▸A
   have u:P≠am (pos 7):=fun e=>absurd ((hp.1 7 h7).2.2.2.2.2.1 (e▸(ak.1 l).2.1)) V
   have v:Q≠am (pos 7):=fun e=>absurd ((hp.1 7 h7).2.2.2.2.2.1 (e▸(ak.1 o).2.1)) V
   obtain⟨f,hf,s,U⟩:=Zm h.1 r 10 13 7
   rcases aT B I J R u v (by omega) f hf with rfl|rfl|rfl
   · exact s (ak.1 l).2.1
   · exact s (ak.1 o).2.1
   · exact U (hp.1 7 h7).2.2.2.2.1
lemma dp_27 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (hI:aa 14 D={0,2,9}):False:=by
 have h0:(0:O)∈aa 14 D:=by rw[hI];decide
 have h2:(2:O)∈aa 14 D:=by rw[hI];decide
 have h9:(9:O)∈aa 14 D:=by rw[hI];decide
 have U:dom 2⊆aa 14 D:=by rw[hI];decide
 have W:dom 9⊆aa 14 D:=by rw[hI];decide
 have g:(7:O)∈al 14 D:=by by_contra hc;have:=aN.2 hc;rw[hI] at this;exact absurd this V
 have C:8∈ag 14 D u0.1:=by
  by_contra k
  have M:aZ D b 8=∅:=eq_empty_iff_forall_notMem.2 (fun u hu=>k ((_ms.1 (hR1▸(ay.1 hu).1))▸(ay.1 hu).2))
  exact no_leak_2nbrs h r hb0 hb hp (x:=8) (v3:=6) g V V M h2 h0 V V V V V V (Or.inr V) V (fun h8no=>by
   have h3:=cx_dom h r hp (u:=8) (v:=6) h2 h0 V (Or.inr V)
   have X:=bj_noleak h r hb (x:=8) (fun _ _=>h8no);rw[M,_ce] at X;omega)
 have l1:(af 14 D 1).card<=2:=by
  by_contra hc
  exact (b3.1 (by decide:bK 9 8=false)) (restrict_ports h r hb0 hb hp hR1 (v:=1) (n:=5) h9 W V V ⟨7,V,V⟩ (Or.inr (by rw[hI];decide)) (by omega) C (bE_dom h.1 r V) 8 C)
 have B:3<=(af 14 D 13).card:=by by_contra hc;exact dl_dom h r hp 1 13 7 9 2 h9 h2 V V l1 (by omega)
 have a:=restrict_ports h r hb0 hb hp hR1 (v:=13) (n:=12) h2 U V V ⟨4,V,V⟩ (Or.inl V) B C (bE_dom h.1 r V)
 have l5:(af 14 D 5).card<=2:=clean_le2_of_not_u0 h r hb hR1 (Or.inl V) (fun h5u=>absurd (a 5 h5u) (b3.1 V))
 have l7:(af 14 D 7).card<=2:=clean_le2_of_not_u0 h r hb hR1 (Or.inl V) (fun h7u=>absurd (a 7 h7u) (b3.1 V))
 have R:3<=(af 14 D 10).card:=by by_contra hc;exact dl_dom h r hp 10 5 4 0 9 h0 h9 V V (by omega) l5
 have z:aZ D b 10=∅:=eq_empty_iff_forall_notMem.2 (fun u hu=>absurd (a 10 ((_ms.1 (hR1▸(ay.1 hu).1))▸(ay.1 hu).2)) (b3.1 V))
 have S:(af 14 D 10).card+(aW 14 D (ao 14 D {10})).card<=3:=by have:=bj_any h r hb 10;rw[z,_ce] at this;omega
 have l:aW 14 D (ao 14 D {10})=∅:=card_eq_zero.1 (by omega)
 have d:10∈ag 14 D (b 7):=by by_contra k;have:=bj_noleak h r hb (x:=10) (fun _ _=>k);rw[z,_ce] at this;omega
 have E:aW 14 D (ao 14 D {7})=∅:=Finset.subset_empty.1 (l▸aW_ao_r_le_aW_ao_x h.1 hb g d)
 obtain⟨P7,Q7,G,s,t,I,L⟩:=dV_tree h r E (hb 7 g).2.1 (hb 7 g).1
 have F:=gD h.1 l (ak.1 s).1 (cY h.1 s) (bk_x_ag h.1 E I d)
 have J:=gD h.1 l (ak.1 t).1 (cY h.1 t) (bk_x_ag h.1 E L d)
 obtain⟨Z5,-,A,em5⟩:=small_ports h r hp h9 (by decide:aP 9 5) V l5
 have o:=em5 10 V V
 have c:=em5 12 V V
 have i:am Z5∈af 14 D 7:=by
  by_contra k
  have H:P7≠am Z5:=fun e=>k (e▸s);have K:Q7≠am Z5:=fun e=>k (e▸t)
  obtain⟨f,hf,Q,p⟩:=Zm h.1 r 10 7 12
  rcases aT F J o (fun e=>G (e▸rfl)) H K (by omega) f hf with rfl|rfl|rfl
  · exact Q (ak.1 s).2.1
  · exact Q (ak.1 t).2.1
  · exact p (ak.1 c).2.1
 obtain⟨Z1,T,-,em1⟩:=small_ports h r hp h9 (by decide:aP 9 1) V l1
 have y:=em1 7 V V
 have m:=em1 13 V V
 have j:pos 0≠am Z5:=fun e=>(A 0 V).1 (by have:=(hp.1 0 h0).2.2.2.2.1;rwa[e,aB] at this)
 have w:am Z1=pos 0:=by
  rcases gG (Zj hp h0 7) i j l7 (am Z1) y with q|q;{exact q}
  · exfalso;have N:Z1=Z5:=(by rw[<- aB Z1,<-aB Z5,q]);exact (A 1 V).2 (by rw[<- N,T];simp)
 obtain⟨f,hf,p,P⟩:=Zm h.1 r 7 12 13
 rcases gG (Zj hp h0 7) i j l7 f hf with rfl|rfl
 · exact P (ak.1 (w▸m)).2.1
 · exact p (ak.1 c).2.1
lemma dp_17 {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hR1:aj 14 D b={u0}) (hI:aa 14 D={0,4,5}):False:=by
 have h0:(0:O)∈aa 14 D:=by rw[hI];decide
 have h4:(4:O)∈aa 14 D:=by rw[hI];decide
 have h5:(5:O)∈aa 14 D:=by rw[hI];decide
 have g1:dom 4⊆aa 14 D:=by rw[hI];decide
 have g2:dom 5⊆aa 14 D:=by rw[hI];decide
 have I:(7:O)∈al 14 D:=by by_contra hc;have:=aN.2 hc;rw[hI] at this;exact absurd this V
 have b9:10∈ag 14 D u0.1:=by
  by_contra b7
  have a5:aZ D b 10=∅:=eq_empty_iff_forall_notMem.2 (fun u hu=>b7 ((_ms.1 (hR1▸(ay.1 hu).1))▸(ay.1 hu).2))
  exact no_leak_2nbrs h r hb0 hb hp (x:=10) (v3:=0) I V V a5 h4 h5 V V V V V V (Or.inl h0) V (fun h10no=>by
   have h3:=cx_dom h r hp (u:=10) (v:=0) h4 h5 V (Or.inl h0);have f2:=bj_noleak h r hb (x:=10) (fun _ _=>h10no);rw[a5,_ce] at f2;omega)
 have d:∀ (v i x:O),v∈({9,11,12,13}:o)->isClean (aa 14 D) v->i∈aa 14 D->dom i⊆aa 14 D->aP i v->aP i 10->(∃ y:O,ac v y=true/\bK y 10=false)->¬ dj i x->3<=(af 14 D v).card->x∈ag 14 D u0.1->False:=by
  intro v i x hv e6 hi e8 d4 d0 f0 d5 f3 f5
  have L:∀ i v:O,v∈({9,11,12,13}:o)->aP i v->∃ w:O,aP v w/\w∉dom i:=by decide +kernel
  obtain⟨f,ef,nf⟩:=kb_dom h.1 r f0
  exact d5 (restrict_ports h r hb0 hb hp hR1 hi e8 d4 d0 (L i v hv d4) e6 f3 b9 ⟨f,ef,nf,nf⟩ x f5)
 have N (k:Bool):let a:O:=if k then 9 else 13;let b':O:=if k then 12 else 11;let d1:O:=if k then 13 else 9;let d2:O:=if k then 11 else 12;let i1:O:=if k then 5 else 4;let i2:O:=if k then 4 else 5;let p1:O:=if k then 6 else 2;let p2:O:=if k then 2 else 6;3<=(af 14 D a).card→3<=(af 14 D b').card→(af 14 D 1).card<=2→(af 14 D 3).card<=2→(af 14 D d1).card<=2→(af 14 D d2).card<=2→False:=by
  intro a b' d1 d2 i1 i2 p1 p2 b5 c7 lc1 lc2 ld1 ld2
  have J {P:Prop} (n:P:=by first | (rw[hI];cases k <;> decide) | (cases k <;> decide)):P:=n
  have H:i1∈aa 14 D:=J;have d3:i2∈aa 14 D:=J
  have b6:isClean (aa 14 D) a:=J;have c8:isClean (aa 14 D) b':=J
  have kill {x:O} (n:bK i1 x=false):x∉ag 14 D u0.1:=d a i1 x J b6 H J J J J (b3.1 n) b5
  have lp1:=clean_le2_of_not_u0 h r hb hR1 (x:=p1) J (kill J);have lp2:=clean_le2_of_not_u0 h r hb hR1 (x:=p2) J (kill J)
  have l7:=clean_le2_of_not_u0 h r hb hR1 (x:=7) J (kill J);have c0:8∉ag 14 D u0.1:=kill J
  obtain⟨-,c6,-⟩:=shared_PQ_u h r hb hR1 b6 b5;obtain⟨-,e5,-⟩:=shared_PQ_u h r hb hR1 c8 c7
  obtain⟨P,Q,d9,e0,e2,e1,e4,-⟩:=clean_shared_af h r hb hR1 b6 c8 b5 c7
  have c9:∃ Q0,Q0≠pos i1/\Q0∈af 14 D a/\Q0∈af 14 D b':=by by_cases e:P=pos i1;{exact⟨Q,e▸d9.symm,e2,e4⟩};{exact⟨P,e,e0,e1⟩}
  obtain⟨Q0,a2,M,a0⟩:=c9
  let A:=af 14 D
  have inj:Function.Injective am:=fun x y e=>by rw[←aB x,←aB y,e]
  have edge {x y:O} (g:ac x y=true):∃ e∈A y,am e∈A x:=by
   obtain⟨e,he,hm,-⟩:=bf h r hp (bm ((ae _ _).1 g));exact ⟨e,he,hm⟩
  have ban {i x:O} {e:ℕ×_d} (hi:i∈aa 14 D) (hn:x∉dom i) (he:am e∈A x):pos i≠e:=fun q=>hn ((hp.1 i hi).2.2.2.2.2.1 (by rw[q];exact (ak.1 he).2.1))
  obtain⟨Z1,g4,n1,t1⟩:=small_ports h r hp d3 J J ld1
  obtain⟨Z2,f4,n2,t2⟩:=small_ports h r hp d3 J J ld2
  have wing {c x y p:O} {Z:ℕ×_d} (zc:am Z∈A c) (zp:am Z∈A p) (z7:Z∉A 7) (zx:Z∉A x) (lc:(A c).card<=2) (lx:(A x).card=3) (cn:c∉dom i1) (g7:ac c 7=true) (gx:ac c x=true) (ix:aP i1 x) (iy:aP i1 y) (qx:Q0∈A x) (qy:Q0∈A y) (mv:mV x y 7=true) (kb:∃ j:O,ac c j=true/\bK j p=false):Q0∈A 7/\am Q0∉A p:=by
   obtain⟨E,e7,ec⟩:=edge g7;obtain⟨F,fx,fc⟩:=edge gx
   have ne:am Z≠am E:=fun q=>z7 ((inj q).symm▸e7)
   rcases gG zc ec ne lc (am F) fc with q|q
   · exact False.elim (zx (inj q▸fx))
   have fe:=inj q;subst F
   have eq:E=Q0:=by
    by_contra hn;obtain⟨f,hf,ny,n7⟩:=bE_dom h.1 r mv
    rcases aT (aJ hp H ix) qx fx a2.symm (ban H cn ec) (Ne.symm hn) lx.le f hf with rfl|rfl|rfl
    · exact ny ((hp.1 i1 H).2.2.2.1 y iy)
    · exact ny (ak.1 qy).2.1
    · exact n7 (ak.1 e7).2.1
   subst E;refine ⟨e7,fun hm=>?_⟩
   obtain⟨f,hf,hn⟩:=kb_dom h.1 r kb;rcases gG zc ec ne lc f hf with rfl|rfl;{exact hn (ak.1 zp).2.1};{exact hn (ak.1 hm).2.1}
  have zp1:=t2 p1 J J
  have zp2:=t1 p2 J J
  have ia:aP i1 a:=J;have ib:aP i1 b':=J
  obtain⟨q7,nq2⟩:=wing (t1 1 J J) zp2 (n1 7 J).2 (n1 a J).2 lc1 c6 J J J ia ib M a0 J J
  obtain⟨-,nq1⟩:=wing (t2 3 J J) zp1 (n2 7 J).2 (n2 b' J).2 lc2 e5 J J J ib ia a0 M J J
  have side {p x:O} {Z:ℕ×_d} (zp:am Z∈A p) (zx:Z∉A x) (lp:(A p).card<=2) (g8:ac p 8=true) (gx:ac p x=true) (pn:p∉dom 0) (nq:am Q0∉A p):∃ X Y,X∈A 8/\Y∈A x/\am Y∈A p/\(X=Z∨X=Y)/\pos 0≠X/\Q0≠Y:=by
   obtain⟨X,hx,d7⟩:=edge g8;obtain⟨Y,hy,b8⟩:=edge gx
   have n:am Z≠am Y:=fun q=>zx ((inj q).symm▸hy)
   exact ⟨X,Y,hx,hy,b8,(gG zp b8 n lp _ d7).imp (fun e=>inj e) (fun e=>inj e),ban h0 pn d7,fun q=>nq (q.symm▸b8)⟩
  obtain⟨X,Y,x8,ya,yp,ox,nx,ny⟩:=side zp1 (n2 a J).2 lp1 J J J nq1
  obtain⟨U,T,u8,tb,_,ou,nu,nt⟩:=side zp2 (n1 b' J).2 lp2 J J J nq2
  have yt:Y≠T:=fun eq=>by
   obtain⟨f,hf,hn⟩:=kb_dom h.1 r (x:=a) (a:=b') J
   rcases aT (aJ hp H ia) M ya a2.symm (ban H J yp) ny c6.le f hf with rfl|rfl|rfl
   · exact hn (ak.1 (aJ hp H ib)).2.1
   · exact hn (ak.1 a0).2.1
   · exact hn (ak.1 (eq.symm▸tb)).2.1
  have xu:X≠U:=fun e=>by
   rcases ox with q|q <;> rcases ou with s|s
   · exact (n1 d2 J).2 (by rw[←s,←e,q,f4];simp)
   · exact (n2 b' J).2 (by rw[←q,e,s];exact tb)
   · exact (n1 a J).2 (by rw[←s,←e,q];exact ya)
   · exact yt (q.symm.trans (e.trans s))
  have p08:=Zj hp h0 8
  have f6:=d6 p08 x8 u8 nx nu xu
  have c5:aZ D b 8=∅:=eq_empty_iff_forall_notMem.2 (fun u hu=>c0 ((_ms.1 (hR1▸(ay.1 hu).1))▸(ay.1 hu).2))
  have f8:(af 14 D 8).card+(aW 14 D (ao 14 D {8})).card<=3:=by have:=bj_any h r hb 8;rw[c5,_ce] at this;omega
  have b0:aW 14 D (ao 14 D {8})=∅:=card_eq_zero.1 (by omega)
  have S:8∈ag 14 D (b 7):=by by_contra b7;have:=bj_noleak h r hb (x:=8) (fun _ _=>b7);rw[c5,_ce] at this;omega
  have a8:aW 14 D (ao 14 D {7})=∅:=Finset.subset_empty.1 (b0▸aW_ao_r_le_aW_ao_x h.1 hb I S)
  obtain⟨P7,Q7,c1,b2,b4,c2,c4⟩:=dV_tree h r a8 (hb 7 I).2.1 (hb 7 I).1
  have f9:=gD h.1 b0 (ak.1 b2).1 (cY h.1 b2) (bk_x_ag h.1 a8 c2 S)
  have g0:=gD h.1 b0 (ak.1 b4).1 (cY h.1 b4) (bk_x_ag h.1 a8 c4 S)
  have cover {f:ℕ×_d} (hf:f∈A 7):f=pos 0∨f=Y∨f=T:=by
   have e9:f∈A 8:=by rcases gG b2 b4 (fun e=>c1 (e▸rfl)) l7 f hf with rfl|rfl <;> assumption
   rcases aT p08 x8 u8 nx nu xu (by omega) f e9 with q|q|q
   · exact Or.inl q
   · rcases ox with s|s;{exact False.elim ((n2 7 J).2 ((q.trans s)▸hf))};{exact Or.inr (Or.inl (q.trans s))}
   · rcases ou with s|s;{exact False.elim ((n1 7 J).2 ((q.trans s)▸hf))};{exact Or.inr (Or.inr (q.trans s))}
  have q0:=((cover q7).resolve_right (fun w=>w.elim ny nt))
  obtain⟨f,hf,na,nb⟩:=bE_dom h.1 r (x:=7) (a:=a) (b:=b') J
  rcases cover hf with s|s|s
  · exact na (ak.1 ((q0.trans s.symm)▸M)).2.1
  · exact na (ak.1 (s.symm▸ya)).2.1
  · exact nb (ak.1 (s.symm▸tb)).2.1
 let W:=af 14 D
 have K (v i x:O) (g:v∈({9,11,12,13}:o)/\i∈({0,4,5}:o)/\dom i⊆({0,4,5}:o)/\isClean {0,4,5} v/\isClean {0,4,5} x/\aP i v/\aP i 10/\(∃ y:O,ac v y=true/\bK y 10=false)/\bK i x=false) (hv:3<=(W v).card) (hx:3<=(W x).card):False:=by
  rw[←hI] at g
  obtain ⟨sv,hi,di,cv,cx,iv,it,k,n⟩:=g
  exact d v i x sv cv hi di iv it k (b3.1 n) hv (clean_u0_of_ge3 h r hb hR1 cx hx)
 have low (x:O) (hx:3<=(W x).card→False):(W x).card<=2:=by by_contra q;exact hx (by omega)
 have Ck {P:Prop} (z:P:=by (repeat' apply And.intro) <;> decide):P:=z
 by_cases h9:3<=(af 14 D 9).card
 · have l11:=low 11 (K 9 5 11 Ck h9)
   have l13:=low 13 (K 9 5 13 Ck h9)
   have l1:=low 1 (K 9 5 1 Ck h9)
   have l3:=low 3 (K 9 5 3 Ck h9)
   have a7:3<=(af 14 D 12).card:=by by_contra hc;exact fR_dom h r hp 3 11 12 7 4 5 h4 h5 V V l3 l11 (by omega)
   exact N true h9 a7 l1 l3 l13 l11
 · have l9:(af 14 D 9).card<=2:=by omega
   by_cases a3:3<=(af 14 D 13).card
   · have l12:=low 12 (K 13 4 12 Ck a3)
     have l1:=low 1 (K 13 4 1 Ck a3)
     have l3:=low 3 (K 13 4 3 Ck a3)
     have a6:3<=(af 14 D 11).card:=by by_contra hc;exact fR_dom h r hp 3 11 12 7 4 5 h4 h5 V V l3 (by omega) l12
     exact N false a3 a6 l1 l3 l9 l12
   · have l13:(af 14 D 13).card<=2:=by omega
     have R:3<=(af 14 D 1).card:=by by_contra hc;exact fR_dom h r hp 1 9 13 7 5 4 h5 h4 V V (by omega) l9 l13
     have l11:=low 11 (fun q=>K 11 4 1 Ck q R)
     have l12:=low 12 (fun q=>K 12 5 1 Ck q R)
     have a4:3<=(af 14 D 3).card:=by by_contra hc;exact fR_dom h r hp 3 11 12 7 4 5 h4 h5 V V (by omega) l11 l12
     have port (i v x:O) (hi:i∈aa 14 D) (g:aP i v/\quOk i v=true/\aP v x/\x∉dom i) (l:(W v).card<=2):∃ e∈W x,am e∈W v/\∀ t,cmOk i v t=true→am e∉W t:=by
      obtain ⟨Z,hw,n,t⟩:=small_ports h r hp hi g.1 g.2.1 l
      refine ⟨am Z,t x g.2.2.1 g.2.2.2,?_,?_⟩
      · change am (am Z)∈af 14 D v;rw[aB,hw];simp
      · intro z hz;rw[aB];exact (n z hz).2
     obtain⟨A,a1,a9,na⟩:=port 5 9 1 h5 V l9;obtain⟨B,b1,b13,nb⟩:=port 4 13 1 h4 V l13
     obtain⟨C,c3,c11,nc⟩:=port 4 11 3 h4 V l11;obtain⟨E,e3,e12,ne⟩:=port 5 12 3 h5 V l12
     obtain⟨F,f1,f7,-⟩:=Zb h r hp 1 7;obtain⟨G,g3,g7,-⟩:=Zb h r hp 3 7
     have sep {e f:ℕ×_d} {x:O} (n:am e∉W x) (m:am f∈W x):e≠f:=fun q=>n (q.symm▸m)
     obtain⟨-,d8,-⟩:=shared_PQ_u h r hb hR1 (Or.inr (by rw[hI];decide)) a4
     have span:=aT c3 e3 g3 (sep (nc 12 V) e12) (sep (nc 7 V) g7) (sep (ne 7 V) g7) (Nat.le_of_eq d8)
     have out {z:ℕ×_d} (a6:am z∉W 11) (a7:am z∉W 12) (h7:am z∉W 7):z∉W 3:=fun hz=>(span z hz).elim (sep a6 c11) (fun w=>w.elim (sep a7 e12) (sep h7 g7))
     exact clean_inter_le1 h r hb hR1 (Or.inr (by rw[hI];decide)) (Or.inr (by rw[hI];decide)) R a4 a1 b1 f1 (sep (na 13 V) b13) (sep (na 7 V) f7) (sep (nb 7 V) f7) (out (na 11 V) (na 12 V) (na 7 V)) (out (nb 11 V) (nb 12 V) (nb 7 V))
section
local instance dCleanD {I x}:Decidable (isClean I x):=by unfold isClean;infer_instance
local instance dAdjD {i x}:Decidable (aP i x):=by unfold aP _B.aO;infer_instance
def dCut (I:o) (x v w:O):Prop:=∃ j∈I,aP j v ∧ x∉dom j ∧ cmOk j v w=true
instance {I x v w}:Decidable (dCut I x v w):=by unfold dCut;infer_instance
def dCap (I J L P E:o) (x:O):Prop:=
 isClean I x ∧ P⊆I ∧ (∀ i∈P,aP i x ∨ i∈J) ∧ (∀ v∈E,aP x v) ∧
 (∀ i∈P,∀ v∈E,v∉dom i) ∧
 (∀ v∈E,∀ w∈E,v≠w → (v∈L ∧ dCut I x v w) ∨ (w∈L ∧ dCut I x w v)) ∧ 4≤P.card+E.card
instance {I J L P E x}:Decidable (dCap I J L P E x):=by
 unfold dCap
 repeat' refine @instDecidableAnd _ _ ?_ ?_
 all_goals infer_instance
abbrev dCx (I:o) (x i j v:O):Prop:=i∈I ∧ j∈I ∧ i≠j ∧ ac i x=true ∧ ac j x=true ∧ ac x v=true ∧ v≠i ∧ v≠j ∧ (v∈I ∨ (v∉dom i ∧ v∉dom j))
abbrev dFo (I:o) (x y i q:O):Prop:=isClean I x ∧ isClean I y ∧ i∈I ∧ aP i x ∧ aP i q ∧ mV x y q=true
structure dModel (I:o) (G K:O→Prop):Prop where
 cx:∀ x i j v:O,dCx I x i j v → G x
 dl:∀ z k v i j:O,i∈I ∧ j∈I ∧ (z∉dom j ∧ k∉dom i ∧ v∉dom i) ∧ (ac i z=true ∧ ac j k=true ∧ ac z k=true ∧ ac z v=true ∧ cmOk j k v=true) → ¬G z → ¬G k → False
 fr:∀ u l m v i j:O,i∈I ∧ j∈I ∧ (u∉dom i ∧ u∉dom j) ∧ (ac u l=true ∧ ac u m=true ∧ ac u v=true ∧ ac i l=true ∧ ac j m=true ∧ cmOk i l m=true ∧ cmOk i l v=true ∧ cmOk j m v=true) → ¬G u → ¬G l → ¬G m → False
 fo:∀ x y i q:O,dFo I x y i q → G x → G y → K i
 si:∀ x i j:O,isClean I x ∧ i∈I ∧ j∈I ∧ i≠j ∧ aP i x ∧ aP j x → G x → K i ∨ K j
 cap:∀ (x:O) (P E J L:o),dCap I J L P E x → G x → (∀ i∈J,K i) → (∀ v∈L,¬G v) → False
 tail:∀ x y v i t k j:O,isClean I x ∧ isClean I y ∧ i∈I ∧ k∈I ∧ j∈I ∧ k≠j ∧ aP i v ∧ quOk i v=true ∧ aP v x ∧ aP v t ∧ x∉dom i ∧ t∉dom i ∧ v∉dom k ∧ v∉dom j ∧ mV x y t=true → G x → G y → ¬G v → K k → K j → False
lemma ZzeroM {I G K} (m:dModel I G K) (x y i j v k l w q:O)
 (a:dCx I x i j v:=by decide) (b:dCx I y k l w:=by decide) (c:dFo I x y i q:=by decide)
 (d:dCap I {i} ∅ (if w∈I then {i,k,l,w} else {i,k,l}) (if w∈I then ∅ else {w}) y:=by decide +kernel):False:=by
 have gy:=m.cx y k l w b
 have ki:=m.fo x y i q c (m.cx x i j v a) gy
 exact m.cap y _ _ _ _ d gy (by simpa using ki) (by simp)
lemma dMake {D:Dag} (h:ai 14 D) (r:ar D) {b:O→ℕ} (hb:cU_dom D b) {pos:O→ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} (hr:aj 14 D b={u0}):∃ G K,dModel (aa 14 D) G K:=by
 classical
 let G:=fun x=>3≤(af 14 D x).card
 have H:∃ P Q:ℕ×_d,P≠Q ∧ ∀ x:O,isClean (aa 14 D) x → G x → (af 14 D x).card=3 ∧ P∈af 14 D x ∧ Q∈af 14 D x:=by
  by_cases a:∃ x:O,isClean (aa 14 D) x ∧ G x
  · obtain ⟨x,c,g⟩:=a
    obtain ⟨-,-,-,P,Q,n,p,q,F⟩:=shared_PQ_u h r hb hr c g
    refine ⟨P,Q,n,fun y cy gy=>?_⟩
    obtain ⟨-,e,m,-⟩:=shared_PQ_u h r hb hr cy gy
    obtain ⟨s,t⟩:=F y (clean_u0_of_ge3 h r hb hr cy gy)
    exact ⟨e,PQ_in_af h.1 m p s,PQ_in_af h.1 m q t⟩
  · exact ⟨(0,false),(0,true),by decide,fun x c g=>False.elim (a ⟨x,c,g⟩)⟩
 obtain ⟨P,Q,pq,F⟩:=H
 let K:=fun i=>pos i=P ∨ pos i=Q
 have km {x i:O} (c:isClean (aa 14 D) x) (g:G x) (k:K i):pos i∈af 14 D x:=by
  rcases k with e|e <;> rw[e];exact (F x c g).2.1;exact (F x c g).2.2
 have lo {x:O} (l:¬G x):(af 14 D x).card≤2:=by dsimp [G] at l;omega
 refine ⟨G,K,?_⟩
 constructor
 · rintro x i j v ⟨a,b,n,c,d,e,f,g,t⟩
   exact cx_dom h r hp a b ⟨n,c,d,e,f,g⟩ t
 · rintro z k v i j ⟨a,b,c,d⟩ p q
   exact dl_dom h r hp z k v i j a b c d (lo p) (lo q)
 · rintro u l m v i j ⟨a,b,c,d⟩ p q s
   exact fR_dom h r hp u l m v i j a b c d (lo p) (lo q) (lo s)
 · rintro x y i q ⟨cx,cy,hi,hx,hq,hm⟩ gx gy
   obtain ⟨e,p,s⟩:=F x cx gx
   obtain ⟨-,py,sy⟩:=F y cy gy
   obtain ⟨f,hf,fy,fq⟩:=bE_dom h.1 r hm
   by_contra hn
   change ¬(_ ∨ _) at hn
   rw[not_or] at hn
   rcases aT p s (aJ hp hi hx) pq (Ne.symm hn.1) (Ne.symm hn.2) (by omega) f hf with rfl|rfl|rfl
   exacts [fy (ak.1 py).2.1,fy (ak.1 sy).2.1,fq ((hp.1 i hi).2.2.2.1 q hq)]
 · rintro x i j ⟨cx,hi,hj,n,a,b⟩ gx
   obtain ⟨e,p,s⟩:=F x cx gx
   by_contra! hn
   change (¬(_ ∨ _)) ∧ ¬(_ ∨ _) at hn
   simp only [not_or] at hn
   have:=mm p s (aJ hp hi a) (aJ hp hj b) pq (Ne.symm hn.1.1) (Ne.symm hn.2.1) (Ne.symm hn.1.2) (Ne.symm hn.2.2) (fun w=>n (hp.2 hi hj w))
   omega
 · rintro x A E J L ⟨cx,ai,ap,ae,ad,ac,n⟩ gx kj gl
   choose f hf using fun v (hv:aP x v)=>bf h r hp hv
   let f':O→ℕ×_d:=fun v=>if hv:aP x v then f v hv else (0,false)
   have H {v:O} (hv:v∈E):f' v∈af 14 D x ∧ am (f' v)∈af 14 D v ∧ (∀ i∈aa 14 D,f' v=pos i → v∈dom i) ∧ ∀ i∈aa 14 D,am (f' v)=pos i → x∈dom i:=by simpa only [f',dite_eq_left (ae v hv)] using hf v (ae v hv)
   have diff {v w:O} (vE:v∈E) (wE:w∈E) (vl:v∈L) (d:dCut (aa 14 D) x v w):f' v≠f' w:=by
    obtain ⟨i,hi,iv,xd,cm⟩:=d
    obtain ⟨Z,-,W,C⟩:=qu_dom h r hp hi iv (cmOk_quOk i v w cm) (lo (gl v vl))
    have a:am (f' v)∈af 14 D v:=(H vE).2.1
    rw[W,_mi,_ms] at a
    have eq:=a.resolve_left (fun e=>xd ((H vE).2.2.2 i hi e))
    exact fun e=>(C w cm).2 (eq▸e.symm▸(H wE).2.1)
   have inj:Set.InjOn f' E:=by
    intro v hv w hw eq
    by_contra n
    rcases ac v hv w hw n with ⟨l,d⟩|⟨l,d⟩
    exacts [diff hv hw l d eq,diff hw hv l d eq.symm]
   have dis:Disjoint (A.image pos) (E.image f'):=by
    apply Finset.disjoint_left.2
    intro s a b
    obtain ⟨i,hi,rfl⟩:=mem_image.1 a
    obtain ⟨v,hv,eq⟩:=mem_image.1 b
    exact ad i hi v hv ((H hv).2.2.1 i (ai hi) eq)
   have sub:A.image pos ∪ E.image f' ⊆ af 14 D x:=by
    intro s hs
    rcases mem_union.1 hs with a|b
    · obtain ⟨i,hi,rfl⟩:=mem_image.1 a
      exact (ap i hi).elim (aJ hp (ai hi)) (fun v=>km cx gx (kj i v))
    · obtain ⟨v,hv,rfl⟩:=mem_image.1 b
      exact (H hv).1
   have cc:=_cl sub
   rw[card_union_of_disjoint dis,card_image_of_injOn (fun _ a _ b e=>hp.2 (ai a) (ai b) e),card_image_of_injOn inj] at cc
   have eq:=(F x cx gx).1
   omega
 · rintro x y v i t k j ⟨cx,cy,hi,hk,hj,n,iv,q,vx,vt,xi,ti,vk,vj,m⟩ gx gy lv kk kj
   obtain ⟨Z,-,W,-⟩:=qu_dom h r hp hi iv q (lo lv)
   have T {w:O} (a:aP v w) (b:w∉dom i):am Z∈af 14 D w:=by
    obtain ⟨s,sv,sw,d,-⟩:=bf h r hp a
    rw[W,_mi,_ms] at sv
    exact (sv.resolve_left (fun e=>b (d i hi e)))▸sw
   have zm:Z∈af 14 D v:=by rw[W];simp
   have N {l:O} (hl:l∈aa 14 D) (vd:v∉dom l):pos l≠am Z:=fun e=>vd ((hp.1 l hl).2.2.2.2.2.1 (by rw[e,aB];exact (ak.1 zm).2.1))
   obtain ⟨f,hf,fy,ft⟩:=bE_dom h.1 r m
   rcases aT (km cx gx kk) (km cx gx kj) (T vx xi) (fun e=>n (hp.2 hk hj e)) (N hk vk) (N hj vj) (F x cx gx).1.le f hf with rfl|rfl|rfl
   exacts [fy (ak.1 (km cy gy kk)).2.1,fy (ak.1 (km cy gy kj)).2.1,ft (ak.1 (T vt ti)).2.1]
lemma dCore31 {G K} (s:dModel {0,1,2,4} G K):False:=by
 have a:=s.cx 13 1 2 4 V
 have b:=s.fo 13 7 2 8 V
 have c:=s.fo 13 12 1 9 V
 have d:=s.cap 12 {1,2,4} {3} {1,4} ∅ V
 have e:=s.fr 3 12 7 11 2 1 V
 have f:=s.cap 7 {1,2,4} {0} {2,4} ∅ V
 have g:=s.fo 13 7 4 10 V
 have h:=s.fo 13 3 1 9 V
 have i:=s.cap 3 {1} {7,11,12} {1} {7,12} V
 have j:=s.fo 13 12 4 11 V
 simp at d f i
 tauto
lemma dCore40 {G K} (s:dModel {0,4,5,7} G K):False:=by
 have a:=s.cap 11 {4,5} {3,6} {5} {3} V
 have b:=s.fo 10 3 4 13 V
 have c:=s.fo 10 11 5 9 V
 have d:=s.dl 11 3 6 4 7 V
 have e:=s.cx 10 0 4 5 V
 have f:=s.cap 3 {4,7} {11,12} {4} {11} V
 have g:=s.cap 3 {4,5,7} {11} {4,5} ∅ V
 simp at a f g
 tauto
lemma dCore44 {G K} (s:dModel {4,5,7,8} G K):False:=by
 have a:=s.cx 10 4 5 0 V
 have b:=s.cap 9 {4,5} {1,6} {4} {6} V
 have c:=s.dl 9 6 1 5 8 V
 have d:=s.cap 10 {4,5,8} {0} {8} ∅ V
 have e:=s.fo 6 10 8 2 V
 have f:=s.fo 10 9 4 11 V
 simp at b d
 tauto
lemma dCore45 {G K} (s:dModel {0,2,3,9} G K):False:=by
 have a:=s.cx 12 2 3 5 V
 have b:=s.cap 13 {2,3} {1,4} {3} {1} V
 have c:=s.dl 13 1 4 2 9 V
 have d:=s.fo 12 13 3 11 V
 have e:=s.cap 12 {2,3,9} {5} {9} ∅ V
 have f:=s.fo 1 12 9 6 V
 simp at b e
 tauto
lemma dCore46 {G K} (s:dModel {0,2,4,9} G K):False:=by
 have a:=s.fo 12 13 2 8 V
 have b:=s.si 13 2 4 V
 have c:=s.fo 11 13 4 10 V
 have d:=s.fr 3 11 12 7 4 2 V
 have e:=s.cap 1 {2,4,9} {7} {2,4} ∅ V
 have f:=s.fo 13 11 2 12 V
 have g:=s.cap 3 {2} {7,11,12} {2} {11,12} V
 have h:=s.cap 3 {4} {7,11,12} {4} {11,12} V
 have i:=s.cx 13 2 4 1 V
 have j:=s.tail 13 11 1 9 7 2 4 V
 have k:=s.fo 13 12 4 11 V
 have l:=s.tail 13 12 1 9 7 2 4 V
 simp at e g h
 have z (p:K 2) (q:K 4):¬G 1:=fun m=>e m p q
 have z11:¬G 11:=fun m=>j i m (z (f i m) (c m i)) (f i m) (c m i)
 have z12:¬G 12:=fun m=>l i m (z (a m i) (k i m)) (a m i) (k i m)
 have z3:G 3:=Classical.byContradiction (fun t=>d t z11 z12)
 rcases b i with p|q
 exacts [z12 (g z3 p z11),z12 (h z3 q z11)]
lemma dCore49 {G K} (s:dModel {2,4,7,9} G K):False:=by
 have a:=s.fo 10 8 4 11 V
 have b:=s.dl 10 5 0 4 9 V
 have c:=s.fo 6 13 9 5 V
 have d:=s.cap 13 {2,4,9} {1} {9} ∅ V
 have e:=s.cx 13 2 4 1 V
 have f:=s.dl 8 6 0 2 9 V
 have g:=s.fo 13 5 4 11 V
 have h:=s.cap 8 {2,4} {0,6} {4} {6} V
 simp at d h
 tauto
abbrev Zt(i j x v:O):Prop:=i≠j/\ac i x=true/\ac j x=true/\ac x v=true/\v≠i/\v≠j
abbrev Zv(I:o)(i j v:O):Prop:=v∈I\/v∉dom i/\v∉dom j
abbrev Zside(I:o)(i j v:O):Prop:=(dom i⊆I/\j∉dom i/\v∉dom i)\/(i=0/\(7:O)∈I)
abbrev Zallow(i j a y:O):Prop:=(bK i y=true/\bK j y=true)\/(bK i y=true/\∀ q:O,ac j q=true->mV a y q=false)\/(bK j y=true/\∀ q:O,ac i q=true->mV a y q=false)
abbrev Zst(I:o)(a i j v:O):Prop:=isClean I a/\i∈I/\j∈I/\Zt i j a v/\Zv I i j v/\Zside I i j v/\Zside I j i v
section
variable {D:Dag}(h:ai 14 D)(r:ar D){b:O->ℕ}(hb:cU_dom D b){p:O->Za}(hp:bA_dom D p){u:Σ _:ℕ,ℕ}(hr:aj 14 D b={u}){I:o}(d:aa 14 D=I)
include h r hb hp hr d
omit hb hr in
lemma Zdy (B:bL 14 D=0){i j a v:O}(hi:i∈I)(hj:j∈I)(g:Zt i j a v)(f:Zv I i j v)(e:Zside I i j v)(n:(af 14 D a).card<=3):∀ t,t∈Zg D (p i)->dj i t:=by
 subst I
 rcases e with ⟨m,q,t⟩|⟨rfl,z⟩
 · exact dy_dom h r B hp hi hj m g f q t n
 · exact (cT_07 h r B hp hi z).1
lemma Zlow (B:bL 14 D=0)(a i j v:O)(m:Zst I a i j v)(y:O)(cy:isClean I y)(e:¬Zallow i j a y):(af 14 D y).card<=2:=by
 subst I
 obtain⟨ca,hi,hj,g,f,f1,f2⟩:=m
 have n:=cx_dom h r hp hi hj g f
 obtain⟨-,t,-⟩:=shared_PQ_u h r hb hr ca n
 have s:=Zdy h r hp rfl B hi hj g f f1 (by omega)
 obtain⟨a1,a2,a3,a4,a5,a6⟩:=g
 have w:=Zdy h r hp rfl B hj hi ⟨a1.symm,a3,a2,a4,a6,a5⟩ (by rcases f with z|⟨z,k⟩;exact Or.inl z;exact Or.inr ⟨k,z⟩) f2 (by omega)
 apply clean_le2_of_not_u0 h r hb hr cy
 intro hy
 apply e
 simpa only[Zallow,cW] using eF_cand_dom h r hb hp hr ca hi hj ⟨a1,a2,a3,a4,a5,a6⟩ f s w y hy
lemma Zone (B:bL 14 D=0)(a i j v x y z k l:O)(m:Zst I a i j v)(n:isClean I x/\isClean I y/\k∈I/\l∈I/\¬Zallow i j a x)(o:¬Zallow i j a y)
 (u:x∉dom l/\y∉dom k/\z∉dom k)(g:ac k x=true/\ac l y=true/\ac x y=true/\ac x z=true/\cmOk l y z=true):False:=by
 obtain⟨cx,cy,hk,hl,ex⟩:=n
 have f:=Zlow h r hb hp hr d B a i j v m
 exact dl_dom h r hp x y z k l (d▸hk) (d▸hl) u g (f x cx ex) (f y cy o)
lemma Ztwo (B:bL 14 D=0)(a i j v x y z w k l:O)(m:Zst I a i j v)(n:isClean I x/\isClean I y/\isClean I z/\k∈I/\l∈I/\¬Zallow i j a x)(o:¬Zallow i j a y/\¬Zallow i j a z)
 (u:x∉dom k/\x∉dom l)(g:ac x y=true/\ac x z=true/\ac x w=true/\ac k y=true/\ac l z=true/\cmOk k y z=true/\cmOk k y w=true/\cmOk l z w=true):False:=by
 obtain⟨cx,cy,cz,hk,hl,ex⟩:=n
 have f:=Zlow h r hb hp hr d B a i j v m
 exact fR_dom h r hp x y z w k l (d▸hk) (d▸hl) u g (f x cx ex) (f y cy o.1) (f z cz o.2)
end
lemma dp {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (L:bd 14 D=(al 14 D).card+1) (c:Fin 68) (Y:3<=(bU c).card) (d:aa 14 D=bU c):False:=by
 obtain⟨b,hb⟩:=b_dom h.1 r;obtain⟨pos,hp⟩:=bQ_dom h r
 have hR1c:(aj 14 D b).card=1:=by have:=bS_dom h.1 hb;omega
 obtain⟨u0,hR1⟩:=_c1.1 hR1c
 have Z:{I:o}->aa 14 D=I->I.card=3->bL 14 D=0:=by intro I e m;have u:=aV 14 D;rw[e,m] at u;have:=bg 14 D;omega
 obtain⟨G,K,model⟩:=dMake h r hb hp hR1
 rw[d] at model
 fin_cases c
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact absurd Y V
 · exact Ztwo h r hb hp hR1 d (Z d V) 13 1 2 4 3 7 12 11 1 2 V V V V V
 · exact Ztwo h r hb hp hR1 d (Z d V) 7 1 3 0 2 12 13 8 3 1 V V V V V
 · exact ZzeroM model 7 12 1 3 0 2 3 5 9
 · exact Ztwo h r hb hp hR1 d (Z d V) 13 2 4 1 3 11 12 7 4 2 V V V V V
 · exact both24 h r hb hp hR1 (Z d V) (Zu d 2) (Zu d 4)
 · exact ZzeroM model 11 12 4 3 6 2 3 5 10
 · exact dp_17 h r (Z d V) hb hp hR1 d
 · exact ZzeroM model 9 13 5 1 6 1 4 2 10
 · exact ZzeroM model 12 13 5 2 3 2 4 1 9
 · exact Zone h r hb hp hR1 d (Z d V) 8 0 2 6 1 13 9 7 2 V V V V V
 · exact both24 h r hb hp hR1 (Z d V) (Zu d 2) (Zu d 4)
 · exact dp_22 h r (Z d V) hb hp hR1 d
 · exact Zone h r hb hp hR1 d (Z d V) 7 1 3 0 2 12 13 8 3 V V V V V
 · exact Zone h r hb hp hR1 d (Z d V) 13 1 4 2 6 9 11 8 1 V V V V V
 · exact dp_25 h r (Z d V) hb hp hR1 d
 · exact dp_26 h r (Z d V) hb hp hR1 d
 · exact dp_27 h r (Z d V) hb hp hR1 d
 · exact Zone h r hb hp hR1 d (Z d V) 12 2 3 5 6 11 8 9 3 V V V V V
 · exact both24 h r hb hp hR1 (Z d V) (Zu d 2) (Zu d 4)
 · exact ZzeroM model 7 12 1 0 3 2 3 5 9
 · exact dCore31 model
 · exact ZzeroM model 11 12 4 3 6 2 3 5 10
 · exact ZzeroM model 7 11 1 3 0 3 4 6 9
 · exact ZzeroM model 9 13 5 1 6 1 4 2 10
 · exact ZzeroM model 12 13 5 2 3 2 4 1 9
 · exact ZzeroM model 9 12 1 5 6 2 5 3 7
 · exact ZzeroM model 7 9 3 1 0 1 5 6 11
 · exact ZzeroM model 9 11 5 6 1 4 6 3 12
 · exact ZzeroM model 8 10 2 0 6 0 4 5 12
 · exact dCore40 model
 · exact ZzeroM model 10 12 4 5 0 2 5 3 11
 · exact ZzeroM model 7 11 1 3 0 3 4 6 9
 · exact ZzeroM model 9 13 5 1 6 1 4 2 10
 · exact dCore44 model
 · exact dCore45 model
 · exact dCore46 model
 · exact ZzeroM model 11 12 4 3 6 2 3 5 10
 · exact ZzeroM model 1 8 9 7 13 0 2 6 5
 · exact dCore49 model
 · exact ZzeroM model 6 11 8 9 11 3 4 6 0
 · exact ZzeroM model 0 7 8 10 7 1 3 0 2
 · exact ZzeroM model 7 11 1 0 3 3 4 6 9
 · exact ZzeroM model 9 12 1 5 6 2 5 3 7
 · exact ZzeroM model 7 9 3 0 1 1 5 6 11
 · exact ZzeroM model 7 9 3 1 0 1 5 6 11
 · exact ZzeroM model 9 11 5 6 1 4 6 3 12
 · exact ZzeroM model 9 11 1 5 6 4 6 3 7
 · exact ZzeroM model 8 10 2 0 6 0 4 5 12
 · exact ZzeroM model 8 9 2 6 0 5 6 1 12
 · exact ZzeroM model 7 9 3 1 0 1 5 6 11
 · exact ZzeroM model 11 12 4 3 6 2 3 5 10
 · exact ZzeroM model 1 8 9 7 13 0 2 6 5
 · exact ZzeroM model 7 9 3 0 1 1 5 6 11
 · exact ZzeroM model 9 11 1 5 6 4 6 3 7
 · exact ZzeroM model 7 9 3 1 0 1 5 6 11
 · exact ZzeroM model 8 9 2 0 6 5 6 1 12
 · exact ZzeroM model 7 9 3 0 1 1 5 6 11
end
def eN:o:=univ.filter λv:O=>7<=v.val
def i_:o:=univ.filter λv:O=>v.val<7
lemma aDc (x:O):(aD x).card=3:=gf x
def mW3 (Oc3 Oc5:o) (x:O) (A:o):ℕ:=if A.card=2/\A⊆aD x then 2 else if A.card=4/\aD x⊆A then 2 else if A.card=5/\aD x⊆A then 1 else if A.card=6/\x=0/\Oc5.Nonempty/\aD 0⊆A/\∀k∈Oc5,¬bX k⊆A then 1 else 0
def mW4 (a4:O->O) (k:O) (A:o):ℕ:=if A.card=2/\A⊆aD k then 2 else if A.card=3/\(∀z∈i_,A≠aD z)/\A⊆aD k∪{a4 k} then 2 else if (A.card=5\/A.card=6)/\aD k∪{a4 k}⊆A then 1 else 0
def mW5 (Oc3:o) (k:O) (A:o):ℕ:=if A=bX k then (if (0:O)∈Oc3 then 1 else 2) else if A.card=2/\A⊆aD k then 2 else if A.card=3/\(∀z∈i_,A≠aD z)/\A⊆bX k then 2 else if A.card=4/\A⊆bX k/\A≠aD k∪{8}/\A≠aD k∪{10}/\¬((0:O)∈Oc3/\aD 0⊆A) then 2 else if A.card=6/\bX k⊆A then 1 else 0
def qtOrbits:Finset (Fin 68):={30,32,33,34,36,37,42,43,47,52,54,55,57,59,60,63,64,65,67}
namespace _M3
open _0
abbrev I9:=@subset_inter
abbrev IS:=@insert_subset
abbrev SK:=@sum_insert
abbrev ER:=@inter_eq_right
abbrev EL:=@inter_eq_left
abbrev PW:=@mem_powerset
abbrev SM:=@smul_eq_mul
abbrev OD:=@of_decide_eq_true
abbrev Nt:=@not_not
abbrev U1:=@subset_union_left
abbrev BI:=@mem_biUnion
abbrev DJ:=@Disjoint
abbrev PS:=@powerset
abbrev IP:=@if_pos
abbrev IN:=@if_neg
abbrev L9:=@le_trans
abbrev CM:=@card_le_mul_card_image
abbrev SP:=@sum_pair
abbrev Sd:=@sdiff_subset
abbrev _t:=true
abbrev _f:=false
abbrev pF {t} {s:Finset t} {p:t->Prop} [DecidablePred p] {a} (h:a∈s.filter p):=_mf.1 h
abbrev pN {t} [DecidableEq t] {a b:Finset t} {x} (h:x∈a∩b):=_mn.1 h
abbrev pD {t} [DecidableEq t] {a b:Finset t} {x} (h:x∈a\b):=_md.1 h
lemma D9 {p:Prop} [Decidable p] (h:decide p=_t:=by decide +kernel):p:=OD h
lemma S9 {t} {s:Finset t} {f:t->ℕ} {a:t} (h:a∈s):f a<=∑x∈s,f x:=SL (λ_ _=>Zl _) h
lemma NS {t} {s:Finset t} {f:t->ℕ} (c:ℕ) (h:∀x∈s,c<=f x):c*s.card<=∑x∈s,f x:=by simpa[SM,mul_comm] using card_nsmul_le_sum s f c h
abbrev Q0 (D:Dag) (P M:o):=aQ 14 D P M
abbrev K1:o:={1,3}
abbrev K8:o:={8,10}
abbrev K5:o:={0,2,4,5,6}
abbrev D8 (k:O):=aD k∪{8}
abbrev D0 (k:O):=aD k∪{10}
abbrev D7 (k:O):=aD k\{7}
abbrev c5 (A C:o):=if C.card=0 then 0 else if C.card=1 then 2 else if (0:O)∈A then 3 else 4
abbrev H3 (D:Dag) (P A:o):=∀x∈A,aD x⊆P/\Q0 D P (aD x)
abbrev H4 (D:Dag) (P B:o) (a4:O->O):=∀k∈B,a4 k∈K8/\aD k∪{a4 k}⊆P/\Q0 D P (aD k∪{a4 k})/\¬Q0 D P (aD k)
abbrev H5 (D:Dag) (P C:o):=∀k∈C,bX k⊆P/\Q0 D P (bX k)/\¬Q0 D P (aD k)/\¬Q0 D P (D8 k)/\¬Q0 D P (D0 k)
abbrev HR (D:Dag) (P A B C:o) (R:Finset o):=∀M∈R,M.card=2/\Q0 D P M/\∀x∈A∪B∪C,¬M⊆aD x
abbrev Hn (D:Dag) (P:o) (k:O):=¬Q0 D P (aD k)/\¬Q0 D P (D8 k)/\¬Q0 D P (D0 k)/\¬Q0 D P (bX k)
abbrev Hn' (D:Dag) (P:o) (k:O):=(aD k⊆P->¬Q0 D P (aD k))/\(D8 k⊆P->¬Q0 D P (D8 k))/\(D0 k⊆P->¬Q0 D P (D0 k))/\(bX k⊆P->¬Q0 D P (bX k))
abbrev HB (A B C:o) (a4:O->O) (M:o):=(M.card=3/\(∀z∈i_,M≠aD z)\/(M.card=4/\(∀z∈A,¬aD z⊆M)))/\(∀k∈B,¬M⊆aD k∪{a4 k})/\(∀k∈C,¬M⊆bX k)
def B9 {t} (s:Finset t) (p:t->_d):=decide (_f∉s.val.map p)
lemma A9 {t} {s:Finset t} {p:t->_d} (h:B9 s p=_t) {a:t} (u:a∈s):p a=_t:=by by_contra b;exact(OD h:_f∉s.val.map p) (Multiset.mem_map.2 ⟨a,u,Bool.eq_false_iff.2 b⟩)
lemma K7 {D:Dag} (g:au 14 D) (h:ar D) (x:O->_d) (v:O) (b:ℕ) (c:j_ 14 D b v.val) (i:¬cN dj x) (j:cN aP (bB v x)):val D x b=_f/\val D (bB v x) b=_t:=by have d:val D x b≠val D (bB v x) b:=λe=>i (h.2 x ((mw g x _ v (dd v x) b c e).symm▸h.1 _ j));have a:=gJ g x (bB v x) (iE v x) b;cases f:val D x b;{cases l:val D (bB v x) b;{exact AB (f.trans l.symm) d};{exact⟨rfl,rfl⟩}};{exact AB (f.trans (a f).symm) d}
lemma g9 {i:O} {S:o} (h:cN dj (bB i (bM S))):(∃a∈S,dj i a)\/∃a∈S,∃b∈S,dj a b:=by obtain⟨u,v,c,e,d⟩:=h;simp only[bB,bM,BO,DE] at e d;rcases e with rfl|e<;>rcases d with rfl|d;{exact AB c (ij _)};{exact .inl ⟨v,d,c⟩};{exact .inl ⟨u,e,lL c⟩};{exact .inr ⟨u,e,v,d,c⟩}
lemma F8 (v:O):¬cN dj (cl v):=λ⟨_,_,h,c,d⟩=>by simp only[cl,DE] at c d;exact ij _ (c▸d▸h)
def kX (T:o) (f:O):=T.erase f∪(aD f).filter λa=>∀g∈T.erase f,ac g a=_f
lemma P3:∀A B C D:Finset (Fin 3),A⊆B\/B⊆A\/A⊆C\/C⊆A\/A⊆D\/D⊆A\/B⊆C\/C⊆B\/B⊆D\/D⊆B\/C⊆D\/D⊆C:=D9
def D3:=i_.image aD
def K4:Finset o:={D8 1,D0 1,D8 3,D0 3}
abbrev O9 (x:O) (A:o):=(A.card=2/\A⊆aD x)\/(A.card=3/\A∉D3)\/(A.card=4/\A∉K4)\/A.card=5\/A.card=6
abbrev v4 (a k:O) (A:o):=mW4 (λ_=>a) k A
abbrev v5 (b:_d) (k:O) (A:o):=mW5 (if b then {0} else ∅) k A
abbrev q3 (a k:O) (M:o):=M=aD k\/O9 k M/\2<=v4 a k M
abbrev q4 (k:O) (M:o):=M=aD k\/M=D8 k\/M=D0 k\/(M≠bX k/\O9 k M/\4<=v5 _f k (bX k)+v5 _f k M/\(3<=v5 _t k (bX k)+v5 _t k M\/M.card=4/\aD 0⊆M))
abbrev q5 (k:O) (A1 Z:o):=Z≠A1/\Z≠bX k/\O9 0 Z/\1<=mW3 ∅ {k} 0 Z
def jC (n:Fin 7):=i_.filter λx=>x.val<n.val
def C1 (A t u:o) (x:O):=if x∈u then mW5 t x A else max (if x=0/\x∉t then 0 else mW3 t u x A) (if x∈K1 then max (v4 8 x A) (v4 10 x A) else 0)
lemma T1a:∀x y:O,x∈i_->y∈i_->aD x=aD y->x=y:=D9
lemma T1b:∀k a z:O,k∈K1->a∈K8->z∈i_->aD z⊆aD k∪{a}->z=k:=D9
lemma T1c:∀k a:O,k∈K1->a∈K8->(aD k∪{a}).card=4/\aD k∪{a}∈K4:=D9
lemma T1d:∀k:O,k∈K1->(bX k).card=5/\aD 0⊆bX k/\(∀z:O,z∈i_->aD z⊆bX k->z=0\/z=k):=D9
lemma T1e:∀x y a b:O,x∈K1->y∈K1->a∈K8->b∈K8->aD x∪{a}=aD y∪{b}->x=y:=D9
lemma T1f:bX 1∩bX 3=aD 0/\K1⊆i_/\eN.card=7/\bX 1≠bX 3:=D9
lemma T1g:∀y:O,y∈i_->aD y⊆eN/\bX y⊆eN/\D8 y⊆eN/\D0 y⊆eN:=D9
lemma T1h:∀m:Fin 7,DJ eN (jC m)/\(jC m).card=m.val:=D9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma kC:B9 (PS eN) (λB=>B9 (univ:Finset (Fin 7)) λn=>B9 (PS {0}) λt=>B9 (PS K1) λu=>decide (∑x∈i_,C1 (B∪jC n) t u x<=2))=_t:=D9
def U2 (S:o) (p:o->o->_d):=B9 (PS (eN\S)) λx=>B9 (PS (eN\S)) λy=>!(decide (S⊂S∪x/\S⊂S∪y/\(S∪x)∩(S∪y)=S))||p (S∪x) (S∪y)
def U3 (S:o) (p:o->o->_d):=B9 (PS S) λx=>B9 (PS S) λy=>!(decide (x⊂S/\y⊂S/\x∪y=S))||p x y
lemma wS {D:Dag} (h:au 14 D) {P S:o} (a:P⊆eN) (c:2<=S.card) (q:Q0 D P S) {p1 p2:o->o->_d} (H:(U2 S p1&&U3 S p2)=_t):(∃A B,Q0 D P A/\Q0 D P B/\S⊆A/\S⊆B/\p1 A B=_t)\/(∃A B,Q0 D P A/\Q0 D P B/\A⊆S/\B⊆S/\p2 A B=_t):=by
 obtain⟨h1,h2⟩:=Bool.and_eq_true_iff.1 H;obtain⟨w,e⟩:=q;obtain⟨j,u,-,k,-,-,g⟩:=ew h P S c w e
 rcases g with ⟨x,F,G⟩|⟨-,F,G,U,-,-⟩
 ;{left;have uS {X:o} (s:S⊆X) (q':Q0 D P X):X\S∈PS (eN\S):=PW.2 λ_ h=>_md.2 ⟨a (jw q' (pD h).1),(pD h).2⟩;have T:=A9 (A9 h1 (uS F.subset (iW P _))) (uS G.subset (iW P _));rw[union_sdiff_of_subset F.subset,union_sdiff_of_subset G.subset] at T;have hp:(ag 14 D (cj D j)∩P)∩(ag 14 D (ck D j)∩P)=S:=by {rw[<-k,cB h u x];ext v;simp only[_mn];tauto};exact⟨_,_,iW P _,iW P _,F.subset,G.subset,(Bool.or_eq_true_iff.1 T).resolve_left (by simp[F,G,hp])⟩}
 ;{exact .inr ⟨_,_,iW P _,iW P _,F.subset,G.subset,(Bool.or_eq_true_iff.1 (A9 (A9 h2 (PW.2 F.subset)) (PW.2 G.subset))).resolve_left (by simp[F,G,U])⟩}
lemma T3:B9 K1 (λk=>B9 K8 λa=>let F:=aD k∪{a};U2 F (λA B=>decide (A≠B/\O9 k A/\O9 k B/\2<=v4 a k A+v4 a k B))&&U3 F (λA B=>decide (q3 a k A\/q3 a k B)))=_t:=D9
lemma T4:B9 K1 (λk=>let F:=bX k;U2 F (λA B=>decide (A≠B/\A≠F/\B≠F/\O9 k A/\O9 k B/\3<=v5 _t k F+v5 _t k A+v5 _t k B/\4<=v5 _f k F+v5 _f k A+v5 _f k B))&&U3 F (λA B=>decide (q4 k A\/q4 k B)))=_t:=D9
lemma T5:B9 K1 (λk=>B9 ((PS (bX k)).filter λA1=>A1.card=4/\aD 0⊆A1) λA1=>U2 (aD 0) (λX Y=>decide (q5 k A1 X\/q5 k A1 Y))&&U3 (aD 0) (λX Y=>decide (q5 k A1 X\/q5 k A1 Y)))=_t:=D9
lemma T2k:∀k:O,k∈K1->(D7 k).card=2/\(∀f:O,f∈D7 k->f∉aD 0)/\∀b:O,b∈K1->k≠b->DJ (D7 k) (D7 b)/\bX k∩bX b=aD 0:=D9
lemma T2d:∀c:O,c∈K5->bX c=aD c/\c∉K1/\c∈i_:=D9
lemma T2e:∀a b:O,b∈dom a->b∈eN->a∈eN:=D9
lemma T2f:∀x:O,x∈i_->x≠7/\(x∉K1->bX x=aD x)/\∀y:O,y∈eN->y∉dom x:=D9
lemma T2g:∀x y:O,x∈i_->y∈i_->x≠y->(∃a∈aD y,a∉bX x/\ac x a=_f)\/(∃a∈aD x,a∉bX y/\ac y a=_f):=D9
lemma T2h:B9 K1 (λi=>B9 (PS (bX i)) λM=>decide (¬aD i⊆M\/M=aD i\/M=D8 i\/M=D0 i\/M=bX i))=_t:=D9
lemma T6:B9 K1 (λk=>B9 (D7 k) λf=>B9 (PS (bX k)) λM=>decide (¬(f∈M/\3<=M.card)\/((M=bX k\/M=aD k\/M=D8 k\/M=D0 k\/(M.card=3/\M∉D3)\/(M.card=4/\(∀z:O,z∈i_.erase 0->¬aD z⊆M)/\(aD 0⊆M->M=aD 0∪{f})))/\∀l:O,l∈K1->l≠k->(∀a:O,a∈K8->¬M⊆aD l∪{a})/\¬M⊆bX l)))=_t:=D9
lemma sP {D:Dag} {P I:o} {pos:O->Za} (p:bA_dom D pos) (u:∀i∈I,i∈aa 14 D/\aD i⊆P) (v:∀e∈I.image pos,e∈aE 14 D (ao 14 D P)):∀e∈I.image pos,e∈aE 14 D (ao 14 D P)/\3<=(ag 14 D (aw D e)∩P).card:=λe c=>⟨v e c,by obtain⟨i,f,rfl⟩:=_mg.1 c;have:=_cl (show aD i⊆ag 14 D (aw D (pos i))∩P from λz d=>_mn.2 ⟨(p.1 i (u i f).1).2.2.2.1 z (cn.1 d),(u i f).2 d⟩);rwa[aDc] at this⟩
abbrev Q1 (I A B C:o) (n:ℕ):=let P:=eN\I;let U:=(K5\A).biUnion λk=>aD k∩P;let T:=K1.filter λk=>aD k⊆P/\k∉A/\k∉B/\k∉C;let S:=((K1.filter λk=>k∉A/\k∉B/\k∉C).biUnion λk=>D7 k∩P)\U;let J:=(i_∩I).filter λk=>aD k⊆P;let b:=(J.filter λk=>(k≠0\/dom 0⊆I)/\k∉A/\k∉B/\k∉C).card;n+2+b<=12/\2*(2*A.card+2*B.card+c5 A C+J.card+U.card+n+b)+(if (0:O)∉A then S.card else if U=∅ then 2*T.card else 0)<=2*(2*P.card+12)
def Q2 (I:o):=let P:=eN\I;B9 (PS (i_.filter λk=>aD k⊆P)) λA=>B9 (PS ((K1.filter λk=>aD k⊆P/\(D8 k⊆P\/D0 k⊆P))\A)) λB=>B9 (PS (((K1.filter λk=>bX k⊆P)\A)\B)) λC=>decide (¬Q1 I A B C (14-I.card))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma Q3:B9 qtOrbits (λc=>Q2 (bU c))=_t:=D9
end _M3
section
open _0 _M3
lemma hN_indep:∀a∈eN,∀b∈eN,¬dj a b:=λa u b v=>b3.1 ((D9:∀a∈eN,∀b∈eN,bK a b=_f) a u b v)
lemma hP_indep:∀a∈i_,∀b∈i_,¬dj a b:=λa u b v=>b3.1 ((D9:∀a∈i_,∀b∈i_,bK a b=_f) a u b v)
lemma sp_X_ok:∀k:O,k∈({1,3}:o)->let X:o:=if k=1 then {1,11,12} else {3,9,13};(∀a∈X,∀b∈X,bK a b=_f)/\(∀y:O,y∉eN\bX k\/y∈X)/\∀f∈aD k\{7},∃a∈X,ac f a=_t:=D9
lemma iI_dom {D:Dag} (h:ai 14 D) (f:ar D) {i:O} (g:dom i⊆aa 14 D):bz 14 D i.val (bH 14 D)\/∃b,bz 14 D i.val b/\2<=aF D b/\ag 14 D b=∅:=(jK (iD h i.val (by have:=i.isLt;omega))).imp_right λ⟨b,a,d⟩=>⟨b,a,d,eM_dom h.1 f g a d⟩
lemma jL_dom {D:Dag} (t:au 14 D) (g:ar D) (h:o) (l:∀a∈h,∀b∈h,¬dj a b) {i:O} (m:∀a∈h,dj i a->aP i a) (p:bz 14 D i.val (bH 14 D)):∃j s,j<D.length/\cR D j=_t/\bz 14 D i.val (aw D (j,!s))/\∀a∈h,(a∈Zg D (j,s)↔aP i a):=let ⟨j,s,u,v,_,c,d⟩:=kQ (G:=aP) t i (bH 14 D) p h (λS e q=>by by_contra n;rw[_nf] at n;rcases g9 (g.2 _ n) with ⟨a,k,f⟩|⟨a,k,b,w,r⟩;{exact q a k (m a (e k) f)};{exact l a (e k) b (e w) r}) λa _ f=>⟨g.1 _ ⟨i,a,f,dm i _,by simp[bB,bM]⟩,by by_contra n;rw[_nf,gn] at n;exact F8 a (g.2 _ n)⟩;⟨j,s,u,v,c,d⟩
lemma iJ_dom {D:Dag} (h:au 14 D) (q:ar D) (d:o) (u:∀a∈d,∀b∈d,¬dj a b) {i j:O} {w:ℕ} (v:∀a∈d,dj i a->aP i a) (l:bz 14 D i.val w) (x:j_ 14 D w j.val) (e:∃a∈d,aP j a/\¬aP i a):∃k s,k<D.length/\cR D k=_t/\14+k<=w/\bz 14 D i.val (aw D (k,!s))/\∀a∈d,(a∈Zg D (k,s)↔aP i a):=by
 classical
 let F:=d.filter λa=>¬aP i a;have y:¬cN dj (bB i (bM F)):=λr=>(g9 r).elim (λ⟨a,t,f⟩=>(pF t).2 (v a (pF t).1 f)) λ⟨a,t,b,J,z⟩=>u a (pF t).1 b (pF J).1 z
 obtain⟨a,A,m,p⟩:=e;have C:=(K7 h q _ j w x y ⟨j,a,m,dm j _,by simp only[bB,bM,F,BO,DE,_mf];exact .inr (.inr ⟨A,p⟩)⟩).1
 refine kQ (G:=aP) h i w l d (λS E K=>by by_contra r;rw[_nf] at r;rw[gJ h _ _ (λk g=>by simp only[bB,bM,BO,DE] at g⊢;exact g.imp_right λg=>_mf.2 ⟨E g,K k g⟩) w r] at C;exact _fnt C.symm) λa _ f=>let I:=K7 h q (bM {a}) i w (ds h l) (by rw[gn];exact F8 a) ⟨i,a,f,dm i _,by simp[bB,bM]⟩;⟨I.2,I.1⟩
lemma ml_dom {D:Dag} (h:ai 14 D) (H:ar D) (P:o) (I:∀a∈P,∀b∈P,¬dj a b) (J:o) (k:∀i∈J,dom i⊆aa 14 D/\aD i⊆P/\∀M,aD i⊆M->M⊆bX i∩P->¬Q0 D P M) (hd:∀i∈J,∀j∈J,i≠j->(∃a∈P\(bX i\aD i),aP j a/\¬aP i a)\/(∃a∈P\(bX j\aD j),aP i a/\¬aP j a)):J.card<=bL 14 D:=by
 classical
 let F i:=P\(bX i\aD i);have A i a (t:a∈F i) b (n:b∈F i):=I a (Sd t) b (Sd n)
 have p i a (f:a∈F i) (E:dj i a):aP i a:=by by_contra C;exact(pD f).2 (_md.2 ⟨cL.2 E,λg=>C (cn.1 g)⟩)
 have r {i} (e:i∈J) q (m:∀a∈F i,(a∈ag 14 D q↔aP i a)):False:=(k i e).2.2 (ag 14 D q∩P) (λa f=>_mn.2 ⟨(m a (_md.2 ⟨(k i e).2.1 f,λg=>(pD g).2 f⟩)).2 (cn.1 f),(k i e).2.1 f⟩) (λa f=>let ⟨G,d⟩:=pN f;_mn.2 ⟨if w:a∈bX i then w else fQ i (cn.2 ((m a (_md.2 ⟨d,λg=>w (pD g).1⟩)).1 G)),d⟩) ⟨q,rfl⟩
 choose! f y using λi (e:i∈J)=>(iI_dom h H (k i e).1).resolve_left λM=>let ⟨_,_,_,_,_,m⟩:=jL_dom h.1 H (F i) (A i) (p i) M;r e _ m
 have B:Set.InjOn f J:=λi e j N R=>by by_contra S;have go {x z} (u:x∈J) (v:z∈J) (E:f z=f x) (h':∃a∈F x,aP z a/\¬aP x a):=let ⟨_,_,_,_,_,_,m⟩:=iJ_dom h.1 H (F x) (A x) (p x) (y x u).1 (E▸ds h.1 (y z v).1) h';r u _ m;exact(hd i e j N S).elim (go e N R.symm) (go N e R)
 exact(_cij B).symm▸ph h.1 (J.image f) λb m=>let ⟨i,e,E⟩:=_mg.1 m;E▸(y i e).2
lemma qw_dom {D:Dag} (h:ai 14 D) (e:ar D) (f:bL 14 D=0) {P:o} (g:∀a∈P,∀b∈P,¬dj a b) {i:O} (hd:dom i⊆aa 14 D) (c:aD i⊆P) (heq:bX i∩P⊆aD i):Q0 D P (aD i):=by by_contra m;have:=ml_dom h e P g {i} (λj n=>(_ms.1 n)▸⟨hd,c,λM a b=>Subset.antisymm (b.trans heq) a▸m⟩) λa u b v e=>AB ((_ms.1 u).trans (_ms.1 v).symm) e;rw[_cs] at this;omega
lemma e6_dom {D:Dag} {pos:O->Za} (a:bA_dom D pos) (T J:o) (hJ:∀i∈J,i∈aa 14 D/\(∃x∈T,aP i x)/\∀x∈T,x∉dom i):J.image pos⊆aE 14 D (ao 14 D T)/\(J.image pos).card=J.card:=⟨λ_ k=>let ⟨i,b,E⟩:=_mg.1 k;let ⟨n,_,l,g,_,_,_⟩:=a.1 i (hJ i b).1;let ⟨x,d,c⟩:=(hJ i b).2.1;E▸fL.2 ⟨n,⟨x,_mn.2 ⟨g x c,d⟩⟩,λ⟨y,f⟩=>(hJ i b).2.2 y (pN f).2 (pD (l (pN f).1)).1⟩,_cij λi b j m=>a.2 (hJ i b).1 (hJ j m).1⟩
def kL_dom (T J:o):_d:=
 decide (T.card=3/\J.card=3/\((T⊆eN/\J⊆i_)\/(T⊆i_/\J⊆eN)))&&
 decide (∀v:O,(dom v∩T).Nonempty->v∈T)&&
 decide (∀i∈J,i≠0/\i≠7/\(∃a∈T,ac i a=_t)/\(∀a∈T,a∉dom i)/\∀f∈T,∃a∈kX T f,ac i a=_t)&&
 decide (∀f∈T,(∀a∈kX T f,∀b∈kX T f,bK a b=_f)/\∃a∈kX T f,ac f a=_t)&&
 decide (∀i∈J,(aD i∩T).card=2/\∀j∈J,aD j∩T⊆aD i∩T->j=i)&&
 decide (∀i∈J,∀a∈T,bK i a=_t->ac i a=_t)&&
 decide (∀i∈J,∀j∈J,i≠j->∃a∈(if T⊆eN then eN else i_)\(bX i\aD i),ac j a=_t/\ac i a=_f)&&
 decide (∀t∈T,(J.filter (λi=>ac i t=_t)).card<=2/\∀i∈J,ac i t=_f->T.erase t⊆aD i)
lemma _M3.kL {D:Dag} (h:ai 14 D) (e:ar D) {b:O->ℕ} (g:cU_dom D b) {pos:O->Za} (c:bA_dom D pos) {T J:o} (n:kL_dom T J=_t) (t:∀i∈J,i∈aa 14 D):(∀S⊆J,(∀i∈S,¬Q0 D T (aD i∩T))->S.card<=bL 14 D)/\∃w:O->Za,(∀f∈T,DJ (ag 14 D (aw D (w f))) (kX T f))/\J.image pos∪T.image w⊆aE 14 D (ao 14 D T)/\(J.image pos∪T.image w).card=J.card+T.card/\(aE 14 D (ao 14 D T)).card+(aW 14 D (ao 14 D T)).card+(al 14 D).card<=2*T.card+bd 14 D:=by
 classical
 simp only[kL_dom,BA,DE,and_assoc] at n;obtain⟨a2,a4,S,R,p,I,_,d,C,_⟩:=n;let P:o:=if T⊆eN then eN else i_
 have ⟨r,s,f⟩:T⊆P/\(∀i∈J,aD i⊆P)/\∀a∈P,∀b∈P,¬dj a b:=by rcases S with ⟨a,b⟩|⟨a,b⟩;{simp only[P,IP a];exact⟨a,λi u=>(V:∀x∈i_,aD x⊆eN) i (b u),hN_indep⟩};have j:¬T⊆eN:=λq=>by {obtain⟨v,y⟩:=_cp.1 (by omega:0<T.card);exact _dl.1 (V:DJ eN i_) (q y) (a y)};simp only[P,IN j];exact⟨a,λi u=>(V:∀x∈eN,aD x⊆i_) i (b u),hP_indep⟩
 have K:∀S⊆J,(∀i∈S,¬Q0 D T (aD i∩T))->S.card<=bL 14 D:=λS u v=>ml_dom h e P f S (λi y=>⟨by rw[dom_eq_self (p i (u y)).1 (p i (u y)).2.1];exact SS.2 (t i (u y)),s i (u y),λm a b ⟨w,z⟩=>v i y ⟨w,by ext q;rw[_mn];exact⟨λ⟨y',x⟩=>_mn.2 ⟨cn.2 ((ae i q).1 (d i (u y) q x ((cW i q).2 (cL.1 (pN (b (z▸_mn.2 ⟨y',r x⟩))).1)))),x⟩,λx=>by have m':=a (pN x).1;rw[<-z] at m';exact⟨(pN m').1,(pN x).2⟩⟩⟩⟩) λi x j y U=>let ⟨a,V,Y,N⟩:=C i (u x) j (u y) U;.inl ⟨a,V,(ae _ _).1 Y,aH.1 N⟩
 obtain⟨u,v⟩:=e6_dom c T J λi m=>⟨t i m,(p i m).2.2.1.imp λ_ x=>⟨x.1,(ae _ _).1 x.2⟩,(p i m).2.2.2.1⟩
 choose! w1 w2 A B C' E F using λf (m:f∈T)=>fm_dom h.1 e (kX T f) (λa u b v=>b3.1 ((I f m).1 a u b v)) f ((I f m).2.imp λ_ x=>⟨x.1,(ae _ _).1 x.2⟩)
 let w f:=(w1 f,w2 f);have O:Set.InjOn w T:=λf m x q z=>by by_contra N;exact _dl.1 (F f m) (CG (λa=>ag 14 D (aw D a)) z▸C' x q) (U1 (_me.2 ⟨Ne.symm N,q⟩))
 have U:DJ (J.image pos) (T.image w):=_dl.2 λx m q=>let ⟨i,z,H⟩:=_mg.1 m;let ⟨f,a,b⟩:=_mg.1 q;let ⟨c',d',e'⟩:=(p i z).2.2.2.2 f a;_dl.1 (F f a) ((CG (λy=>ag 14 D (aw D y)) (H.trans b.symm))▸(c.1 i (t i z)).2.2.2.1 c' ((ae _ _).1 e')) d'
 have x:T.image w⊆aE 14 D (ao 14 D T):=λx z=>let ⟨f,m,H⟩:=_mg.1 z;H▸fL.2 ⟨A f m,⟨f,_mn.2 ⟨C' f m,m⟩⟩,λ⟨q,N⟩=>let ⟨n1,n2⟩:=pN N;_dl.1 (F f m) (cr h.1 (A f m) (B f m) (w2 f) n1) (U1 (_me.2 ⟨λh=>E f m (h▸n1),n2⟩))⟩
 have:=co h T (by rw[oc e];simp);have:=cZ_dom h.1 g T λz _=>R z;have:=_cl (IL:T∩al 14 D⊆T);exact⟨K,w,F,US u x,by rw[_cud U,v,_cij O],by omega⟩
lemma lO_dom {D:Dag} (h:ai 14 D) (s:ar D) (L:bL 14 D<=1) {T J:o} (n:kL_dom T J=_t) (t:∀i∈J,i∈aa 14 D):(al 14 D).card+3<=bd 14 D:=by
 classical
 obtain⟨b,B⟩:=b_dom h.1 s;obtain⟨pos,g⟩:=bQ_dom h s;obtain⟨K,w,-,s1,c1,M0⟩:=kL h s B g n t
 simp only[kL_dom,BA,DE,and_assoc] at n;obtain⟨a2,a4,_,_,_,_,w',_,_,_⟩:=n
 let M i:=if Q0 D T (aD i∩T) then aD i∩T else Zg D (pos i)∩T
 have l1 i (u:i∈J):Q0 D T (M i):=by dsimp[M];split_ifs with r;{exact r};{exact⟨_,rfl⟩}
 have l2 i (u:i∈J):aD i∩T⊆M i:=by dsimp[M];split_ifs;{exact Subset.rfl};{exact λa x=>_mn.2 ⟨(g.1 i (t i u)).2.2.2.1 a (cn.1 (pN x).1),(pN x).2⟩}
 let F:=J.filter λi=>¬Q0 D T (aD i∩T);have y:=K F (_fs _ _) λ_ u=>(pF u).2
 have k:Set.InjOn M J:=λi d j m f=>by by_contra e;have q {i j} (d:i∈J) (m:j∈J) (f:M i=M j) (e:i≠j):¬Q0 D T (aD i∩T):=λr=>e ((w' i d).2 j m (by have h1:M i=aD i∩T:=IP r;rw[<-h1,f];exact l2 j m)).symm;have:=(O1 (s:=F)).2 ⟨i,_mf.2 ⟨d,q d m f e⟩,j,_mf.2 ⟨m,q m d f.symm (Ne.symm e)⟩,e⟩;omega
 have:=eZ h.1 T (J.image M) λX u=>let ⟨i,d,E⟩:=_mg.1 u;E▸⟨(w' i d).1▸_cl (l2 i d),l1 i d⟩;rw[_cij k] at this;have:=_cl s1;have:(du 14 D T).card<=(aW 14 D (ao 14 D T)).card:=_cl (_fs _ _);omega
lemma o4_dom {D:Dag} (h:ai 14 D) (H:ar D) (z:bL 14 D=0) (Z:bd 14 D<=(al 14 D).card+3) {b:O->ℕ} (hb:cU_dom D b) {pos:O->Za} (k:bA_dom D pos) {T J:o} (p:kL_dom T J=_t) (A:∀i∈J,i∈aa 14 D):(∀t∈T,(af 14 D t).card<=3/\aW 14 D (ao 14 D {t})=∅)/\∀u∈aj 14 D b,(ag 14 D u.1∩T).Nonempty:=by
 classical
 obtain⟨K,w,hw,s1,c1,M0⟩:=kL h H hb k p A;have q:=h.1;simp only[kL_dom,BA,DE,and_assoc] at p;obtain⟨a2,a8,_,V,_,_,B,_,_,r⟩:=p
 let F:=J.image λi=>aD i∩T;have n:F.card=J.card:=_cij λi d j R E=>(B j R).2 i d E.le
 have hF M (W:M∈F):M.card=2/\Q0 D T M:=let ⟨i,d,E⟩:=_mg.1 W;E▸⟨(B i d).1,by by_contra f;have:=K {i} (SS.2 d) λ_ u=>(_ms.1 u)▸f;rw[_cs] at this;omega⟩
 have:=eZ q T F λM W=>⟨(hF M W).1.ge,(hF M W).2⟩;have:(du 14 D T).card<=(aW 14 D (ao 14 D T)).card:=_cl (_fs _ _);have:=_cl s1
 have h0:J.image pos∪T.image w=aE 14 D (ao 14 D T):=_eqc s1 (by omega);have W:du 14 D T=aW 14 D (ao 14 D T):=_eqc (_fs _ _) (by omega)
 have d v (m:T⊆ag 14 D v):False:=by have:=eZ q T (insert T F) (λM W=>(_mi.1 W).elim (λE=>by subst E;exact⟨by omega,⟨v,ER.2 m⟩⟩) λW=>⟨(hF M W).1.ge,(hF M W).2⟩);rw[_cin λf=>by {have:=(hF T f).1;omega}] at this;omega
 have N:Set.InjOn (λj=>ag 14 D (14+j)∩T) (du 14 D T):=card_image_iff.1 (le_antisymm card_image_le (by have:=_cl (show F⊆(du 14 D T).image λj=>ag 14 D (14+j)∩T from λM W=>let ⟨j,s,a⟩:=lp q (hF M W).1.ge (hF M W).2;_mg.2 ⟨j,s,a⟩);omega))
 have c {t v} (y:t∈T) (m:t∈ag 14 D v):v∈ao 14 D T:=cC.2 ⟨_,_mn.2 ⟨m,y⟩⟩;have S v:(ag 14 D v∩T).card<3:=by by_contra m;exact d v (ER.1 (_eqc IR (by omega)))
 refine⟨λt y=>⟨?_,EE λj s=>?_⟩,by have:=co h T (by rw[oc H];simp);have:=d9_dom q hb T;have:=bS_dom q hb;have:=_cl (IL:T∩al 14 D⊆T);have:((al 14 D).filter λv=>(ag 14 D (b v)∩T).Nonempty).card<=(T∩al 14 D).card:=_cl λv f=>let ⟨m,u,y⟩:=pF f;_mn.2 ⟨V v ⟨u,_mn.2 ⟨(hb v m).2.2.1 (pN y).1,(pN y).2⟩⟩,m⟩;have e:((aj 14 D b).filter λu=>(ag 14 D u.1∩T).Nonempty)=aj 14 D b:=_eqc (_fs _ _) (by omega);exact λu m=>by rw[<-e] at m;exact(_mf.1 m).2⟩
 · have G:af 14 D t⊆insert (w t) ((J.filter λi=>ac i t=_t).image pos):=λe m=>by
    obtain⟨u,v,x⟩:=ak.1 m;have Y:=cY q m
    rcases _mu.1 (h0.symm▸fL.2 ⟨u,⟨t,_mn.2 ⟨v,y⟩⟩,λ⟨g,a⟩=>by obtain⟨a1,a2⟩:=pN a;have L:=(pF (W.symm▸_mf.2 ⟨MR.2 u,c a2 a1,c a2 (cr q u Y _f a1),c a2 (cr q u Y _t a1)⟩:e.1∈du 14 D T)).2;have:=_cl (show insert t (ag 14 D (14+e.1)∩T)⊆ag 14 D (aw D e)∩T from λa' f=>(_mi.1 f).elim (λE=>E▸_mn.2 ⟨v,y⟩) λf=>_mn.2 ⟨cr q u Y e.2 (pN f).1,(pN f).2⟩);rw[_cin λf=>x (pN f).1] at this;have:=S (aw D e);omega⟩) with a|a
    · obtain⟨i,j,rfl⟩:=_mg.1 a;refine mem_insert_of_mem (_mg.2 ⟨i,_mf.2 ⟨j,?_⟩,rfl⟩);by_contra f';rw[Bnt] at f';exact d (aw D (pos i)) λa' b'=>if x':a'=t then x'▸v else (k.1 i (A i j)).2.2.2.1 a' (cn.1 ((r t y).2 i j f' (_me.2 ⟨x',b'⟩)))
    · obtain⟨g,j,rfl⟩:=_mg.1 a;exact if x':g=t then x'▸mem_insert_self _ _ else AB (_dl.1 (hw g j) v (U1 (_me.2 ⟨Ne.symm x',y⟩))) id
   exact((_cl G).trans (card_insert_le _ _)).trans (by have:=card_image_le (s:=J.filter λi=>ac i t=_t) (f:=pos);have:=(r t y).1;omega)
 · rw[aW,_mf,MR] at s;obtain⟨a,u,v,x⟩:=s;rw[b7] at u v x;have M:j∈du 14 D T:=W.symm▸_mf.2 ⟨MR.2 a,c y u,c y v,c y x⟩;have K':=(pF M).2
   obtain⟨j',-,-,X,L,-,U⟩:=ew q T _ K' (14+j) rfl;obtain rfl:j'=j:=N (_mf.2 ⟨L,X.symm▸K'⟩) M X
   rcases U with ⟨-,U,-⟩|⟨-,U,Y,O,-,-⟩;{have:=CL U;have:=S (cj D j');omega}
   have h1 {w'} (hw:t∈ag 14 D w') (h2:(ag 14 D w'∩T).card<(ag 14 D (14+j')∩T).card):({t}:o)=ag 14 D w'∩T:=_eqc (SS.2 (_mn.2 ⟨hw,y⟩)) (by have:=S (14+j');rw[_cs];omega);rw[<-O,<-h1 v (CL U),<-h1 x (CL Y),union_self,_cs] at K';omega
lemma gI {t:Type} [DecidableEq t] {R A B C D:Finset t} (m:R.card=3) (g:A⊆R) (i:B⊆R) (j:C⊆R) (k:D⊆R):A⊆B\/B⊆A\/A⊆C\/C⊆A\/A⊆D\/D⊆A\/B⊆C\/C⊆B\/B⊆D\/D⊆B\/C⊆D\/D⊆C:=by
 classical
 obtain⟨p,q,n,-,-,-,d⟩:=card_eq_three.1 m;let f:Fin 3->t:=![p,q,n];let b (S:Finset t):=univ.filter λu:Fin 3=>f u∈S
 have a {X Y:Finset t} (l:X⊆R) (c:b X⊆b Y):X⊆Y:=λx u=>by have h (v:Fin 3) (e:f v=x):x∈Y:=e▸(pF (c (_mf.2 ⟨_mv v,e.symm▸u⟩))).2;have e:=l u;rw[d,_mi,_mi,_ms] at e;rcases e with rfl|rfl|rfl;{exact h 0 rfl};{exact h 1 rfl};{exact h 2 rfl}
 rcases P3 (b A) (b B) (b C) (b D) with h|h|h|h|h|h|h|h|h|h|h|h<;>repeat' first | (left;exact a (by assumption) h) | right | exact a (by assumption) h
lemma bX_eq_aD_810:∀k:O,k∈({1,3}:o)->bX k=aD k∪{8,10}:=D9
lemma mI_plus_col {Oc3 Oc4 Oc5:o} {a4:O->O} {B0:Finset o} (p3:Oc3⊆i_) (p:Oc4⊆K1) (q:Oc5⊆K1) (u:DJ Oc3 Oc4) (v:DJ Oc3 Oc5) (z:DJ Oc4 Oc5) (k:∀k∈Oc4,a4 k∈K8) (r:∀M∈B0,HB Oc3 Oc4 Oc5 a4 M) {A:o} (s:(A.card=2/\∃x∈Oc3∪Oc4∪Oc5,A⊆aD x)\/(A.card=3/\∀z∈i_,A≠aD z)\/A.card=4\/A.card=5\/A.card=6):∑x∈Oc3,mW3 Oc3 Oc5 x A+∑k∈Oc4,mW4 a4 k A+∑k∈Oc5,mW5 Oc3 k A+(if A∈B0 then 2 else 0)<=2:=by
 classical
 by_cases a:A∈B0
 ;{rw[IP a];obtain⟨d,B,l⟩:=r A a;rw[sum_eq_zero λx b=>by unfold mW3;rcases d with ⟨c,-⟩|⟨c,e⟩;{simp[c]};{simp[c,e x b]},sum_eq_zero λj m=>by unfold mW4;rcases d with ⟨c,-⟩|⟨c,-⟩;{simp only[c,Nat.reduceEqDiff,false_and,↓reduceIte,B j m,and_false,or_self]};{simp[c]},sum_eq_zero λj m=>by unfold mW5;have g:A≠bX j:=λe=>by {subst e;have:=(T1d j (q m)).1;rcases d with ⟨c,-⟩|⟨c,-⟩<;>omega};rcases d with ⟨c,-⟩|⟨c,-⟩<;>simp[g,c,l j m]];decide}
 rw[IN a,add_zero];let t:=Oc3∩{0};let F:=C1 A t Oc5
 have b3:∑x∈Oc3,mW3 Oc3 Oc5 x A<=∑x∈Oc3,F x:=sum_le_sum λx b=>by have c:¬(x=0/\x∉t):=λ⟨e,n⟩=>n (_mn.2 ⟨b,_ms.2 e⟩);simp only[F,C1,IN (_dl.1 v b),IN c];exact le_max_left _ _
 have b4:∑x∈Oc4,mW4 a4 x A<=∑x∈Oc4,F x:=sum_le_sum λx b=>by simp only[F,C1,IN (_dl.1 z b),IP (p b)];refine L9 ?_ (le_max_right _ _);rcases _mi.1 (k x b) with e|e;{simp only[mW4,v4,e];exact le_max_left _ _};{simp only[mW4,v4,_ms.1 e];exact le_max_right _ _}
 have C:∑x∈Oc5,mW5 Oc3 x A<=∑x∈Oc5,F x:=sum_le_sum λx b=>by simp only[F,C1,IP b,t,mW5,_mn,_mss,and_true,le_refl]
 have j:=SU (f:=F) (US (US p3 (p.trans T1f.2.1)) (q.trans T1f.2.1));rw[sum_union (disjoint_union_left.2 ⟨v,z⟩),sum_union u] at j
 let B:=A∩eN;have hB:B⊆eN:=IR;have:B.card<=A.card:=_cl IL;let n:Fin 7:=⟨A.card-B.card,by rcases s with h|h|h|h|h<;>omega⟩;obtain⟨dn,kn⟩:=T1h n;let C':=B∪jC n
 have cA:A.card=C'.card:=by dsimp[C'];rw[_cud (disjoint_of_subset_left hB dn),kn];dsimp[n];omega
 have hE:A∩eN=C'∩eN:=by dsimp[C'];rw[union_inter_distrib_right,EL.2 hB,disjoint_iff_inter_eq_empty.1 dn.symm,union_empty]
 have hF:∑x∈i_,F x=∑x∈i_,C1 C' t Oc5 x:=SC rfl λx hx=>by
  have E {S} (s:S⊆eN):A∩S=C'∩S:=by simpa only[inter_assoc,ER.2 s] using CG (λY:o=>Y∩S) hE
  have l {S} (s:S⊆eN):S⊆A↔S⊆C':=by rw[<-ER,E s,ER]
  have r' {S} (s:S⊆eN):A⊆S↔C'⊆S:=by have q' (P:o):P⊆S↔P.card<=(P∩S).card:=by {rw[eq_iff_card_le_of_subset IL,EL]};rw[q' A,q' _,E s,cA]
  have e' {S} (s:S⊆eN):A=S↔C'=S:=by rw[Subset.antisymm_iff,r' s,l s,<-Subset.antisymm_iff]
  obtain⟨d1,j1,p1,q1⟩:=T1g x hx;simp only[F,C1,mW3,v4,mW4,mW5,cA,l d1,l (T1g 0 V).1,l j1,l p1,l q1,r' d1,r' j1,r' p1,r' q1,e' j1,e' p1,e' q1,forall₂_congr λz a=>not_congr (e' (T1g z a).1),forall₂_congr λz a=>not_congr (l (T1g z (T1f.2.1 (q a))).2.1),ne_eq]
 have:=OD (A9 (A9 (A9 (A9 kC (PW.2 hB)) (_mv n)) (PW.2 (IR:t⊆{0}))) (PW.2 q));dsimp[C',t] at hF;omega
lemma mI_plus {D:Dag} (h:au 14 D) {P Oc3 Oc4 Oc5:o} {a4:O->O} {R2 B0 B1:Finset o} (a:P⊆eN) (b:Oc3⊆i_) (c:Oc4⊆K1) (e:Oc5⊆K1) (f:DJ Oc3 Oc4) (j:DJ Oc3 Oc5) (l:DJ Oc4 Oc5) (m:H3 D P Oc3) (n:H4 D P Oc4 a4) (p5:H5 D P Oc5) (q:HR D P Oc3 Oc4 Oc5 R2) (r:∀M∈B0,Q0 D P M/\M∉Oc3.image aD/\M∉Oc4.image (λk=>aD k∪{a4 k})/\M∉R2/\HB Oc3 Oc4 Oc5 a4 M) (t:∀M∈B1,Q0 D P M/\M.card=4/\aD 0⊆M/\(∀k∈Oc4,M≠aD k∪{a4 k})/\(∀k∈Oc5,¬M⊆bX k)) (u:B1.Nonempty->(0:O)∈Oc3):2*Oc3.card+2*Oc4.card+c5 Oc3 Oc5+R2.card+B0.card+(if B1.card=0 then 0 else if Oc5.card=1/\(0:O)∈Oc3 then (if 2<=B1.card then 1 else 0) else B1.card-1)<=(du 14 D P).card:=by
 classical
 let L3:=Oc3.image aD;let L4:=Oc4.image λk=>aD k∪{a4 k};let Q:=(PS P).filter λA=>2<=A.card/\Q0 D P A
 let d:=Q.filter λA=>A∉L3/\A∉L4/\A∉R2/\((A.card=2/\∃x∈Oc3∪Oc4∪Oc5,A⊆aD x)\/(A.card=3/\∀z∈i_,A≠aD z)\/A.card=4\/A.card=5\/A.card=6)
 have fc k (i:k∈Oc4):(aD k∪{a4 k}).card=4:=(T1c k _ (c i) (n k i).1).1;have bc k (i:k∈Oc5):(bX k).card=5:=(T1d k (e i)).1
 have x3:L3.card=Oc3.card:=_cij λx v y w=>T1a x y (b v) (b w);have x2:L4.card=Oc4.card:=_cij λx v y w=>T1e x y _ _ (c v) (c w) (n x v).1 (n y w).1
 have c3 M (y:M∈L3):M.card=3:=let ⟨x,_,E⟩:=_mg.1 y;E▸aDc x;have c4 M (y:M∈L4):M.card=4:=let ⟨k,i,E⟩:=_mg.1 y;E▸fc k i
 have inQ {M} (v:Q0 D P M) (c':2<=M.card):M∈Q:=_mf.2 ⟨PW.2 (jw v),c',v⟩
 have n3' {M} (h':M.card≠3):M∉L3:=λu=>h' (c3 M u);have n4' {M} (h':M.card≠4):M∉L4:=λu=>h' (c4 M u);have n2' {M} (h':M.card≠2):M∉R2:=λu=>h' (q M u).1
 have dm {x:O} {A:o} (hx:x∈Oc3∪Oc4∪Oc5) (v:Q0 D P A) (H:O9 x A):A∈d:=by
  rcases H with ⟨c',s'⟩|⟨c',h'⟩|⟨c',h'⟩|c'|c'
  ;{exact _mf.2 ⟨inQ v c'.ge,n3' (c'▸V),n4' (c'▸V),λu=>(q A u).2.2 x hx s',.inl ⟨c',x,hx,s'⟩⟩}
  ;{exact _mf.2 ⟨inQ v (c'▸V),λu=>let ⟨z,w,E⟩:=_mg.1 u;h' (_mg.2 ⟨z,b w,E⟩),n4' (c'▸V),n2' (c'▸V),.inr (.inl ⟨c',λz w e=>h' (_mg.2 ⟨z,w,e.symm⟩)⟩)⟩}
  ;{exact _mf.2 ⟨inQ v (c'▸V),n3' (c'▸V),λu=>let ⟨k,i,E⟩:=_mg.1 u;h' (E▸(T1c k _ (c i) (n k i).1).2),n2' (c'▸V),.inr (.inr (.inl c'))⟩}
  ;{exact _mf.2 ⟨inQ v (c'▸V),n3' (c'▸V),n4' (c'▸V),n2' (c'▸V),.inr (.inr (.inr (.inl c')))⟩}
  ;{exact _mf.2 ⟨inQ v (c'▸V),n3' (c'▸V),n4' (c'▸V),n2' (c'▸V),.inr (.inr (.inr (.inr c')))⟩}
 have S {A B:o} (v:A∈d) (w:B∈d):({A,B}:Finset o)⊆d:=IS v (SS.2 w)
 have s8:L3.card+L4.card+R2.card+d.card<=(du 14 D P).card:=by
  have dj {X Y:Finset o} {a b:ℕ} (h1:∀M∈X,M.card=a) (h2:∀M∈Y,M.card=b) (ne:a≠b):DJ X Y:=_dl.2 λM u v=>ne ((h1 M u).symm.trans (h2 M v))
  have sub:L3∪L4∪R2⊆Q:=US (US (λM v=>let ⟨x,w,E⟩:=_mg.1 v;E▸inQ (m x w).2 (aDc x▸V)) (λM v=>let ⟨k,i,E⟩:=_mg.1 v;E▸inQ (n k i).2.2.1 (fc k i▸V))) λM v=>inQ (q M v).2.1 (q M v).1.ge
  have:=eZ h P Q λM v=>(pF v).2;have:=_cl (show d⊆Q\(L3∪L4∪R2) from λM v=>let ⟨q',h1,h2,h3,_⟩:=pF v;_md.2 ⟨q',λu=>(_mu.1 u).elim (λu=>(_mu.1 u).elim h1 h2) h3⟩);have:=CS sub
  rw[_cud (disjoint_union_left.2 ⟨dj c3 (λM v=>(q M v).1) V,dj c4 (λM v=>(q M v).1) V⟩),_cud (dj c3 c4 V)] at this;omega
 let J:=mW3 Oc3 Oc5;let w4:=mW4 a4;let w5:=mW5 Oc3;let s3 x:=∑A∈d,J x A;let s5 k:=∑A∈d,w5 k A
 have p7 A (F:A∈d):=mI_plus_col b c e f j l (λk i=>(n k i).1) (λM v=>(r M v).2.2.2.2) (pF F).2.2.2.2
 have b3 x (v:x∈Oc3):2<=s3 x:=by rcases k5 h ((_cl a).trans T1f.2.2.1.le) (aDc x) (m x v).2 with ⟨A,z,y,s⟩|⟨A,z,y,s⟩|⟨A,B,g,z,w,y,k,s,p,-⟩;{exact L9 (by simp[J,mW3,y,s]) (S9 (dm (U1 (U1 v)) z (.inl ⟨y,s⟩)))};{exact L9 (by simp[J,mW3,y,s]) (S9 (_mf.2 ⟨inQ z (y▸V),n3' (y▸V),λu=>let ⟨k,i,E⟩:=_mg.1 u;_dl.1 f v (T1b k _ x (c i) (n k i).1 (b v) (E▸s)▸i),n2' (y▸V),.inr (.inr (.inl y))⟩))};{refine L9 ?_ (SU (S (dm (U1 (U1 v)) z (.inr (.inr (.inr (.inl y))))) (dm (U1 (U1 v)) w (.inr (.inr (.inr (.inl k)))))));rw[SP g];simp[J,mW3,y,k,s,p]}
 have m3 k (i:k∈Oc4):2<=∑A∈d,w4 k A:=by obtain⟨v,_,w,g⟩:=n k i;have hk:k∈Oc3∪Oc4∪Oc5:=U1 (_mu.2 (.inr i));rcases wS h a (fc k i▸V) w (A9 (A9 T3 (c i)) v) with ⟨A,B,N,K,-,-,T⟩|⟨A,B,N,K,-,-,T⟩;{obtain⟨d1,oA,oB,hW⟩:=OD T;exact L9 hW (by rw[<-SP d1];exact SU (S (dm hk N oA) (dm hk K oB)))};{have go {M} (q':Q0 D P M) (H:q3 (a4 k) k M):=H.elim (λE=>AB (E▸q') g) λ⟨o',h'⟩=>L9 h' (S9 (dm hk q' o'));exact(OD T).elim (go N) (go K)}
 have E k (i:k∈Oc5):bX k∈d:=dm (_mu.2 (.inr i)) (p5 k i).2.1 (.inr (.inr (.inr (.inl (bc k i)))))
 have g2 k (i:k∈Oc5):J 0 (bX k)=1:=by simp[J,mW3,bc k i,(T1d k (e i)).2.1]
 have d3 {A:o} (z:A.card=4) (s:aD 0⊆A):J 0 A=2:=by simp[J,mW3,z,s]
 have g1 (y:(0:O)∈Oc3) k (i:k∈Oc5):1<=s5 k:=L9 (by simp[w5,mW5,y]) (S9 (E k i))
 have b' {A:o} (z:A.card=4) k (i:k∈Oc5):A≠bX k:=λd=>AB (z.symm.trans (d▸bc k i)) V
 have g k (i:k∈Oc5):((0:O)∉Oc3->4<=s5 k)/\((0:O)∈Oc3->3<=s5 k\/∃A∈d,A.card=4/\aD 0⊆A/\A⊆bX k):=by
  obtain⟨_,v,g,x,y⟩:=p5 k i;have hk:k∈Oc3∪Oc4∪Oc5:=_mu.2 (.inr i)
  have wt (h0:(0:O)∈Oc3) M:w5 k M=v5 _t k M:=by simp[w5,v5,mW5,h0]
  have wf (h0:(0:O)∉Oc3) M:w5 k M=v5 _f k M:=by simp[w5,v5,mW5,h0]
  rcases wS h a (bc k i▸V) v (A9 T4 (e i)) with ⟨A,B,N,K,-,-,T⟩|⟨A,B,N,K,sA,sB,T⟩
  ;{obtain⟨d1,d2,d3',oA,oB,ht,hf⟩:=OD T;have L:w5 k (bX k)+w5 k A+w5 k B<=s5 k:=by {have:=SU (IS (E k i) (S (dm hk N oA) (dm hk K oB))) (f:=w5 k);rw[SK (by simp[d2.symm,d3'.symm]),SP d1] at this;dsimp[s5];omega}
    exact⟨λh0=>by simp only[wf h0] at L;omega,λh0=>.inl (by simp only[wt h0] at L;omega)⟩}
  ;{have go {M} (q':Q0 D P M) (s:M⊆bX k) (H:q4 k M):((0:O)∉Oc3->4<=s5 k)/\((0:O)∈Oc3->3<=s5 k\/∃A∈d,A.card=4/\aD 0⊆A/\A⊆bX k):=by
     rcases H with rfl|rfl|rfl|⟨ne,oM,hf,ht⟩;{exact AB q' g};{exact AB q' x};{exact AB q' y}
     have L:w5 k (bX k)+w5 k M<=s5 k:=by {have:=SU (S (E k i) (dm hk q' oM)) (f:=w5 k);rwa[SP ne.symm] at this}
     exact⟨λh0=>by simp only[wf h0] at L;omega,λh0=>ht.imp (λh'=>by simp only[wt h0] at L;omega) λ⟨c',s0⟩=>⟨M,dm hk q' oM,c',s0,s⟩⟩
    exact(OD T).elim (go N sA) (go K sB)}
 have g4:B0⊆d:=λM v=>let ⟨z,x,y,w,s,_,_⟩:=r M v;_mf.2 ⟨inQ z (by rcases s with ⟨c',-⟩|⟨c',-⟩<;>omega),x,y,w,s.elim (λs=>.inr (.inl s)) λs=>.inr (.inr (.inl s.1))⟩
 have b2:B1⊆d:=λM v=>let ⟨z,y,_,w,_⟩:=t M v;_mf.2 ⟨inQ z (y▸V),n3' (y▸V),λu=>let ⟨k,i,E⟩:=_mg.1 u;w k i E.symm,n2' (y▸V),.inr (.inr (.inl y))⟩
 have k7 {k} (i:k∈Oc5):bX k∉B1:=λv=>b' (t _ v).2.1 k i rfl;have n3 {k A} (i:k∈Oc5) (s:A⊆bX k):A∉B1:=λv=>(t A v).2.2.2.2 k i s
 have p9:∑x∈Oc3,s3 x+∑k∈Oc4,∑A∈d,w4 k A+∑k∈Oc5,s5 k+2*B0.card<=2*d.card:=by have L:=sum_le_card_nsmul d _ 2 p7;simp only[SM,sum_add_distrib] at L;rw[sum_comm (s:=d) (t:=Oc3),sum_comm (s:=d) (t:=Oc4),sum_comm (s:=d) (t:=Oc5),show ∑A∈d,(if A∈B0 then 2 else 0)=2*B0.card by rw[<-sum_filter,filter_mem_eq_inter,ER.2 g4,sum_const,SM,mul_comm],mul_comm d.card 2] at L;exact L
 have:=NS 2 m3;have:=NS 2 b3;have a1:∑A∈B1,J 0 A=2*B1.card:=by rw[SC rfl λA F=>d3 (t A F).2.1 (t A F).2.2.1,sum_const,SM,mul_comm]
 have m6:2*B1.card<=s3 0:=a1▸SU b2;have:Oc5.card<=2:=(_cl e).trans (by rw[_c2 V])
 dsimp[c5];by_cases h0:(0:O)∈Oc3
 ;{have:=CE h0▸NS 2 λx v=>b3 x (erase_subset _ _ v);have:∑x∈Oc3,s3 x=s3 0+∑x∈Oc3.erase 0,s3 x:=(add_sum_erase Oc3 _ h0).symm
   by_cases z:Oc5.card=0;{have:=b3 0 h0;split_ifs<;>omega}
   by_cases y:Oc5.card=1
   ;{obtain⟨k,v⟩:=_c1.1 y;have i:k∈Oc5:=v▸_mss k;have:∑x∈Oc5,s5 x=s5 k:=by rw[v,sum_singleton]
     have c1:(if 2<=B1.card then 7 else 5)<=s3 0+s5 k:=by
      rcases (g k i).2 h0 with c'|⟨A,z',H,a',G⟩;{have:=b3 0 h0;split_ifs<;>omega}
      have:=g1 h0 k i;split_ifs
      ;{have L:=SU (IS z' (IS (E k i) b2)) (f:=J 0);rw[SK (by simp[b' H k i,n3 i G]),SK (k7 i),a1,d3 H a',g2 k i] at L;dsimp[s3];omega}
      ;{have mk {Z} (q':Q0 D P Z) (H':q5 k A Z):5<=s3 0+s5 k:=by {have L:=SU (IS z' (S (E k i) (dm (U1 (U1 h0)) q' H'.2.2.1))) (f:=J 0);rw[SK (by simp[b' H k i,H'.1.symm]),SP H'.2.1.symm,d3 H a',g2 k i,show J 0 Z=mW3 ∅ {k} 0 Z by simp[J,mW3,v]] at L;dsimp[s3];omega};rcases wS h a (aDc 0▸V) (m 0 h0).2 (A9 (A9 T5 (e i)) (_mf.2 ⟨PW.2 G,H,a'⟩)) with ⟨X,Y,M,N,-,-,T⟩|⟨X,Y,M,N,-,-,T⟩<;>exact(OD T).elim (mk M) (mk N)}
     simp only[y,h0,and_self,↓reduceIte];split_ifs at c1⊢<;>omega}
   ;{have b1:Oc5=K1:=_eqc e (by rw[_c2 V];omega);have h1:1∈Oc5:=b1▸V;have h3:3∈Oc5:=b1▸V;have:∑k∈Oc5,s5 k=s5 1+s5 3:=by rw[b1,SP V]
     have c1:8<=s3 0+s5 1+s5 3/\6+2*B1.card<=s3 0+s5 1+s5 3:=by
      have:=g1 h0 1 h1;have:=g1 h0 3 h3;let T:=insert (bX 1) (insert (bX 3) B1);have ts:T⊆d:=IS (E 1 h1) (IS (E 3 h3) b2)
      have tv:∑A∈T,J 0 A=2+2*B1.card:=by dsimp[T];rw[SK (by simp[T1f.2.2.2,k7 h1]),SK (k7 h3),g2 1 h1,g2 3 h3,a1];omega
      have nt {k A} (i:k∈Oc5) (z:A.card=4) (s:A⊆bX k):A∉T:=by simp[T,b' z 1 h1,b' z 3 h3,n3 i s]
      have e6 {k A} (i:k∈Oc5) (v:A∈d) (z:A.card=4) (s:aD 0⊆A) (s':A⊆bX k):4+2*B1.card<=s3 0:=by have L:=SU (IS v ts) (f:=J 0);rw[SK (nt i z s'),d3 z s,tv] at L;dsimp[s3];omega
      rcases (g 1 h1).2 h0 with a'|⟨A,z',H,v,G⟩<;>rcases (g 3 h3).2 h0 with b'|⟨B,w',M,y',F⟩;{have:=b3 0 h0;omega};{have:=e6 h3 w' M y' F;omega};{have:=e6 h1 z' H v G;omega}
      have L:=SU (IS z' (IS w' ts)) (f:=J 0);rw[SK (by simp[show A≠B from λd=>by {have:=_cl (I9 G (d▸F));rw[T1f.1,aDc 0] at this;omega},nt h1 H G]),SK (nt h3 M F),d3 H v,d3 M y',tv] at L;dsimp[s3];omega
     split_ifs<;>omega}}
 ;{have:B1.card=0:=C0.2 (N0.1 λv=>h0 (u v));have:=NS (s:=Oc5) (f:=s5) 4 λk i=>(g k i).1 h0;split_ifs<;>omega}
lemma _M3.sR {D:Dag} (h:au 14 D) (d:ar D) {P A B C S:o} {a4:O->O} {R:Finset o} (a:P⊆eN) (b:A⊆i_) (c:B⊆K1) (e:C⊆K1) (f:DJ A B) (g:DJ A C) (j:DJ B C) (k:H3 D P A) (l:H4 D P B a4) (m:H5 D P C) (q:HR D P A B C R) (hs:∀f∈S,∃k∈K1,f∈D7 k∩P/\k∉A/\k∉B/\k∉C/\Hn' D P k):∃(K:O->O) (F:O->Za) (u:o) (b0 b1:ℕ),u⊆S/\S.card<=u.card+2*b0+b1/\(∀f∈u,dG 14 D P (bX (K f)) f (F f))/\(0<b1->S.Nonempty/\(0:O)∈A)/\2*A.card+2*B.card+c5 A C+R.card+b0+(if b1=0 then 0 else if C.card=1/\(0:O)∈A then (if 2<=b1 then 1 else 0) else b1-1)<=(du 14 D P).card:=by
 classical
 choose! K Z using hs
 choose! F1 F2 A1 A2 A3 A4 A5 using λf (v:f∈S)=>let ⟨m,_,g⟩:=sp_X_ok _ (Z f v).1;let ⟨a',q',y⟩:=g f (pN (Z f v).2.1).1;fm_dom h d _ (λa u b v=>b3.1 (m a u b v)) f ⟨a',q',(ae _ _).1 y⟩
 let F f:=(F1 f,F2 f);let Mf f:=ag 14 D (aw D (F f))∩P
 have sb f (v:f∈S):Mf f⊆bX (K f):=λo' i'=>by by_contra y';exact _dl.1 (A5 f v) (pN i').1 (((sp_X_ok _ (Z f v).1).2.1 o').resolve_left (Nt.2 (_md.2 ⟨a (pN i').2,y'⟩)))
 let u:=S.filter λf=>(Mf f).card<=2;let n:=S\u;let p0 f:=(0:O)∈A/\(Mf f).card=4/\aD 0⊆Mf f;let w:=n.filter λf=>¬p0 f;let l':=n.filter p0;let B0:=w.image Mf;let B1:=l'.image Mf
 have spM x (v:x∈n):(((Mf x).card=3/\Mf x∉D3)\/((Mf x).card=4/\(∀z∈i_.erase 0,¬aD z⊆Mf x)/\(aD 0⊆Mf x->Mf x=aD 0∪{x})))/\(∀y∈B,¬Mf x⊆aD y∪{a4 y})/\∀y∈C,¬Mf x⊆bX y:=by
  have Y:=(pD v).1;obtain⟨hk,hf,_,nk,nl,h1,h2,h3,h4⟩:=Z x Y;have hq:Q0 D P (Mf x):=iW P _
  obtain⟨H,N⟩:=(OD (A9 (A9 (A9 T6 hk) (pN hf).1) (PW.2 (sb x Y)))).resolve_left (Nt.2 ⟨_mn.2 ⟨A3 x Y,(pN hf).2⟩,Nat.lt_of_not_ge λe'=>(pD v).2 (_mf.2 ⟨Y,e'⟩)⟩)
  refine⟨?_,λy o'=>(N y (c o') λe'=>nk (e'▸o')).1 (a4 y) (l y o').1,λy o'=>(N y (e o') λe'=>nl (e'▸o')).2⟩
  rcases H with e'|e'|e'|e'|z|z;{exact AB (e'▸hq) (h4 (jw (e'▸hq)))};{exact AB (e'▸hq) (h1 (jw (e'▸hq)))};{exact AB (e'▸hq) (h2 (jw (e'▸hq)))};{exact AB (e'▸hq) (h3 (jw (e'▸hq)))};{exact .inl z};{exact .inr z}
 have wf:w.card<=2*B0.card:=CM _ 2 λX v=>by obtain⟨x,y,rfl⟩:=_mg.1 v;have Y:=(pD (pF y).1).1;rw[<-(T2k (K x) (Z x Y).1).1];exact _cl λi z=>by obtain⟨o',e'⟩:=pF z;have hi:=(pD (pF o').1).1;have t:=Z i hi;have q':K i=K x:=by {by_contra m';have z':=I9 (e'▸sb i hi) (sb x Y);rw[((T2k _ t.1).2.2 _ (Z x Y).1 m').2] at z';exact(T2k _ t.1).2.1 i (pN t.2.1).1 (z' (e'▸_mn.2 ⟨A3 i hi,(pN t.2.1).2⟩))};rw[<-q'];exact(pN t.2.1).1
 have lv x (v:x∈l'):Mf x=aD 0∪{x}:=(spM x (pF v).1).1.elim (λ⟨e',_⟩=>by have:=(pF v).2.2.1;omega) λ⟨_,_,e'⟩=>e' (pF v).2.2.2
 have lc:l'.card=B1.card:=(_cij λx u' y v' e'=>by rcases _mu.1 (show x∈aD 0∪{y} by rw[<-lv y v',<-e',lv x u'];simp) with z|z;{have t:=Z x (pD (pF u').1).1;exact AB z ((T2k _ t.1).2.1 x (pN t.2.1).1)};{exact _ms.1 z}).symm
 have:=card_filter_add_card_filter_not (s:=n) p0;have:=CS (show u⊆S from _fs _ _)
 have hm:=mI_plus h a b c e f g j k l m (R2:=R) (B0:=B0) (B1:=B1) q
  (λM v=>by obtain⟨x,y,rfl⟩:=_mg.1 v;obtain⟨H,y1,y2⟩:=spM x (pF y).1;have s:(Mf x).card=3/\(∀z∈i_,Mf x≠aD z)\/((Mf x).card=4/\∀z∈A,¬aD z⊆Mf x):=H.imp (λ⟨c',nd⟩=>⟨c',λz w e'=>nd (_mg.2 ⟨z,w,e'.symm⟩)⟩) λ⟨c',h4,_⟩=>⟨c',λz z'=>if h0:z=0 then h0▸λs0=>(pF y).2 ⟨h0▸z',c',s0⟩ else h4 z (_me.2 ⟨h0,b z'⟩)⟩;exact⟨iW P _,λz=>let ⟨i,o',e'⟩:=_mg.1 z;s.elim (λ⟨_,g'⟩=>g' i (b o') e'.symm) λ⟨m',_⟩=>by rw[<-e',aDc] at m';omega,λz=>let ⟨i,o',e'⟩:=_mg.1 z;y1 i o' (e'▸Subset.rfl),λz=>by have:=(q _ z).1;rcases s with ⟨m',-⟩|⟨m',-⟩<;>omega,s,y1,y2⟩)
  (λM v=>let ⟨x,y,E⟩:=_mg.1 v;let ⟨_,y1,y2⟩:=spM x (pF y).1;E▸⟨iW P _,(pF y).2.2.1,(pF y).2.2.2,λi o' e'=>y1 i o' (e'▸Subset.rfl),y2⟩)
  λ⟨M,v⟩=>let ⟨x,y,_⟩:=_mg.1 v;(pF y).2.1
 exact⟨K,F,u,B0.card,B1.card,_fs _ _,by dsimp[w,l',n] at *;omega,λx v=>let u':=(pF v).1;⟨A1 x u',A2 x u',(pN (Z x u').2.1).2,A3 x u',A4 x u',sb x u',(pF v).2⟩,λz=>let ⟨x,v⟩:=_cp.1 (lc▸z);⟨⟨x,(pD (pF v).1).1⟩,(pF v).2.1⟩,hm⟩
lemma qt_sp0_aux {D:Dag} (h:ai 14 D) (d:ar D) (z:ap 14 D<=12) {P Oc3 Oc4 Oc5 Iin sp0:o} {a4:O->O} {pos:O->Za} (a:P⊆eN) (b:Oc3⊆i_) (c:Oc4⊆K1) (e:Oc5⊆K1) (f:DJ Oc3 Oc4) (g:DJ Oc3 Oc5) (j:DJ Oc4 Oc5) (k:H3 D P Oc3) (l:H4 D P Oc4 a4) (m:H5 D P Oc5) (n:∀k∈sp0,k∈K1/\aD k⊆P/\k∉Oc3/\k∉Oc4/\k∉Oc5/\Hn D P k) (_:(0:O)∈Oc3) (p:bA_dom D pos) (q:∀i∈Iin,i∈aa 14 D/\aD i⊆P) (r:∀e∈Iin.image pos,e∈aE 14 D (ao 14 D P)) (s:(Iin.image pos).card=Iin.card) (t:(aE 14 D (ao 14 D P)).card+(aW 14 D (ao 14 D P)).card=P.card+bn D (ao 14 D P)) (v:bn D (ao 14 D P)+(al 14 D).card<=P.card+bd 14 D):2*Oc3.card+2*Oc4.card+c5 Oc3 Oc5+Iin.card+sp0.card+(al 14 D).card+bL 14 D<=2*P.card+12:=by
 classical
 let S:=sp0.biUnion D7;have b8:S.card=2*sp0.card:=by rw[card_biUnion λx u y w N=>((T2k x (n x u).1).2.2 y (n y w).1 N).1,SC rfl λx w=>(T2k x (n x w).1).1,sum_const,SM,mul_comm]
 obtain⟨K,F,u,b0,b1,-,cu,gu,-,R⟩:=sR h.1 d (R:=∅) (S:=S) a b c e f g j k l m (λ_ h=>AB h (NM _)) λy w=>let ⟨x,u,A⟩:=BI.1 w;let ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9⟩:=n x u;⟨x,a1,_mn.2 ⟨A,a2 (pD A).1⟩,a3,a4,a5,λ_=>a6,λ_=>a7,λ_=>a8,λ_=>a9⟩
 have:=CM u 2 λy _=>nT h.1 u (λy=>bX (K y)) F gu y;have M:=pg P (Iin.image pos) (sP p q r) (u.image λy=>ch 14 D P (F y)) λy w=>let ⟨i,u,E⟩:=_mg.1 w;E▸lq h.1 (gu i u)
 rw[s] at M;rw[_ce] at R;have:=bg 14 D;rw[b8] at cu;have:=_cl (US (λx w=>(n x w).1) e);rw[_cud (_dl.2 λx w=>(n x w).2.2.2.2.1),_c2 V] at this;split_ifs at R<;>omega
lemma qt_U_aux {D:Dag} (h:ai 14 D) (d:ar D) (z:ap 14 D<=12) {P Oc3 Oc4 Oc5 Iin U Ssp:o} {a4:O->O} {pos:O->Za} (a:P⊆eN) (I:∀a∈P,∀b∈P,¬dj a b) (b:Oc3⊆i_) (c:Oc4⊆K1) (e:Oc5⊆K1) (f:DJ Oc3 Oc4) (g:DJ Oc3 Oc5) (j:DJ Oc4 Oc5) (k:H3 D P Oc3) (l:H4 D P Oc4 a4) (m:H5 D P Oc5) (u1:∀f∈U,∃c∈K5\Oc3,f∈aD c∩P) (u2:∀c∈K5\Oc3,aD c⊆P->¬Q0 D P (aD c)) (n:∀f∈Ssp,f∉U/\(0:O)∉Oc3/\∃k∈K1,f∈D7 k∩P/\k∉Oc3/\k∉Oc4/\k∉Oc5/\Hn' D P k) (p:bA_dom D pos) (q:∀i∈Iin,i∈aa 14 D/\aD i⊆P) (r:∀e∈Iin.image pos,e∈aE 14 D (ao 14 D P)) (s:(Iin.image pos).card=Iin.card) (t:(aE 14 D (ao 14 D P)).card+(aW 14 D (ao 14 D P)).card=P.card+bn D (ao 14 D P)) (v:bn D (ao 14 D P)+(al 14 D).card<=P.card+bd 14 D):2*(2*Oc3.card+2*Oc4.card+c5 Oc3 Oc5+Iin.card+U.card+(al 14 D).card+bL 14 D)+Ssp.card<=2*(2*P.card+12):=by
 classical
 choose! C Q using u1
 have a1:∀f∈U,∃e,dG 14 D P (aD (C f)∩P) f e:=λf y=>by
  obtain⟨q1,q2⟩:=Q f y;have w:=(T2d (C f) (pD q1).1).1
  obtain⟨i,b',y',z',A',B',C'⟩:=fm_dom h.1 d (insert (C f) (P\(aD (C f)∩P))) (λx u y v=>by rcases _mi.1 u with rfl|u<;>rcases _mi.1 v with rfl|v;{exact ij _};{exact λc=>(pD v).2 (_mn.2 ⟨w▸cL.2 c,(pD v).1⟩)};{exact λc=>(pD u).2 (_mn.2 ⟨w▸cL.2 (lL c),(pD u).1⟩)};{exact I x (pD u).1 y (pD v).1}) f ⟨C f,mem_insert_self _ _,bm (cn.1 (pN q2).1)⟩
  have sc:ag 14 D (aw D (i,b'))∩P⊆aD (C f)∩P:=λv m=>by by_contra p';exact _dl.1 C' (pN m).1 (mem_insert_of_mem (_md.2 ⟨(pN m).2,p'⟩))
  refine⟨(i,b'),y',z',(pN q2).2,A',B',sc,?_⟩;by_cases x:aD (C f)⊆P;{have:=CL (SN.2 ⟨sc,λe'=>u2 _ q1 x ⟨_,(EL.2 x)▸e'⟩⟩);rw[EL.2 x,aDc] at this;omega};have h1:=CL (ssubset_of_subset_of_ne IL (mt EL.1 x));have:=_cl sc;rw[aDc] at h1;omega
 choose! W Y using a1;let S:=U.filter λf=>∀M,M⊆aD (C f)∩P->M.card=2->f∈M->¬Q0 D P M;have y:S⊆U:=_fs _ _
 have Z:∀f∈U\S,∃M,M⊆aD (C f)∩P/\M.card=2/\f∈M/\Q0 D P M:=λf m'=>by by_contra x;exact(pD m').2 (_mf.2 ⟨(pD m').1,λM a b c w=>x ⟨M,a,b,c,w⟩⟩)
 choose! pr a2 using Z;let R2:=(U\S).image pr
 have:(U\S).card<=2*R2.card:=CM _ 2 λM m'=>by obtain⟨x,w,rfl⟩:=_mg.1 m';rw[<-(a2 x w).2.1];exact _cl λf m'=>(pF m').2▸(a2 f (pF m').1).2.2.1
 have R:HR D P Oc3 Oc4 Oc5 R2:=λM m'=>by obtain⟨f,y,rfl⟩:=_mg.1 m';obtain⟨x,w,-,q'⟩:=a2 f y;refine⟨w,q',λi J E=>?_⟩;have o':=(Q f (pD y).1).1;have N:C f≠i:=λN=>by {subst N;have u:=(T2d _ (pD o').1).2.1;exact(_mu.1 J).elim (λJ=>(_mu.1 J).elim (pD o').2 λJ=>u (c J)) λJ=>u (e J)};have:=_cl (I9 (x.trans IL) E);have h1:=ig (C f) i N;change (aD (C f)∩aD i).card<=1 at h1;omega
 obtain⟨K,F,u,b0,b1,us,cu,gu,l0,hm⟩:=sR h.1 d a b c e f g j k l m R λi m'=>(n i m').2.2
 have hb1:b1=0:=by by_contra h';obtain⟨⟨i,hi⟩,h0⟩:=l0 (by omega);exact(n i hi).2.1 h0
 rw[hb1,IP rfl] at hm;let A:=U∪u;let lf f:=if f∈U then W f else F f;let qf f:=if f∈U then aD (C f)∩P else bX (K f)
 have G f (m':f∈A):dG 14 D P (qf f) f (lf f):=(_mu.1 m').elim (λm'=>by simp only[lf,qf,IP m'];exact Y f m') λm'=>by simp only[lf,qf,IN (n f (us m')).1];exact gu f m'
 have M:=pW h.1 P (Iin.image pos) (sP p q r) A S qf lf G (y.trans U1) λf m'=>by simp only[lf,IP (y m')];exact jN (Y f (y m')) (pF m').2
 have V:DJ U u:=_dl.2 λf o1 o2=>(n f (us o2)).1 o1
 have aS:(A\S).card=(U\S).card+u.card:=by dsimp[A];rw[union_sdiff_distrib,Finset.sdiff_eq_self_iff_disjoint.2 (V.symm.mono_right y),_cud (V.mono_left Sd)]
 have:=CS y;have:=bg 14 D;rw[s,aS] at M;omega
lemma qt_mIplus {D:Dag} (h:ai 14 D) (hD:ar D) (h12:ap 14 D<=12):let I:=aa 14 D;let P:=eN\I;∃(A B C:o),A⊆i_/\B⊆K1/\C⊆K1/\DJ A B/\DJ A C/\DJ B C/\(∀x∈A,aD x⊆P)/\(∀k∈B,aD k⊆P/\(D8 k⊆P\/D0 k⊆P))/\(∀k∈C,bX k⊆P)/\let E:=K5\A;let U:=E.biUnion (λc=>aD c∩P);let K:=K1.filter (λk=>aD k⊆P/\k∉A/\k∉B/\k∉C);let S:=(K1.filter (λk=>k∉A/\k∉B/\k∉C)).biUnion (λk=>D7 k∩P)\U;let J:=(i_∩I).filter (λi=>aD i⊆P);let M:=(J.filter (λi=>(i≠0\/dom 0⊆I)/\i∉A/\i∉B/\i∉C)).card;M<=bL 14 D/\2*(2*A.card+2*B.card+c5 A C+J.card+U.card+(al 14 D).card+M)+(if (0:O)∉A then S.card else if U=∅ then 2*K.card else 0)<=2*(2*P.card+12):=by
 classical
 let I:=aa 14 D;let P:=eN\I;have p:P⊆eN:=Sd;have F a (u:a∈P) b (v:b∈P):=hN_indep a (p u) b (p v)
 let q8 k:=D8 k⊆P/\Q0 D P (D8 k);let q0 k:=D0 k⊆P/\Q0 D P (D0 k);let A:=i_.filter λx=>aD x⊆P/\Q0 D P (aD x)
 let B:=K1.filter λk=>aD k⊆P/\¬Q0 D P (aD k)/\(q8 k\/q0 k);let C:=K1.filter λk=>bX k⊆P/\¬Q0 D P (aD k)/\¬Q0 D P (D8 k)/\¬Q0 D P (D0 k)/\Q0 D P (bX k)
 have J1:DJ A B:=_dl.2 λ_ s r=>(pF r).2.2.1 (pF s).2.2;have G1:DJ A C:=_dl.2 λ_ s r=>(pF r).2.2.1 (pF s).2.2;have H1:DJ B C:=_dl.2 λ_ s r=>(pF s).2.2.2.elim (λo'=>(pF r).2.2.2.1 o'.2) λo'=>(pF r).2.2.2.2.1 o'.2
 let a4 (k:O):O:=if q8 k then 8 else 10;have a1:H4 D P B a4:=λk r=>by obtain⟨-,_,n,c⟩:=pF r;dsimp[a4];split_ifs with o';{exact⟨V,o'.1,o'.2,n⟩};{have d:=c.resolve_left o';exact⟨V,d.1,d.2,n⟩}
 let E:=K5\A;let U:=E.biUnion λc=>aD c∩P;let J:=(i_∩I).filter λi=>aD i⊆P;let b3:=J.filter λi=>(i≠0\/dom 0⊆I)/\i∉A/\i∉B/\i∉C
 have hn k (r:k∈K1) (a:k∉A) (b:k∉B) (c:k∉C):Hn D P k:=let f:¬Q0 D P (aD k):=λq=>a (_mf.2 ⟨T1f.2.1 r,jw q,q⟩);let g:¬Q0 D P (D8 k):=λq=>b (_mf.2 ⟨r,U1.trans (jw q),f,.inl ⟨jw q,q⟩⟩);let j:¬Q0 D P (D0 k):=λq=>b (_mf.2 ⟨r,U1.trans (jw q),f,.inr ⟨jw q,q⟩⟩);⟨f,g,j,λq=>c (_mf.2 ⟨r,jw q,f,g,j,q⟩)⟩
 have a5:b3.card<=bL 14 D:=ml_dom h hD P F b3 (λi u=>by obtain⟨c,o',n,C',t⟩:=pF u;obtain⟨a,d⟩:=pF c;obtain⟨X,v⟩:=pN a;refine⟨if z:i=0 then z▸o'.resolve_left (Nt.2 z) else by rw[dom_eq_self z (T2f i X).1];exact SS.2 v,d,λM S R q=>?_⟩;by_cases u:i∈K1;{obtain⟨a,b,c,d⟩:=hn i u n C' t;rcases (OD (A9 (A9 T2h u) (PW.2 (R.trans IL)))).resolve_left (Nt.2 S) with rfl|rfl|rfl|rfl;{exact a q};{exact b q};{exact c q};{exact d q}};{exact n (_mf.2 ⟨X,d,(Subset.antisymm (((T2f i X).2.1 u)▸R.trans IL) S)▸q⟩)}) λi u j v d=>let hi:=pF (pF u).1;let hj:=pF (pF v).1;(T2g i j (pN hi.1).1 (pN hj.1).1 d).imp (λ⟨a,b,E',c⟩=>⟨a,_md.2 ⟨hj.2 b,λR=>E' (pD R).1⟩,cn.1 b,aH.1 c⟩) λ⟨a,b,E',c⟩=>⟨a,_md.2 ⟨hi.2 b,λR=>E' (pD R).1⟩,cn.1 b,aH.1 c⟩
 obtain⟨b,hb⟩:=b_dom h.1 hD;obtain⟨pos,hp⟩:=bQ_dom h hD;obtain⟨e7,w⟩:=e6_dom hp P J λi u=>let ⟨a,d⟩:=pF u;let ⟨x,v⟩:=_cp.1 (aDc i▸V:0<(aD i).card);⟨(pN a).2,⟨x,d v,cn.1 v⟩,λy o'=>(T2f i (pN a).1).2.2 y (p o')⟩
 have b1:=co h P (by rw[oc hD];simp);have b4:bn D (ao 14 D P)+(al 14 D).card<=P.card+bd 14 D:=L9 (cZ_dom h.1 hb P λv u ⟨a,b⟩=>_md.2 ⟨T2e v a (pN b).1 (p (pN b).2),λm=>aN.1 m u⟩) (by have:=_cl (IL:P∩al 14 D⊆P);omega)
 have T x (u:x∈A):=(pF u).2;have a0:H5 D P C:=λk r=>let ⟨_,a,b,c,d,e⟩:=pF r;⟨a,e,b,c,d⟩;have m i (u:i∈J):i∈aa 14 D/\aD i⊆P:=⟨(pN (pF u).1).2,(pF u).2⟩;have W c (u:c∈E) v q:=(pD u).2 (_mf.2 ⟨(T2d c (pD u).1).2.2,v,q⟩)
 have K:A⊆i_:=_fs _ _;have L:B⊆K1:=_fs _ _;have N:C⊆K1:=_fs _ _
 refine⟨A,B,C,K,L,N,J1,G1,H1,λx u=>(pF u).2.1,λk r=>⟨(pF r).2.1,(pF r).2.2.2.imp And.left And.left⟩,λk r=>(pF r).2.1,a5,?_⟩
 let K':=K1.filter λk=>aD k⊆P/\k∉A/\k∉B/\k∉C;let S':=(K1.filter λk=>k∉A/\k∉B/\k∉C).biUnion (λk=>D7 k∩P)\U
 let goU {S'} hS:=qt_U_aux h hD h12 p F K L N J1 G1 H1 T a1 a0 (λ_=>BI.1) W (Ssp:=S') hS hp m e7 w b1 b4
 dsimp[I,P,E,U,J,b3] at goU a5⊢;by_cases a:(0:O)∉A;{rw[IP a];have:=goU (S':=S') λf u=>let ⟨e,d⟩:=pD u;let ⟨k,r,o'⟩:=BI.1 e;let ⟨s,n,C',t⟩:=pF r;let ⟨x,y,z,w⟩:=hn k s n C' t;⟨d,a,k,s,o',n,C',t,λ_=>x,λ_=>y,λ_=>z,λ_=>w⟩;dsimp[S',U,E,P,I] at this;omega}
 rw[IN a];by_cases c:U=∅<;>dsimp[U,E,P,I] at c;{rw[IP c,c,_ce];have:=qt_sp0_aux h hD h12 p K L N J1 G1 H1 T a1 a0 (sp0:=K') (λk r=>let ⟨s,v,n,C',t⟩:=pF r;⟨s,v,n,C',t,hn k s n C' t⟩) (Nt.1 a) hp m e7 w b1 b4;dsimp[K',I,P,J] at this;omega};{rw[IN c];have:=goU (S':=∅) λ_ h=>AB h (NM _);rw[_ce] at this;omega}
lemma qt_kill {D:Dag} (h:ai 14 D) (hD:ar D) (h12:ap 14 D<=12) (hR2:(al 14 D).card+2<=bd 14 D) (c:Fin 68) (hc:c∈qtOrbits) (hI:aa 14 D=bU c):False:=by obtain⟨A,B,C,o',m,l,d,b,i,pa,pb,pc,j,n⟩:=qt_mIplus h hD h12;have z:=A9 Q3 hc;rw[<-hI] at z;have e:14-(aa 14 D).card=(al 14 D).card:=by {have:=aV 14 D;omega};exact OD (A9 (A9 (A9 z (PW.2 λk a=>_mf.2 ⟨o' a,pa k a⟩)) (PW.2 λk a=>_md.2 ⟨_mf.2 ⟨m a,pb k a⟩,_dl.1 d.symm a⟩)) (PW.2 λk a=>_md.2 ⟨_md.2 ⟨_mf.2 ⟨l a,pc k a⟩,_dl.1 b.symm a⟩,_dl.1 i.symm a⟩)) (e▸⟨(Nat.add_le_add hR2 j).trans ((bg 14 D)▸h12),n⟩)
end
namespace _4
abbrev S0:=Σ _:ℕ,ℕ
abbrev _ee:=@Finset.eq_empty_iff_forall_notMem
abbrev _ss:=@Finset.singleton_subset_iff
abbrev C:=isClean
abbrev B:=@bj_clean
abbrev E (u v:O):=ac u v=true
abbrev Q (u v:O):=bK u v=false
abbrev M (i x t:O):=cmOk i x t=true
abbrev Y (x a b:O):=mV x a b=true
abbrev EG (i j x v:O):=i≠j/\E i x/\E j x/\E x v/\v≠i/\v≠j
abbrev CG (S:o) (x t i q:O):=dom i⊆S/\t∉dom x/\E i x/\E i q/\Y x t q/\Q i t
abbrev EO (a i j y:O):=¬((bK i y=true/\bK j y=true)\/(bK i y=true/\∀ q:O,E j q->mV a y q=false)\/(bK j y=true/\∀ q:O,E i q->mV a y q=false))
abbrev CT (S:o) (i1 i2:O):=((i1=0\/i1=7)/\(0:O)∈S/\(7:O)∈S)\/(dom i1⊆S/\i2∉dom i1)
abbrev DL (S:o) (z k v iz ik:O):=iz∈S/\ik∈S/\(z∉dom ik/\k∉dom iz/\v∉dom iz)/\(E iz z/\E ik k/\E z k/\E z v/\M ik k v)
structure W (D:Dag) (b:O->ℕ) (p:O->ℕ×_d) (j:Fin 68) where
 h:ai 14 D
 r:ar D
 z:bL 14 D=0
 b:cU_dom D b
 p:bA_dom D p
 I:aa 14 D=bU j
lemma eP {x y:O} (g:E x y):aP x y:=(ae _ _).1 g
lemma sw {α} [DecidableEq α] {x y:α} {S:Finset α} (h:S={x,y}):S={y,x}:=h.trans (pair_comm _ _)
lemma EGs {i j x v:O} (h:EG i j x v):EG j i x v:=⟨h.1.symm,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2,h.2.2.2.2.1⟩
lemma nq {D:Dag} (h:ai 14 D) (r:ar D) {p:O->ℕ×_d} (hp:bA_dom D p) {a i y:O} {P K:ℕ×_d} (hi:i∈aa 14 D) (Pa:P∈af 14 D a) (Ka:K∈af 14 D a) (pi:p i∈af 14 D a) (PK:P≠K) (hn:¬(p i=P\/p i=K)) (hl:(af 14 D a).card<=3) (yP:y∈ag 14 D (aw D P)) (yK:y∈ag 14 D (aw D K)):∀ q:O,E i q->mV a y q=false:=fun q g=>by
 by_contra m;rw[_nf] at m;obtain⟨f,fa,c,d⟩:=bE_dom h.1 r m
 have:=aT Pa Ka pi PK (fun e=>hn (.inl e.symm)) (fun e=>hn (.inr e.symm)) hl f fa
 have:=(hp.1 i hi).2.2.2.1 q (eP g);grind only
lemma r4 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) {j:Fin 68} (hI:aa 14 D=bU j) (K:∀ {b p},W D b p j->∀ u v:S0,u≠v->aj 14 D b={u,v}->False) (hc:(bU j).card=4:=by decide):False:=by
 have a:=aV 14 D;rw[hI,hc] at a
 by_cases z:bd 14 D<=(al 14 D).card;{exact dn h r h12 z j hI}
 by_cases e:bd 14 D=(al 14 D).card+1;{exact dp h r h12 e j (by omega) hI}
 have:=bg 14 D;obtain⟨b,c⟩:=b_dom h.1 r;obtain⟨p,q⟩:=bQ_dom h r
 obtain⟨u,v,n,k⟩:=_ct2.1 (by have:=bS_dom h.1 c;omega:(aj 14 D b).card=2)
 exact K ⟨h,r,by omega,c,q,hI⟩ u v n k
end _4
section
open _4
lemma cT_07_uncond {D:Dag} {pos:O->ℕ×_d} (hp:bA_dom D pos) (h0:(0:O)∈aa 14 D) (h7:(7:O)∈aa 14 D):(∀ t,t∈ag 14 D (aw D (pos 0))->dj 0 t)/\(∀ t,t∈ag 14 D (aw D (pos 7))->dj 7 t):=by
 have e:pos 7=am (pos 0):=_ms.1 ((hp.1 0 h0).2.2.2.2.2.2▸aJ hp h7 (V:aP 7 0))
 exact⟨fun t ht=>(V:∀ u∈dom 7,dj 0 u) t ((hp.1 7 h7).2.2.2.2.2.1 (by rwa[e,aB])),fun t ht=>(V:∀ u∈dom 0,dj 7 u) t ((hp.1 0 h0).2.2.2.2.2.1 (by rwa[<-e]))⟩
lemma dV_any {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} {x:O} {u:Σ _:ℕ,ℕ} (hM:aW 14 D (ao 14 D {x})=∅) (hu:u∈aZ D b x):∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x/\∀ y:O,y∈ag 14 D u.1->y∈ag 14 D (aw D P)/\y∈ag 14 D (aw D Q):=by
 obtain⟨a,c⟩:=ay.1 hu;obtain⟨P,K,d,e,f,g,k⟩:=dV_tree h r hM c (by have:=(dW.1 (_mf.1 (_md.1 a).1).1).2;omega)
 exact⟨P,K,fun q=>d (congrArg Prod.fst q),e,f,fun y hy=>⟨bk_x_ag h.1 hM g hy,bk_x_ag h.1 hM k hy⟩⟩
lemma dV_dom {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {x:O} {u:Σ _:ℕ,ℕ} (hcx:isClean (aa 14 D) x) (hZx:aZ D b x={u}) (hx3:3<=(af 14 D x).card):∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x/\∀ y:O,y∈ag 14 D u.1->y∈ag 14 D (aw D P)/\y∈ag 14 D (aw D Q):=
 dV_any h r (card_eq_zero.1 (by have:=B h r hb hcx;rw[hZx,_cs] at this;omega)) (hZx▸_mss u)
lemma clean_shared_af_u {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {x y:O} {u:Σ _:ℕ,ℕ} (hcx:isClean (aa 14 D) x) (hcy:isClean (aa 14 D) y) (hZx:aZ D b x={u}) (hZy:aZ D b y={u}) (hx3:3<=(af 14 D x).card) (hy3:3<=(af 14 D y).card):∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x/\P∈af 14 D y/\Q∈af 14 D y:=by
 obtain⟨P,K,d,e,f,g⟩:=dV_dom h r hb hcx hZx hx3
 have N:aW 14 D (ao 14 D {y})=∅:=card_eq_zero.1 (by have:=B h r hb hcy;rw[hZy,_cs] at this;omega)
 obtain⟨a,c⟩:=g y (ay.1 (hZy▸_mss u)).2
 exact⟨P,K,d,e,f,gD h.1 N (ak.1 e).1 (cY h.1 e) a,gD h.1 N (ak.1 f).1 (cY h.1 f) c⟩
lemma eF_cand_dom_u {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} {a i1 i2 v3:O} (hca:isClean (aa 14 D) a) (hZa:aZ D b a={u0}) (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (hg:i1≠i2/\ac i1 a=true/\ac i2 a=true/\ac a v3=true/\v3≠i1/\v3≠i2) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (hc1:∀ t,t∈ag 14 D (aw D (pos i1))->dj i1 t) (hc2:∀ t,t∈ag 14 D (aw D (pos i2))->dj i2 t):∀ y:O,y∈ag 14 D u0.1->(dj i1 y/\dj i2 y)\/(dj i1 y/\∀ q:O,ac i2 q=true->mV a y q=false)\/(dj i2 y/\∀ q:O,ac i1 q=true->mV a y q=false):=fun y hy=>by
 have l:(af 14 D a).card<=3:=by have:=B h r hb hca;rw[hZa,_cs] at this;omega
 obtain⟨P,K,d,e,f,g⟩:=dV_dom h r hb hca hZa (cx_dom h r hp hi1 hi2 hg hdomv);obtain⟨m,n⟩:=g y hy
 have p1:=aJ hp hi1 (eP hg.2.1);have p2:=aJ hp hi2 (eP hg.2.2.1)
 let c {i} (k:∀ t,t∈ag 14 D (aw D (pos i))->dj i t) (q:pos i=P\/pos i=K):=k y (q.elim (·▸m) (·▸n))
 by_cases s:pos i1=P\/pos i1=K <;> by_cases t:pos i2=P\/pos i2=K
 ;{exact .inl ⟨c hc1 s,c hc2 t⟩};{exact .inr (.inl ⟨c hc1 s,nq h r hp hi2 e f p2 d t l m n⟩)};{exact .inr (.inr ⟨c hc2 t,nq h r hp hi1 e f p1 d s l m n⟩)}
 have:=mm e f p1 p2 d (fun q=>s (.inl q.symm)) (fun q=>t (.inl q.symm)) (fun q=>s (.inr q.symm)) (fun q=>t (.inr q.symm)) (fun q=>hg.1 (hp.2 hi1 hi2 q));omega
lemma eF_cand_1side_u {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {u0:Σ _:ℕ,ℕ} {a i2:O} (hca:isClean (aa 14 D) a) (hZa:aZ D b a={u0}) (ha3:3<=(af 14 D a).card) (hi2:i2∈aa 14 D) (ha2:ac i2 a=true) (hc2:∀ t,t∈ag 14 D (aw D (pos i2))->dj i2 t):∀ y:O,y∈ag 14 D u0.1->dj i2 y\/∀ q:O,ac i2 q=true->mV a y q=false:=fun y hy=>by
 have l:(af 14 D a).card<=3:=by have:=B h r hb hca;rw[hZa,_cs] at this;omega
 obtain⟨P,K,d,e,f,g⟩:=dV_dom h r hb hca hZa ha3;obtain⟨m,n⟩:=g y hy
 by_cases t:pos i2=P\/pos i2=K;{exact .inl (hc2 y (t.elim (·▸m) (·▸n)))}
 exact .inr (nq h r hp hi2 e f (aJ hp hi2 (eP ha2)) d t l m n)
lemma iK_dom {D:Dag} (m:au 14 D) {b:O->ℕ} (hb:cU_dom D b) {x y:O} (hxe:x∈al 14 D) (hcx:isClean (aa 14 D) x) (hny:y∉dom x):bn D (aR 14 D x y)=1+((aj 14 D b).filter (fun u=>x∈ag 14 D u.1/\y∉ag 14 D u.1)).card:=by
 let P (w:ℕ):=x∈ag 14 D w/\y∉ag 14 D w
 have q:bn D (aR 14 D x y)=((dq 14 D).filter (fun u=>P u.1)).card:=by
  rw[eI 14 D P];symm;exact sum_subset (fun w h=>f_.2 (_mf.1 h).2) fun w h c=>by have l:w∉cD 14 D:=fun d=>c (_mf.2 ⟨d,f_.1 h⟩);rw[bP] at l;simp[d0 m w (by omega)]
 have r:(dq 14 D).filter (fun u=>P u.1)={(⟨b x,0⟩:S0)}∪(aj 14 D b).filter (fun u=>P u.1):=by
  ext u;have e:=eY_dom m hb;simp only[aj,da,_mu,_mf,_md,_ms];constructor
  ;{intro a;by_cases p:u∈cz 14 D b
    ;{left;obtain⟨v,z,rfl⟩:=_mg.1 p;suffices v=x by rw[this]
      by_contra n;exact absurd z (aN.1 (by rcases (V:∀ a c:O,a∈dom c->c≠a->((a=1\/a=3)/\c=0)\/((a=8\/a=10)/\c=7)) x v ((hb v z).2.2.1 a.2.1) n with ⟨k,rfl⟩|⟨k,rfl⟩ <;> rcases hcx with l|⟨l,s⟩|⟨l,s⟩ <;> first | exact s | (exfalso;clear * - k l;revert x;decide)))}
    exact .inr ⟨⟨⟨a.1,⟨x,a.2.1⟩⟩,p⟩,a.2⟩}
  rintro(rfl|⟨⟨⟨a,-⟩,-⟩,c⟩);{exact⟨(_mf.1 (e (_mg.2 ⟨x,hxe,rfl⟩))).1,(hb x hxe).2.1,fun k=>hny ((hb x hxe).2.2.1 k)⟩};exact⟨a,c⟩
 rw[q,r,_cud (_dl.2 fun _ a c=>by rw[_ms.1 a] at c;exact (_md.1 (_mf.1 c).1).2 (_mg.2 ⟨x,hxe,rfl⟩)),_cs]
lemma jx_dom {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {x c:O} (hxe:x∈al 14 D) (hcx:isClean (aa 14 D) x) (hxc:x≠c) (hnc:c∉dom x) (hsub:aZ D b x⊆aZ D b c) (hw:∃ w,x∈ag 14 D w/\c∈ag 14 D w) (hz:∃ z:O,ac x z=true/\bK c z=false):∃ f,∀ e∈af 14 D x,e≠f->c∈ag 14 D (aw D e):=by
 classical
 have a:bn D (aR 14 D x c)=1:=by rw[iK_dom h.1 hb hxe hcx hnc,filter_eq_empty_iff.2 (fun _ u d=>d.2 (ay.1 (hsub (ay.2 ⟨u,d.1⟩))).2),_ce]
 have t:=gN h x c hxc (by rw[oc r];exact notMem_empty x);rw[a] at t
 obtain⟨w,p,q⟩:=hw;obtain⟨j1,s1,v,y,A,i,j,k,-,-⟩:=ji h.1 hxc ⟨p,q⟩;have l:(j1,s1)∈aE 14 D (aR 14 D x c):=dY.2 ⟨v,⟨j,k⟩,fun d=>d.2 i⟩
 obtain⟨z,g,n⟩:=hz
 obtain⟨j2,s2,K,-,G,m,L⟩:=fm_dom h.1 r {c,z} (fun u a v b=>by simp only[_mi,_ms] at a b;rcases a with rfl|rfl <;> rcases b with rfl|rfl <;> first | exact ij _ | exact b3.1 n | exact fun d=>b3.1 n (lL d)) x ⟨z,by simp,eP g⟩
 have F:(j2,s2)∈aE 14 D (aR 14 D x c):=dY.2 ⟨K,⟨G,fun d=>_dl.1 L d (by simp)⟩,fun d=>m d.1⟩
 have d:(aE 14 D (aR 14 D x c)).card=2:=by have:=one_lt_card.2 ⟨_,l,_,F,fun p=>m ((show j1=j2 from congrArg Prod.fst p)▸A)⟩;omega
 obtain⟨f,hf⟩:=_c1.1 (by rw[card_erase_of_mem l,d]:((aE 14 D (aR 14 D x c)).erase (j1,s1)).card=1)
 exact⟨f,fun e u s=>by by_contra q;obtain⟨k,m,n⟩:=ak.1 u;exact s (_ms.1 (hf▸_me.2 ⟨fun d=>by have:=cY h.1 u;rw[d,y] at this;exact _fnt this,dY.2 ⟨k,⟨m,q⟩,fun K=>n K.1⟩⟩))⟩
lemma orb49_cut {D:Dag} (h:ai 14 D) (r:ar D) (l:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) (x t i q:O) (c:isClean (aa 14 D) x) (hi:dom i⊆aa 14 D) (g:t∉dom x/\ac i x=true/\ac i q=true/\mV x t q=true/\bK i t=false) (hn:(aZ D b x).Nonempty) (hs:aZ D b x⊆aZ D b t):False:=by
 obtain⟨a,d,k,m,n⟩:=g;have p:=m;simp only[mV,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at p
 obtain⟨⟨⟨v,-⟩,-⟩,z,w,y,-⟩:=p;obtain⟨u,hu⟩:=hn;obtain⟨ur,xu⟩:=ay.1 hu
 obtain⟨f,hf⟩:=jx_dom h r hb (fC ur xu) c v a hs ⟨u.1,xu,(ay.1 (hs hu)).2⟩ ⟨z,w,b3.2 fun e=>b3.1 y (lL e)⟩
 obtain⟨j,s,jd,jc,sp,he⟩:=jL_dom h.1 r {t} (fun _ a _ b=>by rw[_ms.1 a,_ms.1 b];exact ij _) (i:=i) (fun _ a e=>(b3.1 n (_ms.1 a▸e)).elim) (gr_dom h r l hi (iD h i.val (Nat.lt_add_right _ i.isLt)))
 have o':aF D (aw D (j,!s))=1:=by have:=ef (cM (n:=14) jd (!s));by_contra e;have K:2<=aF D (aw D (j,!s)):=(by omega);exact not_nonempty_empty (eM_dom h.1 r hi sp K▸fJ h.1 l K)
 have A (v:O) (g:aP i v):=jV_dom h.1 r jd s jc sp o' (by unfold bH;omega) g
 have ex:(j,s)∈af 14 D x:=ak.2 ⟨jd,A x (eP d),fun e=>(V:∀ a b:O,E a b->b∉dom a) i x d (fk_dom h.1 r i _ (ds h.1 sp) (cr h.1 jd jc (!s) e))⟩
 have f0:(j,s)=f:=by by_contra e;exact b3.1 n (.inl ((he t (_mss _)).1 (hf _ ex e)))
 obtain⟨e,he,et,eq⟩:=bE_dom h.1 r m
 exact eq (by rw[show e=f by by_contra y;exact et (hf _ he y),<-f0];exact A q (eP k))
lemma cy_dom {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {v t j q:O} (hcv:isClean (aa 14 D) v) (hj:j∈aa 14 D) (hsub:aZ D b v⊆aZ D b t) (hne:(aZ D b v).Nonempty) (hnt:t∉dom v) (hg:ac j v=true/\ac j q=true/\mV v t q=true):t∈ag 14 D (aw D (pos j)):=by
 obtain⟨a,c,m⟩:=hg;have p:=m;simp only[mV,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at p
 obtain⟨⟨⟨d,-⟩,-⟩,z,w,n,-⟩:=p;obtain⟨u,hu⟩:=hne
 obtain⟨f,hf⟩:=jx_dom h r hb (fC (ay.1 hu).1 (ay.1 hu).2) hcv d hnt hsub ⟨u.1,(ay.1 hu).2,(ay.1 (hsub hu)).2⟩ ⟨z,w,b3.2 fun e=>b3.1 n (lL e)⟩
 by_contra k;have s:pos j=f:=by by_contra e;exact k (hf _ (aJ hp hj (eP a)) e)
 obtain⟨e,he,g,l⟩:=bE_dom h.1 r m;exact g (hf e he fun p=>l (by rw[p,<-s];exact (hp.1 j hj).2.2.2.1 q (eP c)))
lemma o0_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {v i1 i2 v3 t q:O} (hcv:isClean (aa 14 D) v) (hi1:i1∈aa 14 D) (hi2:i2∈aa 14 D) (hdom1:dom i1⊆aa 14 D) (hsub:aZ D b v⊆aZ D b t) (hc1:(aZ D b v).card=1) (hnt:t∉dom v) (hdomv:v3∈aa 14 D\/(v3∉dom i1/\v3∉dom i2)) (hg:i1≠i2/\ac i1 v=true/\ac i2 v=true/\ac v v3=true/\v3≠i1/\v3≠i2/\i2∉dom i1/\v3∉dom i1/\ac i1 q=true/\mV v t q=true/\bK i1 t=false):False:=
 (fun _ _ _ _=>orb49_cut h r hb0 hb v t i1 q hcv hdom1 ⟨hnt,hg.2.1,hg.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2⟩ (_cp.1 (by omega)) hsub) hp hi1 hi2 hdomv
lemma fa_dom {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (a b' a1 a2 qa1 qa2 b1 b2 vb:O) (hca:isClean (aa 14 D) a) (hcb:isClean (aa 14 D) b') (ha1:a1∈aa 14 D) (ha2:a2∈aa 14 D) (hb1:b1∈aa 14 D) (hb2:b2∈aa 14 D) (hvb:vb∉dom a1/\vb∉dom a2/\vb∉dom b1/\vb∉dom b2) (hnt:b'∉dom a/\b'∉dom a1/\b'∉dom a2) (hg:a1≠a2/\a1≠b1/\a1≠b2/\a2≠b1/\a2≠b2/\b1≠b2/\ac a1 a=true/\ac a2 a=true/\ac a1 qa1=true/\mV a b' qa1=true/\ac a2 qa2=true/\mV a b' qa2=true/\ac b1 b'=true/\ac b2 b'=true/\ac b' vb=true) (hne:(aZ D b a).Nonempty) (hsub:aZ D b a⊆aZ D b b') (h2:(aZ D b b').card<=2):False:=by
 obtain⟨c,d,f,g,k,m,n,p,s,t,u,v,w,y,z⟩:=hg;obtain⟨e,he,-,l,-⟩:=bf h r hp (eP z)
 let q {x y} (i:x∈aa 14 D) (j:y∈aa 14 D) (o':x≠y):pos x≠pos y:=fun e=>o' (hp.2 i j e)
 let l' {x} (i:x∈aa 14 D) (o':vb∉dom x):pos x≠e:=fun d=>o' (l x i d.symm)
 have:=mn (cV_dom hp ha1 (cy_dom h r hb hp hca ha1 hsub hne hnt.1 ⟨n,s,t⟩) hnt.2.1) (cV_dom hp ha2 (cy_dom h r hb hp hca ha2 hsub hne hnt.1 ⟨p,u,v⟩) hnt.2.2) (aJ hp hb1 (eP w)) (aJ hp hb2 (eP y)) he (q ha1 ha2 c) (q ha1 hb1 d) (q ha1 hb2 f) (l' ha1 hvb.1) (q ha2 hb1 g) (q ha2 hb2 k) (l' ha2 hvb.2.1) (q hb1 hb2 m) (l' hb1 hvb.2.2.1) (l' hb2 hvb.2.2.2)
 have:=B h r hb hcb;omega
lemma eO_dom {D:Dag} (h:ai 14 D) (r:ar D) (hb0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (hR2:(aj 14 D b).card=2) (a b' i0 ia ib va vb qa qb:O) (hca:isClean (aa 14 D) a) (hcb:isClean (aa 14 D) b') (hi0:i0∈aa 14 D) (hia:ia∈aa 14 D) (hib:ib∈aa 14 D) (hdoma:dom ia⊆aa 14 D) (hdomb:dom ib⊆aa 14 D) (hdomva:va∈aa 14 D\/(va∉dom ia/\va∉dom i0)) (hdomvb:vb∉dom i0/\vb∉dom ia/\vb∉dom ib) (hg:i0≠ia/\i0≠ib/\ia≠ib/\i0∉dom ia/\va∉dom ia/\i0∉dom ib/\ia∉dom ib/\b'∉dom a/\a∉dom b'/\b'∉dom ia/\ac i0 a=true/\ac ia a=true/\ac a va=true/\va≠i0/\va≠ia/\ac i0 b'=true/\ac ib b'=true/\ac b' vb=true/\ac ia qa=true/\mV a b' qa=true/\bK ia b'=false/\ac ib qb=true/\mV b' a qb=true/\bK ib a=false) (hne:(aZ D b a).Nonempty) (hsub:aZ D b a⊆aZ D b b'):False:=by
 obtain⟨-,-,-,-,-,-,-,c,-,-,-,d,-,-,-,-,-,-,f,g,k,-,-,-⟩:=hg
 exact (fun _ _ _ _ _ _ _ _ _=>orb49_cut h r hb0 hb a b' ia qa hca hdoma ⟨c,d,f,g,k⟩ hne hsub) hp hR2 hcb hi0 hia hib hdomb hdomva hdomvb
lemma aE_du_clean_T {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) (T:o) (hnl:∀ v∈al 14 D,(dom v∩T).Nonempty->v∈T):(aE 14 D (ao 14 D T)).card+(du 14 D T).card<=T.card+(T.card+(aj 14 D b).card):=by
 have:=co h T (by rw[oc r];simp);have:=cZ_dom h.1 hb T hnl;have:=bS_dom h.1 hb;have:(du 14 D T).card<=(aW 14 D (ao 14 D T)).card:=_cl (_fs _ _);have:=_cl (inter_subset_left:T∩al 14 D⊆T);omega
lemma dZ_dom {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (j:Fin 68) (hI:aa 14 D=bU j) (h4:(bU j).card=4) (a b' ia1 ia2 av ib1 ib2 bv:O) (ha1:ia1∈aa 14 D) (ha2:ia2∈aa 14 D) (hb1:ib1∈aa 14 D) (hb2:ib2∈aa 14 D) (hca:isClean (aa 14 D) a) (hcb:isClean (aa 14 D) b') (hva:av∈aa 14 D\/(av∉dom ia1/\av∉dom ia2)) (hvb:bv∈aa 14 D\/(bv∉dom ib1/\bv∉dom ib2)) (Ea:ia1≠ia2/\ac ia1 a=true/\ac ia2 a=true/\ac a av=true/\av≠ia1/\av≠ia2) (Eb:ib1≠ib2/\ac ib1 b'=true/\ac ib2 b'=true/\ac b' bv=true/\bv≠ib1/\bv≠ib2) (z k v iz ik:O) (hiz:iz∈aa 14 D) (hik:ik∈aa 14 D) (hcz:isClean (aa 14 D) z) (hck:isClean (aa 14 D) k) (hdomzk:z∉dom ik/\k∉dom iz/\v∉dom iz) (hzk:ac iz z=true/\ac ik k=true/\ac z k=true/\ac z v=true/\cmOk ik k v=true) (ha_ct:∀ (pos:O->ℕ×_d),bL 14 D=0->bA_dom D pos->(af 14 D a).card<=3->(∀ t,t∈ag 14 D (aw D (pos ia1))->dj ia1 t)/\(∀ t,t∈ag 14 D (aw D (pos ia2))->dj ia2 t)) (hb_ct:∀ (pos:O->ℕ×_d),bL 14 D=0->bA_dom D pos->(af 14 D b').card<=3->(∀ t,t∈ag 14 D (aw D (pos ib1))->dj ib1 t)/\(∀ t,t∈ag 14 D (aw D (pos ib2))->dj ib2 t)) (hzk_out:∀ y∈({z,k}:o),¬((dj ia1 y/\dj ia2 y)\/(dj ia1 y/\∀ q:O,ac ia2 q=true->mV a y q=false)\/(dj ia2 y/\∀ q:O,ac ia1 q=true->mV a y q=false))/\¬((dj ib1 y/\dj ib2 y)\/(dj ib1 y/\∀ q:O,ac ib2 q=true->mV b' y q=false)\/(dj ib2 y/\∀ q:O,ac ib1 q=true->mV b' y q=false))) (hl:∀ (b:O->ℕ),cU_dom D b->∀ pos,bL 14 D=0->bA_dom D pos->(aj 14 D b).card=2->(aZ D b a).Nonempty->aZ D b a⊆aZ D b b'->False) (hm:∀ (b:O->ℕ),cU_dom D b->∀ pos,bL 14 D=0->bA_dom D pos->(aj 14 D b).card=2->(aZ D b b').Nonempty->aZ D b b'⊆aZ D b a->False):False:=r4 h r h12 hI (fun {b p} w u x n q=>by
 have c:(aj 14 D b).card=2:=by rw[q,_c2 n]
 have d:(aZ D b a).Nonempty:=_cp.1 (by have:=cx_dom h r w.p ha1 ha2 Ea hva;have:=B h r w.b hca;omega)
 have e:(aZ D b b').Nonempty:=_cp.1 (by have:=cx_dom h r w.p hb1 hb2 Eb hvb;have:=B h r w.b hcb;omega)
 suffices K:∀ U X,aj 14 D b={U,X}->aZ D b a={U}->aZ D b b'={X}->False by rcases dJ n (q▸_fs _ _) (q▸_fs _ _) d e (hl b w.b p w.z w.p c d) (hm b w.b p w.z w.p c e) with ⟨s,t⟩|⟨s,t⟩;{exact K u x q s t};exact K x u (sw q) s t
 intro U X q s t
 obtain⟨c1,c2⟩:=ha_ct p w.z w.p (by have:=B h r w.b hca;rw[s,_cs] at this;omega)
 obtain⟨d1,d2⟩:=hb_ct p w.z w.p (by have:=B h r w.b hcb;rw[t,_cs] at this;omega)
 have f:=eF_cand_dom_u h r w.b w.p hca s ha1 ha2 Ea hva c1 c2;have g:=eF_cand_dom_u h r w.b w.p hcb t hb1 hb2 Eb hvb d1 d2
 have l (y) (m:y∈({z,k}:o)) (u:C (aa 14 D) y):(af 14 D y).card<=2:=by
  have Z:aZ D b y=∅:=_ee.2 fun i j=>by obtain⟨m',g'⟩:=ay.1 j;rw[q,_mi,_ms] at m';rcases m' with rfl|rfl;{exact (hzk_out y m).1 (f y g')};exact (hzk_out y m).2 (g y g')
  have:=B h r w.b u;rw[Z,_ce] at this;omega
 exact dl_dom h r w.p z k v iz ik hiz hik hdomzk hzk (l z (by simp) hcz) (l k (by simp) hck)) h4
end
namespace _4
lemma ps {D:Dag} {b:O->ℕ} (x:O):aZ D b x⊆aj 14 D b:=_fs _ _
lemma pA {D:Dag} {b:O->ℕ} {u v:S0} {x:O} (s:aj 14 D b={u,v}) (n:x∉ag 14 D u.1):aZ D b x⊆{v}:=fun _ w=>by obtain⟨m,g⟩:=ay.1 w;rw[s,_mi,_ms] at m;exact _ms.2 (m.resolve_left fun q=>n (q▸g))
lemma pp {α} [DecidableEq α] {u v:α} {S:Finset α} (s:S⊆{u,v}) (n:S.Nonempty):S={u}\/S={v}\/S={u,v}:=by
 obtain⟨_,h⟩:=n;have:=s h;simp only[_mi,_ms] at this
 by_cases a:u∈S <;> by_cases c:v∈S <;> [refine .inr (.inr ?_);refine .inl ?_;refine .inr (.inl ?_);grind only] <;> (ext x;have:=@s x;simp only[_mi,_ms] at this⊢;grind only)
lemma pB {D:Dag} {b:O->ℕ} {A K:S0} (k:aj 14 D b={A,K}) {x y:O} (z:aZ D b x={A}) (n:(aZ D b y).Nonempty) (c:¬aZ D b x⊆aZ D b y):aZ D b y={K}:=by
 rcases pp (k▸ps y) n with q|q|q;{exact (c (by rw[z,q])).elim};{exact q};exact (c (by rw[z,q];simp)).elim
lemma dJ3 {D:Dag} {b:O->ℕ} {u v:S0} (n:u≠v) (k:aj 14 D b={u,v}) {a c d:O} (x:(aZ D b a).Nonempty) (y:(aZ D b c).Nonempty) (z:(aZ D b d).Nonempty) (f:¬aZ D b a⊆aZ D b c) (g:¬aZ D b c⊆aZ D b a) (p:∀ w,aZ D b a={w}->aZ D b d={w}->False) (q:∀ w,aZ D b c={w}->aZ D b d={w}->False) (s:aZ D b d={u,v}->False):False:=by
 rcases dJ n (k▸ps a) (k▸ps c) x y f g with ⟨i,j⟩|⟨i,j⟩ <;> rcases pp (k▸ps d) z with e|e|e <;> first | exact p _ i e | exact q _ j e | exact s e
lemma dz4 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) {j:Fin 68} (hI:aa 14 D=bU j) (a b' i1 i2 av j1 j2 bv z k v iz ik ca qa cb qb:O)
 (G1:(bU j).card=4/\i1∈bU j/\i2∈bU j/\j1∈bU j/\j2∈bU j/\C (bU j) a/\C (bU j) b'/\av∉dom i1/\av∉dom i2:=by decide +kernel)
 (G2:bv∉dom j1/\bv∉dom j2/\EG i1 i2 a av/\EG j1 j2 b' bv/\iz∈bU j/\ik∈bU j/\C (bU j) z/\C (bU j) k:=by decide +kernel)
 (G3:(z∉dom ik/\k∉dom iz/\v∉dom iz)/\(E iz z/\E ik k/\E z k/\E z v/\M ik k v)/\CT (bU j) i1 i2/\CT (bU j) i2 i1/\CT (bU j) j1 j2/\CT (bU j) j2 j1:=by decide +kernel)
 (G4:CG (bU j) a b' ca qa/\CG (bU j) b' a cb qb/\∀ y∈({z,k}:o),EO a i1 i2 y/\EO b' j1 j2 y:=by decide +kernel):False:=by
 obtain⟨c,d,e,f,m,n,p,q,s⟩:=G1;obtain⟨t,u,A,B',F,H,J,K⟩:=G2;obtain⟨L,N,P,Q',R,S⟩:=G3;obtain⟨⟨X,Y'⟩,⟨Z,U⟩,V'⟩:=G4
 let g {x t m n:O} (i:m∈bU j) (k:n∈bU j) (G:EG m n x t) (a:t∉dom m) (c:t∉dom n) (T:CT (bU j) m n) (p:O->ℕ×_d) (z:bL 14 D=0) (w:bA_dom D p) (l:(af 14 D x).card<=3):∀ y,y∈ag 14 D (aw D (p m))->dj m y:=by
  rcases hI▸T with ⟨rfl|rfl,u,v⟩|⟨y,y'⟩;{exact (cT_07_uncond w u v).1};{exact (cT_07_uncond w u v).2};exact dy_dom h r z w (hI▸i) (hI▸k) y G (.inr ⟨a,c⟩) y' a l
 exact dZ_dom h r h12 j hI c a b' i1 i2 av j1 j2 bv (hI▸d) (hI▸e) (hI▸f) (hI▸m) (hI▸n) (hI▸p) (.inr ⟨q,s⟩) (.inr ⟨t,u⟩) A B' z k v iz ik (hI▸F) (hI▸H) (hI▸J) (hI▸K) L N (fun p z w l=>⟨g d e A q s P p z w l,g e d (EGs A) s q Q' p z w l⟩) (fun p z w l=>⟨g f m B' t u R p z w l,g m f (EGs B') u t S p z w l⟩) (fun y hy=>by simpa only[<-cW] using V' y hy) (fun _ c _ z _ _=>orb49_cut h r z c a b' ca qa (hI▸n) (hI▸X) Y') (fun _ c _ z _ _=>orb49_cut h r z c b' a cb qb (hI▸p) (hI▸Z) U)
namespace W
section
variable {D:Dag} {b:O->ℕ} {p:O->ℕ×_d} {j:Fin 68} (w:W D b p j)
include w
lemma aJ (i x:O) (g:i∈bU j/\E i x:=by decide):p i∈af 14 D x:=_U.aJ w.p (w.I▸g.1) (eP g.2)
abbrev bF (x y:O) (g:E x y:=by decide):=_U.bf w.h w.r w.p (eP g)
lemma ne (i:O) {x:O} {e:ℕ×_d} (m:am e∈af 14 D x) (g:i∈bU j/\x∉dom i:=by decide):p i≠e:=fun k=>g.2 (em_dom w.p (w.I▸g.1) (k.symm▸m))
lemma pn (x:O) (l:3<=(af 14 D x).card) (g:C (bU j) x:=by decide):(aZ D b x).Nonempty:=_cp.1 (by have:=B w.h w.r w.b (w.I▸g);omega)
lemma pl (x:O) (z:aZ D b x=∅) (g:C (bU j) x:=by decide):(af 14 D x).card<=2:=by have:=B w.h w.r w.b (w.I▸g);rw[z,_ce] at this;omega
lemma cap (x:O) {u:S0} (z:aZ D b x={u}) (g:C (bU j) x:=by decide):(af 14 D x).card<=3:=by have:=B w.h w.r w.b (w.I▸g);rw[z,_cs] at this;omega
lemma eqs (x:O) {u:S0} (s:aZ D b x⊆{u}) (l:3<=(af 14 D x).card) (g:C (bU j) x:=by decide):aZ D b x={u}:=_eqc s (by have:=_cp.2 (w.pn x l g);rw[_cs];omega)
lemma cut (x t i q:O) (n:(aZ D b x).Nonempty) (s:aZ D b x⊆aZ D b t) (g:C (bU j) x/\CG (bU j) x t i q:=by decide):False:=orb49_cut w.h w.r w.z w.b x t i q (w.I▸g.1) (w.I▸g.2.1) g.2.2 n s
lemma l2 (x t i q:O) (s:aZ D b x⊆aZ D b t) (g:C (bU j) x/\CG (bU j) x t i q:=by decide):(af 14 D x).card<=2:=by by_contra k;exact w.cut x t i q (w.pn x (by omega) g.1) s g
lemma c2 {u:S0} (x t i q:O) (sx:aZ D b x⊆{u}) (st:aZ D b t⊆{u}) (n:(aZ D b x).Nonempty) (g:C (bU j) t/\C (bU j) x/\CG (bU j) x t i q:=by decide):(af 14 D t).card<=2:=w.pl t (_ee.2 fun _ k=>w.cut x t i q n (fun _ a=>((_ms.1 (sx a)).trans (_ms.1 (st k)).symm)▸k) g.2) g.1
lemma cx (x i k v:O) (g:C (bU j) x/\i∈bU j/\k∈bU j/\EG i k x v/\v∉dom i/\v∉dom k:=by decide):(aZ D b x).Nonempty:=w.pn x (cx_dom w.h w.r w.p (w.I▸g.2.1) (w.I▸g.2.2.1) g.2.2.2.1 (.inr g.2.2.2.2)) g.1
lemma dl0 (z k v iz ik:O) (a:(af 14 D z).card<=2) (c:(af 14 D k).card<=2) (g:DL (bU j) z k v iz ik:=by decide):False:=dl_dom w.h w.r w.p z k v iz ik (w.I▸g.1) (w.I▸g.2.1) g.2.2.1 g.2.2.2 a c
lemma dl (z k v iz ik:O) (a:(af 14 D z).card<=2) (g:DL (bU j) z k v iz ik:=by decide):3<=(af 14 D k).card:=by by_contra q;exact w.dl0 z k v iz ik a (by omega) g
lemma dl' (z k v iz ik:O) (c:(af 14 D k).card<=2) (g:DL (bU j) z k v iz ik:=by decide):3<=(af 14 D z).card:=by by_contra q;exact w.dl0 z k v iz ik (by omega) c g
lemma pt (i x:O) (s:(af 14 D x).card<=2) (g:i∈bU j/\E i x/\quOk i x=true:=by decide):∃ e,(∀ y,E x y->y∉dom i->e∈af 14 D y)/\am e∈af 14 D x/\∀ t,M i x t->t∉ag 14 D (aw D (am e))/\am e∉af 14 D t:=by
 obtain⟨f,-,F,N⟩:=qu_dom w.h w.r w.p (w.I▸g.1) (eP g.2.1) g.2.2 s
 refine⟨am f,fun y c d=>?_,by rw[aB,F];simp,fun t k=>by rw[aB];exact N t k⟩
 obtain⟨e,u,v,n,-⟩:=_U.bf w.h w.r w.p (eP c);rw[F,_mi,_ms] at u;exact u.resolve_left (fun k=>d (n i (w.I▸g.1) k))▸v
lemma peq (i x a t v:O) (c:(af 14 D x).card<=2) (d:(af 14 D a).card<=2) (g:i∈bU j/\E i x/\E x a/\a∉dom i/\E a t/\E a v/\M i x t/\M i x v:=by decide):∃ e,e∈af 14 D t/\e∈af 14 D v/\am e∈af 14 D a:=by
 obtain⟨k,m,n,q,s,u,y,z⟩:=g;obtain⟨l,A,-,N⟩:=w.pt i x c ⟨k,m,cmOk_quOk i x t y⟩
 obtain⟨e,h1,h2,-⟩:=w.bF a t s;obtain⟨f,h3,h4,-⟩:=w.bF a v u
 have:=(N t y).2;have:=(N v z).2;have:=gG (A a n q) h1 (by grind only) d f h3;exact⟨am e,h2,by grind only,by rwa[aB]⟩
lemma ed (y z:O) (g:E y z:=by decide):∃ d,d∈af 14 D y/\am d∈af 14 D z:=by obtain⟨d,a,c,-⟩:=w.bF y z g;exact⟨d,a,c⟩
lemma ep (i z y:O) (s:(af 14 D z).card<=2) (g:i∈bU j/\E i z/\quOk i z=true/\E z y/\y∉dom i:=by decide):∃ d,d∈af 14 D y/\am d∈af 14 D z:=by obtain⟨d,D',m,-⟩:=w.pt i z s ⟨g.1,g.2.1,g.2.2.1⟩;exact⟨d,D' y g.2.2.2.1 g.2.2.2.2,m⟩
lemma sh {u:S0} (x y q i c k d o' z:O) (zx:aZ D b x={u}) (zy:aZ D b y={u}) (l:3<=(af 14 D x).card) (m:3<=(af 14 D y).card) (s:(af 14 D c).card<=2) (t:(af 14 D d).card<=2) (e:∃ f,f∈af 14 D y/\am f∈af 14 D z) (g:C (bU j) x/\C (bU j) y/\i∈bU j/\k∈bU j/\o'∈bU j/\E i c/\E c x/\E c q/\x∉dom i/\q∉dom i/\E k d/\E d y/\y∉dom k/\E o' y/\d∉dom o'/\z∉dom o'/\c∉dom o'/\M k d z/\M i c d/\M i c z/\Y x y q:=by decide):False:=by
 obtain⟨h1,h2,h3,h4,h5,a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,b6,b7,m1,m2,m3,mv⟩:=g
 obtain⟨a,A,u,v⟩:=w.pt i c s ⟨h3,a1,cmOk_quOk _ _ _ m2⟩;obtain⟨f,F,n,q'⟩:=w.pt k d t ⟨h4,b1,cmOk_quOk _ _ _ m1⟩;obtain⟨r',g1,g2⟩:=e
 have T:=aT (w.aJ o' y ⟨h5,b4⟩) (F y b2 b3) g1 (w.ne o' n ⟨h5,b5⟩) (w.ne o' g2 ⟨h5,b6⟩) (fun e=>(q' z m1).2 (e▸g2)) (w.cap y zy h2)
 have N:a∉af 14 D y:=fun e=>by have:=T a e;have:=w.ne o' u ⟨h5,b7⟩;have:=(v d m2).2;have:=(v z m3).2;grind only
 obtain⟨P,K,pq,px,qx,py,qy⟩:=clean_shared_af_u w.h w.r w.b (w.I▸h1) (w.I▸h2) zx zy l m
 obtain⟨r,hr,k1,k2⟩:=bE_dom w.h.1 w.r mv
 have:=aT px qx (A x a2 a4) pq (fun e=>N (e▸py)) (fun e=>N (e▸qy)) (w.cap x zx h1) r hr
 have:=(ak.1 py).2.1;have:=(ak.1 qy).2.1;have:=(ak.1 (A q a3 a5)).2.1;grind only
lemma pf (x i k v:O) {u:S0} (hu:aZ D b x={u}) (g:(C (bU j) x/\i∈bU j/\k∈bU j/\dom i⊆bU j/\dom k⊆bU j)/\EG i k x v/\(k∉dom i/\i∉dom k/\v∉dom i/\v∉dom k):=by decide):∀ y∈ag 14 D u.1,(dj i y/\dj k y)\/(dj i y/\∀ q:O,E k q->mV x y q=false)\/(dj k y/\∀ q:O,E i q->mV x y q=false):=
 eF_cand_dom_u w.h w.r w.b w.p (w.I▸g.1.1) hu (w.I▸g.1.2.1) (w.I▸g.1.2.2.1) g.2.1 (.inr g.2.2.2.2) (dy_dom w.h w.r w.z w.p (w.I▸g.1.2.1) (w.I▸g.1.2.2.1) (w.I▸g.1.2.2.2.1) g.2.1 (.inr g.2.2.2.2) g.2.2.1 g.2.2.2.2.1 (w.cap x hu g.1.1)) (dy_dom w.h w.r w.z w.p (w.I▸g.1.2.2.1) (w.I▸g.1.2.1) (w.I▸g.1.2.2.2.2) (EGs g.2.1) (.inr ⟨g.2.2.2.2.2,g.2.2.2.2.1⟩) g.2.2.2.1 g.2.2.2.2.2 (w.cap x hu g.1.1))
lemma pfs {u v:S0} (k:aj 14 D b={u,v}) (x i c t:O) (S:o) (hu:aZ D b x={u}) (g:((C (bU j) x/\i∈bU j/\c∈bU j/\dom i⊆bU j/\dom c⊆bU j)/\EG i c x t/\(c∉dom i/\i∉dom c/\t∉dom i/\t∉dom c))/\∀ y∈S,EO x i c y:=by decide):∀ y∈S,aZ D b y⊆{v}:=fun y m=>
 pA k fun q=>by have h':=g.2 y m;simp only[EO,cW] at h';exact h' (w.pf x i c t hu g.1 y q)
lemma s35 {u v:S0} (uv:u≠v) (k:aj 14 D b={u,v}) (S:o) (K:∀ A B':S0,aj 14 D b={A,B'}->aZ D b 12={A}->aZ D b 13={B'}->(∀ y∈S,aZ D b y=∅)->False) (g0:C (bU j) 12/\C (bU j) 13/\(2:O)∈bU j/\(4:O)∈bU j/\(5:O)∈bU j/\dom 2⊆bU j/\dom 4⊆bU j/\dom 5⊆bU j:=by decide) (g:∀ y∈S,EO 12 2 5 y/\EO 13 2 4 y:=by decide):False:=by
 obtain⟨c1,c2,i2,i4,i5,d2,d4,d5⟩:=g0;have n1:=w.cx 12 2 5 3 ⟨c1,i2,i5,V,V⟩;have n2:=w.cx 13 2 4 1 ⟨c2,i2,i4,V,V⟩
 suffices L:∀ A B',aj 14 D b={A,B'}->aZ D b 12={A}->aZ D b 13={B'}->False by rcases dJ uv (k▸ps 12) (k▸ps 13) n1 n2 (fun s=>w.cut 12 13 5 9 n1 s ⟨c1,d5,V⟩) (fun s=>w.cut 13 12 4 11 n2 s ⟨c2,d4,V⟩) with ⟨a,c⟩|⟨a,c⟩;{exact L u v k a c};exact L v u (sw k) a c
 intro A B' r z1 z2;exact K A B' r z1 z2 fun y m=>_ee.2 fun t q=>by
  obtain⟨a,c⟩:=ay.1 q;rw[r,_mi,_ms] at a;have e:=g y m;simp only[EO,cW] at e
  rcases a with rfl|rfl;{exact e.1 (w.pf 12 2 5 3 z1 ⟨⟨c1,i2,i5,d2,d5⟩,V⟩ y c)};exact e.2 (w.pf 13 2 4 1 z2 ⟨⟨c2,i2,i4,d2,d4⟩,V⟩ y c)
end
end W
lemma r5 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) {j:Fin 68} (hI:aa 14 D=bU j) (T J S:o) (L:List (O×O×O×O)) (K:∀ {p},bA_dom D p->(∀ y∈S,(af 14 D y).card<=2)->False)
 (G1:(bU j).card=5/\kL_dom T J=true/\J⊆bU j/\(∀ y∈S,C (bU j) y)/\∀ x∈T,∃ q∈L,q.1=x:=by decide +kernel)
 (G2:∀ q∈L,C (bU j) q.1/\q.2.1∈J/\q.2.2.1∈J/\dom q.2.1⊆bU j/\dom q.2.2.1⊆bU j/\EG q.2.1 q.2.2.1 q.1 q.2.2.2:=by decide +kernel)
 (G3:∀ q∈L,(q.2.2.1∉dom q.2.1/\q.2.1∉dom q.2.2.1/\q.2.2.2∉dom q.2.1/\q.2.2.2∉dom q.2.2.1)/\∀ y∈S,EO q.1 q.2.1 q.2.2.1 y:=by decide +kernel):False:=by
 obtain⟨c,k,s,y,m⟩:=G1
 by_cases a:bd 14 D<=(al 14 D).card;{exact dn h r h12 a j hI}
 by_cases d:bd 14 D=(al 14 D).card+1;{exact dp h r h12 d j (by omega) hI}
 have:=aV 14 D;rw[hI,c] at this;have:=bg 14 D;have J':J⊆aa 14 D:=hI▸s;have:=lO_dom h r (by omega) k J'
 obtain⟨b,u⟩:=b_dom h.1 r;obtain⟨p,q⟩:=bQ_dom h r;obtain⟨l,f⟩:=o4_dom h r (by omega) (by omega) u q k J'
 let w:W D b p j:=⟨h,r,by omega,u,q,hI⟩
 refine K q fun t n=>w.pl t (_ee.2 fun z g=>?_) (y t n)
 obtain⟨v,e⟩:=ay.1 g;obtain⟨x,z'⟩:=f z v;rw[_mn] at z'
 have xu:aZ D b x={z}:=(_eqc (_ss.2 (ay.2 ⟨v,z'.1⟩)) (by have a:=fC v z'.1;have:0<((al 14 D).filter fun o'=>x∈ag 14 D (b o')).card:=_cp.2 ⟨x,_mf.2 ⟨a,(u x a).2.1⟩⟩;have i:=ez_dom h r u x;rw[(l x z'.2).2,_ce] at i;have:=(l x z'.2).1;rw[_cs];omega)).symm
 obtain⟨⟨x',i,o',v'⟩,a,rfl⟩:=m x z'.2;obtain⟨c1,c2,c3,c4,c5,c6⟩:=G2 _ a;obtain⟨c7,c8⟩:=G3 _ a
 have e':=c8 t n;simp only[EO,cW] at e';exact e' (w.pf x' i o' v' xu ⟨⟨c1,s c2,s c3,c4,c5⟩,c6,c7⟩ t e)
end _4
section
open _4
lemma orb_39 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨39,V⟩):False:=dz4 h r h12 hI 8 10 0 2 6 0 4 5 1 13 9 7 2 2 12 4 11
lemma orb_50 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨50,V⟩):False:=dz4 h r h12 hI 6 11 8 9 11 3 4 6 2 12 13 8 3 8 0 3 7
lemma orb_51 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨51,V⟩):False:=dz4 h r h12 hI 0 7 8 10 7 1 3 0 2 12 13 8 3 8 2 1 9
lemma orb_48 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨48,V⟩):False:=dz4 h r h12 hI 1 8 7 9 13 0 2 6 3 12 11 7 2 9 5 2 12
lemma orb_61 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨61,V⟩):False:=r5 h r h12 hI {11,12,13} {2,3,4} {1,7} [(11,3,4,6),(12,2,3,5),(13,2,4,1)] fun q l=>dl_dom h r q 1 7 13 9 3 (hI▸V) (hI▸V) V V (l 1 V) (l 7 V)
lemma orb_53 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨53,V⟩):False:=r5 h r h12 hI {9,12,13} {1,2,5} {3,7,11} [(9,1,5,6),(12,2,5,3),(13,1,2,4)] fun q l=>fR_dom h r q 3 11 7 12 4 1 (hI▸V) (hI▸V) V V (l 3 V) (l 11 V) (l 7 V)
lemma orb_38 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨38,V⟩):False:=r4 h r h12 hI fun w _ _ n k=>by
 have a:=w.cx 9 5 6 1;have c:=w.cx 11 4 6 3;have d:=w.cx 12 2 5 3
 exact dJ3 n k a c d (w.cut 9 11 5 12 a) (w.cut 11 9 4 13 c) (fun _ x y=>w.cut 9 12 6 11 a (by rw[x,y])) (fun _ x y=>w.cut 11 12 4 10 c (by rw[x,y])) fun y=>w.cut 9 12 6 11 a (by rw[y,<-k];exact ps 9)
lemma orb_35 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨35,V⟩):False:=r4 h r h12 hI fun w _ _ n k=>w.s35 n k {1,3,7,9,11} fun _ _ _ _ z e=>by
 obtain⟨x,a,c,d⟩:=w.peq 5 9 1 7 13 (w.pl 9 (e 9 V)) (w.pl 1 (e 1 V))
 obtain⟨f,g,m,-⟩:=w.peq 4 11 3 7 12 (w.pl 11 (e 11 V)) (w.pl 3 (e 3 V))
 obtain⟨s,t,u,v⟩:=bE_dom h.1 r (V:Y 7 12 13)
 have:f=x:=(gG t a (fun q=>v (q▸(ak.1 c).2.1)) (w.pl 7 (e 7 V)) f g).resolve_left fun q=>u (q▸(ak.1 m).2.1)
 obtain⟨s,t,q,l⟩:=bE_dom h.1 r (V:Y 13 12 11)
 have:=aT (w.aJ 2 13) (w.aJ 4 13) c (fun q=>(V:(2:O)≠4) (w.p.2 (hI▸V) (hI▸V) q)) (w.ne 2 d) (w.ne 4 d) (w.cap 13 z) s t
 have:=(ak.1 (w.aJ 2 12)).2.1;have:=(ak.1 (w.aJ 4 11)).2.1;have:=(ak.1 m).2.1;grind only
lemma orb_41 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨41,V⟩):False:=r4 h r h12 hI fun {b _} w _ _ n k=>w.s35 n k {6,9} fun A K q y z e=>by
 have a:=w.cx 10 4 5 0
 have c:aZ D b 10={A,K}:=by rcases pp (q▸ps 10) a with d|d|d;{exact (w.cut 10 12 4 11 a (by rw[d,y])).elim};{exact (w.cut 10 13 5 9 a (by rw[d,z])).elim};exact d
 exact fR_dom h r w.p 6 8 9 11 2 5 (hI▸V) (hI▸V) V V (w.pl 6 (e 6 V)) (w.l2 8 10 2 12 (by rw[c,<-q];exact ps 8)) (w.pl 9 (e 9 V))
lemma orb_44 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨44,V⟩):False:=r4 h r h12 hI fun {b _} w u v n k=>by
 suffices K:∀ U X,aj 14 D b={U,X}->aZ D b 10={U}->False by
  have a:=w.cx 10 4 5 0;rcases pp (k▸ps 10) a with e|e|e;{exact K u v k e};{exact K v u (sw k) e}
  have s (x:O):aZ D b x⊆aZ D b 10:=by rw[e,<-k];exact ps x
  have c:=w.l2 2 10 8 6 (s 2);have d:=w.l2 6 10 8 2 (s 6)
  have f:=w.dl 6 9 11 8 5 d;have g:=w.dl 6 11 9 8 4 d;have l:=w.dl 2 12 13 8 5 c
  have m:=w.pn 9 f;have q:=w.pn 11 g
  exact dJ3 n k m q (w.pn 12 l) (w.cut 9 11 5 12 m) (w.cut 11 9 4 13 q) (fun _ x y=>w.sh 9 12 11 8 6 8 2 5 3 x y f l d c (w.ed 12 3)) (fun _ x y=>w.cut 11 12 4 10 q (by rw[x,y])) fun y=>w.cut 10 12 4 11 a (by rw[e,y])
 intro U X q y;have s:=w.pfs q 10 4 5 0 {2,6,9,11,12,13} y
 have a:3<=(af 14 D 2).card:=by by_contra z;have c:=w.dl 2 12 13 8 5 (by omega);exact w.cut 12 13 5 9 (w.pn 12 c) (by rw[w.eqs 12 (s 12 V) c,w.eqs 13 (s 13 V) (w.dl 2 13 12 8 4 (by omega))])
 have c:3<=(af 14 D 6).card:=by by_contra z;have d:=w.dl 6 9 11 8 5 (by omega);exact w.cut 9 11 5 12 (w.pn 9 d) (by rw[w.eqs 9 (s 9 V) d,w.eqs 11 (s 11 V) (w.dl 6 11 9 8 4 (by omega))])
 have d:=w.pn 2 a
 exact w.sh 2 6 3 5 12 5 9 8 11 (w.eqs 2 (s 2 V) a) (w.eqs 6 (s 6 V) c) a c (w.c2 2 12 8 0 (s 2 V) (s 12 V) d) (w.c2 2 9 8 0 (s 2 V) (s 9 V) d) (w.ep 4 11 6 (w.c2 2 11 8 0 (s 2 V) (s 11 V) d))
lemma orb_45 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨45,V⟩):False:=r4 h r h12 hI fun {b _} w u v n k=>by
 suffices K:∀ U X,aj 14 D b={U,X}->aZ D b 12={U}->False by
  have a:=w.cx 12 2 3 5;rcases pp (k▸ps 12) a with e|e|e;{exact K u v k e};{exact K v u (sw k) e}
  have s (x:O):aZ D b x⊆aZ D b 12:=by rw[e,<-k];exact ps x
  have c:=w.l2 1 12 9 6 (s 1);have d:=w.l2 6 12 9 1 (s 6)
  have f:=w.dl 1 7 13 9 3 c;have g:=w.dl 6 11 8 9 3 d;have l:=w.dl 1 13 7 9 2 c
  have m:=w.pn 7 f;have q:=w.pn 11 g;have t:=w.pn 13 l
  exact dJ3 n k m t q (w.cut 7 13 3 11 m) (w.cut 13 7 2 12 t) (fun _ x y=>w.sh 7 11 13 9 1 9 6 3 4 x y f g c d (w.ed 11 4)) (fun _ x y=>w.cut 11 13 3 7 q (by rw[y,x])) fun y=>w.cut 12 11 2 8 a (by rw[e,y])
 intro U X q y;have s:=w.pfs q 12 2 3 5 {1,6,11,13} y
 have c:(af 14 D 13).card<=2:=by by_contra z;have a:=w.pn 13 (by omega);exact w.dl0 6 11 8 9 3 (w.c2 13 6 2 12 (s 13 V) (s 6 V) a) (w.c2 13 11 2 12 (s 13 V) (s 11 V) a)
 have d:(af 14 D 11).card<=2:=by by_contra z;exact w.dl0 1 13 7 9 2 (w.c2 11 1 3 12 (s 11 V) (s 1 V) (w.pn 11 (by omega))) c
 have f:=w.dl' 1 13 7 9 2 c;have g:=w.dl' 6 11 8 9 3 d
 exact w.sh 1 6 4 2 13 3 11 9 8 (w.eqs 1 (s 1 V) f) (w.eqs 6 (s 6 V) g) f g c d (w.ed 6 8)
lemma orb_49 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨49,V⟩):False:=r4 h r h12 hI fun {b p} w u v n k=>by
 let I:=bU ⟨49,V⟩;have i7:(7:O)∈aa 14 D:=hI▸V;have i9:(9:O)∈aa 14 D:=hI▸V;have c:=w.cx 13 2 4 1
 have l:(aZ D b 1).Nonempty:=by
  have:=cx_dom h r w.p (u:=1) (v:=13) i9 i7 V (.inr V);by_contra z;rw[not_nonempty_iff_eq_empty] at z
  exact no_leak_2nbrs h r w.z w.b w.p (x:=1) (v3:=13) (not_not.1 (mt aN.2 (hI▸(V:(0:O)∉bU ⟨49,V⟩)))) V V z i9 i7 V V V V V V (.inr V) V fun x=>by have:=bj_noleak h r w.b (x:=1) (fun _ _=>x);rw[z,_ce] at this;omega
 suffices K:∀ A K:S0,A≠K->aj 14 D b={A,K}->aZ D b 13={A}->False by
  rcases pp (k▸ps 13) c with e|e|e;{exact K u v n k e};{exact K v u n.symm (sw k) e}
  have d:=w.pn 8 (w.dl 6 8 11 9 2 (w.l2 6 13 9 5 (by rw[e,<-k];exact ps 6)))
  have f:=w.pn 10 (w.dl 5 10 12 9 4 (w.l2 5 13 9 6 (by rw[e,<-k];exact ps 5)))
  obtain⟨a,m⟩:=l;have q:=(ay.1 m).1;rw[k,_mi,_ms] at q
  rcases dJ n (k▸ps 8) (k▸ps 10) d f (w.cut 8 10 2 13 d) (w.cut 10 8 4 13 f) with ⟨x,y⟩|⟨x,y⟩ <;> rcases q with rfl|rfl <;> first | exact w.cut 8 1 2 12 d (x▸_ss.2 m) | exact w.cut 10 1 4 11 f (y▸_ss.2 m)
 intro A K d R z
 have s:=w.pfs R 13 2 4 1 {0,1,5,6} z;have z1:aZ D b 1={K}:=_eqc (s 1 V) (by rw[_cs];exact _cp.2 l)
 have B' (t o' u x v i j:O) (g1:C I t/\CG I t 1 i v/\C I u/\CG I u t 9 x/\C I o'/\CG I o' t j 13:=by decide) (g2:DL I x o' v 9 j/\C I x/\E u t/\t∉dom 9/\Q v 1/\x∈({0,1,5,6}:o):=by decide):aZ D b t⊆{A}:=pA (sw R) fun m=>by
  obtain⟨c1,f1,c2,f2,c3,f3⟩:=g1;obtain⟨d',c4,u1,t9,v1,xm⟩:=g2;have⟨_,_,a,_,_,q⟩:=f2;have⟨_,_,_,⟨g1,_,_,g2,_⟩⟩:=d'
  have m':K∈aZ D b t:=ay.2 ⟨R▸by simp,m⟩
  have e:aZ D b t={A,K}:=by rcases pp (R▸ps t) ⟨K,m'⟩ with y|y|y;{exact (d.symm (_ms.1 (y▸m'))).elim};{exact (w.cut t 1 i v ⟨K,m'⟩ (by rw[y,z1]) ⟨c1,f1⟩).elim};exact y
  have y:=w.dl' x o' v 9 j (w.l2 o' t j 13 (by rw[e,<-R];exact ps o') ⟨c3,f3⟩) d';have zx:=w.eqs x (s x xm) y c4
  have f:=lQ_dom h r w.z w.p i9 (hI▸V) (eP a) (eP u1) t9 (w.l2 u t 9 x (by rw[e,<-R];exact ps u) ⟨c2,f2⟩)
  obtain⟨P,J,n',N1,N2,F⟩:=dV_dom h r w.b (hI▸c4) zx y;have:=F 1 (ay.1 (z1▸_mss K)).2;obtain⟨a',y'⟩:=F t m
  obtain⟨f',hf,fn⟩:=kb_dom h.1 r ⟨v,g2,v1⟩
  have:=aT N1 N2 (w.aJ 9 x ⟨V,g1⟩) n' (fun k=>b3.1 q (f t (k▸a'))) (fun k=>b3.1 q (f t (k▸y'))) (w.cap x zx c4) f' hf
  have:=(ak.1 (w.aJ 9 1)).2.1;grind only
 have z8:=B' 8 10 6 5 12 2 4;have z0:=B' 10 8 5 6 11 4 2
 have s0:(af 14 D 0).card<=2:=by
  by_contra q;have z':=w.eqs 0 (s 0 V) (by omega)
  have a:=w.dl 6 8 11 9 2 (w.l2 6 0 9 1 (z'▸s 6 V))
  exact w.cut 8 10 2 13 (w.pn 8 a) (by rw[w.eqs 8 z8 a,w.eqs 10 z0 (w.dl 5 10 12 9 4 (w.l2 5 0 9 1 (z'▸s 5 V)))])
 have f (k i:O) (q:aZ D b k⊆{A}) (m:am (p 7)∈af 14 D k) (g:C I k/\i∈I/\E i k/\E i 13/\M i k 7/\Y k 13 7:=by decide):False:=by
  obtain⟨g1,g2,g3,g4,g5,g6⟩:=g;have n':(13:O)∉ag 14 D (aw D (am (p 7))):=fun y=>absurd ((w.p.1 7 i7).2.2.2.2.2.1 y) V
  by_cases c':(af 14 D k).card<=2
  ;{obtain⟨y,-,t,o'⟩:=qu_dom h r w.p (hI▸g2) (eP g3) (cmOk_quOk i k 7 g5) c'
    rw[t,_mi,_ms] at m;rcases m with e|e;{exact n' (e▸(ak.1 (w.aJ i 13 ⟨g2,g4⟩)).2.1)};exact (o' 7 g5).1 (e▸cd w.p i7)}
  have c':3<=(af 14 D k).card:=(by omega);have t:=w.eqs k q c' g1
  obtain⟨P,J,u',v',x',y'⟩:=dV_dom h r w.b (hI▸g1) t c';obtain⟨a,c⟩:=y' 13 (ay.1 (z▸_mss A)).2;obtain⟨e,d',k1,k2⟩:=bE_dom h.1 r g6
  have:=aT v' x' m u' (fun y=>n' (y▸a)) (fun y=>n' (y▸c)) (w.cap k t g1) e d';have:=cd w.p i7;grind only
 obtain⟨e,a,c,-⟩:=w.bF 0 8;obtain⟨g,t,y,-⟩:=w.bF 0 10
 obtain rfl:g=e:=(gG (w.aJ 7 0) a (fun q=>f 8 2 z8 (q.symm▸c)) s0 g t).resolve_left fun q=>f 10 4 z0 (q▸y)
 have m (k t i:O) (a':am g∈af 14 D k) (c':am g∈af 14 D t) (g':i∈I/\E i k/\M i k t/\(0:O)∉dom i:=by decide):3<=(af 14 D k).card:=by
  obtain⟨g1,g2,g3,g4⟩:=g';by_contra q;obtain⟨x,-,t',o'⟩:=qu_dom h r w.p (hI▸g1) (eP g2) (cmOk_quOk i k t g3) (by omega)
  rw[t',_mi,_ms] at a';rcases a' with d'|d';{exact g4 (em_dom w.p (hI▸g1) ((by rw[<-d',aB]:g=am (p i))▸a))};exact (o' t g3).2 (d'▸c')
 have q:=w.eqs 8 z8 (m 8 10 2 c y);exact w.cut 8 10 2 13 (q▸⟨_,_mss _⟩) (by rw[q,w.eqs 10 z0 (m 10 8 4 y c)])
lemma orb_40 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨40,V⟩):False:=r4 h r h12 hI fun {b p} w u v n k=>by
 let I:=bU ⟨40,V⟩;let S:o:={1,3,9,11,12,13};have a:=w.cx 10 4 5 0;obtain⟨k0,k7⟩:=cT_07_uncond w.p (hI▸V) (hI▸V)
 have T (y) (m:y∈S):¬aZ D b 10⊆aZ D b y:=by obtain⟨i,q,g⟩:=(show ∀ y∈S,∃ i q:O,CG I 10 y i q by decide) y m;exact w.cut 10 y i q a (g:=⟨V,g⟩)
 have A':=w.dl 1 9 13 7 5;have E':=w.dl 3 11 12 7 4;have F':=w.dl 3 12 11 7 5
 suffices K:∀ A K,aj 14 D b={A,K}->aZ D b 10={A}->False by
  rcases pp (k▸ps 10) a with e|e|e;{exact K u v k e};{exact K v u (sw k) e}
  have z:aZ D b 10=aj 14 D b:=e.trans k.symm
  have o' (x y:O) (g:E 7 x/\E x y/\x≠10/\(10:O)∉dom x/\Q 10 y/\y∉dom 7/\C I x/\∀ i∈({0,4,5}:o),y∉dom i/\Q i x/\(i≠0->x∉dom i):=by decide):(af 14 D x).card<=2:=by
   obtain⟨c,d,f,l,m,q,s,g2⟩:=g;by_contra! t;obtain⟨u',hu⟩:=w.pn x t s
   obtain⟨v',hv⟩:=jx_dom h r w.b (fC (ay.1 hu).1 (ay.1 hu).2) (hI▸s) f l (z▸ps x) ⟨u'.1,(ay.1 hu).2,(ay.1 ((z▸ps x) hu)).2⟩ ⟨y,d,m⟩
   obtain rfl:p 7=v':=by by_contra i;exact (V:¬dj 7 10) (k7 10 (hv _ (w.aJ 7 x ⟨V,c⟩) i))
   obtain⟨e',ex,ey,ny,-⟩:=w.bF x y d;have et:=hv e' ex fun i=>q (ny 7 (hI▸V) i)
   let J:o:={0,4,5};let U:=((af 14 D 10).image Prod.fst)∪(aW 14 D (ao 14 D {10}))
   have s' {a:O} (f:ℕ×_d) (ha:f∈af 14 D a) (ht:(10:O)∈ag 14 D (aw D f)):f.1∈U:=by
    by_cases i:(10:O)∈ag 14 D (14+f.1);{obtain⟨c1,c2⟩:=_mn.1 (cB h.1 (ak.1 ha).1 (cY h.1 ha)▸i);exact _mu.2 (.inr (_mf.2 ⟨mem_range.2 (ak.1 ha).1,b7.2 i,b7.2 c1,b7.2 c2⟩))}
    exact _mu.2 (.inl (_mg.2 ⟨f,ak.2 ⟨(ak.1 ha).1,ht,i⟩,rfl⟩))
   have ji:J⊆aa 14 D:=hI▸V;have jg:∀ i∈J,aP i 10/\(10:O)∉dom i:=V
   have jp (i) (i':i∈J):p i∈af 14 D 10:=_U.aJ w.p (ji i') (jg i i').1
   have jq (i) (i':i∈J) (f:ℕ×_d) (ht:(10:O)∈ag 14 D (aw D f)) (t':f.1=(p i).1):f=p i:=(eq_or_am t').resolve_right fun y'=>(jg i i').2 ((w.p.1 i (ji i')).2.2.2.2.2.1 (y'▸ht))
   have se:U=insert e'.1 (J.image (fun i=>(p i).1)):=(_eqc (insert_subset (s' e' ex et) fun _ m=>by obtain⟨i,j,rfl⟩:=_mg.1 m;exact s' _ (jp i j) (ak.1 (jp i j)).2.1) (by have:U.card<=4:=(card_union_le _ _).trans (Nat.add_le_add_right card_image_le _ |>.trans (by have:=B h r w.b (by rw[hI];exact (V:C I 10));rw[z,k,_c2 n] at this;omega));rw[_cin fun m=>by obtain⟨i,j,t'⟩:=_mg.1 m;exact (g2 i j).1 (ny i (ji j) (jq i j _ et t'.symm)),_cij fun i a' j c' t'=>w.p.2 (ji a') (ji c') (jq j c' _ (ak.1 (jp i a')).2.1 t'),show J.card=3 from V];omega)).symm
   have F {a:O} (f:ℕ×_d) (ha:f∈af 14 D a) (ht:(10:O)∈ag 14 D (aw D f)):(f=e'\/f=am e')\/∃ i∈J,f=p i:=by
    have i:=s' f ha ht;rw[se,_mi] at i;rcases i with i|i;{exact .inl (eq_or_am i)};obtain⟨i,j,t'⟩:=_mg.1 i;exact .inr ⟨i,j,jq i j f ht t'.symm⟩
   have cp (i) (j:i∈J):x∉ag 14 D (aw D (p i)):=by
    by_cases z':i=0;{subst i;exact fun i=>b3.1 (g2 0 j).2.1 (k0 _ i)}
    have d':dom i={i}:=dom_eq_self z' ((V:∀ y∈J,y≠7) i j)
    refine fun i'=>b3.1 (g2 i j).2.1 (cT_dom h r w.z w.p (ji j) (d'▸_ss.2 (ji j)) (jg i j).1 (fun f hf hn hs=>?_) x i')
    rcases F f hf (ak.1 hf).2.1 with (rfl|rfl)|⟨y',a',rfl⟩;{exact (g2 i j).1 (hs (ak.1 ey).2.1)};{exact (g2 i j).2.2 z' (hs (by rw[aB];exact (ak.1 ex).2.1))}
    have i':=hs (cd w.p (ji a'));rw[d',_ms] at i';exact hn (i'▸rfl)
   have:=(_cl (fun f hf=>by by_cases f7:f=p 7;{exact _mi.2 (.inl f7)};rcases F f hf (hv f hf f7) with (rfl|rfl)|⟨i,j,rfl⟩;{simp};{exact (el h.1 ex hf).elim};exact (cp i j (ak.1 hf).2.1).elim:af 14 D x⊆{p 7,e'})).trans card_le_two;omega
  have l1:=o' 1 9;have l3:=o' 3 11;have H:=E' l3;have j:=A' l1;have c:=F' l3
  suffices N:∀ U X,aj 14 D b={U,X}->aZ D b 11={U}->False by rcases pp (k▸ps 11) (w.pn 11 H) with f|f|f;{exact N u v k f};{exact N v u (sw k) f};exact T 11 V (by rw[e,f])
  intro U X q z1
  exact w.sh 9 12 13 7 1 7 3 5 2 (pB q z1 (w.pn 9 j) (w.cut 11 9 4 13 (w.pn 11 H))) (pB q z1 (w.pn 12 c) (w.cut 11 12 4 13 (w.pn 11 H))) j c l1 l3 (w.ed 12 2)
 intro A K q y
 have z (y') (m:y'∈S) (l:3<=(af 14 D y').card):aZ D b y'={K}:=pB q y (w.pn y' l ((show ∀ x∈S,C I x by decide) y' m)) (T y' m)
 have c:3<=(af 14 D 1).card:=by by_contra i;have j:=A' (by omega);exact w.cut 9 13 5 12 (w.pn 9 j) (by rw[z 9 V j,z 13 V (w.dl 1 13 9 7 4 (by omega))])
 have d:3<=(af 14 D 3).card:=by by_contra i;have j:=E' (by omega);exact w.cut 11 12 4 13 (w.pn 11 j) (by rw[z 11 V j,z 12 V (F' (by omega))])
 have s (y') (m:y'∈({9,11,12}:o)):(af 14 D y').card<=2:=by
  by_contra e;obtain⟨g1,g2,g3,g4,g5,g6⟩:=(show ∀ y∈({9,11,12}:o),y∈S/\y∉dom 1/\E 7 1/\E 7 0/\Y 1 y 0/\Q 7 y by decide) y' m
  exact b3.1 g6 (k7 y' (cy_dom h r w.b w.p (hI▸V) (hI▸V) (by rw[z 1 V c,z y' g1 (by omega)]) (w.pn 1 c) g2 ⟨g3,g4,g5⟩))
 exact w.sh 1 3 6 5 9 4 11 7 12 (z 1 V c) (z 3 V d) c d (s 9 V) (s 11 V) (w.ep 5 12 3 (s 12 V))
lemma orb_56 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨56,V⟩):False:=by
 obtain⟨b,c⟩:=b_dom h.1 r;obtain⟨p,q⟩:=bQ_dom h r;let I:=bU ⟨56,V⟩;let K:o:={9,11,12,13};let J:o:={2,4,5,6};have s:J⊆aa 14 D:=hI▸V
 have l (x) (m:x∈K):C (aa 14 D) x:=hI▸(show ∀ x∈K,C I x by decide) x m
 have n {x} (m:x∈K):(aZ D b x).Nonempty:=by
  obtain⟨i,a,j,d,v,e,f⟩:=(show ∀ x∈K,∃ i∈J,∃ j∈J,∃ v:O,EG i j x v/\v∉dom i/\v∉dom j by decide +kernel) x m
  exact _cp.1 (by have:=cx_dom h r q (s a) (s d) e (.inr f);have:=B h r c (l x m);omega)
 have a:=aV 14 D;rw[hI,show I.card=5 from V] at a;have:=bS_dom h.1 c;have:=bg 14 D
 by_cases z:bL 14 D=0
 ;{obtain⟨R,t,u⟩:=Infinite.exists_superset_card_eq (aj 14 D b) 3 (by omega)
   have f {x y} (g:x∈K) (m:y∈K) (d:x≠y) (e:aZ D b x⊆aZ D b y):False:=by
    obtain⟨i,v,w,y'⟩:=(show ∀ x∈K,∀ y∈K,x≠y->∃ i q:O,CG I x y i q by decide +kernel) x g y m d
    exact orb49_cut h r z c x y i v (l x g) (hI▸w) y' (n g) e
   rcases gI u ((ps 9).trans t) ((ps 11).trans t) ((ps 12).trans t) ((ps 13).trans t) with y|y|y|y|y|y|y|y|y|y|y|y <;> exact f V V V y}
 by_cases y:bd 14 D<=(al 14 D).card;{exact dn h r h12 y _ hI}
 by_cases o':bd 14 D=(al 14 D).card+1;{exact dp h r h12 o' _ V hI}
 have d:(aj 14 D b).card=2:=(by omega);obtain⟨u,w,e,k⟩:=_ct2.1 d
 let F a b' a1 a2 q1 q2 b1 b2 v h1 h2 h3 h4 h5 h6 g1 g2 g3 t:=fa_dom h r c q a b' a1 a2 q1 q2 b1 b2 v (l a h1) (l b' h2) (s h3) (s h4) (s h5) (s h6) g1 g2 g3 (n h1) t (d▸_cl (ps b'))
 have g {t:S0} (a b' j m c1 c2 v:O) (x:aZ D b a={t}) (y:aZ D b b'={t}) (z:a∈K/\b'∈K/\j∈J/\c1∈J/\c2∈J/\j≠c1/\j≠c2/\c1≠c2/\b'∉dom a/\b'∉dom j/\E j a/\E j m/\Y a b' m/\E c1 b'/\E c2 b'/\E b' v/\v∉dom j/\v∉dom c1/\v∉dom c2:=by decide):False:=by
  obtain⟨h1,h2,h3,h4,h5,d1,d2,d3,n1,n2,j1,j2,m1,e1,e2,bv,v1,v2,v3⟩:=z;obtain⟨f,hf,-,i,-⟩:=bf h r q (eP bv)
  let A {x y} (u:x∈J) (v:y∈J) (o':x≠y):p x≠p y:=fun g=>o' (q.2 (s u) (s v) g)
  let N {x} (u:x∈J) (o':v∉dom x):p x≠f:=fun g=>o' (i x (s u) g.symm)
  have:=mm (cV_dom q (s h3) (cy_dom h r c q (l a h1) (s h3) (by rw[x,y]) (n h1) n1 ⟨j1,j2,m1⟩) n2) (aJ q (s h4) (eP e1)) (aJ q (s h5) (eP e2)) hf (A h3 h4 d1) (A h3 h5 d2) (N h3 v1) (A h4 h5 d3) (N h4 v2) (N h5 v3)
  have:=B h r c (l b' h2);rw[y,_cs] at this;omega
 rcases dJ e (k▸ps 9) (k▸ps 13) (n V) (n V) (F 9 13 5 6 10 8 2 4 1 V V V V V V V V V) (F 13 9 2 4 8 10 5 6 1 V V V V V V V V V) with ⟨x,-⟩|⟨x,-⟩ <;>
 rcases dJ e (k▸ps 11) (k▸ps 12) (n V) (n V) (F 11 12 4 6 10 8 2 5 3 V V V V V V V V V) (F 12 11 2 5 8 9 4 6 3 V V V V V V V V V) with ⟨y,z'⟩|⟨y,z'⟩ <;> first | exact g 9 11 5 12 4 6 3 x y | exact g 9 12 6 11 2 5 3 x z'
end
lemma pc {n:ℕ} (D:Dag) (w:ℕ) (h:n+D.length<=w):ag n D w=∅:=by ext v;simp[ee,fs D (cl v) w h]
lemma kR {n:ℕ} {D:Dag} {P:Finset (Fin n)} {e:ℕ×_d} {j:ℕ} (h:ch n D P e=Sum.inr j):e.1=j/\(ag n D (n+e.1)∩P).Nonempty:=by
 unfold ch at h;split_ifs at h with a;exact⟨Sum.inr.inj h,nonempty_iff_ne_empty.mpr a⟩
lemma bz_unique_step {D:Dag} (e:au 14 D) {a w u:ℕ} (hbz:bz 14 D a w) (hstep:bk 14 D a u) (hne:a≠w):u<=w/\bz 14 D u w:=by
 rcases Relation.ReflTransGen.cases_head hbz with rfl|⟨v,hv1,hv2⟩;{exact absurd rfl hne}
 obtain⟨j,s,hj,rfl,ha⟩:=fj.1 hstep;obtain⟨j',s',hj',rfl,ha'⟩:=fj.1 hv1.1
 have hja:j∈bV D a:=_mf.2 ⟨mem_range.2 hj,by cases s;{rw[aX] at ha;exact Or.inl ha};{rw[bh] at ha;exact Or.inr ha}⟩
 have hja':j'∈bV D a:=_mf.2 ⟨mem_range.2 hj',by cases s';{rw[aX] at ha';exact Or.inl ha'};{rw[bh] at ha';exact Or.inr ha'}⟩
 have heq:j=j':=card_le_one.1 (by show (bV D a).card<=1;have:=hv1.2;unfold aF at this;omega) j hja j' hja'
 subst heq;exact⟨dt e (fun _ _ q=>q.1) hv2,hv2⟩
lemma bz_chain_or {D:Dag} (e:au 14 D) {v w u:ℕ} (hbz:bz 14 D v w) (hp:Relation.ReflTransGen (bk 14 D) v u):bz 14 D u w\/Relation.ReflTransGen (bk 14 D) w u:=by
 induction hp using Relation.ReflTransGen.head_induction_on with
 | refl=>exact Or.inl hbz
 | @head a b hstep hp2 ih=>
  by_cases haw:a=w;{subst haw;exact Or.inr (Relation.ReflTransGen.head hstep hp2)}
  · obtain⟨-,hbz2⟩:=bz_unique_step e hbz hstep haw;exact ih hbz2
abbrev B3:=Bool×Bool×Bool
def q3S (p q:B3):Bool:=(!p.1||q.1)&&(!p.2.1||q.2.1)&&(!p.2.2||q.2.2)
def q3C (p:B3):ℕ:=p.1.toNat+p.2.1.toNat+p.2.2.toNat
def q3I (p q:B3):Bool:=p.1&&q.1||p.2.1&&q.2.1||p.2.2&&q.2.2
def q3Z (D:Dag) (b:O->ℕ) (u v w:Σ _:ℕ,ℕ) (x:O):B3:=(decide (u∈aZ D b x),decide (v∈aZ D b x),decide (w∈aZ D b x))
lemma q3s {D:Dag} {b:O->ℕ} {u v w:Σ _:ℕ,ℕ} (e:aj 14 D b={u,v,w}) {x y:O} (h:q3S (q3Z D b u v w x) (q3Z D b u v w y)=true):aZ D b x⊆aZ D b y:=by
 intro t ht;have:=(ay.1 ht).1;rw[e,_mi,_mi,_ms] at this;simp only[q3S,q3Z,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not] at h
 rcases this with rfl|rfl|rfl;{exact h.1.1.resolve_left (not_not.2 ht)};{exact h.1.2.resolve_left (not_not.2 ht)};{exact h.2.resolve_left (not_not.2 ht)}
lemma q3c {D:Dag} {b:O->ℕ} {u v w:Σ _:ℕ,ℕ} (e:aj 14 D b={u,v,w}) (d:u≠v/\u≠w/\v≠w) (x:O):(aZ D b x).card=q3C (q3Z D b u v w x):=by
 unfold aZ;rw[e,filter_insert,filter_insert,filter_singleton];simp only[q3C,q3Z];obtain⟨d1,d2,d3⟩:=d
 by_cases a:x∈ag 14 D u.1 <;> by_cases c:x∈ag 14 D v.1 <;> by_cases f:x∈ag 14 D w.1 <;> simp[a,c,f,aZ,e,d1,d2,d3]
lemma q3i {D:Dag} {b:O->ℕ} {u v w:Σ _:ℕ,ℕ} {x y:O} (h:q3I (q3Z D b u v w x) (q3Z D b u v w y)=true):∃ t,t∈aZ D b x/\t∈aZ D b y:=by
 simp only[q3I,q3Z,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h;rcases h with (h|h)|h <;> exact⟨_,h⟩
lemma q3g {α:Type} [DecidableEq α] {s:Finset α} {a b c d e:α} (h1:a∈s) (h2:b∈s) (h3:c∈s) (h4:d∈s) (h5:e∈s) (n1:a≠b) (n2:a≠c) (n3:a≠d) (n4:a≠e) (n5:b≠c) (n6:b≠d) (n7:b≠e) (n8:c≠d) (n9:c≠e) (n10:d≠e) (hm:s.card<=5):∀ x∈s,x=a\/x=b\/x=c\/x=d\/x=e:=by
 intro x hx;by_contra hn;simp only[not_or] at hn;have:=mn (s:=s.erase x) (_me.2 ⟨Ne.symm hn.1,h1⟩) (_me.2 ⟨Ne.symm hn.2.1,h2⟩) (_me.2 ⟨Ne.symm hn.2.2.1,h3⟩) (_me.2 ⟨Ne.symm hn.2.2.2.1,h4⟩) (_me.2 ⟨Ne.symm hn.2.2.2.2,h5⟩) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10;rw[card_erase_of_mem hx] at this;omega
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 0 in
lemma q62b:∀ a b c d:B3,1<=q3C a->1<=q3C b->1<=q3C c->1<=q3C d->q3S a d=false->q3S b d=false->q3S c d=false->q3S a b=false->q3S a c=false->q3S b a=false->q3S b c=false->q3S c a=false->q3S c b=false->q3S d a=false->(q3C d=1->q3I d b->q3I d c->q3C b<=2->q3C c<=2->False)->False:=by decide +kernel
lemma orb_62 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨62,V⟩):False:=by
 have hT:=aV 14 D;rw[hI,(by decide:(bU ⟨62,V⟩).card=5)] at hT
 by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 _ hI}
 by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 _ (by decide) hI}
 have hts:=bg 14 D;obtain⟨b,hb⟩:=b_dom h.1 r;obtain⟨pos,hp⟩:=bQ_dom h r;have hR:=bS_dom h.1 hb
 have m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,7,9}:o):=fun x=>by rw[hI];rfl
 have i0:(0:O)∈aa 14 D:=(m 0).2 (by decide);have i7:(7:O)∈aa 14 D:=(m 7).2 (by decide)
 have cl:∀ x:O,isClean (aa 14 D) x:=fun x=>by by_cases a:x=1\/x=3;{exact Or.inr (Or.inl ⟨a,i0⟩)};by_cases c:x=8\/x=10;{exact Or.inr (Or.inr ⟨c,i7⟩)};{left;push Not at a c;exact⟨a.1,a.2,c.1,c.2⟩}
 have c7:=cT_07_uncond hp i0 i7
 have i2:(2:O)∈aa 14 D:=(m 2).2 (by decide);have i4:(4:O)∈aa 14 D:=(m 4).2 (by decide);have i9:(9:O)∈aa 14 D:=(m 9).2 (by decide)
 have bc:∀ x,(af 14 D x).card<=2+(aZ D b x).card:=fun x=>by have:=bj_clean h r hb (cl x);omega
 have pn:∀ {i j:O},i∈aa 14 D->j∈aa 14 D->i≠j->pos i≠pos j:=fun a c d q=>d (hp.2 a c q)
 have ne:∀ {i y:O} {f:ℕ×_d},i∈aa 14 D->(∀ k∈aa 14 D,f=pos k->y∈dom k)->y∉dom i->pos i≠f:=fun a g n q=>n (g _ a q.symm)
 have Y:∀ {v t j q:O},j∈aa 14 D->aZ D b v⊆aZ D b t->(aZ D b v).Nonempty->ac j v=true->ac j q=true->mV v t q=true->t∉dom v->t∉dom j->pos j∈af 14 D t:=fun a s ne g1 g2 g3 n1 n2=>cV_dom hp a (cy_dom h r hb hp (cl _) a s ne n1 ⟨g1,g2,g3⟩) n2
 have n13:(aZ D b 13).Nonempty:=_cp.1 (by have:=cx_dom h r hp (u:=13) (v:=1) i2 i4 V (Or.inr V);have:=bc 13;omega)
 have n8:(aZ D b 8).Nonempty:=_cp.1 (by have:=cx_dom h r hp (u:=8) (v:=6) i0 i2 V (Or.inr V);have:=bc 8;omega)
 have n10:(aZ D b 10).Nonempty:=_cp.1 (by have:=cx_dom h r hp (u:=10) (v:=5) i0 i4 V (Or.inr V);have:=bc 10;omega)
 have n1:(aZ D b 1).Nonempty:=_cp.1 (by have:=cx_dom h r hp (u:=1) (v:=13) i7 i9 V (Or.inr V);have:=bc 1;omega)
 have k1:aZ D b 1⊆aZ D b 13->(aZ D b 1).Nonempty->False:=fun s n=>absurd (c7.2 13 (cy_dom h r hb hp (cl 1) i7 s n V (q:=0) V)) V
 have k8:aZ D b 8⊆aZ D b 13->(aZ D b 8).Nonempty->False:=fun s n=>absurd (c7.1 13 (cy_dom h r hb hp (cl 8) i0 s n V (q:=7) V)) V
 have k10:aZ D b 10⊆aZ D b 13->(aZ D b 10).Nonempty->False:=fun s n=>absurd (c7.1 13 (cy_dom h r hb hp (cl 10) i0 s n V (q:=7) V)) V
 rcases (by omega:(aj 14 D b).card=2\/(aj 14 D b).card=3) with a2|a3
 · have za:∀ x,aZ D b x⊆aj 14 D b:=fun x _ q=>(ay.1 q).1
   have zs:∀ x,(aZ D b x).card<=2:=fun x=>a2▸_cl (za x)
   have K:∀ u w:Σ _:ℕ,ℕ,aj 14 D b={u,w}->u∈aZ D b 13->w∉aZ D b 13->False:=by
    intro u w e z1 z2
    have mem:∀ {x y},y∈aZ D b x->y=u\/y=w:=fun hy=>by have:=(ay.1 hy).1;rwa[e,_mi,_ms] at this
    have sb:∀ x y,(u∈aZ D b x->u∈aZ D b y)->(w∈aZ D b x->w∈aZ D b y)->aZ D b x⊆aZ D b y:=fun x y p q z hz=>by rcases mem hz with rfl|rfl;{exact p hz};{exact q hz}
    have w1:w∈aZ D b 1:=by_contra fun c=>k1 (sb 1 13 (fun _=>z1) (fun q=>absurd q c)) n1
    have w8:w∈aZ D b 8:=by_contra fun c=>k8 (sb 8 13 (fun _=>z1) (fun q=>absurd q c)) n8
    have w10:w∈aZ D b 10:=by_contra fun c=>k10 (sb 10 13 (fun _=>z1) (fun q=>absurd q c)) n10
    have u1:u∉aZ D b 1:=fun c=>by
     have s:=sb 13 1 (fun _=>c) (fun q=>absurd q z2);obtain⟨f,hf,-,hg,-⟩:=bf h r hp (by decide:aP 1 13)
     have:=mn (aJ hp i7 (by decide:aP 7 1)) (aJ hp i9 (by decide:aP 9 1)) (Y (q:=12) i2 s n13 V V V V V) (Y (q:=11) i4 s n13 V V V V V) hf (pn i7 i9 V) (pn i7 i2 V) (pn i7 i4 V) (ne i7 hg V) (pn i9 i2 V) (pn i9 i4 V) (ne i9 hg V) (pn i2 i4 V) (ne i2 hg V) (ne i4 hg V)
     have:=bc 1;have:=zs 1;omega
    have s1:=fun x (wx:w∈aZ D b x)=>sb 1 x (fun c=>absurd c u1) (fun _=>wx)
    have E:∀ x j k (y:O) (f:ℕ×_d),x≠1->j∈aa 14 D->k∈aa 14 D->pos j∈af 14 D x->pos k∈af 14 D x->f∈af 14 D x->pos 9∈af 14 D x->(∀ i∈aa 14 D,f=pos i->y∈dom i)->pos j≠pos k->pos j≠f->pos k≠f->pos j≠pos 9->pos k≠pos 9->y∉dom 9->aZ D b x=aj 14 D b:=fun x j k y f _ _ _ a c d g hg p1 p2 p3 p4 p5 p6=>_eqc (za x) (by have:=mm a c d g p1 p2 p4 p3 p5 (ne i9 hg p6).symm;have:=bc x;omega)
    obtain⟨f8,hf8,-,hg8,-⟩:=bf h r hp (by decide:aP 8 6);obtain⟨f0,hf0,-,hg0,-⟩:=bf h r hp (by decide:aP 10 5)
    have e8:=E 8 0 2 6 f8 V i0 i2 (aJ hp i0 V) (aJ hp i2 V) hf8 (Y (q:=5) i9 (s1 8 w8) n1 V V V V V) hg8 (pn i0 i2 V) (ne i0 hg8 V) (ne i2 hg8 V) (pn i0 i9 V) (pn i2 i9 V) V
    have p9:=Y (q:=6) i9 (s1 10 w10) n1 V V V V V
    have e0:=E 10 0 4 5 f0 V i0 i4 (aJ hp i0 V) (aJ hp i4 V) hf0 p9 hg0 (pn i0 i4 V) (ne i0 hg0 V) (ne i4 hg0 V) (pn i0 i9 V) (pn i4 i9 V) V
    have:=mn (aJ hp i0 (by decide:aP 0 10)) (aJ hp i4 (by decide:aP 4 10)) p9 (Y (q:=12) i2 (by rw[e8,e0]) n8 V V V V V) hf0 (pn i0 i4 V) (pn i0 i9 V) (pn i0 i2 V) (ne i0 hg0 V) (pn i4 i9 V) (pn i4 i2 V) (ne i4 hg0 V) (pn i9 i2 V) (ne i9 hg0 V) (ne i2 hg0 V)
    have:=bc 10;have:=zs 10;omega
   obtain⟨u,w,uw,e⟩:=_ct2.1 a2;obtain⟨y,hy⟩:=n13;have:=(ay.1 hy).1;rw[e,_mi,_ms] at this
   rcases this with rfl|rfl
   · by_cases c:w∈aZ D b 13;{exact k1 (fun z hz=>by have:=(ay.1 hz).1;rw[e,_mi,_ms] at this;rcases this with rfl|rfl <;> assumption) n1};exact K _ _ e hy c
   · by_cases c:u∈aZ D b 13;{exact k1 (fun z hz=>by have:=(ay.1 hz).1;rw[e,_mi,_ms] at this;rcases this with rfl|rfl <;> assumption) n1};exact K _ _ (by rw[e,pair_comm]) hy c
 · have b0:bL 14 D=0:=by omega
   obtain⟨u,v,w,d1,d2,d3,e⟩:=card_eq_three.1 a3
   have zc:=q3c e ⟨d1,d2,d3⟩
   have hd:∀ {i:O},i∈aa 14 D->i≠0->i≠7->dom i⊆aa 14 D:=fun a n0 n7 x hx=>by simp only[dom,n0,n7,ite_false,_ms] at hx;rw[hx];exact a
   have h2:=hd i2 V V;have h4:=hd i4 V V;have h9:=hd i9 V V
   have N:∀ x,(aZ D b x).Nonempty->1<=q3C (q3Z D b u v w x):=fun x n=>by rw[<-zc];exact _cp.2 n
   have kc:∀ {x t:O} (i q:O),dom i⊆aa 14 D->(t∉dom x/\ac i x=true/\ac i q=true/\mV x t q=true/\bK i t=false)->(aZ D b x).Nonempty->q3S (q3Z D b u v w x) (q3Z D b u v w t)=false:=fun i q a g n=>Bool.eq_false_iff.2 fun s=>orb49_cut h r b0 hb _ _ i q (cl _) a g n (q3s e s)
   have k7:∀ {x t:O},(aZ D b x⊆aZ D b t->(aZ D b x).Nonempty->False)->(aZ D b x).Nonempty->q3S (q3Z D b u v w x) (q3Z D b u v w t)=false:=fun k n=>Bool.eq_false_iff.2 fun s=>k (q3s e s) n
   refine q62b _ _ _ _ (N 1 n1) (N 8 n8) (N 10 n10) (N 13 n13) (k7 k1 n1) (k7 k8 n8) (k7 k10 n10) (kc 9 5 h9 V n1) (kc 9 6 h9 V n1) (kc 2 12 h2 V n8) (kc 2 12 h2 V n8) (kc 4 11 h4 V n10) (kc 4 11 h4 V n10) (kc 2 12 h2 V n13) ?_
   intro c13 j8 j10 c8 c10
   obtain⟨x,x3,x8⟩:=q3i j8;obtain⟨y,y3,y0⟩:=q3i j10
   rw[card_le_one.1 (by rw[zc];omega) _ y3 _ x3] at y0
   have G:∀ {i k:O},k∈aa 14 D->k∉dom i->¬ag 14 D (aw D (am (pos k)))⊆dom i:=fun a n s=>n (s (cd hp a))
   have F:∀ {i y:O} {f:ℕ×_d},am f∈af 14 D y->y∉dom i->¬ag 14 D (aw D (am f))⊆dom i:=fun a n s=>n (s (ak.1 a).2.1)
   obtain⟨f,hf,-,hg,-⟩:=bf h r hp (by decide:aP 13 1)
   have A2:=aJ hp i2 (by decide:aP 2 13);have A4:=aJ hp i4 (by decide:aP 4 13)
   have b3:=bj_clean h r hb (cl 13);have z3:=zc 13
   have M3:aW 14 D (ao 14 D {13})=∅:=card_eq_zero.1 (by have:=d6 A2 A4 hf (pn i2 i4 V) (ne i2 hg V) (ne i4 hg V);omega)
   have E:∀ (t i l y:O) {g:ℕ×_d},i∈aa 14 D->l∈aa 14 D->g∈af 14 D t->(∀ k∈aa 14 D,g=pos k->y∈dom k)->pos l∈af 14 D t->q3C (q3Z D b u v w t)<=2->(ac 0 t=true/\ac i t=true/\0≠i/\0≠l/\i≠l/\y∉dom 0/\y∉dom i/\y∉dom l)->aW 14 D (ao 14 D {t})=∅/\∀ p∈af 14 D t,p=pos 0\/p=pos i\/p=g\/p=pos l:=
    fun t i l y g a c hq hq2 hl ct ⟨g1,g2,g3,g4,g5,g6,g7,g8⟩=>by
     have P0:=aJ hp i0 ((ae _ _).1 g1);have Pi:=aJ hp a ((ae _ _).1 g2)
     have:=mm P0 Pi hq hl (pn i0 a g3) (ne i0 hq2 g6) (pn i0 c g4) (ne a hq2 g7) (pn a c g5) (ne c hq2 g8).symm
     have:=bj_clean h r hb (cl t);have:=zc t
     exact⟨card_eq_zero.1 (by omega),gh P0 Pi hq hl (pn i0 a g3) (ne i0 hq2 g6) (pn i0 c g4) (ne a hq2 g7) (pn a c g5) (ne c hq2 g8).symm (by omega)⟩
   obtain⟨f8,hf8,hf82,hg8,-⟩:=bf h r hp (by decide:aP 8 6);obtain⟨f0,hf0,-,hg0,-⟩:=bf h r hp (by decide:aP 10 5)
   have A:10∈ag 14 D (aw D (pos 2))->8∈ag 14 D (aw D (pos 4))->False:=fun a c=>by
    obtain⟨-,en⟩:=E 8 2 4 6 i2 i4 hf8 hg8 (cV_dom hp i4 c V) c8 V
    exact absurd (cT_dom h r b0 hp i2 h2 (by decide:aP 2 8) (fun p hp hn=>by rcases en p hp with rfl|rfl|rfl|rfl;{exact G i0 V};{exact absurd rfl hn};{exact F hf82 V};{exact G i4 V}) 10 a) V
   have B:∀ (t i l y z:O) {g:ℕ×_d},i∈aa 14 D->l∈aa 14 D->g∈af 14 D t->(∀ k∈aa 14 D,g=pos k->y∈dom k)->q3C (q3Z D b u v w t)<=2->(ac 0 t=true/\ac i t=true/\0≠i/\0≠l/\i≠l/\y∉dom 0/\y∉dom i/\y∉dom l/\t∉dom l/\ac 0 z=true/\ac i 13=true/\ac l 13=true/\mV t 13 z=true/\(1:O)∉dom i/\(1:O)∉dom l)->t∈ag 14 D (aw D f)->t∈ag 14 D (aw D (pos l))->False:=
    fun t i l y z g a c hq hq2 ct ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15⟩ ft lt=>by
     obtain⟨M,en⟩:=E t i l y a c hq hq2 (cV_dom hp c lt g9) ct ⟨g1,g2,g3,g4,g5,g6,g7,g8⟩
     have fm:=gD h.1 M (ak.1 hf).1 (cY h.1 hf) ft
     obtain⟨q,hq,q3,qz⟩:=bE_dom h.1 r g13
     have f3:=(ak.1 hf).2.1
     rcases en f fm with e0|e0|e0|e0
     · exact absurd (c7.1 13 (e0▸f3)) V
     · exact absurd (hg i a e0) g14
     · rcases en q hq with rfl|rfl|rfl|rfl
       · exact qz ((hp.1 0 i0).2.2.2.1 z ((ae _ _).1 g10))
       · exact q3 ((hp.1 i a).2.2.2.1 13 ((ae _ _).1 g11))
       · exact q3 (e0▸f3)
       · exact q3 ((hp.1 l c).2.2.2.1 13 ((ae _ _).1 g12))
     · exact absurd (hg l c e0) g15
   obtain⟨P,Q,hPQ,hP,hQ,hc⟩:=dV_any h r M3 x3
   have m8:=hc 8 (ay.1 x8).2;have m0:=hc 10 (ay.1 y0).2
   have T:=fun e (k:e∈af 14 D 13)=>aT A2 A4 hf (pn i2 i4 V) (ne i2 hg V) (ne i4 hg V) (by omega) e k
   have B0:=B 10 4 2 5 8 i4 i2 hf0 hg0 c10 V;have B8:=B 8 2 4 6 10 i2 i4 hf8 hg8 c8 V
   rcases T P hP with rfl|rfl|rfl <;> rcases T Q hQ with rfl|rfl|rfl <;> first|exact hPQ rfl|exact A m0.1 m8.2|exact A m0.2 m8.1|exact B0 m0.2 m0.1|exact B0 m0.1 m0.2|exact B8 m8.2 m8.1|exact B8 m8.1 m8.2
abbrev q58_K (a t:B3):Prop:=1<=q3C a->q3S a t=false
set_option synthInstance.maxSize 30000 in
set_option synthInstance.maxHeartbeats 0 in
lemma q58_E:∀ a:B3,1<=q3C a->∀ b:B3,1<=q3C b->q58_K a b->q58_K b a->∀ c:B3,1<=q3C c->q58_K a c->q58_K b c->(q3C c=1->q3I c a=true->q3I c b=true->False)->∀ d:B3,1<=q3C d->q58_K a d->q58_K b d->q58_K c d->q58_K d c->(q3C d=1->q3I d a=true->q3I d b=true->False)->∀ e:B3,q58_K a e->q58_K b e->q58_K d e->q58_K e c->∀ f:B3,q58_K a f->q58_K b f->q58_K c f->q58_K f d->∀ g:B3,q58_K c g->q58_K d g->q58_K f g->(q3C e=0->q3C g=0->False)->∀ i:B3,q58_K d i->q58_K e i->q58_K g i->q58_K i c->(q3C f=0->q3C i=0->False)->∀ j:B3,q58_K c j->q58_K d j->q58_K f j->(q3C g=0->q3C i=0->q3C j=0->q3C e=1->q3S e f=true->q3S e a=true->False)->False:=by decide +kernel
lemma orb_58 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨58,V⟩):False:=by
 have hT:=aV 14 D;rw[hI,(by decide:(bU ⟨58,V⟩).card=5)] at hT
 by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 _ hI}
 by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 _ (by decide) hI}
 have hts:=bg 14 D;obtain⟨b,B⟩:=b_dom h.1 r;obtain⟨p,P⟩:=bQ_dom h r;have hR:=bS_dom h.1 B
 have m:∀ x:O,x∈({0,2,4,5,7}:o)->x∈aa 14 D:=fun x=>by rw[hI];exact id
 have i0:=m 0 V;have i7:=m 7 V;have i2:=m 2 V;have i4:=m 4 V;have i5:=m 5 V
 have cl:∀ x:O,isClean (aa 14 D) x:=fun x=>by by_cases a:x=1\/x=3;{exact .inr (.inl ⟨a,i0⟩)};by_cases c:x=8\/x=10;{exact .inr (.inr ⟨c,i7⟩)};{left;push Not at a c;exact⟨a.1,a.2,c.1,c.2⟩}
 have c7:=cT_07_uncond P i0 i7
 have bc:∀ x,(af 14 D x).card<=2+(aZ D b x).card:=fun x=>by have:=bj_clean h r B (cl x);omega
 have N:∀ x:O,(∃ i j z:O,i∈({0,2,4,5,7}:o)/\j∈({0,2,4,5,7}:o)/\i≠j/\ac i x=true/\ac j x=true/\ac x z=true/\z≠i/\z≠j/\z∉dom i/\z∉dom j)->3<=(af 14 D x).card:=fun x ⟨i,j,z,a,c,g,n⟩=>cx_dom h r P (m i a) (m j c) ⟨g,n.1,n.2.1,n.2.2.1,n.2.2.2.1,n.2.2.2.2.1⟩ (.inr n.2.2.2.2.2)
 rcases (by omega:(aj 14 D b).card=2\/(aj 14 D b).card=3) with a2|a3
 · obtain⟨u,v,uv,e2⟩:=_ct2.1 a2
   have Q:∀ {J:o} {x k:O},J⊆aa 14 D->(∀ i∈J,p i∈af 14 D x)->aP x k->(∀ i∈J,k∉dom i)->J.card+1<=(af 14 D x).card:=@fun J x k hJ hP hk hd=>by
    obtain⟨e,he,-,hn,-⟩:=bf h r P hk
    have:=_cl (insert_subset he (fun _ y=>by obtain⟨i,hi,rfl⟩:=_mg.1 y;exact hP i hi):insert e (J.image p)⊆af 14 D x);rwa[_cin (fun y=>by obtain⟨i,hi,q⟩:=_mg.1 y;exact hd i hi (hn i (hJ hi) q.symm)),_cij (fun _ a _ c=>P.2 (hJ a) (hJ c))] at this
   have Y:∀ {x y j q:O},j∈aa 14 D->(aZ D b x).Nonempty->aZ D b x⊆aZ D b y->(y∉dom x/\ac j x=true/\ac j q=true/\mV x y q=true/\y∉dom j)->p j∈af 14 D y:=fun a n s g=>cV_dom P a (cy_dom h r B P (cl _) a s n g.1 ⟨g.2.1,g.2.2.1,g.2.2.2.1⟩) g.2.2.2.2
   have W:∀ x:O,_->(aZ D b x).Nonempty:=fun x g=>_cp.1 (by have:=bc x;have:=N x g;omega)
   have n8:=W 8 V;have n10:=W 10 V;have n12:=W 12 V;have n13:=W 13 V
   have k:∀ y:O,¬dj 0 y->aZ D b 8⊆aZ D b y->(y∉dom 8/\mV 8 y 7=true)->False:=fun y d s g=>d (c7.1 y (cy_dom h r B P (cl 8) i0 s n8 g.1 ⟨V,V,g.2⟩))
   have F:∀ x,2<=(aZ D b x).card->aZ D b 8⊆aZ D b x:=fun x c y d=>by have e:aZ D b x=aj 14 D b:=_eqc (_fs _ _) (by omega);rw[e];exact (ay.1 d).1
   have O:∀ y z:O,(∀ i∈({2,4,5}:o),p i∈af 14 D y)->aP y z->(∀ i∈({2,4,5}:o),z∉dom i)->aZ D b 8⊆aZ D b y:=fun y z a c d=>F y (by have:=Q (by rw[hI];decide) a c d;have:=bc y;have:Finset.card ({2,4,5}:o)=3:=(by decide);omega)
   have o1:¬aZ D b 12⊆aZ D b 13:=fun s=>k 13 V (O 13 1 (fun i d=>by simp only[_mi,_ms] at d;rcases d with rfl|rfl|rfl;{exact aJ P i2 V};{exact aJ P i4 V};{exact Y i5 n12 s (q:=9) V}) V V) V
   have o2:¬aZ D b 13⊆aZ D b 12:=fun s=>k 12 V (O 12 3 (fun i d=>by simp only[_mi,_ms] at d;rcases d with rfl|rfl|rfl;{exact aJ P i2 V};{exact Y i4 n13 s (q:=11) V};{exact aJ P i5 V}) V V) V
   have G:∀ s t,aj 14 D b={s,t}->s∉aZ D b 8->aZ D b 8⊆{t}:=fun s t e n z d=>by have:=(ay.1 d).1;rw[e,_mi,_ms] at this;rcases this with rfl|rfl;{exact absurd d n};{exact _mss _}
   have e3:aj 14 D b={v,u}:=by rw[e2,pair_comm]
   refine (fun s=>by have:=Q (J:={0,2,4,5}) (by rw[hI];decide) (fun i d=>by simp only[_mi,_ms] at d;rcases d with rfl|rfl|rfl|rfl;{exact aJ P i0 V};{exact aJ P i2 V};{exact Y i4 n10 s (q:=11) V};{exact Y i5 n10 s (q:=9) V}) (by decide:aP 8 6) (by decide);have:=bc 8;have:(aZ D b 8).card<=2:=a2▸_cfl _ _;have:Finset.card ({0,2,4,5}:o)=4:=(by decide);omega:¬aZ D b 10⊆aZ D b 8) (fun t d=>by_contra fun n=>?_);have q:=(ay.1 d).1;rw[e2,_mi,_ms] at q
   rcases dJ uv (e2▸_fs _ _) (e2▸_fs _ _) n12 n13 o1 o2 with ⟨c,c'⟩|⟨c,c'⟩ <;> rcases q with rfl|rfl <;> first|exact k 12 V (by rw[c];exact G _ _ e2 n) V|exact k 13 V (by rw[c'];exact G _ _ e2 n) V|exact k 12 V (by rw[c];exact G _ _ e3 n) V|exact k 13 V (by rw[c'];exact G _ _ e3 n) V
 · have b0:bL 14 D=0:=by omega
   obtain⟨u,v,w,d1,d2,d3,e3⟩:=card_eq_three.1 a3
   have dI:∀ i:O,i∈({2,4,5}:o)->dom i⊆aa 14 D:=by rw[hI];decide
   set Z:=q3Z D b u v w;have C:∀ x,(aZ D b x).card=q3C (Z x):=q3c e3 ⟨d1,d2,d3⟩
   have KK:∀ x y:O,((aZ D b x).Nonempty->aZ D b x⊆aZ D b y->False)->q58_K (Z x) (Z y):=fun x y k n=>by cases q:q3S (Z x) (Z y);{rfl};{exact (k (_cp.1 (by rw[C];omega)) (q3s e3 q)).elim}
   have K:∀ x y:O,(∃ j q:O,y∉dom x/\ac j x=true/\ac j q=true/\mV x y q=true/\bK j y=false/\(j=0\/j=7\/j∈({2,4,5}:o)))->q58_K (Z x) (Z y):=fun x y ⟨j,q,a,c,e,f,g,o⟩=>KK x y fun n s=>by rcases o with rfl|rfl|o;{exact b3.1 g (c7.1 y (cy_dom h r B P (cl x) i0 s n a ⟨c,e,f⟩))};{exact b3.1 g (c7.2 y (cy_dom h r B P (cl x) i7 s n a ⟨c,e,f⟩))};{exact orb49_cut h r b0 B x y j q (cl x) (dI j o) ⟨a,c,e,f,g⟩ n s}
   have NE:∀ x:O,_->1<=q3C (Z x):=fun x g=>by rw[<-C];have:=bc x;have:=N x g;omega
   have DL:∀ x y z ix iy:O,ix∈aa 14 D->iy∈aa 14 D->(x∉dom iy/\y∉dom ix/\z∉dom ix)->(ac ix x=true/\ac iy y=true/\ac x y=true/\ac x z=true/\cmOk iy y z=true)->q3C (Z x)=0->q3C (Z y)=0->False:=fun x y z ix iy a c g k e f=>dl_dom h r P x y z ix iy a c g k (by have:=bc x;rw[C,e] at this;omega) (by have:=bc y;rw[C,f] at this;omega)
   have S2:∀ x i j z:O,(i∈({2,4,5}:o)/\j∈({2,4,5}:o)/\(bK i 8=false\/bK i 10=false)/\(bK j 8=false\/bK j 10=false))->(i≠j/\ac i x=true/\ac j x=true/\ac x z=true/\z≠i/\z≠j/\j∉dom i/\i∉dom j/\z∉dom i/\z∉dom j)->q3C (Z x)=1->q3I (Z x) (Z 8)=true->q3I (Z x) (Z 10)=true->False:=fun x i j z ⟨a,c,ni,nj⟩ g k e f=>by
    obtain⟨t,ht⟩:=_c1.1 (by rw[C];exact k)
    have M:∀ y,q3I (Z x) (Z y)=true->y∈ag 14 D t.1:=fun y k=>by obtain⟨s,a,c⟩:=q3i k;rw[ht,_ms] at a;exact a▸(ay.1 c).2
    obtain⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g0⟩:=g;have I:=dI i a;have J:=dI j c;have x':=I (dom_self i);have z':=J (dom_self j);have t':(af 14 D x).card<=3:=by have:=bc x;rw[C,k] at this;omega
    have ci:=dy_dom h r b0 P x' z' I ⟨g1,g2,g3,g4,g5,g6⟩ (.inr ⟨g9,g0⟩) g7 g9 t';have cj:=dy_dom h r b0 P z' x' J ⟨g1.symm,g3,g2,g4,g6,g5⟩ (.inr ⟨g0,g9⟩) g8 g0 t'
    obtain⟨E,F,n,e',f',Y⟩:=dV_dom h r B (cl x) ht (cx_dom h r P x' z' ⟨g1,g2,g3,g4,g5,g6⟩ (.inr ⟨g9,g0⟩))
    have G:∀ q,(q=p i\/q=p j)->(∀ y∈ag 14 D t.1,y∈ag 14 D (aw D q))->False:=fun q o d=>o.elim (fun o=>ni.elim (fun n=>b3.1 n (ci 8 (o▸d 8 (M 8 e)))) (fun n=>b3.1 n (ci 10 (o▸d 10 (M 10 f))))) (fun o=>nj.elim (fun n=>b3.1 n (cj 8 (o▸d 8 (M 8 e)))) (fun n=>b3.1 n (cj 10 (o▸d 10 (M 10 f)))))
    by_cases m:E=p i\/E=p j;{exact G E m fun y d=>(Y y d).1};by_cases o:F=p i\/F=p j;{exact G F o fun y d=>(Y y d).2}
    push Not at m o;have:=mm e' f' (aJ P x' ((ae _ _).1 g2)) (aJ P z' ((ae _ _).1 g3)) n m.1 m.2 o.1 o.2 (fun e=>g1 (P.2 x' z' e));omega
   have FN:q3C (Z 9)=0->q3C (Z 11)=0->q3C (Z 6)=0->q3C (Z 1)=1->q3S (Z 1) (Z 3)=true->q3S (Z 1) (Z 8)=true->False:=fun a c d k s s'=>by
    obtain⟨t,ht⟩:=_c1.1 (by rw[C];exact k)
    have l:∀ x,q3C (Z x)=0->(af 14 D x).card<=2:=fun x e=>by have:=bc x;rw[C,e] at this;omega
    have t1:(af 14 D 1).card<=3:=by have:=bc 1;rw[C,k] at this;omega
    have z3:=q3s e3 s (by rw[ht];exact _mss _);have z8:=q3s e3 s' (by rw[ht];exact _mss _)
    obtain⟨E,F,n,e,f,Y⟩:=dV_dom h r B (cl 1) ht (by by_contra c;exact dl_dom h r P 1 9 13 7 5 i7 i5 V V (by omega) (l 9 a))
    have n7:∀ e,(∀ y,y∈ag 14 D t.1->y∈ag 14 D (aw D e))->p 7≠e:=fun e q d=>absurd (c7.2 8 (d▸q 8 (ay.1 z8).2)) V
    obtain⟨Q,-,e9,q9⟩:=qu_dom h r P i5 (by decide:aP 5 9) V (l 9 a);obtain⟨U,-,e11,-⟩:=qu_dom h r P i4 (by decide:aP 4 11) V (l 11 c)
    have A:∀ x y i X,i∈aa 14 D->af 14 D x={p i,X}->aP x y->y∉dom i->am X∈af 14 D y:=fun x y i X hi e g n=>by obtain⟨f,hf,hm,hd,-⟩:=bf h r P g;rw[e,_mi,_ms] at hf;rcases hf with rfl|rfl;{exact absurd (hd i hi rfl) n};{exact hm}
    have z:Q∈af 14 D 9:=by rw[e9];simp
    have t9:3∈ag 14 D (aw D (am Q)):=by
     rcases aT (aJ P i7 (by decide:aP 7 1)) e f (n7 E fun y d=>(Y y d).1) (n7 F fun y d=>(Y y d).2) n t1 _ (A 9 1 5 Q i5 e9 V V) with q|q|q
     · exact absurd ((P.1 7 i7).2.2.2.2.2.1 (show (9:O)∈ag 14 D (aw D (am (p 7))) by rw[<-q,aB];exact (ak.1 z).2.1)) V
     · exact q▸(Y 3 (ay.1 z3).2).1
     · exact q▸(Y 3 (ay.1 z3).2).2
    obtain⟨f,hf,f3,-⟩:=bE_dom h.1 r (by decide:mV 6 3 2=true)
    rcases gG (A 9 6 5 Q i5 e9 V V) (A 11 6 4 U i4 e11 V V) (fun q=>(q9 11 V).2 (by rw[<-aB Q,q,aB,e11];simp)) (l 6 d) f hf with rfl|rfl;{exact f3 t9};{exact f3 (ak.1 (A 11 3 4 U i4 e11 V V)).2.1}
   exact q58_E _ (NE 8 V) _ (NE 10 V) (K 8 10 V) (K 10 8 V) _ (NE 12 V) (K 8 12 V) (K 10 12 V) (S2 12 2 5 3 V V) _ (NE 13 V) (K 8 13 V) (K 10 13 V) (K 12 13 V) (K 13 12 V) (S2 13 2 4 1 V V) _ (K 8 1 V) (K 10 1 V) (K 13 1 V) (K 1 12 V) _ (K 8 3 V) (K 10 3 V) (K 12 3 V) (K 3 13 V) _ (K 12 9 V) (K 13 9 V) (K 3 9 V) (DL 1 9 13 7 5 i7 i5 V V) _ (K 13 11 V) (K 1 11 V) (K 9 11 V) (K 11 12 V) (DL 3 11 12 7 4 i7 i4 V V) _ (K 12 6 V) (K 13 6 V) (K 3 6 V) FN
lemma q31_a {D:Dag} (h:ai 14 D) {x:O} {e:ℕ×_d} (he:e∈af 14 D x) (hx:x∈ag 14 D (aw D (am e))):False:=by
 obtain⟨a,b,c⟩:=ak.1 he;rw[cB h.1 a (cY h.1 he)] at c;cases f:e.2<;>simp[aw,am,f] at b hx<;>exact c (_mn.2 (by first|exact⟨b,hx⟩|exact⟨hx,b⟩))
lemma q31_q {α:Type} [DecidableEq α] {s:Finset α} {a z e:α} (W:s={a,z}) (k:e∈s) (n:e≠a):e=z:=by rw[W,_mi,_ms] at k;exact k.resolve_left n
lemma q31_G {D:Dag} (h:ai 14 D) {x y:O} {e:ℕ×_d} (he:e∈af 14 D x) (c:y∈ag 14 D (aw D e)):e∈af 14 D y\/e.1∈aW 14 D (ao 14 D {y}):=by
 obtain⟨a,-,-⟩:=ak.1 he;by_cases k:y∈ag 14 D (14+e.1)
 ·right;have q:=k;rw[cB h.1 a (cY h.1 he),_mn] at q;simp only[aW,_mf,mem_range,b7];exact⟨a,k,q.1,q.2⟩
 ·exact Or.inl (ak.2 ⟨a,c,k⟩)
lemma q31_T {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} {x y z:O} (hM:aW 14 D (ao 14 D {x})=∅) (hZ:∀u∈aj 14 D b,x∈ag 14 D u.1) {E A B:ℕ×_d} (a:∀P∈af 14 D x,y∈ag 14 D (aw D P)->P=E\/P=A) (c:∀P∈af 14 D x,z∈ag 14 D (aw D P)->P=E\/P=B):aZ D b y⊆aZ D b z\/aZ D b z⊆aZ D b y:=by
 by_contra n;rw[not_or,not_subset,not_subset] at n;obtain⟨⟨u,hu,nu⟩,w,hw,nw⟩:=n;have L:∀(v:Σ _:ℕ,ℕ) (t:O) (C:ℕ×_d),v∈aZ D b t->(∀P∈af 14 D x,t∈ag 14 D (aw D P)->P=E\/P=C)->Relation.ReflTransGen (bk_x D x) v.1 (aw D E):=fun v t C hv k=>by
  obtain⟨hR,ht⟩:=ay.1 hv;obtain⟨P,Q,pq,hP,hQ,rP,rQ⟩:=dV_tree h r hM (hZ v hR) (by have:=(dW.1 (_mf.1 (_md.1 hR).1).1).2;omega);rcases k P hP (bk_x_ag h.1 hM rP ht) with q|q;{rw[<-q];exact rP};rcases k Q hQ (bk_x_ag h.1 hM rQ ht) with q'|q';{rw[<-q'];exact rQ};{exact absurd (by rw[q,q']) pq}
 rcases reconv_aW h.1 hM (L u y A hu a) (L w z B hw c) with s|s
 ·exact nw (ay.2 ⟨(ay.1 hw).1,s (ay.1 hu).2⟩)
 ·exact nu (ay.2 ⟨(ay.1 hu).1,s (ay.1 hw).2⟩)
lemma q31_3 {α:Type} [DecidableEq α] {S A B C:Finset α} (hS:S.card<=2) (a:A⊆S) (b:B⊆S) (c:C⊆S) (n:C.Nonempty):A⊆B\/B⊆A\/A⊆C\/B⊆C:=by
 by_contra q;rw[not_or,not_or,not_or] at q;obtain⟨q1,q2,q3,q4⟩:=q;obtain⟨u,hu,nu⟩:=not_subset.1 q1;obtain⟨w,hw,nw⟩:=not_subset.1 q2;obtain⟨v,hv⟩:=n;have g:=gG (a hu) (b hw) (fun e=>nu (by rw[e];exact hw)) hS;rcases g v (c hv) with q|q
 ·exact q3 (fun x hx=>by rcases g x (a hx) with p|p;{rw[p,<-q];exact hv};{exact absurd (p▸hx) nw})
 ·exact q4 (fun x hx=>by rcases g x (b hx) with p|p;{exact absurd (p▸hx) nu};{rw[p,<-q];exact hv})
lemma orb_31 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨31,V⟩):False:=by
 have hT:=aV 14 D;rw[hI,(by decide:(bU ⟨31,V⟩).card=4)] at hT;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 _ hI};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 _ (by decide) hI};have hts:=bg 14 D;obtain⟨b,hb⟩:=b_dom h.1 r;obtain⟨pos,hp⟩:=bQ_dom h r;have hR:=bS_dom h.1 hb;have b0:bL 14 D=0:=by omega
 have a2:(aj 14 D b).card=2:=by omega
 have m:∀ x:O,x∈aa 14 D↔x∈({0,1,2,4}:o):=fun x=>by rw[hI];rfl
 have i0:=(m 0).2 V;have i1:=(m 1).2 V;have i2:=(m 2).2 V;have i4:=(m 4).2 V;have d:∀i:O,i∈({1,2,4}:o)->dom i⊆aa 14 D:=fun i g x c=>(m x).2 (by revert i x;decide)
 have cl:∀x:O,x≠8∧x≠10->isClean (aa 14 D) x:=fun x ⟨a,c⟩=>by by_cases g:x=1\/x=3;{exact Or.inr (Or.inl ⟨g,i0⟩)};{left;push Not at g;exact⟨g.1,g.2,a,c⟩}
 have bj:=fun x a=>bj_clean h r hb (cl x a)
 have ne:∀x:O,x≠8∧x≠10->3<=(af 14 D x).card->(aZ D b x).Nonempty:=fun x a c=>_cp.1 (by have:=bj x a;omega)
 have nl:∀x:O,x∉({0,1,2,4}:o)->x∈al 14 D:=fun x c=>by by_contra q;exact c ((m x).1 (aN.2 q))
 have F:=fun x y (g:aP x y)=>bf h r hp g
 have J:=fun i a (g:i∈({0,1,2,4}:o)∧aP i a)=>aJ hp ((m i).2 g.1) g.2
 have U:=fun i x (k:i∈aa 14 D) (g:aP i x∧quOk i x=true)=>qu_dom h r hp k g.1 g.2
 have K:=fun x t i (c:x≠8∧x≠10∧i∈({1,2,4}:o)) g=>orb49_cut h r b0 hb x t i 13 (cl x ⟨c.1,c.2.1⟩) (d i c.2.2) g
 have L:∀x:O,(aZ D b x).Nonempty->(aZ D b 11).Nonempty->(aZ D b 12).Nonempty->(x∉dom 11∧ac 4 11=true∧ac 4 13=true∧mV 11 x 13=true∧bK 4 x=false)->(x∉dom 12∧ac 2 12=true∧ac 2 13=true∧mV 12 x 13=true∧bK 2 x=false)->False:=fun x z z1 z2 g1 g2=>by
  rcases q31_3 (A:=aZ D b 11) (B:=aZ D b 12) a2.le (_fs _ _) (_fs _ _) (_fs _ _) z with s|s|s|s<;>first|exact K 11 12 4 V V z1 s|exact K 12 11 2 V V z2 s|exact K 11 x 4 V g1 z1 s|exact K 12 x 2 V g2 z2 s
 have c13:=cx_dom h r hp i1 i2 (u:=13) V (Or.inl i4);have p1:=J 1 13 V;have p2:=J 2 13 V;have p4:=J 4 13 V;have n12:=mt (hp.2 i1 i2) V;have n14:=mt (hp.2 i1 i4) V;have n24:=mt (hp.2 i2 i4) V;have T:=fun (l:(af 14 D 13).card<=3)=>(⟨aT p1 p2 p4 n12 n14 n24 l,dy_dom h r b0 hp i1 i2 (d 1 V) V (Or.inl i4) V V l,dy_dom h r b0 hp i2 i1 (d 2 V) V (Or.inl i4) V V l,dy_dom h r b0 hp i4 i1 (d 4 V) V (Or.inl i2) V V l⟩:_∧_∧_∧_)
 have A:∀u w:Σ _:ℕ,ℕ,aj 14 D b={u,w}->u∈aZ D b 13->w∉aZ D b 13->False:=fun u w R a d=>by
  have Z:aZ D b 13={u}:=ext fun v=>⟨fun e=>by have:=(ay.1 e).1;rw[R,_mi,_ms] at this;rcases this with rfl|rfl;{exact _mss _};{exact absurd e d},fun e=>by rw[_ms.1 e];exact a⟩
  obtain⟨A,t1,t2,t4⟩:=T (by have:=bj 13 V;rw[Z,_cs] at this;omega);obtain⟨P,Q,hPQ,hP,hQ,hy⟩:=dV_dom h r hb (cl 13 V) Z c13;have K:∃i j:O,(i≠j∧i∈({1,2,4}:o)∧j∈({1,2,4}:o))∧∀y,y∈ag 14 D u.1->bK i y=true∧bK j y=true:=by
   rcases A P hP with rfl|rfl|rfl<;>rcases A Q hQ with rfl|rfl|rfl<;>first|exact absurd rfl hPQ|refine⟨_,_,?_,fun y c=>⟨(cW _ _).2 (by first|exact t1 _ (hy y c).1|exact t2 _ (hy y c).1|exact t4 _ (hy y c).1),(cW _ _).2 (by first|exact t1 _ (hy y c).2|exact t2 _ (hy y c).2|exact t4 _ (hy y c).2)⟩⟩<;>exact V
  obtain⟨i,j,g,H⟩:=K;have K0:∀i j y:O,(i≠j∧i∈({1,2,4}:o)∧j∈({1,2,4}:o))->bK i y=true->bK j y=true->¬(y≠8∧y≠10∧y≠13):=by decide
  have K2:∀i j:O,(i≠j∧i∈({1,2,4}:o)∧j∈({1,2,4}:o))->bK i 8=true->bK j 8=true->bK i 10=true->bK j 10=true->False:=by decide
  have nu:∀y:O,(y≠8∧y≠10∧y≠13)->y∉ag 14 D u.1:=fun y a e=>K0 i j y g (H y e).1 (H y e).2 a
  have big:∀y:O,(y≠8∧y≠10∧y≠13)->3<=(af 14 D y).card->aZ D b y={w}:=fun y p e=>by
   rcases subset_singleton_iff.1 (fun v c=>by obtain⟨q,c⟩:=ay.1 c;rw[R,_mi] at q;rcases q with q|q;{exact absurd (q▸c) (nu y p)};{exact q}:aZ D b y⊆{w}) with g|g;{have:=bj y ⟨p.1,p.2.1⟩;rw[g,_ce] at this;omega};{exact g}
  have sm:∀y:O,(y≠8∧y≠10∧y≠13)->y∉ag 14 D w.1->(af 14 D y).card<=2:=fun y a e=>by
   by_contra f;exact e (ay.1 (by rw[big y a (by omega)];exact _mss w:w∈aZ D b y)).2
  have S:∀x i a c j k:O,(x≠8∧x≠10∧x≠13)->(∀y:O,(y=3∨y=a∨y=c)->(y≠8∧y≠10∧y≠13)∧bK i y=false∧mV x y 13=true)->ac i x=true->ac i 13=true->(3∉dom j∧3∉dom k)∧ac 3 a=true∧ac 3 c=true∧ac 3 x=true∧ac j a=true∧ac k c=true∧cmOk j a c=true∧cmOk j a x=true∧cmOk k c x=true->i∈aa 14 D->(∀t,t∈ag 14 D (aw D (pos i))->dj i t)->j∈aa 14 D->k∈aa 14 D->(af 14 D x).card<=2:=fun x i a c j k g G q1 q2 N hi ti hj hk=>by
   by_contra f;have e:=eF_cand_1side_u h r hb hp (cl x ⟨g.1,g.2.1⟩) (big x g (by omega)) (by omega) hi q1 ti;have e:=fun y v=>sm y (G y v).1 fun k=>(e y k).elim (b3.1 (G y v).2.1) fun f=>by have:=(G y v).2.2;rw[f 13 q2] at this;exact Bool.false_ne_true this
   exact fR_dom h r hp 3 a c x j k hj hk N.1 N.2 (e 3 (Or.inl rfl)) (e a (Or.inr (Or.inl rfl))) (e c (Or.inr (Or.inr rfl)))
  have s7:=S 7 1 11 12 4 2 V V V V V i1 t1 i4 i2;have s11:=S 11 4 7 12 1 2 V V V V V i4 t4 i1 i2;have s12:=S 12 2 7 11 1 4 V V V V V i2 t2 i1 i4;have A7:=gG (J 0 7 V) (J 1 7 V) (mt (hp.2 i0 i1) V) s7;obtain⟨Z1,-,W1,c1⟩:=U 4 11 i4 V s11;obtain⟨Z2,-,W2,c2⟩:=U 2 12 i2 V s12;obtain⟨e7,h7,k7,f7,y7⟩:=F 3 7 V;obtain⟨e1,h1,k1,f1,g1⟩:=F 3 11 V;obtain⟨e2,h2,k2,f2,g2⟩:=F 3 12 V;have E1:=q31_q W1 k1 (mt (g1 4 i4) V);have E2:=q31_q W2 k2 (mt (g2 2 i2) V);have E7:am e7=pos 0:=(A7 _ k7).resolve_right (mt (y7 1 i1) V);have D7:∀y,y∈ag 14 D (aw D e7)->y∈dom 0:=fun y c=>(hp.1 0 i0).2.2.2.2.2.1 (by rw[<-E7,aB];exact c)
  have m12:e1≠e2:=fun e=>(c1 12 V).2 (by rw[<-E1,e,E2,W2];simp)
  have m17:e1≠e7:=fun e=>(c1 7 V).2 (by rw[<-E1,e];exact k7)
  have m27:e2≠e7:=fun e=>(c2 7 V).2 (by rw[<-E2,e];exact k7)
  have c3:=d6 h1 h2 h7 m12 m17 m27;have Z3:=big 3 V c3;have A3:=aT h1 h2 h7 m12 m17 m27 (by have:=bj 3 V;rw[Z3,_cs] at this;omega);have s9:(af 14 D 9).card<=2:=by
   by_contra c;have z:=big 9 V (by omega);rcases A3 _ (cV_dom hp i1 (cy_dom h r hb hp (t:=3) (j:=1) (q:=13) (cl 9 V) i1 (by rw[z,Z3]) (by rw[z];exact⟨w,_mss w⟩) V V) V) with e|e|e;{exact mt (f1 1 i1) V e.symm};{exact mt (f2 1 i1) V e.symm};{exact mt (f7 1 i1) V e.symm}
  obtain⟨Z9,-,W9,c9⟩:=U 1 9 i1 V s9;have nz:∀x i v:O,i∈aa 14 D->leakRoot x=7->x∈dom 7->x≠7->i≠0->ac i x=true->ac 0 x=true->ac x v=true->v≠i->v≠0->(v∉dom i∧v∉dom 0)->bK i 7=false->0≠i->(aZ D b x).Nonempty:=fun x i v hi l a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11=>by
   by_contra c;rw[not_nonempty_iff_eq_empty] at c;by_cases g:x∈ag 14 D (b 7)
   ·exact no_leak_2nbrs h r b0 hb hp (nl 7 V) a1 a2 c hi i0 a3 a4 a5 a6 a7 a8 (Or.inr a9) a10 (fun k=>k g)
   ·have:=bj_noleak h r hb (x:=x) (fun _ _=>by rw[l];exact g);rw[c,_ce] at this;have:=cx_dom h r hp i0 hi ⟨a11,a5,a4,a6,a8,a7⟩ (Or.inr ⟨a9.2,a9.1⟩);omega
  have W:(8:O)∈ag 14 D w.1\/(10:O)∈ag 14 D w.1:=by
   by_contra c;push Not at c;have q:∀x:O,(aZ D b x).Nonempty->x∉ag 14 D w.1->x∈ag 14 D u.1:=fun x ⟨v,hv⟩ k=>by obtain⟨a,e⟩:=ay.1 hv;rw[R,_mi,_ms] at a;rcases a with rfl|rfl;{exact e};{exact absurd e k}
   have a:=H 8 (q 8 (nz 8 2 6 i2 V V V V V V V V V V V V) c.1);have e:=H 10 (q 10 (nz 10 4 5 i4 V V V V V V V V V V V V) c.2);exact K2 i j g a.1 a.2 e.1 e.2
  obtain⟨P3,Q3,hPQ3,hP3,hQ3,hy3⟩:=dV_dom h r hb (cl 3 V) Z3 c3;have B:∀x:O,x∈ag 14 D w.1->x∉dom 0->x∈ag 14 D (aw D e1)/\x∈ag 14 D (aw D e2):=fun x c d=>by
   have y:=hy3 x c;rcases A3 P3 hP3 with rfl|rfl|rfl<;>rcases A3 Q3 hQ3 with rfl|rfl|rfl<;>first|exact absurd rfl hPQ3|exact absurd (D7 x y.1) d|exact absurd (D7 x y.2) d|exact y|exact y.symm
  have Y:∀s:O,∀{x a c i k:O} {Za Zc ea ec:ℕ×_d},af 14 D a={pos i,Za}->(∀t,cmOk i a t=true->t∉ag 14 D (aw D Za)∧Za∉af 14 D t)->am ea=Za->af 14 D c={pos k,Zc}->(∀t,cmOk k c t=true->t∉ag 14 D (aw D Zc)∧Zc∉af 14 D t)->am ec=Zc->ea≠ec->(∀e∈af 14 D 3,e=ea∨e=ec∨e=e7)->x∈ag 14 D (aw D ea)->i∈aa 14 D->(aP 9 s∧aP a s)->aP s x->(s∉dom 1∧s∉dom i∧s∉dom 0)->(cmOk 1 9 a=true∧cmOk 1 9 x=true∧cmOk 1 9 c=true∧cmOk k c x=true)->(s≠8∧s≠10∧s≠13)->False:=fun s x a c i k Za Zc ea ec Wa ca Ea Wc cc Ec mac A' hx hi ⟨G1,G2⟩ G3 ⟨G4,G5,G6⟩ ⟨G7,G8,G9,G10⟩ G11=>by
   have z:Za∉af 14 D x:=fun q=>q31_a h q (by rw[<-Ea,aB];exact hx)
   obtain⟨f,hf,kf,ff,-⟩:=F 9 s G1;obtain⟨f',hf',kf',ff',-⟩:=F a s G2;obtain⟨e0,h0,k0,-,-⟩:=F s x G3;have a9:am Z9∈af 14 D s:=q31_q W9 hf (mt (ff 1 i1) G4)▸kf;have a1:ea∈af 14 D s:=by rw[<-aB ea,Ea,<-q31_q Wa hf' (mt (ff' i hi) G5)];exact kf'
   have n1:am Z9≠ea:=fun e=>(c9 a G7).2 (by rw[<-aB Z9,e,Ea,Wa];simp)
   have n2:am Z9≠e0:=fun e=>(c9 x G8).2 (by rw[<-aB Z9,e];exact k0)
   have n3:ea≠e0:=fun e=>z (by rw[<-Ea,e];exact k0)
   have c6:=d6 a9 a1 h0 n1 n2 n3;obtain⟨P,Q,hPQ,hP,hQ,hP6,hQ6⟩:=clean_shared_af_u h r hb (cl 3 V) (cl s ⟨G11.1,G11.2.1⟩) Z3 (big s G11 c6) c3 c6;have a2:ec∈af 14 D s:=by rcases A' P hP with rfl|rfl|rfl<;>rcases A' Q hQ with rfl|rfl|rfl<;>first|exact absurd rfl hPQ|exact hP6|exact hQ6|exact absurd (D7 s (ak.1 hP6).2.1) G6|exact absurd (D7 s (ak.1 hQ6).2.1) G6
   have:=mm a9 a1 h0 a2 n1 n2 (fun e=>(c9 c G9).2 (by rw[<-aB Z9,e,Ec,Wc];simp)) n3 mac (fun e=>(cc x G10).2 (by rw[<-Ec,<-e];exact k0));have:=bj s ⟨G11.1,G11.2.1⟩;rw[big s G11 c6,_cs] at this;omega
  rcases W with g|g
  ·exact Y 6 W1 c1 E1 W2 c2 E2 m12 A3 (B 8 g V).1 i4 V V V V V
  ·exact Y 5 W2 c2 E2 W1 c1 E1 m12.symm (fun e k=>by rcases A3 e k with q|q|q<;>simp[q]) (B 10 g V).2 i2 V V V V V
 have B:aZ D b 13=aj 14 D b->False:=fun hZ=>by
  have Zs:∀x:O,aZ D b x⊆aZ D b 13:=fun x=>by rw[hZ];exact _fs _ _
  have hZa:∀u∈aj 14 D b,(13:O)∈ag 14 D u.1:=fun u hu=>(ay.1 (by rw[hZ];exact hu:u∈aZ D b 13)).2
  have b13:=bj 13 V;rw[hZ,a2] at b13;have J3:3<=(af 14 D 3).card->∃f,∀e∈af 14 D 3,e≠f->(13:O)∈ag 14 D (aw D e):=fun c=>by
   obtain⟨u,hu⟩:=ne 3 V c;exact jx_dom h r hb (nl 3 V) (cl 3 V) V V (Zs 3) ⟨u.1,(ay.1 hu).2,hZa u (ay.1 hu).1⟩ ⟨7,V,V⟩
  have C:∀E:ℕ×_d,(∀P∈af 14 D 13,P=pos 1\/P=pos 2\/P=pos 4\/P=E)->(af 14 D 3).card<=2->(∀y:O,y∈ag 14 D (aw D (am E))->y≠1->y≠2->y≠4->∀a c:O,a∈({7,11,12}:o)->c∈({7,11,12}:o)->aZ D b a⊆aZ D b c\/aZ D b c⊆aZ D b a)->False:=fun E hA s3 hT=>by
   have p07:=J 0 7 V;have p17:=J 1 7 V;have U3:∀e:ℕ×_d,e∈af 14 D 3->(13:O)∉ag 14 D (aw D e)->(13:O)∈ag 14 D (aw D (am e))->am e∈af 14 D 13:=fun e he n c=>ak.2 ⟨(ak.1 he).1,c,fun k=>n (cr h.1 (ak.1 he).1 (cY h.1 he) e.2 k)⟩
   have W:∀i:O,(i∈({0,1,2,4}:o)∧(3:O)∉dom i)->∀e∈af 14 D 3,am e≠pos i:=fun i g e he q=>g.2 (em_dom hp ((m i).2 g.1) (by rw[<-q,aB];exact he))
   have Bx:∀x i s:O,i∈aa 14 D->(aP i x∧aP x s∧s∉dom i∧x≠8∧x≠10)->∀X:ℕ×_d,X∈af 14 D x->X≠pos i->s∉ag 14 D (aw D (am X))->(aZ D b x).Nonempty:=fun x i s hi g X hX n4 n6=>by
    obtain⟨f,hf,kf,ff,-⟩:=F x s g.2.1;exact ne x ⟨g.2.2.2.1,g.2.2.2.2⟩ (d6 (aJ hp hi g.1) hX hf (Ne.symm n4) (fun e=>g.2.2.1 (ff i hi e.symm)) (fun e=>n6 (by rw[e];exact (ak.1 kf).2.1)))
   have B7:∀X:ℕ×_d,X∈af 14 D 7->X≠pos 0->X≠pos 1->(aZ D b 7).Nonempty:=fun X hX a c=>ne 7 V (d6 p07 p17 hX (mt (hp.2 i0 i1) V) (Ne.symm a) (Ne.symm c))
   by_cases s7:(af 14 D 7).card<=2
   ·have A7:=gG p07 p17 (mt (hp.2 i0 i1) V) s7
    obtain⟨e,he,ke,-,ge⟩:=F 3 7 V;have a0:am (pos 0)∈af 14 D 3:=by rw[<-(A7 _ ke).resolve_right (mt (ge 1 i1) V),aB];exact he
    have N:∀t:O,mV 7 t 13=true->t∉ag 14 D (aw D (pos 0)):=fun t v c=>by
     obtain⟨f,hf,n1,n2⟩:=bE_dom h.1 r v;rcases A7 f hf with q|q;{exact n1 (q▸c)};{exact n2 (q▸(hp.1 1 i1).2.2.2.1 13 V)}
    obtain⟨e1,h1,k1,-,-⟩:=F 3 11 V;obtain⟨e2,h2,k2,-,-⟩:=F 3 12 V;have m1:am (pos 0)≠e1:=fun q=>N 11 V (by have:=(ak.1 k1).2.1;rwa[<-q,aB] at this)
    have m2:am (pos 0)≠e2:=fun q=>N 12 V (by have:=(ak.1 k2).2.1;rwa[<-q,aB] at this)
    have A3:=gG a0 h1 m1 s3;rw[(A3 _ h2).resolve_left (Ne.symm m2)] at k2;have M:∀t:O,mV 3 0 t=true->t∉ag 14 D (aw D e1):=fun t v c=>by
     obtain⟨f,hf,n1,n2⟩:=bE_dom h.1 r v;rcases A3 f hf with q|q;{exact n1 (q▸cd hp i0)};{exact n2 (q▸c)}
    by_cases c:(13:O)∈ag 14 D (aw D (am e1))
    ·rcases hA _ (U3 e1 h1 (M 13 V) c) with q|q|q|q<;>try exact W _ V e1 h1 q
     have z1:=Bx 11 4 6 i4 V E (q▸k1) (fun e=>W 4 V e1 h1 (q.trans e)) (by rw[<-q,aB];exact M 6 V);have z2:=Bx 12 2 5 i2 V E (q▸k2) (fun e=>W 2 V e1 h1 (q.trans e)) (by rw[<-q,aB];exact M 5 V);rcases hT 3 (by rw[<-q,aB];exact (ak.1 h1).2.1) V V V 11 12 V V with s|s;{exact K 11 12 4 V V z1 s};{exact K 12 11 2 V V z2 s}
    ·obtain⟨f,hf⟩:=jx_dom h r hb (nl 11 V) (cl 11 V) V V (Zs 11) ⟨_,(hp.1 4 i4).2.2.2.1 11 V,(hp.1 4 i4).2.2.2.1 13 V⟩ ⟨3,V,V⟩
     obtain⟨e',h',n1,n2⟩:=bE_dom h.1 r (V:mV 11 13 12=true);have qf:am e1=f:=by by_contra q;exact c (hf _ k1 q)
     exact n1 (hf e' h' (fun q=>n2 (by rw[q,<-qf];exact (ak.1 k2).2.1)))
   have G:∀a i s c k t:O,(af 14 D a).card<=2->i∈aa 14 D->k∈aa 14 D->(aP i a∧quOk i a=true)->(aP a 3∧aP a s)->((3:O)∉dom i∧s∉dom i∧cmOk i a 7=true∧cmOk i a c=true)->(mV 3 s 0=true∧mV 3 s 13=true∧mV 3 s t=true∧aP 3 c∧(3:O)∉dom k)->(aP k c∧aP c t)->(t∉dom k∧c≠8∧c≠10)->c∈({7,11,12}:o)->(c∉dom 7∧ac 1 7=true∧ac 1 13=true∧mV 7 c 13=true∧bK 1 c=false)->(c≠8∧c≠10∧k∈({1,2,4}:o))->((7:O)∉dom c∧ac k c=true∧ac k 13=true∧mV c 7 13=true∧bK k 7=false)->False:=fun a i s c k t sa hi hk ⟨a1,a2⟩ ⟨a3,a4⟩ ⟨a5,a6,a7,a8⟩ ⟨a9,a10,a11,a12,a13⟩ b1 b2 a15 a16 a17 a18=>by
    obtain⟨Z,-,W2,cz⟩:=qu_dom h r hp hi a1 a2 sa;obtain⟨e,he,ke,fe,-⟩:=F a 3 a3;obtain⟨e',he',ke',fe',-⟩:=F a s a4;rw[q31_q W2 he (mt (fe i hi) a5)] at ke;rw[q31_q W2 he' (mt (fe' i hi) a6)] at ke';obtain⟨e7,h7,k7,-,g7⟩:=F 3 7 V;have A3:=gG ke h7 (fun q=>(cz 7 a7).2 (by rw[<-aB Z,q];exact k7)) s3;have M:∀t:O,mV 3 s t=true->t∉ag 14 D (aw D e7):=fun t v c=>by
     obtain⟨f,hf,n1,n2⟩:=bE_dom h.1 r v;rcases A3 f hf with q|q;{exact n1 (q▸(ak.1 ke').2.1)};{exact n2 (q▸c)}
    obtain⟨e1,h1,k1,-,-⟩:=F 3 c a12;rw[(A3 _ h1).resolve_left (fun q=>(cz c a8).2 (by rw[<-aB Z,<-q];exact k1))] at k1;have x0:am e7≠pos 0:=fun q=>M 0 a9 (by rw[<-aB e7,q];exact cd hp i0)
    have z7:=B7 _ k7 x0 (mt (g7 1 i1) V);have zc:=Bx c k t hk ⟨b1.1,b1.2,b2⟩ _ k1 (mt (g7 k hk) a13) (by rw[aB];exact M t a11);have fin:∀y:O,y∈ag 14 D (aw D (am E))->y≠1->y≠2->y≠4->False:=fun y hy b1 b2 b4=>by
     rcases hT y hy b1 b2 b4 7 c V a15 with q|q;{exact K 7 c 1 V a16 z7 q};{exact K c 7 k a17 a18 zc q}
    by_cases c:(13:O)∈ag 14 D (aw D (am e7))
    ·rcases hA _ (U3 e7 h7 (M 13 a10) c) with q|q|q|q<;>try exact mt (g7 _ ((m _).2 V)) V q
     exact fin 3 (by rw[<-q,aB];exact (ak.1 h7).2.1) V V V
    ·obtain⟨f,hf⟩:=jx_dom h r hb (nl 7 V) (cl 7 V) V V (Zs 7) ⟨_,(hp.1 1 i1).2.2.2.1 7 V,(hp.1 1 i1).2.2.2.1 13 V⟩ ⟨0,V,V⟩
     have c0:=hf _ p07 (fun q=>x0 ((by by_contra q;exact c (hf _ k7 q):am e7=f).trans q.symm));rcases hA _ (ak.2 ⟨(hp.1 0 i0).1,c0,fun k=>absurd (_md.1 ((hp.1 0 i0).2.2.1 k)).1 V⟩) with q|q|q|q<;>try exact mt (hp.2 i0 ((m _).2 V)) V q
     exact fin 0 (by rw[<-q];exact cd hp i0) V V V
   by_cases s12:(af 14 D 12).card<=2;{exact G 12 2 5 11 4 6 s12 i2 i4 V V V V V V V V V V};by_cases s11:(af 14 D 11).card<=2;{exact G 11 4 6 12 2 5 s11 i4 i2 V V V V V V V V V V};exact L 7 (ne 7 V (by omega)) (ne 11 V (by omega)) (ne 12 V (by omega)) V V
  by_cases l:(af 14 D 13).card<=3
  ·obtain⟨A,t1,t2,t4⟩:=T l
   refine C (pos 1) (fun P hP=>by rcases A P hP with q|q|q<;>simp[q]) ?_ (fun y hy n _ _=>absurd ((by decide:∀y:O,y∈dom 1->y=1) y ((hp.1 1 i1).2.2.2.2.2.1 hy)) n);by_contra c;obtain⟨f,hf⟩:=J3 (by omega);obtain⟨X,hX,Y,hY,xy⟩:=one_lt_card.1 (by have:=pred_card_le_card_erase (s:=af 14 D 3) (a:=f);omega:1<((af 14 D 3).erase f).card);have G:∀e:ℕ×_d,e∈(af 14 D 3).erase f->e.1∈aW 14 D (ao 14 D {13}):=fun e he=>by
    obtain⟨ef,he⟩:=_me.1 he;exact (q31_G h he (hf e he ef)).resolve_left fun q=>by rcases A e q with rfl|rfl|rfl<;>first|exact absurd (t1 3 (ak.1 he).2.1) V|exact absurd (t2 3 (ak.1 he).2.1) V|exact absurd (t4 3 (ak.1 he).2.1) V
   rcases eq_or_am (card_le_one.1 (by omega) _ (G X hX) _ (G Y hY)) with q|q;{exact xy q};{exact el h.1 (_me.1 hY).2 (q▸(_me.1 hX).2)}
  have hM:aW 14 D (ao 14 D {13})=∅:=card_eq_zero.1 (by omega);obtain⟨E,hE,nE⟩:∃E∈af 14 D 13,E∉({pos 1,pos 2,pos 4}:Finset (ℕ×_d)):=by by_contra q;push Not at q;exact l ((_cl (fun e he=>q e he)).trans card_le_three)
  rw[_mi,_mi,_ms,not_or,not_or] at nE;have A:=gh p1 p2 p4 hE n12 n14 (Ne.symm nE.1) n24 (Ne.symm nE.2.1) (Ne.symm nE.2.2) (by omega);have X1:∀i:O,i∈({1,2,4}:o)->i∈({0,1,2,4}:o)∧aP i 13:=by decide
  have X4:∀i j:O,i∈({1,2,4}:o)->j∈dom i->j=i∧(j≠1->j≠2->j≠4->False):=by decide
  have CT:∀y:O,y∈ag 14 D (aw D (am E))->y≠1->y≠2->y≠4->∀i:O,i∈({1,2,4}:o)->∀t,t∈ag 14 D (aw D (pos i))->dj i t:=fun y hy y1 y2 y4 i hi=>cT_dom h r b0 hp ((m i).2 (X1 i hi).1) (d i hi) (X1 i hi).2 (fun p hq ne s=>by
   rcases A p hq with q|q|q|q;{exact ne (by rw[q,(X4 i 1 hi (s (q▸cd hp i1))).1])};{exact ne (by rw[q,(X4 i 2 hi (s (q▸cd hp i2))).1])};{exact ne (by rw[q,(X4 i 4 hi (s (q▸cd hp i4))).1])};{exact (X4 i y hi (s (q▸hy))).2 y1 y2 y4})
  have G3:∀e:ℕ×_d,e∈af 14 D 3->(13:O)∈ag 14 D (aw D e)->e∈af 14 D 13:=fun e he c=>(q31_G h he c).resolve_right (by rw[hM];exact notMem_empty _)
  refine C E A ?_ ?_
  ·by_contra c;obtain⟨f,hf⟩:=J3 (by omega)
   obtain⟨e1,h1,k1,f1,g1⟩:=F 3 11 V;obtain⟨e2,h2,k2,f2,g2⟩:=F 3 12 V;have R:∀(e:ℕ×_d) (y:O),e∈af 14 D 3->e≠f->(∀i∈aa 14 D,e=pos i->y∈dom i)->y∈ag 14 D (aw D (am e))->(y=11∨y=12)->False:=fun e y he ef fe ky yy=>by
    have N:∀i:O,i∈({1,2,4}:o)->y∉dom i∧y≠i:=by rcases yy with p|p<;>rw[p]<;>decide
    rcases A e (G3 e he (hf e he ef)) with q|q|q|q<;>try exact (N _ V).1 (fe _ ((m _).2 V) q)
    rw[q] at ky;have ct:=CT y ky (N 1 V).2 (N 2 V).2 (N 4 V).2;exact c ((_cl (fun x hx=>by
     by_cases xf:x=f;{rw[xf];exact _mi.2 (Or.inl rfl)};rcases A x (G3 x hx (hf x hx xf)) with rfl|rfl|rfl|rfl<;>first|exact _mi.2 (Or.inr (_mss _))|exact absurd (ct _ V 3 (ak.1 hx).2.1) V)).trans (card_le_two (a:=f) (b:=E)))
   by_cases q1:e1=f
   ·by_cases q2:e2=f
    ·rw[q1] at k1 g1;rw[q2] at k2 g2
     by_cases s11:(af 14 D 11).card<=2
     ·obtain⟨Z,-,W,cz⟩:=U 4 11 i4 V s11;exact (cz 12 V).2 (q31_q W k1 (mt (g1 4 i4) V)▸k2)
     by_cases s12:(af 14 D 12).card<=2
     ·obtain⟨Z,-,W,cz⟩:=U 2 12 i2 V s12;exact (cz 11 V).2 (q31_q W k2 (mt (g2 2 i2) V)▸k1)
     exact L 3 (ne 3 V (by omega)) (ne 11 V (by omega)) (ne 12 V (by omega)) V V
    ·exact R e2 12 h2 q2 f2 (ak.1 k2).2.1 V
   ·exact R e1 11 h1 q1 f1 (ak.1 k1).2.1 V
  ·intro y hy n1 n2 n4;have ct:=CT y hy n1 n2 n4
   have G:∀y:O,y∈({7,11,12}:o)->∃B,∀P∈af 14 D 13,y∈ag 14 D (aw D P)->P=E\/P=B:=fun y hy=>by
    simp only[_mi,_ms] at hy;rcases hy with rfl|rfl|rfl<;>exact⟨_,fun P hP c=>by rcases A P hP with rfl|rfl|rfl|rfl<;>first|exact Or.inl rfl|exact absurd (ct _ V _ c) V|exact Or.inr rfl⟩
   intro a c ha hc;obtain⟨B1,g1⟩:=G a ha;obtain⟨B2,g2⟩:=G c hc;exact q31_T h r hM hZa g1 g2
 obtain⟨u1,u2,hu,R⟩:=_ct2.1 a2;by_cases a:u1∈aZ D b 13<;>by_cases e:u2∈aZ D b 13
 ·exact B (ext fun v=>⟨fun q=>(ay.1 q).1,fun q=>by rw[R,_mi,_ms] at q;rcases q with rfl|rfl;exacts[a,e]⟩)
 ·exact A u1 u2 R a e
 ·exact A u2 u1 (by rw[R,pair_comm]) e a
 obtain⟨v,q⟩:=ne 13 V c13;have:=(ay.1 q).1;rw[R,_mi,_ms] at this;rcases this with rfl|rfl;exacts[a q,e q]
lemma q66_K{p:Prop}(h:p:=by decide +kernel):p:=h
abbrev q66_A:o:={0,9,11,12,13}
abbrev q66_F:o:={9,11,12,13}
abbrev q66_I:o:={2,4,5,6}
abbrev q66_U:o:={0,2,4,5,6,7}
def q66_G(D:Dag)(i:O):Prop:=∃ j s,j<D.length/\cR D j=true/\bz 14 D i.val (aw D (j,!s))/\aF D (aw D (j,!s))=1/\∀ a∈_B.np,(a∈ag 14 D (aw D (j,s))↔aP i a)
lemma q66_L{D:Dag}(e:au 14 D){j}(s)(d:j<D.length):aw D (j,s)<14+j:=by cases s<;>simp[aX,bh,e j d]
lemma q66_o{D:Dag}(e:au 14 D){v w j:ℕ}{s}(p:bz 14 D v w)(q:bz 14 D v (aw D (j,s)))(d:j<D.length)(l:14+j<=w):aF D (aw D (j,s))=1:=by
 have:=q66_L e s d
 rcases bz_chain_or e p (Relation.ReflTransGen.mono (fun _ _ k=>k.1) _ _ q) with c|c
 ·rcases c.cases_head with rfl|⟨_,k,-⟩<;>omega
 ·have:=dt e (fun _ _ k=>k) c;omega
set_option synthInstance.maxSize 4096 in
lemma q66_s:let N:=fun a b:B3=>q3S a b=false;∀ p q:B3,N q p->∀ r:B3,N p r->N r p->N q r->N r q->∀ s:B3,N s r->N p s->N s p->N q s->N s q->∀ e:B3,N e p->N e q->N e r->N e s->∀ f:B3,N f p->N f q->N f r->N f s->N f e->N e f->False:=by intro N;decide +kernel
lemma q66_X{Z:O->B3}{R:O->O->Prop}(K:∀{x t},R x t->q3S (Z x) (Z t)=false)(p q r s:O)(H:R q p/\R p r/\R r p/\R q r/\R r q/\R s r/\R p s/\R s p/\R q s/\R s q/\R 8 p/\R 8 q/\R 8 r/\R 8 s/\R 10 p/\R 10 q/\R 10 r/\R 10 s/\R 10 8/\R 8 10:=by decide +kernel):False:=let⟨a,b,c,d,g,h,i,j,k,l,m,n,o,t,u,v,w,x,y,z⟩:=H;q66_s _ _ (K a) _ (K b) (K c) (K d) (K g) _ (K h) (K i) (K j) (K k) (K l) _ (K m) (K n) (K o) (K t) _ (K u) (K v) (K w) (K x) (K y) (K z)
lemma q66_nw{D:Dag}(h:ai 14 D)(r:ar D){pos:O->ℕ×_d}(hp:bA_dom D pos)(i0:(0:O)∈aa 14 D)(i7:(7:O)∈aa 14 D):val D (bM q66_A) (aw D (pos 0))=false:=by
 by_contra c;rw[_nf] at c;have P:=hp.1 0 i0
 have I:∀ v,v<14+D.length->7∉ag 14 D v->val D (b4 (0:O) 7) v=true->val D (bM q66_A) v=true:=fun v=>v.strong_induction_on fun v ih lv n7 t=>by
  rcases Nat.lt_or_ge v 14 with l|l
  ·simp[bY D _ v l,b4] at t⊢;rcases t with t|t<;>simp[t,dr D ⟨_,l⟩] at n7⊢;decide
  obtain⟨q,rfl⟩:=Nat.exists_eq_add_of_le l;have hq:q<D.length:=by omega
  by_cases e:q=(pos 0).1;{subst e;rw[dz h.1 _ P.1 (pos 0).2,P.2.1,gop_true,Bool.and_eq_true];exact⟨c,gJ h.1 (cl 0) _ (fun i hi=>by simp only[cl,decide_eq_true_eq] at hi;subst hi;decide) _ (ee.1 (cd hp i0))⟩};have A:=h.1 q hq;have N:∀ s,7∉ag 14 D (aw D (q,s)):=fun s m=>e (congrArg Prod.fst ((_ms.1 ((hp.1 7 i7).2.2.2.2.2.2▸ak.2 ⟨hq,m,n7⟩)).trans (congrArg am (_ms.1 (P.2.2.2.2.2.2▸aJ hp i7 (V:aP 7 0))))))
  cases hc:cR D q<;>simp[cS h.1 _ q hq,hc] at t⊢<;>exact t.imp (ih _ (by omega) (by omega) (aX q▸N false)) (ih _ (by omega) (by omega) (bh q▸N true))
 have⟨_,_,d,a,b⟩:=r.2 _ (I (bH 14 D) (by unfold bH;have:=List.length_pos_iff.mpr h.2.2;omega) (by simp[oc r]) (r.1 _ ⟨0,7,V,by simp[b4],by simp[b4]⟩));exact(q66_K:∀ u v,bM q66_A u->bM q66_A v->¬dj u v) _ _ a b d
lemma q66_dup{D:Dag}(a:au 14 D){P:o}(h0:(0:O)∉P){k:ℕ}{s:_d}(hk:k∈du 14 D P)(e:ag 14 D (aw D (k,s))∩P=ag 14 D (14+k)∩P):∃ D':Dag,au 14 D'/\(∀ M,aQ 14 D P M->aQ 14 D' P M)/\(du 14 D' P).card+1<=(du 14 D P).card:=by
 have⟨kW,k2⟩:=_mf.1 hk;have kl:=mem_range.1 (_mf.1 kW).1
 have wl:=q66_L a s kl
 have z0:ag 14 D 0∩P=∅:=by simpa[h0] using congrArg (·∩P) (dr D 0)
 generalize hD:D.set k (false,aw D (k,s),0)=D'
 have L:D'.length=D.length:=by simp[<-hD]
 have G:∀ j,j≠k->cR D' j=cR D j/\cj D' j=cj D j/\ck D' j=ck D j:=fun j n=>by simp[<-hD,cR,cj,ck,n.symm]
 have⟨g0,g1,g2⟩:cR D' k=false/\cj D' k=aw D (k,s)/\ck D' k=0:=by simp[<-hD,cR,cj,ck,kl]
 have a':au 14 D':=fun j hj=>if n:j=k then by subst n;rw[g1,g2];exact⟨wl,by omega,fun q=>by simp[<-e,q,z0] at k2⟩ else(G j n).2.1▸(G j n).2.2▸a j (L▸hj)
 have pt:∀ w,ag 14 D' w∩P=ag 14 D w∩P:=fun w=>w.strong_induction_on fun w ih=>by
  rcases Nat.lt_or_ge w 14 with l|l;{simp[dr _ ⟨w,l⟩]}
  obtain⟨j,rfl⟩:=Nat.exists_eq_add_of_le l
  by_cases hj:j<D.length;swap;{simp[pc,L,not_lt.1 hj]}
  by_cases n:j=k;{subst n;rw[de a' (L▸hj) g0,g1,g2,union_inter_distrib_right,ih _ wl,ih 0 (by omega),z0,union_empty,e]}
  have⟨b,c,d⟩:=G j n;have A:=a j hj;rw[fY a' j (L▸hj),fY a j hj,b,c,d]
  split_ifs
  ·rw[inter_inter_distrib_right,ih _ A.1,ih _ A.2.1,<-inter_inter_distrib_right]
  ·rw[union_inter_distrib_right,ih _ A.1,ih _ A.2.1,<-union_inter_distrib_right]
 refine⟨D',a',fun M ⟨w,hw⟩=>⟨w,(pt w).trans hw⟩,?_⟩
 refine card_erase_add_one hk▸Nat.succ_le_succ (_cl fun j hj=>?_)
 simp only[du,aW,_mf,_me,cC,mem_range,pt,L] at hj⊢
 have n:j≠k:=by rintro rfl;simp[g2,z0] at hj
 exact⟨n,(G j n).2.1▸(G j n).2.2▸hj⟩
lemma q66_sem{D:Dag}(h:ai 14 D)(r:ar D){pos:O->ℕ×_d}(hp:bA_dom D pos)(m:∀ x:O,x∈aa 14 D↔x∈q66_U):(∃ e∈aE 14 D (ao 14 D _B.np),∀ i∈({0,2,4,5,6}:o),e≠pos i)\/(∃ k∈aW 14 D (ao 14 D _B.np),(ag 14 D (14+k)∩_B.np).card=1/\val D (bM q66_A) (14+k)=false)\/(∃ k∈du 14 D _B.np,∃ s,ag 14 D (aw D (k,s))∩_B.np=ag 14 D (14+k)∩_B.np):=by
 have inp:∀ w,w<14->val D (b4 1 9) w=true->ag 14 D w={1}\/ag 14 D w={9}:=fun w l t=>by rw[bY D _ w l] at t;simp[b4] at t;rcases t with rfl|t<;>simp_all[dr D ⟨_,l⟩]
 obtain⟨w,⟨wv,w1,wP⟩,hm⟩:=wellFounded_lt.has_min {w|val D (b4 1 9) w=true/\1∉ag 14 D w/\ag 14 D w∩_B.np=∅} ⟨bH 14 D,r.1 _ ⟨1,9,V,by simp[b4],by simp[b4]⟩,by simp[oc r],by simp[oc r]⟩;have:w<14+D.length:=by_contra fun q=>_fnt ((fs D _ w (by omega)).symm.trans wv)
 have w14:14<=w:=by by_contra q;rcases inp w (by omega) wv with a|a;exacts[w1 (a▸_mss _),absurd (a▸wP) V]
 obtain⟨j,rfl⟩:=Nat.exists_eq_add_of_le w14;have hj:j<D.length:=by omega
 have A:=h.1 j hj;rw[cS h.1 _ j hj] at wv;cases hc:cR D j
 ·simp[hc,de h.1 hj hc,union_inter_distrib_right] at wv w1 wP;exact(wv.elim (hm _ ⟨·,w1.1,wP.1⟩ A.1) (hm _ ⟨·,w1.2,wP.2⟩ A.2.1)).elim
 simp[hc] at wv;rw[cB h.1 hj hc] at w1;have⟨s,s1,sv,ov⟩:∃ s,1∉ag 14 D (aw D (j,s))/\val D (b4 1 9) (aw D (j,s))=true/\val D (b4 1 9) (aw D (j,!s))=true:=if q:1∈ag 14 D (cj D j) then⟨true,bh j▸fun q2=>w1 (_mn.2 ⟨q,q2⟩),bh j▸wv.2,aX j▸wv.1⟩ else⟨false,aX j▸q,aX j▸wv.1,bh j▸wv.2⟩;
 refine if p0:(j,s)=pos 0 then .inr ?_ else .inl ⟨(j,s),fL.2 ⟨hj,nonempty_of_ne_empty fun q=>hm _ ⟨sv,s1,q⟩ (q66_L h.1 s hj),wP▸not_nonempty_empty⟩,fun i hi q=>by rcases(q66_K:∀ i∈({0,2,4,5,6}:o),i=0\/i∈q66_U/\∀ x∈dom i,x≠1/\x∉_B.np) i hi with rfl|⟨u,e⟩;exact p0 q;have d:=q▸(hp.1 i ((m i).2 u)).2.2.2.2.2.1;exact hm _ ⟨ov,fun q1=>(e _ (d q1)).1 rfl,eq_empty_of_forall_notMem fun x hx=>(e x (d (_mn.1 hx).1)).2 (_mn.1 hx).2⟩ (q66_L h.1 (!s) hj)⟩;have:=p0▸q66_L h.1 s hj;rw[p0] at sv;let T:=Relation.ReflTransGen fun a b=>∃ q,q<D.length/\b=14+q/\cR D q=false/\(cj D q=a\/ck D q=a);have RP:∀{u v},T u v->ag 14 D u⊆ag 14 D v/\(∀ x:O->_d,val D x u=true->val D x v=true)/\u<=v:=fun p=>by
  induction p with
  |refl=>exact⟨Subset.rfl,fun _=>id,le_rfl⟩
  |tail _ st ih=>obtain⟨q,ql,rfl,qc,qi⟩:=st;have:=h.1 q ql;rcases qi with rfl|rfl<;>exact⟨ih.1.trans (by simp[de h.1 ql qc]),fun x a=>by simp[cS h.1 _ q ql,qc,ih.2.1 x a],by omega⟩
 obtain⟨w',⟨wr,wt⟩,hm'⟩:=wellFounded_lt.has_min {w'|T w' (aw D (pos 0))/\val D (b4 1 9) w'=true} ⟨_,.refl,sv⟩;have⟨ws,wx,_⟩:=RP wr;have wf:=Bool.eq_false_iff.2 fun q=>_fnt ((q66_nw h r hp ((m 0).2 V) ((m 7).2 V)).symm.trans (wx _ q));have wd:=fun t ht=>(cT_07_uncond hp ((m 0).2 V) ((m 7).2 V)).1 t (ws ht);have w14':14<=w':=by by_contra q;rcases inp w' (by omega) wt with a|a<;>exact absurd (wd _ (a▸_mss _)) V
 obtain⟨k,rfl⟩:=Nat.exists_eq_add_of_le w14';have hk:k<D.length:=by omega
 have:=h.1 k hk;cases kc:cR D k
 ·simp[cS h.1 _ k hk,kc] at wt;rcases wt with t|t<;>exact(hm' _ ⟨wr.head ⟨k,hk,rfl,kc,by simp⟩,t⟩ (by omega)).elim
 have kP:(ag 14 D (14+k)∩_B.np).Nonempty:=nonempty_of_ne_empty fun q=>hm _ ⟨wt,fun q1=>absurd (wd 1 q1) V,q⟩ (by omega);have ki:=cB h.1 hk kc;have kW:k∈aW 14 D (ao 14 D _B.np):=_mf.2 ⟨mem_range.2 hk,cC.2 kP,cC.2 (kP.mono (ki▸inter_subset_inter_right inter_subset_left)),cC.2 (kP.mono (ki▸inter_subset_inter_right inter_subset_right))⟩;have⟨s',fs',ss⟩:∃ s',val D (bM q66_A) (aw D (k,s'))=false/\ag 14 D (14+k)⊆ag 14 D (aw D (k,s')):=by rw[cS h.1 _ k hk,kc,gop_true,Bool.and_eq_false_iff] at wf;rcases wf with q|q;exacts[⟨false,aX k▸q,aX k▸ki▸inter_subset_left⟩,⟨true,bh k▸q,bh k▸ki▸inter_subset_right⟩]
 have sY:ag 14 D (aw D (k,s'))∩_B.np⊆{8,10}:=fun t ht=>by_contra fun q=>_fnt (fs'.symm.trans (gJ h.1 (cl t) (bM q66_A) (fun i hi=>by simp only[cl,bM,decide_eq_true_eq] at hi⊢;subst hi;exact(q66_K:∀ t∈_B.np,t∉({8,10}:o)->t∈q66_A) _ (_mn.1 ht).2 q) _ (ee.1 (_mn.1 ht).1)))
 have:=card_pos.2 kP;have:=_cl sY;have:=_c2 (V:(8:O)≠10);exact if c1:(ag 14 D (14+k)∩_B.np).card=1 then .inl ⟨k,kW,c1,wf⟩ else .inr ⟨k,_mf.2 ⟨kW,by omega⟩,s',(_eqc (inter_subset_inter_right ss) (by omega)).symm⟩
lemma q66_du{D:Dag}(a:au 14 D)(Q:∀ i∈q66_I,aQ 14 D _B.np (aD i))(q0:aQ 14 D _B.np {8,10})(F:Finset o)(hF:∀ M∈F,aQ 14 D _B.np M/\(M=({9,13}:o)\/M=({11,12}:o)\/(3<=M.card/\(M⊆({8,9,10,13}:o)\/M⊆({8,10,11,12}:o))))):9+F.card<=(du 14 D _B.np).card:=by
 have z4:∀ z∈q66_I,z∈i_:=q66_K
 have key:=mI_plus a (P:=_B.np) (Oc3:={2,4,5,6}) (Oc4:=∅) (Oc5:=∅) (a4:=id) (R2:=insert {8,10} (F.filter (·.card=2))) (B0:=F.filter (¬·.card=2)) (B1:=∅) q66_K q66_K q66_K q66_K q66_K q66_K q66_K (fun x hx=>⟨(q66_K:∀ x∈q66_I,aD x⊆_B.np) x hx,Q x hx⟩) nofun nofun
  (fun M hM=>by rcases _mi.1 hM with rfl|hM;exact⟨V,q0,q66_K⟩;have⟨m,c⟩:=_mf.1 hM;have⟨q,e⟩:=hF M m;rcases e with rfl|rfl|e<;>first|exact⟨V,q,q66_K⟩|omega)
  (fun M hM=>by
   have⟨m,c⟩:=_mf.1 hM;have⟨q,e⟩:=hF M m;rcases e with rfl|rfl|⟨m3,e⟩<;>try exact(c V).elim
   have N:∀ z∈i_,¬aD z⊆M:=fun z hz q=>have⟨u,v⟩:=(q66_K:∀ z∈i_,¬aD z⊆({8,9,10,13}:o)/\¬aD z⊆({8,10,11,12}:o)) z hz;e.elim (u<|q.trans ·) (v<|q.trans ·)
   have:M.card<=4:=by rcases e with e|e<;>exact(_cl e).trans V
   exact⟨q,fun q=>by have⟨z,hz,e⟩:=_mg.1 q;exact N z (z4 z hz) e.le,by simp,fun q=>c (by rcases _mi.1 q with rfl|q;decide;exact(_mf.1 q).2),if h:M.card=3 then .inl ⟨h,fun z hz q=>N z hz q.ge⟩ else .inr ⟨by omega,fun z hz=>N z (z4 z hz)⟩,nofun,nofun⟩)
  nofun q66_K
 have:=card_filter_add_card_filter_not (s:=F) (·.card=2);simp[card_insert_of_notMem (fun q=>absurd (hF _ (_mf.1 q).1).2 V:({8,10}:o)∉F.filter (·.card=2))] at key;omega
set_option synthInstance.maxSize 4096 in
lemma orb_66 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨66,V⟩):False:=by
 have hT:=aV 14 D;rw[hI,(V:(bU ⟨66,V⟩).card=6)] at hT
 by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 _ hI}
 by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 _ V hI}
 have:=bg 14 D;have⟨b,hb⟩:=b_dom h.1 r;have⟨pos,hp⟩:=bQ_dom h r;have:=bS_dom h.1 hb
 have m:∀ x:O,x∈aa 14 D↔x∈q66_U:=fun x=>by rw[hI];rfl
 have i0:=(m 0).2 V;have i7:=(m 7).2 V
 have C:∀ x:O,isClean (aa 14 D) x:=by rw[hI];decide
 have c7:=cT_07_uncond hp i0 i7
 have N:∀ x∈_B.np,(aZ D b x).Nonempty:=fun x hx=>by
  have⟨i,j,v,a,c,d,e⟩:=(q66_K:∀ x∈_B.np,∃ i j v:O,i∈q66_U/\j∈q66_U/\(i≠j/\ac i x=true/\ac j x=true/\ac x v=true/\v≠i/\v≠j)/\(v∈q66_U\/v∉dom i/\v∉dom j)) x hx
  exact _cp.1 (by have:=bj_clean h r hb (C x);have:=cx_dom h r hp ((m i).2 a) ((m j).2 c) d (e.imp (m v).2 id);omega)
 rcases(by omega:(aj 14 D b).card=2\/(aj 14 D b).card=3/\bL 14 D<=1\/(aj 14 D b).card=4/\bL 14 D=0)with a|⟨a,l⟩|⟨a,l⟩
 ·have W:∀ v t:O,(∀ i∈({0,2,4,5,6}:o),aP i t\/t∉dom v/\t∉dom i/\∃ q,ac i v=true/\ac i q=true/\mV v t q=true)->(aZ D b v).Nonempty->¬aZ D b v⊆aZ D b t:=fun v t g a s=>by
   have A:({0,2,4,5,6}:o)⊆aa 14 D:=by rw[hI];decide
   have:=card_le_card_of_injOn pos (fun i hi=>have c:=A hi;(g i hi).elim (aJ hp c) fun ⟨d,e,q,f⟩=>cV_dom hp c (cy_dom h r hb hp (C v) c s a d f) e) fun _ i _ j=>hp.2 (A i) (A j)
   have:=bj_clean h r hb (C t);have:=_cfl (aj 14 D b) (fun u=>t∈ag 14 D u.1);unfold aZ at *;rw[(V:({0,2,4,5,6}:o).card=5)] at *;omega
  have n8:=N 8 V;have n10:=N 10 V;have⟨y,hy⟩:=N 9 V
  have k:∀ v:O,v=8\/v=10->¬aZ D b v⊆aZ D b 9:=fun v e s=>by rcases e with rfl|rfl<;>exact absurd (c7.1 _ (cy_dom h r hb hp (q:=7) (C _) i0 s (N _ V) V ⟨V,V,V⟩)) V
  have⟨u1,u2,hu,hU⟩:=_ct2.1 a
  have S:∀ x,aZ D b x⊆{u1,u2}:=fun x=>hU▸_fs _ _
  have hy2:=S 9 hy;simp only[_mi,_ms] at hy2
  rcases dJ hu (S 8) (S 10) n8 n10 (W 8 10 q66_K n8) (W 10 8 q66_K n10) with ⟨e1,e2⟩|⟨e1,e2⟩<;>rcases hy2 with rfl|rfl<;>first|exact k 8 (.inl rfl) (by rw[e1];simpa)|exact k 10 (.inr rfl) (by rw[e2];simpa)
 ·have⟨c,hc,G⟩:∃ c∈q66_I,∀ i∈q66_I,i≠c->q66_G D i:=by
   have hd:∀ i∈q66_I,dom i⊆aa 14 D:=by rw[hI];decide
   have A:∀ a∈_B.np,∀ b∈_B.np,¬dj a b:=q66_K
   have M:∀ i∈q66_I,∀ a∈_B.np,dj i a->aP i a:=q66_K
   have S:∀ i∈q66_I,bz 14 D i.val (bH 14 D)->q66_G D i:=fun i n p=>by
    have⟨j,s,d,c,q,e⟩:=jL_dom h.1 r _ A (M i n) p;exact⟨j,s,d,c,q,q66_o h.1 p q d (by unfold bH;omega),e⟩
   by_cases a:∀ i∈q66_I,bz 14 D i.val (bH 14 D);{exact⟨2,V,fun i n _=>S i n (a i n)⟩}
   push Not at a;have⟨c,hc,nc⟩:=a;have⟨w,cw,w2,we⟩:=(iI_dom h r (hd c hc)).resolve_left nc
   refine⟨c,hc,fun i n ic=>?_⟩
   rcases iI_dom h r (hd i n) with p|⟨v,iw,v2,ve⟩;{exact S i n p}
   obtain rfl:v=w:=by_contra fun n=>by have:=ph h.1 {v,w} (by simp[*]);rw[_c2 n] at this;omega
   have⟨k,s,d,c,t,q,e⟩:=iJ_dom h.1 r _ A (M i n) iw (ds h.1 cw) ((q66_K:∀ i∈q66_I,∀ j∈q66_I,i≠j->∃ a∈_B.np,aP j a/\¬aP i a) i n c hc ic)
   exact⟨k,s,d,c,q,q66_o h.1 iw q d t,e⟩
  obtain⟨u,v,w,-,-,-,e⟩:=card_eq_three.1 a
  have K:∀{x t:O},x∈_B.np/\t∈_B.np/\t∉dom x/\((∃ i q:O,i∈q66_I/\i≠c/\ac i x=true/\ac i q=true/\mV x t q=true/\bK i t=false)\/ac 0 x=true/\mV x t 7=true/\¬dj 0 t)->q3S (q3Z D b u v w x) (q3Z D b u v w t)=false:=fun ⟨x8,t8,nt,g⟩=>Bool.eq_false_iff.2 fun s=>by
   have hs:=q3s e s;have⟨u',hu⟩:=N _ x8
   rcases g with ⟨i,q,hi,ic,gx,gq,gm,gt⟩|g
   ·obtain⟨⟨⟨xt,-⟩,-⟩,z,xz,tz,-⟩:=by simpa[mV] using gm
    have⟨ur,xu⟩:=ay.1 hu
    have⟨f,hf⟩:=jx_dom h r hb (fC ur xu) (C _) xt nt hs ⟨_,xu,(ay.1 (hs hu)).2⟩ ⟨z,xz,b3.2 fun d=>b3.1 tz (lL d)⟩
    have⟨j,s,d,c,w,o,e⟩:=G i hi ic;have A:=fun(v:O)(g:aP i v)=>jV_dom h.1 r d s c w o (by unfold bH;omega) g
    have⟨y,m,n,l⟩:=bE_dom h.1 r gm
    obtain rfl:(j,s)=f:=by_contra fun k=>b3.1 gt (.inl ((e _ t8).1 (hf _ (ak.2 ⟨d,A _ ((ae _ _).1 gx),fun k=>(q66_K:∀ a b:O,ac a b=true->b∉dom a) i _ gx (fk_dom h.1 r i _ (ds h.1 w) (cr h.1 d c (!s) k))⟩) k)))
    obtain rfl:y=_:=by_contra fun k=>n (hf _ m k)
    exact l (A q ((ae _ _).1 gq))
   ·exact g.2.2 (c7.1 _ (cy_dom h r hb hp (C _) i0 hs (N _ x8) nt ⟨g.1,V,g.2.1⟩))
  simp only[_mi,_ms] at hc;rcases hc with rfl|rfl|rfl|rfl;exacts[q66_X @K 12 9 13 11,q66_X @K 11 9 13 12,q66_X @K 9 11 12 13,q66_X @K 9 12 11 13]
 ·classical
  let P:=_B.np;let U(w:ℕ):=ag 14 D w∩P
  let Y(f:O):o:=if f=9\/f=13 then {1,11,12} else {3,9,13}
  let I:=insert 0 q66_I;let A:=q66_F
  have:=co h P (by simp[oc r]);have u:(al 14 D)ᶜ=q66_U:=hI
  have:=cZ_dom h.1 hb P (by rw[<-compl_compl (al 14 D),u];decide)
  have:=_cl (inter_subset_left:P∩al 14 D⊆P);have:P.card=6:=V
  have⟨Es,Ec⟩:=e6_dom hp P I (by rw[hI];decide);have:I.card=5:=V
  have J:∀ i∈q66_I,dom i⊆aa 14 D/\aD i⊆P/\bX i∩P⊆aD i/\i∈aa 14 D:=by rw[hI];decide
  have p0:U (aw D (pos 0))={8,10}:=Subset.antisymm (fun t ht=>(q66_K:∀ t∈P,dj 0 t->t∈({8,10}:o)) t (_mn.1 ht).2 (c7.1 t (_mn.1 ht).1)) (by rw[insert_subset_iff,singleton_subset_iff];constructor<;>exact _mn.2 ⟨(hp.1 0 i0).2.2.2.1 _ V,V⟩)
  let w(m:o)(s:Bool):O:=let l:List O:=[9,11,12,13];((if s then l else l.reverse).find? (·∈m)).getD 0
  let H(m:o):Prop:=m={9,13}\/m={11,12}\/3<=m.card/\(m⊆{8,9,10,13}\/m⊆{8,10,11,12})
  let F:=univ.filter fun m=>aQ 14 D P m/\H m;let v:=val D (bM q66_A)
  let x(e:ℕ×_d):=if v (aw D e) then w (U (aw D e)) false else 0
  have c{D':Dag}(a:au 14 D')(t:∀ m,aQ 14 D P m->aQ 14 D' P m):=q66_du a (fun i j=>let⟨b,c,d,_⟩:=J i j;t _ (qw_dom h r l q66_K b c d)) (t _ ⟨_,p0⟩) F fun m j=>(_mf.1 j).2.imp_left (t m)
  let d:=du 14 D P;let z:=∃ k∈d,∃ s,U (aw D (k,s))=U (14+k)
  let Z:=if z then insert ∅ F else F
  have FZ:F⊆Z:=by unfold Z;split_ifs<;>simp
  have:9+Z.card<=d.card:=by
   unfold Z;split_ifs with z
   ·have⟨k,j,s,e⟩:=z;have⟨D',a',t,n⟩:=q66_dup h.1 (P:=P) V j e
    have:=c a' t;have:=card_insert_le (∅:o) F;unfold d P;unfold P at n;omega
   ·exact c h.1 fun _=>id
  let V':=ao 14 D P;let E:=aE 14 D V'\I.image pos;let W:=aW 14 D V'\d
  have k0:∀ k∈aW 14 D V',(U (14+k)).card=1->k∈W:=fun k j n=>by unfold U at n;simpa[W,d,du,n] using j
  let S:=Z.disjSum (E.disjSum W)
  let B(t:o⊕((ℕ×_d)⊕ℕ))(s:Bool):O:=t.elim (w · s) (Sum.elim (fun e=>if e.2=s then x e else 0) (fun k=>x (k,s)))
  have c:q66_A.card<=(S×ˢ(univ:Finset Bool)).card:=card_le_card_of_surjOn (fun u=>B u.1 u.2) fun f j=>by
   change ∃u∈S×ˢuniv,B u.1 u.2=f;simp[S,-Bool.exists_bool]
   rcases _mi.1 j with rfl|j
   ·rcases q66_sem h r hp m with ⟨e,a,b⟩|⟨k,a,b,c⟩|q
    ·exact .inr (.inl ⟨e.1,e.2,_md.2 ⟨a,fun z=>let⟨i,j,z⟩:=_mg.1 z;b i j z.symm⟩,!e.2,by simp[B]⟩)
    ·right;right;refine⟨k,k0 k a b,?_⟩
     by_contra p;push Not at p
     have N(s:Bool):v (aw D (k,s))=true:=by_contra fun n=>p s (by simp[B,x,n])
     unfold v at N;rw[dz h.1 _ (mem_range.1 (_mf.1 a).1) false,N,N] at c;cases z:cR D k<;>simp[z] at c
    ·exact .inl ⟨∅,by unfold Z;rw[if_pos (q:z)];simp,false,rfl⟩
   have⟨g,y,fp,n0,nn,o,t⟩:=(q66_K:∀ f∈A,(∀ a∈Y f,∀ b∈Y f,¬dj a b)/\(∃ a∈Y f,aP f a)/\f∈P/\¬dj 0 f/\(∀ i∈q66_I,∃ a∈Y f,aP i a)/\(∀ i,cl f i=true->bM q66_A i=true)/\∀ m⊆P\Y f,f∈m->H m/\(∃ s,w m s=f)\/m.card<=2/\w m false=f) f j
   have⟨k,s,kl,kr,ft,fn,ds⟩:=fm_dom h.1 r (Y f) g f y
   let M:=U (aw D (k,s));have u:M⊆P\Y f:=fun _ ht=>_md.2 ⟨(_mn.1 ht).2,_dl.1 ds (_mn.1 ht).1⟩
   rcases t M u (_mn.2 ⟨ft,fp⟩) with ⟨z,a⟩|⟨sm,eq⟩
   ·exact .inl ⟨M,FZ (_mf.2 ⟨mem_univ _,⟨_,rfl⟩,z⟩),a⟩
   have e:x (k,s)=f:=by simpa[x,v,gJ h.1 _ _ o _ (ee.1 ft)] using eq
   have b:=lq h.1 (show dG 14 D P _ f (k,s) from ⟨kl,kr,fp,ft,fn,u,sm⟩);rcases q:ch 14 D P (k,s) with v|k<;>rw[q] at b
   ·obtain⟨rfl,-⟩:=iX q;refine .inr (.inl ⟨k,s,_md.2 ⟨b.1,?_⟩,s,by simpa[B] using e⟩)
    intro z;have⟨i,hi,q⟩:=_mg.1 z;rcases _mi.1 hi with rfl|hi
    ·exact n0 (c7.1 _ (q▸ft))
    ·have⟨a,y,p⟩:=nn i hi;exact _dl.1 ds (q▸(hp.1 i (J i hi).2.2.2).2.2.2.1 a p) y
   ·obtain⟨rfl,-⟩:=kR q;exact .inr (.inr ⟨_,k0 _ b.1 b.2,_,e⟩)
  have Wd:d⊆aW 14 D (ao 14 D P):=_fs _ _
  have:=_cl Wd;have:=_cl Es
  simp[S,E,W,V',card_sdiff_of_subset Es,card_sdiff_of_subset Wd,(V:q66_A.card=5)] at c;omega
lemma q46_a {D:Dag} (h:ai 14 D) {x:O} {e:ℕ×_d} (he:e∈af 14 D x) (hx:x∈ag 14 D (aw D (am e))):False:=by
 obtain⟨a,b,c⟩:=ak.1 he;rw[cB h.1 a (cY h.1 he)] at c;cases f:e.2<;>simp[aw,am,f] at b hx<;>exact c (_mn.2 (by first|exact⟨b,hx⟩|exact⟨hx,b⟩))
lemma q46_q {α:Type} [DecidableEq α] {s:Finset α} {a z e:α} (W:s={a,z}) (k:e∈s) (n:e≠a):e=z:=by rw[W,_mi,_ms] at k;exact k.resolve_left n
lemma q46_G {D:Dag} (h:ai 14 D) {x y:O} {e:ℕ×_d} (he:e∈af 14 D x) (c:y∈ag 14 D (aw D e)):e∈af 14 D y\/e.1∈aW 14 D (ao 14 D {y}):=by
 by_cases k:y∈ag 14 D (14+e.1)
 · right;have q:=k;rw[cB h.1 (ak.1 he).1 (cY h.1 he),_mn] at q
   simp only[aW,_mf,mem_range,b7];exact⟨(ak.1 he).1,k,q.1,q.2⟩
 · exact Or.inl (ak.2 ⟨(ak.1 he).1,c,k⟩)
lemma q46_T {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} {x y z:O} (hM:aW 14 D (ao 14 D {x})=∅) (hZ:∀u∈aj 14 D b,x∈ag 14 D u.1) {E A B:ℕ×_d} (a:∀P∈af 14 D x,y∈ag 14 D (aw D P)->P=E\/P=A) (c:∀P∈af 14 D x,z∈ag 14 D (aw D P)->P=E\/P=B):aZ D b y⊆aZ D b z\/aZ D b z⊆aZ D b y:=by
 by_contra n;rw[not_or,not_subset,not_subset] at n;obtain⟨⟨u,hu,nu⟩,w,hw,nw⟩:=n
 have L:∀(v:Σ _:ℕ,ℕ) (t:O) (C:ℕ×_d),v∈aZ D b t->(∀P∈af 14 D x,t∈ag 14 D (aw D P)->P=E\/P=C)->Relation.ReflTransGen (bk_x D x) v.1 (aw D E):=fun v t C hv k=>by
  obtain⟨hR,ht⟩:=ay.1 hv
  obtain⟨P,Q,pq,hP,hQ,rP,rQ⟩:=dV_tree h r hM (hZ v hR) (by have:=(dW.1 (_mf.1 (_md.1 hR).1).1).2;omega)
  rcases k P hP (bk_x_ag h.1 hM rP ht) with q|q
  · rw[<-q];exact rP
  · rcases k Q hQ (bk_x_ag h.1 hM rQ ht) with q'|q'
    · rw[<-q'];exact rQ
    · exact absurd (by rw[q,q']) pq
 rcases reconv_aW h.1 hM (L u y A hu a) (L w z B hw c) with s|s
 · exact nw (ay.2 ⟨(ay.1 hw).1,s (ay.1 hu).2⟩)
 · exact nu (ay.2 ⟨(ay.1 hu).1,s (ay.1 hw).2⟩)
lemma q46_k {α:Type} {R:Finset α} {a b c d:α} {Y Z:α->Prop} (hR:∀P∈R,P=a\/P=b\/P=c\/P=d) (ya:¬Y a) (za:¬Z a) (yy:¬Y b\/¬Y c\/¬Y d) (zz:¬Z b\/¬Z c\/¬Z d):∃E A B:α,(∀P∈R,Y P->P=E\/P=A)/\(∀P∈R,Z P->P=E\/P=B):=by
 have F:∀(E A:α) (W:α->Prop),¬W a->(∀P,P=b\/P=c\/P=d->W P->P=E\/P=A)->∀P∈R,W P->P=E\/P=A:=fun E A W w k P hP p=>by rcases hR P hP with q|q;{rw[q] at p;exact absurd p w};{exact k P q p}
 rcases yy with y|y|y <;> rcases zz with z|z|z
 · exact⟨c,d,d,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨d,c,b,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨c,d,b,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨d,b,c,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨b,d,d,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨b,d,c,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨c,b,d,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨b,c,d,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
 · exact⟨b,c,c,F _ _ _ ya (by rintro P (rfl|rfl|rfl) p <;> simp_all),F _ _ _ za (by rintro P (rfl|rfl|rfl) p <;> simp_all)⟩
lemma q46_i {D:Dag} (h:ai 14 D) {x:O} {e f:ℕ×_d} (he:e∈af 14 D x) (hf:f∈af 14 D x) (k:e.1=f.1):e=f:=by
 by_contra n
 have q:am e=f:=by rcases e with ⟨a,c⟩;rcases f with ⟨a',c'⟩;simp only[am] at *;subst k;cases c<;>cases c'<;>simp_all
 exact q46_a h he (by rw[q];exact (ak.1 hf).2.1)
lemma q46_w {D:Dag} {y:O} {e:ℕ×_d} (k:e.1∈aW 14 D (ao 14 D {y})):y∈ag 14 D (aw D e):=by
 simp only[aW,_mf,mem_range,b7] at k;unfold aw;split
 · exact k.2.2.2
 · exact k.2.2.1
lemma q46_c {D:Dag} (h:ai 14 D) {x y:O} {T G:Finset (ℕ×_d)} (hT:T⊆af 14 D y) (hx:∀e∈T,x∈ag 14 D (aw D e)) (hG:G⊆af 14 D x) (d:∀e∈G,e∉T):T.card+G.card<=(af 14 D x).card+(aW 14 D (ao 14 D {x})).card:=by
 classical
 have a:=card_filter_add_card_filter_not (s:=T) (fun e=>e∈af 14 D x)
 have c:(T.filter (fun e=>e∈af 14 D x)).card+G.card<=(af 14 D x).card:=by
  rw[<-card_union_of_disjoint (disjoint_left.2 fun e he g=>d e g (mem_filter.1 he).1)]
  exact card_le_card (union_subset (fun e he=>(mem_filter.1 he).2) hG)
 have c':(T.filter (fun e=>¬e∈af 14 D x)).card<=(aW 14 D (ao 14 D {x})).card:=card_le_card_of_injOn Prod.fst (fun e he=>by rw[mem_coe] at he;exact (q46_G h (hT (mem_filter.1 he).1) (hx e (mem_filter.1 he).1)).resolve_left (mem_filter.1 he).2) (fun e he f hf k=>by rw[mem_coe] at he hf;exact q46_i h (hT (mem_filter.1 he).1) (hT (mem_filter.1 hf).1) k)
 omega
lemma q46_S {D:Dag} (h:ai 14 D) (r:ar D) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) {x i:O} {w:Σ _:ℕ,ℕ} (i0:(0:O)∈aa 14 D) (hi:i∈aa 14 D) (g:aP 0 x/\aP i x/\aP i 13/\mV x 7 13=true/\(0:O)≠i) (h7:aZ D b 7={w}) (hx:x∈ag 14 D w.1) (h13:(13:O)∈ag 14 D w.1) (c7:3<=(af 14 D 7).card) (n0:pos 0∉af 14 D 13) (ti:(7:O)∉ag 14 D (aw D (pos i))) (c8:(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=4):False:=by
 obtain⟨P,Q,pq,hP,hQ,hy⟩:=dV_dom h r hb (Or.inl ⟨V,V,V,V⟩) h7 c7
 obtain⟨f,hf,n7,n13⟩:=bE_dom h.1 r g.2.2.2.1
 have a0:=aJ hp i0 g.1;have a1:=aJ hp hi g.2.1
 have N:∀e∈af 14 D 7,(13:O)∈ag 14 D (aw D e)->e∉({pos 0,pos i,f}:Finset (ℕ×_d)):=fun e he k q=>by
  rw[_mi,_mi,_ms] at q;rcases q with q|q|q
  · exact n0 (cV_dom hp i0 (by rw[<-q];exact k) V)
  · exact ti (by rw[<-q];exact (ak.1 he).2.1)
  · exact n7 (by rw[<-q];exact (ak.1 he).2.1)
 have c3:({pos 0,pos i,f}:Finset (ℕ×_d)).card=3:=card_eq_three.2 ⟨_,_,_,fun e=>g.2.2.2.2 (hp.2 i0 hi e),fun e=>n7 (by rw[<-e];exact (hp.1 0 i0).2.2.2.1 7 V),fun e=>n13 (by rw[<-e];exact (hp.1 i hi).2.2.2.1 13 g.2.2.1),rfl⟩
 have:=q46_c h (x:=x) (y:=7) (T:={P,Q}) (G:={pos 0,pos i,f}) (by intro e he;rw[_mi,_ms] at he;rcases he with rfl|rfl;{exact hP};{exact hQ}) (by intro e he;rw[_mi,_ms] at he;rcases he with rfl|rfl;{exact (hy x hx).1};{exact (hy x hx).2}) (by intro e he;rw[_mi,_mi,_ms] at he;rcases he with rfl|rfl|rfl;{exact a0};{exact a1};{exact hf}) (fun e he k=>by rw[_mi,_ms] at k;rcases k with rfl|rfl;{exact N _ hP (hy 13 h13).1 he};{exact N _ hQ (hy 13 h13).2 he})
 rw[_c2 pq,c3] at this;omega
lemma q46_X {D:Dag} (h:ai 14 D) (r:ar D) {pos:O->ℕ×_d} (hp:bA_dom D pos) (m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,9}:o)) (s1:(af 14 D 1).card<=2) (s3:(af 14 D 3).card<=2) (s7:(af 14 D 7).card<=2) (s12:(af 14 D 12).card<=2):False:=by
 have i2:(2:O)∈aa 14 D:=(m 2).2 V;have i9:(9:O)∈aa 14 D:=(m 9).2 V
 have mi:∀{e f:ℕ×_d},am e=am f->e=f:=fun {e f} q=>by rw[<-aB e,q,aB]
 obtain⟨Z1,-,W1,c1⟩:=qu_dom h r hp i9 (by decide:aP 9 1) V s1
 obtain⟨Z2,-,W2,c2⟩:=qu_dom h r hp i2 (by decide:aP 2 12) V s12
 obtain⟨a1,h1,k1,f1,-⟩:=bf h r hp (by decide:aP 1 7);obtain⟨a2,h2,k2,f2,-⟩:=bf h r hp (by decide:aP 1 13)
 have E1:a1=Z1:=by rw[W1,_mi,_ms] at h1;exact h1.resolve_left (fun e=>absurd (f1 9 i9 e) V)
 have E2:a2=Z1:=by rw[W1,_mi,_ms] at h2;exact h2.resolve_left (fun e=>absurd (f2 9 i9 e) V)
 obtain⟨f,hf,n11,n13⟩:=bE_dom h.1 r (by decide:mV 7 11 13=true)
 have A7:=gG (show am Z1∈af 14 D 7 by rw[<-E1];exact k1) hf (fun e=>n13 (by rw[<-e,<-E2];exact (ak.1 k2).2.1)) s7
 obtain⟨e7,h7,k7,-,-⟩:=bf h r hp (by decide:aP 3 7);obtain⟨e1,h1',k1',-,-⟩:=bf h r hp (by decide:aP 3 11);obtain⟨e2,h2',k2',-,g2⟩:=bf h r hp (by decide:aP 3 12)
 have E3:am e2=Z2:=by rw[W2,_mi,_ms] at k2';exact k2'.resolve_left (fun e=>absurd (g2 2 i2 e) V)
 have q:e7=e1:=by
  by_contra n;have:=d6 h7 h1' h2' n (fun e=>(c2 7 V).2 (by rw[<-E3,<-e];exact k7)) (fun e=>(c2 11 V).2 (by rw[<-E3,<-e];exact k1'));omega
 rcases A7 _ k7 with p|p
 · exact (c1 3 V).2 (by rw[<-mi p];exact h7)
 · exact n11 (by rw[<-p,q];exact (ak.1 k1').2.1)
lemma q46_Y {D:Dag} (h:ai 14 D) (r:ar D) {pos:O->ℕ×_d} (hp:bA_dom D pos) (m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,9}:o)) (s1:(af 14 D 1).card<=2) (s3:(af 14 D 3).card<=2) (s7:(af 14 D 7).card<=2) (s11:(af 14 D 11).card<=2):False:=by
 have i0:(0:O)∈aa 14 D:=(m 0).2 V;have i4:(4:O)∈aa 14 D:=(m 4).2 V;have i9:(9:O)∈aa 14 D:=(m 9).2 V
 have mi:∀{e f:ℕ×_d},am e=am f->e=f:=fun {e f} q=>by rw[<-aB e,q,aB]
 obtain⟨Z1,-,W1,c1⟩:=qu_dom h r hp i9 (by decide:aP 9 1) V s1
 obtain⟨Z4,-,W4,c4⟩:=qu_dom h r hp i4 (by decide:aP 4 11) V s11
 obtain⟨a1,h1,k1,f1,-⟩:=bf h r hp (by decide:aP 1 7)
 have E1:a1=Z1:=by rw[W1,_mi,_ms] at h1;exact h1.resolve_left (fun e=>absurd (f1 9 i9 e) V)
 obtain⟨e7,h7,k7,-,-⟩:=bf h r hp (by decide:aP 7 3);obtain⟨e1,h1',k1',-,g1⟩:=bf h r hp (by decide:aP 3 11);obtain⟨e6,h6,k6,-,g6⟩:=bf h r hp (by decide:aP 6 11)
 have E3:am e1=Z4:=by rw[W4,_mi,_ms] at k1';exact k1'.resolve_left (fun e=>absurd (g1 4 i4 e) V)
 have E6:am e6=Z4:=by rw[W4,_mi,_ms] at k6;exact k6.resolve_left (fun e=>absurd (g6 4 i4 e) V)
 have A7:=gG (show am Z1∈af 14 D 7 by rw[<-E1];exact k1) h7 (fun e=>(c1 3 V).2 (by rw[<-aB Z1,e];exact k7)) s7
 have A3:=gG h1' k7 (fun e=>(c4 7 V).2 (by rw[<-E3,e,aB];exact h7)) s3
 obtain⟨f,hf,n0,n6⟩:=bE_dom h.1 r (by decide:mV 3 0 6=true)
 rcases A3 f hf with p|p
 · exact n6 (by rw[p,mi (E3.trans E6.symm)];exact (ak.1 h6).2.1)
 rcases A7 _ (aJ hp i0 (by decide:aP 0 7)) with q|q
 · exact (c1 0 V).1 (by rw[<-aB Z1,<-q];exact cd hp i0)
 · exact n0 (by rw[p,<-q];exact cd hp i0)
lemma q46_A {D:Dag} (h:ai 14 D) (r:ar D) (b0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,9}:o)) {u w:Σ _:ℕ,ℕ} (hR:aj 14 D b={u,w}) (hZ:aZ D b 13={u}):False:=by
 have i0:(0:O)∈aa 14 D:=(m 0).2 V;have i2:(2:O)∈aa 14 D:=(m 2).2 V;have i4:(4:O)∈aa 14 D:=(m 4).2 V;have i9:(9:O)∈aa 14 D:=(m 9).2 V
 have hd:∀ x:O,x∈dom 2\/x∈dom 4\/x∈dom 9->x∈({0,2,4,9}:o):=by decide
 have d2:dom 2⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inl c));have d4:dom 4⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inr (Or.inl c)));have d9:dom 9⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inr (Or.inr c)))
 have cl:∀ x:O,x≠8->x≠10->isClean (aa 14 D) x:=fun x a c=>by by_cases g:x=1\/x=3;{exact Or.inr (Or.inl ⟨g,i0⟩)};{left;push Not at g;exact⟨g.1,g.2,a,c⟩}
 have bj:=fun x a c=>bj_clean h r hb (cl x a c)
 have c13:=cx_dom h r hp i2 i4 (u:=13) (v:=1) ⟨V,V,V,V,V,V⟩ (Or.inr V)
 have l13:(af 14 D 13).card<=3:=by have:=bj 13 V V;rw[hZ,_cs] at this;omega
 have t2:=dy_dom h r b0 hp (i1:=2) (i2:=4) (v3:=1) i2 i4 d2 ⟨V,V,V,V,V,V⟩ (Or.inr V) V V l13
 have t4:=dy_dom h r b0 hp (i1:=4) (i2:=2) (v3:=1) i4 i2 d4 ⟨V,V,V,V,V,V⟩ (Or.inr V) V V l13
 have H:=eF_cand_dom_u h r hb hp (cl 13 V V) hZ i2 i4 (v3:=1) ⟨V,V,V,V,V,V⟩ (Or.inr V) t2 t4
 have K0:∀ y:O,((dj 2 y/\dj 4 y)\/(dj 2 y/\∀ q:O,ac 4 q=true->mV 13 y q=false)\/(dj 4 y/\∀ q:O,ac 2 q=true->mV 13 y q=false))->y=8\/y=10\/y=13:=by simp only[<-cW];decide +kernel
 have nu:∀ y:O,y≠8->y≠10->y≠13->y∉ag 14 D u.1:=fun y a c d e=>by rcases K0 y (H y e) with g|g|g <;> contradiction
 have zs:∀ y:O,y∉ag 14 D u.1->aZ D b y⊆{w}:=fun y g v c=>by obtain⟨a,c⟩:=ay.1 c;rw[hR,_mi] at a;rcases a with rfl|a;{exact absurd c g};{exact a}
 have zr:∀ y:O,y≠8->y≠10->y≠13->w∉aZ D b y->(af 14 D y).card<=2:=fun y a c d e=>by
  have k:aZ D b y=∅:=eq_empty_iff_forall_notMem.2 fun v hv=>e (by rw[<-_ms.1 (zs y (nu y a c d) hv)];exact hv)
  have:=bj y a c;rw[k,_ce] at this;omega
 have sb:∀ x t:O,w∈aZ D b t->x≠8->x≠10->x≠13->aZ D b x⊆aZ D b t:=fun x t c a d g v hv=>by rw[_ms.1 (zs x (nu x a d g) hv)];exact c
 have mi:∀{e f:ℕ×_d},am e=am f->e=f:=fun {e f} q=>by rw[<-aB e,q,aB]
 have h7:(7:O)∈al 14 D:=by by_contra c;exact absurd ((m 7).1 (aN.2 c)) V
 have z8:(aZ D b 8).Nonempty:=nonempty_iff_ne_empty.2 fun z=>no_leak_2nbrs h r b0 hb hp (x:=8) (v3:=6) h7 V V z i2 i0 V V V V V V (Or.inr V) V (fun k=>by have:=cx_dom h r hp (u:=8) (v:=6) i2 i0 ⟨V,V,V,V,V,V⟩ (Or.inr V);have:=bj_noleak h r hb (x:=8) (fun _ _=>k);rw[z,_ce] at this;omega)
 have z10:(aZ D b 10).Nonempty:=nonempty_iff_ne_empty.2 fun z=>no_leak_2nbrs h r b0 hb hp (x:=10) (v3:=5) h7 V V z i4 i0 V V V V V V (Or.inr V) V (fun k=>by have:=cx_dom h r hp (u:=10) (v:=5) i4 i0 ⟨V,V,V,V,V,V⟩ (Or.inr V);have:=bj_noleak h r hb (x:=10) (fun _ _=>k);rw[z,_ce] at this;omega)
 by_cases a11:w∈aZ D b 11
 · have K:=fun (t:O) g c=>orb49_cut h r b0 hb 11 t 4 13 (cl 11 V V) d4 g ⟨w,a11⟩ (sb 11 t c V V V)
   exact q46_X h r hp m (zr 1 V V V (fun c=>orb49_cut h r b0 hb 1 11 9 5 (cl 1 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 1 11 a11 V V V))) (zr 3 V V V (K 3 ⟨V,V,V,V,V⟩)) (zr 7 V V V (K 7 ⟨V,V,V,V,V⟩)) (zr 12 V V V (K 12 ⟨V,V,V,V,V⟩))
 by_cases a12:w∈aZ D b 12
 · have K:=fun (t:O) g c=>orb49_cut h r b0 hb 12 t 2 13 (cl 12 V V) d2 g ⟨w,a12⟩ (sb 12 t c V V V)
   exact q46_Y h r hp m (zr 1 V V V (fun c=>orb49_cut h r b0 hb 1 12 9 6 (cl 1 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 1 12 a12 V V V))) (zr 3 V V V (K 3 ⟨V,V,V,V,V⟩)) (zr 7 V V V (K 7 ⟨V,V,V,V,V⟩)) (zr 11 V V V (K 11 ⟨V,V,V,V,V⟩))
 have s11:=zr 11 V V V a11;have s12:=zr 12 V V V a12
 have h3:3<=(af 14 D 3).card:=by by_contra c;exact fR_dom h r hp 3 11 12 7 4 2 i4 i2 V V (by omega) s11 s12
 have w3:w∈aZ D b 3:=by by_contra c;have:=zr 3 V V V c;omega
 have nl:∀x:O,x∉({0,2,4,9}:o)->x∈al 14 D:=fun x c=>by by_contra q;exact c ((m x).1 (aN.2 q))
 have J:∀c z:O,w∈aZ D b c->(3:O)≠c->c∉dom 3->ac 3 z=true->bK c z=false->∃f,∀e∈af 14 D 3,e≠f->c∈ag 14 D (aw D e):=fun c z k a d g n=>jx_dom h r hb (nl 3 V) (cl 3 V V) a d (sb 3 c k V V V) ⟨w.1,(ay.1 w3).2,(ay.1 k).2⟩ ⟨z,g,n⟩
 obtain⟨Z2,-,W2,c2⟩:=qu_dom h r hp i2 (by decide:aP 2 12) V s12
 obtain⟨Z4,-,W4,c4⟩:=qu_dom h r hp i4 (by decide:aP 4 11) V s11
 obtain⟨e7,h7,k7,-,-⟩:=bf h r hp (by decide:aP 7 3)
 by_cases a8:w∈aZ D b 8 <;> by_cases a10:w∈aZ D b 10
 · obtain⟨f8,g8⟩:=J 8 11 a8 V V V V;obtain⟨f10,g10⟩:=J 10 11 a10 V V V V
   have s5:=zr 5 V V V (fun c=>orb49_cut h r b0 hb 5 10 9 6 (cl 5 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 5 10 a10 V V V))
   obtain⟨Z5,-,W5,c5⟩:=qu_dom h r hp i9 (by decide:aP 9 5) V s5
   obtain⟨e3,h3',k3,g3,-⟩:=bf h r hp (by decide:aP 12 3);obtain⟨e5,h5,k5,g5,l5⟩:=bf h r hp (by decide:aP 12 5)
   have E3:=q46_q W2 h3' (fun e=>absurd (g3 2 i2 e) V);have E5:=q46_q W2 h5 (fun e=>absurd (g5 2 i2 e) V);have F5:=q46_q W5 k5 (fun e=>absurd (l5 9 i9 e) V)
   have Y:Z5∈af 14 D 3:=by rw[<-F5,E5,<-E3];exact k3
   obtain⟨f,hf,n5,n8⟩:=bE_dom h.1 r (by decide:mV 3 5 8=true);obtain⟨f',hf',n8',n10⟩:=bE_dom h.1 r (by decide:mV 3 8 10=true)
   have q1:f=f8:=by by_contra c;exact n8 (g8 f hf c)
   have q2:f'=f8:=by by_contra c;exact n8' (g8 f' hf' c)
   have q3:Z5=f10:=by by_contra c;exact (c5 10 V).1 (g10 _ Y c)
   have q4:f'=f10:=by by_contra c;exact n10 (g10 _ hf' c)
   exact n5 (by rw[q1,<-q2,q4,<-q3];exact (ak.1 (show Z5∈af 14 D 5 by rw[W5];exact _mi.2 (Or.inr (_mss _)))).2.1)
 · obtain⟨f8,g8⟩:=J 8 11 a8 V V V V
   have s6:=zr 6 V V V (fun c=>orb49_cut h r b0 hb 6 8 9 5 (cl 6 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 6 8 a8 V V V))
   have s1:=zr 1 V V V (fun c=>orb49_cut h r b0 hb 1 8 9 5 (cl 1 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 1 8 a8 V V V))
   obtain⟨Z6,-,W6,c6⟩:=qu_dom h r hp i9 (by decide:aP 9 6) V s6
   obtain⟨e3,h3',k3,g3,-⟩:=bf h r hp (by decide:aP 11 3);obtain⟨e6,h6,k6,g6,l6⟩:=bf h r hp (by decide:aP 11 6)
   have E3:=q46_q W4 h3' (fun e=>absurd (g3 4 i4 e) V);have E6:=q46_q W4 h6 (fun e=>absurd (g6 4 i4 e) V);have F6:=q46_q W6 k6 (fun e=>absurd (l6 9 i9 e) V)
   have Y:Z6∈af 14 D 3:=by rw[<-F6,E6,<-E3];exact k3
   have q3:Z6=f8:=by by_contra c;exact (c6 8 V).1 (g8 _ Y c)
   have ne:am e7≠Z6:=fun e=>(c4 7 V).2 (by rw[<-mi (show am e7=am Z4 by rw[e,<-F6,E6])];exact h7)
   have N:=g8 _ k7 (by rw[<-q3];exact ne)
   by_cases a7:w∈aZ D b 7
   · obtain⟨f7,g7⟩:=J 7 11 a7 V V V V
     have r1:am e7=f7:=by by_contra c;exact q46_a h h7 (g7 _ k7 c)
     have r2:Z6=f7:=by by_contra c;exact (c6 7 V).1 (g7 _ Y c)
     exact ne (r1.trans r2.symm)
   · have s7:=zr 7 V V V a7
     obtain⟨Z1,-,W1,c1⟩:=qu_dom h r hp i9 (by decide:aP 9 1) V s1
     obtain⟨a1,ha1,ka1,fa1,-⟩:=bf h r hp (by decide:aP 1 7)
     have E1:=q46_q W1 ha1 (fun e=>absurd (fa1 9 i9 e) V)
     have A7:=gG (aJ hp i0 (by decide:aP 0 7)) h7 (fun e=>absurd ((hp.1 0 i0).2.2.2.2.2.1 (by rw[e];exact N)) V) s7
     rcases A7 _ (show am Z1∈af 14 D 7 by rw[<-E1];exact ka1) with q|q
     · exact (c1 0 V).1 (by rw[<-aB Z1,q];exact cd hp i0)
     · exact (c1 3 V).2 (by rw[<-aB Z1,q];exact k7)
 · obtain⟨f10,g10⟩:=J 10 11 a10 V V V V
   have s5:=zr 5 V V V (fun c=>orb49_cut h r b0 hb 5 10 9 6 (cl 5 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 5 10 a10 V V V))
   have s1:=zr 1 V V V (fun c=>orb49_cut h r b0 hb 1 10 9 6 (cl 1 V V) d9 ⟨V,V,V,V,V⟩ ⟨w,c⟩ (sb 1 10 a10 V V V))
   obtain⟨Z5,-,W5,c5⟩:=qu_dom h r hp i9 (by decide:aP 9 5) V s5
   obtain⟨e3,h3',k3,g3,-⟩:=bf h r hp (by decide:aP 12 3);obtain⟨e5,h5,k5,g5,l5⟩:=bf h r hp (by decide:aP 12 5)
   have E3:=q46_q W2 h3' (fun e=>absurd (g3 2 i2 e) V);have E5:=q46_q W2 h5 (fun e=>absurd (g5 2 i2 e) V);have F5:=q46_q W5 k5 (fun e=>absurd (l5 9 i9 e) V)
   have Y:Z5∈af 14 D 3:=by rw[<-F5,E5,<-E3];exact k3
   have q3:Z5=f10:=by by_contra c;exact (c5 10 V).1 (g10 _ Y c)
   have ne:am e7≠Z5:=fun e=>(c2 7 V).2 (by rw[<-mi (show am e7=am Z2 by rw[e,<-F5,E5])];exact h7)
   have N:=g10 _ k7 (by rw[<-q3];exact ne)
   by_cases a7:w∈aZ D b 7
   · obtain⟨f7,g7⟩:=J 7 11 a7 V V V V
     have r1:am e7=f7:=by by_contra c;exact q46_a h h7 (g7 _ k7 c)
     have r2:Z5=f7:=by by_contra c;exact (c5 7 V).1 (g7 _ Y c)
     exact ne (r1.trans r2.symm)
   · have s7:=zr 7 V V V a7
     obtain⟨Z1,-,W1,c1⟩:=qu_dom h r hp i9 (by decide:aP 9 1) V s1
     obtain⟨a1,ha1,ka1,fa1,-⟩:=bf h r hp (by decide:aP 1 7)
     have E1:=q46_q W1 ha1 (fun e=>absurd (fa1 9 i9 e) V)
     have A7:=gG (aJ hp i0 (by decide:aP 0 7)) h7 (fun e=>absurd ((hp.1 0 i0).2.2.2.2.2.1 (by rw[e];exact N)) V) s7
     rcases A7 _ (show am Z1∈af 14 D 7 by rw[<-E1];exact ka1) with q|q
     · exact (c1 0 V).1 (by rw[<-aB Z1,q];exact cd hp i0)
     · exact (c1 3 V).2 (by rw[<-aB Z1,q];exact k7)
 · have gu:∀x:O,(aZ D b x).Nonempty->w∉aZ D b x->x∈ag 14 D u.1:=fun x ⟨v,hv⟩ c=>by obtain⟨a,k⟩:=ay.1 hv;rw[hR,_mi,_ms] at a;rcases a with rfl|rfl;{exact k};{exact absurd hv c}
   have g8:=gu 8 z8 a8;have g10:=gu 10 z10 a10
   obtain⟨P,Q,pq,hP,hQ,hy⟩:=dV_dom h r hb (cl 13 V V) hZ c13
   obtain⟨f,hf,n8,-⟩:=bE_dom h.1 r (by decide:mV 13 8 12=true)
   rcases aT hP hQ hf pq (fun e=>n8 (by rw[<-e];exact (hy 8 g8).1)) (fun e=>n8 (by rw[<-e];exact (hy 8 g8).2)) l13 _ (aJ hp i2 (by decide:aP 2 13)) with q|q|q
   · exact absurd (t2 10 (by rw[q];exact (hy 10 g10).1)) V
   · exact absurd (t2 10 (by rw[q];exact (hy 10 g10).2)) V
   · exact n8 (by rw[<-q];exact (hp.1 2 i2).2.2.2.1 8 V)
lemma q46_B {D:Dag} (h:ai 14 D) (r:ar D) (b0:bL 14 D=0) {b:O->ℕ} (hb:cU_dom D b) {pos:O->ℕ×_d} (hp:bA_dom D pos) (m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,9}:o)) (hZ:aZ D b 13=aj 14 D b) (hc:(aj 14 D b).card=2):False:=by
 have i0:(0:O)∈aa 14 D:=(m 0).2 V;have i2:(2:O)∈aa 14 D:=(m 2).2 V;have i4:(4:O)∈aa 14 D:=(m 4).2 V;have i9:(9:O)∈aa 14 D:=(m 9).2 V
 have hd:∀ x:O,x∈dom 2\/x∈dom 4\/x∈dom 9->x∈({0,2,4,9}:o):=by decide
 have d2:dom 2⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inl c));have d4:dom 4⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inr (Or.inl c)));have d9:dom 9⊆aa 14 D:=fun x c=>(m x).2 (hd x (Or.inr (Or.inr c)))
 have cl:∀ x:O,x≠8->x≠10->isClean (aa 14 D) x:=fun x a c=>by by_cases g:x=1\/x=3;{exact Or.inr (Or.inl ⟨g,i0⟩)};{left;push Not at g;exact⟨g.1,g.2,a,c⟩}
 have bj:=fun x a c=>bj_clean h r hb (cl x a c)
 have nl:∀x:O,x∉({0,2,4,9}:o)->x∈al 14 D:=fun x c=>by by_contra q;exact c ((m x).1 (aN.2 q))
 have Zs:∀x:O,aZ D b x⊆aZ D b 13:=fun x=>by rw[hZ];exact _fs _ _
 have hZa:∀u∈aj 14 D b,(13:O)∈ag 14 D u.1:=fun u hu=>(ay.1 (by rw[hZ];exact hu:u∈aZ D b 13)).2
 have em:∀x:O,x≠8->x≠10->¬(aZ D b x).Nonempty->(af 14 D x).card<=2:=fun x a c n=>by have:=bj x a c;rw[not_nonempty_iff_eq_empty.1 n,_ce] at this;omega
 have s1:=em 1 V V (fun n=>orb49_cut h r b0 hb 1 13 9 5 (cl 1 V V) d9 ⟨V,V,V,V,V⟩ n (Zs 1))
 have s5:=em 5 V V (fun n=>orb49_cut h r b0 hb 5 13 9 6 (cl 5 V V) d9 ⟨V,V,V,V,V⟩ n (Zs 5))
 have s6:=em 6 V V (fun n=>orb49_cut h r b0 hb 6 13 9 5 (cl 6 V V) d9 ⟨V,V,V,V,V⟩ n (Zs 6))
 have c13:=cx_dom h r hp i2 i4 (u:=13) (v:=1) ⟨V,V,V,V,V,V⟩ (Or.inr V)
 have b13:=bj 13 V V;rw[hZ,hc] at b13
 have mi:∀{e f:ℕ×_d},am e=am f->e=f:=fun {e f} q=>by rw[<-aB e,q,aB]
 obtain⟨Z5,-,W5,c5⟩:=qu_dom h r hp i9 (by decide:aP 9 5) V s5
 obtain⟨Z6,-,W6,c6⟩:=qu_dom h r hp i9 (by decide:aP 9 6) V s6
 obtain⟨Z1,-,W1,c1⟩:=qu_dom h r hp i9 (by decide:aP 9 1) V s1
 have J:∀x z:O,x∉({0,2,4,9}:o)->x≠8->x≠10->x≠13->13∉dom x->ac x z=true->bK 13 z=false->(aZ D b x).Nonempty->∃f,∀e∈af 14 D x,e≠f->(13:O)∈ag 14 D (aw D e):=fun x z a c d g k l n ⟨v,hv⟩=>jx_dom h r hb (nl x a) (cl x c d) g k (Zs x) ⟨v.1,(ay.1 hv).2,hZa v (ay.1 hv).1⟩ ⟨z,l,n⟩
 obtain⟨a1,ha1,ka1,fa1,-⟩:=bf h r hp (by decide:aP 1 7)
 have E1:=q46_q W1 ha1 (fun e=>absurd (fa1 9 i9 e) V)
 obtain⟨e7,h7,k7,-,-⟩:=bf h r hp (by decide:aP 7 3)
 have Y5:(af 14 D 12).card<=2->Z5∈af 14 D 3:=fun s12=>by
  obtain⟨Z2,-,W2,c2⟩:=qu_dom h r hp i2 (by decide:aP 2 12) V s12
  obtain⟨e2,h2,k2,-,g2⟩:=bf h r hp (by decide:aP 3 12);obtain⟨e5,h5,k5,f5,g5⟩:=bf h r hp (by decide:aP 5 12)
  rw[<-q46_q W5 h5 (fun e=>absurd (f5 9 i9 e) V),mi ((q46_q W2 k5 (fun e=>absurd (g5 2 i2 e) V)).trans (q46_q W2 k2 (fun e=>absurd (g2 2 i2 e) V)).symm)];exact h2
 have Y6:(af 14 D 11).card<=2->Z6∈af 14 D 3:=fun s11=>by
  obtain⟨Z4,-,W4,c4⟩:=qu_dom h r hp i4 (by decide:aP 4 11) V s11
  obtain⟨e1,h1,k1,-,g1⟩:=bf h r hp (by decide:aP 3 11);obtain⟨e6,h6,k6,f6,g6⟩:=bf h r hp (by decide:aP 6 11)
  rw[<-q46_q W6 h6 (fun e=>absurd (f6 9 i9 e) V),mi ((q46_q W4 k6 (fun e=>absurd (g6 4 i4 e) V)).trans (q46_q W4 k1 (fun e=>absurd (g1 4 i4 e) V)).symm)];exact h1
 have L:(aZ D b 3).Nonempty->(af 14 D 11).card<=2\/(af 14 D 12).card<=2\/(af 14 D 7).card<=2->False:=fun n c=>by
  obtain⟨f3,g3⟩:=J 3 7 V V V V V V V n
  rcases c with c|c|c
  · obtain⟨f,hf,n6,n13⟩:=bE_dom h.1 r (by decide:mV 3 6 13=true)
    have a:Z6=f3:=by by_contra q;exact (c6 13 V).1 (g3 _ (Y6 c) q)
    have d:f=f3:=by by_contra q;exact n13 (g3 _ hf q)
    exact n6 (by rw[d,<-a];exact (ak.1 (show Z6∈af 14 D 6 by rw[W6];exact _mi.2 (Or.inr (_mss _)))).2.1)
  · obtain⟨f,hf,n5,n13⟩:=bE_dom h.1 r (by decide:mV 3 5 13=true)
    have a:Z5=f3:=by by_contra q;exact (c5 13 V).1 (g3 _ (Y5 c) q)
    have d:f=f3:=by by_contra q;exact n13 (g3 _ hf q)
    exact n5 (by rw[d,<-a];exact (ak.1 (show Z5∈af 14 D 5 by rw[W5];exact _mi.2 (Or.inr (_mss _)))).2.1)
  · have A7:=gG (show am Z1∈af 14 D 7 by rw[<-E1];exact ka1) h7 (fun e=>(c1 3 V).2 (by rw[<-aB Z1,e];exact k7)) c
    rcases A7 _ (aJ hp i0 (by decide:aP 0 7)) with q|q
    · exact (c1 0 V).1 (by rw[<-aB Z1,<-q];exact cd hp i0)
    obtain⟨f,hf,n0,n13⟩:=bE_dom h.1 r (by decide:mV 3 0 13=true)
    have a:am e7=f3:=by by_contra p;exact absurd ((hp.1 0 i0).2.2.2.2.2.1 (show (13:O)∈ag 14 D (aw D (am (pos 0))) by rw[q];exact g3 _ k7 p)) V
    have d:f=f3:=by by_contra p;exact n13 (g3 _ hf p)
    exact n0 (by rw[d,<-a,<-q];exact cd hp i0)
 have p2:=aJ hp i2 (by decide:aP 2 13);have p4:=aJ hp i4 (by decide:aP 4 13)
 obtain⟨a2,ha2,ka2,fa2,-⟩:=bf h r hp (by decide:aP 1 13)
 have z13:am Z1∈af 14 D 13:=by rw[<-q46_q W1 ha2 (fun e=>absurd (fa2 9 i9 e) V)];exact ka2
 have z1:Z1∈af 14 D 1:=by rw[W1];exact _mi.2 (Or.inr (_mss _))
 have a7:(7:O)∈ag 14 D (aw D (am Z1)):=(ak.1 (show am Z1∈af 14 D 7 by rw[<-E1];exact ka1)).2.1
 have n24:pos 2≠pos 4:=fun e=>absurd (hp.2 i2 i4 e) V
 have nZ:∀i:O,i∈aa 14 D->(1:O)∉dom i->pos i≠am Z1:=fun i hi d e=>d ((hp.1 i hi).2.2.2.2.2.1 (by rw[e,aB];exact (ak.1 z1).2.1))
 have N13:(aZ D b 13).Nonempty:=_cp.1 (by rw[hZ,hc];omega)
 have le1:∀t:O,(aZ D b 13⊆aZ D b t->False)->(aZ D b t).card<=1:=fun t k=>by by_contra c;exact k (_eqc (Zs t) (by rw[hZ,hc];omega)).symm.subset
 have F4:¬(af 14 D 13).card<=3->aW 14 D (ao 14 D {13})=∅/\∃E,∀P∈af 14 D 13,P=pos 2\/P=pos 4\/P=am Z1\/P=E:=fun c4=>by
  refine⟨card_eq_zero.1 (by omega),?_⟩
  obtain⟨E0,hE,nE⟩:∃E∈af 14 D 13,E∉({pos 2,pos 4,am Z1}:Finset (ℕ×_d)):=by by_contra q;push Not at q;exact c4 ((_cl (fun e he=>q e he)).trans card_le_three)
  rw[_mi,_mi,_ms,not_or,not_or] at nE
  exact⟨E0,gh p2 p4 z13 hE n24 (nZ 2 i2 V) (Ne.symm nE.1) (nZ 4 i4 V) (Ne.symm nE.2.1) (Ne.symm nE.2.2) (by omega)⟩
 have s3:¬(aZ D b 3).Nonempty->(af 14 D 3).card<=2:=em 3 V V
 have s7:¬(aZ D b 7).Nonempty->(af 14 D 7).card<=2:=em 7 V V
 have hl7:=nl 7 V
 have z8:(aZ D b 8).Nonempty:=nonempty_iff_ne_empty.2 fun z=>no_leak_2nbrs h r b0 hb hp (x:=8) (v3:=6) hl7 V V z i2 i0 V V V V V V (Or.inr V) V (fun k=>by have:=cx_dom h r hp (u:=8) (v:=6) i2 i0 ⟨V,V,V,V,V,V⟩ (Or.inr V);have:=bj_noleak h r hb (x:=8) (fun _ _=>k);rw[z,_ce] at this;omega)
 have z10:(aZ D b 10).Nonempty:=nonempty_iff_ne_empty.2 fun z=>no_leak_2nbrs h r b0 hb hp (x:=10) (v3:=5) hl7 V V z i4 i0 V V V V V V (Or.inr V) V (fun k=>by have:=cx_dom h r hp (u:=10) (v:=5) i4 i0 ⟨V,V,V,V,V,V⟩ (Or.inr V);have:=bj_noleak h r hb (x:=10) (fun _ _=>k);rw[z,_ce] at this;omega)
 have OT:∀u∈aj 14 D b,∃w∈aj 14 D b,∀v∈aj 14 D b,v=u\/v=w:=fun u hu=>by
  obtain⟨w,hw⟩:=card_eq_one.1 (show ((aj 14 D b).erase u).card=1 by rw[card_erase_of_mem hu,hc])
  exact⟨w,(mem_erase.1 (show w∈(aj 14 D b).erase u by rw[hw];exact _mss _)).2,fun v hv=>by by_cases e:v=u;{exact Or.inl e};{right;exact _ms.1 (by rw[<-hw];exact mem_erase.2 ⟨e,hv⟩)}⟩
 have KK:∀(k i:O) (u:Σ _:ℕ,ℕ),i∈aa 14 D->aP i k->aP i 13->isClean (aa 14 D) k->aZ D b k={u}->3<=(af 14 D k).card->(∃z:O,mV k z 13=true)->∀y:O,y∈ag 14 D u.1->y∈ag 14 D (aw D (pos i)):=fun k i u hi a1 a2 ck hu c3 ⟨z,hm⟩ y hy=>by
  obtain⟨P,Q,pq,hP,hQ,H⟩:=dV_dom h r hb ck hu c3
  obtain⟨f,hf,-,n⟩:=bE_dom h.1 r hm
  have u13:=hZa u (ay.1 (show u∈aZ D b k by rw[hu];exact _mss _)).1
  have l:=bj_clean h r hb ck;rw[hu,_cs] at l
  rcases aT hP hQ hf pq (fun e=>n (by rw[<-e];exact (H 13 u13).1)) (fun e=>n (by rw[<-e];exact (H 13 u13).2)) (by omega) _ (aJ hp hi a1) with q|q|q
  · rw[q];exact (H y hy).1
  · rw[q];exact (H y hy).2
  · exact absurd ((hp.1 i hi).2.2.2.1 13 a2) (by rw[q];exact n)
 have N0:(af 14 D 13).card<=3->pos 0∉af 14 D 13:=fun c4 k=>by
  rcases aT p2 p4 z13 n24 (nZ 2 i2 V) (nZ 4 i4 V) c4 _ k with q|q|q
  · exact absurd (hp.2 i0 i2 q) V
  · exact absurd (hp.2 i0 i4 q) V
  · exact (c1 0 V).1 (by rw[<-aB Z1,<-q];exact cd hp i0)
 have ZW:∀(i:O) (u w:Σ _:ℕ,ℕ),(∀v∈aj 14 D b,v=u\/v=w)->(∀y:O,y∈ag 14 D u.1->dj i y)->∀x:O,¬dj i x->(aZ D b x).Nonempty->aZ D b x={w}:=fun i u w ow K x nx ⟨v,hv⟩=>by
  have q:∀v∈aZ D b x,v=w:=fun v hv=>(ow v (ay.1 hv).1).resolve_left (fun e=>nx (K x (by rw[<-e];exact (ay.1 hv).2)))
  exact eq_singleton_iff_unique_mem.2 ⟨by rw[<-q v hv];exact hv,q⟩
 have l11:=le1 11 (orb49_cut h r b0 hb 13 11 2 12 (cl 13 V V) d2 ⟨V,V,V,V,V⟩ N13)
 have l12:=le1 12 (orb49_cut h r b0 hb 13 12 4 11 (cl 13 V V) d4 ⟨V,V,V,V,V⟩ N13)
 by_cases e11:(aZ D b 11).Nonempty <;> by_cases e12:(aZ D b 12).Nonempty
 · have C1:=orb49_cut h r b0 hb 11 12 4 10 (cl 11 V V) d4 ⟨V,V,V,V,V⟩ e11
   have C2:=orb49_cut h r b0 hb 12 11 2 8 (cl 12 V V) d2 ⟨V,V,V,V,V⟩ e12
   by_cases c4:(af 14 D 13).card<=3
   · have A13:=aT p2 p4 z13 n24 (nZ 2 i2 V) (nZ 4 i4 V) c4
     obtain⟨u,hu⟩:=card_eq_one.1 (le_antisymm l11 (_cp.2 e11));obtain⟨w,hw⟩:=card_eq_one.1 (le_antisymm l12 (_cp.2 e12))
     have uj:=(ay.1 (show u∈aZ D b 11 by rw[hu];exact _mss _)).1;have wj:=(ay.1 (show w∈aZ D b 12 by rw[hw];exact _mss _)).1
     obtain⟨w',-,ow⟩:=OT u uj
     have ww:w=w':=(ow w wj).resolve_left (fun e=>C1 (by rw[hu,hw,e]))
     have Sg:∀x:O,(aZ D b 11⊆aZ D b x->False)->(aZ D b 12⊆aZ D b x->False)->¬(aZ D b x).Nonempty:=fun x p q ⟨v,hv⟩=>by
      rcases ow v (ay.1 hv).1 with e|e
      · exact p (by rw[hu,singleton_subset_iff,<-e];exact hv)
      · exact q (by rw[hw,singleton_subset_iff,ww,<-e];exact hv)
     have s3':=em 3 V V (Sg 3 (orb49_cut h r b0 hb 11 3 4 13 (cl 11 V V) d4 ⟨V,V,V,V,V⟩ e11) (orb49_cut h r b0 hb 12 3 2 13 (cl 12 V V) d2 ⟨V,V,V,V,V⟩ e12))
     have s7':=em 7 V V (Sg 7 (orb49_cut h r b0 hb 11 7 4 13 (cl 11 V V) d4 ⟨V,V,V,V,V⟩ e11) (orb49_cut h r b0 hb 12 7 2 13 (cl 12 V V) d2 ⟨V,V,V,V,V⟩ e12))
     have A7:=gG (aJ hp i0 (by decide:aP 0 7)) (show am Z1∈af 14 D 7 by rw[<-E1];exact ka1) (fun e=>(c1 0 V).1 (by rw[<-aB Z1,<-e];exact cd hp i0)) s7'
     have k0:am (pos 0)∈af 14 D 3:=by
      rcases A7 _ h7 with q|q
      · rw[<-q];exact k7
      · exact absurd (show Z1∈af 14 D 3 by rw[<-aB Z1,<-q];exact k7) (c1 3 V).2
     obtain⟨f,hf,n0,n13⟩:=bE_dom h.1 r (by decide:mV 3 0 13=true)
     have A3:=gG k0 hf (fun e=>n0 (by rw[<-e];exact cd hp i0)) s3'
     have X:∀(k:O) (g:ℕ×_d),aP 3 k->(∀e∈af 14 D k,e≠g->(13:O)∈ag 14 D (aw D e))->pos 0≠g->am f=g:=fun k g a H ng=>by
      obtain⟨e1,he,ke,-,ge⟩:=bf h r hp a
      rcases A3 _ he with q|q
      · rw[q,aB] at ke;exact absurd (cV_dom hp i0 (H _ ke ng) V) (N0 c4)
      rw[q] at ke ge;by_contra c
      rcases q46_G h ke (H _ ke c) with t|t
      · rcases A13 _ t with t|t|t
        · exact absurd (ge 2 i2 t) V
        · exact absurd (ge 4 i4 t) V
        · exact (c1 3 V).2 (by rw[<-mi t];exact hf)
      · exact n13 (q46_w (e:=f) t)
     obtain⟨f1,H1⟩:=J 11 3 V V V V V V V e11;obtain⟨f2,H2⟩:=J 12 3 V V V V V V V e12
     obtain⟨g1,hg1,m10,m13⟩:=bE_dom h.1 r (by decide:mV 11 10 13=true)
     obtain⟨g2,hg2,m8,m13'⟩:=bE_dom h.1 r (by decide:mV 12 8 13=true)
     obtain⟨g3,hg3,m11,m13''⟩:=bE_dom h.1 r (by decide:mV 12 11 13=true)
     have q1:g1=f1:=by by_contra c;exact m13 (H1 _ hg1 c)
     have q2:g2=f2:=by by_contra c;exact m13' (H2 _ hg2 c)
     have q3:g3=f2:=by by_contra c;exact m13'' (H2 _ hg3 c)
     have x1:=X 11 f1 V H1 (fun e=>m10 (by rw[q1,<-e];exact (hp.1 0 i0).2.2.2.1 10 V))
     have x2:=X 12 f2 V H2 (fun e=>m8 (by rw[q2,<-e];exact (hp.1 0 i0).2.2.2.1 8 V))
     exact m11 (by rw[q3,<-x2,x1,<-q1];exact (ak.1 hg1).2.1)
   obtain⟨hM,-⟩:=F4 c4
   have k13:(af 14 D 13).card=4:=by omega
   obtain⟨f,hf,n1,n2⟩:=bE_dom h.1 r (by decide:mV 13 11 12=true)
   have c3:((af 14 D 13).erase f).card=3:=by rw[card_erase_of_mem hf,k13]
   obtain⟨p,q,s,-,-,-,hT⟩:=card_eq_three.1 c3
   rw[hT] at c3
   have G4:∀P∈af 14 D 13,P=f\/P=p\/P=q\/P=s:=fun P hP=>by by_cases e:P=f;{exact Or.inl e};{right;have:=mem_erase.2 ⟨e,hP⟩;rw[hT,_mi,_mi,_ms] at this;exact this}
   have sT:({p,q,s}:Finset (ℕ×_d))⊆af 14 D 13:=by rw[<-hT];exact erase_subset _ _
   have CN:∀k z:O,mV k z 13=true->(af 14 D k).card+(aW 14 D (ao 14 D {k})).card<=3->k∉ag 14 D (aw D p)\/k∉ag 14 D (aw D q)\/k∉ag 14 D (aw D s):=fun k z hm c=>by
    by_contra o;push Not at o;obtain⟨a1,a2,a3⟩:=o
    obtain⟨g,hg,-,n⟩:=bE_dom h.1 r hm
    have:=q46_c h (x:=k) (y:=13) (T:={p,q,s}) (G:={g}) sT (by intro e he;rw[_mi,_mi,_ms] at he;rcases he with rfl|rfl|rfl;{exact a1};{exact a2};{exact a3}) (singleton_subset_iff.2 hg) (fun e he k'=>by rw[_ms.1 he] at k';exact n (ak.1 (sT k')).2.1)
    rw[c3,_cs] at this;omega
   obtain⟨E,A,B,g1,g2⟩:=q46_k (Y:=fun P=>(11:O)∈ag 14 D (aw D P)) (Z:=fun P=>(12:O)∈ag 14 D (aw D P)) G4 n1 n2 (CN 11 10 V (by have:=bj 11 V V;omega)) (CN 12 8 V (by have:=bj 12 V V;omega))
   rcases q46_T h r hM hZa g1 g2 with o|o
   · exact C1 o
   · exact C2 o
 · have s12:=em 12 V V e12
   by_cases n3:(aZ D b 3).Nonempty;{exact L n3 (Or.inr (Or.inl s12))}
   by_cases n7:(aZ D b 7).Nonempty;swap;{exact q46_X h r hp m s1 (s3 n3) (s7 n7) s12}
   have t2:=lQ_dom h r b0 hp i2 d2 (by decide:aP 2 12) (by decide:aP 12 5) V s12
   have K:=orb49_cut h r b0 hb 11 7 4 13 (cl 11 V V) d4 ⟨V,V,V,V,V⟩ e11
   by_cases c4:(af 14 D 13).card<=3
   · obtain⟨u,hu⟩:=card_eq_one.1 (le_antisymm l11 (_cp.2 e11))
     have t4:=dy_dom h r b0 hp (i1:=4) (i2:=2) (v3:=1) i4 i2 d4 ⟨V,V,V,V,V,V⟩ (Or.inr V) V V c4
     have K4:=KK 11 4 u i4 V V (cl 11 V V) hu (by by_contra c;exact fR_dom h r hp 3 11 12 7 4 2 i4 i2 V V (s3 n3) (by omega) s12) ⟨10,V⟩
     obtain⟨w,hw,ow⟩:=OT u (ay.1 (show u∈aZ D b 11 by rw[hu];exact _mss _)).1
     have Zw:=ZW 4 u w ow (fun y hy=>t4 y (K4 y hy))
     have w8:w∈aZ D b 8:=by rw[Zw 8 V z8];exact _mss _
     exact q46_S h r hb hp (x:=8) (i:=2) i0 i2 ⟨V,V,V,V,V⟩ (Zw 7 V n7) (ay.1 w8).2 (hZa w hw) (by by_contra c;exact q46_X h r hp m s1 (s3 n3) (by omega) s12) (N0 c4) (fun k=>absurd (t2 7 k) V) (by have:=bj_any h r hb 8;rw[Zw 8 V z8,_cs] at this;omega)
   obtain⟨hM,E0,G4⟩:=F4 c4
   obtain⟨h1,hh1,y1,y2⟩:=bE_dom h.1 r (by decide:mV 13 7 12=true);obtain⟨h2,hh2,z1',z2'⟩:=bE_dom h.1 r (by decide:mV 13 11 12=true)
   obtain⟨E,A,B,g1,g2⟩:=q46_k (Y:=fun P=>(7:O)∈ag 14 D (aw D P)) (Z:=fun P=>(11:O)∈ag 14 D (aw D P)) G4 (fun k=>absurd (t2 7 k) V) (fun k=>absurd (t2 11 k) V)
    (by rcases G4 h1 hh1 with q|q|q|q <;> rw[q] at y1 y2;{exact absurd ((hp.1 2 i2).2.2.2.1 12 V) y2};{exact Or.inl y1};{exact absurd a7 y1};{exact Or.inr (Or.inr y1)})
    (by rcases G4 h2 hh2 with q|q|q|q <;> rw[q] at z1' z2';{exact absurd ((hp.1 2 i2).2.2.2.1 12 V) z2'};{exact absurd ((hp.1 4 i4).2.2.2.1 11 V) z1'};{exact Or.inr (Or.inl z1')};{exact Or.inr (Or.inr z1')})
   rcases q46_T h r hM hZa g1 g2 with q|q
   · exact K (_eqc q (by have:=le1 11 (orb49_cut h r b0 hb 13 11 2 12 (cl 13 V V) d2 ⟨V,V,V,V,V⟩ N13);have:=_cp.2 n7;omega)).symm.subset
   · exact K q
 · have s11:=em 11 V V e11
   by_cases n3:(aZ D b 3).Nonempty;{exact L n3 (Or.inl s11)}
   by_cases n7:(aZ D b 7).Nonempty;swap;{exact q46_Y h r hp m s1 (s3 n3) (s7 n7) s11}
   have t4:=lQ_dom h r b0 hp i4 d4 (by decide:aP 4 11) (by decide:aP 11 6) V s11
   have K:=orb49_cut h r b0 hb 12 7 2 13 (cl 12 V V) d2 ⟨V,V,V,V,V⟩ e12
   by_cases c4:(af 14 D 13).card<=3
   · obtain⟨u,hu⟩:=card_eq_one.1 (le_antisymm l12 (_cp.2 e12))
     have t2:=dy_dom h r b0 hp (i1:=2) (i2:=4) (v3:=1) i2 i4 d2 ⟨V,V,V,V,V,V⟩ (Or.inr V) V V c4
     have K2:=KK 12 2 u i2 V V (cl 12 V V) hu (by by_contra c;exact fR_dom h r hp 3 11 12 7 4 2 i4 i2 V V (s3 n3) s11 (by omega)) ⟨8,V⟩
     obtain⟨w,hw,ow⟩:=OT u (ay.1 (show u∈aZ D b 12 by rw[hu];exact _mss _)).1
     have Zw:=ZW 2 u w ow (fun y hy=>t2 y (K2 y hy))
     have w10:w∈aZ D b 10:=by rw[Zw 10 V z10];exact _mss _
     exact q46_S h r hb hp (x:=10) (i:=4) i0 i4 ⟨V,V,V,V,V⟩ (Zw 7 V n7) (ay.1 w10).2 (hZa w hw) (by by_contra c;exact q46_Y h r hp m s1 (s3 n3) (by omega) s11) (N0 c4) (fun k=>absurd (t4 7 k) V) (by have:=bj_any h r hb 10;rw[Zw 10 V z10,_cs] at this;omega)
   obtain⟨hM,E0,G4⟩:=F4 c4
   have G4':∀P∈af 14 D 13,P=pos 4\/P=pos 2\/P=am Z1\/P=E0:=fun P hP=>by rcases G4 P hP with q|q|q|q;{exact Or.inr (Or.inl q)};{exact Or.inl q};{exact Or.inr (Or.inr (Or.inl q))};{exact Or.inr (Or.inr (Or.inr q))}
   obtain⟨h1,hh1,y1,y2⟩:=bE_dom h.1 r (by decide:mV 13 7 11=true);obtain⟨h2,hh2,z1',z2'⟩:=bE_dom h.1 r (by decide:mV 13 11 12=true)
   obtain⟨E,A,B,g1,g2⟩:=q46_k (Y:=fun P=>(7:O)∈ag 14 D (aw D P)) (Z:=fun P=>(12:O)∈ag 14 D (aw D P)) G4' (fun k=>absurd (t4 7 k) V) (fun k=>absurd (t4 12 k) V)
    (by rcases G4 h1 hh1 with q|q|q|q <;> rw[q] at y1 y2;{exact Or.inl y1};{exact absurd ((hp.1 4 i4).2.2.2.1 11 V) y2};{exact absurd a7 y1};{exact Or.inr (Or.inr y1)})
    (by rcases G4 h2 hh2 with q|q|q|q <;> rw[q] at z1' z2';{exact absurd ((hp.1 2 i2).2.2.2.1 12 V) z2'};{exact absurd ((hp.1 4 i4).2.2.2.1 11 V) z1'};{exact Or.inr (Or.inl z2')};{exact Or.inr (Or.inr z2')})
   rcases q46_T h r hM hZa g1 g2 with q|q
   · exact K (_eqc q (by have:=le1 12 (orb49_cut h r b0 hb 13 12 4 11 (cl 13 V V) d4 ⟨V,V,V,V,V⟩ N13);have:=_cp.2 n7;omega)).symm.subset
   · exact K q
 · have s11:=em 11 V V e11;have s12:=em 12 V V e12
   exact L (_cp.1 (Nat.pos_of_ne_zero fun c=>fR_dom h r hp 3 11 12 7 4 2 i4 i2 V V (by have:=bj 3 V V;omega) s11 s12)) (Or.inl s11)
lemma orb_46 {D:Dag} (h:ai 14 D) (r:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨46,V⟩):False:=by
 have hT:=aV 14 D;rw[hI,(by decide:(bU ⟨46,V⟩).card=4)] at hT
 by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 _ hI}
 by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 _ (by decide) hI}
 have hts:=bg 14 D;obtain⟨b,hb⟩:=b_dom h.1 r;obtain⟨pos,hp⟩:=bQ_dom h r;have hR:=bS_dom h.1 hb
 have b0:bL 14 D=0:=by omega
 have a2:(aj 14 D b).card=2:=by omega
 obtain⟨u1,u2,hu,hR2⟩:=_ct2.1 a2
 have m:∀ x:O,x∈aa 14 D↔x∈({0,2,4,9}:o):=fun x=>by rw[hI];rfl
 have c:=cx_dom h r hp ((m 2).2 V) ((m 4).2 V) (u:=13) (v:=1) ⟨V,V,V,V,V,V⟩ (Or.inr V)
 have k:=bj_clean h r hb (x:=13) (Or.inl ⟨V,V,V,V⟩)
 have s:∀ v,v∈aZ D b 13->v=u1\/v=u2:=fun v e=>by have:=(ay.1 e).1;rw[hR2,_mi,_ms] at this;exact this
 by_cases a:u1∈aZ D b 13 <;> by_cases d:u2∈aZ D b 13
 · exact q46_B h r b0 hb hp m (_eqc (_fs _ _) (by rw[a2,<-_c2 hu];exact _cl (fun v e=>by rcases _mi.1 e with rfl|e;{exact a};{rw[_ms.1 e];exact d}))) a2
 · exact q46_A h r b0 hb hp m hR2 (ext fun v=>⟨fun e=>by rcases s v e with g|g;{rw[g];exact _mss _};{rw[g] at e;exact absurd e d},fun e=>by rw[_ms.1 e];exact a⟩)
 · exact q46_A h r b0 hb hp m (u:=u2) (w:=u1) (by rw[hR2,pair_comm]) (ext fun v=>⟨fun e=>by rcases s v e with g|g;{rw[g] at e;exact absurd e a};{rw[g];exact _mss _},fun e=>by rw[_ms.1 e];exact d⟩)
 · have:aZ D b 13=∅:=eq_empty_iff_forall_notMem.2 fun v e=>by rcases s v e with rfl|rfl;{exact a e};{exact d e}
   rw[this,_ce] at k;omega
lemma m4_cover (k:Fin 68) (h4:4<=(bU k).card) (hn:k∉qtOrbits):k.val=31\/k.val=35\/k.val=38\/k.val=39\/k.val=40\/k.val=41\/k.val=44\/k.val=45\/k.val=46\/k.val=48\/k.val=49\/k.val=50\/k.val=51\/k.val=53\/k.val=56\/k.val=58\/k.val=61\/k.val=62\/k.val=66:=by revert k h4 hn;decide +kernel
lemma g14_upper_umbrella_lb_26 (C:Circuit) (d:Monotone2 C) (j:∀ x:O->_d,_B.bw x->C.eval (_of x)=true) (l:∀ x:O->_d,C.eval (_of x)=true->bx x) (f:C.size<=25):False:=by
 obtain⟨D,h,r,-,h12,-,hm⟩:=mU C d j l f
 obtain⟨k,hk⟩:=fP hm;have hI:aa 14 D=bU k:=hk.symm
 by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h12 h0 k hI}
 by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h12 h1 k (by have:=aV 14 D;have:=bg 14 D;rw[hI] at *;omega) hI}
 by_cases hq:k∈qtOrbits;{exact qt_kill h r h12 (by omega) k hq hI}
 have h4:4<=(bU k).card:=by have:=aV 14 D;have:=bg 14 D;rw[hI] at *;omega
 rcases m4_cover k h4 hq with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
 · exact orb_31 h r h12 (by rwa[show k=⟨31,V⟩ from Fin.ext e] at hI)
 · exact orb_35 h r h12 (by rwa[show k=⟨35,V⟩ from Fin.ext e] at hI)
 · exact orb_38 h r h12 (by rwa[show k=⟨38,V⟩ from Fin.ext e] at hI)
 · exact orb_39 h r h12 (by rwa[show k=⟨39,V⟩ from Fin.ext e] at hI)
 · exact orb_40 h r h12 (by rwa[show k=⟨40,V⟩ from Fin.ext e] at hI)
 · exact orb_41 h r h12 (by rwa[show k=⟨41,V⟩ from Fin.ext e] at hI)
 · exact orb_44 h r h12 (by rwa[show k=⟨44,V⟩ from Fin.ext e] at hI)
 · exact orb_45 h r h12 (by rwa[show k=⟨45,V⟩ from Fin.ext e] at hI)
 · exact orb_46 h r h12 (by rwa[show k=⟨46,V⟩ from Fin.ext e] at hI)
 · exact orb_48 h r h12 (by rwa[show k=⟨48,V⟩ from Fin.ext e] at hI)
 · exact orb_49 h r h12 (by rwa[show k=⟨49,V⟩ from Fin.ext e] at hI)
 · exact orb_50 h r h12 (by rwa[show k=⟨50,V⟩ from Fin.ext e] at hI)
 · exact orb_51 h r h12 (by rwa[show k=⟨51,V⟩ from Fin.ext e] at hI)
 · exact orb_53 h r h12 (by rwa[show k=⟨53,V⟩ from Fin.ext e] at hI)
 · exact orb_56 h r h12 (by rwa[show k=⟨56,V⟩ from Fin.ext e] at hI)
 · exact orb_58 h r h12 (by rwa[show k=⟨58,V⟩ from Fin.ext e] at hI)
 · exact orb_61 h r h12 (by rwa[show k=⟨61,V⟩ from Fin.ext e] at hI)
 · exact orb_62 h r h12 (by rwa[show k=⟨62,V⟩ from Fin.ext e] at hI)
 · exact orb_66 h r h12 (by rwa[show k=⟨66,V⟩ from Fin.ext e] at hI)
end _U
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
lemma ah {α:Type} (l:_F α) (v d:α) (w:ℕ):(l ++ [v]).getD w d=if w<l.length then l.getD w d else if w=l.length then v else d:=by
 split_ifs with a b;{simp[List.getD_eq_getElem?_getD,List.getElem?_append_left a]};{subst b;simp[List.getD_eq_getElem?_getD]};exact List.getD_eq_default _ _ (by simp;omega)
lemma an (a:_F _d) (g:Gate) (w:ℕ):(_B.cE a g).getD w false=if w<a.length then a.getD w false else if w=a.length then g.op.eval (g.inputs.map fun i=>a.getD i false) else false:=ah a _ false w
lemma ir (a:_F Gate) (b:_F _d):(a.foldl _B.cE b).length=b.length+a.length:=by
 induction a generalizing b with | nil=>simp | cons _ _ ih=>simp[ih,_B.cE];omega
lemma ofg (x:O->_d) {i:ℕ} (h:i<14):(_of x).getD i false=x ⟨i,h⟩:=by rw[_lge _ _ (by simp[h]),List.getElem_ofFn]
def c_ (σ:O->O) (i:ℕ):ℕ:=if h:i<14 then (σ ⟨i,h⟩).val else i
def bG (σ:O->O) (C:Circuit):Circuit:=⟨C.gates.map fun g=>⟨g.op,g.inputs.map (c_ σ)⟩,c_ σ C.output⟩
lemma o6 (σ:O->O) (c:_F Gate):∀ w w':_F _d,w.length=w'.length->14<=w.length->(∀ i,w'.getD (c_ σ i) false=w.getD i false)->∀ i,((c.map fun g=>(⟨g.op,g.inputs.map (c_ σ)⟩:Gate)).foldl _B.cE w').getD (c_ σ i) false=(c.foldl _B.cE w).getD i false:=by
 induction c with | nil=>intro _ _ _ _ h;exact h | cons g c ih=>
  intro w w' k l h;refine ih _ _ (by simp[_B.cE,k]) (by simp[_B.cE];omega) fun j=>?_
  have m:(g.inputs.map (c_ σ)).map (fun i=>w'.getD i false)=g.inputs.map fun i=>w.getD i false:=by rw[List.map_map];exact List.map_congr_left fun a _=>h a
  rw[an,an,m,k];have hj:=h j;by_cases d:j<14
  · have:c_ σ j<14:=by simp[c_,d]
    simp only[show c_ σ j<w'.length by omega,show j<w'.length by omega,ite_true];exact hj
  · rw[show c_ σ j=j by simp[c_,d]] at hj⊢;split_ifs <;> first | exact hj | rfl
lemma gj (σ:O->O) (C:Circuit) (y:O->_d):(bG σ C).eval (_of y)=C.eval (_of fun i=>y (σ i)):=by
 refine o6 σ C.gates (_of fun i=>y (σ i)) (_of y) (by simp) (by simp) (fun i=>?_) C.output
 by_cases a:i<14;{have h1:c_ σ i<14:=(by simp[c_,a]);rw[ofg _ h1,ofg _ a];exact congrArg y (_fe (by simp[c_,a]))}
 rw[show c_ σ i=i by simp[c_,a],List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
abbrev Inc (a b:Fin 7):=a=b\/a=b+1\/a=b+3
def _cM (p l:Fin 7):Fin 7:=if p=l then 1 else if p=l+3 then 2 else 4
def s_ (p l:Fin 7) (i:O):O:=_B.kW (if h:i.val<7 then Fin.castAdd 7 (_cM p l*(⟨i.val,h⟩-p)) else Fin.natAdd 7 (_cM p l*(⟨i.val-7,by omega⟩-l)))
lemma q0:∀ p l:Fin 7,s_ p l (Fin.castAdd 7 p)=0/\s_ p l (Fin.natAdd 7 l)=7:=by decide +kernel
lemma q1:∀ p l a b:Fin 7,Inc p l->Inc a b->_B.aO (s_ p l (Fin.castAdd 7 a)) (s_ p l (Fin.natAdd 7 b)):=by decide +kernel
lemma q2:∀ p l a b:Fin 7,Inc p l->Inc a b->let m:=_cM p l;Inc (m*m*a+p) (m*m*b+l)/\s_ p l (Fin.castAdd 7 (m*m*a+p))=_B.kW (Fin.castAdd 7 a)/\s_ p l (Fin.natAdd 7 (m*m*b+l))=_B.kW (Fin.natAdd 7 b):=by decide +kernel
abbrev ErSt:=_F Gate×_F (Option ℕ)
abbrev AO (g:Gate):=g.op=GateOp.and\/g.op=GateOp.or
abbrev M2 (gs:_F Gate):=∀ g∈gs,AO g/\g.inputs.length<=2
abbrev Wb (d:ErSt):=∀ w w',d.2.getD w none=some w'->w'<14+d.1.length
abbrev Rk (d:_F Gate):=∀ k<d.length,let g:=d.getD k ⟨GateOp.or,[]⟩;AO g/\g.inputs.length=2/\∀ u∈g.inputs,u<15+k
lemma fU (n:_F Gate) (p:∀ g∈n,AO g) (j l:_F _d) (c:j.length=l.length) (h:∀ k,j.getD k false=true->l.getD k false=true):∀ k,(n.foldl _B.cE j).getD k false=true->(n.foldl _B.cE l).getD k false=true:=by
 induction n generalizing j l with | nil=>exact h | cons g r ih=>
  refine ih (fun g' h'=>p g' (List.mem_cons_of_mem _ h')) _ _ (by simp[_B.cE,c]) fun k b=>?_
  rw[an] at b⊢;rw[c] at b;split_ifs at b⊢;{exact h k b}
  rcases p g List.mem_cons_self with d|d <;> rw[d] at b⊢ <;> simp[GateOp.eval] at b⊢
  · exact fun a u=>h a (b a u)
  · rcases b with ⟨a,u,v⟩;exact⟨a,u,h a v⟩
def bO (c:ErSt) (g:Gate):ErSt:=
 match c.2.getD (g.inputs.getD 0 0) none,c.2.getD (g.inputs.getD 1 0) none,g.op with
 | some a',some b',op=>⟨c.1 ++ [⟨op,[a',b']⟩],c.2 ++ [some (14+c.1.length)]⟩
 | some a',none,GateOp.and=>⟨c.1,c.2 ++ [some a']⟩
 | none,some b',GateOp.and=>⟨c.1,c.2 ++ [some b']⟩
 | _,_,_=>⟨c.1,c.2 ++ [none]⟩
def mr:ErSt:=⟨[],(List.range 14).map some ++ [none]⟩
def ev (s:_F _d):Option ℕ->_d | none=>true | some i=>s.getD i false
lemma mr_lt {w:ℕ} (h:w<14):mr.2.getD w none=some w:=by revert w h;decide
lemma mr_ge {w:ℕ} (h:14<=w):mr.2.getD w none=none:=by rcases eq_or_lt_of_le h with rfl|c;exact V;exact List.getD_eq_default _ _ (by simp[mr];omega)
lemma bO_ok (d:ErSt) (g:Gate) (hM:M2 d.1) (hw:Wb d) (hOp:AO g):
 let d':=bO d g
 d'.2.length=d.2.length+1 /\ d'.1.length<=d.1.length+1 /\
 ((d.2.getD (g.inputs.getD 0 0) none=none\/d.2.getD (g.inputs.getD 1 0) none=none)->d'.1.length=d.1.length) /\
 M2 d'.1 /\ Wb d' /\ ∀ w<d.2.length,d'.2.getD w none=d.2.getD w none:=by
 cases ha:d.2.getD (g.inputs.getD 0 0) none <;> cases hb:d.2.getD (g.inputs.getD 1 0) none <;> rcases hOp with hOp|hOp <;>
  simp only[bO,Wb,M2,AO,ha,hb,hOp,List.length_append,List.length_singleton] <;>
  refine⟨trivial,by omega,by simp,fun g' hg'=>by first | exact hM g' hg' | (simp at hg';rcases hg' with hg'|rfl;{exact hM g' hg'};simp),
   fun w w' h=>by rw[ah] at h;split_ifs at h <;> first | (have:=hw w w' h;omega) | (cases h;first | omega | (have:=hw _ _ ha;omega) | (have:=hw _ _ hb;omega)),
   fun w hw'=>by rw[ah];simp only[hw',ite_true]⟩
lemma bO_ev (d:ErSt) (g:Gate) (A:_F _d) (hA:A.length=14) (hw:Wb d) (hOp:AO g):
 let d':=bO d g;let s:=d.1.foldl _B.cE A;let s':=d'.1.foldl _B.cE A
 (∀ w<d.2.length,ev s' (d'.2.getD w none)=ev s (d.2.getD w none)) /\
 ev s' (d'.2.getD d.2.length none)=g.op.eval [ev s (d.2.getD (g.inputs.getD 0 0) none),ev s (d.2.getD (g.inputs.getD 1 0) none)]:=by
 have hs:(d.1.foldl _B.cE A).length=14+d.1.length:=by rw[ir,hA]
 cases ha:d.2.getD (g.inputs.getD 0 0) none <;> cases hb:d.2.getD (g.inputs.getD 1 0) none
 case some.some a' b'=>
  simp only[bO,ha,hb,List.foldl_append,List.foldl_cons,List.foldl_nil]
  refine⟨fun w hw'=>?_,by rw[ah];simp only[_nr,ite_false,ite_true,ev];rw[an,hs];simp only[_nr,ite_false,ite_true,List.map_cons,List.map_nil]⟩
  rw[ah];simp only[hw',ite_true];cases hc:d.2.getD w none with | none=>rfl | some w'=>have:=hw w w' hc;simp only[ev];rw[an,hs];simp only[this,ite_true]
 all_goals
  rcases hOp with hOp|hOp <;> simp only[bO,ha,hb,hOp] <;>
   exact⟨fun w hw'=>by rw[ah];simp only[hw',ite_true],by rw[ah];simp only[_nr,ite_false,ite_true];simp[ev,GateOp.eval]⟩
lemma lS (H:Gate) (d:_F Gate):Rk d->
 let e:=d.foldl bO mr
 e.2.length=15+d.length /\ e.1.length<=d.length /\ ((∃ g∈d,14∈g.inputs)->e.1.length+1<=d.length) /\
 M2 e.1 /\ Wb e /\ e.2.getD 14 none=none /\
 ∀ x:O->_d,let y:=_of x;let h:=(H :: d).foldl _B.cE y;let s:=e.1.foldl _B.cE y
  (∀ w,h.getD w false=true->ev s (e.2.getD w none)=true) /\
  ∀ P:ℕ->Prop,(∀ w<15,P w->ev y (mr.2.getD w none)=(_B.cE y H).getD w false)->
   (∀ g∈d,∀ u∈g.inputs,P u)->∀ w<e.2.length,P w->ev s (e.2.getD w none)=h.getD w false:=by
 induction d using List.reverseRecOn with
 | nil=>
  intro _;simp only[List.foldl_nil,List.length_nil]
  refine⟨V,Nat.le_refl _,by simp,by simp[M2,mr],fun w w' h=>?_,mr_ge (le_refl 14),fun x=>⟨fun w hw=>?_,fun _ hP0 _=>hP0⟩⟩
  · by_cases c:w<14;{rw[mr_lt c] at h;cases h;exact c};rw[mr_ge (by omega)] at h;cases h
  · by_cases c:w<14;{rw[mr_lt c];simp only[ev];rw[List.foldl_cons,List.foldl_nil,an] at hw;simp only[List.length_ofFn,c,ite_true] at hw;exact hw};rw[mr_ge (by omega)];rfl
 | append_singleton d g ih=>
  intro A
  have Ad:Rk d:=fun k hk=>by have:=A k (by simp;omega);rw[ah] at this;simp only[hk,ite_true] at this;exact this
  have hg:=A d.length (by simp);rw[ah] at hg;simp only[_nr,ite_false,ite_true] at hg
  obtain⟨hOp,hL2,hIn⟩:=hg
  let a:=g.inputs.getD 0 0;let b:=g.inputs.getD 1 0
  have hgi:g.inputs=[a,b]:=by rcases h:g.inputs with _|⟨u,_|⟨v,_|_⟩⟩ <;> simp_all[a,b]
  obtain⟨rl,gl,g14,gs,wl,e14,hv⟩:=ih Ad
  set e:=d.foldl bO mr
  obtain⟨o2,o1,od,om,ow,olt⟩:=bO_ok e g gs wl hOp
  dsimp only;rw[show (d ++ [g]).foldl bO mr=bO e g from List.foldl_append,List.length_append,List.length_singleton]
  refine⟨by omega,by omega,fun hex=>?_,om,ow,by rw[olt 14 (by omega)];exact e14,fun x=>?_⟩
  · rcases hex with ⟨g',hg',h14'⟩;simp at hg';rcases hg' with hg'|rfl;{have:=g14 ⟨g',hg',h14'⟩;omega}
    rw[hgi] at h14';simp only[List.mem_cons,List.not_mem_nil,or_false] at h14'
    have:=od (by rcases h14' with h|h;{left;change e.2.getD a none=none;rw[<-h];exact e14};right;change e.2.getD b none=none;rw[<-h];exact e14);omega
  · obtain⟨ile,ieq⟩:=hv x;obtain⟨elt,eat⟩:=bO_ev e g (_of x) (by simp) wl hOp
    set h:=(H :: d).foldl _B.cE (_of x)
    have hl:h.length=15+d.length:=by simp only[h,ir,List.length_ofFn,List.length_cons];omega
    rw[show (H :: (d ++ [g])).foldl _B.cE (_of x)=_B.cE h g from List.foldl_append]
    refine⟨fun w hw=>?_,fun P hP0 hPg w hw hPw=>?_⟩
    · rw[an] at hw;split_ifs at hw with h1 h2;{rw[elt w (by omega)];exact ile w hw}
      rw[show w=e.2.length by omega,eat];rw[hgi] at hw
      rcases hOp with hOp|hOp <;> rw[hOp] at hw⊢ <;> simp[GateOp.eval] at hw⊢
      · exact⟨ile _ hw.1,ile _ hw.2⟩
      · exact hw.imp (ile _) (ile _)
    · have iP:=ieq P hP0 fun g' hg'=>hPg g' (List.mem_append_left _ hg')
      rw[an];split_ifs with h1 h2;{rw[elt w (by omega)];exact iP w (by omega) hPw}
      · have ham:a∈g.inputs:=by rw[hgi];simp
        have hbm:b∈g.inputs:=by rw[hgi];simp
        have ha:=hIn a ham;have hb:=hIn b hbm
        rw[show w=e.2.length by omega,eat,iP a (by omega) (hPg g (by simp) a ham),iP b (by omega) (hPg g (by simp) b hbm),hgi];rfl
      · omega
lemma _dm (a b:O) (h:Nat.testBit (68723673216:ℕ) (14*Min.min a.val b.val+Max.max a.val b.val)=true):∃ p l:Fin 7,Inc p l/\((a=Fin.castAdd 7 p/\b=Fin.natAdd 7 l)\/(a=Fin.natAdd 7 l/\b=Fin.castAdd 7 p)):=by revert a b h;decide +kernel
lemma no_fano_27_or_incident (C:Circuit) (hS:C.size<=27) (hA:IsAO2 14 C) (hF:(gateAt C 0).op=GateOp.or) (hN:∀ x:O->_d,C.eval (_of x)=true↔ ∃ p l:Fin 7,Inc p l/\x (Fin.castAdd 7 p)=true/\x (Fin.natAdd 7 l)=true) (hM:Nat.testBit (68723673216:ℕ) (14*Min.min (opnd C 0 0) (opnd C 0 1)+Max.max (opnd C 0 0) (opnd C 0 1))=true):False:=by
 cases A:C.gates with
 | nil=>
  have hv:∀ x:O->_d,C.eval (_of x)=(_of x).getD C.output false:=fun x=>by simp[Circuit.eval,Circuit.wires,A]
  by_cases ho:C.output<14
  · obtain⟨p,l,-,h1,h2⟩:=(hN fun i=>decide (i.val=C.output)).1 (by rw[hv,ofg _ ho];simp);simp at h1 h2;omega
  · have S:=(hN fun _=>true).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩;rw[hv,List.getD_eq_default _ _ (by simp;omega)] at S;exact _fnt S
 | cons g0 rest=>
  have hp:0<C.gates.length:=by simp[A]
  have h0o:g0.op=GateOp.or:=by simpa[gateAt,A] using hF
  have h0i:g0.inputs=[opnd C 0 0,opnd C 0 1]:=by have:=hA.2.2 g0 (by simp[A]);simp only[opnd,gateAt,A,List.getD_cons_zero];rcases h:g0.inputs with _|⟨a,_|⟨b,_|_⟩⟩ <;> simp_all
  have ha:opnd C 0 0<14:=hA.2.1 0 hp _ (by simp[gateAt,A,h0i])
  have hb:opnd C 0 1<14:=hA.2.1 0 hp _ (by simp[gateAt,A,h0i])
  let u':O:=⟨opnd C 0 0,ha⟩;let v':O:=⟨opnd C 0 1,hb⟩
  obtain⟨p,l,hpl,huv⟩:=_dm u' v' hM
  have hrok:Rk rest:=fun k hk=>by
   have hk1:k+1<C.gates.length:=by simp[A];omega
   have hg:gateAt C (k+1)=rest.getD k ⟨GateOp.or,[]⟩:=by simp[gateAt,A]
   have hm:rest.getD k ⟨GateOp.or,[]⟩∈C.gates:=by rw[<-hg,gateAt,_lge _ _ hk1];exact List.getElem_mem hk1
   exact⟨hA.1 _ hm,hA.2.2 _ hm,fun u hu=>by have:=hA.2.1 (k+1) hk1 u (hg▸hu);omega⟩
  obtain⟨rl,gl,g14,gs,-,e14,evl⟩:=lS g0 rest hrok
  set st:=rest.foldl bO mr
  have hCe:∀ x:O->_d,C.eval (_of x)=((g0 :: rest).foldl _B.cE (_of x)).getD C.output false:=fun x=>by dsimp only[Circuit.eval,Circuit.wires];rw[A];rfl
  have hout:C.output<15+rest.length:=by
   have h1:=(hN fun _=>true).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩;rw[hCe] at h1
   by_contra hge;rw[List.getD_eq_default _ _ (by rw[ir,List.length_ofFn,List.length_cons];omega)] at h1;exact _fnt h1
  have hP0:∀ x:O->_d,(x u'=true\/x v'=true)->∀ w<15,ev (_of x) (mr.2.getD w none)=(_B.cE (_of x) g0).getD w false:=by
   intro x hx w hw;rw[an];by_cases h:w<14;{rw[mr_lt h];simp only[ev,List.length_ofFn,h,ite_true]}
   obtain rfl:w=14:=by omega
   rw[mr_ge (le_refl 14)];simp only[ev,List.length_ofFn,_nr,ite_false,ite_true,h0o,h0i,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false,id_eq]
   rw[ofg _ ha,ofg _ hb];simpa using hx
  obtain⟨out',ho'⟩:∃ out',st.2.getD C.output none=some out':=by
   cases hr:st.2.getD C.output none with | some w'=>exact⟨w',rfl⟩ | none=>
    let x0:O->_d:=fun i=>decide (i=u')
    have h1:=(evl x0).2 (fun _=>True) (fun w hw _=>hP0 x0 (Or.inl (by simp[x0])) w hw) (fun _ _ _ _=>trivial) C.output (by omega) trivial
    rw[hr,<-hCe] at h1;obtain⟨a,b,-,h2,h3⟩:=(hN x0).1 h1.symm;simp[x0] at h2 h3;have:=congrArg Fin.val (h2.trans h3.symm);simp at this;omega
  let D:Circuit:=bG (s_ p l) ⟨st.1,out'⟩
  have hMd:Monotone2 D:=by rintro g hg;obtain⟨g',hg',rfl⟩:=List.mem_map.mp hg;exact⟨(gs g' hg').1,by simpa using (gs g' hg').2⟩
  have hFσ:∀ y:O->_d,C.eval (_of fun i=>y (s_ p l i))=true↔_B.bw y:=fun y=>by
   rw[hN];constructor
   · rintro⟨a,b,hab,ha,hb⟩;exact(_B.ce y).2 ⟨_,_,q1 p l a b hpl hab,ha,hb⟩
   · rintro⟨u,v,huv,hu,hv⟩;obtain⟨a,b,hab,rfl,rfl⟩:=_B.sL u v huv;obtain⟨h1,h2,h3⟩:=q2 p l a b hpl hab;exact⟨_,_,h1,h2.symm▸hu,h3.symm▸hv⟩
  have hDe:∀ y:O->_d,D.eval (_of y)=(st.1.foldl _B.cE (_of fun i=>y (s_ p l i))).getD out' false:=fun y=>gj (s_ p l) ⟨st.1,out'⟩ y
  have hL:∀ y:O->_d,_B.bw y->D.eval (_of y)=true:=fun y hy=>by
   have:=(evl fun i=>y (s_ p l i)).1 C.output (by rw[<-hCe];exact(hFσ y).2 hy);rw[ho'] at this;rw[hDe];exact this
  have hG:∀ y:O->_d,(y 0=true\/y 7=true)->D.eval (_of y)=C.eval (_of fun i=>y (s_ p l i)):=fun y hy=>by
   have h07:=q0 p l
   have huvy:y (s_ p l u')=true\/y (s_ p l v')=true:=by rcases huv with ⟨h1,h2⟩|⟨h1,h2⟩;{rw[h1,h2,h07.1,h07.2];exact hy};rw[h1,h2,h07.1,h07.2];exact hy.symm
   have:=(evl fun i=>y (s_ p l i)).2 (fun _=>True) (fun w hw _=>hP0 _ huvy w hw) (fun _ _ _ _=>trivial) C.output (by omega) trivial
   rw[ho'] at this;rw[hDe,hCe];exact this
  by_cases h14r:∃ g∈rest,14∈g.inputs
  · refine _U.g14_upper_umbrella_lb_26 D hMd hL (fun x hx=>?_) (by have:=g14 h14r;simp[Circuit.size,D,bG,A] at hS⊢;omega)
    by_contra hn;by_cases h07x:x 0=true\/x 7=true
    · rw[hG x h07x,hFσ,_B.ce] at hx;obtain⟨a,b,hab,ha,hb⟩:=hx;exact hn ⟨a,b,Or.inl hab,ha,hb⟩
    · simp only[not_or,Bool.not_eq_true] at h07x
      have hk:∀ v:O,(v=0\/v=7)->(∀ c,_B.aO v c->x c=false)->False:=by
       intro v hv hnb;let x':O->_d:=fun i=>x i||decide (i=v)
       have hx':D.eval (_of x')=true:=fU D.gates (fun g h=>(hMd g h).1) (_of x) (_of x') (by simp) (fun k b=>by by_cases e:k<14;{rw[ofg _ e] at b⊢;simp[x',b]};rw[List.getD_eq_default _ _ (by simp;omega)] at b;exact absurd b _fnt) D.output hx
       rw[hG x' (by rcases hv with rfl|rfl <;> simp[x']),hFσ,_B.ce] at hx'
       obtain⟨a,b,hab,ha,hb⟩:=hx';simp only[x',Bool.or_eq_true,decide_eq_true_eq] at ha hb
       rcases ha with ha|rfl <;> rcases hb with hb|rfl
       · exact hn ⟨a,b,Or.inl hab,ha,hb⟩
       · exact _fnt ((hnb a (_B.bl hab)).symm.trans ha)
       · exact _fnt ((hnb b hab).symm.trans hb)
       · exact _B.dv _ hab
      have hq:(x 1=false/\x 3=false)\/(x 8=false/\x 10=false):=by
       by_contra hb;simp only[not_or,not_and,_nf] at hb
       cases h1:x 1 <;> cases h8:x 8
       · exact hn ⟨3,10,by decide,hb.1 h1,hb.2 h8⟩
       · exact hn ⟨3,8,by decide,hb.1 h1,h8⟩
       · exact hn ⟨1,10,by decide,h1,hb.2 h8⟩
       · exact hn ⟨1,8,by decide,h1,h8⟩
      have h7:∀ c:O,_B.aO 7 c->c=0\/c=1\/c=3:=fun c hc=>by have:=(_B.ad 7 c).2 hc;revert c this;decide +kernel
      have h0:∀ c:O,_B.aO 0 c->c=7\/c=8\/c=10:=fun c hc=>by have:=(_B.ad 0 c).2 hc;revert c this;decide +kernel
      rcases hq with ⟨h1f,h3f⟩|⟨h8f,h10f⟩
      · exact hk 7 (Or.inr rfl) fun c hc=>by rcases h7 c hc with rfl|rfl|rfl <;> simp_all
      · exact hk 0 (Or.inl rfl) fun c hc=>by rcases h0 c hc with rfl|rfl|rfl <;> simp_all
  · have hno:∀ g∈rest,∀ u∈g.inputs,u≠14:=fun g hg u hu h=>h14r ⟨g,hg,h▸hu⟩
    have hF:∀ y:O->_d,D.eval (_of y)=true↔_B.bw y:=fun y=>by
     have hne:C.output≠14:=fun h=>by rw[h,e14] at ho';cases ho'
     have:=(evl fun i=>y (s_ p l i)).2 (fun w=>w≠14) (fun w hw hne=>by rw[mr_lt (by omega),an];simp only[ev,List.length_ofFn,show w<14 by omega,ite_true]) hno C.output (by omega) hne
     rw[ho'] at this;rw[show D.eval (_of y)=C.eval (_of fun i=>y (s_ p l i)) by rw[hDe,hCe];exact this,hFσ]
    have:=_B.hV D hMd hF;simp[Circuit.size,D,bG,A] at hS this;omega
lemma no_fano_27_or07 (C:Circuit) (hSize:C.size<=27) (hAO:IsAO2 14 C) (hDist:∀ j<C.size,opnd C j 0≠opnd C j 1) (hFirst:(gateAt C 0).op=GateOp.or) (hMin:Min.min (opnd C 0 0) (opnd C 0 1)=0) (hMax:Max.max (opnd C 0 0) (opnd C 0 1)=7) (hFano:∀ x:O->_d,C.eval (_of x)=true↔ ∃ p l:Fin 7,(p=l\/p=l+1\/p=l+3) /\x (Fin.castAdd 7 p)=true/\x (Fin.natAdd 7 l)=true):False:=by
 have _:=hDist;exact no_fano_27_or_incident C hSize hAO hFirst hFano (by rw[hMin,hMax];decide)
end PEqualNP.Outside.L_meta_17987
theorem PEqualNP.Outside.L_meta_17987 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (68723673216 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               ∃ (x8 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x8 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true) := by
 exact fun C s a _ f n m=>False.elim (PEqualNP.Outside.L_meta_17987.no_fano_27_or_incident C s a f n m)
