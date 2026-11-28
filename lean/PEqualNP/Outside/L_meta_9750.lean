import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9750
abbrev H:=true
abbrev J:=false
abbrev Z:=List
abbrev I:=Finset
abbrev Q:=Option
abbrev W:=Z Nat
abbrev F (n:Nat):=Fin n
abbrev X:=@Bool.and_eq_true
abbrev B:=Fin 12
abbrev G:=@Prod.fst
abbrev L:=@Nat.land
abbrev M:=@Nat.beq
abbrev Y:=Bool
abbrev BV:=BitVec
abbrev S2:=I (B)
abbrev Sn (n:Nat):=I (Fin n)
abbrev PP:=Nat×Nat
abbrev LP:=List (Nat×Nat)
abbrev NN:=Nat->Nat
abbrev AO:=BitVec.allOnes 320
abbrev O:=@Finset.mem_filter
abbrev A1:=@List.getD_eq_getElem?_getD
abbrev A2:=@Finset.mem_insert_of_mem
abbrev A3:=@Finset.mem_inter
abbrev A4:=@List.mem_toFinset
abbrev A5:=@Finset.mem_singleton
abbrev A6:=@decide_eq_true_eq
abbrev A7:=@Finset.mem_image
abbrev A8:=@BitVec.toNat
abbrev A9:=@Finset.mem_insert
abbrev Aa:=@Finset.card_le_card
abbrev Ab:=@List.mem_cons
abbrev Ac:=@Finset.mem_range
abbrev Ad:=@Nat.testBit_and
abbrev Ae:=@List.all_eq_true
abbrev Af:=@BitVec.eq_of_getLsbD_eq
abbrev Ag:=@Nat.shiftLeft_eq
abbrev Ah:=@List.getElem?_eq_getElem
abbrev Ai:=@Bool.or_eq_true
abbrev Aj:=@List.mem_map
abbrev Ak:=@Bool.false_eq_true
abbrev Al:=@Finset.card_insert_of_notMem
abbrev Am:=@Finset.mem_sdiff
abbrev Ao:=@Finset.mem_singleton_self
abbrev Ap:=@List.toFinset_card_of_nodup
abbrev Aq:=@BitVec.getLsbD_and
abbrev Ar:=@beq_iff_eq
abbrev As:=@List.map_cons
abbrev At:=@Option.bind_eq_some_iff
abbrev Au:=@Finset.card_image_of_injective
abbrev Av:=@Nat.testBit_shiftRight
abbrev Aw:=@Nat.add_comm
abbrev Ax:=@Finset.image_insert
abbrev Ay:=@Nat.testBit_or
abbrev Az:=@congrArg
abbrev AA:=@Finset.mem_union
abbrev AB:=@ite_false
abbrev AC:=@Finset.mem_univ
abbrev AD:=@Bool.true_and
abbrev AE:=@Finset.nonempty_iff_ne_empty
abbrev AF:=@Nat.eq_of_testBit_eq
abbrev AG:=@Finset.disjoint_left
abbrev AH:=@Nat.testBit_eq_false_of_lt
abbrev AI:=@Nat.strong_induction_on
abbrev AJ:=@Finset.card_union_of_disjoint
abbrev AK:=@List.mem_cons_of_mem
abbrev AL:=@Finset.mem_insert_self
abbrev AM:=@List.mem_range
abbrev AN:=@Finset.mem_erase
abbrev AP:=@Nat.testBit_two_pow_sub_one
abbrev AQ:=@List.length_map
abbrev AR:=@ite_eq_right_iff
abbrev AS:=@Finset.not_nonempty_empty
abbrev AT:=@List.perm_of_nodup_nodup_toFinset_eq
abbrev AU:=@Nat.zero_le
abbrev AV:=@Finset.ssubset_iff_subset_ne
abbrev AW:=@BitVec.getLsbD_not
abbrev AX:=@ite_true
abbrev AY:=@List.length_cons
abbrev AZ:=@Nat.add_assoc
abbrev B0:=@Bool.not_eq_false
abbrev B1:=@BitVec.getLsbD_or
abbrev B2:=@Finset.card_union_add_card_inter
abbrev B3:=@decide_eq_true
abbrev B4:=@List.getElem?_map
abbrev B5:=@List.map_append
abbrev B6:=@decide_true
abbrev B7:=@List.nodup_cons
abbrev B8:=@Bool.false_ne_true
abbrev B9:=@Finset.inter_subset_left
abbrev Ba:=@Nat.pow_le_pow_right
abbrev Bb:=@Finset.inter_eq_left
abbrev Bc:=@Finset.card_pos
abbrev Bd:=@Finset.notMem_empty
abbrev Be:=@Finset.nodup_toList
abbrev Bf:=@List.any_eq_true
abbrev Bg:=@Finset.sum_congr
abbrev Bh:=@List.mem_singleton
abbrev Bi:=@List.toFinset_cons
abbrev Bj:=@Finset.card_image_of_injOn
abbrev Bk:=@Finset.card_singleton
abbrev Bl:=@Finset.card_insert_le
abbrev Bm:=@Finset.inter_subset_right
abbrev Bn:=@List.foldl_cons
abbrev Bo:=@List.contains_eq_mem
abbrev Bp:=@Bool.eq_false_iff
abbrev Bq:=@Finset.card_lt_card
abbrev Br:=@Finset.union_subset
abbrev Bt:=@Nat.add_sub_cancel_left
abbrev Bu:=@Nat.le_add_right
abbrev Bv:=@Finset.card_filter
abbrev Bw:=@List.mem_filterMap
abbrev Bx:=@List.mem_append
abbrev By:=@Finset.singleton_subset_iff
abbrev Bz:=@Finset.mem_toList
abbrev BA:=@Nat.le_refl
abbrev BB:=@Finset.card_filter_add_card_filter_not
abbrev BC:=@Bool.or_eq_false_iff
abbrev BD:=@List.length_pos_iff
abbrev BE:=@Finset.subset_inter
abbrev BF:=@Finset.card_eq_zero
abbrev BG:=@Finset.filter_congr
abbrev BH:=@List.length_erase_of_mem
abbrev BI:=@Finset.forall_mem_insert
abbrev BJ:=@List.mem_cons_self
abbrev BK:=@Finset.card_sdiff_add_card_eq_card
abbrev BL:=@BitVec.getLsbD_allOnes
abbrev BM:=@Finset.not_nonempty_iff_eq_empty
abbrev BN:=@Finset.union_inter_distrib_right
abbrev BO:=@Set.mem_singleton_iff
abbrev BP:=@List.getElem?_eq_none
abbrev BQ:=@List.length_ofFn
abbrev BR:=@List.countP_cons
abbrev BS:=@Option.getD_some
abbrev BT:=@Bool.false_or
abbrev BU:=@Option.map_some
abbrev BW:=@decide_eq_false
abbrev BX:=@Nat.testBit_xor
abbrev BY:=@Finset.insert_erase
abbrev BZ:=@BitVec.ofBoolListLE
abbrev C0:=@List.idxOf_lt_length_of_mem
abbrev C1:=@Nat.zero_add
abbrev C2:=@List.map_nil
abbrev C3:=@BitVec.getLsbD_ofBoolListLE
abbrev C4:=@List.map_map
abbrev C5:=@Finset.sum_le_sum_of_subset
abbrev C6:=@Finset.mem_biUnion
abbrev C7:=@Finset.singleton_injective
abbrev C8:=@Set.mem_insert_iff
abbrev C9:=@Nat.or_lt_two_pow
abbrev Ca:=@List.foldl_append
abbrev Cb:=@Bool.and_true
abbrev Cd:=@Finset.insert_eq_of_mem
abbrev Ce:=@List.length_take
abbrev Ch:=@Bool.not_eq_true
abbrev Ci:=@Nat.not_lt
abbrev Cj:=@Nat.two_pow_pos
abbrev Ck:=@Finset.card_filter_le
abbrev Cl:=@Nat.eq_of_beq_eq_true
abbrev Cm:=@Finset.filter_filter
abbrev Cn:=@BitVec.or_comm
abbrev Co:=@Finset.card_union_le
abbrev Cp:=@Finset.single_le_sum
abbrev Cq:=@Finset.filter_subset
abbrev Cr:=@Nat.pow_lt_pow_right
abbrev Cs:=@Bool.and_false
abbrev Cv:=@List.getElem?_range
abbrev Cw:=@Finset.sdiff_subset
abbrev Cx:=@Nat.testBit_two_pow
abbrev Cy:=@List.map_congr_left
abbrev Cz:=@List.getElem?_ofFn
abbrev CA:=@bne_iff_ne
abbrev CB:=@Finset.card_eq_one
abbrev CC:=@List.length_append
abbrev CD:=@Finset.mem_product
abbrev CE:=@BitVec.getLsbD_xor
abbrev CF:=@Finset.eq_empty_iff_forall_notMem
abbrev CH:=@Finset.card_empty
abbrev CI:=@Finset.eq_empty_of_forall_notMem
abbrev Qa {a b:Prop}:=@absurd a b
abbrev Qm:=@List.mem_map_of_mem
abbrev D1:=@Relation.ReflTransGen
abbrev D2:=@Bool.cond_false
abbrev D3:=@Nat.shiftRight
abbrev D4:=@Bool.cond_true
abbrev D5:=@Or.inl
abbrev D6:=@Or.inr
abbrev D7:=@Equiv.Perm
abbrev D8:=@Bool.not_eq_true'
abbrev D9:=@Nat.xor
abbrev Da:=@List.ofFn
abbrev Db:=@Nat.ble
abbrev Dc:=@Nat.lor
abbrev Dd:=@Nat.shiftLeft
abbrev De:=@Nat.sub
abbrev Df:=@Nat.ble_eq
abbrev Dg:=@List.perm_cons_erase
abbrev Dh:=@List.mem_of_getElem?
abbrev Di:=@List.length_eraseIdx_of_lt
abbrev Dj:=@Nat.mod
abbrev Dl:=@Option.some.injEq
abbrev Dn:=@Nat.add
abbrev Do:=@BitVec.toNat_inj
abbrev Dp:=@Relation.ReflTransGen.tail
abbrev Dq:=@Relation.ReflTransGen.cases_head
abbrev Dr:=@Relation.ReflTransGen.head_induction_on
abbrev Ds:=@List.getElem_cons_succ
abbrev Dt:=@Relation.ReflTransGen.head
abbrev Du:=@Ne.symm
abbrev Dw:=@Bool.not_true
abbrev Dy:=@Bool.not_false
abbrev Dz:=@Nat.add_zero
abbrev DA:=@List.getElem_cons_zero
abbrev DB:=@List.sum_cons
abbrev DC:=@Bool.or_false
abbrev DD:=@Relation.ReflTransGen.refl
abbrev DE:=@Nat.beq_eq
abbrev DF:=@List.mem_erase_of_ne
abbrev DG:=@List.Nodup.getElem_inj_iff
abbrev DH:=@Nat.div
abbrev DI:=@Function.comp_def
abbrev DJ:=@Nat.succ_eq_add_one
abbrev DK:=@List.getD_cons_succ
abbrev DL:=@Nat.pow_succ
abbrev DM:=@Bool.false_and
abbrev DN:=@Nat.zero_testBit
abbrev DO:=@List.getElem_map
abbrev DP:=@Bool.toNat_false
abbrev DQ:=@Nat.add_eq
abbrev DR:=@List.zipWith_cons_cons
abbrev DS:=@BitVec.eq_of_toNat_eq
abbrev DT:=@List.getElem_of_mem
abbrev DU:=@List.getD_cons_zero
abbrev DV:=@Nat.mul
abbrev DW:=@Bool.not_not
abbrev DX:=@Finset.eq_of_subset_of_card_le
abbrev DY:=@Finset.card_pair
abbrev DZ:=@BitVec.toNat_and
abbrev E0:=@Finset.card_le_mul_card_image
abbrev E1:=@List.countP_map
abbrev E2:=@Finset.union_sdiff_of_subset
abbrev E3:=@Bool.eq_iff_iff
abbrev E4:=@Finset.filter_eq_empty_iff
abbrev E5:=@Nat.shiftRight_eq_div_pow
abbrev E6:=@List.mem_of_find?_eq_some
abbrev E7:=@List.getElem?_append_left
abbrev E8:=@Finset.image_subset_image
abbrev E9:=@Finset.card_erase_of_mem
abbrev Ea:=@Bool.true_xor
abbrev Eb:=@Set.InjOn
abbrev Ec:=@Finset.sum_add_distrib
abbrev Ed:=@Equiv.apply_symm_apply
abbrev Ee:=@Bool.true_or
abbrev Ef:=@Bool.or_true
namespace Mono
open Finset Sum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def rE:Y->Y->Y->Y
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[local simp] theorem gop_true (a b:Y):rE H a b=(a&&b):=rfl
@[local simp] theorem gop_false (a b:Y):rE J a b=(a||b):=rfl
abbrev N:=Z (Y×Nat×Nat)
def oi (D:N)(j:Nat):Y:=(D.getD j (J,0,0)).1
def nX (D:N)(j:Nat):Nat:=(D.getD j (J,0,0)).2.1
def nL (D:N)(j:Nat):Nat:=(D.getD j (J,0,0)).2.2
def ox (w:Z Y)(g:Y×Nat×Nat):Z Y:=w++[rE g.1 (w.getD g.2.1 J) (w.getD g.2.2 J)]
def wl (D:N)(w:Z Y):Z Y:=D.foldl ox w
def val (D:N){n:Nat}(x:F n->Y)(w:Nat):Y:=(wl D (Da x)).getD w J
def R (n:Nat)(D:N):Prop:=∀ j,j<D.length->nX D j<n+j/\nL D j<n+j/\nX D j≠nL D j
def mP (D:N)(w:Nat):I Nat:=(range D.length).filter (fun j=>nX D j=w\/nL D j=w)
def K (D:N)(w:Nat):Nat:=(mP D w).card
def sk (n:Nat)(D:N):Prop:=∀ w,w+1<n+D.length->1<=K D w
def m7 (n:Nat)(D:N):Prop:=R n D/\sk n D/\D≠[]
def mN (n:Nat)(D:N):Nat:=n+D.length-1
def nn {n:Nat}(v:F n):F n->Y:=fun i=>decide (i=v)
def V (n:Nat)(D:N)(w:Nat):Sn n:=univ.filter (fun v=>val D (nn v) w=H)
def mo (D:N)(a:I Nat):Nat:=∑ w∈a,(K D w-1)
def nc (n:Nat)(D:N):I Nat:=range (n+D.length-1)
def me (n:Nat)(D:N):Nat:=mo D (nc n D)
def nh (n:Nat)(D:N):Nat:=mo D ((nc n D).filter (fun w=>(V n D w).Nonempty))
def oL (n:Nat)(D:N):Nat:=mo D ((nc n D).filter (fun w=>¬(V n D w).Nonempty))
def qN (n:Nat)(D:N):I Nat:=(range (n+D.length)).filter (fun w=>2<=K D w)
def mb (n:Nat)(D:N):Sn n:=(qN n D).biUnion (V n D)
def U (n:Nat)(D:N):Sn n:=univ \ mb n D
def pz (n:Nat)(D:N):I (Σ _:Nat,Nat):=(nc n D).sigma (fun w=>range (K D w-1))
def np (n:Nat)(D:N):I (Σ _:Nat,Nat):=(pz n D).filter (fun u=>(V n D u.1).Nonempty)
def ps (D:N):I (Nat×Y):=range D.length ×ˢ univ
def E (D:N)(e:Nat×Y):Nat:=if e.2=H then nL D e.1 else nX D e.1
def mt (n:Nat)(D:N)(a:I Nat):I (Nat×Y):=(ps D).filter (fun e=>E D e∈a/\n+e.1∉a)
def mI (n:Nat)(D:N)(a:I Nat):I Nat:=(range D.length).filter (fun j=>n+j∈a/\nX D j∈a/\nL D j∈a)
def p6 (n:Nat)(a:I Nat):I Nat:=a.filter (fun w=>w<n)
def S (n:Nat)(D:N)(T:Sn n):I Nat:=(range (n+D.length)).filter (fun w=>(V n D w∩T).Nonempty)
def mw (n:Nat)(D:N)(b:F n->Nat):Prop:=∀ v∈mb n D,2<=K D (b v)/\V n D (b v)={v}
def mF (n:Nat)(D:N)(b:F n->Nat):I (Σ _:Nat,Nat):=(mb n D).image (fun v=>(⟨b v,0⟩:Σ _:Nat,Nat))
def mi (n:Nat)(D:N)(b:F n->Nat):I (Σ _:Nat,Nat):=np n D \ mF n D b
lemma rv (D:N)(j:Nat)(h:j<D.length):oi D j=(D[j]).1:=by simp[oi,Ah h]
lemma ro (D:N)(j:Nat)(h:j<D.length):nX D j=(D[j]).2.1:=by simp[nX,Ah h]
lemma rx (D:N)(j:Nat)(h:j<D.length):nL D j=(D[j]).2.2:=by simp[nL,Ah h]
lemma qJ (g:Y×Nat×Nat)(D:N)(w:Z Y):wl (g::D) w=wl D (ox w g):=rfl
lemma pH (D ze:N)(w:Z Y):wl (D++ze) w=wl ze (wl D w):=by simp[wl]
lemma om (w:Z Y)(g:Y×Nat×Nat):(ox w g).length=w.length+1:=by simp[ox]
lemma p3 (D:N):∀ w:Z Y,(wl D w).length=w.length+D.length:=by induction D with|nil=>intro w;simp[wl] | cons g D a=>intro w;rw[qJ,a,om];simp;omega
lemma pg (w:Z Y)(g:Y×Nat×Nat)(i:Nat)(h:i<w.length):(ox w g).getD i J=w.getD i J:=by simp[ox,E7 h]
lemma pn (D:N):∀ (w:Z Y) (i:Nat),i<w.length->(wl D w).getD i J=w.getD i J:=by induction D with|nil=>intro w i _;rfl | cons g D a=>intro w i h;rw[qJ,a _ _ (by rw[om];omega),pg _ _ _ h]
lemma rZ (w:Z Y)(i:Nat)(h:w.length<=i):w.getD i J=J:=by simp[BP h]
lemma oA (w:Z Y)(g:Y×Nat×Nat):(ox w g).getD w.length J=rE g.1 (w.getD g.2.1 J) (w.getD g.2.2 J):=by simp[ox]
lemma qZ (D:N)(w:Z Y)(j:Nat)(c:j<D.length):(wl D w).getD (w.length+j) J=rE (oi D j) ((wl (D.take j) w).getD (nX D j) J) ((wl (D.take j) w).getD (nL D j) J):=by
 have a:D=D.take j++D[j]::D.drop (j+1):=(by simp);have b:(wl (D.take j) w).length=w.length+j:=by rw[p3,Ce];omega
 rw[rv D j c,ro D j c,rx D j c];conv_lhs=>rw[a,pH,qJ];rw[pn _ _ _ (by rw[om,b];omega),<-b,oA]
lemma oq (D:N)(w:Z Y)(j i:Nat)(c:i<w.length+j)(d:j<=D.length):(wl (D.take j) w).getD i J=(wl D w).getD i J:=by
 have a:D=D.take j++D.drop j:=(by simp);have b:(wl (D.take j) w).length=w.length+j:=by rw[p3,Ce];omega
 conv_rhs=>rw[a,pH]
 rw[pn (D.drop j) (wl (D.take j) w) i (by rw[b];exact c)]
lemma my (D:N){n:Nat}(x:F n->Y)(i:Nat)(h:i<n):val D x i=x ⟨i,h⟩:=by unfold val;rw[pn _ _ _ (by simpa using h)];simp[h]
lemma os (D:N){n:Nat}(x:F n->Y)(w:Nat)(h:n+D.length<=w):val D x w=J:=by unfold val;exact rZ _ _ (by rw[p3];simpa using h)
lemma rY (D:N){n:Nat}(x:F n->Y)(k w:Nat)(a:w<n+k)(b:k<=D.length):val (D.take k) x w=val D x w:=by unfold val;exact oq D _ k w (by simpa using a) b
lemma mS {n:Nat}{D:N}(b:R n D)(x:F n->Y)(j:Nat)(a:j<D.length):val D x (n+j)=rE (oi D j) (val D x (nX D j)) (val D x (nL D j)):=by
 obtain⟨c,d,-⟩:=b j a;have h:=qZ D (Da x) j a;simp only[BQ] at h;unfold val;rw[h,oq D _ j _ (by simpa using c) a.le,
  oq D _ j _ (by simpa using d) a.le]
lemma pp {n:Nat}{D:N}(c:R n D)(x:F n->Y)(f:Nat->Y)(a:∀ i (h:i<n),f i=x ⟨i,h⟩)(g:∀ j,j<D.length->f (n+j)=rE (oi D j) (f (nX D j)) (f (nL D j))):∀ w,w<n+D.length->val D x w=f w:=by
 intro w;induction w using AI with
 | _ w d=>
   intro hw;by_cases e:w<n;. rw[my D x w e,a w e]
   . obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have b:j<D.length:=(by omega)
     obtain⟨k,l,-⟩:=c j b;rw[mS c x j b,g j b,d _ k (by omega),d _ l (by omega)]
abbrev qX:=Y ⊕ Nat
def mL (zw:Z Y):qX->Y
 | inl b=>b
 | inr k=>zw.getD k J
def nu (m:Z qX)(i:Nat):qX:=m.getD i (inl J)
def n0 (t:Y):qX->qX->qX ⊕ (Nat×Nat)
 | inl a,r=>inl (if a=t then r else inl a)
 | inr i,inl b=>inl (if b=t then inr i else inl b)
 | inr i,inr j=>if i=j then inl (inr i) else inr (i,j)
def mR:GateOp->Y
 | GateOp.and=>H
 | _=>J
def mC (n:Nat)(c:Z qX×N)(g:Gate):Z qX×N:=match g.inputs with
 | []=>(c.1++[inl (mR g.op)],c.2)
 | [a]=>(c.1++[nu c.1 a],c.2)
 | a::b::_=>
   match n0 (mR g.op) (nu c.1 a) (nu c.1 b) with
   | inl r=>(c.1++[r],c.2)
   | inr p=>(c.1++[inr (n+c.2.length)],c.2++[(mR g.op,p.1,p.2)])
def pi (zb:Nat):qX->Prop
 | inl _=>True
 | inr k=>k<zb
def py (n:Nat)(a:Z qX×N):Prop:=R n a.2/\∀ r∈a.1,pi (n+a.2.length) r
lemma ry {a a':Nat}(h:a<=a')(r:qX)(c:pi a r):pi a' r:=by
 rcases r with b|k;. trivial
 . exact lt_of_lt_of_le c h
lemma nJ (a:Z Y)(m:Z qX)(i:Nat):mL a (nu m i)=(m.map (mL a)).getD i J:=by simp only[nu,A1,B4];cases m[i]?<;>rfl
lemma ou (a:Nat)(m:Z qX)(b:∀ r∈m,pi a r)(i:Nat):pi a (nu m i):=by
 simp only[nu,A1];rcases h:m[i]? with _|r;. trivial
 . exact b r (Dh h)
lemma pW (a:Z Y)(g:Y×Nat×Nat)(r:qX)(c:pi a.length r):mL (ox a g) r=mL a r:=by
 rcases r with b|k;. rfl
 . exact pg a g k c
lemma r7 (t:Y)(c:Z Y)(a b r:qX)(h:n0 t a b=inl r):mL c r=rE t (mL c a) (mL c b):=by
 rcases a with a|i;. simp only[n0,inl.injEq] at h;subst h;cases t<;>cases a<;>simp[mL]
 . rcases b with b|j
   . simp only[n0,inl.injEq] at h;subst h;cases t<;>cases b<;>simp[mL]
   . simp only[n0] at h;split_ifs at h with hij;simp only[inl.injEq] at h;subst h;subst hij;cases t<;>simp[mL]
lemma rr (c:Nat)(t:Y)(a b r:qX)(d:pi c a)(e:pi c b)(h:n0 t a b=inl r):pi c r:=by
 rcases a with a|i
 . simp only[n0,inl.injEq] at h;subst h;split_ifs
   . exact e
   . trivial
 . rcases b with b|j
   . simp only[n0,inl.injEq] at h;subst h;split_ifs
     . exact d
     . trivial
   . simp only[n0] at h;split_ifs at h;simp only[inl.injEq] at h;subst h;exact d
lemma r6 (t:Y)(a b:qX)(p:Nat×Nat)(h:n0 t a b=inr p):a=inr p.1/\b=inr p.2/\p.1≠p.2:=by
 rcases a with a|i;. simp[n0] at h
 . rcases b with b|j
   . simp[n0] at h
   . simp only[n0] at h;split_ifs at h with hij;cases h;exact⟨rfl,rfl,hij⟩
lemma rS (b:GateOp)(a:b∈({GateOp.and,GateOp.or}:Set GateOp)):b.eval []=mR b:=by rcases a with rfl|rfl<;>rfl
lemma rV (b:GateOp)(a:b∈({GateOp.and,GateOp.or}:Set GateOp))(u:Y):b.eval [u]=u:=by rcases a with rfl|rfl<;>simp[GateOp.eval]
lemma rk (b:GateOp)(a:b∈({GateOp.and,GateOp.or}:Set GateOp))(u v:Y):b.eval [u,v]=rE (mR b) u v:=by rcases a with rfl|rfl<;>simp[GateOp.eval,mR]
lemma pu (D ze:N)(k:Nat)(h:k<D.length):(D++ze).getD k (J,0,0)=D.getD k (J,0,0):=by simp[E7 h]
lemma qK (D:N)(g:Y×Nat×Nat):(D++[g]).getD D.length (J,0,0)=g:=by simp
lemma qs {n:Nat}{D:N}(e:R n D)(t:Y)(i j:Nat)(d:i<n+D.length)(f:j<n+D.length)(a:i≠j):R n (D++[(t,i,j)]):=by
 intro k c;simp only[CC,List.length_singleton] at c;by_cases c':k<D.length;. simp only[nX,nL,pu D _ k c'];exact e k c'
 . have b:k=D.length:=(by omega);subst b;simp only[nX,nL,qK];exact⟨d,f,a⟩
lemma qc {n:Nat}{D:N}(c:R n D)(k:Nat):R n (D.take k):=by intro j hj;simp only[Ce] at hj;have b:j<k:=(by omega);have a:j<D.length:=(by omega);have e:(D.take k).getD j (J,0,0)=D.getD j (J,0,0):=(by simp[b]);simp only[nX,nL,e];exact c j a
lemma r3 (n:Nat)(t:Z qX×N)(g:Gate)(hg:g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2)(h:py n t):py n (mC n t g)/\(mC n t g).2.length<=t.2.length+1/\∀ (x:F n->Y) (w:Z Y),t.1.map (mL (wl t.2 (Da x)))=w->(mC n t g).1.map (mL (wl (mC n t g).2 (Da x)))=w++[g.op.eval (g.inputs.map fun i=>w.getD i J)]:=by
 obtain⟨m,D⟩:=t;obtain⟨op,q⟩:=g;obtain⟨f,j⟩:=hg;obtain⟨u,d⟩:=h;dsimp only at u d f j ⊢;rcases q with _|⟨a,_|⟨b,_|⟨c,h0⟩⟩⟩;. refine⟨⟨u,fun r s=>by simp only[mC,Bx,Bh] at s;rcases s with s|rfl;exact d r s;trivial⟩,by simp[mC],fun x w v=>by subst v;simp only[mC,B5,As,C2,mL,rS op f]⟩
 . refine⟨⟨u,fun r s=>by simp only[mC,Bx,Bh] at s;rcases s with s|rfl;exact d r s;exact ou _ m d a⟩,by simp[mC],fun x w v=>by subst v;simp only[mC,B5,As,C2,rV op f,nJ]⟩
 . have k:=ou _ m d a;have l:=ou _ m d b;rcases hc:n0 (mR op) (nu m a) (nu m b) with r|p
   . refine⟨⟨by simpa only[mC,hc] using u,fun r' s=>by simp only[mC,hc,Bx,Bh] at s ⊢;rcases s with s|rfl;exact d r' s;exact rr _ _ _ _ _ k l hc⟩,by simp[mC,hc],fun x w v=>by subst v;simp only[mC,hc,B5,As,C2,rk op f,r7 _ (wl D (Da x)) _ _ _ hc,nJ]⟩
   . obtain⟨z,eb,o⟩:=r6 _ _ _ _ hc;rw[z] at k;rw[eb] at l;have u':=qs u (mR op) p.1 p.2 k l o;refine⟨⟨by simpa only[mC,hc] using u',fun r' s=>by simp only[mC,hc,Bx,Bh,CC,List.length_singleton] at s ⊢;exact s.elim (fun h=>ry (by omega) r' (d r' h)) (fun h=>h▸Nat.lt_succ_self _)⟩,by simp[mC,hc],fun x w v=>?_⟩
     subst v;set y:=wl D (Da x);have e:y.length=n+D.length:=(by rw[p3,BQ]);have hW':wl (D++[(mR op,p.1,p.2)]) (Da x)=ox y (mR op,p.1,p.2):=by rw[pH];rfl
     have h1:m.map (mL (ox y (mR op,p.1,p.2)))=m.map (mL y):=Cy fun r s=>pW _ _ r (by rw[e];exact d r s);have h2:(ox y (mR op,p.1,p.2)).getD (n+D.length) J=rE (mR op) ((m.map (mL y)).getD a J) ((m.map (mL y)).getD b J):=by rw[<-e,oA,<-nJ,<-nJ,z,eb];rfl
     simp only[mC,hc,hW',B5,As,C2,h1,mL,h2,rk op f]
 . simp at j
lemma qO (n:Nat)(gs:Z Gate)(a:∀ g∈gs,g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2):∀ st:Z qX×N,py n st->py n (gs.foldl (mC n) st)/\(gs.foldl (mC n) st).2.length<=st.2.length+gs.length/\∀ (x:F n->Y) (w:Z Y),st.1.map (mL (wl st.2 (Da x)))=w->(gs.foldl (mC n) st).1.map (mL (wl (gs.foldl (mC n) st).2 (Da x)))=gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i J)]) w:=by
 induction gs with
 | nil=>intro st h;exact⟨h,by simp,fun x w b=>b⟩
 | cons g gs f=>
   intro st h;obtain⟨c,l,d⟩:=r3 n st g (a g (by simp)) h;obtain⟨j,k,e⟩:=f (fun g' hg'=>a g' (by simp[hg'])) _ c;refine⟨j,?_,fun x w b=>?_⟩;. simp only[Bn,AY];omega
   . simp only[Bn];exact e x _ (d x w b)
lemma sp (n:Nat)(x:F n->Y):((List.range n).map inr).map (mL (wl ([]:N) (Da x)))=Da x:=by
 apply List.ext_getElem
 . simp
 . intro i a b;simp only[AQ,List.length_range] at a;simp[mL,wl,a]
lemma o1 {n:Nat}(e:Circuit)(a:Monotone2 e):(∃ b:Y,∀ x:F n->Y,e.eval (Da x)=b)\/(∃ i:F n,∀ x:F n->Y,e.eval (Da x)=x i)\/(∃ D:N,R n D/\D≠[]/\D.length<=e.size/\∀ x:F n->Y,val D x (mN n D)=e.eval (Da x)):=by
 have q:py n ((List.range n).map inr,([]:N)):=by
  refine⟨fun j o=>Qa o (by simp),fun r f=>?_⟩
  simp only[Aj,AM] at f;obtain⟨k,g,rfl⟩:=f;simpa[pi] using g
 obtain⟨⟨hS,hok⟩,hlen,hsem⟩:=qO n e.gates a _ q;generalize e.gates.foldl (mC n) ((List.range n).map inr,([]:N))=st
  at hS hok hlen hsem
 have⟨m,D⟩:=st;dsimp only at hS hok hlen hsem;have c:∀ x:F n->Y,e.eval (Da x)=mL (wl D (Da x)) (nu m e.output):=by intro x;rw[nJ,hsem x (Da x) (sp n x)];rfl
 have g:=ou _ m hok e.output;rcases f:nu m e.output with b|k;. exact D5 ⟨b,fun x=>by rw[c x,f];rfl⟩
 . rw[f] at g;have g':k<n+D.length:=g;by_cases d:k<n
   . exact D6 (D5 ⟨⟨k,d⟩,fun x=>by rw[c x,f];exact my D x k d⟩)
   . have l:(D.take (k-n+1)).length=k-n+1:=by rw[Ce];omega
     refine D6 (D6 ⟨D.take (k-n+1),qc hS _,?_,?_,fun x=>?_⟩);. intro h;rw[h] at l;simp at l
     . rw[l];simp only[List.length_nil,C1] at hlen;unfold Circuit.size;omega
     . have p:mN n (D.take (k-n+1))=k:=by unfold mN;rw[l];omega
       rw[p,rY D x (k-n+1) k (by omega) (by omega),c x,f];rfl
lemma ov {D:N}{w:Nat}(h:K D w=0)(j:Nat)(a:j<D.length):nX D j≠w/\nL D j≠w:=by unfold K mP at h;rw[BF,E4] at h;have:=h (Ac.mpr a);tauto
def pG (c a:Nat):Nat:=if c<a then a-1 else a
def mM (c w:Nat):Nat:=if w<c then w else w+1
def ny (n j:Nat)(D:N):N:=(D.eraseIdx j).map (fun g=>(g.1,pG (n+j) g.2.1,pG (n+j) g.2.2))
lemma nI (n j:Nat)(D:N)(a:j<D.length):(ny n j D).length=D.length-1:=by simp[ny,List.length_eraseIdx,a]
lemma qv (n j:Nat)(D:N)(k:Nat)(a:mM j k<D.length):oi (ny n j D) k=oi D (mM j k)/\nX (ny n j D) k=pG (n+j) (nX D (mM j k))/\nL (ny n j D) k=pG (n+j) (nL D (mM j k)):=by
 have e:(ny n j D).getD k (J,0,0) = ((D.getD (mM j k) (J,0,0)).1,pG (n+j) (D.getD (mM j k) (J,0,0)).2.1,pG (n+j) (D.getD (mM j k) (J,0,0)).2.2):=by simp only[ny,A1,B4,List.getElem?_eraseIdx];unfold mM at a ⊢;split_ifs at a ⊢<;>simp[Ah a]
 unfold oi nX nL;rw[e];exact⟨rfl,rfl,rfl⟩
lemma ph {n:Nat}{D:N}(g:R n D)(j:Nat)(f:j<D.length)(h:K D (n+j)=0):R n (ny n j D):=by
 intro k e;rw[nI n j D f] at e;have e':mM j k<D.length:=by unfold mM;split_ifs<;>omega
 have c:(k<j/\mM j k=k)\/(j<=k/\mM j k=k+1):=by unfold mM;split_ifs<;>omega
 obtain⟨m,q,d⟩:=g _ e';obtain⟨o,p⟩:=ov h _ e';obtain⟨-,i,l⟩:=qv n j D k e';rw[i,l];generalize mM j k=k' at *;generalize nX D k'=a at *;generalize nL D k'=b at *;refine⟨?_,?_,?_⟩<;>unfold pG<;>split_ifs<;>omega
lemma rp {n:Nat}{D:N}(d:R n D)(j:Nat)(c:j<D.length)(f:K D (n+j)=0)(x:F n->Y)(w:Nat)(l:w<n+(D.length-1)):val (ny n j D) x w=val D x (mM (n+j) w):=by
 refine pp (ph d j c f) x (fun u=>val D x (mM (n+j) u)) (fun i g=>?_) (fun k b=>?_) w (by rw[nI n j D c];exact l)
 . have e:mM (n+j) i=i:=by unfold mM;split_ifs<;>omega
   show val D x (mM (n+j) i)=x ⟨i,g⟩;rw[e];exact my D x i g
 . rw[nI n j D c] at b;have b':mM j k<D.length:=by unfold mM;split_ifs<;>omega
   obtain⟨m,o,r⟩:=qv n j D k b';obtain⟨p,s⟩:=ov f _ b';have q:mM (n+j) (n+k)=n+mM j k:=by unfold mM;split_ifs<;>omega
   have h:∀ a,a≠n+j->mM (n+j) (pG (n+j) a)=a:=by intro a ha;unfold mM pG;split_ifs<;>omega
   show val D x (mM (n+j) (n+k))=rE (oi (ny n j D) k) (val D x (mM (n+j) (nX (ny n j D) k))) (val D x (mM (n+j) (nL (ny n j D) k)));rw[q,m,o,r,h _ p,h _ s];exact mS d x _ b'
lemma r8 {n:Nat}(r:(F n->Y)->Y)(c:∀ i:F n,∃ x y:F n->Y,(∀ k,k≠i->x k=y k)/\r x≠r y):∀ (s:Nat) (D:N),D.length=s->R n D->D≠[]->(∀ x:F n->Y,val D x (mN n D)=r x)->∃ D':N,m7 n D'/\D'.length<=s/\∀ x:F n->Y,val D' x (mN n D')=r x:=by
 intro s;induction s using AI with
 | _ s ih=>
   intro D hlen hS hne hD;have p:0<D.length:=BD.mpr hne;by_cases v:sk n D;. exact⟨D,⟨hS,v,hne⟩,hlen.le,hD⟩
   . obtain⟨w,z,a⟩:∃ w,w+1<n+D.length/\K D w=0:=by by_contra l;exact v fun w z=>by by_contra h0;exact l ⟨w,z,by omega⟩
     by_cases f:w<n
     . exfalso;have⟨x,y,o,d⟩:=c ⟨w,f⟩;apply d;rw[<-hD x,<-hD y];have e:mN n D≠w:=by unfold mN;omega
       have g:=pp hS y (fun u=>if u=w then y ⟨w,f⟩ else val D x u) (fun i hi=>by by_cases b:i=w;subst b;simp;simp only[b,AB];rw[my D x i hi];exact o ⟨i,hi⟩ fun h=>b (Az Fin.val h)) (fun j q=>by obtain⟨ha,hb⟩:=ov a j q;have m:n+j≠w:=(by omega);simp only[m,ha,hb,AB];exact mS hS x j q) (mN n D) (by unfold mN;omega)
       simp only[e,AB] at g;exact g.symm
     . obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have q:j<D.length:=(by omega);have t:=nI n j D q
       obtain⟨D',h1,h2,h3⟩:=ih (D.length-1) (by omega) (ny n j D) t (ph hS j q a) (fun h=>by rw[h] at t;simp at t;omega) (fun x=>by rw[show mN n (ny n j D)=n+(D.length-1)-1 by unfold mN;rw[t],rp hS j q a x _ (by omega),show mM (n+j) (n+(D.length-1)-1)=mN n D by unfold mM mN;split_ifs<;>omega];exact hD x)
       exact⟨D',h1,by omega,h3⟩
lemma nV {n:Nat}(c:(F n->Y)->Y)(a:∀ i:F n,∃ x y:F n->Y,(∀ k,k≠i->x k=y k)/\c x≠c y)(D:N)(d:R n D)(b:D≠[])(e:∀ x:F n->Y,val D x (mN n D)=c x):∃ D':N,m7 n D'/\D'.length<=D.length/\∀ x:F n->Y,val D' x (mN n D')=c x:=r8 c a D.length D rfl d b e
lemma oU {n:Nat}(f:Circuit)(a:Monotone2 f)(d:∀ b:Y,∃ x:F n->Y,f.eval (Da x)≠b)(e:∀ i:F n,∃ x:F n->Y,f.eval (Da x)≠x i)(c:∀ i:F n,∃ x y:F n->Y,(∀ k,k≠i->x k=y k)/\f.eval (Da x)≠f.eval (Da y)):∃ D:N,m7 n D/\D.length<=f.size/\∀ x:F n->Y,val D x (mN n D)=f.eval (Da x):=by
 rcases o1 (n:=n) f a with
  ⟨b,r⟩|⟨i,q⟩|⟨D,p,h,j,o⟩
 . have⟨x,g⟩:=d b;exact Qa (r x) g
 . have⟨x,g⟩:=e i;exact Qa (q x) g
 . have⟨D',l,s,m⟩:=nV (fun x=>f.eval (Da x)) c D p h o;exact⟨D',l,by omega,m⟩
section SurplusFlow
variable {n:Nat} {D:N}
lemma n2 {w:Nat}:w∈nc n D↔w+1 < n+D.length:=by unfold nc;rw[Ac];omega
lemma mq (j:Nat):E D (j,J)=nX D j:=by simp[E]
lemma mx (j:Nat):E D (j,H)=nL D j:=by simp[E]
lemma n5 (b:R n D)(w:Nat)(h:n+D.length<=w+1):K D w=0:=by unfold K mP;rw[BF,E4];intro j c;have a:=Ac.mp c;have:=b j a;omega
lemma nE (a:R n D){w:Nat}(h:1<=K D w):w+1<n+D.length:=by by_contra b;have:=n5 a w (by omega);omega
lemma nP (P:Nat×Y->Prop)[DecidablePred P]:((ps D).filter P).card=∑ j∈range D.length,((if P (j,J) then 1 else 0)+(if P (j,H) then 1 else 0)):=by rw[Bv,ps,sum_product];refine Bg rfl (fun j _=>?_);rw[Fintype.sum_bool,add_comm]
lemma qU:(ps D).card=2*D.length:=by simp[ps,card_product,Nat.mul_comm]
lemma rO (a:R n D)(e:Nat×Y)(b:e∈ps D):E D e+1<n+D.length:=by
 obtain⟨j,c⟩:=e;have d:j<D.length:=(by simpa[ps] using b)
 have:=a j d;cases c;. rw[mq];omega
 . rw[mx];omega
lemma qn (a:R n D)(w:Nat):K D w=((ps D).filter (fun e=>E D e=w)).card:=by rw[nP,K,mP,Bv];refine Bg rfl (fun j b=>?_);have:=(a j (Ac.mp b)).2.2;rw[mq,mx];split_ifs<;>omega
lemma og (c:R n D)(b:I Nat):∑ w∈b,K D w=((ps D).filter (fun e=>E D e∈b)).card:=by
 rw[card_eq_sum_card_fiberwise (f:=E D) (s:=(ps D).filter (fun e=>E D e∈b)) (t:=b) (fun e a=>mem_coe.mpr (O.mp (mem_coe.mp a)).2)];refine Bg rfl (fun w d=>?_);rw[qn c,Cm];congr 1;ext e;simp only[O];constructor;. rintro⟨a,rfl⟩;exact⟨a,d,rfl⟩
 . rintro⟨a,-,h⟩;exact⟨a,h⟩
lemma nQ {a:I Nat}(b:∀ w∈a,1<=K D w):mo D a+a.card=∑ w∈a,K D w:=by rw[mo,card_eq_sum_ones,<-Ec];exact Bg rfl (fun w c=>Nat.sub_add_cancel (b w c))
lemma pJ (h:m7 n D):me n D+n=D.length+1:=by
 have⟨c,f,a⟩:=h;have b:0<D.length:=BD.mpr a;have i:mo D (nc n D)+(nc n D).card=∑ w∈nc n D,K D w:=nQ (fun w g=>f w (n2.mp g));have k:∑ w∈nc n D,K D w=2*D.length:=by rw[og c,filter_true_of_mem,qU];intro e d;exact n2.mpr (rO c e d)
 have j:(nc n D).card=n+D.length-1:=card_range _;unfold me;omega
lemma nZ (n:Nat)(D:N):me n D=nh n D+oL n D:=by unfold me nh oL mo;exact(sum_filter_add_sum_filter_not _ _ _).symm
lemma o0 (n:Nat)(D:N):nh n D<=me n D:=by rw[nZ];omega
lemma pQ (h:m7 n D)(w:Nat)(l:w<n+D.length):D1 (fun a b=>b<n+D.length/\n<=b/\(nX D (b-n)=a\/nL D (b-n)=a)) w (mN n D):=by
 have⟨g,f,_⟩:=h;generalize hk:n+D.length-w=k;induction k using AI generalizing w with
 | _ k i=>
   by_cases d:w+1=n+D.length
   . have c:w=mN n D:=by unfold mN;omega
     rw[c]
   . obtain⟨j,e⟩:=Bc.mp (f w (by omega));simp only[mP,O,Ac] at e;have m:=g j e.1;refine Dt (b:=n+j) ⟨by omega,by omega,?_⟩ (i (n+D.length-(n+j)) (by omega) (n+j) (by omega) rfl)
     simpa using e.2
lemma s9 {v:F n}{w:Nat}:v∈V n D w↔val D (nn v) w=H:=by simp[V]
lemma oQ (b:R n D)(x y:F n->Y)(a:∀ i,x i=H->y i=H)(w:Nat):val D x w=H->val D y w=H:=by
 induction w using AI with
 | _ w d=>
   by_cases e:w<n;. rw[my D x w e,my D y w e];exact a _
   . by_cases k:w<n+D.length
     . obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have c:j<D.length:=(by omega)
       obtain⟨f,g,-⟩:=b j c;rw[mS b x j c,mS b y j c];have h:=d _ f;have l:=d _ g;cases oi D j<;>
        simp only[gop_true,gop_false,X,Ai]<;>tauto
     . rw[os D x w (by omega)];simp
lemma nF (D:N)(i:F n):V n D i.val={i}:=by ext v;rw[s9,my D (nn v) i.val i.isLt];simp[nn,eq_comm]
lemma rz (D:N)(w:Nat)(h:n+D.length<=w):V n D w=∅:=by ext v;simp[s9,os D (nn v) w h]
lemma od (b:R n D)(j:Nat)(a:j<D.length):V n D (n+j)=if oi D j=H then V n D (nX D j)∩V n D (nL D j) else V n D (nX D j)∪V n D (nL D j):=by ext v;rw[s9,mS b _ j a];cases oi D j<;>simp[s9]
lemma qT (h:m7 n D)(f:I Nat)(k:f⊆nc n D)(b:∀ j,j<D.length->n+j∈f->nX D j∈f\/nL D j∈f):(mt n D f).card+(mI n D f).card=(p6 n f).card+mo D f:=by
 obtain⟨m,l,-⟩:=h;have a:∀ w∈f,w+1<n+D.length:=fun w g=>n2.mp (k g);have p:mo D f+f.card=((ps D).filter (fun e=>E D e∈f)).card:=(by rw[<-og m,nQ (fun w g=>l w (a w g))])
 have o:=BB (s:=(ps D).filter (fun e=>E D e∈f)) (fun e:Nat×Y=>n+e.1∈f)
 rw[Cm,Cm] at o;have q:((ps D).filter (fun e=>E D e∈f/\n+e.1∈f)).card = ((range D.length).filter (fun j=>n+j∈f)).card+(mI n D f).card:=by
  rw[nP,mI,Bv,Bv,<-Ec];refine Bg rfl (fun j i=>?_);have:=b j (Ac.mp i);rw[mq,mx];by_cases d:n+j∈f<;>by_cases r:nX D j∈f<;>by_cases v:nL D j∈f<;>
   simp_all
 have t:f.card=(p6 n f).card + ((range D.length).filter (fun j=>n+j∈f)).card:=by
  rw[<-BB (s:=f) (fun w=>w<n),p6];congr 1;have c:f.filter (fun w=>¬ w<n) = ((range D.length).filter (fun j=>n+j∈f)).image (fun j=>n+j):=by
   ext w;simp only[O,A7,Ac];constructor;. rintro⟨g,u⟩;have:=a w g;exact⟨w-n,⟨by omega,by rwa[Nat.add_sub_cancel' (by omega)]⟩,by omega⟩
   . rintro⟨j,⟨-,i⟩,rfl⟩;exact⟨i,by omega⟩
  rw[c,Au _ (add_right_injective n)]
 unfold mt;omega
lemma q0 (T:Sn n)(a:V n D (mN n D)∩T=∅):S n D T⊆nc n D:=by
 intro w hw;simp only[S,O,Ac] at hw;rw[n2];by_contra c;have b:w=mN n D:=by unfold mN;omega
 rw[b,a] at hw;exact AS hw.2
lemma p7 (D:N)(T:Sn n):(p6 n (S n D T)).card=T.card:=by
 have a:p6 n (S n D T)=T.image (fun v:F n=>v.val):=by
  ext w;simp only[p6,S,O,Ac,A7];constructor;. rintro⟨⟨-,v,b⟩,hw⟩;have c:V n D w={⟨w,hw⟩}:=nF D ⟨w,hw⟩;rw[c,A3,A5] at b;exact⟨v,b.2,by rw[b.1]⟩
  . rintro⟨v,b,rfl⟩;refine⟨⟨by have:=v.isLt;omega,v,?_⟩,v.isLt⟩;rw[nF];simp[b]
 rw[a,Au _ Fin.val_injective]
lemma nm (h:m7 n D)(T:Sn n)(a:V n D (mN n D)∩T=∅):(mt n D (S n D T)).card+(mI n D (S n D T)).card=T.card+mo D (S n D T):=by
 rw[<-p7 D T];refine qT h _ (q0 T a) (fun j d e=>?_);have⟨f,g,_⟩:=h.1 j d;simp only[S,O,Ac] at e ⊢;obtain⟨v,b⟩:=e.2;rw[A3,od h.1 j d] at b;split_ifs at b with ht;. rw[A3] at b;exact D5 ⟨by omega,v,A3.mpr ⟨b.1.1,b.2⟩⟩
 . rw[AA] at b;rcases b.1 with c|c
   . exact D5 ⟨by omega,v,A3.mpr ⟨c,b.2⟩⟩
   . exact D6 ⟨by omega,v,A3.mpr ⟨c,b.2⟩⟩
lemma se {u:Σ _:Nat,Nat}:u∈pz n D↔u.1∈nc n D/\u.2+1 < K D u.1:=by rw[pz,mem_sigma,Ac];constructor<;>rintro⟨a,b⟩<;>exact⟨a,by omega⟩
lemma nK (n:Nat)(D:N)(p:Nat->Prop)[DecidablePred p]:((pz n D).filter (fun u=>p u.1)).card=mo D ((nc n D).filter p):=by
 have a:(pz n D).filter (fun u=>p u.1) = ((nc n D).filter p).sigma (fun w=>range (K D w-1)):=by ext u;simp only[pz,O,mem_sigma];tauto
 rw[a,card_sigma,mo];simp
lemma oM (n:Nat)(D:N):(np n D).card=nh n D:=by unfold np nh;exact nK n D (fun w=>(V n D w).Nonempty)
lemma sd {v:F n}:v∈mb n D↔∃ w,2<=K D w/\v∈V n D w:=by
 simp only[mb,qN,C6,O,Ac];constructor;. rintro⟨w,⟨-,b⟩,a⟩;exact⟨w,b,a⟩
 . rintro⟨w,b,a⟩;refine⟨w,⟨?_,b⟩,a⟩;by_contra c;rw[rz D w (by omega)] at a;exact Bd v a
lemma sc {v:F n}:v∈U n D↔∀ w,v∈V n D w->K D w<=1:=by
 rw[U,Am,sd];constructor;. rintro⟨-,h⟩ w a;by_contra c;exact h ⟨w,by omega,a⟩
 . intro h;refine⟨AC v,?_⟩;rintro⟨w,a,b⟩;have:=h w b;omega
lemma n4 {v:F n}{T:Sn n}:(({v}:Sn n)∩T).Nonempty↔v∈T:=by
 constructor;. rintro⟨u,a⟩;rw[A3,A5] at a;exact a.1▸a.2
 . intro h;exact⟨v,A3.mpr ⟨Ao v,h⟩⟩
lemma oB (b:F n->Nat)(c:mw n D b):Eb (fun v=>(⟨b v,0⟩:Σ _:Nat,Nat)) (mb n D:Set (F n)):=by intro v hv v2 hv2 he;have a:b v=b v2:=Az Sigma.fst he;have d:=(c v hv).2;rw[a,(c v2 hv2).2] at d;exact(C7 d).symm
lemma nM (a:R n D)(b:F n->Nat)(c:mw n D b):mF n D b⊆np n D:=by
 intro u hu;obtain⟨v,e,rfl⟩:=A7.mp hu;obtain⟨g,f⟩:=c v e;have d:1<=K D (b v):=(by omega);rw[np,O,se];refine⟨⟨n2.mpr (nE a d),?_⟩,?_⟩;. show 0+1<K D (b v);omega
 . show (V n D (b v)).Nonempty;rw[f];exact singleton_nonempty v
lemma pe (b:F n->Nat)(a:mw n D b):(mF n D b).card=(mb n D).card:=Bj (oB b a)
lemma pj (c:R n D)(b:F n->Nat)(a:mw n D b):(mb n D).card<=nh n D:=by rw[<-pe b a,<-oM];exact Aa (nM c b a)
lemma nH (c:R n D)(b:F n->Nat)(a:mw n D b):(mi n D b).card+(mb n D).card=nh n D:=by rw[<-pe b a,<-oM];exact BK (nM c b a)
lemma nR (j:R n D)(b:F n->Nat)(i:mw n D b)(T:Sn n):mo D (S n D T)=(T∩mb n D).card+((mi n D b).filter (fun u=>(V n D u.1∩T).Nonempty)).card:=by
 let P (u:Σ _:Nat,Nat):=(V n D u.1∩T).Nonempty;have k:mo D (S n D T)=((pz n D).filter P).card:=by
  rw[nK n D (fun w=>(V n D w∩T).Nonempty)];symm;refine sum_subset (fun w g=>?_) (fun w g c=>?_);. rw[O] at g;have:=n2.mp g.1;exact O.mpr ⟨Ac.mpr (by omega),g.2⟩
  . rw[S,O] at g;have e:w∉nc n D:=fun l=>c (O.mpr ⟨l,g.2⟩);rw[n2] at e;simp[n5 j w (by omega)]
 have o:(pz n D).filter P=(mF n D b).filter P∪(mi n D b).filter P:=by ext u;have a:=nM j b i;simp only[mi,np,AA,O,Am];exact⟨fun f=>if hr:u∈mF n D b then D5 ⟨hr,f.2⟩ else D6 ⟨⟨⟨f.1,f.2.mono B9⟩,hr⟩,f.2⟩,fun f=>f.elim (fun h=>⟨(O.mp (a h.1)).1,h.2⟩) (fun h=>⟨h.1.1.1,h.2⟩)⟩
 have m:(mF n D b).filter P=(T∩mb n D).image fun v=>(⟨b v,0⟩:Σ _:Nat,Nat):=by rw[mF,filter_image];congr 1;ext v;simp only[O,A3,P];exact⟨fun⟨hv,d⟩=>⟨by rwa[(i v hv).2,n4] at d,hv⟩,fun⟨hT,hv⟩=>⟨hv,by rwa[(i v hv).2,n4]⟩⟩
 rw[k,o,AJ (disjoint_filter_filter disjoint_sdiff:Disjoint ((mF n D b).filter P) ((mi n D b).filter P)),m,Bj ((oB b i).mono (coe_subset.mpr Bm))]
lemma pa (a:R n D)(b:F n->Nat)(c:mw n D b)(T:Sn n):mo D (S n D T)+(mb n D).card <=(T∩mb n D).card+nh n D:=by
 have d:=nR a b c T;have e:=nH a b c;have f:=Ck (mi n D b) (fun u=>(V n D u.1∩T).Nonempty)
 omega
end SurplusFlow
def mE {n:Nat}(a:D7 (F n))(w:Nat):Nat:=if h:w<n then(a ⟨w,h⟩).val else w
def mf {n:Nat}(a:D7 (F n))(D:N):N:=D.map (fun g=>(g.1,mE a g.2.1,mE a g.2.2))
lemma o9 {n:Nat}(a:D7 (F n)){w:Nat}(h:w<n):mE a w=(a ⟨w,h⟩).val:=by simp[mE,h]
lemma n6 {n:Nat}(a:D7 (F n)){w:Nat}(h:n<=w):mE a w=w:=by simp[mE,Ci.mpr h]
lemma mD {n:Nat}(a:D7 (F n)){m:Nat}(b:n<=m)(w:Nat):mE a w < m↔w < m:=by
 by_cases h:w<n;. rw[o9 a h];have:=(a ⟨w,h⟩).isLt;constructor<;>intro<;>omega
 . rw[n6 a (Ci.mp h)]
lemma nB {n:Nat}(a:D7 (F n))(w:Nat):mE a⁻¹ (mE a w)=w:=by
 by_cases h:w<n;. rw[o9 a h,o9 a⁻¹ (a ⟨w,h⟩).isLt];simp
 . rw[n6 a (Ci.mp h),n6 a⁻¹ (Ci.mp h)]
lemma nU' {n:Nat}(a:D7 (F n))(w:Nat):mE a (mE a⁻¹ w)=w:=by simpa using nB a⁻¹ w
lemma oj {n:Nat}(c:D7 (F n)){a b:Nat}:mE c a=mE c b↔a=b:=by
 refine⟨fun h=>?_,Az _⟩
 have:=Az (mE c⁻¹) h;rwa[nB,nB] at this
lemma ml {n:Nat}(a:D7 (F n))(D:N):(mf a D).length=D.length:=by simp[mf]
lemma ss {n:Nat}(b:D7 (F n))(D:N)(j:Nat)(a:j<D.length):oi (mf b D) j=oi D j:=by rw[rv _ j (by rw[ml];exact a),rv D j a];simp[mf]
lemma rq {n:Nat}(b:D7 (F n))(D:N)(j:Nat)(a:j<D.length):nX (mf b D) j=mE b (nX D j):=by rw[ro _ j (by rw[ml];exact a),ro D j a];simp[mf]
lemma rm {n:Nat}(b:D7 (F n))(D:N)(j:Nat)(a:j<D.length):nL (mf b D) j=mE b (nL D j):=by rw[rx _ j (by rw[ml];exact a),rx D j a];simp[mf]
lemma oX {n:Nat}(b:D7 (F n)){D:N}(c:R n D):R n (mf b D):=by intro j hj;rw[ml] at hj;obtain⟨d,e,a⟩:=c j hj;rw[rq b D j hj,rm b D j hj];exact⟨(mD b (Bu n j) _).mpr d,(mD b (Bu n j) _).mpr e,fun h=>a ((oj b).mp h)⟩
lemma pU {n:Nat}(a:D7 (F n)){D:N}(e:R n D)(x:F n->Y)(w:Nat):val (mf a D) x (mE a w)=val D (fun i=>x (a i)) w:=by
 by_cases b:w<n+D.length
 . refine(pp (oX a e) x (fun w'=>val D (fun i=>x (a i)) (mE a⁻¹ w')) ?_ ?_ (mE a w) ?_).trans ?_
   . intro i d;show val D (fun i=>x (a i)) (mE a⁻¹ i)=x ⟨i,d⟩;rw[o9 a⁻¹ d,my D _ _ (a⁻¹ ⟨i,d⟩).isLt];simp
   . intro j c;rw[ml] at c;show val D (fun i=>x (a i)) (mE a⁻¹ (n+j)) = rE (oi (mf a D) j) (val D (fun i=>x (a i)) (mE a⁻¹ (nX (mf a D) j))) (val D (fun i=>x (a i)) (mE a⁻¹ (nL (mf a D) j)))
     rw[n6 a⁻¹ (Bu n j),ss a D j c,rq a D j c,rm a D j c,nB,nB,mS e _ j c]
   . rw[ml];exact(mD a (Bu _ _) w).mpr b
   . show val D (fun i=>x (a i)) (mE a⁻¹ (mE a w))=_
     rw[nB]
 . have b':=Ci.mp b;rw[n6 a (le_trans (Bu _ _) b'),os _ _ _ (by rw[ml];exact b'),os _ _ _ b']
lemma nz {n:Nat}(a:D7 (F n))(D:N)(w:Nat):K (mf a D) (mE a w)=K D w:=by unfold K mP;rw[ml];congr 1;apply BG;intro j b;have b':=Ac.mp b;rw[rq a D j b',rm a D j b',oj,oj]
lemma qQ {n:Nat}(b:D7 (F n)){D:N}(d:sk n D):sk n (mf b D):=by
 rcases eq_or_ne D [] with rfl|c;. exact d
 . intro w' hw';rw[ml] at hw';have a:=BD.mpr c;rw[<-nU' b w',nz];apply d;by_cases h:w' < n
   . have:=(mD b⁻¹ le_rfl w').mpr h;omega
   . rw[n6 b⁻¹ (Ci.mp h)];exact hw'
lemma pl {n:Nat}(a:D7 (F n)){D:N}(h:m7 n D):m7 n (mf a D):=⟨oX a h.1,qQ a h.2.1,by simpa[mf] using h.2.2⟩
lemma r5 {n:Nat}(c:D7 (F n)){D:N}(d:R n D)(a:D≠[])(x:F n->Y):val (mf c D) x (mN n (mf c D))=val D (fun i=>x (c i)) (mN n D):=by
 have b:=BD.mpr a;have e:mN n (mf c D)=mE c (mN n D):=by rw[n6 c (by unfold mN;omega)];simp[mN,ml]
 rw[e,pU c d]
lemma qo {n:Nat}(a:D7 (F n))(v:F n):(fun i=>nn v (a i))=nn (a⁻¹ v):=by
 funext i;simp only[nn,decide_eq_decide];constructor;. intro h;rw[<-h];simp
 . intro h;rw[h];simp
lemma nS {n:Nat}(b:D7 (F n)){D:N}(c:R n D)(w:Nat):V n (mf b D) (mE b w)=(V n D w).image b:=by
 ext v;simp only[V,O,AC,true_and,A7];rw[pU b c,qo];constructor;. intro h;exact⟨b⁻¹ v,h,by simp⟩
 . rintro⟨a,d,rfl⟩;simpa using d
lemma qP {n:Nat}(b:D7 (F n)){m:Nat}(d:n<=m)(P:Nat->Prop)[DecidablePred P](g:Nat->Nat):∑ w∈(range m).filter (fun w=>P (mE b w)),g (mE b w)=∑ w∈(range m).filter P,g w:=by
 refine sum_nbij' (mE b) (mE b⁻¹) ?_ ?_ ?_ ?_ ?_;. intro a c;simp only[O,Ac] at c ⊢;exact⟨(mD b d a).mpr c.1,c.2⟩
 . intro a c;simp only[O,Ac] at c ⊢;exact⟨(mD b⁻¹ d a).mpr c.1,by rw[nU'];exact c.2⟩
 . intro a _;exact nB b a
 . intro a _;exact nU' b a
 . intro a _;rfl
lemma ns {n:Nat}(c:D7 (F n))(D:N)(P kq:Nat->Prop)[DecidablePred P][DecidablePred kq](a:∀ w,kq (mE c w)↔P w):mo (mf c D) ((nc n (mf c D)).filter kq)=mo D ((nc n D).filter P):=by
 rcases eq_or_ne D [] with rfl|d;. simp[mo,mf,K,mP]
 . have b:=BD.mpr d;have e:n<=n+D.length-1:=(by omega);unfold mo nc;rw[ml];exact(qP c e kq (fun w=>K (mf c D) w-1)).symm.trans (Bg (BG fun w _=>a w) fun w _=>by rw[nz])
lemma oG {n:Nat}(a:D7 (F n))(D:N):me n (mf a D)=me n D:=by
 simpa[me] using
  ns a D (fun _=>True) (fun _=>True) (fun _=>Iff.rfl)
lemma qF {n:Nat}(a:D7 (F n)){D:N}(b:R n D):nh n (mf a D)=nh n D:=ns a D _ _ (fun w=>by rw[nS a b];simp)
lemma qD {n:Nat}(a:D7 (F n)){D:N}(b:R n D):oL n (mf a D)=oL n D:=ns a D _ _ (fun w=>by rw[nS a b];simp)
lemma oC {n:Nat}(b:D7 (F n)){D:N}(f:R n D):mb n (mf b D)=(mb n D).image b:=by
 ext v;simp only[mb,C6,A7,qN,O,Ac];constructor;. rintro⟨w',⟨c',d⟩,hv⟩;obtain⟨w,rfl⟩:∃ w,w'=mE b w:=⟨mE b⁻¹ w',(nU' b w').symm⟩;rw[nS b f,A7] at hv;obtain⟨a,e,rfl⟩:=hv;rw[nz] at d;rw[ml,mD b (Bu _ _)] at c';exact⟨a,⟨w,⟨c',d⟩,e⟩,rfl⟩
 . rintro⟨a,⟨w,⟨c,d⟩,e⟩,rfl⟩;refine⟨mE b w,⟨?_,?_⟩,?_⟩
   . rw[ml];exact(mD b (Bu _ _) w).mpr c
   . rw[nz];exact d
   . rw[nS b f];exact mem_image_of_mem _ e
lemma px {n:Nat}(c:D7 (F n)){D:N}(d:R n D):U n (mf c D)=(U n D).image c:=by
 ext v;simp only[U,oC c d,Am,AC,true_and,A7];constructor;. intro h;exact⟨c⁻¹ v,fun e=>h ⟨c⁻¹ v,e,by simp⟩,by simp⟩
 . rintro⟨a,f,rfl⟩ ⟨b,hb,hab⟩;exact f (c.injective hab▸hb)
def qb:Z (Nat×Nat):=[(0,7),(0,11),(1,6),(1,10),(1,11),(2,9),(2,10),(3,8),(3,9),(3,11),(4,7),(4,8),(4,10),(5,6),(5,7),(5,9)]
def G12Edge (x:B->Y):Prop:=∃ u v:B,(u.val,v.val)∈qb/\x u=H/\x v=H
abbrev oF (u v:B):Prop:=(u.val,v.val)∈qb\/(v.val,u.val)∈qb
def ma (u v:B):Y:=(([2176,3136,1536,2816,1408,704,34,49,24,44,22,11]:Z Nat).getD u.val 0).testBit v.val
lemma mj:∀ u v:B,ma u v=H↔oF u v:=by decide +kernel
lemma sb {u v:B}:ma u v=J↔¬ oF u v:=by rw[<-mj,Ch]
lemma oS {u v:B}:oF u v->oF v u:=Or.symm
lemma pm (u:B):¬ oF u u:=by revert u;decide +kernel
lemma mV (x:B->Y):G12Edge x↔∃ u v:B,oF u v/\x u=H/\x v=H:=by
 constructor;. rintro⟨u,v,h,a,b⟩;exact⟨u,v,D5 h,a,b⟩
 . rintro⟨u,v,h|h,a,b⟩
   . exact⟨u,v,h,a,b⟩
   . exact⟨v,u,h,b,a⟩
def mH (v:B):S2:=univ.filter (fun u=>ma v u=H)
def m5 (i:B):S2:=univ.filter (fun a=>oF i a)
lemma n7 (v:B):m5 v=mH v:=BG (fun u _=>(mj v u).symm)
lemma s8 {i a:B}:a∈m5 i↔oF i a:=by simp[m5]
lemma mQ (v:B):(m5 v).card=2\/(m5 v).card=3:=by rw[n7];revert v;decide +kernel
lemma pF (u v:B)(h:u≠v):(univ.filter (fun z=>oF u z/\oF v z)).card<=1:=by rw[BG (fun z _=>and_congr (mj u z).symm (mj v z).symm)];revert u v;decide +kernel
lemma rc:∀ v w:B,v≠w->∃ z,ma v z=H/\ma w z=J:=by decide +kernel
lemma nN (v w:B)(h:v≠w):∃ z,oF v z/\¬ oF w z:=by obtain⟨z,b,c⟩:=rc v w h;refine⟨z,(mj v z).mp b,fun a=>?_⟩;rw[<-mj,c] at a;exact B8 a
lemma qj {i j:B}(h:m5 i=m5 j):i=j:=by by_contra c;obtain⟨z,a,b⟩:=nN i j c;have:z∈m5 j:=h▸(by simp[m5,a]);simp[m5,b] at this
def p4 (a:S2):Prop:=∀ u v:B,oF u v->u∈a\/v∈a
def nv (a:S2):Prop:=∀ u∈a,∀ v∈a,¬ oF u v
lemma oE (c:S2):nv c↔p4 (univ \ c):=by
 constructor;. intro h u v a;by_contra b;simp only[Am,AC,true_and,not_or,not_not] at b;exact h u b.1 v b.2 a
 . intro h u e v f a;rcases h u v a with d|d<;>simp[e,f] at d
def ni (v:B):B:=Fin.ofNat 12 (([7,11,10,9,8,6,5,0,4,3,2,1]:Z Nat).getD v.val 0)
lemma qH:∀ v:B,ma v (ni v)=H/\ni (ni v)=v:=by decide +kernel
lemma q8 (v:B):oF v (ni v)/\ni (ni v)=v:=⟨(mj _ _).mp (qH v).1,(qH v).2⟩
lemma pE (b:S2)(h:p4 b):6<=b.card:=by
 have a:(univ:S2)⊆b∪b.image ni:=by
  intro v _;rcases h v (ni v) (q8 v).1 with c|c;. exact mem_union_left _ c
  . exact mem_union_right _ (A7.mpr ⟨_,c,(q8 v).2⟩)
 have d:=Aa a;have e:=Co b (b.image ni);have g:=card_image_le (s:=b) (f:=ni);simp only[card_univ,Fintype.card_fin] at d;omega
def of (a:D7 (B)):Prop:=∀ u v:B,oF (a u) (a v)↔oF u v
lemma rh {a:D7 (B)}(h:∀ u v:B,ma (a u) (a v)=ma u v):of a:=fun u v=>by
 rw[<-mj,<-mj u v,h]
lemma rC:of 1:=fun _ _=>Iff.rfl
lemma rN {sg τ:D7 (B)}(a:of sg)(hτ:of τ):of (sg*τ):=fun u v=>(a (τ u) (τ v)).trans (hτ u v)
lemma rg (a:D7 (B))(b:of a)(x:B->Y):G12Edge (fun i=>x (a i))↔G12Edge x:=by
 rw[mV,mV];constructor;. rintro⟨u,v,h,c,d⟩;exact⟨a u,a v,(b u v).mpr h,c,d⟩
 . rintro⟨u,v,h,c,d⟩;refine⟨a.symm u,a.symm v,?_,by simpa using c,by simpa using d⟩;rw[<-b,Ed,Ed];exact h
lemma pY {e:D7 (B)}(c:of e){d:S2}(f:nv d):nv (d.image e):=by intro u hu v hv;obtain⟨a,g,rfl⟩:=A7.mp hu;obtain⟨b,h,rfl⟩:=A7.mp hv;rw[c a b];exact f a g b h
def rK (l:Z Nat)(v:B):B:=Fin.ofNat 12 (l.getD v.val 0)
def mY:Z (S2):=[{0,1,2,3,4,5},{0,1,2,3,4},{0,1,2,5,8},{0,1,3,4,5},{0,1,2,3},{0,1,2,5},{0,1,2,8},{0,1,3,4},{0,1,4,9},{0,1,5,8},{0,1,8,9},{0,2,6,8},{1,3,4,5},{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,1,8},{0,1,9},{0,2,6},{0,9,10},{1,3,4},{1,3,7},{0,1},{0,2},{0,6},{0,9},{1,3},{1,5},{1,7},{0},{1}]
def nC (n:Fin 33):S2:=((∅:S2)::mY).getD n.val ∅
lemma oc {b:S2}(h:b∈mY):∃ n:Fin 33,n≠0/\nC n=b:=by obtain⟨i,a,rfl⟩:=List.mem_iff_getElem.mp h;have a':i<32:=a;refine⟨⟨i+1,by omega⟩,by simp[Fin.ext_iff],?_⟩;show ((∅:S2)::mY).getD (i+1) ∅=mY[i];rw[DK];exact List.getD_eq_getElem _ _ a
abbrev rU (a:S2):Prop:=∀ u∈a,∀ v∈a,ma u v=J
lemma si {a:S2}:rU a↔nv a:=by
 refine forall₂_congr fun u _=>forall₂_congr fun v _=>?_
 rw[<-mj,Ch]
def hc_tab:Z (Z Nat):=[[0,1,2,3,4,5,6,7,8,9,10,11],[0,3,2,1,5,4,8,7,6,10,9,11],[0,4,2,5,1,3,8,11,6,9,10,7],[0,5,2,4,3,1,6,11,8,10,9,7],[2,1,0,4,3,5,6,9,8,7,11,10],[2,3,0,5,1,4,8,10,6,7,11,9],[2,4,0,1,5,3,8,9,6,11,7,10],[2,5,0,3,4,1,6,10,8,11,7,9],[6,7,8,9,10,11,0,1,2,3,4,5],[6,9,8,7,11,10,2,1,0,4,3,5],[6,10,8,11,7,9,2,5,0,3,4,1],[6,11,8,10,9,7,0,5,2,4,3,1],[8,7,6,10,9,11,0,3,2,1,5,4],[8,9,6,11,7,10,2,4,0,1,5,3],[8,10,6,7,11,9,2,3,0,5,1,4],[8,11,6,9,10,7,0,4,2,5,1,3]]
def pT (k:Fin 16):B->B:=rK (hc_tab.getD k.val [])
lemma rI:∀ k:Fin 16,∀ a b:B,pT k a=pT k b->a=b:=by decide +kernel
lemma rJ:∀ k:Fin 16,∀ u v:B,ma (pT k u) (pT k v)=ma u v:=by decide +kernel
lemma rH (k:Fin 16):∃ τ:D7 (B),of τ/\⇑τ=pT k:=by have c:Function.Injective (pT k):=fun a b h=>rI k a b h;exact⟨Equiv.ofBijective (pT k) ⟨c,Finite.injective_iff_surjective.mp c⟩,rh fun u v=>rJ k u v,rfl⟩
def hc_witTab:Z (Z Nat):=[[0,0,4,1,2,3,8,8,9,12,14,10],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,1,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,4,0,0,0,0,0,0,0,0,0],[0,0,0,0,4,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0],[0,0,4,0,0,2,0,0,0,0,0,0],[0,0,0,1,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,12,0,13,0,0,0],[0,0,4,0,0,0,0,0,0,0,0,0],[0,0,4,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,2,3,0,0,1,0,0,0],[0,0,0,1,2,0,0,0,8,12,15,0],[0,0,0,0,2,0,12,0,13,0,0,0],[0,0,4,0,0,1,0,0,0,0,0,0],[0,0,4,1,2,0,0,0,9,0,0,0],[0,0,4,0,0,0,0,0,9,8,0,0],[0,0,0,1,2,3,0,0,1,0,1,0],[0,0,4,0,4,0,0,0,9,4,0,0]]
def rT (n:Fin 33)(w:B):Fin 16:=Fin.ofNat 16 ((hc_witTab.getD n.val []).getD w.val 0)
lemma rW:∀ n:Fin 33,∀ w:B,w∉nC n->rU (insert w (nC n))->(insert w (nC n)).image (pT (rT n w))∈mY:=by decide +kernel
lemma so (a:S2)(hR:a=∅\/a∈mY)(w:B)(b:w∉a)(c:nv (insert w a)):∃ τ:D7 (B),of τ/\(insert w a).image τ∈mY:=by
 obtain⟨n,rfl⟩:∃ n:Fin 33,nC n=a:=by
  rcases hR with rfl|hR;. exact⟨0,rfl⟩
  . have⟨n,_,h⟩:=oc hR;exact⟨n,h⟩
 have⟨τ,hτ,d⟩:=rH (rT n w);exact⟨τ,hτ,by rw[d];exact rW n w b (si.mpr c)⟩
lemma rR (d:S2):nv d->d=∅\/∃ sg:D7 (B),of sg/\d.image sg∈mY:=by
 induction d using Finset.induction_on with
 | empty=>intro _;exact D5 rfl
 | insert v e k m=>
   intro hI;have l:nv e:=fun u i w n=>
    hI u (A2 i) w (A2 n)
   obtain⟨sg,a,b,p,c⟩:∃ sg:D7 (B),of sg/\∃ b,(b=∅\/b∈mY)/\e.image sg=b:=by
    rcases m l with h|⟨sg,a,f⟩;. exact⟨1,rC,∅,D5 rfl,by simp[h]⟩
    . exact⟨sg,a,_,D6 f,rfl⟩
   have g:(insert v e).image sg=insert (sg v) b:=(by rw[Ax,c]);have o:sg v∉b:=by rw[<-c];simpa using k
   have j:nv (insert (sg v) b):=by rw[<-g];exact pY a hI
   obtain⟨τ,hτ,f⟩:=so b p (sg v) o j;refine D6 ⟨τ*sg,rN hτ a,?_⟩;rw[Equiv.Perm.coe_mul,<-image_image,g];exact f
lemma oK (b:S2)(c:nv b)(a:b.Nonempty):∃ sg:D7 (B),of sg/\b.image sg∈mY:=by
 rcases rR b c with h|h;. exact Qa h a.ne_empty
 . exact h
lemma qG:¬ G12Edge (fun _=>J):=by rintro⟨u,v,-,h,-⟩;exact B8 h
lemma o2 (v:B):¬ G12Edge (fun i=>decide (i=v)):=by rw[mV];rintro⟨a,b,c,d,e⟩;simp only[A6] at d e;subst d;subst e;exact pm _ c
lemma r4 {u v:B}(h:oF u v):G12Edge (fun i=>decide (i=u)||decide (i=v)):=(mV _).mpr ⟨u,v,h,by simp,by simp⟩
lemma qC (i:B):∃ x y:B->Y,(∀ k,k≠i->x k=y k)/\¬ G12Edge x/\G12Edge y:=by
 refine⟨fun k=>decide (k=ni i),fun k=>decide (k=i)||decide (k=ni i),?_,o2 _,r4 (q8 i).1⟩
 intro k hk;simp[hk]
def mB (D:N):Prop:=∀ x:B->Y,val D x (mN 12 D)=H↔G12Edge x
lemma qw (j:Circuit)(a:Monotone2 j)(g:∀ x:B->Y,j.eval (Da x)=H↔G12Edge x):∃ D:N,m7 12 D/\D.length<=j.size/\mB D:=by
 have f:oF (0:B) 7:=(by decide)
 have⟨D,o,d,c⟩:=oU (n:=12) j a (by
  intro b;cases b;. exact⟨_,by rw[Ne,B0];exact(g _).2 (r4 f)⟩
  . exact⟨fun _=>J,fun h=>qG ((g _).1 h)⟩)
  (by
   intro i;refine⟨fun k=>decide (k=i),fun h=>o2 i ((g _).1 ?_)⟩;rw[h];simp)
  (by
   intro i;obtain⟨x,y,e,m,l⟩:=qC i;refine⟨x,y,e,fun h=>m ((g x).1 ?_)⟩;rw[h];exact(g y).2 l)
 exact⟨D,o,d,fun x=>by rw[c x];exact g x⟩
lemma qS {D:N}(a:mB D):V 12 D (mN 12 D)=∅:=CF.2
 (fun v b=>o2 v ((a _).1 (s9.1 b)))
lemma ri (a:D7 (B))(b:of a){D:N}(h:m7 12 D)(c:mB D):m7 12 (mf a D)/\mB (mf a D)/\(mf a D).length=D.length/\me 12 (mf a D)=me 12 D/\nh 12 (mf a D)=nh 12 D/\oL 12 (mf a D)=oL 12 D/\mb 12 (mf a D)=(mb 12 D).image a/\U 12 (mf a D)=(U 12 D).image a:=by
 refine⟨pl a h,fun x=>?_,ml a D,oG a D,qF a h.1,qD a h.1,oC a h.1,px a h.1⟩
 rw[r5 a h.1 h.2.2 x,c];exact rg a b x
lemma nj (n:Nat)(D:N):(U n D).card+(mb n D).card=n:=by have h:=BK (subset_univ (mb n D));rw[card_univ,Fintype.card_fin] at h;exact h
lemma pd (D:N):p4 (mb 12 D)↔nv (U 12 D):=by have h:univ \ U 12 D=mb 12 D:=(by simp[U]);rw[oE,h]
lemma rQ {D:N}(h:m7 12 D)(f:mB D)(e:nv (U 12 D))(a:(U 12 D).Nonempty):∃ D':N,m7 12 D'/\mB D'/\D'.length=D.length/\me 12 D'=me 12 D/\nh 12 D'=nh 12 D/\oL 12 D'=oL 12 D/\(mb 12 D').card=(mb 12 D).card/\U 12 D'∈mY:=by
 obtain⟨c,d,b⟩:=oK _ e a;obtain⟨g,m,i,k,o,j,n,l⟩:=ri c d h f;refine⟨mf c D,g,m,i,k,o,j,?_,?_⟩;. rw[n,Au _ c.injective]
 . rw[l];exact b
lemma qi {D:N}(h:m7 12 D)(a:D.length<=20):me 12 D+11=D.length/\me 12 D<=9:=by have:=pJ h;omega
lemma qR {D:N}(h:m7 12 D)(c:D.length<=20)(b:B->Nat)(d:mw 12 D b)(a:p4 (mb 12 D)):6<=(mb 12 D).card/\(mb 12 D).card<=nh 12 D/\nh 12 D<=me 12 D/\me 12 D<=9:=⟨pE _ a,pj h.1 b d,o0 12 D,(qi h c).2⟩
lemma o6 {D:N}(h:m7 12 D)(c:D.length<=20)(b:B->Nat)(d:mw 12 D b)(a:p4 (mb 12 D)):(U 12 D).Nonempty/\3<=(U 12 D).card/\(U 12 D).card<=6:=by obtain⟨f,i,j,g⟩:=qR h c b d a;have e:=nj 12 D;exact⟨Bc.1 (by omega),by omega,by omega⟩
def mW {n:Nat}(a:F n->F n->Prop)(x:F n->Y):Prop:=∃ u v:F n,a u v/\x u=H/\x v=H
def mm (n:Nat)(zg:F n->F n->Prop)(D:N):Prop:=∀ x:F n->Y,val D x (mN n D)=H↔mW zg x
def mA {n:Nat}(zg:F n->F n->Prop):Prop:=(∀ u v,zg u v->zg v u)/\(∀ u,¬ zg u u)/\(∀ v w,v≠w->∃ z,zg v z/\¬ zg w z)/\(∀ u v,∃ a,zg u a/\a≠v)
def mv (n:Nat)(D:N)(a b:Nat):Prop:=b<n+D.length/\n<=b/\(nX D (b-n)=a\/nL D (b-n)=a)
def mO {n:Nat}(u z:F n):F n->Y:=fun i=>decide (i=u)||decide (i=z)
def mh {n:Nat}(v:F n)(x:F n->Y):F n->Y:=fun i=>decide (i=v)||x i
def mg {n:Nat}(A:Sn n):F n->Y:=fun i=>decide (i∈A)
lemma ok {α:Type}{r p:α->α->Prop}(h:∀ a b,r a b->p a b){a b:α}(c:D1 r a b):D1 p a b:=by induction c with|refl=>exact DD | tail _ d e=>exact Dp e (h _ _ d)
section SemCore
variable {n:Nat} {zg:F n->F n->Prop} {D:N}
lemma ng (v:F n)(x:F n->Y):∀ k,k≠v->x k=mh v x k:=by intro k hk;simp[mh,hk]
lemma na (v:F n)(x:F n->Y):mh v x v=H:=by simp[mh]
lemma pq (v:F n)(x:F n->Y):∀ i,x i=H->mh v x i=H:=by intro i hi;simp[mh,hi]
lemma qB {x:F n->Y}{u:F n}(a:x u=H):∀ i,nn u i=H->x i=H:=by intro i hi;simp only[nn,A6] at hi;rw[hi];exact a
lemma mU (b:R n D){u:F n}{w:Nat}(a:u∈V n D w){x:F n->Y}(c:x u=H):val D x w=H:=oQ b (nn u) x (qB c) w (s9.mp a)
lemma nq {v:F n}{w:Nat}(a:v∈V n D w):w<n+D.length:=by by_contra b;rw[rz D w (by omega)] at a;exact Bd v a
lemma mK (c:R n D){j:Nat}(a:j<D.length)(b:oi D j=H):V n D (n+j)=V n D (nX D j)∩V n D (nL D j):=by rw[od c j a];simp[b]
lemma no (c:R n D){j:Nat}(a:j<D.length)(b:oi D j=J):V n D (n+j)=V n D (nX D j)∪V n D (nL D j):=by rw[od c j a];simp[b]
lemma n8 (c:R n D){j:Nat}(a:j<D.length)(b:oi D j=H)(s:Y):V n D (n+j)⊆V n D (E D (j,s)):=by
 rw[mK c a b];cases s;. rw[mq];exact B9
 . rw[mx];exact Bm
lemma o5 (b:R n D){j:Nat}(a:j<D.length)(s:Y):E D (j,s)<n+j:=by
 have⟨c,d,_⟩:=b j a;cases s;. rw[mq];exact c
 . rw[mx];exact d
lemma rl (c:R n D){j:Nat}(b:j<D.length)(s:Y):E D (j,s)≠E D (j,!s):=by
 have⟨_,_,a⟩:=c j b;cases s;. simpa[E] using a
 . simpa[E] using a.symm
lemma nw {j:Nat}(a:j<D.length)(s:Y):mv n D (E D (j,s)) (n+j):=by
 refine⟨by omega,by omega,?_⟩
 rw[Bt];cases s;. exact D5 (mq j).symm
 . exact D6 (mx j).symm
lemma sh {a b:Nat}:mv n D a b↔∃ j s,j < D.length/\b=n+j/\E D (j,s)=a:=by
 constructor
 . rintro⟨e,f,c|c⟩
   . exact⟨b-n,J,by omega,by omega,by rw[mq];exact c⟩
   . exact⟨b-n,H,by omega,by omega,by rw[mx];exact c⟩
 . rintro⟨j,s,d,rfl,rfl⟩;refine⟨by omega,by omega,?_⟩;rw[Bt];cases s
   . exact D5 (mq j).symm
   . exact D6 (mx j).symm
lemma oO (c:R n D){a b:Nat}(h:mv n D a b):a<b:=by obtain⟨d,e,f⟩:=h;have:=c (b-n) (by omega);omega
lemma nO {a c:Nat}(h:mv n D a c):c-n∈mP D a:=by unfold mP;rw[O,Ac];exact⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma oz {a c:Nat}(h:mv n D a c):1<=K D a:=Bc.mpr ⟨_,nO h⟩
lemma mT {a c c':Nat}(b:mv n D a c)(d:mv n D a c')(e:K D a=1):c=c':=by have h:=nO b;have f:=nO d;have⟨r,g⟩:=CB.mp (show (mP D a).card=1 from e);rw[g,A5] at h f;have:=b.2.1;have:=d.2.1;omega
lemma nG (g:R n D)(x y:F n->Y)(v:F n)(d:∀ k,k≠v->x k=y k)(w:Nat)(f:val D x w≠val D y w):D1 (fun a b=>mv n D a b/\val D x b≠val D y b) v.val w:=by
 induction w using AI with
 | _ w o=>
   by_cases i:w<n
   . rw[my D x w i,my D y w i] at f;have e:(⟨w,i⟩:F n)=v:=by by_contra q;exact f (d _ q)
     rw[<-e]
   . by_cases c:w<n+D.length
     . obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have h:j<D.length:=(by omega)
       have⟨r,s,_⟩:=g j h;have p:=f;rw[mS g x j h,mS g y j h] at p;by_cases m:val D x (nX D j)=val D y (nX D j)
       . have l:val D x (nL D j)≠val D y (nL D j):=by intro l;apply p;rw[m,l]
         exact Dp (o _ s l) ⟨⟨c,by omega,D6 (by rw[Bt])⟩,f⟩
       . exact Dp (o _ r m) ⟨⟨c,by omega,D5 (by rw[Bt])⟩,f⟩
     . exfalso;apply f;rw[os D x w (by omega),os D y w (by omega)]
def pv (n:Nat)(D:N)(b v:Nat):Prop:=b=v\/¬ D1 (fun a c=>mv n D a c/\c≠b) v (mN n D)
lemma q6 (l:R n D)(x y:F n->Y)(v:F n)(e:∀ k,k≠v->x k=y k)(b:Nat)(d:pv n D b v.val)(i:val D x b=val D y b):val D x (mN n D)=val D y (mN n D):=by
 by_contra g;rcases d with rfl|d
 . rw[my D x _ v.isLt,my D y _ v.isLt] at i;have f:x=y:=by
    funext k;by_cases j:k=v;. rw[j];exact i
    . exact e k j
   exact g (by rw[f])
 . exact d (ok (fun a c h=>⟨h.1,fun m=>h.2 (by rw[m];exact i)⟩) (nG l x y v e _ g))
def md (n:Nat)(D:N)(a b:Nat):Prop:=D1 (fun a c=>mv n D a c/\K D a=1) a b
lemma mX (k:R n D){v b:Nat}(h:md n D v b):pv n D b v:=by
 induction h using Dr with
 | refl=>exact D5 rfl
 | @head a c hstep _ i=>
   by_cases d:b=a;. exact D5 d
   . right;intro l;rcases Dq l with g|⟨c',j,f⟩
     . have o:=n5 k a (by rw[g];unfold mN;omega);have m:=hstep.2;omega
     . have e:c=c':=mT hstep.1 j.1 hstep.2;subst e;rcases i with rfl|i
       . exact j.2 rfl
       . exact i f
lemma nx (f:R n D)(v:F n):∀ w,v∈V n D w->(∀ u,u<w->v∈V n D u->K D u<=1)->md n D v.val w:=by
 intro w;induction w using AI with
 | _ w h=>
   intro hv hlow;by_cases g:w<n;. have i:V n D w={⟨w,g⟩}:=nF D ⟨w,g⟩;rw[i,A5] at hv;rw[hv];exact DD
   . have b:=nq hv;obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have e:j<D.length:=(by omega)
     have c:∀ s:Y,v∈V n D (E D (j,s))->md n D v.val (n+j):=by intro s hva;have a:mv n D (E D (j,s)) (n+j):=nw e s;have b':=o5 f e s;have d:=oz a;have l:=hlow _ b' hva;exact Dp (h _ b' hva (fun u k=>hlow u (by omega))) ⟨a,by omega⟩
     rw[od f j e] at hv;split_ifs at hv with ht;. exact c J (by rw[mq];exact(A3.mp hv).1)
     . rcases AA.mp hv with d|d
       . exact c J (by rw[mq];exact d)
       . exact c H (by rw[mx];exact d)
lemma nl (f:mA zg)(v:F n):¬ mW zg (nn v):=by rintro⟨a,c,b,e,d⟩;simp only[nn,A6] at e d;rw[e,d] at b;exact f.2.1 _ b
lemma qY {u v:F n}(a:zg u v):mW zg (mO u v):=⟨u,v,a,by simp[mO],by simp[mO]⟩
lemma n9 (b:mA zg)(a:mm n zg D):V n D (mN n D)=∅:=CF.2
 (fun v c=>nl b v ((a _).1 (s9.1 c)))
lemma nT (w:mA zg)(r:R n D)(s:mm n zg D)(v:F n)(b:Nat)(e:pv n D b v.val):V n D b⊆{v}:=by
 intro u hu;rw[A5];by_contra i;obtain⟨p,l,q,-⟩:=w;obtain⟨z,h,g⟩:=q v u (Du i);have j:val D (mO u z) b=H:=mU r hu (by simp[mO]);have k:val D (mh v (mO u z)) b=H:=mU r hu (by simp[mh,mO]);have f:=q6 r _ _ v (ng v (mO u z)) b e (by rw[j,k]);have x:¬ mW zg (mO u z):=by
  rintro⟨a,c,d,o,m⟩;simp only[mO,Ai,A6] at o m;rcases o with o|o<;>rcases m with m|m<;>rw[o,m] at d
  . exact l _ d
  . exact g d
  . exact g (p _ _ d)
  . exact l _ d
 have y:mW zg (mh v (mO u z)):=⟨v,z,h,na v _,by simp[mh,mO]⟩;have t:=(s _).mpr y;rw[<-f] at t;exact x ((s _).mp t)
lemma pI (h:mA zg)(e:R n D)(g:mm n zg D)(v:F n)(i:v∈mb n D):∃ b,2<=K D b/\V n D b={v}/\md n D v.val b:=by
 classical
 have a:∃ w,2<=K D w/\v∈V n D w:=sd.mp i;obtain⟨k,f⟩:=Nat.find_spec a;have c:md n D v.val (Nat.find a):=nx e v _ f (fun u j d=>by
  have:=Nat.find_min a j;by_contra l;exact this ⟨by omega,d⟩)
 exact⟨Nat.find a,k,Subset.antisymm (nT h e g v _ (mX e c)) (By.mpr f),c⟩
def oy (n:Nat)(D:N)(b:F n->Nat):Prop:=∀ v∈mb n D,2<=K D (b v)/\V n D (b v)={v}/\md n D v.val (b v)
lemma oo (f:mA zg)(e:R n D)(d:mm n zg D):∃ b:F n->Nat,oy n D b:=by
 classical
 have h:∀ v:F n,∃ b,v∈mb n D->2<=K D b/\V n D b={v}/\md n D v.val b:=by
  intro v;by_cases a:v∈mb n D;. obtain⟨b,c⟩:=pI f e d v a;exact⟨b,fun _=>c⟩
  . exact⟨0,fun h=>Qa h a⟩
 choose b c using h;exact⟨b,fun v a=>c v a⟩
lemma oI {b:F n->Nat}(a:oy n D b):mw n D b:=fun v c=>⟨(a v c).1,(a v c).2.1⟩
lemma oD (d:mA zg)(c:R n D)(a:mm n zg D):∃ b:F n->Nat,mw n D b:=by have⟨b,e⟩:=oo d c a;exact⟨b,oI e⟩
lemma sa {v:F n}:v∈U n D↔v∉mb n D:=by simp[U]
lemma pO (b:R n D){v:F n}(c:v∈U n D){w:Nat}(a:v∈V n D w):md n D v.val w:=nx b v w a (fun u _ d=>sc.mp c u d)
lemma q1 (e:mA zg)(a:R n D)(d:mm n zg D){v:F n}(c:v∈U n D){w:Nat}(b:v∈V n D w):V n D w={v}:=Subset.antisymm (nT e a d v w (mX a (pO a c b)))
 (By.mpr b)
lemma s6 {v:F n}{w:Nat}:w∈S n D {v}↔v∈V n D w:=by
 simp only[S,O,Ac];constructor;. rintro⟨-,u,a⟩;rw[A3,A5] at a;exact a.2▸a.1
 . intro h;exact⟨nq h,v,A3.mpr ⟨h,Ao v⟩⟩
lemma s7 {v:F n}{e:Nat×Y}:e∈mt n D (S n D {v})↔e.1 < D.length/\v∈V n D (E D e)/\v∉V n D (n+e.1):=by simp[mt,ps,and_true,s6]
lemma po {v:F n}(a:v∈U n D):mo D (S n D {v})=0:=by unfold mo;refine sum_eq_zero (fun w b=>?_);have:=sc.mp a w (s6.mp b);omega
lemma nt (hG:mA zg)(x:R n D)(z:mm n zg D){u v:F n}(m:zg u v):∃ j,j<D.length/\oi D j=H/\val D (mO u v) (n+j)=H/\u∉V n D (n+j)/\v∉V n D (n+j)/\∃ s:Y,u∈V n D (E D (j,s))/\v∉V n D (E D (j,s))/\v∈V n D (E D (j,!s))/\u∉V n D (E D (j,!s)):=by
 classical
 have g:∃ w,val D (mO u v) w=H/\u∉V n D w/\v∉V n D w:=⟨mN n D,(z _).2 (qY m),by rw[n9 hG z];simp,by rw[n9 hG z];simp⟩
 have⟨b,d,c⟩:=Nat.find_spec g;have e:∀ a < Nat.find g,val D (mO u v) a=H->u∈V n D a\/v∈V n D a:=fun a ha h1=>by by_contra p;rw[not_or] at p;exact Nat.find_min g ha ⟨h1,p.1,p.2⟩
 generalize Nat.find g=w at b d c e;have o:w<n+D.length:=by by_contra p;rw[os D _ w (by omega)] at b;exact B8 b
 have hn:n<=w:=by by_contra p;have p':w<n:=(by omega);rw[my D _ w p'] at b;rw[nF D ⟨w,p'⟩,A5] at d c;simp only[mO,Ai,A6] at b;rcases b with h|h;exact d h.symm;exact c h.symm
 obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have q:j<D.length:=(by omega)
 obtain⟨ha,hb,-⟩:=x j q;have k:=b;rw[mS x _ j q] at b;rw[od x j q] at d c;cases y:oi D j;. exfalso;rw[y] at b d c;simp only[gop_false,Ai] at b;simp only[Ak,AB,AA,not_or] at d c;rcases b with h|h<;>(rcases e _ (by assumption) h with h'|h'<;>tauto)
 . rw[y] at b d c;simp only[gop_true,X] at b;simp only[AX,A3,not_and] at d c;have f:u∉V n D (n+j)/\v∉V n D (n+j):=by rw[mK x q y];simp only[A3,not_and];exact⟨d,c⟩
   refine⟨j,q,y,k,f.1,f.2,?_⟩;rcases e _ ha b.1 with r|r;. have t:=d r;have i:=(e _ hb b.2).resolve_left t;exact⟨false,by simp[E,r],by simp[E];exact fun h=>c h i,by simp[E,i],by simp[E,t]⟩
   . have t:=c r;have l:=(e _ hb b.2).resolve_right t;exact⟨H,by simp[E,l],by simp[E,t],by simp[E,r],by simp[E];exact fun h=>d h l⟩
lemma nd (r:mA zg)(h:m7 n D)(t:mm n zg D){v:F n}(hv:v∈U n D):∃ e:Nat×Y,e.1<D.length/\oi D e.1=H/\V n D (E D e)={v}/\V n D (n+e.1)=∅/\(∀ a,zg v a->a∈V n D (E D (e.1,!e.2)))/\mt n D (S n D {v})={e}/\mI n D (S n D {v})=∅:=by
 have z:=h.1;have l:=nm h {v} (by rw[n9 r t];simp);rw[po hv,Bk] at l;have b:∀ a,zg v a->∃ j s,j<D.length/\oi D j=H/\(j,s)∈mt n D (S n D {v})/\a∈V n D (E D (j,!s)):=by intro a d;have⟨j,hj,ht,_,h2,_,s,h1,_,h3,_⟩:=nt r z t d;exact⟨j,s,hj,ht,s7.mpr ⟨hj,h1,h2⟩,h3⟩
 obtain⟨a0,y,-⟩:=r.2.2.2 v v;obtain⟨u,w,p,q,m,-⟩:=b a0 y;have f:(mt n D (S n D {v})).card=1:=by have:=Bc.mpr ⟨_,m⟩;omega
 have g:mI n D (S n D {v})=∅:=BF.mp (by omega);obtain⟨e,o⟩:=CB.mp f;rw[o,A5] at m;subst m;have c:V n D (E D (u,w))={v}:=q1 r z t hv (s7.mp (by rw[o];exact Ao _)).2.1;have k:v∉V n D (n+u):=(s7.mp (by rw[o];exact Ao _)).2.2;refine⟨(u,w),p,q,c,?_,?_,o,g⟩
 . refine CI (fun x hx=>?_)
   have i:=n8 z p q w hx;rw[c,A5] at i;exact k (i▸hx)
 . intro a d;have⟨j,s,_,_,hm,ha⟩:=b a d;rw[o,A5] at hm;rw[Prod.mk.injEq] at hm;obtain⟨rfl,rfl⟩:=hm;exact ha
lemma qh (e:mA zg)(h:m7 n D)(f:mm n zg D){u v:F n}(b:zg u v):u∈mb n D\/v∈mb n D:=by by_contra g;rw[not_or] at g;have⟨z,_,_,_,_,m,l,_⟩:=nd e h f (sa.mpr g.1);obtain⟨ev,-,-,i,-,-,o,-⟩:=nd e h f (sa.mpr g.2);obtain⟨j,q,-,-,p,k,s,x,-,y,-⟩:=nt e h.1 f b;have w:(j,s)∈mt n D (S n D {u}):=s7.mpr ⟨q,x,p⟩;have r:(j,!s)∈mt n D (S n D {v}):=s7.mpr ⟨q,y,k⟩;rw[l,A5] at w;rw[o,A5] at r;subst w;subst r;obtain⟨a,d,c⟩:=e.2.2.2 u v;have t:a∈V n D (E D (j,!s)):=m a d;rw[i,A5] at t;exact c t
lemma q2 {A:Sn n}(g:∀ a∈A,∀ b∈A,¬ zg a b):¬ mW zg (mg A):=by rintro⟨a,c,d,f,e⟩;simp only[mg,A6] at f e;exact g a f c e d
lemma pw (hG:mA zg)(r:R n D)(y:mm n zg D)(A:Sn n)(hA:∀ a∈A,∀ b∈A,¬ zg a b)(x:F n)(m:∃ a∈A,zg x a):∃ j s,j<D.length/\oi D j=H/\x∈V n D (E D (j,s))/\x∉V n D (n+j)/\Disjoint (V n D (E D (j,s))) A:=by
 by_contra h;have d:∀ j s,j<D.length->oi D j=H->x∈V n D (E D (j,s))->x∉V n D (n+j)->val D (mg A) (E D (j,s))=H/\val D (mh x (mg A)) (E D (j,s))=H:=fun j s f u q h2=>by
  obtain⟨a,e,k⟩:=not_disjoint_iff.mp fun hd=>h ⟨j,s,f,u,q,h2,hd⟩;exact⟨mU r e (by simp[mg,k]),mU r e (by simp[mh,mg,k])⟩
 have o:∀ w,x∉V n D w->val D (mg A) w=val D (mh x (mg A)) w:=fun w=>by
  induction w using AI with
  | _ w t=>
    intro hw;by_cases z:w<n;. rw[my D _ w z,my D _ w z];rw[nF D ⟨w,z⟩,A5] at hw;exact ng x _ _ fun hc=>hw hc.symm
    . by_cases p:w<n+D.length
      . obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w-n,by omega⟩;have f:j<D.length:=(by omega)
        obtain⟨v,hb,-⟩:=r j f;rw[mS r _ j f,mS r _ j f];cases u:oi D j;. rw[no r f u,AA,not_or] at hw;rw[t _ v hw.1,t _ hb hw.2]
        . have i:=hw;rw[mK r f u,A3,not_and] at i;by_cases c:x∈V n D (nX D j)
          . have q:=d j J f u (by rw[mq];exact c) hw;rw[mq] at q;rw[t _ hb (i c),q.1,q.2]
          . by_cases l:x∈V n D (nL D j)
            . have q:=d j H f u (by rw[mx];exact l) hw;rw[mx] at q;rw[t _ v c,q.1,q.2]
            . rw[t _ v c,t _ hb l]
      . rw[os D _ w (by omega),os D _ w (by omega)]
 have g:=o (mN n D) (by rw[n9 hG y];exact Bd x);obtain⟨a,v,c⟩:=m;exact q2 hA ((y _).mp (g▸(y _).mpr ⟨x,a,c,na x _,by simp[mh,mg,v]⟩))
lemma oR (m:R n D)(T zm:Sn n)(hM:2<=zm.card)(w:Nat)(t:V n D w∩T=zm):∃ j,j<D.length/\n+j<=w/\V n D (n+j)∩T=zm/\j∈mI n D (S n D T)/\(∀ u,u<n+j->V n D u∩T≠zm)/\((oi D j=H/\zm ⊂ V n D (nX D j)∩T/\zm ⊂ V n D (nL D j)∩T)\/(oi D j=J/\V n D (nX D j)∩T ⊂ zm/\V n D (nL D j)∩T ⊂ zm/\(V n D (nX D j)∩T)∪(V n D (nL D j)∩T)=zm/\(V n D (nX D j)∩T).Nonempty/\(V n D (nL D j)∩T).Nonempty)):=by
 classical
 have c:∃ u,V n D u∩T=zm:=⟨w,t⟩;have l:=Nat.find_min' c t;have b:∀ u < Nat.find c,V n D u∩T≠zm:=fun u z=>Nat.find_min c z;have a:=Nat.find_spec c;generalize Nat.find c=f at l b a;have e:zm.Nonempty:=Bc.mp (by omega);have d:∀ {u:Nat},(V n D u∩T).Nonempty->u∈S n D T:=fun⟨v,i⟩=>O.mpr ⟨Ac.mpr (nq (A3.mp i).1),v,i⟩;have o:f<n+D.length:=by have⟨v,i⟩:=e;rw[<-a] at i;exact nq (A3.mp i).1
 have p:n<=f:=by by_contra x;have x':f<n:=(by omega);have h1:zm.card<=1:=(by rw[<-a,nF D ⟨f,x'⟩];exact(Aa B9).trans (by simp));omega
 obtain⟨j,rfl⟩:∃ j,f=n+j:=⟨f-n,by omega⟩;have k:j<D.length:=(by omega)
 obtain⟨ha,hb,-⟩:=m j k;have h:=b _ ha;have g:=b _ hb;set A:=V n D (nX D j)∩T;set y:=V n D (nL D j)∩T;have r:A.Nonempty/\y.Nonempty:=by
  cases q:oi D j;. rw[no m k q,BN] at a;change A∪y=zm at a;exact⟨AE.mpr fun s=>g (by rwa[s,empty_union] at a),AE.mpr fun s=>h (by rwa[s,union_empty] at a)⟩
  . rw[mK m k q] at a;have⟨v,i⟩:=e;rw[<-a] at i;simp only[A3] at i;exact⟨⟨v,A3.mpr ⟨i.1.1,i.2⟩⟩,⟨v,A3.mpr ⟨i.1.2,i.2⟩⟩⟩
 refine⟨j,k,l,a,O.mpr ⟨Ac.mpr k,d (a.symm▸e),d r.1,d r.2⟩,b,?_⟩;cases q:oi D j;. right;rw[no m k q,BN] at a;exact⟨rfl,AV.mpr ⟨a▸subset_union_left,h⟩,AV.mpr ⟨a▸subset_union_right,g⟩,a,r.1,r.2⟩
 . left;rw[mK m k q] at a;exact⟨rfl,AV.mpr ⟨fun v i=>by rw[<-a] at i;simp only[A3] at i ⊢;exact⟨i.1.1,i.2⟩,Du h⟩,AV.mpr ⟨fun v i=>by rw[<-a] at i;simp only[A3] at i ⊢;exact⟨i.1.2,i.2⟩,Du g⟩⟩
end SemCore
lemma qu:∀ u v:B,∃ a,ma u a=H/\a≠v:=by decide +kernel
lemma s5:mA (fun u v:B=>oF u v):=⟨fun _ _=>oS,pm,nN,fun u v=>by
 have⟨a,h1,h2⟩:=qu u v
 exact⟨a,(mj u a).mp h1,h2⟩⟩
lemma mG {D:N}(a:mB D):mm 12 (fun u v:B=>oF u v) D:=fun x=>(a x).trans (mV x)
lemma mZ {D:N}(h:m7 12 D)(a:mB D):∃ b:B->Nat,mw 12 D b:=oD s5 h.1 (mG a)
lemma pD {D:N}(h:m7 12 D)(b:mB D):p4 (mb 12 D):=fun _ _ a=>qh s5 h (mG b) a
lemma qg (j:Circuit)(d:Monotone2 j)(o:∀ x:B->Y,j.eval (Da x)=H↔G12Edge x)(f:j.size<=20):∃ D:N,m7 12 D/\mB D/\D.length<=20/\me 12 D<=9/\3<=(U 12 D).card/\U 12 D∈mY:=by obtain⟨D0,k,g,e⟩:=qw j d o;have a:D0.length<=20:=(by omega);obtain⟨b,n⟩:=mZ k e;have c:=pD k e;obtain⟨m,h,-⟩:=o6 k a b n c;obtain⟨D,i,l,q,-,-,-,-,p⟩:=rQ k e ((pd D0).mp c) m;have a':D.length<=20:=(by omega);obtain⟨b',n'⟩:=mZ i l;obtain⟨-,h',-⟩:=o6 i a' b' n' (pD i l);exact⟨D,i,l,a',(qi i a').2,h',p⟩
def C (n:Nat)(D:N)(x:F n):I (Nat×Y):=mt n D (S n D {x})
def mn (e:Nat×Y):Nat×Y:=(e.1,!e.2)
section SemCodes
variable {n:Nat} {zg:F n->F n->Prop} {D:N}
lemma s4 {x:F n}{e:Nat×Y}:e∈C n D x↔e.1 < D.length/\x∈V n D (E D e)/\x∉V n D (n+e.1):=s7
lemma mJ (e:Nat×Y):mn (mn e)=e:=by simp[mn]
lemma rs (e:Nat×Y):mn e≠e:=by intro h;have a:=Az Prod.snd h;simp[mn] at a
lemma qy {e f:Nat×Y}(h:e.1=f.1):f=e\/f=mn e:=by have⟨j,s⟩:=e;obtain⟨k,t⟩:=f;simp only at h;subst h;cases s<;>cases t<;>simp[mn]
lemma qI (c:R n D){x:F n}{e:Nat×Y}(d:e∈C n D x):oi D e.1=H:=by
 have⟨f,b,g⟩:=s4.mp d;by_contra a;rw[Ch] at a;apply g;rw[no c f a,AA];obtain⟨j,s⟩:=e;cases s;. left;simpa[E] using b
 . right;simpa[E] using b
lemma rD (b:mA zg)(h:m7 n D)(a:mm n zg D)(x:F n):(C n D x).card+(mI n D (S n D {x})).card=1+mo D (S n D {x}):=by have c:=nm h {x} (by rw[n9 b a];simp);rwa[Bk] at c
lemma qr (i:mA zg)(h:R n D)(g:mm n zg D){x y:F n}(a:zg x y):∃ e,e∈C n D x/\mn e∈C n D y/\y∉V n D (E D e)/\x∉V n D (E D (mn e))/\val D (mO x y) (n+e.1)=H:=by have⟨j,f,_,b,d,c,s,k,o,l,m⟩:=nt i h g a;exact⟨(j,s),s4.mpr ⟨f,k,d⟩,s4.mpr ⟨f,l,c⟩,o,m,b⟩
lemma oW (o:mA zg)(r:R n D)(q:mm n zg D){x a b y:F n}(i:¬ zg a b)(k:zg x y)(g:¬ zg y a)(f:¬ zg y b):∃ e,e∈C n D x/\a∉V n D (E D e)/\b∉V n D (E D e):=by
 have c:=o.1;have d:=o.2.1;have z:∀ u∈({a,b,y}:Sn n),∀ v∈({a,b,y}:Sn n),¬ zg u v:=by
  intro u l v m;simp only[A9,A5] at l m;rcases l with l|l|l<;>rcases m with m|m|m<;>rw[l,m]
  . exact d a
  . exact i
  . exact fun h=>g (c _ _ h)
  . exact fun h=>i (c _ _ h)
  . exact d b
  . exact fun h=>f (c _ _ h)
  . exact g
  . exact f
  . exact d y
 obtain⟨j,s,t,-,w,h2,p⟩:=pw o r q {a,b,y} z x ⟨y,by simp,k⟩;exact⟨(j,s),s4.mpr ⟨t,w,h2⟩,fun h=>AG.mp p h (by simp),
  fun h=>AG.mp p h (by simp)⟩
lemma qE (g:mA zg)(j:R n D)(i:mm n zg D){x a:F n}(d:x≠a):∃ e,e∈C n D x/\a∉V n D (E D e):=by
 obtain⟨z,f,c⟩:=g.2.2.1 x a d;obtain⟨e,k,l,-⟩:=oW g j i (a:=a) (b:=a) (g.2.1 a) f (fun h=>c (g.1 _ _ h)) (fun h=>c (g.1 _ _ h))
 exact⟨e,k,l⟩
end SemCodes
lemma pk {α:Type}{f:α->α->Prop}(d:∀ a a' b,f a b->f a' b->a=a'){u v c:α}(m:D1 f u c)(l:D1 f v c):D1 f u v\/D1 f v u:=by
 induction m with
 | refl=>exact D6 l
 | tail k g n=>
   rcases Relation.ReflTransGen.cases_tail l with h|⟨b',i',j⟩;. left;rw[<-h];exact Dp k g
   . have e:b'=_:=d _ _ _ j g;rw[e] at i';exact n i'
def ob (n:Nat)(D:N)(b:F n->Nat):Prop:=∀ v∈mb n D,2<=K D (b v)/\V n D (b v)={v}/\md n D v.val (b v)/\∀ w,2<=K D w->v∈V n D w->b v<=w
def p5 (n:Nat)(D:N)(c:Sn n)(a b:Nat):Prop:=mv n D a b/\K D a=1/\∀ x∈c,x∈V n D a/\x∈V n D b
section SemArms
variable {n:Nat} {zg:F n->F n->Prop} {D:N}
lemma nk (e:R n D){d:Nat->Nat->Prop}(f:∀ a b,d a b->mv n D a b){a b:Nat}(h:D1 d a b):a<=b:=by induction h with|refl=>exact le_refl _ | tail _ c g=>exact le_trans g (le_of_lt (oO e (f _ _ c)))
lemma oV (l:mA zg)(i:R n D)(k:mm n zg D):∃ b:F n->Nat,ob n D b:=by
 classical
 have h:∀ v:F n,∃ b,v∈mb n D->2<=K D b/\V n D b={v}/\md n D v.val b/\∀ w,2<=K D w->v∈V n D w->b<=w:=by
  intro v;by_cases g:v∈mb n D
  . have a:∃ w,2<=K D w/\v∈V n D w:=sd.mp g;obtain⟨o,j⟩:=Nat.find_spec a;have c:md n D v.val (Nat.find a):=nx i v _ j (fun u m f=>by
     have:=Nat.find_min a m;by_contra p;exact this ⟨by omega,f⟩)
    exact⟨Nat.find a,fun _=>⟨o,Subset.antisymm (nT l i k v _ (mX i c)) (By.mpr j),c,fun w d e=>Nat.find_min' a ⟨d,e⟩⟩⟩
  . exact⟨0,fun h=>Qa h g⟩
 choose b hb using h;exact⟨b,fun v g=>hb v g⟩
lemma nY {b:F n->Nat}(a:ob n D b):mw n D b:=fun v c=>⟨(a v c).1,(a v c).2.1⟩
lemma o7 (f:R n D){x:F n}(g:mI n D (S n D {x})=∅){j:Nat}(c:j<D.length)(b:x∈V n D (n+j)):oi D j=J/\¬(x∈V n D (nX D j)/\x∈V n D (nL D j)):=by
 have a:¬(x∈V n D (nX D j)/\x∈V n D (nL D j)):=by
  intro hc;have e:j∈mI n D (S n D {x}):=by rw[mI,O,Ac];exact⟨c,s6.mpr b,s6.mpr hc.1,s6.mpr hc.2⟩
  rw[g] at e;exact Bd _ e
 refine⟨?_,a⟩;by_contra d;rw[B0] at d;rw[mK f c d,A3] at b;exact a b
lemma oN (d:mA zg)(h:m7 n D)(c:mm n zg D)(b:F n->Nat)(e:mw n D b)(x:F n):(C n D x).card+(mI n D (S n D {x})).card=1+(({x}:Sn n)∩mb n D).card+((mi n D b).filter (fun u=>x∈V n D u.1)).card:=by
 have j:=rD d h c x;have i:=nR h.1 b e {x};have f:(mi n D b).filter (fun u=>(V n D u.1∩{x}).Nonempty) = (mi n D b).filter (fun u=>x∈V n D u.1):=by
  refine BG (fun u _=>?_)
  constructor;. rintro⟨y,a⟩;rw[A3,A5] at a;exact a.2▸a.1
  . intro g;exact⟨x,A3.mpr ⟨g,Ao x⟩⟩
 rw[f] at i;omega
lemma rf (hG:mA zg)(h:m7 n D)(hC:mm n zg D)(y:Sn n)(hX:y.Nonempty)(hM:∀ x∈y,mI n D (S n D {x})=∅):∀ c,(∀ x∈y,x∈V n D c)->(∀ x∈y,∀ w,c<=w->x∈V n D w->K D w<=1)->∃ e:Nat×Y,(∀ x∈y,e∈C n D x)/\D1 (p5 n D y) c (E D e):=by
 classical
 have hS:=h.1;have⟨x0,a⟩:=hX;intro c;generalize hk:n+D.length-c=k;induction k using AI generalizing c with
 | _ k ih=>
   intro hc hlow;have t:=nq (hc x0 a);have l:c≠mN n D:=by intro he;have:=hc x0 a;rw[he,n9 hG hC] at this;exact Bd _ this
   have i:1<=K D c:=h.2.1 c (by unfold mN at l;omega);have hf:K D c=1:=le_antisymm (hlow x0 a c (le_refl c) (hc x0 a)) i;have⟨j,m⟩:=Bc.mp i;simp only[mP,O,Ac] at m;obtain⟨hj,f⟩:=m;obtain⟨s,hs⟩:∃ s:Y,E D (j,s)=c:=by
    rcases f with z|z;. exact⟨J,by rw[mq];exact z⟩
    . exact⟨H,by rw[mx];exact z⟩
   have u:c<n+j:=hs▸o5 hS hj s;by_cases d:∃ x1∈y,x1∈V n D (n+j)
   . have⟨x1,p,g⟩:=d;have ht:=(o7 hS (hM x1 p) hj g).1;have b:∀ x∈y,x∈V n D (n+j):=by
      intro x v;rw[no hS hj ht,AA];rcases f with z|z;. left;rw[z];exact hc x v
      . right;rw[z];exact hc x v
     obtain⟨e,q,r⟩:=ih (n+D.length-(n+j)) (by omega) (n+j) rfl b (fun x v w hw=>hlow x v w (by omega));refine⟨e,q,Dt ⟨?_,hf,fun x v=>⟨hc x v,b x v⟩⟩ r⟩;rw[<-hs];exact nw hj s
   . refine⟨(j,s),fun x v=>s4.mpr ⟨hj,?_,fun o=>d ⟨x,v,o⟩⟩,?_⟩
     . rw[hs];exact hc x v
     . rw[hs]
lemma qL (hG:mA zg)(h:m7 n D)(hC:mm n zg D)(zx:Sn n)(hX:zx.Nonempty)(hM:∀ x∈zx,mI n D (S n D {x})=∅)(r:Nat)(hr:∀ x∈zx,x∈V n D r)(hf:2<=K D r)(h6:∀ x∈zx,∀ w,r<w->x∈V n D w->K D w<=1):∃ P kq:Nat×Y,P.1≠kq.1/\∀ x∈zx,P∈C n D x/\kq∈C n D x:=by
 classical
 have hS:=h.1;have⟨x0,c⟩:=hX;obtain⟨j1,k,j2,l,z⟩:=one_lt_card.mp (show 1<(mP D r).card from hf);have d:∀ j∈mP D r,j<D.length/\r<n+j/\(nX D j=r\/nL D j=r):=fun j hj=>by simp only[mP,O,Ac] at hj;have:=hS j hj.1;exact⟨hj.1,by omega,hj.2⟩
 have i:∀ j∈mP D r,∃ e:Nat×Y,(∀ x∈zx,e∈C n D x)/\((e.1=j/\E D e=r)\/D1 (p5 n D zx) (n+j) (E D e)):=fun j hj=>by
  have⟨t,x3,hi⟩:=d j hj;obtain⟨s,hs⟩:∃ s:Y,E D (j,s)=r:=hi.elim (fun y=>⟨J,by rw[mq];exact y⟩) (fun y=>⟨H,by rw[mx];exact y⟩)
  by_cases o:∃ x1∈zx,x1∈V n D (n+j)
  . have⟨x1,hm,hg⟩:=o;have h8:∀ x∈zx,x∈V n D (n+j):=fun x hx=>by rw[no hS t (o7 hS (hM x1 hm) t hg).1,AA];exact hi.imp (fun y=>by rw[y];exact hr x hx) (fun y=>by rw[y];exact hr x hx)
    obtain⟨e,hz,hk⟩:=rf hG h hC zx ⟨x0,c⟩ hM (n+j) h8 (fun x hx w hw=>h6 x hx w (by omega));exact⟨e,hz,D6 hk⟩
  . exact⟨(j,s),fun x hx=>s4.mpr ⟨t,hs▸hr x hx,fun hl=>o ⟨x,hx,hl⟩⟩,D5 ⟨rfl,hs⟩⟩
 have f:∀ a b,p5 n D zx a b->mv n D a b:=fun _ _ h0=>h0.1;have he:∀ a a' b,p5 n D zx a b->p5 n D zx a' b->a=a':=fun a a' b y h2=>by
  by_contra m;obtain⟨x5,hn,q⟩:=y.1;obtain⟨-,-,q'⟩:=h2.1;have p:b-n<D.length:=(by omega);apply(o7 hS (hM x0 c) p (by rw[Nat.add_sub_cancel' hn];exact(y.2.2 x0 c).2)).2;have ha:=(y.2.2 x0 c).1;have ha':=(h2.2.2 x0 c).1;rcases q with e1|e1<;>rcases q' with e2|e2<;>first|exact Qa (e1.symm.trans e2) m|(rw[e1,e2];exact⟨ha,ha'⟩)|(rw[e1,e2];exact⟨ha',ha⟩)
 have g:∀ ja∈mP D r,∀ jb∈mP D r,ja≠jb->¬ D1 (p5 n D zx) (n+ja) (n+jb):=fun ja xn jb p h0 hp=>by
  obtain⟨-,xz,-⟩:=d ja xn;obtain⟨hb,x2,hd⟩:=d jb p;rcases Relation.ReflTransGen.cases_tail hp with ya|⟨u,xt,xb⟩;. exact h0 (by omega)
  . have x4:=nk hS f xt;have v:u=r:=by by_contra v;have⟨_,_,xf⟩:=xb.1;rw[Bt] at xf;apply(o7 hS (hM x0 c) hb (xb.2.2 x0 c).2).2;have hu:=(xb.2.2 x0 c).1;have hh:=hr x0 c;rcases xf with e1|e1<;>rcases hd with e2|e2<;>first|exact Qa (e1.symm.trans e2) v|(rw[e1,e2];exact⟨hu,hh⟩)|(rw[e1,e2];exact⟨hh,hu⟩)
    omega
 obtain⟨P,h5,hy⟩:=i j1 k;obtain⟨kq,h7,h9⟩:=i j2 l;refine⟨P,kq,fun hq=>?_,fun x hx=>⟨h5 x hx,h7 x hx⟩⟩;have h3:kq=P:=(qy hq).resolve_right fun y=>by
  have⟨ho,hc,hv⟩:=s4.mp (h5 x0 c);have h4:=(s4.mp (h7 x0 c)).2.1;rw[y] at h4;apply hv;rw[mK hS ho (qI hS (h5 x0 c)),A3];obtain⟨j,s⟩:=P;cases s<;>simp_all[E,mn]
 rw[h3] at h9;have⟨_,y3,_⟩:=d j1 k;obtain⟨-,y1,-⟩:=d j2 l;rcases hy with⟨xr,ye⟩|xg<;>rcases h9 with⟨xp,yg⟩|xe
 . exact z (xr.symm.trans xp)
 . have:=nk hS f xe;omega
 . have:=nk hS f xg;omega
 . rcases pk he xg xe with y|y;exact g j1 k j2 l z y;exact g j2 l j1 k (Du z) y
lemma oa (j:mA zg)(h:m7 n D)(i:mm n zg D)(b:F n->Nat)(k:mw n D b){d:Σ _:Nat,Nat}(a:mi n D b={d}){x:F n}(c:3<=(C n D x).card):(C n D x).card=3/\mI n D (S n D {x})=∅/\x∈mb n D/\x∈V n D d.1:=by
 have g:=oN j h i b k x;have o:(({x}:Sn n)∩mb n D).card<=1:=(Aa B9).trans (by simp);have l:=Ck (mi n D b) (fun u=>x∈V n D u.1);rw[a,Bk] at l;rw[a] at g;refine⟨by omega,BF.mp (by omega),?_,?_⟩;. by_contra m;have f:({x}:Sn n)∩mb n D=∅:=(by rw[singleton_inter_of_notMem m]);rw[f,CH] at g;omega
 . have f:0<(({d}:I (Σ _:Nat,Nat)).filter (fun u=>x∈V n D u.1)).card:=(by omega)
   have⟨u,e⟩:=Bc.mp f;rw[O,A5] at e;exact e.1▸e.2
lemma oT (z:mA zg)(h:m7 n D)(y:mm n zg D)(b:F n->Nat)(hb:ob n D b)(r:nh n D=(mb n D).card+1)(zx:Sn n)(hX:zx.Nonempty)(c:∀ x∈zx,3<=(C n D x).card):∃ P kq:Nat×Y,P.1≠kq.1/\∀ x∈zx,P∈C n D x/\kq∈C n D x:=by
 have hS:=h.1;have e:=nY hb;have f:(mi n D b).card=1:=by have:=nH hS b e;omega
 obtain⟨t,a⟩:=CB.mp f;have p:t∈mi n D b:=by rw[a];exact Ao _
 have l:t∈pz n D:=(O.mp (Am.mp p).1).1;have m:2<=K D t.1:=by have:=(se.mp l).2;omega
 refine qL z h y zx hX (fun x u=>(oa z h y b e a (c x u)).2.1)
  t.1 (fun x u=>(oa z h y b e a (c x u)).2.2.2) m ?_
 intro x u w hrw hxw;obtain⟨-,-,h2,h3⟩:=oa z h y b e a (c x u);by_contra hc;have s:2<=K D w:=(by omega);have q:(⟨w,0⟩:Σ _:Nat,Nat)∈np n D:=by rw[np,O,se];exact⟨⟨n2.mpr (nE hS (w:=w) (by omega)),by show 0+1<K D w;omega⟩,⟨x,hxw⟩⟩
 by_cases k:(⟨w,0⟩:Σ _:Nat,Nat)∈mF n D b;. have⟨v,hv,o⟩:=A7.mp k;have i:b v=w:=Az Sigma.fst o;have j:=(hb v hv).2.1;rw[i] at j;rw[j,A5] at hxw;have g:=(hb x h2).2.2.2 t.1 m h3;rw[hxw,i] at g;omega
 . have d:(⟨w,0⟩:Σ _:Nat,Nat)∈mi n D b:=Am.mpr ⟨q,k⟩;rw[a,A5] at d;have:w=t.1:=Az Sigma.fst d;omega
end SemArms
section SemPaths
variable {n:Nat} {zg:F n->F n->Prop} {D:N}
lemma o4 (a:F n):mg ({a}:Sn n)=nn a:=by funext k;simp[mg,nn]
lemma nD (b:R n D)(x:F n->Y){j:Nat}(a:j<D.length)(s:Y):val D x (n+j)=rE (oi D j) (val D x (E D (j,s))) (val D x (E D (j,!s))):=by
 rw[mS b x j a];cases s;. simp[E]
 . cases oi D j<;>simp[E,Bool.and_comm,Bool.or_comm]
lemma oe (g:mA zg){i:F n}{f:Sn n}(h:mW zg (mh i (mg f))):(∃ a∈f,zg i a)\/∃ a∈f,∃ b∈f,zg a b:=by
 have⟨u,v,c,d,e⟩:=h;simp only[mh,mg,Ai,A6] at d e;rcases d with d|d<;>rcases e with e|e
 . rw[d,e] at c;exact Qa c (g.2.1 i)
 . rw[d] at c;exact D5 ⟨v,e,c⟩
 . rw[e] at c;exact D5 ⟨u,d,g.1 _ _ c⟩
 . exact D6 ⟨u,d,v,e,c⟩
lemma pP (k:R n D){v b t:Nat}(h:md n D v b)(g:b<=t):b=v\/¬ D1 (fun a c=>mv n D a c/\c≠b) v t:=by
 induction h using Dr with
 | refl=>exact D5 rfl
 | @head a c hstep i j=>
   by_cases d:b=a;. exact D5 d
   . right;intro o;rcases Dq o with m|⟨c',l,i'⟩
     . have p:=oO k hstep.1;have q:=nk k (fun _ _ f=>f.1) i;omega
     . have e:c=c':=mT hstep.1 l.1 hstep.2;subst e;rcases j with rfl|j
       . exact l.2 rfl
       . exact j i'
lemma qx (l:R n D)(x y:F n->Y)(v:F n)(e:∀ k,k≠v->x k=y k)(b t:Nat)(d:b=v.val\/¬ D1 (fun a c=>mv n D a c/\c≠b) v.val t)(i:val D x b=val D y b):val D x t=val D y t:=by
 by_contra g;rcases d with rfl|d
 . rw[my D x _ v.isLt,my D y _ v.isLt] at i;have f:x=y:=by
    funext k;by_cases j:k=v;. rw[j];exact i
    . exact e k j
   exact g (by rw[f])
 . exact d (ok (fun a c h=>⟨h.1,fun m=>h.2 (by rw[m];exact i)⟩) (nG l x y v e _ g))
lemma qf (g:R n D){a c q:Nat}(h:md n D a c)(hq:D1 (mv n D) a q):D1 (mv n D) c q\/(md n D q c/\q≠c):=by
 revert hq;induction h using Dr with
 | refl=>exact fun hq=>D5 hq
 | @head a a' hstep e ih=>
   intro hq;rcases Dq hq with f|⟨a'',i,e'⟩;. right;have j:=oO g hstep.1;have k:=nk g (fun _ _ d=>d.1) e;refine⟨?_,by omega⟩;rw[<-f];exact Dt hstep e
   . have b:a'=a'':=mT hstep.1 i hstep.2;subst b;exact ih e'
lemma pB (o:R n D)(v:F n){j:Nat}(r:j<D.length)(s:Y)(e:md n D v.val (E D (j,!s)))(w:K D (E D (j,!s))=1)(x y:F n->Y)(f:∀ k,k≠v->x k=y k):val D x (E D (j,s))=val D y (E D (j,s)):=by
 by_contra g;have z:D1 (mv n D) v.val (E D (j,s)):=ok (fun _ _ h=>h.1) (nG o x y v f _ g);have b:mv n D (E D (j,!s)) (n+j):=nw r (!s);have a:mv n D (E D (j,s)) (n+j):=nw r s;have l:=o5 o r s;have i:=o5 o r (!s);rcases qf o e z with u|⟨u,h2⟩
 . rcases Dq u with p|⟨c',t,m⟩
   . exact rl o r s p.symm
   . have d:n+j=c':=mT b t w;subst d;have:=nk o (fun _ _ h=>h) m;omega
 . rcases Dq u with p|⟨q',t,m⟩
   . exact h2 p
   . have d:n+j=q':=mT a t.1 t.2;subst d;have:=nk o (fun _ _ h=>h.1) m;omega
lemma pf (f:R n D)(g:mm n zg D)(x:F n->Y)(v:F n)(b:Nat)(c:pv n D b v.val)(h:¬ mW zg x)(i:mW zg (mh v x)):val D x b=J/\val D (mh v x) b=H:=by
 have d:val D x b≠val D (mh v x) b:=by intro heq;have k:=q6 f x _ v (ng v x) b c heq;exact h ((g x).mp (by rw[k];exact(g _).mpr i))
 have a:=oQ f x (mh v x) (pq v x) b;cases e:val D x b
 . refine⟨rfl,?_⟩;cases j:val D (mh v x) b
   . exact Qa (e.trans j.symm) d
   . rfl
 . exact Qa (e.trans (a e).symm) d
lemma rn (r:R n D)(i:F n)(w:Nat)(l:md n D i.val w)(Bs zn:Sn n)(hN:zn⊆Bs)(h0:val D (mh i (mg (Bs \ zn))) w=J)(h1:∀ a∈zn,val D (mh i (mg {a})) w=H)(hz:∀ a∈zn,val D (mg {a}) w=J):∃ j s,j<D.length/\oi D j=H/\n+j<=w/\md n D i.val (E D (j,!s))/\V n D (E D (j,s))∩Bs=zn:=by
 set z:=mg (Bs \ zn);have hJ:∀ c,md n D i.val c->val D (mh i z) c=H\/∃ j s,j<D.length/\oi D j=H/\n+j<=c/\md n D i.val (E D (j,!s))/\K D (E D (j,!s))=1/\val D z (E D (j,s))=J:=fun c u=>by
  induction u with
  | refl=>left;rw[my D _ _ i.isLt];exact na i _
  | tail h7 y ih=>
    obtain⟨j,s,q,rfl,rfl⟩:=sh.mp y.1;have p:=o5 r q s;rcases ih with hy|⟨j',s',q',t',v,u',hf',hv'⟩
    . cases t:oi D j
      . left;rw[nD r _ q s,t,gop_false,hy];rfl
      . by_cases hq:val D (mh i z) (E D (j,!s))=H
        . left;rw[nD r _ q s,t,gop_true,hy,hq];rfl
        . right;refine⟨j,!s,q,t,le_refl _,by rw[DW];exact h7,by rw[DW];exact y.2,by by_contra b;rw[B0] at b;exact hq (oQ r _ _ (pq i _) _ b)⟩
    . exact D6 ⟨j',s',q',t',by omega,u',hf',hv'⟩
 rcases hJ w l with hy|⟨j,s,q,t,v,u,hf,hv⟩;. exact(B8 (h0.symm.trans hy)).elim
 . refine⟨j,s,q,t,v,u,?_⟩;have k:md n D i.val (n+j):=Dp u ⟨nw q (!s),hf⟩;ext a;rw[A3];constructor
   . rintro⟨m,o⟩;by_contra d;exact B8 (hv.symm.trans (mU r m (x:=z) (by simp[z,mg,o,d])))
   . intro d;refine⟨?_,hN d⟩;have g:val D (mg {a}) (n+j)≠val D (mh i (mg {a})) (n+j):=fun h6=>by have h2:=qx r _ _ i (ng i (mg {a})) (n+j) w (pP r k v) h6;rw[hz a d,h1 a d] at h2;exact B8 h2
     have f:val D (mh i (mg {a})) (n+j)=H:=by by_contra b;rw[Ch] at b;apply g;rw[b];by_contra h;rw[B0] at h;rw[oQ r _ _ (pq i _) _ h] at b;exact Bool.noConfusion b
     rw[nD r _ q s,t,gop_true,X] at f;have e:=pB r i q s u hf _ _ (ng i (mg {a}));rw[f.1,o4] at e;exact s9.mpr e
lemma pt (k:R n D)(i:F n)(w:Nat)(d:md n D i.val w)(Bs:Sn n)(l:∀ vs:Sn n,vs⊆Bs->(∀ a∈vs,¬ zg i a)->val D (mh i (mg vs)) w=J)(h:∀ a∈Bs,zg i a->val D (mh i (mg {a})) w=H/\val D (mg {a}) w=J):∃ j s,j < D.length/\oi D j=H/\n+j<=w/\md n D i.val (E D (j,!s))/\∀ a∈Bs,(a∈V n D (E D (j,s))↔zg i a):=by
 classical
 obtain⟨j,s,m,o,e,p,b⟩:=rn k i w d Bs (Bs.filter (fun a=>zg i a)) (Cq _ _) (l _ Cw (fun a g c=>by
  rw[Am,O] at g;exact g.2 ⟨g.1,c⟩))
  (fun a g=>(h a (O.mp g).1 (O.mp g).2).1)
  (fun a g=>(h a (O.mp g).1 (O.mp g).2).2)
 refine⟨j,s,m,o,e,p,fun a g=>?_⟩
 constructor;. intro f;have:a∈V n D (E D (j,s))∩Bs:=A3.mpr ⟨f,g⟩;rw[b,O] at this;exact this.2
 . intro c;have:a∈Bs.filter (fun a=>zg i a):=O.mpr ⟨g,c⟩;rw[<-b] at this;exact(A3.mp this).1
lemma pR (j:mA zg)(d:R n D)(g:mm n zg D){i:F n}(h:i∈U n D){b:Nat}(c:md n D i.val b)(k:2<=K D b):V n D b=∅:=by have a:=nT j d g i b (mX d c);refine CI (fun x f=>?_);have e:=a f;rw[A5] at e;have l:=sc.mp h b (e▸f);omega
lemma qq {a t:Nat}(e:D1 (mv n D) a t):md n D a t\/∃ b,md n D a b/\2<=K D b:=by
 induction e using Dr with
 | refl=>exact D5 DD
 | @head a a' hstep _ ih=>
   by_cases d:K D a=1
   . rcases ih with c|⟨b,c,f⟩
     . exact D5 (Dt ⟨hstep,d⟩ c)
     . exact D6 ⟨b,Dt ⟨hstep,d⟩ c,f⟩
   . have:=oz hstep;exact D6 ⟨a,DD,by omega⟩
lemma pN (g:mA zg)(h:m7 n D)(e:mm n zg D){i:F n}(f:i∈U n D):md n D i.val (mN n D)\/∃ b,md n D i.val b/\2<=K D b/\V n D b=∅:=by
 have a:i.val<n+D.length:=by have:=i.isLt;omega
 have j:D1 (mv n D) i.val (mN n D):=pQ h i.val a;rcases qq j with c|⟨b,c,d⟩;. exact D5 c
 . exact D6 ⟨b,c,d,pR g h.1 e f c d⟩
lemma qz (a:R n D){b:Nat}(d:2<=K D b)(c:V n D b=∅):b∈(nc n D).filter (fun w=>¬(V n D w).Nonempty):=O.mpr ⟨n2.mpr (nE a (w:=b) (by omega)),
 by rw[c];exact AS⟩
lemma qm (p:mA zg)(q:R n D)(l:mm n zg D)(Bs:Sn n)(f:∀ a∈Bs,∀ b∈Bs,¬ zg a b){i:F n}(e:md n D i.val (mN n D)):∃ j s,j < D.length/\oi D j=H/\md n D i.val (E D (j,!s))/\∀ a∈Bs,(a∈V n D (E D (j,s))↔zg i a):=by
 have⟨j,s,r,t,_,h,k⟩:=pt (zg:=zg) q i (mN n D) e Bs (fun v d g=>by
  by_contra h;rw[B0] at h;rcases oe p ((l _).mp h) with⟨a,m,c⟩|⟨a,m,b,u,o⟩;. exact g a m c
  . exact f a (d m) b (d u) o)
  (fun a _ c=>by
   constructor;. exact(l _).mpr ⟨i,a,c,na i _,by simp[mh,mg]⟩
   . by_contra h;rw[B0,o4] at h;exact nl p a ((l _).mp h))
 exact⟨j,s,r,t,h,k⟩
lemma pL (hG:mA zg)(x:R n D)(hC:mm n zg D)(Bs:Sn n)(m:∀ a∈Bs,∀ b∈Bs,¬ zg a b){i j:F n}{w:Nat}(f:md n D i.val w)(l:pv n D w j.val)(d:∃ a∈Bs,zg j a/\¬ zg i a):∃ k s,k < D.length/\oi D k=H/\n+k<=w/\md n D i.val (E D (k,!s))/\∀ a∈Bs,(a∈V n D (E D (k,s))↔zg i a):=by
 classical
 have p:¬ mW zg (mh i (mg (Bs.filter (fun a=>¬ zg i a)))):=by
  intro y;rcases oe hG y with⟨a,z,e⟩|⟨a,z,b,hb,h0⟩;. exact(O.mp z).2 e
  . exact m a (O.mp z).1 b (O.mp hb).1 h0
 obtain⟨a0,r,g,h⟩:=d;have o:mW zg (mh j (mh i (mg (Bs.filter (fun a=>¬ zg i a))))):=⟨j,a0,g,na j _,by simp[mh,mg,r,h]⟩;have q:=(pf x hC _ j w l p o).1;refine pt x i w f Bs (fun vs u t=>?_) (fun a _ e=>?_)
 . by_contra y;rw[B0] at y;have c:=oQ x (mh i (mg vs)) (mh i (mg (Bs.filter (fun a=>¬ zg i a)))) (fun k v=>by
    simp only[mh,mg,Ai,A6] at v ⊢;rcases v with v|v;. exact D5 v
    . exact D6 (O.mpr ⟨u v,t k v⟩)) w y
   rw[q] at c;exact B8 c
 . have h2:=pf x hC (mg {a}) i w (mX x f) (by rw[o4];exact nl hG a) ⟨i,a,e,na i _,by simp[mh,mg]⟩
   exact⟨h2.2,h2.1⟩
end SemPaths
def mu (n:Nat)(D:N)(P zm:Sn n):Prop:=∃ w,V n D w∩P=zm
def ot (n:Nat)(D:N)(P:Sn n):I Nat:=(mI n D (S n D P)).filter (fun j=>2<=(V n D (n+j)∩P).card)
def n3 (n:Nat)(D:N)(P zu:Sn n)(f:F n)(e:Nat×Y):Prop:=e.1<D.length/\oi D e.1=H/\f∈P/\f∈V n D (E D e)/\f∉V n D (n+e.1)/\V n D (E D e)∩P⊆zu/\(V n D (E D e)∩P).card<=2
def ms (n:Nat)(D:N)(P:Sn n)(e:Nat×Y):(Nat×Y) ⊕ Nat:=if V n D (n+e.1)∩P=∅ then inl e else inr e.1
def ql (n:Nat)(D:N)(P:Sn n)(c:(Nat×Y) ⊕ Nat):Prop:=Sum.elim (fun e=>e∈mt n D (S n D P)/\(V n D (E D e)∩P).card<=2) (fun j=>j∈mI n D (S n D P)/\(V n D (n+j)∩P).card=1) c
section SupMask
variable {n:Nat} {D:N}
lemma ow (P:Sn n)(w:Nat):mu n D P (V n D w∩P):=⟨w,rfl⟩
lemma oY {P zm:Sn n}(h:mu n D P zm):zm⊆P:=by obtain⟨w,rfl⟩:=h;exact Bm
lemma n1 {P:Sn n}{w:Nat}:w∈S n D P↔(V n D w∩P).Nonempty:=by
 simp only[S,O,Ac];constructor;. exact fun h=>h.2
 . intro h;have⟨v,a⟩:=h;exact⟨nq (A3.mp a).1,v,a⟩
lemma rd (d:R n D){P zm:Sn n}(b:2<=zm.card)(h:mu n D P zm):∃ j∈ot n D P,V n D (n+j)∩P=zm:=by have⟨w,e⟩:=h;obtain⟨j,-,-,c,a,-,-⟩:=oR d P zm b w e;exact⟨j,O.mpr ⟨a,by rw[c];exact b⟩,c⟩
lemma pX (e:R n D)(P:Sn n)(c:I (Sn n))(d:∀ zm∈c,2<=zm.card/\mu n D P zm):c.card<=(ot n D P).card:=by
 have a:c⊆(ot n D P).image (fun j=>V n D (n+j)∩P):=by intro zm hM;have⟨j,f,b⟩:=rd e (d zm hM).1 (d zm hM).2;exact A7.mpr ⟨j,f,b⟩
 exact(Aa a).trans card_image_le
lemma pC (p:R n D){P T:Sn n}(q:P.card<=7)(y:T.card=3)(h:mu n D P T):(∃ A,mu n D P A/\A.card=2/\A⊆T)\/(∃ A,mu n D P A/\A.card=4/\T⊆A)\/(∃ A zb,A≠zb/\mu n D P A/\mu n D P zb/\A.card=5/\zb.card=5/\T⊆A/\T⊆zb/\A∩zb=T):=by
 obtain⟨w,t⟩:=h;obtain⟨j,r,-,m,-,-,l⟩:=oR p P T (by omega) w t;have c:mu n D P (V n D (nX D j)∩P):=ow P _;have a:mu n D P (V n D (nL D j)∩P):=ow P _;rcases l with⟨x,i,g⟩|⟨-,i,g,k,-,-⟩
 . have b:(V n D (nX D j)∩P)∩(V n D (nL D j)∩P)=T:=by rw[<-m,mK p r x];ext v;simp only[A3];tauto
   generalize V n D (nX D j)∩P=A at c i b;generalize V n D (nL D j)∩P=zb at a g b;have e:=Bq i;have d:=Bq g;have z:(A∪zb).card<=7:=(Aa (Br (oY c) (oY a))).trans q;have f:=B2 A zb;rw[b] at f;by_cases o:A.card=4;. exact D6 (D5 ⟨A,c,o,i.subset⟩)
   by_cases o':zb.card=4;. exact D6 (D5 ⟨zb,a,o',g.subset⟩)
   refine D6 (D6 ⟨A,zb,?_,c,a,by omega,by omega,i.subset,g.subset,b⟩)
   intro hEq;rw[hEq,inter_self] at b;rw[b] at d;omega
 . generalize V n D (nX D j)∩P=A at c i k;generalize V n D (nL D j)∩P=zb at a g k;have e:=Bq i;have d:=Bq g;have s:=Co A zb;rw[k] at s;by_cases u:A.card=2
   . exact D5 ⟨A,c,u,i.subset⟩
   . exact D5 ⟨zb,a,by omega,g.subset⟩
lemma pV {T T' A:Sn n}(e:A.card=2)(c:A⊆T)(d:A⊆T')(a:T≠T'->(T∩T').card<=1):T=T':=by by_contra b;have g:=Aa (BE c d);have f:=a b;omega
lemma pZ {T T' A:Sn n}(d:T.card=3)(d':T'.card=3)(f:A.card=4)(c:T⊆A)(e:T'⊆A)(a:T≠T'->(T∩T').card<=1):T=T':=by by_contra b;have i:=Aa (Br c e);have g:=B2 T T';have h:=a b;omega
lemma r0 {T1 T2 T3 A:Sn n}(g:T1.card=3)(j:T2.card=3)(h:T3.card=3)(i:A.card<=5)(f:T1⊆A)(e:T2⊆A)(d:T3⊆A)(b:(T1∩T2).card<=1)(c:(T1∩T3).card<=1)(a:(T2∩T3).card<=1):False:=by
 have l:=Aa (Br (Br f e) d);have m:=B2 T1 T2;have k:=B2 (T1∪T2) T3;have o:((T1∪T2)∩T3).card<=(T1∩T3).card+(T2∩T3).card:=by rw[BN];exact Co _ _
 omega
lemma qt (hS:R n D){P:Sn n}(hP:P.card<=7)(d:I (Sn n))(o:∀ T∈d,T.card=3/\mu n D P T)(a:∀ T∈d,∀ T'∈d,T≠T'->(T∩T').card<=1):∃ Aux:I (Sn n),d.card<=Aux.card/\∀ A∈Aux,mu n D P A/\((A.card=2/\∃ T∈d,A⊆T)\/A.card=4\/A.card=5):=by
 classical
 let kq (A:Sn n):=(A.card=2/\∃ T∈d,A⊆T)\/A.card=4\/A.card=5;let Aux:=P.powerset.filter fun A=>mu n D P A/\kq A;let w (A T:Sn n):=if A.card=5 then(if T⊆A then 1 else 0) else(if A⊆T\/T⊆A then 2 else 0);refine⟨Aux,?_,fun A hA=>(O.mp hA).2⟩;have b:∀ A,mu n D P A->kq A->A∈Aux:=fun A v r=>O.mpr ⟨mem_powerset.mpr (oY v),v,r⟩;have g:∀ T∈d,2<=∑ A∈Aux,w A T:=fun T c=>by
  rcases pC hS hP (o T c).1 (o T c).2 with⟨A,ho,u,hs⟩|⟨A,ho,u,hs⟩|⟨A,zb,h7,hd,h8,y,s,h9,hf,-⟩;. exact le_trans (by simp[w,u,hs]) (Cp (fun _ _=>AU _) (b A ho (D5 ⟨u,T,c,hs⟩)))
  . exact le_trans (by simp[w,u,hs]) (Cp (fun _ _=>AU _) (b A ho (D6 (D5 u))))
  . have f:({A,zb}:I (Sn n))⊆Aux:=fun x hx=>by rcases A9.1 hx with rfl|hx;exact b _ hd (D6 (D6 y));rw[A5.1 hx];exact b _ h8 (D6 (D6 s))
    exact le_trans (by rw[sum_pair h7];simp[w,y,s,h9,hf]) (C5 f)
 have e:∀ A∈Aux,∑ T∈d,w A T<=2:=fun A hA=>by
  by_cases p:A.card=5
  . rw[show ∑ T∈d,w A T=(d.filter (fun T=>T⊆A)).card by rw[Bv];exact Bg rfl fun T _=>by simp[w,p]]
    by_contra m;have⟨T1,T2,T3,t,q,z,j,i,k⟩:=two_lt_card_iff.mp (show 2<(d.filter (fun T=>T⊆A)).card by omega)
    rw[O] at t q z;exact r0 (o _ t.1).1 (o _ q.1).1 (o _ z.1).1 p.le t.2 q.2 z.2 (a _ t.1 _ q.1 j) (a _ t.1 _ z.1 i) (a _ q.1 _ z.1 k)
  . rw[show ∑ T∈d,w A T=2*(d.filter (fun T=>A⊆T\/T⊆A)).card by rw[Bv,mul_sum];exact Bg rfl fun T _=>by simp[w,p]]
    have l:(d.filter (fun T=>A⊆T\/T⊆A)).card<=1:=card_le_one.mpr fun T c T' c'=>by
     rw[O] at c c';have c3:=(o T c.1).1;have c3':=(o T' c'.1).1;rcases (O.mp hA).2.2 with⟨r,-⟩|h4|p';. exact pV r (c.2.resolve_right fun h=>by have:=Aa h;omega) (c'.2.resolve_right fun h=>by have:=Aa h;omega) (a T c.1 T' c'.1)
     . exact pZ c3 c3' h4 (c.2.resolve_left fun h=>by have:=Aa h;omega) (c'.2.resolve_left fun h=>by have:=Aa h;omega) (a T c.1 T' c'.1)
     . exact Qa p' p
    omega
 have v:=card_nsmul_le_sum d _ 2 g;have r:=sum_le_card_nsmul Aux _ 2 e;rw[sum_comm] at v;simp only[smul_eq_mul] at v r;omega
lemma rt (u:R n D){P:Sn n}(v:P.card<=7)(g:I (Sn n))(i:∀ T∈g,T.card=3/\mu n D P T)(b:∀ T∈g,∀ T'∈g,T≠T'->(T∩T').card<=1)(j:I (Sn n))(k:∀ zm∈j,mu n D P zm/\2<=zm.card/\zm∉g/\zm.card≠4/\zm.card≠5/\(zm.card=2->∀ T∈g,¬ zm⊆T)):2*g.card+j.card<=(ot n D P).card:=by
 classical
 have⟨Aux,e,a⟩:=qt u v g i b;have f:Disjoint g Aux:=by rw[AG];intro T p s;have:=(i T p).1;rcases (a T s).2 with⟨h,-⟩|h|h<;>omega
 have c:Disjoint (g∪Aux) j:=by
  rw[AG];intro zm l m;have⟨_,_,q,t,o,r⟩:=k zm m;rcases AA.mp l with h|h;. exact q h
  . rcases (a zm h).2 with⟨y,T,p,x⟩|w|z
    . exact r y T p x
    . exact t w
    . exact o z
 have d:=pX u P ((g∪Aux)∪j) (by
  intro zm l;rcases AA.mp l with h|h
  . rcases AA.mp h with h|h
    . exact⟨by have:=(i zm h).1;omega,(i zm h).2⟩
    . refine⟨?_,(a zm h).1⟩;rcases (a zm h).2 with⟨h,-⟩|h|h<;>omega
  . exact⟨(k zm h).2.1,(k zm h).1⟩)
 rw[AJ c,AJ f] at d;omega
lemma qk {o:F n->F n->Prop}(t:mA o)(q:R n D)(r:mm n o D){P zu zx:Sn n}(g:zu⊆P)(hU:zu.card<=2\/(zu.card=3/\¬ mu n D P zu))(u:∀ a∈zx,∀ b∈zx,¬ o a b)(i:P \ zu⊆zx){f:F n}(p:f∈zu)(d:∃ a∈zx,o f a):∃ e,n3 n D P zu f e:=by
 have⟨j,s,w,ht,x,h2,y⟩:=pw t q r zx u f d;have c:V n D (E D (j,s))∩P⊆zu:=by intro v hv;rw[A3] at hv;by_contra l;exact AG.mp y hv.1 (i (Am.mpr ⟨hv.2,l⟩))
 refine⟨(j,s),w,ht,g p,x,h2,c,?_⟩;rcases hU with hU|⟨z,m⟩;. exact(Aa c).trans hU
 . have k:V n D (E D (j,s))∩P≠zu:=fun h=>m ⟨_,h⟩;have:=Bq (AV.mpr ⟨c,k⟩);omega
lemma o8 (c:R n D){P zu:Sn n}{f:F n}{e:Nat×Y}(h:n3 n D P zu f e):V n D (n+e.1)∩P⊆(V n D (E D e)∩P).erase f:=by have⟨d,g,_,_,i,_,_⟩:=h;intro v b;rw[A3] at b;rw[AN,A3];exact⟨fun a=>i (a▸b.1),n8 c d g e.2 b.1,b.2⟩
lemma qa {P zu:Sn n}{f:F n}{e:Nat×Y}(h:n3 n D P zu f e)(b:∀ zm,zm⊆zu->zm.card=2->f∈zm->¬ mu n D P zm):V n D (E D e)∩P={f}:=by obtain⟨-,-,g,i,-,d,k⟩:=h;have a:f∈V n D (E D e)∩P:=A3.mpr ⟨i,g⟩;have c:(V n D (E D e)∩P).card≠2:=fun j=>b _ d j a (ow P _);exact(DX (By.mpr a) (by rw[Bk];omega)).symm
lemma on {P:Sn n}{e a:Nat×Y}(h:ms n D P e=inl a):e=a/\V n D (n+e.1)∩P=∅:=by unfold ms at h;split_ifs at h with h0;exact⟨inl.inj h,h0⟩
lemma pA {P:Sn n}{e:Nat×Y}{j:Nat}(h:ms n D P e=inr j):e.1=j/\(V n D (n+e.1)∩P).Nonempty:=by unfold ms at h;split_ifs at h with h0;exact⟨inr.inj h,AE.mpr h0⟩
lemma rj (k:R n D){P zu:Sn n}{f:F n}{e:Nat×Y}(h:n3 n D P zu f e):ql n D P (ms n D P e):=by
 have b:=o8 k h;obtain⟨j,o,l,q,-,-,r⟩:=h;have c:f∈V n D (E D e)∩P:=A3.mpr ⟨q,l⟩;unfold ms;split_ifs with h0;. show e∈mt n D (S n D P)/\(V n D (E D e)∩P).card<=2;refine⟨?_,r⟩;rw[mt,O];refine⟨CD.mpr ⟨Ac.mpr j,AC _⟩,n1.mpr ⟨f,c⟩,?_⟩;rw[n1,h0];exact AS
 . show e.1∈mI n D (S n D P)/\(V n D (n+e.1)∩P).card=1;have a:(V n D (n+e.1)∩P).Nonempty:=AE.mpr h0;have d:=Aa b;rw[E9 c] at d;have g:=Bc.mpr a;refine⟨?_,by omega⟩;have⟨v,i⟩:=a;rw[A3] at i;have m:=n8 k j o J i.1;have p:=n8 k j o H i.1;rw[mq] at m;rw[mx] at p;rw[mI,O,Ac];exact⟨j,n1.mpr ⟨v,A3.mpr i⟩,n1.mpr ⟨v,A3.mpr ⟨m,i.2⟩⟩,n1.mpr ⟨v,A3.mpr ⟨p,i.2⟩⟩⟩
lemma pK (i:R n D){P zu zu':Sn n}{f f':F n}{e:Nat×Y}(h:n3 n D P zu f e)(h':n3 n D P zu' f' e)(b:(V n D (n+e.1)∩P).Nonempty):f=f':=by
 by_contra c;have⟨q,j⟩:=b;have g:=o8 i h j;have k:=o8 i h' j;rw[AN] at g k;have a:({q,f,f'}:Sn n)⊆V n D (E D e)∩P:=by
  intro x d;simp only[A9,A5] at d;rcases d with d|d|d<;>rw[d]
  . exact g.2
  . exact A3.mpr ⟨h.2.2.2.1,h.2.2.1⟩
  . exact A3.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩
 have l:=Aa a;have m:({q,f,f'}:Sn n).card=3:=by rw[Al,DY c];simp only[A9,A5,not_or];exact⟨g.1,k.1⟩
 have:=h.2.2.2.2.2.2;omega
lemma nA (g:R n D){P zu zu':Sn n}{f f':F n}{e e':Nat×Y}(h:n3 n D P zu f e)(h':n3 n D P zu' f' e')(c:V n D (E D e)∩P={f})(b:f≠f'):ms n D P e≠ms n D P e':=by
 intro heq;have j:V n D (n+e.1)∩P=∅:=by have a:=o8 g h;rw[c,erase_singleton] at a;exact subset_empty.mp a
 have i:ms n D P e=inl e:=(by simp[ms,j]);rw[i] at heq;have k:=(on heq.symm).1;subst k;have d:f'∈V n D (E D e')∩P:=A3.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩;rw[c,A5] at d;exact b d.symm
lemma qW (q:R n D){P:Sn n}(Lab:Sn n)(p:F n->Sn n)(a:F n->Nat×Y)(b:∀ f∈Lab,n3 n D P (p f) f (a f))(c:(Nat×Y) ⊕ Nat):(Lab.filter (fun f=>ms n D P (a f)=c)).card<=2:=by
 rcases c with u|s
 . by_cases g:(Lab.filter (fun f=>ms n D P (a f)=inl u)).Nonempty
   . obtain⟨r,e⟩:=g;rw[O] at e;have d:=(b r e.1).2.2.2.2.2.2;rw[(on e.2).1] at d;refine le_trans (Aa ?_) d;intro f l;rw[O] at l;have m:=b f l.1;rw[(on l.2).1] at m;exact A3.mpr ⟨m.2.2.2.1,m.2.2.1⟩
   . rw[BM] at g;rw[g];simp
 . have h:Eb (fun f=>(a f).2) (Lab.filter (fun f=>ms n D P (a f)=inr s):Set (F n)):=by intro f l f' l' hs;rw[mem_coe,O] at l l';have⟨o,i⟩:=pA l.2;obtain⟨o',-⟩:=pA l'.2;have k:a f=a f':=Prod.ext (o.trans o'.symm) hs;have m':=b f' l'.1;rw[<-k] at m';exact pK q (b f l.1) m' i
   have j:=card_le_card_of_injOn (t:=(univ:I Y)) (fun f=>(a f).2) (fun _ _=>AC _) h;simpa using j
lemma qM (e:R n D){P:Sn n}(Lab:Sn n)(d:F n->Sn n)(a:F n->Nat×Y)(b:∀ f∈Lab,n3 n D P (d f) f (a f)):Lab.card<=2*(Lab.image (fun f=>ms n D P (a f))).card:=E0 Lab 2 (fun c _=>qW e Lab d a b c)
lemma pb (k:R n D){P:Sn n}(Lab vs:Sn n)(o:F n->Sn n)(a:F n->Nat×Y)(b:∀ f∈Lab,n3 n D P (o f) f (a f))(e:vs⊆Lab)(d:∀ f∈vs,V n D (E D (a f))∩P={f}):2*vs.card+(Lab \ vs).card <=2*(Lab.image (fun f=>ms n D P (a f))).card:=by
 have p:(vs.image (fun f=>ms n D P (a f))).card=vs.card:=Bj (fun f j f' j' g=>by
  by_contra i;exact nA k (b f (e j)) (b f' (e j')) (d f j) i g)
 have s:=qM k (Lab \ vs) o a (fun f j=>b f (Am.mp j).1);have r:Disjoint (vs.image (fun f=>ms n D P (a f))) ((Lab \ vs).image (fun f=>ms n D P (a f))):=by rw[AG];intro c m l;obtain⟨f,j,rfl⟩:=A7.mp m;obtain⟨f',j',g⟩:=A7.mp l;rw[Am] at j';exact nA k (b f (e j)) (b f' j'.1) (d f j) (fun h=>j'.2 (h▸j)) g.symm
 have q:(vs.image (fun f=>ms n D P (a f))∪(Lab \ vs).image (fun f=>ms n D P (a f))).card <= (Lab.image (fun f=>ms n D P (a f))).card :=
  Aa (Br (E8 e) (E8 Cw))
 rw[AJ r,p] at q;omega
lemma q4 (P:Sn n)(g:I (Nat×Y))(q:∀ e∈g,e∈mt n D (S n D P))(f:I ((Nat×Y) ⊕ Nat))(l:∀ c∈f,ql n D P c)(d:Disjoint g f.toLeft):(ot n D P).card+g.card+f.card <=(mt n D (S n D P)).card+(mI n D (S n D P)).card:=by
 have r:∀ e∈f.toLeft,e∈mt n D (S n D P)/\(V n D (E D e)∩P).card<=2:=fun e k=>l _ (mem_toLeft.mp k);have o:∀ j∈f.toRight,j∈mI n D (S n D P)/\(V n D (n+j)∩P).card=1:=fun j i=>l _ (mem_toRight.mp i);have m:g.card+f.toLeft.card<=(mt n D (S n D P)).card:=by
  rw[<-AJ d];refine Aa (fun e k=>?_);rcases AA.mp k with h|h;. exact q e h
  . exact(r e h).1
 have p:(ot n D P).card+f.toRight.card<=(mI n D (S n D P)).card:=by
  rw[<-AJ]
  . refine Aa (fun j i=>?_)
    rcases AA.mp i with h|h;. exact(O.mp h).1
    . exact(o j h).1
  . rw[AG];intro j m p;have a:=(O.mp m).2;have b:=(o j p).2;omega
 have s:=card_toLeft_add_card_toRight (u:=f);omega
lemma qp (m:R n D)(P:Sn n)(j:I (Nat×Y))(p:∀ e∈j,e∈mt n D (S n D P))(Lab vs:Sn n)(l:F n->Sn n)(a:F n->Nat×Y)(d:∀ f∈Lab,n3 n D P (l f) f (a f))(h:vs⊆Lab)(g:∀ f∈vs,V n D (E D (a f))∩P={f})(hdis:∀ e∈j,∀ f∈Lab,e≠a f):2*((ot n D P).card+j.card)+2*vs.card+(Lab \ vs).card <=2*((mt n D (S n D P)).card+(mI n D (S n D P)).card):=by
 have r:=pb m Lab vs l a d h g;have hdis':Disjoint j (Lab.image (fun f=>ms n D P (a f))).toLeft:=by
  rw[AG];intro e q o;rw[mem_toLeft,A7] at o;have⟨f,k,b⟩:=o;have i:a f=e:=by
   unfold ms at b;split at b;. exact inl.inj b
   . exact Qa b (by simp)
  exact hdis e q f k i.symm
 have s:=q4 P j p (Lab.image (fun f=>ms n D P (a f))) (by
  intro c hc;obtain⟨f,k,rfl⟩:=A7.mp hc;exact rj m (d f k)) hdis'
 omega
end SupMask
def oH (n:Nat)(c:F n->F n->Prop)(D:N)(b:F n->Nat×Y):Prop:=(∀ i∈U n D,(b i).1<D.length/\V n D (n+(b i).1)=∅/\(∀ a,c i a->a∈V n D (E D (b i)))/\V n D (E D ((b i).1,!(b i).2))={i})/\∀ i∈U n D,∀ i'∈U n D,b i=b i'->i=i'
lemma oJ {n:Nat}{d:F n->F n->Prop}{D:N}(j:mA d)(h:m7 n D)(g:mm n d D):∃ pos:F n->Nat×Y,oH n d D pos:=by
 classical
 have b:∀ i:F n,∃ e:Nat×Y,i∈U n D->(e.1<D.length/\V n D (n+e.1)=∅/\(∀ a,d i a->a∈V n D (E D e))/\V n D (E D (e.1,!e.2))={i}):=by
  intro i;by_cases c:i∈U n D;. obtain⟨e,f,-,k,o,p,-,-⟩:=nd j h g c;exact⟨(e.1,!e.2),fun _=>⟨f,o,p,by simpa using k⟩⟩
  . exact⟨(0,J),fun l=>Qa l c⟩
 choose pos hpos using b;refine⟨pos,hpos,fun i c i' c' m=>?_⟩
 have f:=(hpos i c).2.2.2;rw[m,(hpos i' c').2.2.2] at f;exact(C7 f).symm
lemma sn {n:Nat}{D:N}(f:R n D)(c:I Nat)(d:∀ b∈c,2<=K D b/\V n D b=∅):c.card<=oL n D:=by
 have a:c⊆(nc n D).filter (fun w=>¬(V n D w).Nonempty):=fun b e=>qz f (d b e).1 (d b e).2;calc c.card=∑ _w∈c,1:=by simp
  _<=∑ w∈c,(K D w-1):=sum_le_sum (fun w g=>by have:=(d w g).1;omega)
  _<=oL n D:=C5 a
lemma rM {n:Nat}{D:N}(hS:R n D){P:Sn n}(hP:P.card<=7)(L3:I (Sn n))(x:∀ T∈L3,T.card=3/\mu n D P T)(k:∀ T∈L3,∀ T'∈L3,T≠T'->(T∩T').card<=1)(L2:I (Sn n))(h2:∀ zm∈L2,zm.card=2/\mu n D P zm/\∀ T∈L3,¬ zm⊆T)(v:I (Nat×Y))(hE:∀ e∈v,e∈mt n D (S n D P))(Lab:Sn n)(u:F n->Sn n)(hw:∀ f∈Lab,∃ e,n3 n D P (u f) f e)(i:∀ f∈Lab,∀ T∈L3,(u f∩T).card<=1)(j:∀ f∈Lab,∀ zm∈L2,(u f∩zm).card<=1)(d:∀ e∈v,∀ f∈Lab,∀ w,n3 n D P (u f) f w->e≠w):2*L3.card+L2.card+v.card+Lab.card <=(mt n D (S n D P)).card+(mI n D (S n D P)).card:=by
 classical
 choose! wit hwit using hw;let t:=Lab.filter fun f=>∀ zm,zm⊆u f->zm.card=2->f∈zm->¬ mu n D P zm;have h:t⊆Lab:=Cq _ _;have o:∀ f∈Lab \ t,∃ zm,zm⊆u f/\zm.card=2/\f∈zm/\mu n D P zm:=fun f p=>by rw[Am,O] at p;by_contra hc;exact p.2 ⟨p.1,fun zm y h2 h4 h5=>hc ⟨zm,y,h2,h4,h5⟩⟩
 choose! pr hpr using o;have c:Disjoint L2 ((Lab \ t).image pr):=AG.mpr fun zm b s=>by obtain⟨f,p,rfl⟩:=A7.1 s;have:=Aa (BE (hpr f p).1 (Subset.refl _));have:=(hpr f p).2.1;have:=j f (Am.1 p).1 _ b;omega
 have hX:=rt hS hP L3 x k (L2∪(Lab \ t).image pr) fun zm hM=>by
  rcases AA.1 hM with b|s;. obtain⟨hc,ho,m⟩:=h2 zm b;exact⟨ho,by omega,fun z=>by have:=(x _ z).1;omega,by omega,by omega,fun _=>m⟩
  . obtain⟨f,p,rfl⟩:=A7.1 s;obtain⟨y,h2',-,h4⟩:=hpr f p;exact⟨h4,by omega,fun z=>by have:=(x _ z).1;omega,by omega,by omega,fun _ T hT a=>by have:=Aa (BE y a);have:=i f (Am.1 p).1 T hT;omega⟩
 rw[AJ c] at hX;have r:=qp hS P v hE Lab t u wit hwit h (fun f p=>qa (hwit f (h p)) (O.1 p).2) (fun e he f p=>d e he f p (wit f) (hwit f p));have q:(Lab \ t).card<=2*((Lab \ t).image pr).card:=E0 _ 2 fun zm _=>by
  by_cases l:((Lab \ t).filter fun f=>pr f=zm).Nonempty;. have⟨g,hg⟩:=l;rw[O] at hg;have b:zm.card=2:=hg.2▸(hpr g hg.1).2.1;rw[<-b];exact Aa fun f p=>by rw[O] at p;exact p.2▸(hpr f p.1).2.2.1
  . rw[BM.1 l];simp
 have:=BK h;omega
def q7:S2:=univ.filter (fun a=>6<=a.val)
lemma oZ:∀ a b:B,ma a b=H->decide (a.val<6)≠decide (b.val<6):=by decide +kernel
lemma pS:∀ a∈q7,∀ b∈q7,¬ oF a b:=by intro a ha b hb hab;simp only[q7,O,AC,true_and] at ha hb;have c:=oZ a b ((mj a b).mpr hab);have d:decide (a.val<6)=J:=BW (by omega);have e:decide (b.val<6)=J:=BW (by omega);rw[d,e] at c;exact c rfl
lemma nf (u v:B)(h:u≠v)(P:S2):((m5 u∩P)∩(m5 v∩P)).card<=1:=by
 refine le_trans (Aa (fun z a=>?_)) (pF u v h)
 simp only[A3,m5,O,AC,true_and] at a;exact O.mpr ⟨AC z,a.1.1,a.2.1⟩
lemma rX {D:N}(h:m7 12 D)(x:mB D)(P:S2)(w:∀ a∈P,∀ b∈P,¬ oF a b)(o:S2)(p:∀ i∈o,i∈U 12 D/\m5 i⊆P/\¬ mu 12 D P (m5 i)):o.card<=oL 12 D:=by
 classical
 have v:=s5;have u:=mG x;have c:∀ i∈o,∀ q,(∀ a∈P,(a∈V 12 D q↔oF i a))->False:=by intro i l q n;refine(p i l).2.2 ⟨q,?_⟩;ext a;rw[A3,s8];exact⟨fun m=>(n a m.2).1 m.1,fun m=>⟨(n a ((p i l).2.1 (s8.2 m))).2 m,(p i l).2.1 (s8.2 m)⟩⟩
 have r:∀ i∈o,∃ b,md 12 D i.val b/\2<=K D b/\V 12 D b=∅:=by
  intro i l;rcases pN v h u (p i l).1 with t|r;. obtain⟨j,s,-,-,-,n⟩:=qm v h.1 u P w t;exact(c i l _ n).elim
  . exact r
 choose! β hβ using r;have e:Eb β o:=by intro i l j hj hij;by_contra f;obtain⟨a,d,g⟩:=nN j i (Du f);obtain⟨k,s,-,-,-,-,n⟩:=pL v h.1 u P w (hβ i l).1 (mX h.1 (hij▸(hβ j hj).1)) ⟨a,(p j hj).2.1 (s8.2 d),d,g⟩;exact c i l _ n
 rw[<-Bj e];refine sn h.1 _ (fun b r=>?_);obtain⟨i,l,rfl⟩:=A7.1 r;exact(hβ i l).2
lemma rF {D:N}(h:m7 12 D)(hD:mB D)(P:S2)(t:P⊆q7)(h7:P⊆mb 12 D)(Oc3 Oc2 Ct Iin:S2)(o:∀ i∈Oc3,m5 i⊆P/\(m5 i).card=3/\mu 12 D P (m5 i))(l:∀ i∈Oc2,m5 i⊆P/\(m5 i).card=2/\mu 12 D P (m5 i))(q:∀ c∈Ct,c∉Oc3/\c∉Oc2/\(m5 c⊆P->¬ mu 12 D P (m5 c)))(d:∀ i∈Iin,i∈U 12 D/\m5 i⊆P):2*Oc3.card+Oc2.card+Iin.card+(Ct.biUnion (fun c=>m5 c∩P)).card+(mb 12 D).card<=2*P.card+nh 12 D:=by
 classical
 have hG:=s5;have hC:=mG hD;have⟨b,hb⟩:=mZ h hD;obtain⟨h3,p⟩:=oJ hG h hC;have h9:∀ a∈P,∀ b∈P,¬ oF a b:=fun a ha b hb=>pS a (t ha) b (t hb);have x:Eb h3 Iin:=fun i hi j hj g=>p.2 i (d i hi).1 j (d j hj).1 g;have hE:∀ e∈Iin.image h3,e∈mt 12 D (S 12 D P):=fun e he=>by
  obtain⟨i,hi,rfl⟩:=A7.1 he;obtain⟨hj,ho,hv,-⟩:=p.1 i (d i hi).1;have v:(m5 i).Nonempty:=Bc.1 (by rcases mQ i with h1|h1<;>omega);obtain⟨a,ha⟩:=v;rw[mt,O];exact⟨CD.2 ⟨Ac.2 hj,AC _⟩,n1.2 ⟨a,A3.2 ⟨hv a (s8.1 ha),(d i hi).2 ha⟩⟩,by rw[n1,ho,empty_inter];exact AS⟩
 choose! ct hct using fun f (hf:f∈Ct.biUnion fun c=>m5 c∩P)=>C6.1 hf
 have u:=rM h.1 ((Aa t).trans (by decide)) (Oc3.image m5) (fun T hT=>by obtain⟨i,hi,rfl⟩:=A7.1 hT;exact⟨(o i hi).2.1,(o i hi).2.2⟩) (fun T hT T' hT' v=>by obtain⟨i,hi,rfl⟩:=A7.1 hT;obtain⟨j,hj,rfl⟩:=A7.1 hT';simpa[m5] using nf i j (fun g=>v (g▸rfl)) univ) (Oc2.image m5) (fun zm hM=>by
  obtain⟨i,hi,rfl⟩:=A7.1 hM;refine⟨(l i hi).2.1,(l i hi).2.2,fun T hT m=>?_⟩;obtain⟨j,hj,rfl⟩:=A7.1 hT;have y:=nf i j (fun g=>by have:=(l i hi).2.1;have:=(o j hj).2.1;rw[g] at *;omega) univ
  have:=Aa (BE (Subset.refl _) m);have:=(l i hi).2.1;simp only[inter_univ] at y;omega)
  (Iin.image h3) hE (Ct.biUnion (fun c=>m5 c∩P)) (fun f=>m5 (ct f)∩P)
  (fun f hf=>by
   obtain⟨hc,h6⟩:=hct f hf;set c:=ct f;refine qk hG h.1 hC (zx:=insert c (P \ (m5 c∩P))) Bm ?_ ?_ (fun a ha=>A2 ha) h6 ⟨c,AL _ _,oS (s8.1 (A3.1 h6).1)⟩
   . by_cases k:m5 c⊆P
     . rcases mQ c with hx|hq;exact D5 (by rw[Bb.2 k];omega);rw[Bb.2 k];exact D6 ⟨hq,(q _ hc).2.2 k⟩
     . have hm:(m5 c∩P).card<(m5 c).card:=Bq (AV.2 ⟨B9,fun z=>k (z▸Bm)⟩);rcases mQ c with hx|hq<;>exact D5 (by omega)
   . have h1:∀ a∈P \ (m5 c∩P),¬ oF c a:=fun a ha hp=>by rw[Am,A3,s8] at ha;exact ha.2 ⟨hp,ha.1⟩
     intro a ha b hb;rcases A9.1 ha with rfl|ha<;>rcases A9.1 hb with rfl|hb;exact pm _;exact h1 _ hb;exact fun hk=>h1 _ ha (oS hk);exact h9 _ (Am.1 ha).1 _ (Am.1 hb).1)
  (fun f hf T hT=>by obtain⟨i,hi,rfl⟩:=A7.1 hT;have:=nf (ct f) i (fun g=>(q _ (hct f hf).1).1 (g▸hi)) P;rwa[Bb.2 (o i hi).1] at this)
  (fun f hf zm hM=>by obtain⟨i,hi,rfl⟩:=A7.1 hM;have:=nf (ct f) i (fun g=>(q _ (hct f hf).1).2.1 (g▸hi)) P;rwa[Bb.2 (l i hi).1] at this)
  (fun e he f hf w hw hg=>by
   obtain⟨i,hi,rfl⟩:=A7.1 he;obtain⟨hc,-⟩:=hct f hf;have s:m5 i⊆V 12 D (E D (h3 i))∩P:=fun a ha=>A3.2 ⟨(p.1 i (d i hi).1).2.2.1 a (s8.1 ha),(d i hi).2 ha⟩;have n:V 12 D (E D (h3 i))∩P⊆m5 (ct f)∩P:=hg▸hw.2.2.2.2.2.1;by_cases r:ct f=i;. rw[r,Bb.2 (d i hi).2] at n;have z:V 12 D (E D (h3 i))∩P=m5 i:=Subset.antisymm n s;exact(q (ct f) hc).2.2 (r▸(d i hi).2) ⟨E D (h3 i),r▸z⟩
   . have y:=nf i (ct f) (Du r) P;rw[Bb.2 (d i hi).2] at y;have:=Aa (BE (Subset.refl _) (s.trans n));rcases mQ i with hd|hd<;>omega)
 have h4:=nm h P (by rw[qS hD];simp);have h5:=pa h.1 b hb P;rw[Bb.2 h7] at h5;rw[Au _ (fun i j g=>qj g),Au _ (fun i j g=>qj g),Bj x] at u;omega
abbrev sj:B->B->Prop:=fun u v=>oF u v
def ru (D:N)(b:B->Nat)(x:B):I (Σ _:Nat,Nat):=(mi 12 D b).filter (fun u=>x∈V 12 D u.1)
lemma sl {D:N}(h:m7 12 D)(c:mB D)(b:B->Nat)(a:mw 12 D b)(x:B):(C 12 D x).card+(mI 12 D (S 12 D {x})).card<=2+(ru D b x).card:=by have e:=oN s5 h (mG c) b a x;have d:=Aa (B9:({x}:S2)∩mb 12 D⊆{x});rw[Bk] at d;unfold ru;omega
lemma rA {n:Nat}{D:N}(b:R n D){x:F n}{e:Nat×Y}(c:e∈C n D x):mn e∉C n D x:=by
 intro hb;have⟨d,a,f⟩:=s4.mp c;have a':=(s4.mp hb).2.1;apply f;rw[mK b d (qI b c),A3];obtain⟨j,s⟩:=e;cases s;. exact⟨by simpa[E] using a,by simpa[E,mn] using a'⟩
 . exact⟨by simpa[E,mn] using a',by simpa[E] using a⟩
lemma nr {D:N}{d:B->Nat×Y}(b:oH 12 sj D d){i a:B}(e:i∈U 12 D)(c:oF i a):d i∈C 12 D a:=by have⟨g,h,f,_⟩:=b.1 i e;exact s4.2 ⟨g,f a c,by rw[h];exact Bd a⟩
lemma qV {D:N}{b:B->Nat×Y}(a:oH 12 sj D b){i t:B}(d:i∈U 12 D)(c:mn (b i)∈C 12 D t):t=i:=by have:=(s4.1 c).2.1;rw[show E D (mn (b i))=E D ((b i).1,!(b i).2) from rfl,(a.1 i d).2.2.2] at this;exact A5.1 this
lemma oh {α:Type}[DecidableEq α]{s:I α}{a b c:α}(j:a∈s)(k:b∈s)(i:c∈s)(h:a≠b)(g:a≠c)(f:b≠c):3<=s.card:=by
 have d:({a,b,c}:I α)⊆s:=by intro e he;simp only[A9,A5] at he;rcases he with rfl|rfl|rfl<;>assumption
 have:=Aa d;rwa[Al (by simp[h,g]),DY f] at this
lemma o3 {α:Type}[DecidableEq α]{s:I α}{a b c:α}(j:a∈s)(k:b∈s)(i:c∈s)(h:a≠b)(g:a≠c)(f:b≠c)(l:s.card<=3):∀ e∈s,e=a\/e=b\/e=c:=by
 intro e he;by_contra d;rw[not_or,not_or] at d;have:=oh (s:=s.erase e) (AN.2 ⟨Du d.1,j⟩) (AN.2 ⟨Du d.2.1,k⟩) (AN.2 ⟨Du d.2.2,i⟩)
  h g f
 rw[E9 he] at this;omega
lemma sr {α:Type}[DecidableEq α]{s:I α}{a b:α}(f:a∈s)(g:b∈s)(d:a≠b)(h:s.card<=2):∀ e∈s,e=a\/e=b:=by intro e he;by_contra c;rw[not_or] at c;have:=oh he f g c.1 c.2 d;omega
lemma q9 {D:N}(h:m7 12 D)(k:mB D){d:B->Nat×Y}(a:oH 12 sj D d){x y:B}(c:oF x y):∃ e∈C 12 D x,mn e∈C 12 D y/\(∀ i∈U 12 D,e=d i->y=i)/\∀ i∈U 12 D,mn e=d i->x=i:=by obtain⟨e,g,j,-⟩:=qr s5 h.1 (mG k) c;exact⟨e,g,j,fun i f b=>qV a f (b▸j),fun i f b=>qV a f (by rw[<-b,mJ];exact g)⟩
lemma qd:∀ x a b:B,(mH x).card=3->x≠a->x≠b->ma a b=J->∃ y,ma x y=H/\ma y a=J/\ma y b=J:=by decide +kernel
lemma pc {D:N}(h:m7 12 D)(i:mB D){x a b:B}(g:(mH x).card=3)(d:x≠a)(f:x≠b)(c:¬ oF a b):∃ e,e∈C 12 D x/\a∉V 12 D (E D e)/\b∉V 12 D (E D e):=by have⟨y,j,k,l⟩:=qd x a b g d f (sb.mpr c);exact oW s5 h.1 (mG i) c ((mj x y).mp j) (sb.mp k) (sb.mp l)
lemma q5 {D:N}(h:m7 12 D)(v:mB D){q:B->Nat×Y}(b:oH 12 sj D q){i x:B}(u:i∈U 12 D)(d:oF i x)(j:(mH x).card=3)(hc:(C 12 D x).card<=2):∃ zz,zz≠q i/\C 12 D x={q i,zz}/\∀ t,t≠x->decide (t.val<6)=decide (x.val<6)->zz∉C 12 D t:=by
 have⟨r,c,e⟩:=s5.2.2.2 i x;obtain⟨zz,hZ,n⟩:=qE s5 h.1 (mG v) (x:=x) (a:=r) (Du e);have hY:q i∈C 12 D x:=nr b u d;have g:zz≠q i:=fun o=>n (o▸(b.1 i u).2.2.1 r c);have y:C 12 D x={q i,zz}:=by
  symm;refine DX (fun f s=>?_) ?_
  . rw[A9,A5] at s;rcases s with rfl|rfl
    . exact hY
    . exact hZ
  . rw[DY (Du g)];exact hc
 refine⟨zz,g,y,fun t k p m=>?_⟩
 have l:¬ oF r t:=by
  intro hadj;have s1:=oZ i x ((mj i x).2 d);have s2:=oZ i r ((mj i r).2 c);have s3:=oZ r t ((mj r t).2 hadj);cases w:decide (i.val<6)<;>cases z:decide (x.val<6)<;>
   cases h3:decide (r.val<6)<;>cases h4:decide (t.val<6)<;>simp_all
 have⟨f,s,w,z⟩:=pc h v j (Du e) (Du k) l;rw[y,A9,A5] at s;rcases s with rfl|rfl;. exact w ((b.1 i u).2.2.1 r c)
 . exact z (s4.1 m).2.1
lemma r9 {D:N}(h:m7 12 D)(w:mB D){l:B->Nat×Y}(a:oH 12 sj D l){k j u v:B}(c:k∈U 12 D)(b:j∈U 12 D)(x:k≠j/\ma k u=H/\ma j u=H/\ma u v=H/\v≠k/\v≠j):3<=(C 12 D u).card:=by
 have⟨i,p,t,n,f,g⟩:=x;rw[mj] at p t n;have s:=nr a c p;have r:=nr a b t;have d:l k≠l j:=fun e=>i (a.2 k c j b e);by_cases m:v∈U 12 D;. exact oh s r (nr a m (oS n)) d (fun e=>f.symm (a.2 k c v m e)) (fun e=>g.symm (a.2 j b v m e))
 . have⟨e,y,_,q,_⟩:=q9 h w a n;exact oh s r y d (fun o=>m (q k c o.symm▸c)) (fun o=>m (q j b o.symm▸b))
lemma sm {D:N}(h:m7 12 D)(j:mB D){l:B->Nat×Y}(a:oH 12 sj D l)(z k v i m:B)(b:i∈U 12 D)(d:m∈U 12 D)(x:z∉U 12 D)(hk:k∉U 12 D)(y:v∉U 12 D)(hg:ma i z=H/\ma m k=H/\ma z k=H/\ma z v=H/\v≠k/\(mH k).card=3/\decide (v.val<6)=decide (k.val<6))(f:(C 12 D z).card<=2)(g:(C 12 D k).card<=2):False:=by
 have⟨w,t,u,s,g5,g6,g7⟩:=hg;rw[mj] at w t u s;obtain⟨Dk,-,p,r⟩:=q5 h j a d t g6 g;obtain⟨e,n,c,o,o'⟩:=q9 h j a u;obtain⟨e',n',c',hg',-⟩:=q9 h j a s;rw[p,A9,A5] at c;have hb:mn e=Dk:=c.resolve_left (fun q=>x (o' m d q▸d));rcases sr (nr a b w) n (fun q=>hk (o i b q.symm▸b)) f e' n' with h1|h1;. exact y (hg' i b h1▸b)
 . exact r v g5 g7 (by rw[<-hb,<-h1];exact c')
def tight_witTab:Z (Y×Nat×Nat×Nat×Nat×Nat):=[(H,0,0,0,0,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(J,1,10,11,6,2),(H,1,3,11,0,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(H,0,1,11,3,0),(J,1,10,11,6,2),(J,1,11,6,10,0),(H,1,3,11,0,0),(H,1,3,11,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0),(H,0,0,0,0,0)]
def rB (n:Fin 33):Y×B×B×B×B×B:=let t:=tight_witTab.getD n.val (H,0,0,0,0,0);(t.1,Fin.ofNat 12 t.2.1,Fin.ofNat 12 t.2.2.1,Fin.ofNat 12 t.2.2.2.1,Fin.ofNat 12 t.2.2.2.2.1,Fin.ofNat 12 t.2.2.2.2.2)
lemma rP:∀ n:Fin 33,3<=(nC n).card->let w:=rB n
 if w.1 then
  let i1:=w.2.1;let i2:=w.2.2.1;let u:=w.2.2.2.1;let v:=w.2.2.2.2.1
  i1∈nC n/\i2∈nC n/\i1≠i2/\ma i1 u=H/\
  ma i2 u=H/\ma u v=H/\v≠i1/\v≠i2
 else
  let z:=w.2.1;let k:=w.2.2.1;let v:=w.2.2.2.1;let iz:=w.2.2.2.2.1;let ik:=w.2.2.2.2.2
  iz∈nC n/\ik∈nC n/\z∉nC n/\k∉nC n/\v∉nC n/\
  ma iz z=H/\ma ik k=H/\ma z k=H/\
  ma z v=H/\v≠k/\(mH k).card=3/\
  decide (v.val<6)=decide (k.val<6):=by decide +kernel
lemma ol {D:N}(h:m7 12 D)(l:mB D)(w:nh 12 D<=(mb 12 D).card)(r:U 12 D∈mY)(d:3<=(U 12 D).card):False:=by
 classical
 obtain⟨b,q⟩:=mZ h l;obtain⟨v,a⟩:=oJ s5 h (mG l);have e:mi 12 D b=∅:=by have m:=nH h.1 b q;have z:=pj h.1 b q;exact BF.1 (by omega)
 have c:∀ x,(C 12 D x).card<=2:=fun x=>by
  have m:=sl h l b q x;unfold ru at m;rw[e] at m;simp only[filter_empty,CH] at m;omega
 have⟨n,_,k⟩:=oc r;rw[<-k] at d;have o:=rP n d;dsimp only at o;split at o;. obtain⟨j,f,p⟩:=o;have y:=r9 h l a (k▸j) (k▸f) p;have:=c (rB n).2.2.2.1;omega
 . obtain⟨i,g,s,u,t,p⟩:=o;exact sm h l a _ _ _ _ _ (k▸i) (k▸g) (k▸s) (k▸u) (k▸t) p (c _) (c _)
def countOrbits:Z (S2):=[{0,1,2,3,4,5},{0,1,2,3,4},{0,1,2,5,8},{0,1,3,4,5},{0,1,2,3},{0,1,2,5},{0,1,2,8},{0,1,3,4},{0,1,4,9},{0,1,5,8},{1,3,4,5}]
def nb (k:Fin 6):B:=⟨k.val,by omega⟩
lemma nW:Function.Injective nb:=by decide
def oP (m:Fin 64):I (Fin 6):=univ.filter (fun k:Fin 6=>m.val.testBit k.val)
lemma q3 (d:I (Fin 6)):∃ m:Fin 64,oP m=d:=by
 classical
 induction d using Finset.induction_on with
 | empty=>exact⟨0,by ext k;simp[oP]⟩
 | insert a s _ e=>
   obtain⟨m,f⟩:=e;have b:2 ^ a.val < 2 ^ 6:=Cr (by omega) a.isLt;refine⟨⟨m.val|||2 ^ a.val,C9 m.isLt b⟩,?_⟩;ext k;simp only[oP,O,AC,true_and,Ay,Cx,Ai,A6,A9];have c:m.val.testBit k.val=H↔k∈s:=by have:=Finset.ext_iff.1 f k;simpa[oP] using this
   rw[c,Fin.ext_iff];tauto
lemma qe:∀ idx:Fin 11,∀ m:Fin 64,let zi:=countOrbits.getD idx.val ∅
 let Oc:=oP m
 let P:=q7 \ zi
 (∀ k∈Oc,mH (nb k)⊆P)->
 let Oc3:=Oc.filter (fun k=>(mH (nb k)).card=3)
 let Oc2:=Oc.filter (fun k=>(mH (nb k)).card=2)
 let Iin:=univ.filter (fun k:Fin 6=>nb k∈zi/\mH (nb k)⊆P)
 let Ct:=univ \ Oc
 let Lab:=Ct.biUnion (fun k=>mH (nb k)∩P)
 (2*P.card+9<2*Oc3.card+Oc2.card+Iin.card+Lab.card+(12-zi.card)+(Iin \ Oc).card)\/
 (9<(13-zi.card)+(Iin \ Oc).card):=by decide +kernel
lemma qA {D:N}(h:m7 12 D)(hD:mB D)(h9:me 12 D<=9)(hI:U 12 D∈mY)(y:3<=(U 12 D).card)(t:U 12 D∈countOrbits):False:=by
 classical
 have h5:(mb 12 D).card+1<=nh 12 D:=by by_contra h7;exact ol h hD (by omega) hI y
 set zi:=U 12 D with hIdef;set P:=q7 \ zi;have p:P⊆q7:=Cw;have h4:P⊆mb 12 D:=fun a ha=>by by_contra h0;exact(Am.1 ha).2 (sa.2 h0)
 let Oc:=univ.filter fun k:Fin 6=>mH (nb k)⊆P/\mu 12 D P (m5 (nb k));let Oc3:=Oc.filter fun k=>(mH (nb k)).card=3;let Oc2:=Oc.filter fun k=>(mH (nb k)).card=2;let Ct:=(univ:I (Fin 6)) \ Oc;let Iin:=univ.filter fun k:Fin 6=>nb k∈zi/\mH (nb k)⊆P;have hF:∀ {d:Nat} {i:B},i∈(Oc.filter fun k=>(mH (nb k)).card=d).image nb->m5 i⊆P/\(m5 i).card=d/\mu 12 D P (m5 i):=fun hi=>by
  obtain⟨k,r,rfl⟩:=A7.1 hi;rw[O] at r;have f:=O.1 r.1;rw[n7];exact⟨f.2.1,r.2,n7 _▸f.2.2⟩
 have n:=rF h hD P p h4 (Oc3.image nb) (Oc2.image nb) (Ct.image nb) (Iin.image nb) (fun _=>hF) (fun _=>hF) (fun c hc=>by
  obtain⟨k,r,rfl⟩:=A7.1 hc;have q:k∉Oc:=(Am.1 r).2;have h8:∀ {d:Nat},nb k∉(Oc.filter fun k=>(mH (nb k)).card=d).image nb:=fun hm=>by obtain⟨k',r',s⟩:=A7.1 hm;rw[nW s] at r';exact q (O.1 r').1
  exact⟨h8,h8,fun w g=>q (O.2 ⟨AC k,n7 _▸w,g⟩)⟩)
  (fun i hi=>by obtain⟨k,r,rfl⟩:=A7.1 hi;have e:=(O.1 r).2;exact⟨e.1,n7 _▸e.2⟩)
 have o:=rX h hD P (fun a ha b hb=>pS a (p ha) b (p hb)) ((Iin \ Oc).image nb) (fun i hi=>by obtain⟨k,r,rfl⟩:=A7.1 hi;rw[Am] at r;have e:=(O.1 r.1).2;exact⟨e.1,n7 _▸e.2,fun g=>r.2 (O.2 ⟨AC k,e.2,g⟩)⟩)
 rw[Au _ nW] at o;rw[Au _ nW,Au _ nW,Au _ nW] at n;have j:(Ct.image nb).biUnion (fun c=>m5 c∩P)=Ct.biUnion (fun k=>mH (nb k)∩P):=by ext x;simp only[C6,A7,A3,n7];exact⟨fun⟨_,⟨k,r,rfl⟩,hx⟩=>⟨k,r,hx⟩,fun⟨k,r,hx⟩=>⟨nb k,⟨k,r,rfl⟩,hx⟩⟩
 rw[j] at n;have z:=nj 12 D;rw[<-hIdef] at z;have h6:=nZ 12 D;obtain⟨u,l,v⟩:=List.mem_iff_getElem.1 t;obtain⟨m,hm⟩:=q3 Oc;have d:=qe ⟨u,l⟩ m;rw[List.getD_eq_getElem _ _ l,v,hm] at d;dsimp only[Oc3,Oc2,Ct,Iin,P] at *;rcases d (fun k r=>(O.1 r).2.1) with h1|h2<;>omega
def sq (D:N)(a:B->Nat×Y)(P kq:Nat×Y):Prop:=oH 12 sj D a/\(∀ x,(C 12 D x).card<=3)/\P≠kq/\∀ x,3<=(C 12 D x).card->P∈C 12 D x/\kq∈C 12 D x
lemma re {D:N}(h:m7 12 D)(m:mB D)(s:me 12 D<=9)(r:U 12 D∈mY)(i:(U 12 D).card=4):∃ pos P kq,sq D pos P kq:=by
 classical
 have o:=s5;have n:=mG m;obtain⟨b,q⟩:=oV o h.1 n;have c:=nY q;obtain⟨pos,a⟩:=oJ o h n;have t:=nH h.1 b c;have w:=o0 12 D;have k:=nj 12 D;have y:nh 12 D=9:=by by_contra j;exact ol h m (by omega) r (by omega)
 have e:∀ x,(C 12 D x).card<=3:=fun x=>by
  have u:=sl h m b c x;have v:(ru D b x).card<=(mi 12 D b).card:=Ck _ _;omega
 by_cases p:(univ.filter (fun x:B=>3<=(C 12 D x).card)).Nonempty
 . obtain⟨P,kq,f,d⟩:=oT o h n b q (by omega) _ p (fun x l=>(O.1 l).2)
   exact⟨pos,P,kq,a,e,fun g=>f (g▸rfl),fun x l=>d x (O.2 ⟨AC x,l⟩)⟩
 . exact⟨pos,(0,J),(1,J),a,e,by decide,fun x l=>(p ⟨x,O.2 ⟨AC x,l⟩⟩).elim⟩
lemma rL {D:N}(h:m7 12 D)(z:mB D)(h9:me 12 D<=9)(t:U 12 D={0,1,8,9}):False:=by
 have u:(U 12 D).card=4:=by rw[t];decide
 have r:U 12 D∈mY:=by rw[t];decide
 obtain⟨l,P,kq,j,w,-,o⟩:=re h z h9 r u;have mem (x:B) (hx:x∈({0,1,8,9}:S2)):x∈U 12 D:=t▸hx;have g:=mem 0 (by decide);have c:=mem 1 (by decide);have d:=mem 8 (by decide);have f:=mem 9 (by decide);obtain⟨zh,m,k,p,v⟩:=q9 h z j (show oF 3 11 by decide)
 have p8:=nr j d (by decide:oF 8 3);have p9:=nr j f (by decide:oF 9 3);have p0:=nr j g (by decide:oF 0 11);have p1:=nr j c (by decide:oF 1 11);have n:l 8≠l 9:=fun e=>Qa (j.2 8 d 9 f e) (by decide);have q:l 0≠l 1:=fun e=>Qa (j.2 0 g 1 c e) (by decide);have b:∀ i∈U 12 D,zh≠l i:=fun i y e=>Qa (p i y e▸y) (by rw[t];decide);have a:∀ i∈U 12 D,mn zh≠l i:=fun i y e=>Qa (v i y e▸y) (by rw[t];decide);rcases o3 p8 p9 m n (b 8 d).symm (b 9 f).symm (w 3) P (o 3 (oh p8 p9 m n (b 8 d).symm (b 9 f).symm)).1 with rfl|rfl|rfl<;>
  rcases o3 p0 p1 k q (a 0 g).symm (a 1 c).symm (w 11) _ (o 11 (oh p0 p1 k q (a 0 g).symm (a 1 c).symm)).1 with s|s|s<;>
  first|exact Qa (j.2 _ (by assumption) _ (by assumption) s) (by decide)|exact a _ (by assumption) s.symm|exact b _ (by assumption) s|exact rs _ s.symm
lemma rG {D:N}(h:m7 12 D)(hD:mB D)(h9:me 12 D<=9)(hI:U 12 D={0,2,6,8}):False:=by
 let s0:S2:={0,2,6,8};let s0:S2:={0,2,6,8};have yo:(U 12 D).card=4:=by rw[hI];decide
 have y2:U 12 D∈mY:=by rw[hI];decide
 obtain⟨xg,P,kq,d,h7,xe,n⟩:=re h hD h9 y2 yo;have c:∀ x:B,x∈s0->x∈U 12 D:=fun x hx=>hI▸hx;have o:∀ x:B,x∉s0->x∉U 12 D:=fun x hx=>hI▸hx;have g (z k v iz ik:B) (hg:iz∈s0/\ik∈s0/\z∉s0/\k∉s0/\v∉s0/\ma iz z=H/\ma ik k=H/\ma z k=H/\ma z v=H/\v≠k/\(mH k).card=3/\decide (v.val<6)=decide (k.val<6)):3<=(C 12 D z).card\/3<=(C 12 D k).card:=by by_contra yk;rw[not_or] at yk;exact sm h hD d z k v iz ik (c iz hg.1) (c ik hg.2.1) (o z hg.2.2.1) (o k hg.2.2.2.1) (o v hg.2.2.2.2.1) hg.2.2.2.2.2 (by omega) (by omega)
 have l (x y ix iy u w iu iw:B) (hg:ix∈s0/\iy∈s0/\iu∈s0/\iw∈s0/\x∉s0/\y∉s0/\u∉s0/\w∉s0/\ma ix x=H/\ma iy y=H/\ma x y=H/\ma iu u=H/\ma iw w=H/\ma u w=H/\ix≠iy/\iu≠ix/\iu≠iy/\iw≠ix/\iw≠iy) (huw:3<=(C 12 D u).card\/3<=(C 12 D w).card) (hsx:3<=(C 12 D x).card) (hsy:3<=(C 12 D y).card):False:=by
  have⟨g1,g2,g3,g4,g5,g6,g7,g8,hr,x5,y1,hs,ht,s,y3,xj,xi,y7,xk⟩:=hg;rw[mj] at hr x5 y1 hs ht s;obtain⟨xs,ya⟩:=n x hsx;obtain⟨xl,xy⟩:=n y hsy;obtain⟨e,xb,xc,yh,yl⟩:=q9 h hD d y1;have mk (a b ia:B) (ga:ia∈s0) (gb:b∉s0) (h1:oF ia a) (hP:P∈C 12 D a) (hQ:kq∈C 12 D a) (f:Nat×Y) (hfa:f∈C 12 D a) (hf2:∀ i∈U 12 D,f=xg i->b=i) (nP:P≠f) (nQ:kq≠f):xg ia=P\/xg ia=kq:=by
   rcases o3 hP hQ hfa xe nP nQ (h7 a) _ (nr d (c ia ga) h1) with h1|h1|h1;. exact D5 h1
   . exact D6 h1
   . exact Qa (hf2 ia (c ia ga) h1.symm▸c ia ga) (o b gb)
  have ho:=mk x y ix g1 g6 hr xs ya e xb yh (fun hh=>rA h.1 (hh▸xl) xc) (fun hh=>rA h.1 (hh▸xy) xc);have hn:=mk y x iy g2 g5 x5 xl xy (mn e) xc yl (fun hh=>rA h.1 (hh▸xs) (by rw[mJ];exact xb)) (fun hh=>rA h.1 (hh▸ya) (by rw[mJ];exact xb));have hq:xg ix≠xg iy:=fun hh=>y3 (d.2 ix (c ix g1) iy (c iy g2) hh);have hj (z z' iz:B) (hiz:iz∈s0) (hz':z'∉s0) (h8:oF iz z) (hzz':oF z z') (hizx:iz≠ix) (hizy:iz≠iy) (hsz:3<=(C 12 D z).card):False:=by
   have⟨y8,xq⟩:=n z hsz;have yb:xg ix∈C 12 D z:=ho.elim (·▸y8) (·▸xq);have xv:xg iy∈C 12 D z:=hn.elim (·▸y8) (·▸xq);obtain⟨f,xx,-,xx',-⟩:=q9 h hD d hzz';rcases o3 yb xv (nr d (c iz hiz) h8) hq (fun hh=>hizx.symm (d.2 ix (c ix g1) iz (c iz hiz) hh)) (fun hh=>hizy.symm (d.2 iy (c iy g2) iz (c iz hiz) hh)) (h7 z) f xx with rfl|rfl|rfl;. exact o z' hz' (xx' ix (c ix g1) rfl▸c ix g1)
   . exact o z' hz' (xx' iy (c iy g2) rfl▸c iy g2)
   . exact o z' hz' (xx' iz (c iz hiz) rfl▸c iz hiz)
  rcases huw with z9|z7;. exact hj u w iu g3 g8 hs s xj xi z9
  . exact hj w u iw g4 g7 ht (oS s) y7 xk z7
 have x6 (a b ia ib m r1 r2 im ir1 ir2:B) (hg:ia∈s0/\ib∈s0/\im∈s0/\ir1∈s0/\ir2∈s0/\a∉s0/\b∉s0/\m∉s0/\r1∉s0/\r2∉s0/\ma ia a=H/\ma ib b=H/\ma im m=H/\ma ir1 r1=H/\ma ir2 r2=H/\ma a m=H/\ma a r1=H/\ma b m=H/\ma b r2=H/\ia≠ib/\r1≠m/\r2≠m/\r1≠r2/\(mH m).card=3/\(mH r1).card=3/\(mH r2).card=3/\decide (r1.val<6)=decide (m.val<6)/\decide (r2.val<6)=decide (m.val<6)) (hsa:3<=(C 12 D a).card) (hsb:3<=(C 12 D b).card) (hcm:(C 12 D m).card<=2) (hcr1:(C 12 D r1).card<=2) (hcr2:(C 12 D r2).card<=2):False:=by
  obtain⟨h4,h2,xf,x2,x3,ha,hb,hm,xu,y0,xw,yc,xt,x0,x4,y4,x1,xo,hy,xz,y9,yd,xm,yt,xr,y5,hw,x7⟩:=hg;rw[mj] at xw yc xt x0 x4 y4 x1 xo hy;obtain⟨Dm,-,yi,yy⟩:=q5 h hD d (c im xf) xt yt hcm;obtain⟨Dr1,-,yf,ys⟩:=q5 h hD d (c ir1 x2) x0 xr hcr1;obtain⟨Dr2,-,yg,ze⟩:=q5 h hD d (c ir2 x3) x4 y5 hcr2;have hl:Dm∈C 12 D m:=(by rw[yi];simp);have hk:Dr1∈C 12 D r1:=(by rw[yf];simp);have t:Dr2∈C 12 D r2:=(by rw[yg];simp);have j (u v iv:B) (Dv:Nat×Y) (hu:u∉s0) (hiv:iv∈s0) (huv:oF u v) (hWv:C 12 D v={xg iv,Dv}):mn Dv∈C 12 D u:=by obtain⟨e,z6,yu,-,z4⟩:=q9 h hD d huv;rw[hWv,A9,A5] at yu;rw[<-yu.resolve_left (fun hh=>o u hu (z4 iv (c iv hiv) hh▸c iv hiv)),mJ];exact z6
  have q (i:B) (hi:i∈s0) (v:B) (hv:v∉s0) (Dx:Nat×Y) (hx:Dx∈C 12 D v):xg i≠mn Dx:=fun he=>o v hv (qV d (c i hi) (by rw[he,mJ];exact hx)▸c i hi);have nM (A zb:Nat×Y) (hAB:A≠zb):mn A≠mn zb:=fun he=>hAB (by rw[<-mJ A,he,mJ]);have r:=nM Dm Dr1 fun he=>yy r1 y9 hw (he▸hk);have p:=nM Dm Dr2 fun he=>yy r2 yd x7 (he▸t);have hd:=nM Dr1 Dr2 fun he=>ys r2 xm.symm (x7.trans hw.symm) (he▸t);have yp:=o3 (nr d (c ia h4) xw) (j a m im Dm ha xf y4 yi) (j a r1 ir1 Dr1 ha x2 x1 yf) (q ia h4 m hm Dm hl) (q ia h4 r1 xu Dr1 hk) r (h7 a);have yn:=o3 (nr d (c ib h2) yc) (j b m im Dm hb xf xo yi) (j b r2 ir2 Dr2 hb x3 hy yg) (q ib h2 m hm Dm hl) (q ib h2 r2 y0 Dr2 t) p (h7 b);have hc (zx:Nat×Y) (hXa:zx∈C 12 D a) (hXb:zx∈C 12 D b):zx=mn Dm:=by
   rcases yp zx hXa with rfl|rfl|rfl<;>rcases yn _ hXb with he|he|he
   . exact Qa (d.2 ia (c ia h4) ib (c ib h2) he) xz
   . exact Qa he (q ia h4 m hm Dm hl)
   . exact Qa he (q ia h4 r2 y0 Dr2 t)
   . exact Qa he.symm (q ib h2 m hm Dm hl)
   . rfl
   . exact Qa he p
   . exact Qa he.symm (q ib h2 r1 xu Dr1 hk)
   . exact Qa he.symm r
   . exact Qa he hd
  exact xe ((hc P (n a hsa).1 (n b hsb).1).trans (hc kq (n a hsa).2 (n b hsb).2).symm)
 have hp:=g 1 11 10 6 0 (by decide);have h6:=g 3 9 11 8 2 (by decide);have xh:=g 5 7 9 6 0 (by decide);have x9:=g 7 4 5 0 8 (by decide);have h0:=g 11 3 1 0 8 (by decide);have xd:=g 9 5 3 2 6 (by decide);by_cases h1:3<=(C 12 D 1).card
 . have hf:(C 12 D 11).card<=2:=by by_contra hf;exact l 1 11 6 0 3 9 8 2 (by decide) h6 h1 (by omega)
   have xn:(C 12 D 10).card<=2:=by by_contra xn;exact l 1 10 6 2 11 3 0 8 (by decide) h0 h1 (by omega)
   have h3:3<=(C 12 D 3).card:=h0.resolve_left (by omega);have h9':(C 12 D 9).card<=2:=by by_contra h9';exact l 3 9 8 2 5 7 6 0 (by decide) xh h3 (by omega)
   exact x6 1 3 6 8 11 10 9 0 2 2 (by decide) h1 h3 hf xn h9'
 . have hf:3<=(C 12 D 11).card:=hp.resolve_left (by omega);have h3:(C 12 D 3).card<=2:=by by_contra h3;exact l 11 3 0 8 9 5 2 6 (by decide) xd hf (by omega)
   have h9':3<=(C 12 D 9).card:=h6.resolve_left (by omega);have h5:(C 12 D 5).card<=2:=by by_contra h5;exact l 9 5 2 6 7 4 0 8 (by decide) x9 h9' (by omega)
   exact x6 11 9 0 2 3 1 5 8 6 6 (by decide) hf h9' h3 (by omega) h5
lemma pM (b:S2)(h:b∈mY)(a:3<=b.card):b.card=3\/b∈countOrbits\/b={0,1,8,9}\/b={0,2,6,8}:=by obtain⟨n,-,rfl⟩:=oc h;revert n;decide +kernel
lemma g12_lb_21 (zc:Circuit)(hmono:Monotone2 zc)(hsize:zc.size<=20)(hC:∀ x:B->Y,zc.eval (Da x)=H↔G12Edge x):False:=by
 obtain⟨D,h,g,-,i,d,b⟩:=qg zc hmono hC hsize;rcases pM _ b d with j|f|c|e;. have a:=nj 12 D;have k:=o0 12 D;exact ol h g (by omega) b d
 . exact qA h g i b d f
 . exact rL h g i c
 . exact rG h g i e
end Mono
namespace Engine
open List
noncomputable section
open PEqualNP.CircuitLowerBounds
abbrev N:=BV 4096
def P:N:=0
def one:N:=BitVec.allOnes 4096
def neg (a:N):N:= ~~~a
def V (d:Nat)(a b:N):N:=if d=0 then a&&&b else if d=1 then a|||b else if d=2 then a&&&~~~b else ~~~a&&&b
def U (a:N):Prop:=a≠P/\a≠one
def eT (u:Y)(d:Nat):Prop:=d<2\/(u=H/\d<4)
def iE (d:Nat):=if d=2 then 3 else if d=3 then 2 else d
lemma eY {u d}(h:eT u d):d=0\/d=1\/(u=H/\d=2)\/(u=H/\d=3):=by
 rcases h with h|⟨h,j⟩;. omega
 . have:d=0\/d=1\/d=2\/d=3:=(by omega);rcases this with a|a|a|a
   . exact D5 a
   . exact D6 (D5 a)
   . exact D6 (D6 (D5 ⟨h,a⟩))
   . exact D6 (D6 (D6 ⟨h,a⟩))
lemma js {u d}(h:eT u d)(a b:N):V d a b=V (iE d) b a:=by rcases eY h with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩<;>simp[V,iE,BitVec.and_comm,Cn]
lemma wO {u d}(h:eT u d):eT u (iE d)/\iE (iE d)=d:=by rcases eY h with rfl|rfl|⟨a,rfl⟩|⟨a,rfl⟩;all_goals simp_all [iE,eT]
def Lv (u:Y)(target:N):Nat->I N->Prop
 | 0,vs=>vs={target}/\U target
 | k+1,vs=>∃ (zu:I N) (a b:N) (d:Nat),eT u d/\vs=insert a (insert b zu)/\U a/\U b/\a≠b/\V d a b∉insert a (insert b zu)/\Lv u target k (insert (V d a b) zu)
lemma Lv.stop {u}{a:N}(b:U a):Lv u a 0 {a}:=⟨rfl,b⟩
lemma Lv.binary {u}{c:N}{k:Nat}{h:I N}{a b:N}{d:Nat}(i:eT u d)(j:U a)(l:U b)(f:a≠b)(e:V d a b∉insert a (insert b h))(g:Lv u c k (insert (V d a b) h)):Lv u c (k+1) (insert a (insert b h)):=⟨h,a,b,d,i,rfl,j,l,f,e,g⟩
lemma Lv.ind {u}{c:N}{e:∀ (k:Nat) (g:I N),Lv u c k g->Prop}(stop:∀ (hp:U c),e 0 {c} (Lv.stop hp))(binary:∀ {k:Nat} {zu:I N} {a b:N} {d:Nat} (hd:eT u d) (ha:U a) (hb:U b) (hab:a≠b) (f:V d a b∉insert a (insert b zu)) (tail:Lv u c k (insert (V d a b) zu)),e k (insert (V d a b) zu) tail->e (k+1) (insert a (insert b zu)) (Lv.binary hd ha hb hab f tail)){k:Nat}{g:I N}(h:Lv u c k g):e k g h:=by induction k generalizing g with|zero=>obtain⟨rfl,hp⟩:=h;exact stop hp | succ k j=>obtain⟨zu,a,b,d,hd,rfl,ha,hb,hab,i,tail⟩:=h;exact binary hd ha hb hab i tail (j tail)
lemma gA {u b k c}(h:Lv u b k c):∀ a∈c,U a:=by induction h using Lv.ind with|stop d=>simpa using d | binary l e i g j _ f=>simp only[BI];exact⟨e,i,fun a h=>f a (A2 h)⟩
lemma gz {u c k e}(h:Lv u c k e):e.card<=k+1:=by induction h using Lv.ind with|stop j=>simp | @binary k zu a b d hd ha hb hab hf _ ih=>have f:V d a b∉zu:=fun g=>hf (A2 (A2 g));rw[Al f] at ih;have i:=Bl (a:=a) (s:=insert b zu);have l:=Bl (a:=b) (s:=zu);omega
def bit (i:Fin 4096)(a:N):Y:=a.getLsbD i.val
lemma f5 (i):bit i P=J:=by simp[bit,P]
lemma fM (i):bit i one=H:=by unfold bit one;rw[BL];simp
lemma ft (i)(a:N):bit i (neg a)=!(bit i a):=by simp[bit,neg,i.isLt]
lemma gT (i d)(a b:N):bit i (V d a b)=(if d=0 then bit i a&&bit i b else if d=1 then bit i a||bit i b else if d=2 then bit i a&&!(bit i b) else !(bit i a)&&bit i b):=by unfold V;split_ifs<;>simp[bit]
lemma fu {a b:N}(h:∀ i,bit i a=bit i b):a=b:=Af fun j c=>h ⟨j,c⟩
def jc (u:Y)(a:N):N:=if u&&bit 0 a then neg a else a
lemma gC (a:N):jc J a=a:=rfl
lemma xU (a:N):bit 0 (jc H a)=J:=by cases h:bit 0 a<;>simp[jc,h,ft]
lemma uV {u}{a:N}(h:bit 0 a=J):jc u a=a:=by simp[jc,h]
lemma wF' (a:N):neg (neg a)=a:=by simp[neg]
lemma w3 (a:N):jc H (neg a)=jc H a:=by cases h:bit 0 a<;>simp[jc,h,ft,wF']
lemma tU {a:N}(h:U (neg a)):U a:=by
 refine⟨?_,?_⟩;. rintro rfl;exact h.2 (by simp[neg,P,one])
 . rintro rfl;exact h.1 (by simp[neg,P,one])
lemma xS {u}{a:N}(h:U (jc u a)):U a:=by
 unfold jc at h;split at h;. exact tU h
 . exact h
def gR (d:Y)(a b:N):=if d then a|||b else a&&&b
lemma gG (i)(d:Y)(a b:N):bit i (gR d a b)=(if d then bit i a||bit i b else bit i a&&bit i b):=by cases d<;>simp[gR,bit]
lemma yj (d:Y)(a b:N):∃ e,e<4/\jc H (gR d a b)=V e (jc H a) (jc H b):=by
 refine⟨if d then(if bit 0 a then(if bit 0 b then 0 else 2) else(if bit 0 b then 3 else 1)) else(if bit 0 a then(if bit 0 b then 1 else 3) else(if bit 0 b then 2 else 0)),?_,?_⟩;. split_ifs<;>omega
 . apply fu;intro i;cases d<;>cases g:bit 0 a<;>cases h:bit 0 b<;>
   simp only[jc,gG,g,h,gT,ft,AD,DM,Cb,Cs,BT,DC,Ee,Ef,Ak,AX,AB]<;>
   cases f:bit i a<;>cases c:bit i b<;>simp[f,c,ft,gG]
def gv (w:Z N)(g:Gate):N:=let a:=g.inputs.map (fun i=>w.getD i P)
 match g.op with
 | .and=>a.foldr (gR J) one
 | .or=>a.foldr (gR H) P
 | .not=>neg (a.headD P)
 | _=>P
def ek (a:Z Gate)(w:Z N):Z N:=a.foldl (fun l g=>l++[gv l g]) w
def eL (w:Z N)(v:N):Prop:=v∈w\/¬U v
def iM (u:Y)(w:Z N)(v:N):Prop:=eL w (jc u v)
lemma w4 (a:N):V 0 a one=a/\V 1 a P=a/\V 0 a P=P/\V 1 a one=one/\V 0 a a=a/\V 1 a a=a/\V 2 a a=P/\V 3 a a=P/\V 2 a P=a/\V 3 P a=a/\V 2 P a=P/\V 3 a P=P/\V 0 P a=P/\V 1 P a=a/\V 0 one a=a/\V 1 one a=one:=by
 refine⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>apply fu<;>intro i<;>
  simp[gT,f5,fM]
lemma y2:neg P=one/\neg one=P:=by simp[neg,P,one]
lemma jR {w:Z N}{a:N}(h:eL w a):a=P\/a=one\/a∈w/\U a:=by
 by_cases b:a=P;. exact D5 b
 by_cases c:a=one;. exact D6 (D5 c)
 exact D6 (D6 ⟨h.resolve_right (fun x=>x ⟨b,c⟩),b,c⟩)
def ix (u:Y)(w:Z N)(z:N):Prop:=∃ d a b,eT u d/\a∈w/\b∈w/\U a/\U b/\a≠b/\z=V d a b
lemma vL {u w a b}(d:Nat)(v:eT u d)(t:eL w a)(z:eL w b)(y:u=H->a≠one/\b≠one):eL w (V d a b)\/ix u w (V d a b):=by
 have x:eL w P:=D6 (fun h=>h.1 rfl);have ro:eL w one:=D6 (fun h=>h.2 rfl);have⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,q,l,k,r,o,p,m⟩:=w4 a;obtain⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,g,f,n,i,c,e,j⟩:=w4 b;by_cases he:a=b
 . subst b;left;rcases eY v with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact a5.symm▸t
   . exact a6.symm▸t
   . exact a7.symm▸x
   . exact a8.symm▸x
 rcases jR t with rfl|rfl|⟨h0,h1⟩
 . left;rcases eY v with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact i.symm▸x
   . exact c.symm▸z
   . exact f.symm▸x
   . exact g.symm▸z
 . left;rcases eY v with rfl|rfl|⟨s,rfl⟩|⟨s,rfl⟩
   . exact e.symm▸z
   . exact j.symm▸ro
   . exact Qa rfl (y s).1
   . exact Qa rfl (y s).1
 rcases jR z with rfl|rfl|⟨h3,h2⟩
 . left;rcases eY v with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact a3.symm▸x
   . exact a2.symm▸t
   . exact a9.symm▸t
   . exact k.symm▸x
 . left;rcases eY v with rfl|rfl|⟨s,rfl⟩|⟨s,rfl⟩
   . exact a1.symm▸t
   . exact a4.symm▸ro
   . exact Qa rfl (y s).2
   . exact Qa rfl (y s).2
 exact D6 ⟨d,a,b,v,h0,h3,h1,h2,he,rfl⟩
lemma vh (a:N):jc H a≠one:=by intro h;have:=xU a;rw[h,fM] at this;cases this
lemma uZ {u w a b}(d:Y)(c:iM u w a)(f:iM u w b):iM u w (gR d a b)\/ix u w (jc u (gR d a b)):=by
 cases u
 . have e:gR d a b=V (if d then 1 else 0) a b:=by cases d<;>rfl
   have h:=vL (u:=J) (if d then 1 else 0) (D5 (by split<;>omega)) c f (by simp);unfold iM;simp only[gC] at h ⊢;rwa[e]
 . obtain⟨e,i,g⟩:=yj d a b;unfold iM;rw[g];exact vL e (D6 ⟨rfl,i⟩) c f (fun _=>⟨vh a,vh b⟩)
lemma ik {u w}{v:N}(h:v=P\/v=one):iM u w v:=by
 refine D6 fun a=>?_
 have:=xS a;rcases h with rfl|rfl;. exact this.1 rfl
 . exact this.2 rfl
lemma tl {u}(w:Z N)(i:Nat):iM u (w.map (jc u)) (w.getD i P):=by simp only[A1];cases h:w[i]? with|none=>exact ik (D5 rfl) | some a=>exact D5 (Qm (Dh h))
lemma xy {w a}(h:iM H w a):iM H w (neg a):=by unfold iM;rwa[w3]
def fj (g:Gate):Y:=match g.op with
 | .not=>H
 | _=>J
lemma vQ (u:Y)(w:Z N)(g:Gate)(h:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2)(e:u=J->fj g=J):iM u (w.map (jc u)) (gv w g)\/(fj g=J/\ix u (w.map (jc u)) (jc u (gv w g))):=by
 have⟨o,l⟩:=g;simp only[C8,BO] at h;obtain⟨f,k⟩:=h;have c (d:Y):iM u (w.map (jc u)) ((l.map (fun i=>w.getD i P)).foldr (gR d) (if d then P else one))\/ix u (w.map (jc u)) (jc u ((l.map (fun i=>w.getD i P)).foldr (gR d) (if d then P else one))):=by
  have b (v:N):gR d v (if d then P else one)=v:=by apply fu;intro i;cases d<;>simp[gG,f5,fM]
  cases l with
  | nil=>exact D5 (ik (by cases d<;>simp))
  | cons i l=>
    cases l with
    | nil=>simp only[As,C2,foldr_cons,foldr_nil,b];exact D5 (tl w i)
    | cons j l=>cases l with|cons a l=>simp at k | nil=>simp only[As,C2,foldr_cons,foldr_nil,b];exact uZ d (tl w i) (tl w j)
 rcases f with rfl|rfl|rfl;. exact(c false).imp id (fun h=>⟨rfl,h⟩)
 . exact(c H).imp id (fun h=>⟨rfl,h⟩)
 . cases u
   . exact Qa (e rfl) (by simp[fj])
   left;cases l with|nil=>exact ik (D6 (by simp[gv,y2])) | cons i l=>exact xy (tl w i)
lemma jE {u f}{w:Z N}{z:N}{k g c}(h:Lv u f k g)(t:eL w z\/(c=1/\ix u w z))(i:∀ a∈g,a∈w++[z]):∃ k' g',k'<=k+c/\Lv u f k' g'/\∀ a∈g',a∈w:=by
 by_cases n:z∈g
 . by_cases m:z∈w
   . refine⟨k,g,by omega,h,?_⟩
     intro a j;have l:a∈w\/a=z:=(by simpa using i a j);rcases l with l|rfl;. exact l
     . exact m
   . have hp:=gA h z n;rcases t with hr|⟨rfl,d,a,b,hd,j,s,x,pb,r,p⟩
     . exact False.elim ((hr.resolve_left m) hp)
     . subst z;let o:=g.erase (V d a b);have ht:Lv u f k (insert (V d a b) o):=(by simpa[o,BY n] using h);have l:∀ v∈o,v∈w:=by intro v hv;have⟨e,n⟩:=AN.mp hv;simpa[e] using i v n
       have y:V d a b∉insert a (insert b o):=by
        intro q;rcases A9.mp q with p|u;. exact m (p.symm▸j)
        rcases A9.mp u with p|u;. exact m (p.symm▸s)
        . exact m (l _ u)
       exact⟨_,_,BA _,Lv.binary hd x pb r y ht,by simpa using And.intro j (And.intro s l)⟩
 . refine⟨k,g,by omega,h,?_⟩
   intro a j;have hn:a≠z:=fun q=>n (q▸j);simpa[hn] using i a j
lemma vM {u f}(gs:Z Gate)(w:Z N)(b:∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2)(d:u=J->∀ g∈gs,fj g=J)(n:U f)(c:f∈(ek gs w).map (jc u)):∃ k vs,k<=gs.countP (fun g=>!fj g)/\Lv u f k vs/\∀ a∈vs,a∈w.map (jc u):=by
 induction gs generalizing w with
 | nil=>exact⟨0,{f},by simp,Lv.stop n,by simpa[ek] using c⟩
 | cons g gs p=>
   obtain⟨k,vs,t,s,m⟩:=p (w++[gv w g]) (fun a j=>b a (by simp[j])) (fun i a j=>d i a (by simp[j])) c
   have e:=vQ u w g (b g (by simp)) (fun i=>d i g (by simp));rw[B5] at m;have e':eL (w.map (jc u)) (jc u (gv w g))\/((if fj g then 0 else 1)=1/\ix u (w.map (jc u)) (jc u (gv w g))) := e.imp id (fun h=>⟨by simp[h.1],h.2⟩)
   obtain⟨l,T,r,i,o⟩:=jE s e' m;refine⟨l,T,?_,i,o⟩;rw[BR];cases q:fj g<;>simp[q] at r ⊢<;>omega
lemma vO (i)(w:Z N)(j:Nat):(w.map (bit i)).getD j J=bit i (w.getD j P):=by simp only[A1,B4];cases w[j]? with|none=>exact(f5 _).symm | some a=>rfl
lemma wk (i)(g:Gate)(w:Z N)(c:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):bit i (gv w g)=g.op.eval (g.inputs.map fun j=>(w.map (bit i)).getD j J):=by
 obtain⟨o,l⟩:=g;simp only[C8,BO] at c;simp only[vO];rcases c with rfl|rfl|rfl;. induction l with|nil=>exact fM _ | cons a l b=>change bit i (gR J _ _)=(_&&_);rw[gG];exact Az (fun x=>bit i (w.getD a P)&&x) b
 . induction l with|nil=>exact f5 _ | cons a l b=>change bit i (gR H _ _)=(_||_);rw[gG];exact Az (fun x=>bit i (w.getD a P)||x) b
 . cases l with|nil=>change bit i (neg P)=!J;rw[ft,f5] | cons a l=>exact ft _ _
lemma wj (gs:Z Gate)(i)(w:Z N)(b:∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):(ek gs w).map (bit i)=gs.foldl (fun(l:Z Y) g=>l++[g.op.eval (g.inputs.map fun j=>l.getD j J)]) (w.map (bit i)):=by induction gs generalizing w with|nil=>rfl | cons g gs c=>change (ek gs (w++[gv w g])).map _=_;rw[c _ (fun a d=>b a (by simp[d]))];simp[wk i g w (b g (by simp))]
abbrev O (a:Type):=a->Y
def jh {b}(a:O b):O b:=fun r=>!(a r)
def ez {d}(c:Y)(a b:O d):O d:=if c then fun r=>a r||b r else fun r=>a r&&b r
def l0 {c}(d:Nat)(a b:O c):O c:=if d=0 then ez J a b else if d=1 then ez H a b else if d=2 then ez J a (jh b) else ez J (jh a) b
def ea {c}(a:O c):Prop:=∃ b:Y,a=fun _=>b
def fS {b}(a:O b):Nat:=by classical exact if ea a then 1 else 0
def g0 {b}(a:Z (O b)):Nat:=(a.map fS).sum
def S {b}(u:Y)(a:Z (O b))(v:O b):Prop:=v∈a\/ea v\/(u=H/\jh v∈a)
def fK {d}(u:Y)(b c:Z (O d)):=∀ a∈c,S u b a
def Rc {zr}(u:Y)(roots:Z (O zr)):Nat->Z (O zr)->Prop
 | 0,b=>b=roots
 | p+1,c=>∃ (op:Y) (bank:Z (O zr)) (a b:O zr),Rc u roots p bank/\S u bank a/\S u bank b/\c=ez op a b::bank
lemma Rc.start {b u}{a:Z (O b)}:Rc u a 0 a:=rfl
lemma Rc.two {g u}{d:Z (O g)}{p c a b}(e:Y)(h:Rc u d p c)(f:S u c a)(i:S u c b):Rc u d (p+1) (ez e a b::c):=⟨e,c,a,b,h,f,i,rfl⟩
lemma Rc.ind {e u}{d:Z (O e)}{c:∀ p bank,Rc u d p bank->Prop}(start:c 0 d Rc.start)(two:∀ {p bank a b} (op:Y) (h:Rc u d p bank) (ha:S u bank a) (hb:S u bank b),c p bank h->c (p+1) (ez op a b::bank) (Rc.two op h ha hb)){p bank}(h:Rc u d p bank):c p bank h:=by induction p generalizing bank with|zero=>obtain rfl:=h;exact start | succ p f=>obtain⟨op,bank,a,b,h,ha,hb,rfl⟩:=h;exact two op h ha hb (f h)
def kept {c:Type}(a:Y)(x:c)(b:Z c):=if a then x::b else b
def Run {zr}(u:Y)(goal:O zr):Nat->Z (O zr)->Prop
 | 0,zs=>List.Perm [goal] zs
 | s+1,zs=>∃ (op:Nat) (ka kb:Y) (a b:O zr) (rest:Z (O zr)),eT u op/\(a::b::rest).Perm zs/\Run u goal s (l0 op a b::kept ka a (kept kb b rest))
lemma Run.stop {b u}{a:O b}:Run u a 0 [a]:=List.Perm.refl _
lemma Run.perm {f u}{c:O f}{s:Nat}{e g:Z (O f)}(p:e.Perm g)(h:Run u c s e):Run u c s g:=by cases s with|zero=>exact List.Perm.trans h p | succ s=>have⟨j,l,i,a,b,d,k,q,h⟩:=h;exact⟨j,l,i,a,b,d,k,q.trans p,h⟩
lemma Run.two {f u}{c:O f}{s:Nat}{a b:O f}{d:Z (O f)}(e:Nat)(j:eT u e)(i g:Y)(h:Run u c s (l0 e a b::kept i a (kept g b d))):Run u c (s+1) (a::b::d):=⟨e,i,g,a,b,d,j,List.Perm.refl _,h⟩
lemma Run.ind {i u}{d:O i}{c:∀ s e,Run u d s e->Prop}(stop:c 0 [d] Run.stop)(perm:∀ {s f g} (p:List.Perm f g) (h:Run u d s f),c s f h->c s g (Run.perm p h))(two:∀ {s a b rest} (op:Nat) (hd:eT u op) (ka kb:Y) (h:Run u d s (l0 op a b::kept ka a (kept kb b rest))),c s _ h->c (s+1) (a::b::rest) (Run.two op hd ka kb h)){s e}(h:Run u d s e):c s e h:=by induction s generalizing e with|zero=>exact perm h Run.stop stop | succ s j=>have⟨op,ka,kb,a,b,rest,hd,p,h⟩:=h;exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (j h))
lemma f1 {b}(a:O b)(xs):g0 (a::xs)=fS a+g0 xs:=by simp[g0]
lemma gB {b}(a:O b)(xs)(k:Y):g0 xs<=g0 (kept k a xs):=by cases k<;>simp[kept,f1]
lemma i8 {b}{a:O b}(h:ea a):ea (jh a):=by obtain⟨v,rfl⟩:=h;exact⟨!v,rfl⟩
lemma vg' {b}(a:O b):jh (jh a)=a:=by funext r;simp[jh]
lemma tG {b}(a:O b):fS (jh a)=fS a:=by
 have:ea (jh a)↔ea a:=⟨fun h=>vg' a▸i8 h,i8⟩
 by_cases h:ea a;. simp[fS,if_pos h,if_pos (this.mpr h)]
 . simp[fS,if_neg h,if_neg (fun x=>h (this.mp x))]
lemma jF {d u}{b:Z (O d)}{a}(c:u=H)(h:S u b a):S u b (jh a):=by
 rcases h with h|h|⟨_,h⟩;. exact D6 (D6 ⟨c,(vg' a).symm▸h⟩)
 . exact D6 (D5 (i8 h))
 . exact D5 h
lemma jQ {c}{a b:O c}(op)(h:ea a)(g:ea b):ea (ez op a b):=by obtain⟨v,rfl⟩:=h;obtain⟨w,rfl⟩:=g;cases op<;>exact⟨_,rfl⟩
lemma jS {f u}(op){a b:O f}{c}(h:ea a\/ea b)(d:S u c a)(e:S u c b):S u c (ez op a b):=by
 rcases h with⟨v,rfl⟩|⟨v,rfl⟩
 . cases op<;>cases v
   . exact D6 (D5 ⟨J,by funext x;simp[ez]⟩)
   . simpa[ez] using e
   . simpa[ez] using e
   . exact D6 (D5 ⟨H,by funext x;simp[ez]⟩)
 . cases op<;>cases v
   . exact D6 (D5 ⟨J,by funext x;simp[ez]⟩)
   . simpa[ez] using d
   . simpa[ez] using d
   . exact D6 (D5 ⟨H,by funext x;simp[ez]⟩)
lemma eW {b u}{a v}(w:O b)(h:S u a v):S u (w::a) v:=h.imp (AK _) (Or.imp id (And.imp id (AK _)))
lemma xn {l u}(e:Z (O l)){p d a b}(op)(i:Rc u e p d)(j:S u d a)(k:S u d b):∃ q next,Rc u e q next/\S u next (ez op a b)/\(∀ v,S u d v->S u next v)/\q+fS a+fS b<=p+1+fS (ez op a b):=by
 classical
 by_cases c:ea a\/ea b
 . refine⟨p,d,i,jS op c j k,fun _ h=>h,?_⟩
   by_cases f:ea a<;>by_cases g:ea b
   . simp[fS,f,g,jQ op f g]
   . simp[fS,f,g]
   . simp[fS,f,g]
   . exact False.elim (c.elim f g)
 . have f:¬ea a:=fun h=>c (D5 h);have g:¬ea b:=fun h=>c (D6 h);exact⟨p+1,_,Rc.two op i j k,D5 (by simp),fun _ h=>eW _ h,
   by simp[fS,f,g]⟩
lemma h8 {h u}{c:Z (O h)}{d a b}(i:eT u d)(e:S u c a)(f:S u c b):∃ op x y,l0 d a b=ez op x y/\S u c x/\S u c y/\fS x=fS a/\fS y=fS b:=by
 rcases eY i with rfl|rfl|⟨g,rfl⟩|⟨g,rfl⟩;. exact⟨J,a,b,rfl,e,f,rfl,rfl⟩
 . exact⟨H,a,b,rfl,e,f,rfl,rfl⟩
 . exact⟨J,a,jh b,rfl,e,jF g f,rfl,tG b⟩
 . exact⟨J,jh a,b,rfl,jF g e,f,tG a,rfl⟩
lemma wJ {j u}(c:Z (O j)){p f a b}(d)(g:eT u d)(h:Rc u c p f)(i:S u f a)(k:S u f b):∃ q next,Rc u c q next/\S u next (l0 d a b)/\(∀ v,S u f v->S u next v)/\q+fS a+fS b<=p+1+fS (l0 d a b):=by have⟨m,x,y,e,n,r,o,l⟩:=h8 g i k;rw[e,<-o,<-l];exact xn c m h n r
lemma hR {c:Type}{k:Y}{x a:c}{b}(h:x∈kept k a b):x=a\/x∈b:=by cases k<;>simp_all [kept]
lemma xZ {y u}{c:O y}(nc:¬ea c){s m}(h:Run u c s m)(i:Z (O y)){p g}(l:Rc u i p g)(j:fK u g m):∃ q next,Rc u i q next/\S u next c/\q+g0 m<=p+s:=by
 classical
 induction h using Run.ind generalizing p g with
 | stop=>exact⟨p,g,l,j _ (by simp),by simp[g0,fS,nc]⟩
 | perm z _ o=>have d:fK u g _:=fun v k=>j v (z.mem_iff.mp k);have⟨q,x,t,k,w⟩:=o l d;exact⟨q,x,t,k,by simpa only[g0,<-(z.map fS).sum_eq] using w⟩
 | @two s a b rest op hd ka kb _ o=>
   obtain⟨r,T,hT,hz,f,le⟩:=wJ i op hd l (j a (by simp)) (j b (by simp));have ht:fK u T (l0 op a b::kept ka a (kept kb b rest)):=by
    intro v h;rcases Ab.mp h with rfl|n;. exact hz
    . apply f v;apply j;rcases hR n with rfl|n
      . simp
      . exact AK _ (Ab.mpr (hR n))
   obtain⟨q,x,t,k,w⟩:=o hT ht;have e:=gB a (kept kb b rest) ka;have e':=gB b rest kb;rw[f1] at w;refine⟨q,x,t,k,?_⟩;rw[f1,f1];omega
def e4 {c d:Type}(b:d->c)(a:O c):O d:=fun r=>a (b r)
lemma gp {c d:Type}(b:d->c)(k:Y)(a:O c)(ws):(kept k a ws).map (e4 b)=kept k (e4 b a) (ws.map (e4 b)):=by cases k<;>simp[kept]
lemma gm {e f:Type}(c:f->e)(d)(a b:O e):e4 c (l0 d a b)=l0 d (e4 c a) (e4 c b):=by unfold l0;split_ifs<;>rfl
lemma i4 {e f:Type}{u}(a:f->e){b s d}(h:Run u b s d):Run u (e4 a b) s (d.map (e4 a)):=by induction h using Run.ind with|stop=>exact Run.stop | perm p _ c=>exact Run.perm (p.map _) c | two i j k g _ c=>simp only[As,gp,gm] at c ⊢;exact Run.two i j k g c
lemma je {n i:Type}{u}(a:i->n){e s g}(h:Run u e s g)(m:¬ea (e4 a e)){d:Z (O i)}{p f zl}(j:Rc u d p f)(k:fK u f (g.map (e4 a)))(l:∀ q bs,Rc u d q bs->S u bs (e4 a e)->zl<=q):zl+g0 (g.map (e4 a))<=p+s:=by have⟨q,bs,r,o,c⟩:=xZ m (i4 a h) d j k;have b:=l q bs r o;omega
abbrev K:=Fin 4096
def A (a:N):O K:=fun r=>bit r a
def eV (f:O K):N:=(BZ (Da f)).cast (BQ)
lemma fZ (f:O K)(r:K):bit r (eV f)=f r:=by simp only[bit,eV,BitVec.getLsbD_cast,C3,A1,Cz];simp[r.isLt]
lemma fy (v:N):eV (A v)=v:=by apply Af;intro j a;exact fZ (A v) ⟨j,a⟩
lemma wA (f:O K):A (eV f)=f:=by funext r;exact fZ f r
lemma tf (a:N):A (neg a)=jh (A a):=by funext r;exact ft _ _
lemma tw (d:Nat)(a b:N):A (V d a b)=l0 d (A a) (A b):=by funext r;simp only[A,gT,l0];split_ifs<;>rfl
lemma jz {b c:Type}(f:b->c)(d:Y)(a:b)(l:Z b):(kept d a l).map f=kept d (f a) (l.map f):=by cases d<;>rfl
lemma i5 {b:Type}(k:Y)(a:b)(l:Z b)(c:l.Nodup)(d:a∉l):(kept k a l).Nodup:=by cases k<;>simp[kept,c,d]
lemma im (k:Y)(a:N)(l:Z N):(kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by cases k<;>simp[kept]
lemma tF {u}{T:N}{k n}(h:Lv u T k n)(v:Z N)(o:v.Nodup)(f:v.toFinset=n):Run u (A T) k (v.map A):=by
 classical
 induction h using Lv.ind generalizing v with
 | stop hp=>
   have w:[T].Perm v:=by apply AT (by simp) o;simpa[f]
   exact Run.perm (w.map _) Run.stop
 | @binary k zu a b d hd ha hb hab fresh _ ih=>
   let g:=((zu.erase a).erase b).toList;let m:=decide (a∈zu);let l:=decide (b∈zu);let e:=kept l b g;let i:=kept m a e;have q:g.toFinset=(zu.erase a).erase b:=(by simp[g]);have s:a∉g:=(by simp[g]);have t:b∉g:=(by simp[g]);have p:g.Nodup:=Be _;have y:=i5 l b g p t;have am:a∉e:=by cases h:l<;>simp[e,kept,h,hab,s]
   have x:=i5 m a e y am;have r:i.toFinset=zu:=by
    change (kept m a (kept l b g)).toFinset=zu;rw[im,im,q];ext j;by_cases aa:a∈zu<;>by_cases bb:b∈zu<;>by_cases aj:j=a<;>
     by_cases bj:j=b<;>simp_all [m,l]
   have z:V d a b∉i:=by intro hz;exact fresh (A2 (A2 (r▸A4.mpr hz)))
   have c:=ih (V d a b::i) (B7.mpr ⟨z,x⟩) (by simp[r]);change Run _ _ _ ((V d a b::kept m a (kept l b g)).map A) at c;rw[As,jz,jz,tw] at c;have perm:(a::b::g).Perm v:=by apply AT (by simp[hab,s,t,p]) o;ext j;by_cases ja:j=a<;>by_cases jb:j=b<;>simp_all [q]
   exact Run.perm (perm.map _) (Run.two d hd m l c)
lemma vR (f:O K):eV (jh f)=neg (eV f):=by rw[<-fy (neg (eV f)),tf,wA]
lemma hQ (d:Y)(f g:O K):eV (ez d f g)=gR d (eV f) (eV g):=by apply fu;intro r;rw[fZ,gG,fZ,fZ];cases d<;>rfl
lemma fx {u}{c:Z (O K)}{a}(h:S u c a):iM u ((c.map eV).map (jc u)) (eV a):=by
 rcases h with d|⟨b,rfl⟩|⟨rfl,d⟩;. exact D5 (Qm (Qm d))
 . apply ik;cases b
   . exact D5 (fu fun i=>(fZ _ i).trans (f5 i).symm)
   . exact D6 (fu fun i=>(fZ _ i).trans (fM i).symm)
 . have:=vR a;refine D5 ?_;rw[<-w3,<-this];exact Qm (Qm d)
lemma wI {u}{i:Z (O K)}{p g}(h:Rc u i p g){T k vs}(e:Lv u T k vs)(sub:∀ a∈vs,a∈(g.map eV).map (jc u)):∃ l zv,l<=p+k/\Lv u T l zv/\∀ a∈zv,a∈(i.map eV).map (jc u):=by
 induction h using Rc.ind generalizing k vs with
 | start=>exact⟨k,vs,by omega,e,sub⟩
 | @two p g a b d h ha hb ih=>
   rw[As,As,hQ] at sub;have f:=uZ d (fx ha) (fx hb);have⟨k',vs',o,e',sub'⟩:=jE (c:=1) e (f.imp id (fun h=>⟨rfl,h⟩)) (fun a n=>by simpa[or_comm] using sub a n)
   have⟨l,zv,q,j,m⟩:=ih e' sub';exact⟨l,zv,by omega,j,m⟩
def eN (a:N):Y:=!(bit 0 a)
lemma vJ {u}{w:Z N}(h:w.all eN=H):w.map (jc u)=w:=by
 have e:w.map (jc u)=w.map id:=by apply Cy;intro a b;exact uV (by simpa[eN] using Ae.mp h a b)
 rw[e,map_id]
lemma uW {u}{c:Z N}{p d T}(g:U T)(m:eN T=H)(j:c.all eN=H)(h:Rc u (c.map A) p d)(b:S u d (A T)):∃ k vs,k<=p/\Lv u T k vs/\∀ a∈vs,a∈c:=by
 have f:=fx b;rw[fy] at f;unfold iM at f;rw[uV (by simpa[eN] using m)] at f;have mem:=f.resolve_right (fun q=>q g);obtain⟨l,n,r,o,i⟩:=wI h (Lv.stop g) (by simpa using mem);refine⟨l,n,by omega,o,?_⟩;have e:(c.map A).map eV=c:=(by simp[DI,fy])
 rw[e,vJ j] at i;exact i
lemma fD {u T k g}(h:Lv u T k g){r s:K}(c:bit r T≠bit s T):∃ a∈g,bit r a≠bit s a:=by
 induction h using Lv.ind with
 | stop l=>exact⟨_,by simp,c⟩
 | @binary k zu a b d f ha hb hab hf _ ih=>
   have⟨v,j,f⟩:=ih;rcases A9.mp j with rfl|i
   . by_cases e:bit r a=bit s a
     . refine⟨b,by simp,?_⟩
       intro beq;exact f (by rw[gT,gT,e,beq])
     . exact⟨a,by simp,e⟩
   . exact⟨v,A2 (A2 i),f⟩
lemma i6 {u T k f}(h:Lv u T k f)(e:Z N)(a:N)(g:∀ v∈f,v∈e)(r s:K)(c:bit r T≠bit s T)(b:∀ v∈e,v≠a->bit r v=bit s v):a∈f:=by
 have⟨v,i,j⟩:=fD h c;by_cases d:v=a;. simpa[d] using i
 . exact False.elim (j (b v (g v i) d))
def fW (q:Nat):Nat:=(1<<<(1<<<q))-1
def ep (q i:Nat):Nat:=let a:=1<<<i
 let b:=((1<<<a)-1)<<<a
 let rec go (k:Nat) (step:Nat) (p:Nat):Nat :=
  match k with
  | 0=>p
  | k'+1=>if step >= (1<<<q) then p else go k' (step<<<1) (p|||(p<<<step))
 go q (a<<<1) b
def i3 (q:Nat):Y:=(range q).all fun i=>let v:=ep q i;decide (v<(1<<<(1<<<q)))&&(range (1<<<q)).all fun s=>v.testBit s==s.testBit i
set_option maxHeartbeats 800000 in
lemma jt:(range 13).all i3=H:=by decide +kernel
lemma eC {q i s:Nat}(d:q<=12)(b:i<q)(c:s<1<<<q):(ep q i).testBit s=s.testBit i:=by have a:=Ae.mp jt q (AM.mpr (by omega));simp only[i3,Ae,X,Ar] at a;exact(a i (AM.mpr b)).2 s (AM.mpr c)
lemma yg {q i:Nat}(c:q<=12)(b:i<q):ep q i<1<<<(1<<<q):=by have a:=Ae.mp jt q (AM.mpr (by omega));simp only[i3,Ae,X,A6] at a;exact(a i (AM.mpr b)).1
def u3:Z N:=(range 12).map fun i=>BitVec.ofNat 4096 (ep 12 i)
def is (m:Nat):Z (Nat×N):=(range 12).filterMap fun i=>if m.testBit i then some (i,u3.getD i P) else none
def h7 (m:Nat):=(is m).map Prod.snd
def eu (m:Nat):=h7 m
def sW (m j:Nat):=if m.testBit j then u3.getD j P else P
def e6 (m:Nat):N:=let x:=sW m;(x 0&&&x 7)|||(x 0&&&x 11)|||(x 1&&&x 6)|||(x 1&&&x 10)|||(x 1&&&x 11)|||(x 2&&&x 9)|||(x 2&&&x 10)|||(x 3&&&x 8)|||(x 3&&&x 9)|||(x 3&&&x 11)|||(x 4&&&x 7)|||(x 4&&&x 8)|||(x 4&&&x 10)|||(x 5&&&x 6)|||(x 5&&&x 7)|||(x 5&&&x 9)
def graph:N:=e6 4095
def ti (r:K)(j:B):=bit r (u3.getD j.val P)
def edge (x:B->Y):Y:=(x 0&&x 7)||(x 0&&x 11)||(x 1&&x 6)||(x 1&&x 10)||(x 1&&x 11)||(x 2&&x 9)||(x 2&&x 10)||(x 3&&x 8)||(x 3&&x 9)||(x 3&&x 11)||(x 4&&x 7)||(x 4&&x 8)||(x 4&&x 10)||(x 5&&x 6)||(x 5&&x 7)||(x 5&&x 9)
lemma fv:∀ (j:B) (r:K),bit r (u3.getD j.val P)=r.val.testBit j.val:=by intro j r;have a:u3.getD j.val P=BitVec.ofNat 4096 (ep 12 j.val):=(by simp[u3,j.isLt]);rw[a,bit,BitVec.getLsbD_ofNat,B3 r.isLt,AD];exact eC (BA 12) j.isLt (by simpa[Ag] using r.isLt)
lemma xt:∀ r:K,bit r graph=edge (ti r):=by intro r;simp only[graph,e6,sW,ti,bit,edge,B1,Aq];rfl
lemma gw:U graph:=by unfold U;decide +kernel
lemma iZ:Da (fun j:B=>u3.getD j.val P)=u3:=by decide +kernel
lemma xH (r:K):Da (ti r)=u3.map (bit r):=by rw[<-iZ,map_ofFn];rfl
lemma wo (a:Circuit)(h:PEqualNP.MetaComplexity.FanInTwo a)(i:Nat)(r:K):bit r ((ek a.gates u3).getD i P)=(a.wires (Da (ti r))).getD i J:=by rw[<-vO,wj _ _ _ (fun g b=>(h g b).1),xH];rfl
def gE (f:K->K)(a:N):=eV fun r=>bit (f r) a
lemma eX (f:K->K)(a:N)(r:K):bit r (gE f a)=bit (f r) a:=fZ _ _
lemma eR (f:K->K)(a:N):A (gE f a)=e4 f (A a):=by funext r;exact eX f a r
lemma iY (f:K->K)(d:Nat)(a b:N):gE f (V d a b)=V d (gE f a) (gE f b):=by apply fu;intro r;simp[eX,gT]
lemma xm (f:K->K)(c:Function.Surjective f):Function.Injective (gE f):=by intro a b h;apply Af;intro j d;have⟨r,g⟩:=c ⟨j,d⟩;have e:=Az (bit r) h;change bit ⟨j,d⟩ a=bit ⟨j,d⟩ b;rw[eX,eX,g] at e;exact e
lemma gg (f:K->K):gE f P=P/\gE f one=one:=by
 constructor<;>apply Af<;>intro j hj
 . exact(eX f P ⟨j,hj⟩).trans ((f5 _).trans (f5 ⟨j,hj⟩).symm)
 . exact(eX f one ⟨j,hj⟩).trans ((fM _).trans (fM ⟨j,hj⟩).symm)
lemma jw {u T k l}(h:Lv u T k l)(f:K->K)(i:Function.Surjective f):Lv u (gE f T) k (l.image (gE f)):=by
 have g:=xm f i;have⟨s,m⟩:=gg f;have j (v) (p:U v):U (gE f v):=⟨fun e=>p.1 (g (e.trans s.symm)),fun e=>p.2 (g (e.trans m.symm))⟩;induction h using Lv.ind with
 | stop q=>simpa using Lv.stop (j _ q)
 | @binary k zu a b d hd ha hb hab hf _ ih=>
   have c:gE f (V d a b)∉(insert a (insert b zu)).image (gE f):=by intro hm;have⟨v,o,r⟩:=A7.mp hm;exact hf (g r▸o)
   simp only[Ax,iY] at c ih ⊢;exact Lv.binary hd (j _ ha) (j _ hb) (fun n=>hab (g n)) c ih
lemma f0 {u T k g}(h:Lv u T k g)(none:u=J){r s:K}(e:bit r T=H)(c:bit s T=J):∃ a∈g,bit r a=H/\bit s a=J:=by
 induction h using Lv.ind with
 | stop f=>exact⟨_,by simp,e,c⟩
 | @binary k zu a b d hd ha hb hab hf _ ih=>
   have⟨v,l,f,i⟩:=ih;rcases A9.mp l with rfl|j
   . rw[gT] at f i;subst none;rcases eY hd with rfl|rfl|⟨h,_⟩|⟨h,_⟩
     . cases p:bit r a<;>cases q:bit s a<;>cases u:bit r b<;>cases z:bit s b<;>simp_all
     . cases p:bit r a<;>cases q:bit s a<;>cases u:bit r b<;>cases z:bit s b<;>simp_all
     . cases h
     . cases h
   . exact⟨v,A2 (A2 j),f,i⟩
def fL (u:Y)(a:Z N)(T:N)(zl:Nat):Prop:=∀ p bank,Rc u (a.map A) p bank->S u bank (A T)->zl<=p
def u1 (u:Y)(T:N)(cap:Nat)(vs:I N):Prop:=∀ k,k<=cap->¬Lv u T k vs
def ic (T:N)(b:Z N)(a:N):Prop:=∃ r s:K,bit r T≠bit s T/\∀ v∈b,v≠a->bit r v=bit s v
lemma xo {u f T g}(j:U T)(m:eN T=H)(l:f.all eN=H)(b:∀ a∈f,ic T f a)(c:u1 u T g f.toFinset):fL u f T (g+1):=by
 intro p bank h ha;obtain⟨k,t,v,d,i⟩:=uW j m l h ha;have n:f.toFinset=t:=by ext a;rw[A4];refine⟨fun q=>?_,i a⟩;obtain⟨r,s,o,e⟩:=b _ q;exact i6 d f a i r s o e
 by_contra! small;exact c k (by omega) (n.symm▸d)
lemma gM {v:N}(c:U v):¬ea (A v):=by
 rintro⟨b,h⟩;have a:iM J [] v:=by
  apply ik;cases b;. exact D5 (fu fun i=>(congrFun h i).trans (f5 i).symm)
  . exact D6 (fu fun i=>(congrFun h i).trans (fM i).symm)
 have a':eL [] v:=a;exact(a'.resolve_left (by simp)) c
lemma vB {c}(a b:Z (O c)):g0 (a++b)=g0 a+g0 b:=by simp[g0]
lemma jm {c}(xs:Z (O c))(b:∀ x∈xs,ea x):g0 xs=xs.length:=by induction xs with|nil=>simp[g0] | cons a xs d=>have f:=b a (by simp);simp only[f1,AY,fS,if_pos f,d (fun x e=>b x (by simp[e]))];omega
lemma vN {u}{w e:Z N}{T zg:N}(pT:U T)(nT:eN T=H)(nR:w.all eN=H)(pG:U zg)(r:K->K)(eq:gE r T=zg)(f8:∀ a∈w,S u (e.map A) (A (gE r a)))(c:I N)(f:∀ a∈c,ic T w a)(g:∀ a∈c,ea (A (gE r a)))(zl:Nat)(m:fL u e zg zl):fL u w T (zl+c.card):=by
 classical
 intro p bank hh z;have⟨k,vs,hk,l,x⟩:=uW pT nT nR hh z;have n:c⊆vs:=by intro a hs;obtain⟨i,j,hd,o⟩:=f a hs;exact i6 l w a x i j hd o
 let d:=c.toList++(vs \ c).toList;have nd:d.Nodup:=by simp only[d,nodup_append];refine⟨Be _,Be _,?_⟩;intro a z b hb he;subst b;exact(Am.mp (Bz.mp hb)).2 (Bz.mp z)
 have fe:d.toFinset=vs:=by ext a;simp[d,E2 n]
 have l':=tF l d nd fe;have gc:e4 r (A T)=A zg:=(eR _ _).symm.trans (Az A eq);have q:fK u (e.map A) ((d.map A).map (e4 r)):=by intro v hv;obtain⟨_,hm,rfl⟩:=Aj.mp hv;obtain⟨a,h,rfl⟩:=Aj.mp hm;rw[<-eR];exact f8 a (x _ (fe▸A4.mpr h))
 have t:=je r l' (gc▸gM pG) Rc.start q (zl:=zl) (gc▸m)
 have s:c.card<=g0 ((d.map A).map (e4 r)):=by
  simp only[d,B5,vB];let y:=(c.toList.map A).map (e4 r);have only:∀ v∈y,ea v:=by intro v hv;obtain⟨_,hm,rfl⟩:=Aj.mp hv;obtain⟨a,h,rfl⟩:=Aj.mp hm;rw[<-eR];exact g _ (Bz.mp h)
  have sz:=jm y only;simp only[y,AQ,Finset.length_toList] at sz;change c.card<=g0 y+_;rw[sz];omega
 omega
def eQ (c:Z N)(a b:N)(d:Nat)(f e:Y):Z N:=V d a b::kept f a (kept e b ((c.erase a).erase b))
lemma vD {l:Z N}(h:l.Nodup)(a:N):(l.erase a).toFinset=l.toFinset.erase a:=by ext x;simp[h.mem_erase_iff]
lemma vq {u}{T:N}{e:Nat}{m:Z N}(n:m.Nodup)(g:T∉m)(c:∀ a∈m,∀ b∈m,∀ d,eT u d->∀ ka kb,a≠b->V d a b∉m->U (V d a b)->(eQ m a b d ka kb).length<=e->u1 u T (e-1) (eQ m a b d ka kb).toFinset):u1 u T e m.toFinset:=by
 classical
 intro k hk h;generalize he:m.toFinset=vs at h;induction h using Lv.ind with
 | stop hp=>have mem:T∈m.toFinset:=he.symm▸Ao _;exact g (A4.mp mem)
 | @binary k zu a b d hd ha hb hab hf tail _=>
   have z:a∈m:=A4.mp (he.symm▸AL _ _);have w:b∈m:=A4.mp (he.symm▸A2 (AL _ _));have f:V d a b∉m:=fun h=>hf (he▸A4.mpr h);have r:=gA tail _ (AL _ _);let ka:=decide (a∈zu);let kb:=decide (b∈zu);let l:=(m.erase a).erase b;have q:l.toFinset=(m.toFinset.erase a).erase b:=by
    rw[show l=(m.erase a).erase b by rfl,vD (n.erase _) b,
     vD n a]
   have o:(kept ka a (kept kb b l)).toFinset=zu:=by
    rw[im,im,q,he];ext j;by_cases aa:a∈zu<;>by_cases bb:b∈zu<;>by_cases ja:j=a<;>
     by_cases jb:j=b<;>simp_all [ka,kb]
   have rn:l.Nodup:=(n.erase _).erase _;have s:a∉l:=fun h=>(n.not_mem_erase) (mem_of_mem_erase h);have v:b∉l:=(n.erase a).not_mem_erase;have t:=i5 kb b l rn v;have y:a∉kept kb b l:=by cases kb<;>simp[kept,s,hab]
   have x:(eQ m a b d ka kb).Nodup:=by refine B7.mpr ⟨?_,i5 ka a _ t y⟩;intro h;exact hf (A2 (A2 (o▸A4.mpr h)))
   have p:(eQ m a b d ka kb).toFinset=insert (V d a b) zu:=by change (V d a b::kept ka a (kept kb b l)).toFinset=_;simp[o]
   have sc:=gz tail;have i:(eQ m a b d ka kb).length<=e:=by rw[<-Ap x,p];omega
   exact c a z b w d hd ka kb hab f r i k (by omega) (p.symm▸tail)
def v5 (T:N)(a:Nat)(d b:Fin a->K)(c:N->BV a×BV a):Prop:=(∀ i,bit (d i) T=H/\bit (b i) T=J)/\∀ w i,(c w).1.getLsbD i.val=bit (d i) w/\(c w).2.getLsbD i.val=bit (b i) w
def eP {n}(a:Y)(s:BV n×BV n):BV n:=if a then s.1&&&~~~s.2 else s.1^^^s.2
def f8 {n}(oriented:Y)(sig:N->BV n×BV n):Z N->BV n
 | []=>0
 | a::ws=>eP oriented (sig a)|||f8 oriented sig ws
lemma vf {n:Nat}{b:Y}{c:N->BV n×BV n}{ws:Z N}{i:F n}:(f8 b c ws).getLsbD i.val=H↔∃ a∈ws,(eP b (c a)).getLsbD i.val=H:=by induction ws with|nil=>simp[f8] | cons a ws d=>simp only[f8,B1,Ai,d,Ab,exists_eq_or_imp]
lemma wU {u T k n}(h:Lv u T k n){m:Z N}(o:m.toFinset=n){d:Nat}{r s:Fin d->K}{g}(b:v5 T d r s g)(c:Y)(e:c=H->u=J):f8 c g m=BitVec.allOnes d:=by
 apply Af;intro j p;let i:Fin d:=⟨j,p⟩;have f:=(b.1 i).1;have q:=(b.1 i).2;rw[BL];simp only[p,B6];apply(vf (i:=i)).mpr;cases c with
 | false=>
   have⟨a,l,w⟩:=fD h (show bit (r i) T≠bit (s i) T by simp[f,q])
   refine⟨a,A4.mp (o.symm▸l),?_⟩;simp only[eP,Ak,AB,CE,(b.2 a i).1,(b.2 a i).2];cases x:bit (r i) a<;>cases y:bit (s i) a<;>simp_all
 | true=>obtain⟨a,l,t,v⟩:=f0 h (e rfl) f q;refine⟨a,A4.mp (o.symm▸l),?_⟩;simp only[eP,AX,Aq,AW,i.isLt,B6,(b.2 a i).1,(b.2 a i).2,t,v,Dy,Bool.and_self]
lemma ie {u T c k}(h:Lv u T k (List.toFinset c)){n:Nat}{r s:F n->K}{b}(a:v5 T n r s b):f8 (!u) b c=BitVec.allOnes n:=by apply wU h rfl a;simp
def t3 (u:Y)(b:Z N)(T d:N)(c:Nat):Prop:=∃ (f:K->K) (roots:Z N),(∀ r,bit (f r) d=H)/\(∀ a∈b,S u (roots.map A) (e4 f (A a)))/\¬ea (e4 f (A T))/\∀ p bank,Rc u (roots.map A) p bank->S u bank (e4 f (A T))->c<=p
def fJ (d a:N):=a&&&d
def em (u:Y)(d:N)(b:Z N)(a:N):=let m:=fJ d a;m==P||m==d||(b.map (fJ d)).any (fun v=>v==m)||(u&&(let c:=fJ d (neg a);(b.map (fJ d)).any (fun v=>v==c)))
lemma vi {f:K->K}{d a b:N}(c:∀ r,bit (f r) d=H)(e:fJ d a=fJ d b):e4 f (A a)=e4 f (A b):=by funext r;have h:=Az (bit (f r)) e;change bit (f r) a=bit (f r) b;simpa only[bit,fJ,Aq,show d.getLsbD (f r).val=H from c r,Cb] using h
lemma wf {f:K->K}{d a:N}(b:∀ r,bit (f r) d=H)(e:fJ d a=P):e4 f (A a)=fun _=>J:=by funext r;have c:=Az (bit (f r)) e;change bit (f r) a=J;rw[f5] at c;simpa only[bit,fJ,Aq,show d.getLsbD (f r).val=H from b r,Cb] using c
lemma v7 {f:K->K}{d a:N}(b:∀ r,bit (f r) d=H)(e:fJ d a=d):e4 f (A a)=fun _=>H:=by funext r;have c:=Az (bit (f r)) e;change bit (f r) a=H;rw[b r] at c;simpa only[bit,fJ,Aq,show d.getLsbD (f r).val=H from b r,Cb] using c
def f6 (u:Y)(f:K->K)(c:Z (O K))(b:Z N):=∀ a∈b,S u c (e4 f (A a))
lemma ee {u}{f:K->K}{d a:N}{i j}(g:∀ r,bit (f r) d=H)(b:f6 u f i j)(c:em u d j a=H):S u i (e4 f (A a)):=by
 simp only[em,any_map,DI,Ai,X,Ar,Bf] at c;rcases c with ((m|o)|⟨v,l,k⟩)|⟨n,v,l,k⟩;. exact D6 (D5 ⟨J,wf g m⟩)
 . exact D6 (D5 ⟨H,v7 g o⟩)
 . exact vi g k▸b v l
 . have h:=jF n (vi g k▸b v l);rw[tf] at h;have e:jh (e4 f (jh (A a)))=e4 f (A a):=by funext r;simp[jh,e4]
   rwa[e] at h
abbrev g6:=Nat×N×N
def eM (c:g6):=V c.1 c.2.1 c.2.2
def tg (u:Y)(d:Nat):=decide (d<2)||(u&&decide (d<4))
lemma xL {u d}(h:tg u d=H):eT u d:=by simpa[tg,eT] using h
def jp (u:Y)(d:N)(a:Z N)(c:g6):=tg u c.1&&(em u d a c.2.1&&em u d a c.2.2)
lemma vn {u}{f:K->K}{d:N}{h j i q}(g:∀ r,bit (f r) d=H)(m:Rc u h q j)(k:f6 u f j i)(c:g6)(b:jp u d i c=H):∃ next,Rc u h (q+1) next/\f6 u f next (eM c::i):=by
 simp only[jp,X] at b;obtain⟨p,x,y,e,o,n,_,_⟩:=h8 (xL b.1) (ee g k b.2.1) (ee g k b.2.2);refine⟨_,Rc.two p m o n,?_⟩;intro a l;rcases Ab.mp l with rfl|l;. rw[eM,tw,gm,e];exact D5 (by simp)
 . exact eW _ (k _ l)
def eI (d a:N):=fJ d a==P||fJ d a==d
lemma jg {d:N}{f:K->K}(b:∀ r,bit (f r) d=H)(ws:Z N):ws.countP (eI d)<=g0 ((ws.map A).map (e4 f)):=by
 classical
 induction ws with
 | nil=>simp[g0]
 | cons a ws c=>
   simp only[BR,As,f1];cases h:eI d a;. simpa using (Nat.le_add_left _ _ |> c.trans)
   . have g:ea (e4 f (A a)):=by
      have i:fJ d a=P\/fJ d a=d:=(by simpa only[eI,Ai,Ar] using h);rcases i with e|j;. exact⟨J,wf b e⟩
      . exact⟨H,v7 b j⟩
     simpa[fS,g,Aw] using Nat.succ_le_succ c
abbrev kU:=N×N×K
def tD (d r:K):K:=if h:r.val<4096-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(4096-d.val),by omega⟩
def tJ (d:K):K:=Fin.ofNat 4096 (4096-d.val)
def j2 (m:kU)(r:K):K:=if bit r m.1 then tD m.2.2 r else if bit r m.2.1 then tD (tJ m.2.2) r else r
def sU (m a b:N):=(m&&&a)|||(~~~m&&&b)
def E {a:Type}(n:Nat)(f:Nat->a):a:=Nat.rec (f 0) (fun k _=>f (Nat.succ k)) n
lemma R {a:Type}(n:Nat)(f:Nat->a):E n f=f n:=by cases n<;>rfl
def kk {w:Nat}(x:BV w){a:Type}(k:BV w->a):a:=E x.toNat fun n=>k (BitVec.ofNat w n)
lemma kw {w:Nat}(x:BV w){a:Type}(k:BV w->a):kk x k=k x:=by unfold kk;rw[R];congr 1;apply DS;simp
def wW {c:Type}(l:LP)(k:LP->c):c:=List.rec (fun k=>k []) (fun p _ d k=>E p.1 fun a=>E p.2 fun b=>d fun e=>k ((a,b)::e)) l k
def jl (m:kU)(a:N):=kk a fun a=>sU m.1 (a.rotateRight m.2.2.val) (sU m.2.1 (a.rotateRight (tJ m.2.2).val) a)
lemma ye (m:kU)(a:N):jl m a=sU m.1 (a.rotateRight m.2.2.val) (sU m.2.1 (a.rotateRight (tJ m.2.2).val) a):=kw _ _
lemma xY (d r:K)(a:N):bit r (a.rotateRight d.val)=bit (tD d r) a:=by unfold bit;rw[BitVec.getLsbD_rotateRight_of_lt d.isLt];by_cases h:r.val<4096-d.val<;>simp[tD,h,r.isLt]
lemma xv (p x y:Y):(p&&x||!p&&y)=(if p then x else y):=by cases p<;>simp
lemma wE (r:K)(m a b:N):bit r (sU m a b)=if bit r m then bit r a else bit r b:=by simp only[bit,sU,Aq,B1,AW,r.isLt,B6,AD];exact xv _ _ _
lemma vW (r:K)(m:kU)(a:N):bit r (jl m a)=bit (j2 m r) a:=by simp only[ye,wE,xY,j2];cases bit r m.1<;>cases bit r m.2.1<;>rfl
def et (a:Z kU)(r:K):=a.foldl (fun j m=>j2 m j) r
def ed (b:Z kU)(a:N):=b.foldr jl a
lemma hE (ms:Z kU)(a:N)(r:K):bit r (ed ms a)=bit (et ms r) a:=by induction ms generalizing r with|nil=>rfl | cons m ms b=>exact(vW r m _).trans (b _)
lemma ew (b:Z kU)(a:N):ed b a=gE (et b) a:=by apply Af;intro j c;exact(hE b a ⟨j,c⟩).trans (eX _ _ ⟨j,c⟩).symm
def tZ (a:Z N)(w:N):=w==P||w==one||a.contains w
lemma wX {u a w}(b:tZ a w=H):S u (a.map A) (A w):=by
 simp only[tZ,Ai,Ar,Bo,A6] at b;rcases b with (rfl|rfl)|c;. exact D6 (D5 ⟨J,funext f5⟩)
 . exact D6 (D5 ⟨H,funext fM⟩)
 . exact D5 (Qm c)
def gl (d:Z kU)(b:Z N)(T:N)(c:Z N)(e:N):=ed d T==e&&b.all (fun a=>tZ c (ed d a))
lemma gI {u e c T b f}(d:gl e c T b f=H):gE (et e) T=f/\∀ a∈c,S u (b.map A) (A (gE (et e) a)):=by simp only[gl,X,Ar,Ae,ew] at d;exact⟨d.1,fun a g=>wX (d.2 a g)⟩
lemma wm {u f c T b e d}(k:gl f c T b e=H)(j:U T)(l:eN T=H)(i:c.all eN=H)(h:U e)(g:fL u b e d):fL u c T d:=by obtain⟨m,a⟩:=gI k;simpa using vN j l i h (et f) m a ∅ (by simp) (by simp) d g
lemma xW {u i g T f h k d}(m:gl i g T f h=H)(j:ed i d=one)(b:U h)(l:fL u f h k):t3 u g T d k:=by
 obtain⟨n,e⟩:=gI m;have c:e4 (et i) (A T)=A h:=(eR _ _).symm.trans (Az A n);refine⟨et i,f,?_,?_,?_,?_⟩;. intro r;rw[<-hE,j,fM]
 . intro a o;rw[<-eR];exact e a o
 . rw[c];exact gM b
 . rw[c];exact l
def tO (T:N)(b:Z N)(a:N)(c:K×K):=(bit c.1 T !=bit c.2 T)&&b.all (fun w=>w==a||bit c.1 w==bit c.2 w)
lemma xO {T roots a rs}(c:tO T roots a rs=H):ic T roots a:=by simp only[tO,X,CA,Ae,Ai,Ar] at c;exact⟨rs.1,rs.2,c.1,fun w d b=>(c.2 w d).resolve_left b⟩
def el (T:N)(b:Z N)(c:Z (N×K×K)):=eN T&&b.all eN&&c.all (fun a=>tO T b a.1 a.2)
lemma ga {T raw xs}(b:el T raw xs=H):∀ a∈(xs.map G).toFinset,ic T raw a:=by simp only[el,X] at b;intro a c;obtain⟨⟨a,r,s⟩,hm,rfl⟩:=Aj.mp (A4.mp c);exact xO (Ae.mp b.2 _ hm)
lemma fs {T raw xs}(a:el T raw xs=H):eN T=H/\raw.all eN=H:=by simp only[el,X] at a;exact a.1
lemma vV {u f T}(b:U T)(g:Z (N×K×K))(h:el T f g=H):fL u f T ((g.map G).toFinset.card-1):=by
 intro p bank hr hit;have⟨k,m,o,c,i⟩:=uW b (fs h).1 (fs h).2 hr hit;have n:(g.map G).toFinset.card<=m.card:=by apply Aa;intro a l;obtain⟨r,s,j,e⟩:=ga h a l;exact i6 c f a i r s j e
 have d:=gz c;omega
def gH (d:Z kU)(T:N)(b:Z N)(c:Z N)(f:N)(e:Z (N×K×K)):=gl d b T c f&&el T b e&&e.all (fun a=>ed d a.1==P||ed d a.1==one)
lemma w8 {u n T i f k l j}(g:gH n T i f k l=H)(c:U T)(b:U k)(e:fL u f k j):fL u i T (j+(l.map G).toFinset.card):=by
 simp only[gH,X] at g;obtain⟨o,d⟩:=gI g.1.1;apply vN c (fs g.1.2).1 (fs g.1.2).2 b _ o d _ (ga g.1.2) _ j e;intro a p;obtain⟨⟨v,r,s⟩,hm,rfl⟩:=Aj.mp (A4.mp p);have m:=Ae.mp g.2 _ hm;simp only[Ai,Ar,ew] at m;rcases m with h|h;. rw[h];exact⟨J,funext f5⟩
 . rw[h];exact⟨H,funext fM⟩
def g5 (z o:Nat):N:=if z&&&o !=0 then P else(range 12).foldl (fun w i=>if z.testBit i then w&&&~~~(u3.getD i P) else if o.testBit i then w&&&u3.getD i P else w) one
def j8 (z o:Nat):Z kU:=(range 12).filterMap fun j=>let x:=u3.getD j P;let a:=Fin.ofNat 4096 (1<<<j);if z.testBit j then some (P,x,a) else if o.testBit j then some (~~~x,P,a) else none
def eo (v:Nat):kU:=let i:=v&&&15;let j:=v>>>4;let a:=u3.getD i P;let b:=u3.getD j P;let d:=(1<<<j)-(1<<<i);(a&&&~~~b,b&&&~~~a,Fin.ofNat 4096 d)
def iW (_t mask:Nat):Z (N×K×K):=(is mask).map fun(i,a)=>(a,0,Fin.ofNat 4096 (1<<<i))
def eg (m b:Nat):Z (N×K×K):=(is m).map fun(i,a)=>let r:=1<<<((b>>>(4*i))&&&15);(a,Fin.ofNat 4096 r,Fin.ofNat 4096 (r|||(1<<<i)))
def eD (T:N):=T !=P&&T !=one
lemma eJ (T:N)(h:eD T=H):U T:=by simpa only[eD,U,X,CA] using h
abbrev gu:=Nat×Nat×Nat×PP
def tI (m z o:Nat):=m^^^(m&&&(z|||o))
def fE (m:Nat):N:=e6 m
def g4 (m:Nat)(c:gu):Nat:=m%4096+4096*(c.1/4096)
def hZ (m:Nat)(c:gu)(b:NN):Y:=let(z,o,q,s,i):=c;let h:=j8 z o;let d:=g4 m c;let a:=tI d (z%4096) o;let f:=ed h (fE m);let g:=iW (z/4096+80) s;let e:=(g.map G).toFinset.card;eD f&&gl h (eu d) (fE m) (eu a) f&&(ed h (g5 z o)==one)&&(if q=0 then el f (eu a) g&&decide (i<=e-1) else eD (e6 q)&&gH (j8 (tI a q 0) 0) f (eu a) (eu q) (e6 q) g&&decide (i<=b q+e))
lemma wT {u}{m:Nat}(c:gu)(a:NN)(b:∀ q,fL u (eu q) (e6 q) (a q))(ok:hZ m c a=H):t3 u (eu (g4 m c)) (fE m) (g5 c.1 c.2.1) c.2.2.2.2:=by
 revert ok;obtain⟨z,o,q,s,n⟩:=c;intro ok;let h:=j8 z o;let d:=g4 m (z,o,q,s,n);let e:=tI d (z%4096) o;let l:=ed h (fE m);let r:=iW (z/4096+80) s;change (((eD l&&gl h (eu d) (fE m) (eu e) l)&&(ed h (g5 z o)==one))&&_)=H at ok;simp only[X,Ar] at ok;apply xW ok.1.1.2 ok.1.2 (eJ _ ok.1.1.1);intro p f j k;have g:=ok.2;by_cases i:q=0;. simp only[i,if_true,X,A6] at g;exact g.2.trans (vV (eJ _ ok.1.1.1) r g.1 p f j k)
 . simp only[i,if_false,X,A6] at g;exact g.2.trans (w8 g.1.2 (eJ _ ok.1.1.1) (eJ _ g.1.1) (b q) p f j k)
def t4 (a c:Nat)(b:W):=(eD (e6 a)&&eN (e6 a)&&(eu a).all eN)&&eD (e6 c)&&gl (b.map eo) (eu a) (e6 a) (eu c) (e6 c)
lemma xJ {u c b e a}(d:t4 c b a=H)(h:fL u (eu b) (e6 b) e):fL u (eu c) (e6 c) e:=by simp only[t4,X] at d;exact wm d.2 (eJ _ d.1.1.1.1) d.1.1.1.2 d.1.1.2 (eJ _ d.1.2) h
def bB (entries:LP)(q:Nat):=((entries.find? (fun a=>a.1==q)).map Prod.snd).getD 0
lemma bS {u}(entries:LP)(sound:∀ e∈entries,fL u (eu e.1) (e6 e.1) e.2)(q:Nat):fL u (eu q) (e6 q) (bB entries q):=by unfold bB;cases h:entries.find? (fun a=>a.1==q) with|none=>exact fun _ _ _ _=>AU _ | some e=>have d:=E6 h;have b:(fun a:PP=>a.1==q) e=H:=find?_some (p:=fun a:PP=>a.1==q) (a:=e) h;have c:e.1=q:=Ar.mp b;simpa only[BU,BS,c] using sound e d
abbrev B9:=N×Nat×Nat×Z N
def B9.d (c:B9):N:=c.1
def B9.b (c:B9):Nat:=c.2.1
def B9.p (c:B9):Nat:=c.2.2.1
def B9.w (c:B9):Z N:=c.2.2.2
def gD (u:Y)(a:Z N)(T:N)(c:B9):=∃ (f:K->K) (roots:Z N) (bank:Z (O K)),(∀ r,bit (f r) c.d=H)/\¬ea (e4 f (A T))/\(∀ q ws,Rc u (roots.map A) q ws->S u ws (e4 f (A T))->c.b<=q)/\Rc u (roots.map A) c.p bank/\f6 u f bank c.w/\True
lemma wD {u h0 T c}(l:gD u h0 T c)(k:Nat)(q:Z N)(d:g6)(r:Y)(e:∀ a∈q,em u c.d c.w a=H)(o:if r then jp u c.d c.w d=H else em u c.d c.w (eM d)=H)(s:k+c.p+r.toNat<c.b+(eM d::q).countP (eI c.d))(nd:(eM d::q).Nodup):u1 u T k (eM d::q).toFinset:=by
 intro t ht run;have⟨f,x,p,g,nc,lo,hp,hs,_⟩:=l;let z:=eM d::q;have j (n:Nat) (i:Z (O K)) (reach:Rc u (x.map A) n i) (zs:f6 u f i (eM d::q)) (le:n=c.p+r.toNat):False:=by
  have f8:fK u i ((z.map A).map (e4 f)):=by intro v hv;obtain⟨_,y,rfl⟩:=Aj.mp hv;obtain⟨a,ha,rfl⟩:=Aj.mp y;exact zs _ ha
  have b:=je f (tF run z nd rfl) nc reach f8 lo;have cm:=jg g z;change k+c.p+r.toNat<c.b+z.countP (eI c.d) at s;omega
 cases r with
 | false=>
   apply j _ _ hp _ rfl;intro a h;rcases Ab.mp h with rfl|y;. exact ee g hs o
   . exact ee g hs (e _ y)
 | true=>
   obtain⟨i,hr,hc⟩:=vn g hp hs d o;apply j _ _ hr _ rfl;intro a h;rcases Ab.mp h with rfl|y;. exact hc _ (by simp)
   . have m:∀ v∈c.w,S u i (e4 f (A v)):=fun v hu=>hc v (AK _ hu);exact ee g m (e _ y)
def gk (u:Y)(c:B9)(k:Nat)(e:Z N)(f:g6):=let z:=eM f;let a:=!(em u c.d c.w z);((k+c.p+a.toNat<c.b+(z::e).countP (eI c.d))&&e.all (em u c.d c.w))&&(!a||jp u c.d c.w f)
lemma jJ {u g T c}(d:gD u g T c){k e f}(h:(eM f::e).Nodup)(a:gk u c k e f=H):u1 u T k (eM f::e).toFinset:=by
 let b:=!(em u c.d c.w (eM f));apply wD d k e f b _ _ _ h
 . simp only[gk,X,Ae] at a;exact a.1.2
 . simp only[gk,X,Ai] at a;cases i:em u c.d c.w (eM f)<;>simp_all [b]
 . simp only[gk,X,A6] at a;exact a.1.1
abbrev fU:=BV 320
abbrev t9:=fU×fU
abbrev D:=N×t9
def gZ {n:Nat}(r:F n->K)(v:N):BV n:=(BZ (Da (fun i=>bit (r i) v))).cast BQ
lemma fd {n:Nat}(r:F n->K)(v:N)(i:F n):(gZ r v).getLsbD i.val=bit (r i) v:=by simp only[gZ,BitVec.getLsbD_cast,C3,A1,Cz];simp[i.isLt]
def f3 (r s:Fin 320->K)(a:N):t9:=(gZ r a,gZ s a)
def g8 (T:N)(r s:Fin 320->K):=∀ i,bit (r i) T=H/\bit (s i) T=J
lemma uX {T r s}(h:g8 T r s):v5 T 320 r s (f3 r s):=by exact⟨h,fun a i=>⟨fd _ _ _,fd _ _ _⟩⟩
def ex (r s:Fin 320->K)(x:D):=x.2=f3 r s x.1
def bv {n:Nat}(d:Nat)(a b:BV n):BV n:=if d=0 then a&&&b else if d=1 then a|||b else if d=2 then a&&&~~~b else ~~~a&&&b
def ji (d:Nat)(x y:D):D:=(V d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
lemma yb {n:Nat}(r:F n->K)(d:Nat)(a b:N):gZ r (V d a b)=bv d (gZ r a) (gZ r b):=by apply Af;intro j c;have h:=fd r (V d a b) ⟨j,c⟩;rw[gT,<-fd r a ⟨j,c⟩,<-fd r b ⟨j,c⟩] at h;rw[h];unfold bv;split_ifs<;>simp[c]
lemma j1 {r s x y}(d)(b:ex r s x)(a:ex r s y):ex r s (ji d x y):=by change x.2=_ at b;change y.2=_ at a;simp[ex,ji,f3,yb,b,a]
def C:D:=(P,0,0)
lemma xP (r s):ex r s C:=by
 apply Prod.ext<;>apply Af<;>intro j hj
 . change (0:fU).getLsbD j=(gZ r P).getLsbD j;rw[show (gZ r P).getLsbD j=bit (r ⟨j,hj⟩) P from fd _ _ ⟨j,hj⟩,f5];simp
 . change (0:fU).getLsbD j=(gZ s P).getLsbD j;rw[show (gZ s P).getLsbD j=bit (s ⟨j,hj⟩) P from fd _ _ ⟨j,hj⟩,f5];simp
lemma wd {r s a}(b:∀ v∈a,ex r s v)(i:Nat):ex r s (List.getD a i C):=by simp only[A1];cases e:a[i]? with|none=>exact xP _ _ | some v=>exact b _ (Dh e)
def fq (a:Nat->fU)(i:Fin 320):K:=(BZ (Da (fun j:B=>(a j.val).getLsbD i.val))).toFin.cast (by simp)
lemma jD (a:Nat->fU)(i:Fin 320)(j:B):bit (fq a i) (u3.getD j.val P)=(a j.val).getLsbD i.val:=by rw[fv];change (BZ (Da (fun h:B=>(a h.val).getLsbD i.val))).getLsbD j.val=_;simp only[C3,A1,Cz];simp[j.isLt]
def tY (m:Nat)(p q:Nat->fU):Z D:=(is m).map (fun(j,a)=>(a,p j,q j))
lemma ij {m j a}(h:(j,a)∈is m):j<12/\a=u3.getD j P:=by
 have⟨v,c,b⟩:=Bw.mp h;simp only[AM] at c;split at b
 next=>
  cases b;exact⟨c,rfl⟩
 next=>contradiction
lemma xQ (m)(p q:Nat->fU):∀ a∈tY m p q,ex (fq p) (fq q) a:=by
 intro a ha;obtain⟨⟨j,v⟩,hv,rfl⟩:=Aj.mp ha;obtain⟨b,rfl⟩:=ij hv;apply Prod.ext<;>apply Af<;>intro i hi
 . exact(jD p ⟨i,hi⟩ ⟨j,b⟩).symm.trans (fd _ _ ⟨i,hi⟩).symm
 . exact(jD q ⟨i,hi⟩ ⟨j,b⟩).symm.trans (fd _ _ ⟨i,hi⟩).symm
def uT (m:Nat)(v:Nat->fU):fU:=let x:=fun j=>if m.testBit j then v j else 0;(x 0&&&x 7)|||(x 0&&&x 11)|||(x 1&&&x 6)|||(x 1&&&x 10)|||(x 1&&&x 11)|||(x 2&&&x 9)|||(x 2&&&x 10)|||(x 3&&&x 8)|||(x 3&&&x 9)|||(x 3&&&x 11)|||(x 4&&&x 7)|||(x 4&&&x 8)|||(x 4&&&x 10)|||(x 5&&&x 6)|||(x 5&&&x 7)|||(x 5&&&x 9)
lemma xF (m:Nat)(v:Nat->fU)(i:Fin 320)(j:B):bit (fq v i) (sW m j.val)=((if m.testBit j.val then v j.val else 0):fU).getLsbD i.val:=by
 by_cases a:m.testBit j.val=H;. simpa[sW,a] using jD v i j
 . simp[sW,a,f5]
lemma y1 (m:Nat)(v:Nat->fU)(i:Fin 320):bit (fq v i) (e6 m)=(uT m v).getLsbD i.val:=by have a (j:Nat) (hj:j<12):(sW m j).getLsbD (fq v i).val=((if m.testBit j then v j else 0):fU).getLsbD i.val:=xF m v i ⟨j,hj⟩;simp only[bit,e6,uT,Aq,B1];simp only[a 0 (by decide),a 1 (by decide),a 2 (by decide),a 3 (by decide),a 4 (by decide),a 5 (by decide),a 6 (by decide),a 7 (by decide),a 8 (by decide),a 9 (by decide),a 10 (by decide),a 11 (by decide)]
abbrev lw:=fU×fU×fU
def gY (z:fU)(c:lw):lw:=kk z fun z=>kk (z|||c.1) fun d=>kk ((z&&&~~~c.1)|||(c.2.1&&&~~~z)) fun a=>kk ((z&&&c.2.1)|||(c.2.2&&&~~~z)) fun b=>(d,a,b)
lemma tv (z:fU)(c:lw):gY z c=(z|||c.1,(z&&&~~~c.1)|||(c.2.1&&&~~~z),(z&&&c.2.1)|||(c.2.2&&&~~~z)):=by unfold gY;simp[kw]
def ei (d:Y)(v:Z D):lw:=v.foldr (fun a c=>gY (eP d a.2) c) (0,0,0)
def i7 (c:lw)(a:fU):fU:=c.1&&&~~~(c.2.1&&&a)
def sn (c:lw)(a b:fU):fU:=c.1&&&~~~((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b)))
lemma xC (c:lw)(a:fU):i7 (gY a c) a=c.1:=by apply Af;intro i b;simp only[i7,tv,B1,Aq,AW,b,B6,AD];cases a.getLsbD i<;>cases c.1.getLsbD i<;>cases c.2.1.getLsbD i<;>rfl
lemma yf (c:lw)(a b:fU):sn (gY a (gY b c)) a b=c.1:=by
 apply Af;intro i d;simp only[sn,tv,B1,Aq,AW,d,B6,AD];cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i<;>
  cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
lemma xA (c:lw)(a b:fU):gY a (gY b c)=gY b (gY a c):=by
 apply Prod.ext
 . apply Af;intro i d;simp only[tv,B1];cases a.getLsbD i<;>cases b.getLsbD i<;>rfl
 . apply Prod.ext<;>apply Af<;>intro i d<;>
   simp only[tv,B1,Aq,AW,d,B6,AD]<;>
   cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i<;>
   cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
lemma ve (d:Y){l r:Z D}(h:l.Perm r):ei d l=ei d r:=by induction h with|nil=>rfl | cons a _ c=>exact Az (gY (eP d a.2)) c | swap a b t=>exact xA _ _ _ | trans _ _ e f=>exact e.trans f
lemma vI (d:Y)(v:Z D){r s}(b:∀ a∈v,ex r s a):(ei d v).1=f8 d (f3 r s) (v.map G):=by induction v with|nil=>rfl | cons a v c=>change (gY (eP d a.2) (ei d v)).1=eP d (f3 r s a.1)|||_;rw[tv];rw[show a.2=f3 r s a.1 from b _ (by simp),c (fun a e=>b a (by simp[e]))]
def gj (c:Z D)(a:D)(b:Y):=if b then c else c.erase a
def il (c:Z D)(a b:D)(e d:Y):=gj (gj c a e) b d
lemma jA {b:Z D}(a:D)(c:a∈b):b.Perm (a::b.erase a):=Dg c
lemma tQ {c:Z D}(d:Y)(a:D)(e:a∈c)(b:Y):(ei d (gj c a b)).1=(if b then(ei d c).1 else i7 (ei d c) (eP d a.2)):=by
 cases b;. change (ei d (c.erase a)).1=i7 (ei d c) _;rw[ve d (jA a e)];exact(xC _ _).symm
 . rfl
lemma xx {d:Z D}(a b:D)(e:a∈d)(f:b∈d)(c:a≠b):d.Perm (a::b::(d.erase a).erase b):=by have g:b∈d.erase a:=(DF (Du c)).mpr f;exact(jA a e).trans (List.Perm.cons _ (jA b g))
lemma xG {c:Z D}(d:Y)(a b:D)(g:a∈c)(h:b∈c)(i:a≠b)(f e:Y):(ei d (il c a b f e)).1=(if f then(if e then(ei d c).1 else i7 (ei d c) (eP d b.2)) else if e then i7 (ei d c) (eP d a.2) else sn (ei d c) (eP d a.2) (eP d b.2)):=by
 cases f<;>cases e
 . change (ei d ((c.erase a).erase b)).1=sn (ei d c) _ _;rw[ve d (xx a b g h i)];exact(yf _ _ _).symm
 . exact tQ d a g J
 . exact tQ d b h J
 . rfl
def jC (a b:Z N):=(a.all (fun x=>b.contains x))&&(b.all (fun x=>a.contains x))
lemma jd {b c}(h:jC b c=H):b.toFinset=c.toFinset:=by simp only[jC,X,Ae,Bo,A6] at h;ext a;simp only[A4];exact⟨h.1 a,h.2 a⟩
def sg (v:lw)(a b:fU)(d c:Y):=if d then(if c then v.1 else i7 v b) else if c then i7 v a else sn v a b
lemma j6 (b:Z D)(a:D)(k:Y):(gj b a k).Sublist b:=by
 cases k;. exact erase_sublist
 . exact List.Sublist.refl _
lemma wG (c:Z D)(a b:D)(e d:Y):(il c a b e d).Sublist c:=(j6 _ _ _).trans (j6 _ _ _)
lemma xM (c:Z D)(a b:D)(e d:Y)(g:a∈c)(f:b∈c)(h:a≠b):(il c a b e d).length=c.length-(if e then 0 else 1)-(if d then 0 else 1):=by have i:b∈c.erase a:=(DF (Du h)).mpr f;cases e<;>cases d<;>simp[il,gj,BH g,BH f,BH i]
def iQ (c:Z D)(e:Nat)(a b:D)(f d:Y):=(ji e a b).1::(il c a b f d).map G
lemma iJ {v:Z N}{w:N}(a:N)(k:Y):w∈kept k a v↔(w=a/\k=H)\/w∈v:=by cases k<;>simp[kept]
lemma tR {v:Z D}(b:v.Nodup)(a w:D)(k:Y):w∈gj v a k↔w∈v/\(w≠a\/k=H):=by cases k<;>simp[gj,b.mem_erase_iff,and_comm]
lemma j7 {ws:Z D}(h:(ws.map G).Nodup){a b:D}(f:a∈ws)(i:b∈ws)(e:a.1=b.1):a=b:=by
 induction ws with
 | nil=>simp at f
 | cons w ws j=>
   have⟨g,k⟩:=B7.mp h;rcases Ab.mp f with rfl|d<;>rcases Ab.mp i with rfl|c
   . rfl
   . exact False.elim (g (by change a.1∈_;rw[e];exact Qm c))
   . exact False.elim (g (by change b.1∈_;rw[<-e];exact Qm d))
   . exact j k d c
lemma v6 {e:Z D}(h:(e.map G).Nodup){a b:D}(k:a∈e)(l:b∈e)(g i:Y)(v:N):v∈(il e a b g i).map G↔v∈e.map G/\(v≠a.1\/g=H)/\(v≠b.1\/i=H):=by
 have j:=h.of_map;have m:=j.sublist (j6 e a g);simp only[il,Aj,tR j,tR m];constructor;. rintro⟨w,f,rfl⟩;exact⟨⟨_,f.1.1,rfl⟩,f.1.2.imp (fun d c=>d (j7 h f.1.1 k c)) id,f.2.imp (fun d c=>d (j7 h f.1.1 l c)) id⟩
 . rintro⟨⟨w,n,rfl⟩,h1,h2⟩;exact⟨w,⟨⟨n,h1.imp (fun d c=>d (Az G c)) id⟩,h2.imp (fun d c=>d (Az G c)) id⟩,rfl⟩
lemma yd {c:Z D}(h:(c.map G).Nodup){a b:D}(i:a∈c)(j:b∈c)(k:a.1≠b.1)(d:Nat)(g e:Y):(iQ c d a b g e).toFinset=(eQ (c.map G) a.1 b.1 d g e).toFinset:=by ext v;have m:=Qm (f:=G) i;have bv':=Qm (f:=G) j;simp only[iQ,eQ,Bi,A9,A4,v6 h i j,iJ,(h.erase _).mem_erase_iff,h.mem_erase_iff,ji];by_cases l:v=a.1<;>by_cases n:v=b.1<;>cases g<;>cases e<;>simp_all
lemma jU {u}(v:Z N)(f:v.Nodup)(a b:N)(d:Nat)(g:eT u d)(e c:Y):(eQ v a b d e c).toFinset=(eQ v b a (iE d) c e).toFinset:=by ext x;simp only[eQ,Bi,A9,A4,iJ,(f.erase _).mem_erase_iff,f.mem_erase_iff,js g a b];tauto
lemma wM (r s:K)(h:∀ a∈u3,bit r a=bit s a):r=s:=by
 apply Fin.ext;apply AF;intro j;by_cases c:j<12
 . let i:B:=⟨j,c⟩;have d:u3.getD i.val P∈u3:=by rw[<-iZ];exact mem_ofFn.mpr ⟨i,rfl⟩
   exact(fv i r).symm.trans ((h _ d).trans (fv i s))
 . have b:4096<=2^j:=by change 2^12<=2^j;exact Ba (by decide) (by omega)
   exact(AH (lt_of_lt_of_le r.isLt b)).trans (AH (lt_of_lt_of_le s.isLt b)).symm
def tT (p q:Z kU):=u3.all (fun a=>ed p (ed q a)==a)
lemma iu {p q}(h:tT p q=H)(r:K):et q (et p r)=r:=by apply wM;intro a c;rw[<-hE,<-hE];have b:=Ar.mp (Ae.mp h a c);rw[b]
def hG (T:N)(p:Z kU):=(ed p T==T)&&tT p p.reverse&&tT p.reverse p
lemma jf {u T n}{f:Z N}(l:u1 u T n f.toFinset)(p:Z kU)(g:hG T p=H):u1 u T n (f.map (ed p.reverse)).toFinset:=by
 simp only[hG,X,Ar] at g;have d:Function.Surjective (et p):=fun r=>⟨et p.reverse r,iu g.2 r⟩;intro k m h;have b:=jw h (et p) d;have e:gE (et p) T=T:=(ew p T).symm.trans g.1.1;have jh (x:N):gE (et p) (ed p.reverse x)=x:=by apply Af;intro j i;change bit ⟨j,i⟩ _=bit ⟨j,i⟩ _;rw[eX,hE,iu g.1.2]
 have c:(f.map (ed p.reverse)).toFinset.image (gE (et p))=f.toFinset:=by
  ext a;simp only[A7,A4,Aj];constructor;. rintro⟨v,⟨w,q,rfl⟩,rfl⟩;simpa only[jh] using q
  . intro o;exact⟨_,⟨a,o,rfl⟩,jh a⟩
 rw[e,c] at b;exact l k m b
def fT (m:Nat)(v:Nat->fU):=uT m v
lemma y6 (m:Nat)(v:Nat->fU)(i:Fin 320):bit (fq v i) (fE m)=(fT m v).getLsbD i.val:=by exact y1 m v i
lemma w9 {m:Nat}{p q:Nat->fU}(a:fT m p=AO)(b:fT m q=0):g8 (fE m) (fq p) (fq q):=by intro i;simp only[y6,a,b,BL,i.isLt,B6];simp
def fw {al:Type}(bits:Nat):Z al->Z al
 | []=>[]
 | w::ws=>if bits&&&1==1 then w::fw (bits>>>1) ws else fw (bits>>>1) ws
lemma it {d:Type}(b:Nat)(ws:Z d):(fw b ws).Sublist ws:=by
 induction ws generalizing b with
 | nil=>exact List.Sublist.slnil
 | cons a ws c=>
   unfold fw;split;. exact List.Sublist.cons₂ _ (c _)
   . exact List.Sublist.cons _ (c _)
def vG (a d:Nat):Nat->Nat->LP×Nat
 | 0,x=>([],x)
 | n+1,x=>
   let(rest,tail):=vG a d n (x>>>(a+d))
   ((x%(1<<<a),(x>>>a)%(1<<<d))::rest,tail)
def uh (u:Y)(entries:LP):=∀ e∈entries,fL u (eu e.1) (e6 e.1) e.2
lemma uD:uh H []:=by simp[uh]
def iy (d:Nat)(a:N):Nat:=L a.toNat d
lemma sF (d a:N):iy d.toNat a=(fJ d a).toNat:=(DZ _ _).symm
def zN (a x y:Nat):Nat:=cond (M a 0) (L x y) (cond (M a 1) (Dc x y) (cond (M a 2) (D9 x (L x y)) (D9 y (L x y))))
lemma tK (e:Nat)(d a b:N):zN e (iy d.toNat a) (iy d.toNat b)=iy d.toNat (V e a b):=by
 have j (x y:N):L x.toNat y.toNat=(x&&&y).toNat:=(DZ x y).symm;have k (x y:N):D9 x.toNat y.toNat=(x^^^y).toNat:=(BitVec.toNat_xor x y).symm;have c (x y:N):Dc x.toNat y.toNat=(x|||y).toNat:=(BitVec.toNat_or x y).symm;simp only[sF];unfold zN;by_cases g:e=0;. subst g;change L _ _=_;rw[j];congr 1;apply fu;intro r;simp only[fJ,V,bit,AX,Aq];cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 by_cases f:e=1;. subst f;change Dc _ _=_;rw[c];congr 1;apply fu;intro r;simp only[fJ,V,bit,Nat.one_ne_zero,AX,AB,Aq,B1];cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have m:M e 0=J:=Bp.mpr (fun h=>g (Cl h));have l:M e 1=J:=Bp.mpr (fun h=>f (Cl h));by_cases i:e=2;. subst i;change D9 _ (L _ _)=_;rw[j,k];congr 1;apply fu;intro r;simp only[fJ,V,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,AX,AB,Aq,CE,AW,r.isLt,B6,AD];cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have n:M e 2=J:=Bp.mpr (fun h=>i (Cl h));rw[m,l,n];change D9 _ (L _ _)=_;rw[j,k];congr 1;apply fu;intro r;simp only[fJ,V,bit,g,f,i,AB,Aq,CE,AW,r.isLt,B6,AD];cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
def jT (v:Nat):Nat:=E (Dj v 2305843009213693951) fun n=>Dj (DV n (Dn n 971)) 2305843009213693951
lemma vm (c:Nat)(a b:N):zN c a.toNat b.toNat=(V c a b).toNat:=by
 have e (v:N):iy one.toNat v=v.toNat:=by rw[sF];congr 1;exact BitVec.and_allOnes
 have:=tK c one a b;rwa[e,e,e] at this
def iv (v t:Nat):Nat:=cond (M t (v&&&15)) (v>>>4) (cond (M t (v>>>4)) (v&&&15) t)
def eO (v:Nat):Y:=and (Db ((v&&&15)+1) (v>>>4)) (Db ((v>>>4)+1) 12)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma xK:∀ v:Fin 192,eO v.val=H->∀ t:B,iv v.val t.val<12/\jl (eo v.val) (u3.getD t.val P)=u3.getD (iv v.val t.val) P:=by decide +kernel
lemma vA {v t:Nat}(a:eO v=H)(b:t<12):iv v t<12/\jl (eo v) (u3.getD t P)=u3.getD (iv v t) P:=by
 have c:v<192:=by simp only[eO,X,Df,E5] at a;omega
 exact xK ⟨v,c⟩ a ⟨t,b⟩
def idxOf (a:W)(t:Nat):Nat:=a.foldl (fun t v=>iv v t) t
lemma wY {a:W}(b:a.all eO=H){t:Nat}(c:t<12):ed (a.map eo).reverse (u3.getD t P)=u3.getD (idxOf a t) P:=by rw[ed,foldr_reverse,foldl_map];induction a generalizing t with|nil=>rfl | cons v a d=>simp only[all_cons,X] at b;have⟨f,e⟩:=vA b.1 c;rw[Bn,e,d b.2 f];rfl
lemma wQ {b d:Type}(f:b->d)(a:Nat)(ws:Z b):(fw a ws).map f=fw a (ws.map f):=by
 induction ws generalizing a with
 | nil=>rfl
 | cons w ws c=>
   rw[As,fw,fw];split;. rw[As,c]
   . exact c _
def v3 (a:I N)(T v:N)(p n:K):=bit p T=H/\bit n T=J/\∀ w∈a,bit p w=H->bit n w=J->w=v
def hX (a b:N)(c:I N):=[a,b].filter fun t=>decide (t∈c)
def fC (a b z v:N):=if v=a\/v=b then z else v
def iU (a b z:N)(c:I N)(f:N->Nat)(v:N):=let kept:=hX a b c;if v∈kept then kept.idxOf v else kept.length+f (fC a b z v)
lemma ln {a b v c}:v∈hX a b c↔(v=a\/v=b)/\v∈c:=by simp[hX]
lemma xk {a b z v:N}{c:I N}(h:v∈insert a (insert b c)):fC a b z v∈insert z c:=by
 by_cases d:v=a\/v=b;. simp[fC,d]
 . simp_all [fC]
lemma vZ {d}(c:eT J d)(a b:N)(r:K):bit r (V d a b)=if d=0 then bit r a&&bit r b else bit r a||bit r b:=by
 rcases eY c with rfl|rfl|⟨h,_⟩|⟨h,_⟩;. simp[bit,V]
 . simp[bit,V]
 . contradiction
 . contradiction
lemma gh {a b d g T v p n}(j:eT J d)(c:v∉hX a b g)(h:v3 (insert a (insert b g)) T v p n):v3 (insert (V d a b) g) T (fC a b (V d a b) v) p n:=by
 refine⟨h.1,h.2.1,?_⟩;intro w f hp hn;rcases A9.mp f with rfl|f
 . rw[vZ j] at hp hn;have e:(bit p a=H/\bit n a=J)\/(bit p b=H/\bit n b=J):=by
    by_cases l:d=0<;>cases u:bit p a<;>cases v:bit n a<;>cases x:bit p b<;>
     cases y:bit n b<;>simp_all
   have i:v=a\/v=b:=by
    rcases e with⟨x,y⟩|⟨x,y⟩;. exact D5 (h.2.2 a (by simp) x y).symm
    . exact D6 (h.2.2 b (by simp) x y).symm
   simp[fC,i]
 . obtain rfl:=h.2.2 w (by simp[f]) hp hn;have k:¬(w=a\/w=b):=fun i=>c (ln.mpr ⟨i,f⟩);simp[fC,k]
lemma hK {a b z d f v w}(e:v∈hX a b d)(g:iU a b z d f v=iU a b z d f w):v=w:=by
 have c:=C0 e;by_cases h:w∈hX a b d;. simp only[iU,if_pos e,if_pos h] at g;exact(idxOf_inj e).mp g
 . simp only[iU,if_pos e,if_neg h] at g;omega
def wg (n v:Nat):fU:=BitVec.ofNat 320 (v+if v%2=1 then(1<<<320)-(1<<<n) else 0)
lemma vj {u c T a b}(h:fL u c T a)(f:b<=a):fL u c T b:=fun p d g e=>f.trans (h p d g e)
lemma uy {u m zl}(hints:Nat)(hp:eD (e6 m)=H)(ess:el (e6 m) (eu m) (eg m hints)=H)(enough:zl<=(List.map G (eg m hints)).toFinset.card-1):fL u (eu m) (e6 m) zl:=vj (vV (eJ _ hp) (eg m hints) ess) enough
lemma yh {u m q a g}(b c:Nat)(f:fL u (eu q) (e6 q) a)(e:gH (j8 b 0) (e6 m) (eu m) (eu q) (e6 q) (eg b c)=H)(h:eD (e6 m)=H)(i:eD (e6 q)=H)(d:g<=a+(List.map G (eg b c)).toFinset.card):fL u (eu m) (e6 m) g:=vj (w8 e (eJ _ h) (eJ _ i) f) d
abbrev w5 (u:Y)(m a:Nat):=fL u (eu m) (e6 m) a
def tW (xs:Array Nat)(i:Nat):=xs.getD (i%8) 0
def tP (xs:Array (PP))(i:Nat):=xs.getD (i%8) (0,0)
lemma uu {u m zl es}(h:w5 u m zl)(tail:uh u es):uh u ((m,zl)::es):=by
 intro e he;rcases Ab.mp he with rfl|h';. exact h
 . exact tail e h'
def sS (b s iw pw dw dispW tabW h:Nat):Q (PP):=E h fun h=>E (Dj (Dn (DH h b) (Dj (D3 dispW (DV dw (Dj h b))) (Dd 1 dw))) s) fun slot=>let w:=Dn (Dn iw pw) 1;E (Dj (D3 tabW (DV w slot)) (Dd 1 w)) fun val=>cond (or (M val 0) (not (M (D3 val (Dn iw pw)) (Dj (DH h (DV b s)) 2)))) none (some (De (Dj val (Dd 1 iw)) 1,Dj (D3 val iw) (Dd 1 pw)))
def vS (blocks:Nat->PP)(i:Nat):=let b:=blocks (DH i 16);E (D3 b.1 (DV 16 (Dj i 16))) fun o=>E (Dj o 65536) fun s=>Dj (D3 b.2 s) (Dd 1 (De (Dj (D3 o 16) 65536) s))
def uB (blocks:Nat->PP)(i:Nat):=let b:=blocks (DH i 16);E (D3 b.1 (DV 12 (Dj i 16))) fun o=>E (Dj o 4096) fun s=>Dj (D3 b.2 s) (Dd 1 (De (Dj (D3 o 12) 4096) s))
def f2 {b:Type}(l:W)(k:W->b):b:=List.rec (fun k=>k []) (fun a _ c k=>E a fun x=>c fun d=>k (x::d)) l k
lemma gf {b:Type}(l:W)(k:W->b):f2 l k=k l:=by induction l generalizing k with|nil=>rfl | cons a l c=>change E a (fun x=>f2 l (fun d=>k (x::d)))=_;rw[R,c]
lemma iT (q s:Nat):(fW q).testBit s=decide (s<1<<<q):=by simp[fW,Ag,one_mul]
lemma f9 {q x s:Nat}(a:s<1<<<q):(fW q^^^x).testBit s=!(x.testBit s):=by rw[BX,iT,B3 a,Ea]
lemma gX {a b:Nat}(h:(a&&&b)=0):a+b=(a|||b):=by
 induction a using Nat.binaryRec generalizing b with
 | zero=>simp
 | bit f a l=>
   induction b using Nat.binaryRec with
   | zero=>simp
   | bit g b _=>
     have i:=Az (fun n=>n.testBit 0) h;simp only[Ad,DN,Nat.testBit_bit_zero] at i;have c:(a&&&b)=0:=by apply AF;intro k;have j:=Az (fun n=>n.testBit (k+1)) h;simpa[Ad,Nat.testBit_bit_succ] using j
     have d:=l c;have e:(Nat.bit f a|||Nat.bit g b)=Nat.bit (f||g) (a|||b):=by apply AF;intro k;cases k with|zero=>simp | succ k=>simp[Nat.testBit_bit_succ]
     rw[e,<-d];cases f<;>cases g<;>simp only[DM,Cs,AD,BT,DC] at i ⊢
     . simp only[Nat.bit,D2];omega
     . simp only[Nat.bit,D2,D4];omega
     . simp only[Nat.bit,D2,D4];omega
     . contradiction
def fn (f:Nat->NN):Nat->Nat->Nat->NN
 | 0,base,x,acc=>if x&&&1==1 then E (f acc base) id else acc
 | d+1,base,x,acc=>
   if x==0 then acc else
    let half:=1<<<d
    E (x&&&((1<<<half)-1)) fun c=>
    E (x>>>half) fun b=>
    E (if c==0 then acc else fn f d base c acc) fun a=>
    if b==0 then a else fn f d (base+half) b a
def ia (f:Nat->Y):Nat->Nat->Nat->Y
 | 0,base,x=>if x&&&1==1 then f base else H
 | d+1,base,x=>
   if x==0 then H else
    let half:=1<<<d
    E (x&&&((1<<<half)-1)) fun b=>
    E (x>>>half) fun a=>
    (if b==0 then H else ia f d base b) &&
    (if a==0 then H else ia f d (base+half) a)
def iI (all m:Nat):Nat->W->NN
 | _,[],nonMax=>m&&&(all^^^nonMax)
 | i,xi::rest,nonMax=>E (nonMax|||((m&&&xi)>>>(1<<<i))) fun nm=>iI all m (i+1) rest nm
def jH (a:Nat)(b:W)(m:Nat):Nat:=iI a m 0 b 0
def iA (lo:Nat):Nat->W->W->NN
 | i,a::nx',b::nb',v=>
   E (v&&&(if(lo>>>i)&&&1==1 then a else b)) fun v'=>iA lo (i+1) nx' nb' v'
 | _,_,_,v=>v
def iP (b:Nat)(c a:W)(d:Nat):Nat:=iA d 0 c a b
def ej:W->NN
 | [],_=>0
 | a::_,0=>a
 | _::as,n+1=>ej as n
lemma eB (l:W)(i:Nat):ej l i=l.getD i 0:=by
 induction l generalizing i with
 | nil=>cases i<;>rfl
 | cons a l b=>cases i with|zero=>rfl| succ i=>exact b i
def j4 {a:Type}(b:Y)(f:Y->a):a:=Bool.rec (f J) (f H) b
lemma kh {a:Type}(b:Y)(f:Y->a):j4 b f=f b:=by cases b<;>rfl
def ip {c b:Type}(f:c->Nat)(l:Z c)(k:W->b):b:= List.rec (fun k=>k []) (fun a _ d k=>E (f a) fun x=>d fun e=>k (x::e)) l k
lemma kg {b c:Type}(f:b->Nat)(l:Z b)(k:W->c):ip f l k=k (l.map f):=by induction l generalizing k with|nil=>rfl| cons a l d=>change E (f a) (fun x=>ip f l fun e=>k (x::e))=_;rw[R,d];rfl
def lF (l:W)(i:Nat):Nat:=List.rec (fun _=>0) (fun a _ b n=>Nat.rec a (fun m _=>b m) n) l i
lemma lk (l:W)(i:Nat):lF l i=l.getD i 0:=by induction l generalizing i with|nil=>cases i<;>rfl| cons a l b=>cases i with|zero=>rfl| succ i=>exact b i
def kX {b:Type}(l:Z b)(i:Nat):Q b:=List.rec (fun _=>none) (fun a _ c n=>Nat.rec (some a) (fun m _=>c m) n) l i
lemma kB {b:Type}(l:Z b)(i:Nat):kX l i=l[i]?:=by induction l generalizing i with|nil=>cases i<;>rfl| cons a l c=>cases i with|zero=>rfl| succ i=>exact c i
def iK (all xi:Nat)(i mask:Nat):Nat->W->NN
 | _,[],acc=>acc
 | j,xj::restJ,acc=>
   E (if j>i&&((mask>>>j)&&&1==1) then acc&&&(all^^^(xi&&&xj)) else acc)
    fun a3=>iK all xi i mask (j+1) restJ a3
def ju (all:Nat)(xs:W):Nat->W->NN
 | _,[],acc=>acc
 | i,mask::rest,acc=>
   ju all xs (i+1) rest (iK all (ej xs i) i mask 0 xs acc)
def hM (q all indep:Nat)(xs notX notBadC:W):Nat->NN
 | 0,cur=>cur
 | t'+1,cur=>
   E (fn (fun acc lo=>acc|||(iP indep notX notBadC lo<<<lo)) q 0 cur 0) fun nxtAll=>
   E (jH all xs nxtAll) fun nxt=>
   hM q all indep xs notX notBadC t' nxt
def us (q maxRank:Nat)(neqs:W)(triples:Z (Nat×PP)):Y:=E (fW q) fun all=>f2 ((range q).map (ep q)) fun xs=>f2 (xs.map (fun xi=>all^^^xi)) fun notX=>E (ju all xs 0 neqs all) fun indep=>f2 ((range q).map (fun c=>let bad:=triples.foldl (fun acc tr=>if tr.2.2==c then acc|||(ej xs tr.1&&&ej xs tr.2.1) else acc) 0;all^^^(bad&&&ej notX c))) fun notBadC=>E (hM q all indep xs notX notBadC maxRank 1) fun finalCur=>E ((1<<<q)-1) fun allQ=>ia (fun lo=>((indep>>>(allQ^^^lo))&&&1)==0) q 0 finalCur
lemma eU (x:Nat):(x&&&1)=1↔x.testBit 0=H:=by rw[Nat.and_one_is_mod,Nat.testBit_zero];have:x%2=0\/x%2=1:=(by omega);rcases this with h|h<;>simp[h]
lemma wH {f:Nat->Y}{d o x k:Nat}(s:k<1<<<d)(a:x.testBit k=H)(b:ia f d o x=H):f (o+k)=H:=by
 induction d generalizing o x k with
 | zero=>
   have n:k=0:=by simp[Ag] at s;omega
   subst n;simp only[ia] at b;have p:(x&&&1)=1:=(eU x).mpr a;simpa[p] using b
 | succ d q=>
   have g:x≠0:=by intro h;simp[h] at a
   simp only[ia,Ar,g,AB,R,X] at b;have m:1<<<(d+1)=(1<<<d)+(1<<<d):=by simp only[Ag,one_mul,DL];omega
   by_cases i:k<1<<<d
   . have j:(x&&&((1<<<(1<<<d))-1)).testBit k=H:=by rw[Ad,a,AD,Ag,one_mul,AP];exact B3 i
     have c:x&&&((1<<<(1<<<d))-1)≠0:=by intro h;simp[h] at j
     have p:=b.1;rw[AR.mpr (fun h=>Qa h c)] at p;exact q i j p
   . have e:(x>>>(1<<<d)).testBit (k-(1<<<d))=H:=by rw[Av,Nat.add_sub_cancel' (by omega:1<<<d<=k)];exact a
     have c:x>>>(1<<<d)≠0:=by intro h;simp[h] at e
     have r:=b.2;rw[AR.mpr (fun h=>Qa h c)] at r;have l:=q (by omega:k-(1<<<d)<1<<<d) e r;simpa[AZ,Nat.add_sub_cancel' (by omega:1<<<d<=k)] using l
lemma wV {f:Nat->NN}(c:∀ a b m,a.testBit m=H->(f a b).testBit m=H)(d e x a m:Nat)(g:a.testBit m=H):(fn f d e x a).testBit m=H:=by
 induction d generalizing e x a with
 | zero=>
   simp only[fn];split;. rw[R];exact c a e m g
   . exact g
 | succ d h=>
   simp only[fn];split;. exact g
   . simp only[R];have i:(if(x&&&((1<<<(1<<<d))-1)==0)=H then a else fn f d e (x&&&((1<<<(1<<<d))-1)) a).testBit m=H:=by
      split;. exact g
      . exact h _ _ _ g
     split;. exact i
     . exact h _ _ _ i
lemma y8 {f:Nat->NN}(g:∀ a b m,a.testBit m=H->(f a b).testBit m=H){d r x a k m:Nat}(u:k<1<<<d)(e:x.testBit k=H)(c:∀ a',(f a' (r+k)).testBit m=H):(fn f d r x a).testBit m=H:=by
 induction d generalizing r x a k with
 | zero=>
   have q:k=0:=by simp[Ag] at u;omega
   subst q;simp only[fn];have s:(x&&&1)=1:=(eU x).mpr e;simp only[s,beq_self_eq_true,AX,R];simpa using c a
 | succ d t=>
   have l:x≠0:=by intro h;simp[h] at e
   simp only[fn,Ar,l,AB,R];have p:1<<<(d+1)=(1<<<d)+(1<<<d):=by simp only[Ag,one_mul,DL];omega
   by_cases n:k<1<<<d
   . have o:(x&&&((1<<<(1<<<d))-1)).testBit k=H:=by rw[Ad,e,AD,Ag,one_mul,AP];exact B3 n
     have i:x&&&((1<<<(1<<<d))-1)≠0:=by intro h;simp[h] at o
     have s:(fn f d r (x&&&((1<<<(1<<<d))-1)) a).testBit m=H:=t n o c;rw[AR.mpr (fun h=>Qa h i)];split;. exact s
     . exact wV g d _ _ _ m s
   . have j:(x>>>(1<<<d)).testBit (k-(1<<<d))=H:=by rw[Av,Nat.add_sub_cancel' (by omega:1<<<d<=k)];exact e
     have i:x>>>(1<<<d)≠0:=by intro h;simp[h] at j
     rw[AR.mpr (fun h=>Qa h i)];exact t (by omega:k-(1<<<d)<1<<<d) j (fun a'=>by
      simpa[AZ,Nat.add_sub_cancel' (by omega:1<<<d<=k)] using c a')
lemma xq {q m:Nat}(i:Nat)(d:W)(a s:Nat)(l:s < 1<<<q):(iI (fW q) m i d a).testBit s=H↔m.testBit s=H/\a.testBit s=J/\∀ k (hk:k < d.length),((m&&&d[k])>>>(1<<<(i+k))).testBit s=J:=by
 induction d generalizing i a with
 | nil=>simp only[iI,Ad,f9 l,X,D8,length_nil];exact⟨fun h=>⟨h.1,h.2,fun _ hk=>by omega⟩,fun h=>⟨h.1,h.2.1⟩⟩
 | cons o j n=>
   simp only[iI,R,n,Ay,BC,AY];constructor;. rintro⟨f,⟨c,g⟩,hrest⟩;refine⟨f,c,fun k hk=>?_⟩;cases k with|zero=>simpa using g | succ k=>have e:=hrest k (by omega);simpa[AZ,Aw 1 k] using e
   . rintro⟨f,c,b⟩;refine⟨f,⟨c,by simpa using b 0 (by omega)⟩,fun k hk=>?_⟩;have e:=b (k+1) (by omega);simpa[AZ,Aw 1 k] using e
lemma gi {s i:Nat}(c:s.testBit i=J):(s+(1<<<i))=(s|||(1<<<i))/\(s&&&(s+(1<<<i)))=s:=by
 have a:(s&&&(1<<<i))=0:=by
  apply AF;intro k;rw[Ad,DN,Ag,one_mul,Cx];by_cases h:i=k;. subst h;simp[c]
  . simp[h]
 have b:s+(1<<<i)=(s|||(1<<<i)):=gX a;refine⟨b,?_⟩;rw[b];apply AF;intro k;rw[Ad,Ay];cases s.testBit k<;>simp
lemma wB {q m s:Nat}(hq:q<=12)(hs:s<1<<<q)(hm:m.testBit s=H):∃ t < 1<<<q,(s&&&t)=s/\(jH (fW q) ((range q).map (ep q)) m).testBit t=H:=by
 have x:∀ d s,s<1<<<q->(1<<<q)-s<=d->m.testBit s=H->∃ t < 1<<<q,(s&&&t)=s/\(jH (fW q) ((range q).map (ep q)) m).testBit t=H:=by
  intro d;induction d with
  | zero=>intro s hs hle;omega
  | succ d ih=>
    intro s hs hle i;let xs:=(range q).map (ep q);by_cases b:(jH (fW q) xs m).testBit s=H;. exact⟨s,hs,Nat.and_self s,b⟩
    . unfold jH at b;rw[xq 0 xs 0 s hs] at b;push Not at b;obtain⟨k,hk,y⟩:=b i (by simp);have f:k<q:=(by simpa[xs] using hk);have p:xs[k]=ep q k:=(by simp[xs]);have a:((m&&&ep q k)>>>(1<<<k)).testBit s=H:=by rw[p] at y;cases h:((m&&&ep q k)>>>(1<<<k)).testBit s<;>simp_all
      rw[Av,Ad,X] at a;have o:s+(1<<<k)<1<<<q:=by by_contra n;have n':1<<<q<=s+(1<<<k):=(by omega);have e:=yg hq f;rw[Ag,one_mul] at e;have c:(ep q k).testBit (s+(1<<<k))=J:=AH (lt_of_lt_of_le e (Ba (by decide) n'));rw[Aw] at c;simp[c] at a
      have z:(ep q k).testBit ((1<<<k)+s)=((1<<<k)+s).testBit k:=eC hq f (by omega);rw[z] at a;have w:s.testBit k=J:=by
       by_contra h1;have v:s.testBit k=H:=by cases h:s.testBit k<;>simp_all
       have j:((1<<<k)+s) / 2 ^ k=s / 2 ^ k+1:=(by rw[Ag,one_mul,Aw,Nat.add_div_right _ (Cj k)]);have r:((1<<<k)+s).testBit k=!s.testBit k:=by simp only[Nat.testBit,E5,j];have:(s / 2 ^ k)%2=0\/(s / 2 ^ k)%2=1:=(by omega);rcases this with h|h<;>simp[h,Nat.add_mod]
       rw[r,v] at a;simp at a
      have g:=(gi w).2;have h2:0<1<<<k:=by rw[Ag,one_mul];exact Cj k
      have i':m.testBit (s+(1<<<k))=H:=by rw[Aw];exact a.1
      obtain⟨t,l,h0,u⟩:=ih (s+(1<<<k)) o (by omega) i';refine⟨t,l,?_,u⟩;calc s&&&t=(s&&&(s+(1<<<k)))&&&t:=by rw[g]
       _=s&&&((s+(1<<<k))&&&t):=Nat.and_assoc _ _ _
       _=s&&&(s+(1<<<k)):=by rw[h0]
       _=s:=g
 exact x ((1<<<q)-s) s hs (BA _) hm
lemma jP {j:Nat}(i:Nat)(l g:W)(v s:Nat)(c:l.length=g.length)(o:v.testBit s=H)(e:∀ k (hk:k<l.length),j.testBit (i+k)=H->l[k].testBit s=H)(f:∀ k (hk:k<g.length),j.testBit (i+k)=J->g[k].testBit s=H):(iA j i l g v).testBit s=H:=by
 induction l generalizing i g v with
 | nil=>cases g with|nil=>exact o| cons _ _=>simp at c
 | cons a l' u=>
   cases g with
   | nil=>simp at c
   | cons b g'=>
     simp only[iA,R];apply u (i+1) g' _ (by simpa using c)
     . rw[Ad,o,AD];by_cases q:j.testBit i=H
       . have r:((j>>>i)&&&1)=1:=(eU _).mpr (by simpa[Av] using q);have m:=e 0 (by simp) (by simpa using q);simpa[r] using m
       . have p:j.testBit i=J:=by cases h:j.testBit i<;>simp_all
         have m:((j>>>i)&&&1)≠1:=fun t=>by
          have:=(eU _).mp t;simp[p] at this
         simp only[Ar,m,AB];exact f 0 (by simp) (by simpa using p)
     . intro k hk d;have n:=e (k+1) (by simp;omega) (by simpa[AZ,Aw 1 k] using d);simpa using n
     . intro k hk d;have n:=f (k+1) (by simp;omega) (by simpa[AZ,Aw 1 k] using d);simpa using n
lemma xw {q:Nat}(r:Nat)(i c:Nat)(j:Nat)(b:W)(f s:Nat)(u:s<1<<<q)(a:f.testBit s=H)(n:r.testBit s=s.testBit i)(e:∀ k (hk:k<b.length),b[k].testBit s=s.testBit (j+k))(l:∀ k,k<b.length->j+k>i->c.testBit (j+k)=H->!(s.testBit i&&s.testBit (j+k))=H):(iK (fW q) r i c j b f).testBit s=H:=by
 induction b generalizing j f with
 | nil=>exact a
 | cons w t v=>
   simp only[iK,R];apply v (j+1) _
   . split
     next d=>
      simp only[X,A6,Ar] at d;rw[Ad,a,AD,f9 u,Ad,n];have m:=e 0 (by simp);simp only[DA,Dz] at m;rw[m];have g:c.testBit j=H:=by have:=(eU _).mp d.2;simpa[Av] using this
      have o:=l 0 (by simp) (by omega) (by simpa using g);simpa using o
     next=>exact a
   . intro k hk;have h:=e (k+1) (by simp;omega);simp only[Ds] at h;rw[h];congr 1;omega
   . intro k hk p g;have h:=l (k+1) (by simp;omega) (by omega) (by simpa[AZ,Aw 1 k] using g);simpa[AZ,Aw 1 k] using h
lemma wS {q:Nat}(u:q<=12)(o:W)(i:Nat)(d:W)(a s:Nat)(p:s<1<<<q)(b:a.testBit s=H)(c:o=(range q).map (ep q))(f:∀ k (hk:k<d.length) j,j<q->j>i+k->d[k].testBit j=H->!(s.testBit (i+k)&&s.testBit j)=H):(ju (fW q) o i d a).testBit s=H:=by
 induction d generalizing i a with
 | nil=>exact b
 | cons n v y=>
   simp only[ju];apply y (i+1) _
   . by_cases w:i<q
     . apply xw _ i n 0 o a s p b
       . rw[eB,c,A1,B4,Cv w];simp[eC u w p]
       . intro k hk;have hk':k<q:=(by simpa[c] using hk);simp[c,eC u hk' p]
       . intro k hk l e;have hk':k<q:=(by simpa[c] using hk);have h:=f 0 (by simp) k hk' (by omega) (by simpa using e);simpa using h
     . have g:∀ j xsj a',j+xsj.length<=q->a'.testBit s=H->(iK (fW q) (ej o i) i n j xsj a').testBit s=H:=by
        intro j xsj;induction xsj generalizing j with
        | nil=>intro a' _ h;exact h
        | cons z r t=>
          intro a' hlen h;simp only[iK,R];have m:¬(j>i):=by simp at hlen;omega
          apply t (j+1) _ (by simp at hlen ⊢;omega);simp[m,h]
       exact g 0 o a (by simp[c]) b
   . intro k hk j x l e;have h:=f (k+1) (by simp;omega) j x (by omega) (by simpa using e);simpa[AZ,Aw 1 k] using h
lemma y9 {q:Nat}(x:q<=12)(t:W)(g:t=(range q).map (ep q))(c s:Nat)(w:s<1<<<q)(d:Z (Nat×PP))(e:Nat)(f:e.testBit s=J)(i:∀ a b,(a,b,c)∈d->a<q->b<q->!(s.testBit a&&s.testBit b)=H):(d.foldl (fun e tr=>if tr.2.2==c then e|||(ej t tr.1&&&ej t tr.2.1) else e) e).testBit s=J:=by
 induction d generalizing e with
 | nil=>exact f
 | cons tr y z=>
   rcases tr with⟨a,b,c'⟩;simp only[Bn];apply z
   . split
     next m=>
      have k:c'=c:=Ar.mp m;subst k;rw[Ay,f,BT,Ad];by_cases u:a<q
      . by_cases v:b<q
        . have l:(ej t a).testBit s=s.testBit a:=by rw[eB,g,A1,B4,Cv u];simp[eC x u w]
          have n:(ej t b).testBit s=s.testBit b:=by rw[eB,g,A1,B4,Cv v];simp[eC x v w]
          rw[l,n];have h:=i a b (by simp) u v;cases r:s.testBit a<;>cases p:s.testBit b<;>simp_all
        . have j:ej t b=0:=by rw[eB,g,A1,BP (by simp;omega)];rfl
          simp[j]
      . have o:ej t a=0:=by rw[eB,g,A1,BP (by simp;omega)];rfl
        simp[o]
     next=>exact f
   . intro a' b' hm u v;exact i a' b' (AK _ hm) u v
def uY (q:Nat)(p:Nat->Y):Nat:=(range q).foldl (fun a i=>if p i then a|||(1<<<i) else a) 0
lemma wq (q:Nat)(p:Nat->Y):uY q p<1<<<q:=by
 have b:∀ n,((range n).foldl (fun a i=>if p i then a|||(1<<<i) else a) 0)<1<<<n:=by
  intro n;induction n with
  | zero=>simp[Ag]
  | succ n c=>
    rw[range_succ,Ca,Bn,foldl_nil];have d:1<<<n<1<<<(n+1):=(by simp[Ag,DL]);have e:1<<<(n+1)=2 ^ (n+1):=(by simp[Ag]);split
    . rw[e];apply C9
      . rw[Ag,one_mul] at c;exact lt_of_lt_of_le c (Ba (by decide) (by omega))
      . rw[Ag,one_mul];exact Cr (by decide) (by omega)
    . exact lt_trans c d
 exact b q
lemma xR (q:Nat)(p:Nat->Y)(k:Nat):(uY q p).testBit k=(decide (k<q)&&p k):=by
 have e:∀ n,((range n).foldl (fun b i=>if p i then b|||(1<<<i) else b) 0).testBit k = (decide (k<n)&&p k):=by
  intro n;induction n with
  | zero=>simp
  | succ n g=>
    rw[range_succ,Ca,Bn,foldl_nil];by_cases c:k=n
    . subst c;split
      next h=>
       rw[Ay,g,Ag,one_mul,Nat.testBit_two_pow_self,Ef];simp[h]
      next h=>
       rw[g];simp[h]
    . have d:(k < n+1)↔(k < n):=(by omega);have a:decide (k < n+1)=decide (k < n):=by by_cases f:k < n<;>simp[f,d]
      split
      next=>
       rw[Ay,g,Ag,one_mul,Cx,BW (Du c),DC,a]
      next=>
       rw[g,a]
 exact e q
lemma jO {q p:Nat}{y:W}{o:Z (Nat×PP)}(hq:q<=12)(hf:us q p y o=H)(f:NN)(z:∀ i < q,f i<=p)(ht:∀ i j,i<q->j<q->i<j->(y.getD i 0).testBit j=H->f i≠f j)(hg:∀ a b c,(a,b,c)∈o->a<q->b<q->c<q->f a=f b->f c<=f a):False:=by
 unfold us at hf;simp only[R,gf] at hf;set ym:=fW q;set xs:=(range q).map (ep q);set g:=xs.map (fun xi=>ym^^^xi);set e:=ju ym xs 0 y ym;set d:=(range q).map (fun c=>let xa:=o.foldl (fun u tr=>if tr.2.2==c then u|||(ej xs tr.1&&&ej xs tr.2.1) else u) 0
  ym^^^(xa&&&ej g c))
 have h0:∀ s < 1<<<q,(∀ i j,i<q->j<q->s.testBit i=H->s.testBit j=H->f i=f j)->e.testBit s=H:=by
  intro s hs hsame;apply wS hq xs 0 y ym s hs (by rw[iT];exact B3 hs) rfl;intro k hk j hj a7 z7;have hv:k<q:=(by omega);have x0:(y.getD k 0).testBit j=H:=by rw[A1,Ah hk];simpa using z7
  by_cases h1:s.testBit k=H
  . by_cases h2:s.testBit j=H
    . exact Qa (hsame k j hv hj h1 h2) (ht k j hv hj (by omega) x0)
    . simp[h1,show s.testBit j=J by cases h:s.testBit j<;>simp_all]
  . simp[show s.testBit k=J by cases h:s.testBit k<;>simp_all]
 have ho:∀ base cur,(∃ lo < 1<<<q,cur.testBit lo=H/\∀ i < q,f i<base->lo.testBit i=H)->∃ lo' < 1<<<q,(jH ym xs (fn (fun u lo=>u|||(iP e g d lo<<<lo)) q 0 cur 0)).testBit lo'=H/\∀ i < q,f i<base+1->lo'.testBit i=H:=by
  rintro base cur ⟨lo,x,h5,v⟩;let s:=uY q (fun i=>!lo.testBit i&&decide (f i=base));have hs:s<1<<<q:=wq q _;have r:∀ i,s.testBit i=(decide (i<q)&&(!lo.testBit i&&decide (f i=base))):=xR q _;have hh:(lo&&&s)=0:=by apply AF;intro k;rw[Ad,DN,r];cases lo.testBit k<;>simp
  have x4:(iP e g d lo).testBit s=H:=by
   unfold iP;apply jP 0 g d e s (by simp[g,d,xs])
   . apply h0 s hs;intro i j hi hj ys yr;rw[r,B3 hi] at ys;rw[r,B3 hj] at yr;simp only[AD,X,A6] at ys yr;exact ys.2.trans yr.2.symm
   . intro k hk h3;simp only[C1] at h3;have hk':k<q:=(by simpa[g,xs] using hk);simp only[g,xs,DO,getElem_range];rw[f9 hs,eC hq hk' hs,r];simp[hk',h3]
   . intro k hk h3;simp only[C1] at h3;have hk':k<q:=(by simpa[d] using hk);simp only[d,DO,getElem_range];rw[f9 hs,Ad];by_cases x9:s.testBit k=H
     . have hu:(ej g k).testBit s=J:=by rw[eB,A1];have:g[k]?=some (ym^^^ep q k):=(by simp[g,xs,hk']);rw[this,BS,f9 hs,eC hq hk' hs,x9];rfl
       simp[hu]
     . have xf:s.testBit k=J:=by cases h:s.testBit k<;>simp_all
       have hr:(o.foldl (fun u tr=>if tr.2.2==k then u|||(ej xs tr.1&&&ej xs tr.2.1) else u) 0).testBit s=J:=by
        apply y9 hq xs rfl k s hs o 0 (by simp);intro a b yz ha hb;by_cases hp:s.testBit a=H
        . by_cases hl:s.testBit b=H
          . rw[r,B3 ha] at hp;rw[r,B3 hb] at hl;simp only[AD,X,A6] at hp hl;have xg:=hg a b k yz ha hb hk' (hp.2.trans hl.2.symm);have xb:f k=base:=by by_contra hn;have:=v k hk' (by omega);simp[h3] at this
            have hx:s.testBit k=H:=by rw[r];simp[hk',h3,xb]
            simp[hx] at xf
          . simp[show s.testBit b=J by cases h:s.testBit b<;>simp_all]
        . simp[show s.testBit a=J by cases h:s.testBit a<;>simp_all]
       rw[hr];rfl
  have x7:lo+s=(lo|||s):=gX hh;have hd:(lo|||s)<1<<<q:=by rw[Ag,one_mul] at x hs ⊢;exact C9 x hs
  have hc:(fn (fun u l=>u|||(iP e g d l<<<l)) q 0 cur 0).testBit (lo|||s)=H:=by
   apply y8 (fun u _ m hm=>by rw[Ay,hm,Ee]) x h5
   intro u';rw[C1,Ay,Nat.testBit_shiftLeft];have xe:lo<=(lo|||s):=(by omega);have x1:(lo|||s)-lo=s:=(by omega);simp[xe,x1,x4]
  obtain⟨lo',x',x2,x5⟩:=wB hq hd hc;refine⟨lo',x',x5,fun i hi hy=>?_⟩;have xc:(lo|||s).testBit i=H:=by
   rw[Ay,r];by_cases xd:lo.testBit i=H;. simp[xd]
   . have x3:lo.testBit i=J:=by cases h:lo.testBit i<;>simp_all
     have hw:f i=base:=by by_contra hn;have:=v i hi (by omega);simp[x3] at this
     simp[hi,x3,hw]
  have h1:=Az (fun n=>n.testBit i) x2;rw[Ad,xc,AD] at h1;exact h1
 have hz:∀ t base cur,(∃ lo < 1<<<q,cur.testBit lo=H/\∀ i < q,f i<base->lo.testBit i=H)->∃ lo' < 1<<<q,(hM q ym e xs g d t cur).testBit lo'=H/\∀ i < q,f i<base+t->lo'.testBit i=H:=by intro t;induction t with|zero=>intro base cur h;simpa[hM] using h | succ t ih=>intro base cur h;simp only[hM,R];have h1:=ho base cur h;have h2:=ih (base+1) _ h1;simpa[AZ,Aw 1 t] using h2
 obtain⟨lo,x,h5,v⟩:=hz p 0 1 ⟨0,by rw[Ag,one_mul];exact Cj q,by simp,fun i _ h=>by omega⟩
 simp only[C1] at v;have he:=wH x h5 hf;simp only[C1,Ar] at he;let t:=((1<<<q)-1)^^^lo;have h4:t<1<<<q:=by simp only[t,Ag,one_mul] at x ⊢;exact Nat.xor_lt_two_pow (Nat.sub_lt (Cj q) Nat.one_pos) x
 have w:∀ i < q,t.testBit i=!lo.testBit i:=by intro i hi;simp[t,Ag,one_mul,B3 hi]
 have x6:e.testBit t=H:=h0 t h4 fun i j hi hj z6 z5=>by
  have hp:∀ k < q,t.testBit k=H->f k=p:=fun k hk yy=>by rw[w k hk,D8] at yy;have:=z k hk;by_contra hn;have:=v k hk (by omega);simp[yy] at this
  exact(hp i hi z6).trans (hp j hj z5).symm
 have h1:((e>>>t)&&&1)=1:=(eU _).mpr (by simpa[Av] using x6);change ((e>>>t)&&&1)=0 at he;omega
abbrev Q9:=Nat×Nat×W×Z (Nat×PP)
def uj (c:Q9):Prop:=let(q,mr,neqs,triples):=c;∀ f:NN,(∀ i < q,f i<=mr)->(∀ i j,i<q->j<q->i<j->(neqs.getD i 0).testBit j=H->f i≠f j)->(∀ a b c',(a,b,c')∈triples->a<q->b<q->c' < q->f a=f b->f c'<=f a)->False
lemma xh {c:Q9}(a:c.1<=12)(h:us c.1 c.2.1 c.2.2.1 c.2.2.2=H):uj c:=by intro f hb hn ht;exact jO a h f hb hn ht
lemma cK:uj (2,0,[2,1],[]):=by intro f hb hn _;have b:f 0=0:=Nat.le_zero.mp (hb 0 (by decide));have a:f 1=0:=Nat.le_zero.mp (hb 1 (by decide));exact hn 0 1 (by decide) (by decide) (by decide) (by decide) (b.trans a.symm)
def wh (i:Nat):Nat->Nat->W
 | 0,_=>[]
 | r+1,v=>((v%(1<<<r))<<<(i+1))::wh (i+1) r (v>>>r)
def jj (q:Nat):Nat->Nat->Z (Nat×PP)
 | 0,_=>[]
 | r+1,v=>
   let a:=v%q;let d:=v / q
   let b:=d%q;let c:=d / q
   (a,b,c%q)::jj q r (c / q)
def uA (v:Nat):Q9:=let q:=v%16;let mr:=(v>>>4)%8;let nt:=(v>>>7)%128;let neqs:=wh 0 q (v>>>14);let trips:=jj q nt (v>>>(14+q*(q-1) / 2));(q,mr,neqs,trips)
def fc (p n:K):Prop:=(p.val&&&n.val)=n.val
def ec (w:N):Prop:=∀ p n:K,fc p n->bit n w=H->bit p w=H
lemma v4:ec P:=fun _ _ _ h=>by simp[f5] at h
lemma v8:ec one:=fun _ _ _ _=>fM _
lemma tL {d:Y}{a b:N}(c:ec a)(e:ec b):ec (gR d a b):=by intro p n hpn hn;cases d with|false=>simp only[gG,Ak,AB,X] at hn ⊢;exact⟨c p n hpn hn.1,e p n hpn hn.2⟩ | true=>simp only[gG,AX,Ai] at hn ⊢;exact hn.imp (c p n hpn) (e p n hpn)
lemma vr (j:B):ec (u3.getD j.val P):=by intro p n hpn hn;rw[fv] at hn ⊢;have h:=Az (fun x=>x.testBit j.val) hpn;rw[Ad,hn,Cb] at h;exact h
lemma y3:∀ w∈u3,ec w:=by intro w hw;rw[<-iZ] at hw;obtain⟨j,rfl⟩:=mem_ofFn.mp hw;exact vr j
lemma gq {a:N}(e:ec a){p n:K}(b:fc p n)(c:bit p (neg a)=H)(d:bit n (neg a)=J):False:=by rw[ft,D8] at c;rw[ft,Bool.not_eq_false'] at d;have:=e p n b d;rw[c] at this;cases this
def L1 (target:N):Nat->I N->Prop
 | 0,vs=>(vs={target}/\U target)\/(∃ (zu:I N) (a:N),vs=insert a zu/\U a/\ec a/\neg a∉insert a zu/\Lv J target 0 (insert (neg a) zu))
 | k+1,vs=>
   (∃ (zu:I N) (a b:N) (d:Nat),d<2/\vs=insert a (insert b zu)/\U a/\U b/\a≠b/\V d a b∉insert a (insert b zu)/\L1 target k (insert (V d a b) zu))\/
   (∃ (zu:I N) (a:N),vs=insert a zu/\U a/\ec a/\neg a∉insert a zu/\Lv J target (k+1) (insert (neg a) zu))
def u2 (T:N)(cap:Nat)(vs:I N):Prop:=∀ k,k<=cap->¬L1 T k vs
lemma L1.stop {a:N}(b:U a):L1 a 0 {a}:=D5 ⟨rfl,b⟩
lemma L1.binary {c:N}{k:Nat}{g:I N}{a b:N}{d:Nat}(i:d<2)(j:U a)(l:U b)(e:a≠b)(h:V d a b∉insert a (insert b g))(f:L1 c k (insert (V d a b) g)):L1 c (k+1) (insert a (insert b g)):=D5 ⟨g,a,b,d,i,rfl,j,l,e,h,f⟩
lemma L1.unary {b:N}{k:Nat}{d:I N}{a:N}(f:U a)(g:ec a)(e:neg a∉insert a d)(c:Lv J b k (insert (neg a) d)):L1 b k (insert a d):=by cases k with|zero=>exact D6 ⟨d,a,rfl,f,g,e,c⟩ | succ k=>exact D6 ⟨d,a,rfl,f,g,e,c⟩
lemma L1.ofFalse {c:N}{k:Nat}{i:I N}(h:Lv J c k i):L1 c k i:=by
 induction k generalizing i with
 | zero=>exact D5 h
 | succ k o=>
   obtain⟨j,a,b,d,m,rfl,n,p,e,l,g⟩:=h;have f:d<2:=by rcases m with h|⟨h,_⟩<;>simp_all
   exact D5 ⟨j,a,b,d,f,rfl,n,p,e,l,o g⟩
lemma we {e k i}(h:L1 e k i):∀ a∈i,U a:=by
 induction k generalizing i with
 | zero=>
   rcases h with⟨rfl,l⟩|⟨j,a,rfl,g,_,_,c⟩;. simpa using l
   . simp only[BI];exact⟨g,fun v f=>gA c v (A2 f)⟩
 | succ k m=>
   rcases h with⟨j,a,b,d,_,rfl,g,n,_,_,c⟩|⟨j,a,rfl,g,_,_,c⟩;. simp only[BI];exact⟨g,n,fun v f=>m c v (A2 f)⟩
   . simp only[BI];exact⟨g,fun v f=>gA c v (A2 f)⟩
lemma tV {e k m}(h:L1 e k m):m.card<=k+1:=by
 induction k generalizing m with
 | zero=>
   rcases h with⟨rfl,_⟩|⟨f,a,rfl,_,_,j,c⟩;. simp
   . have g:neg a∉f:=fun l=>j (A2 l);have i:=gz c;rw[Al g] at i;have n:=Bl (a:=a) (s:=f);omega
 | succ k o=>
   rcases h with⟨f,a,b,d,_,rfl,_,_,_,j,c⟩|⟨f,a,rfl,_,_,j,c⟩;. have g:V d a b∉f:=fun l=>j (A2 (A2 l));have i:=o c;rw[Al g] at i;have n:=Bl (a:=a) (s:=insert b f);have p:=Bl (a:=b) (s:=f);omega
   . have g:neg a∉f:=fun l=>j (A2 l);have i:=gz c;rw[Al g] at i;have n:=Bl (a:=a) (s:=f);omega
lemma ir {T k vs}(h:L1 T k vs){p n:K}(e:fc p n)(l:bit p T=H)(c:bit n T=J):∃ a∈vs,bit p a=H/\bit n a=J:=by
 induction k generalizing vs with
 | zero=>
   rcases h with⟨rfl,_⟩|⟨r,a,rfl,_,m,_,g⟩;. exact⟨T,by simp,l,c⟩
   . have⟨v,q,i,j⟩:=f0 g rfl l c;rcases A9.mp q with rfl|o
     . exact False.elim (gq m e i j)
     . exact⟨v,A2 o,i,j⟩
 | succ k s=>
   rcases h with⟨r,a,b,d,t,rfl,_,_,_,_,g⟩|⟨r,a,rfl,_,m,_,g⟩
   . have⟨v,q,i,j⟩:=s g;rcases A9.mp q with rfl|o
     . have f:d=0\/d=1:=(by omega);rcases f with rfl|rfl<;>(rw[gT] at i j;cases x:bit p a<;>cases y:bit n a<;>cases z:bit p b<;>cases w:bit n b<;>simp_all)
     . exact⟨v,A2 (A2 o),i,j⟩
   . have⟨v,q,i,j⟩:=f0 g rfl l c;rcases A9.mp q with rfl|o
     . exact False.elim (gq m e i j)
     . exact⟨v,A2 o,i,j⟩
lemma jr {T k vs}(h:L1 T k vs){r s:K}(c:bit r T≠bit s T):∃ a∈vs,bit r a≠bit s a:=by
 induction k generalizing vs with
 | zero=>
   rcases h with⟨rfl,_⟩|⟨n,a,rfl,_,_,_,g⟩;. exact⟨T,by simp,c⟩
   . have⟨v,l,i⟩:=fD g c;rcases A9.mp l with rfl|j
     . exact⟨a,by simp,fun m=>i (by rw[ft,ft,m])⟩
     . exact⟨v,A2 j,i⟩
 | succ k o=>
   rcases h with⟨n,a,b,d,_,rfl,_,_,_,_,g⟩|⟨n,a,rfl,_,_,_,g⟩
   . have⟨v,l,i⟩:=o g;rcases A9.mp l with rfl|j
     . by_cases e:bit r a=bit s a
       . exact⟨b,by simp,fun f=>i (by rw[gT,gT,e,f])⟩
       . exact⟨a,by simp,e⟩
     . exact⟨v,A2 (A2 j),i⟩
   . have⟨v,l,i⟩:=fD g c;rcases A9.mp l with rfl|j
     . exact⟨a,by simp,fun m=>i (by rw[ft,ft,m])⟩
     . exact⟨v,A2 j,i⟩
lemma hH {T k vs}(h:L1 T k vs)(e:Z N)(a:N)(f:∀ v∈vs,v∈e)(r s:K)(c:bit r T≠bit s T)(b:∀ v∈e,v≠a->bit r v=bit s v):a∈vs:=by
 have⟨v,g,i⟩:=jr h c;by_cases d:v=a;. simpa[d] using g
 . exact False.elim (i (b v (f v g) d))
def ey (a:I N)(T v:N)(p n:K):Prop:=fc p n/\v3 a T v p n
def fQ (d:I N)(T:N)(f:N->Nat):Prop:=(∀ {a b p n na nb pa pb},a≠b->ey d T a p na->ey d T b p nb->ey d T a pa n->ey d T b pb n->f a≠f b)/\(∀ {a b c p n na pb},ey d T a p na->ey d T b pb n->ey d T c p n->f a=f b->f c<=f a)
lemma gL {k b T v p n}(a:Lv J T k b)(h:ey b T v p n):v∈b/\bit p v=H/\bit n v=J:=by have⟨w,d,c,e⟩:=f0 a rfl h.2.1 h.2.2.1;exact h.2.2.2 w d c e▸⟨d,c,e⟩
lemma gr {k b T v p n}(a:L1 T k b)(h:ey b T v p n):v∈b/\bit p v=H/\bit n v=J:=by have⟨w,d,c,e⟩:=ir a h.1 h.2.1 h.2.2.1;exact h.2.2.2 w d c e▸⟨d,c,e⟩
lemma eK {g T a v p n k}(b:ec a)(i:Lv J T k (insert (neg a) g))(h:ey (insert a g) T v p n):v∈g/\ey (insert (neg a) g) T v p n:=by
 have⟨w,r,l,m⟩:=f0 i rfl h.2.1 h.2.2.1;have c:w∈g:=by
  rcases A9.mp r with rfl|o;. exact False.elim (gq b h.1 l m)
  . exact o
 have f:w=v:=h.2.2.2 w (A2 c) l m;subst f;refine⟨c,h.1,h.2.1,h.2.2.1,fun x q d e=>?_⟩;rcases A9.mp q with rfl|j;. exact False.elim (gq b h.1 d e)
 . exact h.2.2.2 x (A2 j) d e
lemma iC {j T a b d k}(hd:d<2)(h0:a≠b)(g:V d a b∉insert a (insert b j))(c:∀ {v p n},ey (insert a (insert b j)) T v p n->v∈insert a (insert b j)/\bit p v=H/\bit n v=J)(i:∀ {v p n},ey (insert (V d a b) j) T v p n->v∈insert (V d a b) j/\bit p v=H/\bit n v=J)(s:∃ (count:Nat) (f:N->Nat),count+(insert (V d a b) j).card<=k+2/\(∀ v∈insert (V d a b) j,f v<count)/\fQ (insert (V d a b) j) T f):∃ (count:Nat) (f:N->Nat),count+(insert a (insert b j)).card<=(k+1)+2/\(∀ v∈insert a (insert b j),f v<count)/\fQ (insert a (insert b j)) T f:=by
 let z:=V d a b;let kept:=hX a b j;have hd':eT J d:=D5 hd;have⟨count,f,g0,h1,h2⟩:=s;rw[Al fun m=>g (A2 (A2 m))] at g0;have hc:kept.length+(insert a (insert b j)).card=j.card+2:=by by_cases x:a∈j<;>by_cases y:b∈j<;>simp[kept,hX,x,y,h0,Al]<;>omega
 have hg:∀ {v w},v∉kept->w∉kept->iU a b z j f v=iU a b z j f w->f (fC a b z v)=f (fC a b z w):=fun {v w} r uw eq=>by change (if v∈kept then _ else kept.length+_)=(if w∈kept then _ else kept.length+_) at eq;rw[if_neg r,if_neg uw] at eq;omega
 refine⟨kept.length+count,iU a b z j f,by omega,?_,?_,?_⟩;. intro v hv;change (if v∈kept then kept.idxOf v else _)<_;by_cases u:v∈kept;rw[if_pos u];have:=C0 u;omega;rw[if_neg u];exact Nat.add_lt_add_left (h1 _ (xk (z:=z) hv)) _
 . intro v w p n na nb pa pb vw za zb zc kd eq;have r:v∉kept:=fun u=>vw (hK u eq);have uw:w∉kept:=fun u=>vw (hK u eq.symm).symm;have q:=hg r uw eq;by_cases ne:fC a b z v≠fC a b z w
   . exact h2.1 ne ⟨za.1,gh hd' r za.2⟩ ⟨zb.1,gh hd' uw zb.2⟩ ⟨zc.1,gh hd' r zc.2⟩ ⟨kd.1,gh hd' uw kd.2⟩ q
   . have vz:v≠z:=fun e=>g (show z∈_ from e▸(c za).1);have wz:w≠z:=fun e=>g (show z∈_ from e▸(c zb).1);have h3:(v=a/\w=b)\/(v=b/\w=a):=by by_cases va:v=a\/v=b<;>by_cases wa:w=a\/w=b<;>simp_all[fC]<;>grind
     have ha:fC a b z v=z:=by rcases h3 with⟨rfl,_⟩|⟨rfl,_⟩<;>simp[fC]
     have l:w∈insert a (insert b j):=by rcases h3 with⟨_,rfl⟩|⟨_,rfl⟩<;>simp
     have Zp:=(i ⟨zc.1,gh hd' r zc.2⟩).2.1;have Zn:=(i ⟨za.1,gh hd' r za.2⟩).2.2;rw[ha,vZ hd'] at Zp Zn;by_cases op:d=0;. simp[op] at Zp;exact vw (zc.2.2.2 w l (h3.elim (fun⟨_,h⟩=>h▸Zp.2) (fun⟨_,h⟩=>h▸Zp.1)) (c kd).2.2).symm
     . simp[op] at Zn;exact vw (za.2.2.2 w l (c zb).2.1 (h3.elim (fun⟨_,h⟩=>h▸Zn.2) (fun⟨_,h⟩=>h▸Zn.1))).symm
 . intro v w t p n na pb za zb zc eq;have o (e:v=w):t=v:=by subst w;exact(zc.2.2.2 v (c za).1 (c za).2.1 (c zb).2.2).symm
   by_cases r:v∈kept;rw[o (hK r eq)];by_cases uw:w∈kept;rw[o (hK uw eq.symm).symm];have q:=hg r uw eq;change (if t∈kept then kept.idxOf t else kept.length+_)<=(if v∈kept then _ else kept.length+_);rw[if_neg r];by_cases ut:t∈kept;rw[if_pos ut];have:=C0 ut;omega;rw[if_neg ut];exact Nat.add_le_add_left (h2.2 ⟨za.1,gh hd' r za.2⟩ ⟨zb.1,gh hd' uw zb.2⟩ ⟨zc.1,gh hd' ut zc.2⟩ q) _
lemma iN {k q T}(h:Lv J T k q):∃ (m:Nat) (f:N->Nat),m+q.card<=k+2/\(∀ v∈q,f v < m)/\fQ q T f:=by
 induction k generalizing q with
 | zero=>obtain⟨rfl,c⟩:=h;refine⟨1,fun _=>0,by simp,by simp,?_,by simp⟩;intro a b p n na nb pa pb x w y _ _;have e:=(gL (Lv.stop (u:=J) c) w).1;have j:=(gL (Lv.stop (u:=J) c) y).1;simp only[A5] at e j;exact(x (e.trans j.symm)).elim
 | succ k t=>
   obtain⟨zu,a,b,d,r,rfl,s,z,i,g,o⟩:=h;have l:d<2:=by rcases r with h|⟨h,_⟩<;>simp_all
   exact iC l i g (gL (Lv.binary r s z i g o)) (gL o) (t o)
lemma h6 {k m T a}(b:ec a)(hf:neg a∉insert a m)(l:Lv J T k (insert (neg a) m)):∃ (count:Nat) (f:N->Nat),count+(insert a m).card+(if a∈m then 1 else 0)<=k+2/\(∀ v∈insert a m,f v<count)/\fQ (insert a m) T f:=by
 have⟨count,f,g0,d,g⟩:=iN l;have i:neg a∉m:=fun h=>hf (A2 h);rw[Al i] at g0;have j:(insert a m).card+(if a∈m then 1 else 0)=m.card+1:=by
  by_cases x:a∈m;. simp[x,Cd x]
  . simp[x,Al x]
 have e:0<count:=by have:=d (neg a) (AL _ _);omega
 refine⟨count,fun v=>if v∈m then f v else 0,by omega,?_,?_,?_⟩
 . intro v _;by_cases y:v∈m
   . simp[y,d v (A2 y)]
   . simp[y,e]
 . intro v w p n na nb pa pb ne q s o z u;have⟨t,q'⟩:=eK b l q;have⟨r,s'⟩:=eK b l s;have⟨_,o'⟩:=eK b l o;have⟨_,z'⟩:=eK b l z;simp only[t,r,AX] at u;exact g.1 ne q' s' o' z' u
 . intro v w c p n na pb q s o u;have⟨t,q'⟩:=eK b l q;have⟨r,s'⟩:=eK b l s;have⟨h0,o'⟩:=eK b l o;simp only[t,r,h0,AX] at u ⊢;exact g.2 q' s' o' u
lemma ya {k q T}(h:L1 T k q):∃ (count:Nat) (f:N->Nat),count+q.card<=k+2/\(∀ v∈q,f v<count)/\fQ q T f:=by
 induction k generalizing q with
 | zero=>
   rcases h with⟨rfl,l⟩|⟨t,a,rfl,_,o,s,i⟩
   . refine⟨1,fun _=>0,by simp,by simp,?_,by simp⟩
     intro a b p n na nb pa pb ne za zb _ _;have e:=(gr (L1.stop l) za).1;have j:=(gr (L1.stop l) zb).1;simp only[A5] at e j;exact(ne (e.trans j.symm)).elim
   . have⟨count,f,g0,c,g⟩:=h6 o s i;exact⟨count,f,by omega,c,g⟩
 | succ k x=>
   rcases h with⟨t,a,b,d,u,rfl,w,y,r,m,i⟩|⟨t,a,rfl,_,o,s,i⟩;. exact iC u r m (gr (L1.binary u w y r m i)) (gr i) (x i)
   . have⟨count,f,g0,c,g⟩:=h6 o s i;exact⟨count,f,by omega,c,g⟩
def sX:Nat->NN|0,x=>x|n+1,x=>sX n (x*x)
lemma wp (n x:Nat):sX n x=x ^ (2 ^ n):=by induction n generalizing x with|zero=>simp[sX] | succ n a=>rw[sX,a,<-Nat.pow_two,<-Nat.pow_mul,Nat.pow_succ']
def z4:Nat:=sX 12 2-1
lemma tE:z4=2 ^ 4096-1:=by simpa[z4] using Az (· - 1) (wp 12 2)
def en (T:N)(i:Nat):Nat:=((T.toNat>>>(1<<<i))&&&(z4^^^T.toNat))&&&(z4^^^(u3.getD i P).toNat)
def fO (T:N):LP:=(range 12).filterMap fun i=>let fm:=en T i;if fm==0 then none else some (i,fm)
lemma wZ {k:Nat}(a:k<4096):z4.testBit k=H:=by simp[tE,B3 a]
lemma fg {x k:Nat}(a:k<4096):(z4^^^x).testBit k=!(x.testBit k):=by rw[BX,wZ a,Ea]
def fA (b a w:Nat):Nat:=((w>>>a)&&&(z4^^^w))&&&b
def ev (fm sh:Nat):W->Nat->Nat->PP
 | [],c1,c2=>(c1,c2)
 | w::ws,c1,c2=>
   E (fA fm sh w) fun s=>
   E (c1|||s) fun c1'=>
   E (c2|||(c1&&&s)) fun c2'=>
   ev fm sh ws c1' c2'
lemma iF (d c:Nat)(ws:W)(a b r:Nat):(ev d c ws a b).1.testBit r=H↔a.testBit r=H\/∃ w∈ws,(fA d c w).testBit r=H:=by induction ws generalizing a b with|nil=>simp[ev] | cons w ws e=>simp only[ev,R,e,Ay,Ai,Ab,exists_eq_or_imp];tauto
lemma jZ (d c:Nat)(ws:W)(a b r:Nat)(h:b.testBit r=H):(ev d c ws a b).2.testBit r=H:=by induction ws generalizing a b with|nil=>exact h | cons w ws e=>simp only[ev,R];exact e _ _ (by rw[Ay,h,Ee])
lemma x8 (n m:Nat)(q:W)(a b r:Nat)(i:q.Nodup)(h2:(ev n m q a b).2.testBit r=J):(a.testBit r=J\/∀ x∈q,(fA n m x).testBit r=J)/\(∀ x∈q,∀ y∈q,(fA n m x).testBit r=H->(fA n m y).testBit r=H->x=y):=by
 induction q generalizing a b with
 | nil=>exact⟨D6 (by simp),by simp⟩
 | cons u l w=>
   have⟨j,f⟩:=B7.mp i;simp only[ev,R] at h2;have c:=w (a|||fA n m u) (b|||(a&&&fA n m u)) f h2;have g:(b|||(a&&&fA n m u)).testBit r=J:=by
    by_contra k;have z:(b|||(a&&&fA n m u)).testBit r=H:=by cases h:(b|||(a&&&fA n m u)).testBit r<;>simp_all
    have:=jZ n m l (a|||fA n m u) (b|||(a&&&fA n m u)) r z;rw[h2] at this;cases this
   simp only[Ay,Ad,BC,Bool.and_eq_false_iff] at g;constructor
   . rcases c.1 with o'|h2'
     . simp only[Ay,BC] at o';exact D5 o'.1
     . by_cases v:a.testBit r=J
       . exact D5 v
       . right;intro x t;rcases Ab.mp t with rfl|p
         . exact g.2.resolve_left v
         . exact h2' x p
   . intro x t y hy d e;rcases Ab.mp t with rfl|p<;>rcases Ab.mp hy with rfl|s
     . rfl
     . rcases c.1 with o'|h2'
       . simp only[Ay,BC] at o';rw[d] at o';exact Qa o'.2 (by decide)
       . rw[h2' y s] at e;exact Qa e (by decide)
     . rcases c.1 with o'|h2'
       . simp only[Ay,BC] at o';rw[e] at o';exact Qa o'.2 (by decide)
       . rw[h2' x p] at d;exact Qa d (by decide)
     . exact c.2 x p y s d e
lemma ww (i:B)(n:K)(c:n.val.testBit i.val=J):n.val+(1<<<i.val)<4096/\((n.val+(1<<<i.val))&&&n.val)=n.val:=by
 have⟨b,a⟩:=gi c;constructor
 . rw[b];have d:1<<<i.val<2 ^ 12:=by rw[Ag,one_mul];exact Cr (by decide) i.isLt
   exact C9 n.isLt d
 . rw[Nat.and_comm];exact a
lemma yl {T:N}{i r:Nat}(h:(en T i).testBit r=H):r<4096:=by
 by_contra b;have a:T.toNat<2 ^ 4096:=T.isLt;simp only[en,Ad,X] at h;have d:z4.testBit r=J:=by simp[tE,BW (by omega:¬ r<4096)]
 have c:(z4^^^T.toNat).testBit r=J:=by rw[BX,d,AH (lt_of_lt_of_le a (Ba (by decide) (by omega:4096<=r)))];rfl
 rw[c] at h;simp at h
lemma eZ (r:K)(a:N):bit r a=a.toNat.testBit r.val:=by simp[bit,BitVec.getLsbD]
lemma jq {T:N}{i:Nat}(e:i<12){r:Nat}(h:(en T i).testBit r=H):∃ (b:r<4096) (p:K),p.val=r+(1<<<i)/\fc p ⟨r,b⟩/\bit p T=H/\bit ⟨r,b⟩ T=J:=by
 have a:r<4096:=yl h;simp only[en,Ad,Av,fg a,X,D8] at h;have c:r.testBit i=J:=by have f:=fv ⟨i,e⟩ ⟨r,a⟩;rw[eZ] at f;rw[f] at h;exact h.2
 have⟨b,d⟩:=ww ⟨i,e⟩ ⟨r,a⟩ c;refine⟨a,⟨r+(1<<<i),b⟩,rfl,d,?_,?_⟩;. rw[eZ];simpa[Aw] using h.1.1
 . rw[eZ];exact h.1.2
lemma j5 {T:N}{o:Z N}(g:o.Nodup){i:Nat}(u:i<12){v:N}(x:v∈o){r:Nat}(t:(fA (en T i) (1<<<i) v.toNat&&&((ev (en T i) (1<<<i) (o.map A8) 0 0).1&&&(z4^^^(ev (en T i) (1<<<i) (o.map A8) 0 0).2))).testBit r=H):∃ (j:r<4096) (p:K),p.val=r+(1<<<i)/\ey o.toFinset T v p ⟨r,j⟩:=by
 simp only[Ad,X] at t;obtain⟨a,_,b⟩:=t;have a':=a;simp only[fA,Ad,X] at a';obtain⟨c,p,d,e,k,n⟩:=jq u a'.2;rw[fg c,D8] at b;refine⟨c,p,d,e,k,n,?_⟩;intro w y q s;have l:(fA (en T i) (1<<<i) w.toNat).testBit r=H:=by
  simp only[fA,Ad,Av,fg c,X,D8];refine⟨⟨?_,?_⟩,a'.2⟩;. rw[eZ] at q;simpa[d,Aw] using q
  . rw[eZ] at s;exact s
 have f:(o.map A8).Nodup:=g.map (fun _ _ h=>Do.mp h);have m:=(x8 (en T i) (1<<<i) (o.map A8) 0 0 r f b).2
  v.toNat (Qm x) w.toNat (Qm (A4.mp y)) a l
 exact(Do.mp m).symm
def jG (a:LP)(b:W):Y:=a.any fun(i,fm)=>(ev fm (1<<<i) b 0 0).1 !=fm
lemma jV {T:N}{v:Z N}(h:jG (fO T) (v.map A8)=H):∃ p n:K,fc p n/\bit p T=H/\bit n T=J/\∀ w∈v,¬(bit p w=H/\bit n w=J):=by
 simp only[jG,Bf,CA] at h;obtain⟨⟨i,fm⟩,hmem,hne⟩:=h;simp only[fO,Bw,AM] at hmem;have⟨j,z,a⟩:=hmem;split at a;. contradiction
 . simp only[Dl,Prod.mk.injEq] at a;have⟨o,t⟩:=a;subst o;subst t;have g:∀ r,(ev (en T j) (1<<<j) (v.map A8) 0 0).1.testBit r=H->(en T j).testBit r=H:=by
    intro r hr;rw[iF] at hr;rcases hr with h0|⟨w,_,b⟩;. simp at h0
    . simp only[fA,Ad,X] at b;exact b.2
   have m:∃ r,(en T j).testBit r=H/\(ev (en T j) (1<<<j) (v.map A8) 0 0).1.testBit r=J:=by
    by_contra c;push Not at c;apply hne;apply AF;intro r;cases y:(en T j).testBit r
    . cases x:(ev (en T j) (1<<<j) (v.map A8) 0 0).1.testBit r
      . rfl
      . have:=g r x;rw[y] at this;cases this
    . cases x:(ev (en T j) (1<<<j) (v.map A8) 0 0).1.testBit r
      . exact Qa x (c r y)
      . rfl
   obtain⟨r,l,u⟩:=m;obtain⟨d,p,e,f,q,s⟩:=jq z l;refine⟨p,⟨r,d⟩,f,q,s,fun w hw ⟨hwp,hwn⟩=>?_⟩;have b:(fA (en T j) (1<<<j) w.toNat).testBit r=H:=by
    simp only[fA,Ad,Av,fg d,X,D8];refine⟨⟨?_,?_⟩,l⟩;. rw[eZ] at hwp;simpa[e,Aw] using hwp
    . rw[eZ] at hwn;exact hwn
   have k:=(iF (en T j) (1<<<j) (v.map A8) 0 0 r).mpr (D6 ⟨w.toNat,Qm hw,b⟩);rw[u] at k;cases k
lemma jK {T:N}{k:Nat}{g:Z N}(h:jG (fO T) (g.map A8)=H):u1 J T k g.toFinset:=by obtain⟨p,n,_,e,d,a⟩:=jV h;intro t _ f;obtain⟨w,i,c,b⟩:=f0 f rfl e d;exact a w (A4.mp i) ⟨c,b⟩
lemma wi {T:N}{k:Nat}{i:Z N}(h:jG (fO T) (i.map A8)=H):u2 T k i.toFinset:=by obtain⟨p,n,a,f,e,b⟩:=jV h;intro t _ g;obtain⟨w,j,d,c⟩:=ir g a f e;exact b w (A4.mp j) ⟨d,c⟩
lemma fi {x:Nat}(h:x≠0):∃ r,x.testBit r=H:=by
 by_contra a;push Not at a;apply h;apply AF;intro r;cases b:x.testBit r;. simp
 . exact Qa b (a r)
def tC {zr:Type}(roots:Z (O zr)):Nat->Z (O zr)->Prop
 | 0,b=>b=roots
 | p+1,c=>∃ (op:Y) (bank:Z (O zr)) (a b:O zr),tC roots p bank/\S J bank a/\S J bank b/\c=ez op a b::bank
def vt {zr:Type}(roots:Z (O zr)):Nat->Z (O zr)->Prop
 | 0,b=>∃ (bank:Z (O zr)) (a:O zr),tC roots 0 bank/\S J bank a/\b=jh a::bank
 | p+1,c=>
   (∃ (op:Y) (bank:Z (O zr)) (a b:O zr),vt roots p bank/\S J bank a/\S J bank b/\c=ez op a b::bank)\/
   (∃ (bank:Z (O zr)) (a:O zr),tC roots (p+1) bank/\S J bank a/\c=jh a::bank)
def R1 {c:Type}(a:Z (O c))(p:Nat)(u:Y)(b:Z (O c)):Prop:=if u then vt a p b else tC a p b
lemma R1.start {b}{a:Z (O b)}:R1 a 0 J a:=rfl
lemma R1.two {i}{d:Z (O i)}{p u c a b}(e:Y)(h:R1 d p u c)(f:S J c a)(g:S J c b):R1 d (p+1) u (ez e a b::c):=by cases u with|false=>exact⟨e,c,a,b,h,f,g,rfl⟩ | true=>exact D5 ⟨e,c,a,b,h,f,g,rfl⟩
lemma R1.unary {e}{c:Z (O e)}{p b a}(h:R1 c p J b)(d:S J b a):R1 c p H (jh a::b):=by cases p with|zero=>exact⟨b,a,h,d,rfl⟩ | succ p=>exact D6 ⟨b,a,h,d,rfl⟩
lemma jM {o}{i:Z (O o)}{p u j}(h:R1 i p u j):∃ j',Rc H i p j'/\∀ v,S J j v->S H j' v:=by
 have up:∀ {b:Z (O o)} {v:O o},S J b v->S H b v:=fun l=>by
  rcases l with h|h|⟨s,_⟩;. exact D5 h
  . exact D6 (D5 h)
  . cases s
 have d:∀ {b b':Z (O o)} {w:O o},(∀ v,S J b v->S H b' v)->∀ v,S J (w::b) v->S H (w::b') v:=fun c v l=>by
  rcases l with hm|z|⟨s,_⟩
  . rcases Ab.mp hm with rfl|q
    . exact D5 (by simp)
    . exact eW _ (c v (D5 q))
  . exact D6 (D5 z)
  . cases s
 have e:∀ {b b':Z (O o)} (a:O o),(∀ v,S J b v->S H b' v)->S J b a->∀ v,S J (jh a::b) v->S H b' v:=fun a c k v l=>by
  rcases l with hm|z|⟨s,_⟩
  . rcases Ab.mp hm with rfl|q
    . exact jF rfl (c a k)
    . exact c v (D5 q)
  . exact D6 (D5 z)
  . cases s
 induction p generalizing u j with
 | zero=>cases u with|false=>change j=i at h;subst j;exact⟨i,Rc.start,fun _ l=>up l⟩ | true=>obtain⟨m,a,r,k,rfl⟩:=h;change m=i at r;subst m;exact⟨i,Rc.start,e a (fun _ l=>up l) k⟩
 | succ p t=>
   cases u with
   | false=>obtain⟨n,m,a,b,r,k,hb,rfl⟩:=h;obtain⟨m',f,c⟩:=t (u:=J) r;exact⟨ez n a b::m',Rc.two n f (c a k) (c b hb),d c⟩
   | true=>
     rcases h with⟨n,m,a,b,r,k,hb,rfl⟩|⟨m,a,r,k,rfl⟩;. have⟨m',f,c⟩:=t (u:=H) r;exact⟨ez n a b::m',Rc.two n f (c a k) (c b hb),d c⟩
     . obtain⟨n,b1,x,y,h1,hx,hy,rfl⟩:=r;obtain⟨b1',g,c⟩:=t (u:=J) h1;exact⟨ez n x y::b1',Rc.two n g (c x hx) (c y hy),e a (d c) k⟩
lemma vl {m}(e:Z (O m)){p u d a b}(i:Y)(j:R1 e p u d)(k:S J d a)(l:S J d b):∃ q next,R1 e q u next/\S J next (ez i a b)/\(∀ v,S J d v->S J next v)/\q+fS a+fS b<=p+1+fS (ez i a b):=by
 classical
 by_cases c:ea a\/ea b
 . refine⟨p,d,j,jS i c k l,fun _ h=>h,?_⟩
   by_cases f:ea a<;>by_cases g:ea b
   . simp[fS,f,g,jQ i f g]
   . simp[fS,f,g]
   . simp[fS,f,g]
   . exact False.elim (c.elim f g)
 . have f:¬ea a:=fun h=>c (D5 h);have g:¬ea b:=fun h=>c (D6 h);exact⟨p+1,_,R1.two i j k l,D5 (by simp),fun _ h=>eW _ h,
   by simp[fS,f,g]⟩
lemma gx {zr}{c:O zr}(nc:¬ea c){s n}(h:Run J c s n)(j:Z (O zr)){p u i}(m:R1 j p u i)(l:fK J i n):∃ q next,R1 j q u next/\S J next c/\q+g0 n<=p+s:=by
 classical
 induction h using Run.ind generalizing p i with
 | stop=>exact⟨p,i,m,l _ (by simp),by simp[g0,fS,nc]⟩
 | perm eq _ w=>have d:fK J i _:=fun v k=>l v (eq.mem_iff.mp k);have⟨q,zw,z,k,hl⟩:=w m d;exact⟨q,zw,z,k,by simpa only[g0,<-(eq.map fS).sum_eq] using hl⟩
 | @two s a b rest t hd ka kb _ w=>
   obtain⟨t',x,y,e,hx,hy,cx,cy⟩:=h8 hd (l a (by simp)) (l b (by simp));obtain⟨r,T,hT,hz,g,le⟩:=vl j t' m hx hy;rw[<-e] at hz le;rw[cx,cy] at le;have ht:fK J T (l0 t a b::kept ka a (kept kb b rest)):=by
    intro v k;rcases Ab.mp k with rfl|o;. exact hz
    . apply g v;apply l;rcases hR o with rfl|o
      . simp
      . exact AK _ (Ab.mpr (hR o))
   obtain⟨q,zw,z,k,hl⟩:=w hT ht;have f:=gB a (kept kb b rest) ka;have f':=gB b rest kb;rw[f1] at hl;refine⟨q,zw,z,k,?_⟩;rw[f1,f1];omega
def sP {zr:Type}(goal:O zr):Nat->Z (O zr)->Prop
 | 0,zs=>List.Perm [goal] zs\/(∃ (ka:Y) (a:O zr) (rest:Z (O zr)),(a::rest).Perm zs/\Run J goal 0 (jh a::kept ka a rest))
 | s+1,zs=>
   (∃ (op:Nat) (ka kb:Y) (a b:O zr) (rest:Z (O zr)),op<2/\(a::b::rest).Perm zs/\sP goal s (l0 op a b::kept ka a (kept kb b rest)))\/
   (∃ (ka:Y) (a:O zr) (rest:Z (O zr)),(a::rest).Perm zs/\Run J goal (s+1) (jh a::kept ka a rest))
lemma jY {k l:Type}(c:l->k){e s j}(h:sP e s j):sP (e4 c e) s (j.map (e4 c)):=by
 induction s generalizing j with
 | zero=>
   rcases h with f|⟨i,a,d,f,g⟩;. exact D5 (f.map _)
   . refine D6 ⟨i,e4 c a,d.map (e4 c),f.map _,?_⟩
     have:=i4 c g;rw[As,gp] at this;exact this
 | succ s p=>
   rcases h with⟨n,i,m,a,b,d,o,f,g⟩|⟨i,a,d,f,g⟩
   . refine D5 ⟨n,i,m,e4 c a,e4 c b,d.map (e4 c),o,f.map _,?_⟩
     have:=p g;rw[As,gp,gp,gm] at this;exact this
   . refine D6 ⟨i,e4 c a,d.map (e4 c),f.map _,?_⟩
     have:=i4 c g;rw[As,gp] at this;exact this
lemma io {z}{c:O z}(y:¬ea c){s k a g}(w:Run J c s (jh a::kept k a g))(h:Z (O z)){p i}(x:R1 h p J i)(l:fK J i (a::g)):∃ q u next,R1 h q u next/\S J next c/\q+g0 (a::g)<=p+s:=by
 classical
 have m:=l a (by simp);by_cases ca:ea a
 . have f:S J i (jh a):=D6 (D5 (i8 ca));have r:fK J i (jh a::kept k a g):=by
    intro v hv;rcases Ab.mp hv with rfl|j;. exact f
    . rcases hR j with rfl|j
      . exact m
      . exact l v (AK _ j)
   have⟨q,t,n,b,o⟩:=gx y w h x r;have e:=gB a g k;rw[f1,tG] at o;rw[f1];exact⟨q,J,t,n,b,by omega⟩
 . have d:=R1.unary x m;have r:fK J (jh a::i) (jh a::kept k a g):=by
    intro v hv;rcases Ab.mp hv with rfl|j;. exact D5 (by simp)
    . apply eW;rcases hR j with rfl|j
      . exact m
      . exact l v (AK _ j)
   have⟨q,t,n,b,o⟩:=gx y w h d r;have e:=gB a g k;rw[f1,tG] at o;rw[f1];exact⟨q,H,t,n,b,by omega⟩
lemma vE {zr}{f:O zr}(nc:¬ea f){s o}(h:sP f s o)(l:Z (O zr)){p k}(hp:R1 l p J k)(hs:fK J k o):∃ q u next,R1 l q u next/\S J next f/\q+g0 o<=p+s:=by
 classical
 induction s generalizing o p k with
 | zero=>
   rcases h with m|⟨ka,a,j,m,t⟩;. have c:fK false k [f]:=fun v n=>hs v (m.mem_iff.mp n);refine⟨p,J,k,hp,c _ (by simp),?_⟩;unfold g0;rw[<-(m.map fS).sum_eq];simp[fS,nc]
   . have c:fK J k (a::j):=fun v n=>hs v (m.mem_iff.mp n);have⟨q,u,z,hW,d,w⟩:=io nc t l hp c;exact⟨q,u,z,hW,d,by simpa only[g0,<-(m.map fS).sum_eq] using w⟩
 | succ s ih=>
   rcases h with⟨op,ka,kb,a,b,j,hd,m,t⟩|⟨ka,a,j,m,t⟩
   . have c:fK J k (a::b::j):=fun v n=>hs v (m.mem_iff.mp n);obtain⟨op',x,y,e,hx,hy,cx,cy⟩:=h8 (u:=J) (D5 hd) (c a (by simp)) (c b (by simp));obtain⟨r,T,hT,hz,i,le⟩:=vl l op' hp hx hy;rw[<-e] at hz le;rw[cx,cy] at le;have ht:fK J T (l0 op a b::kept ka a (kept kb b j)):=by
      intro v n;rcases Ab.mp n with rfl|hh;. exact hz
      . apply i v;apply c;rcases hR hh with rfl|hh
        . simp
        . exact AK _ (Ab.mpr (hR hh))
     obtain⟨q,u,z,hW,d,w⟩:=ih t hT ht;have g:=gB a (kept kb b j) ka;have g':=gB b j kb;rw[f1] at w;refine⟨q,u,z,hW,d,?_⟩;change q+(o.map fS).sum<=_;rw[<-(m.map fS).sum_eq];change q+g0 (a::b::j)<=_;rw[f1,f1];omega
   . have c:fK J k (a::j):=fun v n=>hs v (m.mem_iff.mp n);have⟨q,u,z,hW,d,w⟩:=io nc t l hp c;exact⟨q,u,z,hW,d,by simpa only[g0,<-(m.map fS).sum_eq] using w⟩
lemma w7 {T:N}{k vs}(h:L1 T k vs)(v:Z N)(z:v.Nodup)(g:v.toFinset=vs):sP (A T) k (v.map A):=by
 classical
 have e:∀ {k' p a} {w:Z N},w.Nodup->neg a∉insert a p->Lv J T k' (insert (neg a) p)->w.toFinset=insert a p->∃ (q:Y) (a':O K) (m:Z (O K)),(a'::m).Perm (w.map A)/\Run J (A T) k' (jh a'::kept q a' m):=by
  intro k' p a w hw n o g';let m:=(p.erase a).toList;let q:=decide (a∈p);let c:=kept q a m;have t:m.toFinset=p.erase a:=(by simp[m]);have y:a∉m:=(by simp[m]);have s:m.Nodup:=Be _;have nd:=i5 q a m s y;have u:c.toFinset=p:=by change (kept q a m).toFinset=p;rw[im,t];ext j;by_cases aa:a∈p<;>by_cases aj:j=a<;>simp_all [q]
  have hf:neg a∉c:=fun hz=>n (A2 (u▸A4.mpr hz));have f:=tF o (neg a::c) (B7.mpr ⟨hf,nd⟩) (by simp[u]);change Run J (A T) k' ((neg a::kept q a m).map A) at f;rw[As,jz,tf] at f;have i:(a::m).Perm w:=by apply AT (by simp[y,s]) hw;ext j;by_cases ja:j=a<;>simp_all [t,g']
  exact⟨q,A a,m.map A,i.map _,f⟩
 induction k generalizing vs v with
 | zero=>
   rcases h with⟨rfl,_⟩|⟨p,a,rfl,_,_,n,o⟩;. have eq:[T].Perm v:=AT (by simp) z (by simpa[g]);exact D5 (eq.map _)
   . exact D6 (e z n o g)
 | succ k ih=>
   rcases h with⟨p,a,b,d,hd,rfl,_,_,x,n,o⟩|⟨p,a,rfl,_,_,n,o⟩
   . let m:=((p.erase a).erase b).toList;let q:=decide (a∈p);let r:=decide (b∈p);let l:=kept r b m;let c:=kept q a l;have t:m.toFinset=(p.erase a).erase b:=(by simp[m]);have y:a∉m:=(by simp[m]);have br:b∉m:=(by simp[m]);have s:m.Nodup:=Be _;have bm:=i5 r b m s br;have am:a∉l:=by cases h:r<;>simp[l,kept,h,x,y]
     have nd:=i5 q a l bm am;have u:c.toFinset=p:=by
      change (kept q a (kept r b m)).toFinset=p;rw[im,im,t];ext j;by_cases aa:a∈p<;>by_cases bb:b∈p<;>
       simp only[q,r,aa,bb,B6,decide_false,Ak,AX,AB,A9,AN]<;>grind
     have hf:V d a b∉c:=fun hz=>
      n (A2 (A2 (u▸A4.mpr hz)))
     have f:=ih o (V d a b::c) (B7.mpr ⟨hf,nd⟩) (by simp[u]);change sP (A T) k ((V d a b::kept q a (kept r b m)).map A) at f;rw[As,jz,jz,tw] at f;have i:(a::b::m).Perm v:=by apply AT (by simp[x,y,br,s]) z;ext j;rw[Bi,Bi,t,g];simp only[A9,AN];tauto
     exact D5 ⟨d,q,r,A a,A b,m.map A,hd,i.map _,f⟩
   . exact D6 (e z n o g)
def fH (a:Z N)(T:N)(b:Nat):Prop:=∀ p u bank,R1 (a.map A) p u bank->S J bank (A T)->b<=p
lemma xD {b T e}(h:fL H b T e):fH b T e:=by intro p u c d hit;obtain⟨c',d',a⟩:=jM d;exact h p c' d' (a _ hit)
lemma vY {T:N}{w:Z N}{z:N}{k g c}(l:L1 T k g)(t:eL w z\/(c=1/\ix J w z))(sub':∀ a∈g,a∈w++[z]):∃ k' g',k'<=k+c/\L1 T k' g'/\∀ a∈g',a∈w:=by
 by_cases j:z∈g
 . by_cases n:z∈w
   . refine⟨k,g,by omega,l,fun a i=>?_⟩
     rcases (by simpa using sub' a i:a∈w\/a=z) with h1|rfl<;>assumption
   . have hp:=we l z j;rcases t with hr|⟨rfl,d,a,b,hd,i,s,x,y,p,rfl⟩
     . exact False.elim ((hr.resolve_left n) hp)
     . have e:d<2:=by rcases hd with h|⟨h,_⟩<;>simp_all
       let m:=g.erase (V d a b);have ht:L1 T k (insert (V d a b) m):=(by simpa[m,BY j] using l)
       have r:∀ v∈m,v∈w:=fun v hv=>by
        have⟨f,j'⟩:=AN.mp hv;simpa[f] using sub' v j'
       have hf:V d a b∉insert a (insert b m):=by
        intro o;rcases A9.mp o with q|u;. exact n (q.symm▸i)
        rcases A9.mp u with q|u;. exact n (q.symm▸s)
        . exact n (r _ u)
       exact⟨_,_,BA _,L1.binary e x y p hf ht,by simpa using And.intro i (And.intro s r)⟩
 . refine⟨k,g,by omega,l,fun a i=>?_⟩
   have hn:a≠z:=fun o=>j (o▸i);simpa[hn] using sub' a i
lemma xV {t:Z N}{p u y T}(h:R1 (t.map A) p u y)(h1:∀ a∈t,ec a){k vs}(f:Lv J T k vs)(h5:∀ a∈vs,a∈y.map eV):(u=J->∃ l zv,l<=p+k/\Lv J T l zv/\∀ a∈zv,a∈t)/\(u=H->∃ l zv,l<=p+k/\L1 T l zv/\∀ a∈zv,a∈t):=by
 have j:∀ {b0:Z (O K)},(∀ v∈b0,ec (eV v))->∀ w,S J b0 w->ec (eV w):=fun xg w hw=>by
  rcases hw with hm|⟨bv,rfl⟩|⟨hf,_⟩;exact xg w hm;cases bv;exact(fu fun i=>(fZ _ i).trans (f5 i).symm:eV _=P).symm▸v4;exact(fu fun i=>(fZ _ i).trans (fM i).symm:eV _=one).symm▸v8;cases hf
 have s:∀ {p' b'},R1 (t.map A) p' J b'->∀ v∈b',ec (eV v):=fun {p'}=>by
  induction p' with
  | zero=>intro b' h' v hv;change b'=t.map A at h';subst h';obtain⟨a,ha,rfl⟩:=Aj.mp hv;rw[fy];exact h1 a ha
  | succ p' ih=>intro b' h' v hv;obtain⟨op,b0,a,b,h0,ha,hb,rfl⟩:=h';rcases Ab.mp hv with rfl|hm;rw[hQ];exact tL (j (ih h0) a ha) (j (ih h0) b hb);exact ih h0 v hm
 have o:(jc J ∘ eV)=eV:=funext fun _=>rfl;have n:∀ {b0:Z (O K)} {op a b},S J b0 a->S J b0 b->eL (b0.map eV) (gR op (eV a) (eV b))\/(1=1/\ix J (b0.map eV) (gR op (eV a) (eV b))):=fun {b0 op a b} ha hb=>by have hc:=uZ (u:=J) op (fx ha) (fx hb);simp only[iM,C4,o,gC] at hc;exact hc.imp id (fun h=>⟨rfl,h⟩)
 have g:∀ {b0:Z (O K)} {z:N} {vs':I N},(∀ x∈vs',x∈z::b0.map eV)->∀ x∈vs',x∈b0.map eV++[z]:=fun he x hx=>(Ab.mp (he x hx)).elim (fun e=>e▸mem_append_right _ BJ) (mem_append_left _);have hz (zl:Nat->I N->Prop) (hstep:∀ {b0:Z (O K)} {z k' vs'},zl k' vs'->eL (b0.map eV) z\/(1=1/\ix J (b0.map eV) z)->(∀ x∈vs',x∈b0.map eV++[z])->∃ k1 S1,k1<=k'+1/\zl k1 S1/\∀ x∈S1,x∈b0.map eV):
  ∀ {p' y'},R1 (t.map A) p' J y'->∀ {k' vs'},zl k' vs'->(∀ a∈vs',a∈y'.map eV)->∃ l zv,l<=p'+k'/\zl l zv/\∀ a∈zv,a∈t:=fun {p'}=>by
  induction p' with|zero=>intro y' h0 k' vs' f' h5';change y'=t.map A at h0;subst h0;rw[show (t.map A).map eV=t by simp[DI,fy]] at h5';exact⟨k',vs',by omega,f',h5'⟩ | succ p' ih=>intro y' h0 k' vs' f' h5';obtain⟨op,b0,a,b,d,ha,hb,rfl⟩:=h0;rw[As,hQ] at h5';obtain⟨k1,S1,h3,r,q⟩:=hstep f' (n ha hb) (g h5');obtain⟨l,zv,hl,hr,hs⟩:=ih d r q;exact⟨l,zv,by omega,hr,hs⟩
 have m:∀ {p' b0 a k' vs'},R1 (t.map A) p' J b0->S J b0 a->Lv J T k' vs'->(∀ v∈vs',v∈(jh a::b0).map eV)->∃ l zv,l<=p'+k'/\L1 T l zv/\∀ v∈zv,v∈t:=fun {p' b0 a k' vs'} d ha f' h5'=>by
  rw[As,vR] at h5';have h4:eL (b0.map eV) (eV a):=by have:=fx ha;rwa[iM,C4,o,gC] at this
  have ht:∃ l zv,l<=k'/\L1 T l zv/\∀ v∈zv,v∈b0.map eV:=by
   by_cases hm:neg (eV a)∈vs'
   . by_cases hw:neg (eV a)∈b0.map eV;exact⟨k',vs',BA _,L1.ofFalse f',fun v hv=>(Ab.mp (h5' v hv)).elim (fun e=>e▸hw) id⟩
     have hd:=tU (gA f' _ hm);have hg:=h4.resolve_right fun hn=>hn hd;let zu:=vs'.erase (neg (eV a));have hu:∀ v∈zu,v∈b0.map eV:=fun v hv=>(Ab.mp (h5' v (AN.mp hv).2)).resolve_left (AN.mp hv).1;exact⟨k',insert (eV a) zu,BA _,L1.unary hd (j (s d) a ha) (fun hh=>(A9.mp hh).elim (fun eq=>hw (eq.symm▸hg)) (fun hu'=>hw (hu _ hu'))) (by simpa[zu,BY hm] using f'),by simpa using And.intro hg hu⟩
   . exact⟨k',vs',BA _,L1.ofFalse f',fun v hv=>(Ab.mp (h5' v hv)).resolve_left fun eq=>hm (eq▸hv)⟩
  have⟨l1,V1,hk,hj,hi⟩:=ht;obtain⟨l,zv,hl,hr,hs⟩:=hz (L1 T) (fun f' hn hg=>vY f' hn hg) d hj hi;exact⟨l,zv,by omega,hr,hs⟩
 have h2:∀ {p' y'},R1 (t.map A) p' H y'->∀ {k' vs'},Lv J T k' vs'->(∀ a∈vs',a∈y'.map eV)->∃ l zv,l<=p'+k'/\L1 T l zv/\∀ a∈zv,a∈t:=fun {p'}=>by
  induction p' with
  | zero=>intro y' h0 k' vs' f' h5';obtain⟨b0,a,d,ha,rfl⟩:=h0;exact m d ha f' h5'
  | succ p' ih=>intro y' h0 k' vs' f' h5';rcases h0 with⟨op,b0,a,b,d,ha,hb,rfl⟩|⟨b0,a,d,ha,rfl⟩;rw[As,hQ] at h5';have⟨k1,S1,h3,r,q⟩:=jE (u:=J) (c:=1) f' (n ha hb) (g h5');obtain⟨l,zv,hl,hr,hs⟩:=ih d r q;exact⟨l,zv,by omega,hr,hs⟩;exact m d ha f' h5'
 exact⟨fun hf=>hz (Lv J T) (fun f' hn hg=>jE (u:=J) (c:=1) f' hn hg) (hf▸h) f h5,fun ht=>h2 (ht▸h) f h5⟩
lemma ii {f:Z N}{p u g T}(o:U T)(c:∀ a∈f,ec a)(h:R1 (f.map A) p u g)(e:S J g (A T)):∃ k vs,k<=p/\L1 T k vs/\∀ a∈vs,a∈f:=by
 have n:=fx e;rw[fy] at n;simp only[iM,gC] at n;have mem:T∈g.map eV:=by
  have q:=n.resolve_right (fun s=>s o);have d:∀ l:Z N,l.map (jc J)=l:=fun l=>by
   induction l with|nil=>rfl| cons x v r=>simp[gC,r]
  rwa[d] at q
 have b:=xV h c (Lv.stop (u:=J) o) (by simpa using mem);cases u with|false=>have⟨l,i,t,j,m⟩:=b.1 rfl;exact⟨l,i,by omega,L1.ofFalse j,m⟩ | true=>obtain⟨l,i,t,j,m⟩:=b.2 rfl;exact⟨l,i,by omega,j,m⟩
lemma vK (m:Nat):∀ a∈h7 m,ec a:=by intro a ha;obtain⟨⟨j,_⟩,hj,rfl⟩:=Aj.mp ha;obtain⟨b,rfl⟩:=ij hj;exact vr ⟨j,b⟩
lemma iX (m:Nat):∀ a∈eu m,ec a:=vK m
lemma wl {g T i}(l:U T)(c:∀ a∈g,ec a)(b:∀ a∈g,ic T g a)(d:u2 T i g.toFinset):fH g T (i+1):=by
 intro p u bank h ha;obtain⟨k,q,t,e,j⟩:=ii l c h ha;have m:g.toFinset=q:=by ext a;rw[A4];refine⟨fun o=>?_,j a⟩;obtain⟨r,s,n,f⟩:=b _ o;exact hH e g a j r s n f
 by_contra! small;exact d k (by omega) (m.symm▸e)
lemma vy {z e:Z N}{T zg:N}(pT:U T)(n:∀ a∈z,ec a)(pG:U zg)(r:K->K)(eq:gE r T=zg)(f8:∀ a∈z,S J (e.map A) (A (gE r a)))(c:I N)(f:∀ a∈c,ic T z a)(g:∀ a∈c,ea (A (gE r a)))(zl:Nat)(m:fH e zg zl):fH z T (zl+c.card):=by
 classical
 intro p u bank hh ha;have⟨k,vs,hk,l,h0⟩:=ii pT n hh ha;have o:c⊆vs:=fun a hs=>by
  have⟨i,j,hd,s⟩:=f a hs;exact hH l z a h0 i j hd s
 let d:=c.toList++(vs \ c).toList;have nd:d.Nodup:=by simp only[d,nodup_append];refine⟨Be _,Be _,fun a ha b hb he=>?_⟩;subst b;exact(Am.mp (Bz.mp hb)).2 (Bz.mp ha)
 have fe:d.toFinset=vs:=by ext a;simp[d,E2 o]
 have l':=w7 l d nd fe;have gc:e4 r (A T)=A zg:=(eR _ _).symm.trans (Az A eq);have t:fK J (e.map A) ((d.map A).map (e4 r)):=by intro v hv;obtain⟨_,hm,rfl⟩:=Aj.mp hv;obtain⟨a,h,rfl⟩:=Aj.mp hm;rw[<-eR];exact f8 a (h0 _ (fe▸A4.mpr h))
 have⟨q,u',bs,hq,ht,y⟩:=vE (gc▸gM pG) (jY r l') (e.map A) R1.start t;have x:zl<=q:=m q u' bs hq (gc▸ht);have w:c.card<=g0 ((d.map A).map (e4 r)):=by
  simp only[d,B5,vB];let xs:=(c.toList.map A).map (e4 r);have only:∀ v∈xs,ea v:=by intro v hv;obtain⟨_,hm,rfl⟩:=Aj.mp hv;obtain⟨a,h,rfl⟩:=Aj.mp hm;rw[<-eR];exact g _ (Bz.mp h)
  have sz:=jm xs only;simp only[xs,AQ,Finset.length_toList] at sz;change c.card<=g0 xs+_;rw[sz];omega
 omega
def sN (b:Z N)(T d:N)(c:Nat):Prop:=∃ (f:K->K) (roots:Z N),(∀ r,bit (f r) d=H)/\(∀ a∈b,S J (roots.map A) (e4 f (A a)))/\¬ea (e4 f (A T))/\∀ p u bank,R1 (roots.map A) p u bank->S J bank (e4 f (A T))->c<=p
lemma wv {j h T g i m d}(o:gl j h T g i=H)(k:ed j d=one)(b:U i)(n:fH g i m):sN h T d m:=by obtain⟨q,e⟩:=gI (u:=J) o;have c:e4 (et j) (A T)=A i:=(eR _ _).symm.trans (Az A q);refine⟨et j,g,fun r=>by rw[<-hE,k,fM],fun a l=>by rw[<-eR];exact e a l,c▸gM b,fun p u f s l=>n p u f s (c▸l)⟩
lemma wy {g T}(b:U T)(c:∀ a∈g,ec a)(h:Z (N×K×K))(j:el T g h=H):fH g T ((h.map G).toFinset.card-1):=by
 intro p u bank hr hit;have⟨k,n,q,d,i⟩:=ii b c hr hit;have o:(h.map G).toFinset.card<=n.card:=by apply Aa;intro a m;obtain⟨r,s,l,f⟩:=ga j a m;exact hH d g a i r s l f
 have e:=tV d;omega
lemma vT {o T i g l m k}(j:gH o T i g l m=H)(c:U T)(d:∀ a∈i,ec a)(b:U l)(f:fH g l k):fH i T (k+(m.map G).toFinset.card):=by
 simp only[gH,X] at j;obtain⟨p,e⟩:=gI (u:=J) j.1.1;apply vy c d b _ p e _ (ga j.1.2) _ k f;intro a q;obtain⟨⟨v,r,s⟩,hm,rfl⟩:=Aj.mp (A4.mp q);have n:=Ae.mp j.2 _ hm;simp only[Ai,Ar,ew] at n;rcases n with h|h;. rw[h];exact⟨J,funext f5⟩
 . rw[h];exact⟨H,funext fM⟩
lemma wL {m:Nat}(c:gu)(a:NN)(d:∀ q,fH (eu q) (e6 q) (a q))(ok:hZ m c a=H):sN (eu (g4 m c)) (fE m) (g5 c.1 c.2.1) c.2.2.2.2:=by
 revert ok;obtain⟨z,o,q,s,n⟩:=c;intro ok;let h:=j8 z o;let e:=g4 m (z,o,q,s,n);let b:=tI e (z%4096) o;let l:=ed h (fE m);let r:=iW (z / 4096+80) s;change (((eD l&&gl h (eu e) (fE m) (eu b) l)&&(ed h (g5 z o)==one))&&_)=H at ok;simp only[X,Ar] at ok;apply wv ok.1.1.2 ok.1.2 (eJ _ ok.1.1.1);intro p u f j k;have g:=ok.2;by_cases i:q=0;. simp only[i,AX,X,A6] at g;exact g.2.trans (wy (eJ _ ok.1.1.1) (iX b) r g.1 p u f j k)
 . simp only[i,AB,X,A6] at g;exact g.2.trans (vT g.1.2 (eJ _ ok.1.1.1) (iX b) (eJ _ g.1.1) (d q) p u f j k)
lemma xE {b d f c}(e:t4 b d c=H)(h:fH (eu d) (e6 d) f):fH (eu b) (e6 b) f:=by
 simp only[t4,X] at e;obtain⟨g,a⟩:=gI (u:=J) e.2;simpa only[CH,Dz] using
  vy (eJ _ e.1.1.1.1) (iX b) (eJ _ e.1.2) _ g a ∅ (by simp) (by simp) f h
lemma y0 {m q a i}(b c:Nat)(f:fH (eu q) (e6 q) a)(e:gH (j8 b 0) (e6 m) (eu m) (eu q) (e6 q) (eg b c)=H)(j:eD (e6 m)=H)(k:eD (e6 q)=H)(d:i<=a+(List.map G (eg b c)).toFinset.card):fH (eu m) (e6 m) i:=fun p u g l h=>d.trans (vT e (eJ _ j) (iX m) (eJ _ k) f p u g l h)
abbrev fp:=Y×B9
def fR (a:Z N)(T:N)(c:fp):Prop:=∃ (f:K->K) (roots:Z N) (bank:Z (O K)),(∀ r,bit (f r) c.2.d=H)/\¬ea (e4 f (A T))/\(∀ q u ws,R1 (roots.map A) q u ws->S J ws (e4 f (A T))->c.2.b<=q)/\R1 (roots.map A) c.2.p c.1 bank/\f6 J f bank c.2.w
def eb (c:g6):N:=if c.1==2 then neg c.2.1 else V c.1 c.2.1 c.2.2
def sT (c:fp)(d:Y)(k:Nat)(i:Z N)(j:g6):Y:=let(l,h):=c;let z:=eb j;let b:=em J h.d h.w z;let a:=(j.1==2);let g:=if d then(!l||!a||b) else(!l&&!a);let e:=if b||a then 0 else 1;let f:=b||(if a then em J h.d h.w j.2.1 else decide (j.1<2)&&em J h.d h.w j.2.1&&em J h.d h.w j.2.2);g&&decide (k+h.p+e<h.b+(z::i).countP (eI h.d))&&i.all (em J h.d h.w)&&f
lemma vo {ho T c u k h op}(p:fR ho T c)(nd:(eb op::h).Nodup)(s:sT c u k h op=H):if u then u1 J T k (eb op::h).toFinset else u2 T k (eb op::h).toFinset:=by
 rcases c with⟨pu,i⟩;have⟨f,l,z,g,nc,lo,hp,hs⟩:=p;simp only[sT,X,A6,Ae] at s;obtain⟨⟨⟨hokU,hbd⟩,hrest⟩,hokOp⟩:=s;let ws:=eb op::h;have hk:u=J->pu=J:=fun hu=>by subst hu;simp only[Ak,AB,X,D8] at hokU;exact hokU.1
 have m:∃ n u' b,R1 (l.map A) n u' b/\f6 J f b ws/\(u=J->u'=J)/\n=i.p+(if em J i.d i.w (eb op)||(op.1==2) then 0 else 1):=by
  cases w:em J i.d i.w (eb op)
  . simp only[w,BT] at hokOp;cases d:(op.1==2)
    . simp only[d,Ak,AB,X,A6] at hokOp;obtain⟨⟨hlt,ha⟩,hb⟩:=hokOp;obtain⟨op',x,y,e,hx,hy,_,_⟩:=h8 (u:=J) (D5 hlt) (ee g hs ha) (ee g hs hb);exact⟨i.p+1,pu,_,R1.two op' hp hx hy,fun a ha'=>(Ab.mp ha').elim (fun eq=>by subst eq;simp only[eb,d,Ak,AB,tw,gm,e];exact D5 BJ) (fun hm=>eW _ (ee g hs (hrest a hm))),hk,by simp⟩
    . have h0:u=H:=(by cases u;simp[d] at hokU;rfl);have h2:pu=J:=(by subst h0;simp[d,w] at hokU;exact hokU);subst h2;simp only[d,AX] at hokOp;exact⟨i.p,H,_,R1.unary hp (ee g hs hokOp),fun a ha=>(Ab.mp ha).elim (fun eq=>by subst eq;simp only[eb,d,AX,tf];exact D5 BJ) (fun hm=>eW _ (ee g hs (hrest a hm))),fun hu=>by simp[hu] at h0,by simp⟩
  . exact⟨i.p,pu,z,hp,fun a ha=>(Ab.mp ha).elim (fun eq=>eq▸ee g hs w) (fun hm=>ee g hs (hrest a hm)),hk,by simp⟩
 obtain⟨n,u',b,j,h1,h5,hc⟩:=m;have o:fK J b ((ws.map A).map (e4 f)):=fun v hv=>by obtain⟨_,hm,rfl⟩:=Aj.mp hv;obtain⟨a,ha,rfl⟩:=Aj.mp hm;exact h1 a ha
 have hd:ws.countP (eI i.d)<=g0 ((ws.map A).map (e4 f)):=jg g ws;change k+i.p+(if em J i.d i.w (eb op)||(op.1==2) then 0 else 1) < i.b+ws.countP (eI i.d) at hbd;cases u;. intro t ht hh;have hu':u'=J:=h5 rfl;subst hu';have⟨q,u'',b',hq,r,h3⟩:=vE nc (jY f (w7 hh ws nd rfl)) (l.map A) j o;have h4:i.b<=q:=lo q u'' b' hq r;omega
 . intro t ht hh;have⟨q,b',hq,r,h3⟩:=gx nc (i4 f (tF hh ws nd rfl)) (l.map A) j o;have h4:i.b<=q:=lo q u' b' hq r;omega
def ff (T:N)(r s:Fin 320->K):Prop:=∀ i,fc (r i) (s i)/\bit (r i) T=H/\bit (s i) T=J
lemma y5 {T ws k}(h:L1 T k (List.toFinset ws)){r s:Fin 320->K}(b:ff T r s):f8 H (f3 r s) ws=AO:=by apply Af;intro j e;let i:Fin 320:=⟨j,e⟩;have⟨c,d,f⟩:=b i;rw[BL];simp only[e,B6];apply(vf (i:=i)).mpr;obtain⟨a,l,g,m⟩:=ir h c d f;refine⟨a,A4.mp l,?_⟩;simp only[eP,AX,Aq,AW,i.isLt,B6,f3,fd,g,m,Dy,Bool.and_self]
def iG (p q:Nat->fU):Y:=(range 12).all fun j=>(p j&&&q j)==q j
lemma yk {p q:Nat->fU}(h:iG p q=H)(i:Fin 320):fc (fq p i) (fq q i):=by
 simp only[iG,Ae,AM,Ar] at h;unfold fc;apply AF;intro j;by_cases d:j<12
 . have a:∀ (v:Nat->fU),(fq v i).val.testBit j=(v j).getLsbD i.val:=by intro v;have:=jD v i ⟨j,d⟩;rw[fv] at this;exact this
   rw[Ad,a p,a q];have e:=Az (fun b:fU=>b.getLsbD i.val) (h j d);simpa[Aq] using e
 . have c:4096<=2 ^ j:=by change 2 ^ 12<=2 ^ j;exact Ba (by decide) (by omega)
   rw[Ad,AH (lt_of_lt_of_le (fq q i).isLt c),Cs]
lemma xX (gs:Z Gate)(w:Z N)(d:∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2)(c:∀ g∈gs,fj g=J)(m:∀ x∈w,ec x):∀ x∈ek gs w,ec x:=by
 induction gs generalizing w with
 | nil=>exact m
 | cons g gs k=>
   apply k (w++[gv w g]) (fun a n=>d a (by simp[n])) (fun a n=>c a (by simp[n]));intro x q;rcases Bx.mp q with o|p;. exact m x o
   . obtain rfl:=Bh.mp p;obtain⟨j,_⟩:=d g (by simp);have h:=c g (by simp);have f:∀ i,ec (w.getD i P):=fun i=>by
      simp only[A1];cases e:w[i]? with|none=>exact v4 | some v=>exact m v (Dh e)
     simp only[C8,BO] at j;rcases j with j|j|j
     . simp only[gv,j];have b:∀ l:W,ec ((l.map fun i=>w.getD i P).foldr (gR J) one):=fun l=>by
        induction l with|nil=>exact v8| cons i l k=>exact tL (f i) k
       exact b g.inputs
     . simp only[gv,j];have b:∀ l:W,ec ((l.map fun i=>w.getD i P).foldr (gR H) P):=fun l=>by
        induction l with|nil=>exact v4| cons i l k=>exact tL (f i) k
       exact b g.inputs
     . simp[fj,j] at h
lemma wu (f:Z Gate)(h:f.countP fj=1):∃ g1 g g2,f=g1++g::g2/\fj g=H/\(∀ x∈g1,fj x=J)/\(∀ x∈g2,fj x=J):=by
 induction f with
 | nil=>simp at h
 | cons x i m=>
   rw[BR] at h;cases d:fj x
   . simp only[d,Ak,AB,Dz] at h;obtain⟨g1,g,g2,rfl,n,l,j⟩:=m h;refine⟨x::g1,g,g2,rfl,n,?_,j⟩;intro y k;rcases Ab.mp k with rfl|a
     . exact d
     . exact l y a
   . simp only[d,AX] at h;have o:i.countP fj=0:=(by omega)
     have j:∀ y∈i,fj y=J:=fun y k=>by
      by_contra c;have a:fj y=H:=by cases e:fj y<;>simp_all
      have b:=countP_pos_iff.mpr ⟨y,k,a⟩;omega
     exact⟨[],x,i,rfl,d,by simp,j⟩
lemma xI (gs:Z Gate)(w:Z N)(j:∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2)(hw:∀ x∈w,ec x)(h5:gs.countP fj=1){b:N}(hp:U b)(hc:b∈ek gs w):∃ k vs,k+1<=gs.length/\L1 b k vs/\∀ a∈vs,a∈w:=by
 let zl (g:Gate):=g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2;obtain⟨g1,g,g2,rfl,x2,h1,h2⟩:=wu gs h5;set W1:=ek g1 w;rw[show ek (g1++g::g2) w=ek g2 (W1++[gv W1 g]) by simp only[W1,ek,Ca,Bn]] at hc
 have m:∀ x∈g1,zl x:=fun x hx=>j x (by simp[hx]);have h0:∀ x∈g2,zl x:=fun x hx=>j x (by simp[hx]);have f:∀ l:Z N,l.map (jc J)=l:=fun l=>by induction l with|nil=>rfl| cons x xs ih=>simp[gC,ih]
 obtain⟨k2,S2,hz,d,c⟩:=vM (u:=J) g2 (W1++[gv W1 g]) h0 (fun _=>h2) hp (by simpa[gC] using hc);rw[f] at c;have hg:k2<=g2.length:=hz.trans countP_le_length;have hk:=xX g1 w m h1 hw;have hj:g.op=GateOp.not:=by cases e:g.op<;>simp_all[fj]
 have o:∃ S1,L1 b k2 S1/\∀ a∈S1,a∈W1:=by
  by_cases hm:gv W1 g∈S2
  . by_cases n:gv W1 g∈W1
    . exact⟨S2,L1.ofFalse d,fun a ha=>(by simpa using c a ha:a∈W1\/a=gv W1 g).elim id (fun e=>e▸n)⟩
    . have hb:=gA d _ hm;have hy:gv W1 g=neg ((g.inputs.map fun i=>W1.getD i P).headD P):=(by simp[gv,hj]);set a:=(g.inputs.map fun i=>W1.getD i P).headD P;rw[hy] at hm n hb c;have h3:=tU hb;have h4:a∈W1:=by cases hi:g.inputs with|nil=>exact Qa (by simp[a,hi]) h3.1| cons x6 _=>have q:a=W1.getD x6 P:=(by simp[a,hi]);rw[q,A1];cases he:W1[x6]? with|none=>exact Qa (by simp[q,he]) h3.1| some v=>exact Dh he
      let zu:=S2.erase (neg a);have hu:∀ v∈zu,v∈W1:=fun v hv=>by have⟨y,hm'⟩:=AN.mp hv;simpa[y] using c v hm'
      exact⟨insert a zu,L1.unary h3 (hk a h4) (fun hh=>(A9.mp hh).elim (fun eq=>n (eq.symm▸h4)) (fun hu'=>n (hu _ hu'))) (by simpa[zu,BY hm] using d),by simpa using And.intro h4 hu⟩
  . exact⟨S2,L1.ofFalse d,fun a ha=>by have y:a≠gv W1 g:=fun eq=>hm (eq▸ha);simpa[y] using c a ha⟩
 have⟨S1,s,t⟩:=o;have p:∀ (z:Z Gate) (w0:Z N),(∀ x∈z,zl x)->(∀ x∈z,fj x=J)->∀ {k' vs'},L1 b k' vs'->(∀ a∈vs',a∈ek z w0)->∃ l zv,l<=z.length+k'/\L1 b l zv/\∀ a∈zv,a∈w0:=fun z=>by
  induction z with|nil=>intro w0 _ _ k' vs' hL hS;exact⟨k',vs',by omega,hL,hS⟩ | cons x xs ih=>intro w0 hleg hnn k' vs' hL hS;obtain⟨l1,V1,x0,ho,hd⟩:=ih (w0++[gv w0 x]) (fun a ha=>hleg a (by simp[ha])) (fun a ha=>hnn a (by simp[ha])) hL hS;have r:=vQ J w0 x (hleg x (by simp)) (fun _=>hnn x (by simp));rw[iM,f,gC] at r;obtain⟨l2,V2,x1,hq,hn⟩:=vY ho (r.imp id (fun h=>⟨rfl,h.2⟩)) hd;exact⟨l2,V2,by simp;omega,hq,hn⟩
 have⟨l,zv,hl,hr,hs⟩:=p g1 w m h1 s t;exact⟨l,zv,by simp only[CC,AY];omega,hr,hs⟩
def vC (i:B):Nat:=[7,6,9,8,7,6,1,0,3,2,1,0].getD i.val 0
def hI (i:B):K:=Fin.ofNat 4096 (1<<<vC i)
def gV (i:B):K:=Fin.ofNat 4096 ((1<<<i.val)|||(1<<<vC i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma gy:(∀ i:B,bit (hI i) graph≠bit (gV i) graph)/\(∀ i j:B,i≠j->bit (hI i) (u3.getD j.val P)=bit (gV i) (u3.getD j.val P)):=by decide +kernel
lemma threeWaySplit (hMono:∀ zc:Circuit,PEqualNP.MetaComplexity.Monotone2 zc->zc.size<=20->(∀ x:B->Y,zc.eval (Da x)=edge x)->False)(hOne:u2 graph 19 u3.toFinset)(hFree:u1 H graph 18 u3.toFinset):¬ PEqualNP.MetaComplexity.HasCircuitSize 12 edge 20:=by
 rintro⟨zc,d,l,b⟩;have c:(ek zc.gates u3).getD zc.output P=graph:=Af fun j hj=>(wo zc d zc.output ⟨j,hj⟩).trans ((b (ti ⟨j,hj⟩)).trans (xt ⟨j,hj⟩).symm);have n:graph∈ek zc.gates u3:=by rw[<-c,A1];cases e:(ek zc.gates u3)[zc.output]? with|none=>exact False.elim (gw.1 (by rw[<-c,A1,e];rfl))| some v=>exact Dh e
 have o (a:N) (z:a∈u3):∃ i:B,u3.getD i.val P=a:=by rw[<-iZ] at z;exact mem_ofFn.mp z
 have y (s:I N) (r:∀ a∈s,a∈u3) (hR:∀ i:B,(∀ v∈u3,v≠u3.getD i.val P->bit (hI i) v=bit (gV i) v)->u3.getD i.val P∈s):s=u3.toFinset:=by ext a;exact⟨fun h=>A4.mpr (r a h),fun z=>by obtain⟨i,rfl⟩:=o a (A4.mp z);exact hR i fun v hv hn=>by obtain⟨j,rfl⟩:=o v hv;exact gy.2 i j fun h=>hn (h▸rfl)⟩
 by_cases h0:zc.gates.countP fj=0;. apply hMono zc (fun g hg=>by obtain⟨f,q⟩:=d g hg;refine⟨?_,q⟩;have t:fj g=J:=(by by_contra h2;have ht:fj g=H:=(by cases e:fj g<;>simp_all);have:=countP_pos_iff.mpr ⟨g,hg,ht⟩;omega);simp only[C8,BO] at f ⊢;rcases f with f|f|f;exact D5 f;exact D6 f;simp[fj,f] at t) l b
 . by_cases h1:zc.gates.countP fj=1
   . obtain⟨k,s,hk,m,r⟩:=xI zc.gates u3 d y3 h1 gw n;exact hOne k (by change zc.gates.length<=20 at l;omega) (y s r (fun i=>hH m u3 _ r (hI i) (gV i) (gy.1 i))▸m)
   . have w:zc.gates.countP fj+zc.gates.countP (fun g=>!fj g)=zc.gates.length:=by induction zc.gates with|nil=>simp| cons g gs ih=>rw[BR,BR,AY];cases fj g<;>simp<;>omega
     have p:=tl (u:=H) (ek zc.gates u3) zc.output;rw[c] at p;unfold iM at p;rw[uV (by decide +kernel:bit 0 graph=J)] at p;obtain⟨k,s,hk,m,r⟩:=vM (u:=H) zc.gates u3 d (by simp) gw (p.resolve_right fun h=>h gw);rw[vJ (by decide +kernel:u3.all eN=H)] at r;exact hFree k (by change zc.gates.length<=20 at l;omega) (y s r (fun i=>i6 m u3 _ r (hI i) (gV i) (gy.1 i))▸m)
lemma y4 {v:Nat}(f:eO v=H){r s:K}(h:fc r s):fc (j2 (eo v) r) (j2 (eo v) s):=by
 unfold fc at h ⊢;apply AF;intro t;by_cases e:t<12
 . have⟨d,c⟩:=vA f e;have a:∀ x:K,(j2 (eo v) x).val.testBit t=x.val.testBit (iv v t):=fun x=>by
    rw[<-fv ⟨t,e⟩,<-vW,c,fv ⟨iv v t,d⟩]
   rw[Ad,a r,a s];simpa[Ad] using Az (fun n=>n.testBit (iv v t)) h
 . have b:4096<=2 ^ t:=by change 2 ^ 12<=2 ^ t;exact Ba (by decide) (by omega)
   rw[Ad,AH (lt_of_lt_of_le (j2 (eo v) s).isLt b),Cs]
lemma yc {a:W}(b:a.all eO=H){r s:K}(h:fc r s):fc (et (a.map eo) r) (et (a.map eo) s):=by induction a generalizing r s with|nil=>exact h | cons v c d=>simp only[all_cons,X] at b;exact d b.2 (y4 b.1 h)
lemma iq (r:K->K)(a:N):gE r (neg a)=neg (gE r a):=fu fun i=>by rw[eX,ft,ft,eX]
lemma vk {r:K->K}(b:∀ p n,fc p n->fc (r p) (r n)){a:N}(c:ec a):ec (gE r a):=by intro p n hpn hn;rw[eX] at hn ⊢;exact c (r p) (r n) (b p n hpn) hn
lemma xT {T k vs}(h:L1 T k vs)(r:K->K)(i:Function.Surjective r)(g:∀ p n,fc p n->fc (r p) (r n)):L1 (gE r T) k (vs.image (gE r)):=by
 classical
 have j:Function.Injective (gE r):=fun a b e=>fu fun x=>by
  obtain⟨y,rfl⟩:=i x;have:=Az (bit y) e;rwa[eX,eX] at this
 have f:∀ {w:N} {zv:I N},w∉zv->gE r w∉zv.image (gE r):=by intro w zv hnw hm;have⟨x,hx,l⟩:=A7.mp hm;exact hnw (j l▸hx)
 have c:∀ {w:N},U w->U (gE r w):=fun⟨h0,h1⟩=>
  ⟨fun e=>h0 (j (e.trans (gg r).1.symm)),fun e=>h1 (j (e.trans (gg r).2.symm))⟩
 induction k generalizing vs with
 | zero=>
   rcases h with⟨rfl,hp⟩|⟨s,a,rfl,t,q,m,o⟩;. exact D5 ⟨by simp,c hp⟩
   . refine D6 ⟨s.image (gE r),gE r a,by rw[Ax],c t,vk g q,?_,?_⟩
     . rw[<-iq,<-Ax];exact f m
     . have u:=jw o r i;rwa[Ax,iq] at u
 | succ k ih=>
   rcases h with⟨s,a,b,d,z,rfl,t,hb,v,m,o⟩|⟨s,a,rfl,t,q,m,o⟩
   . refine D5 ⟨s.image (gE r),gE r a,gE r b,d,z,by rw[Ax,Ax],c t,c hb,fun e=>v (j e),?_,?_⟩
     . rw[<-iY,<-Ax,<-Ax];exact f m
     . have u:=ih o;rwa[Ax,iY] at u
   . refine D6 ⟨s.image (gE r),gE r a,by rw[Ax],c t,vk g q,?_,?_⟩
     . rw[<-iq,<-Ax];exact f m
     . have u:=jw o r i;rwa[Ax,iq] at u
lemma y7 {T n}{i:Z N}(o:u2 T n i.toFinset)(b:W)(q:b.all eO=H)(l:hG T (b.map eo)=H):u2 T n (i.map (ed (b.map eo).reverse)).toFinset:=by
 let p:=b.map eo;simp only[hG,X,Ar] at l;have f:Function.Surjective (et p):=fun r=>⟨et p.reverse r,iu l.2 r⟩;have c:∀ r s,fc r s->fc (et p r) (et p s):=fun _ _ h=>yc q h;intro k t h;have d:=xT h (et p) f c;have g:gE (et p) T=T:=(ew p T).symm.trans l.1.1;have jh (x:N):gE (et p) (ed p.reverse x)=x:=by apply Af;intro j m;change bit ⟨j,m⟩ _=bit ⟨j,m⟩ _;rw[eX,hE,iu l.1.2]
 have e:(i.map (ed p.reverse)).toFinset.image (gE (et p))=i.toFinset:=by
  ext a;simp only[A7,A4,Aj];constructor;. rintro⟨_,⟨w,v,rfl⟩,rfl⟩;simpa only[jh] using v
  . intro u;exact⟨_,⟨a,u,rfl⟩,jh a⟩
 rw[g,e] at d;exact o k t d
lemma yi {T:N}{k:Nat}{v:Z N}(nd:v.Nodup)(h0:T∉v)(q:∀ a∈v,∀ b∈v,∀ d < 2,∀ ka kb:Y,a≠b->V d a b∉v->U (V d a b)->(eQ v a b d ka kb).length<=k->u2 T (k-1) (eQ v a b d ka kb).toFinset)(h:∀ a∈v,neg a∉v->U a->ec a->v.length<=k+1->u1 J T k (neg a::v.erase a).toFinset)(i:∀ a∈v,neg a∉v->U a->ec a->v.length+1<=k+1->∀ t ≤ k,∀ zu:I N,v.toFinset=insert a zu->a∈zu->¬Lv J T t (insert (neg a) zu)):u2 T k v.toFinset:=by
 classical
 have c:∀ {t zu a},t<=k->v.toFinset=insert a zu->U a->ec a->neg a∉insert a zu->Lv J T t (insert (neg a) zu)->False:=by
  intro t zu a ht eq ha he hf h5;have j:a∈v:=A4.mp (eq▸AL a zu);have f:neg a∉v:=fun hm=>hf (eq▸A4.mpr hm);have n:=gz h5;have h1:neg a∉zu:=fun hm=>hf (A2 hm);rw[Al h1] at n;by_cases m:a∈zu
  . have hU:zu=v.toFinset:=(by rw[eq,Cd m]);have l:v.length+1<=k+1:=by rw[hU,Ap nd] at n;omega
    exact i a j f ha he l t ht zu eq m h5
  . have hU:zu=(v.erase a).toFinset:=by ext x;rw[A4,nd.mem_erase_iff];exact⟨fun hx=>⟨fun h4=>m (h4▸hx),A4.mp (eq▸A2 hx)⟩,fun⟨hne,hx⟩=>(A9.mp (eq▸A4.mpr hx)).resolve_left hne⟩
    have l:v.length<=k+1:=by have o:v.toFinset.card=zu.card+1:=(by rw[eq,Al m]);rw[Ap nd] at o;omega
    have g:insert (neg a) zu=(neg a::v.erase a).toFinset:=(by rw[Bi,hU]);exact h a j f ha he l t ht (g▸h5)
 intro t ht run;cases t with
 | zero=>
   rcases run with⟨hS,_⟩|⟨zu,a,eq,ha,he,hf,h5⟩;. exact h0 (A4.mp (by rw[hS];exact Ao T))
   . exact c ht eq ha he hf h5
 | succ t=>
   rcases run with⟨zu,a,b,d,hd,eq,ha,hb,hl,hf,h5⟩|⟨zu,a,eq,ha,he,hf,h5⟩
   . have j:a∈v:=A4.mp (eq▸AL a _);have s:b∈v:=A4.mp (eq▸A2 (AL b _));have f:V d a b∉v:=fun hm=>hf (eq▸A4.mpr hm);have z:U (V d a b):=we h5 _ (AL _ _);let ka:=decide (a∈zu);let kb:=decide (b∈zu);have g:insert (V d a b) zu=(eQ v a b d ka kb).toFinset:=by
      ext x;simp only[eQ,Bi,A9,A4,iJ,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,ka,kb];have r:∀ y,y∈v↔y=a\/y=b\/y∈zu:=fun y=>by
       rw[<-A4,eq,A9,A9]
      rw[r x];by_cases aU:a∈zu<;>by_cases bU:b∈zu<;>
       simp only[aU,bU,B6,decide_false,Ak,AX,AB]<;>grind
     have w:(eQ v a b d ka kb).Nodup:=by
      have p:((v.erase a).erase b).Sublist v:=erase_sublist.trans erase_sublist;have u:((v.erase a).erase b).Nodup:=nd.sublist p;have h2:b∉(v.erase a).erase b:=fun hm=>((nd.sublist erase_sublist).mem_erase_iff.mp hm).1 rfl;have h3:a∉kept kb b ((v.erase a).erase b):=by
       rw[iJ];rintro (⟨rfl,_⟩|hm)
       . exact hl rfl
       . exact(nd.mem_erase_iff.mp (erase_sublist.subset hm)).1 rfl
      refine B7.mpr ⟨fun hm=>?_,i5 ka a _ (i5 kb b _ u h2) h3⟩
      rw[iJ,iJ] at hm;rcases hm with⟨e,_⟩|⟨e,_⟩|hj;. exact f (e.symm▸j)
      . exact f (e.symm▸s)
      . exact f (p.subset hj)
     have n:=tV h5;rw[g,Ap w] at n;exact q a j b s d hd ka kb hl f z (by omega) t (by omega) (g▸h5)
   . exact c ht eq ha he hf h5
def sJ (v:Nat):Nat:=#[0x880,0xc40,0x600,0xb00,0x580,0x2c0,0x22,0x31,0x18,0x2c,0x16,0x0b].getD v 0
def tH {c:Type}(l:Z (fU×fU))(k:Z (fU×fU)->c):c:=List.rec (fun k=>k []) (fun p _ d k=>kk p.1 fun a=>kk p.2 fun b=>d fun e=>k ((a,b)::e)) l k
lemma tj {c:Type}(l:Z (fU×fU))(k:Z (fU×fU)->c):tH l k=k l:=by induction l generalizing k with|nil=>rfl| cons p l d=>change kk p.1 (fun a=>kk p.2 fun b=>tH l fun e=>k ((a,b)::e))=_;rw[kw,kw,d]
def lP {d:Type}(l:Z D)(k:Z D->d):d:=List.rec (fun k=>k []) (fun x _ e k=>kk x.1 fun a=>kk x.2.1 fun b=>kk x.2.2 fun c=>e fun f=>k ((a,b,c)::f)) l k
lemma lM {d:Type}(l:Z D)(k:Z D->d):lP l k=k l:=by induction l generalizing k with|nil=>rfl| cons x l e=>change kk x.1 (fun a=>kk x.2.1 fun b=>kk x.2.2 fun c=>lP l fun f=>k ((a,b,c)::f))=_;rw[kw,kw,kw,e]
def tX (m:Nat):Nat->Nat->Nat->W->W
 | 0,cur,_,acc=>cur::acc
 | i+1,cur,blk,acc=>
   let acc1:=tX m i cur blk acc
   if m.testBit i&&!blk.testBit i then E (cur|||(1<<<i)) fun c=>E (blk|||sJ i) fun b=>tX m i c b acc1 else acc1
def vX (m s:Nat):Y:=(range 12).all fun v=>!m.testBit v||s.testBit v||((sJ v&&&s) !=0)
def wt (m:Nat):LP:=(range 12).flatMap fun u=>if !m.testBit u then [] else((range 12).filter (fun v=>u<v&&m.testBit v&&(sJ u).testBit v)).flatMap fun v=>let r:=(1<<<u)|||(1<<<v);[(r,1<<<u),(r,1<<<v)]
def jW (m:Nat)(a:W):LP:=a.flatMap fun s=>((range 12).filter (fun v=>m.testBit v&&!s.testBit v&&((sJ v&&&s) !=0))).map fun v=>(s|||(1<<<v),s)
def xz (m:Nat)(a:W):LP:=(range 12).flatMap fun u=>if !m.testBit u then [] else((range 12).filter (fun v=>u<v&&m.testBit v&&(sJ u).testBit v)).flatMap fun v=>let r:=(1<<<u)|||(1<<<v);(a.filter fun s=>s.testBit u !=s.testBit v).map fun s=>(r,s)
def wP (b:Y)(m:Nat):LP:=f2 (tX m 12 0 0 []).reverse fun a=>f2 (a.filter (vX m)) fun c=>(wt m++jW m c++(if b then xz m c else jW m (a.filter fun s=>!vX m s))).take 320
def vc (j:Nat):LP->PP
 | []=>(0,0)
 | (pr,qr)::rest=>
   let r:=vc j rest
   E (r.1*2+if pr.testBit j then 1 else 0) fun p=>E (r.2*2+if qr.testBit j then 1 else 0) fun q=>(p,q)
def j9 (a:Y)(m:Nat):Z (fU×fU):=wW (wP a m) fun b=>E b.length fun c=>(range 12).map fun j=>let(p,q):=vc j b;(wg c p,wg c q)
def eH (a:Y)(m:Nat)(j:Nat):fU×fU:=(j9 a m).getD j (0,0)
def sV (x:D):D:=(neg x.1,~~~x.2.1,~~~x.2.2)
lemma wR {n:Nat}(r:F n->K)(a:N):gZ r (neg a)= ~~~(gZ r a):=by apply Af;intro j b;rw[AW,fd r (neg a) ⟨j,b⟩,ft,fd r a ⟨j,b⟩];simp[b]
lemma v9 {r s x}(a:ex r s x):ex r s (sV x):=by change x.2=_ at a;simp[ex,sV,f3,wR,a]
def tk (a:Y)(b:Nat)(x y:D):D:=if !a&&b==2 then sV x else ji b x y
lemma wx {r s x y}(a:Y)(c:Nat)(b:ex r s x)(d:ex r s y):ex r s (tk a c x y):=by
 unfold tk;split;. exact v9 b
 . exact j1 c b d
def i2 (d:Y)(n c:Nat)(a:Z D):Z D:=match n with
 | 0=>a
 | k+1=>
   let w:=tk d ((c>>>10)&&&3) (a.getD (c&&&31) C) (a.getD ((c>>>5)&&&31) C)
   kk w.1 fun u=>kk w.2.1 fun p=>kk w.2.2 fun q=>E (D3 c 12) fun c'=>i2 d k c' (a++[(u,p,q)])
lemma h9 (a:Y)(n bits ws r s)(b:∀ v∈ws,ex r s v):∀ v∈i2 a n bits ws,ex r s v:=by
 induction n generalizing ws bits with
 | zero=>exact b
 | succ n c=>
   simp only[i2,kw,R];apply c;intro v e;rcases Bx.mp e with d|f;. exact b _ d
   . obtain rfl:=Bh.mp f;exact wx a _ (wd b _) (wd b _)
def tq (bits:Nat):W->W
 | []=>[]
 | w::ws=>cond (M (L bits 1) 1) (w::tq (D3 bits 1) ws) (tq (D3 bits 1) ws)
lemma tM (a:Nat)(ws:W):tq a ws=fw a ws:=by
 induction ws generalizing a with|nil=>rfl| cons w ws b=>
  unfold tq fw;rw[b];change cond (a&&&1==1) _ _=_;cases (a&&&1==1)<;>rfl
def sE (a:Y)(b x y:Nat):Nat:=cond (and (not a) (M b 2)) (D9 z4 x) (zN b x y)
lemma vd (c:Y)(i:Nat)(a b:N):sE c i a.toNat b.toNat=(if !c&&i==2 then neg a else V i a b).toNat:=by
 unfold sE;cases h:and (not c) (M i 2) with
 | true=>
   simp only[D4,AX];apply AF;intro j;change (z4^^^a.toNat).testBit j=_;by_cases k:j<4096;. rw[fg k,<-eZ ⟨j,k⟩,<-eZ ⟨j,k⟩,ft]
   . have e:2 ^ 4096<=2 ^ j:=Ba (by decide) (by omega);have g:a.toNat.testBit j=J:=AH (lt_of_lt_of_le a.isLt e);have f:(neg a).toNat.testBit j=J:=AH (lt_of_lt_of_le (neg a).isLt e);have d:z4.testBit j=J:=(by simp[tE,BW k]);rw[BX,d,g,f];rfl
 | false=>simp only[D2];exact vm i a b
def tB (free:Y):Nat->Nat->W->W
 | 0,_,ws=>ws
 | n+1,bits,ws=>
   E (sE free (L (D3 bits 10) 3) (lF ws (L bits 31)) (lF ws (L (D3 bits 5) 31))) fun z=>
   E (D3 bits 12) fun b'=>tB free n b' (ws++[z])
lemma xr (d:Y)(g:N->Nat)(F0:g P=0)(Fg:∀ op a b,g (if !d&&op==2 then neg a else V op a b)=sE d op (g a) (g b))(n c:Nat)(f:Z D):(i2 d n c f).map (fun w=>g w.1)=tB d n c (f.map fun w=>g w.1):=by
 have h (f:Z D) (i:Nat):(f.map fun w=>g w.1).getD i 0=g (f.getD i C).1:=by simp only[A1,B4];cases f[i]? with|none=>exact F0.symm| some v=>rfl
 induction n generalizing c f with
 | zero=>rfl
 | succ n j=>
   simp only[tB,i2,kw,R,lk];rw[j,h,h];have e:(tk d ((c>>>10)&&&3) (f.getD (c&&&31) C) (f.getD ((c>>>5)&&&31) C)).1 = if !d&&((c>>>10)&&&3)==2 then neg (f.getD (c&&&31) C).1
    else V ((c>>>10)&&&3) (f.getD (c&&&31) C).1 (f.getD ((c>>>5)&&&31) C).1:=by
    unfold tk;split<;>rfl
   rw[B5,map_singleton,e,Fg];rfl
abbrev ug:=Nat×Nat×Nat×(NN)
abbrev Qf:=Nat×Nat×Z gu×Z (W) × (Nat->ug)×(Nat->ug) × (Nat->Nat->Q (PP))×(Nat->Nat->Q (PP))×(Nat->Nat->Q (PP))
def Qf.m (g:Qf):Nat:=g.1
def Qf.cap (g:Qf):Nat:=g.2.1
def Qf.o (g:Qf):Z gu:=g.2.2.1
def Qf.a (g:Qf):Z (W):=g.2.2.2.1
def Qf.f (g:Qf):Nat->ug:=g.2.2.2.2.1
def Qf.t (g:Qf):Nat->ug:=g.2.2.2.2.2.1
def Qf.i (g:Qf):Nat->Nat->Q (PP):=g.2.2.2.2.2.2.1
def Qf.j (g:Qf):Nat->Nat->Q (PP):=g.2.2.2.2.2.2.2.1
def Qf.n (g:Qf):Nat->Nat->Q (PP):=g.2.2.2.2.2.2.2.2
def eF (a:Y)(g:Qf):Z D:=let b:=j9 a g.m;tY g.m (fun j=>(b.getD j (0,0)).1) (fun j=>(b.getD j (0,0)).2)
lemma gU (b:Y)(g:Qf):∀ a∈eF b g,ex (fq fun j=>(eH b g.m j).1) (fq fun j=>(eH b g.m j).2) a:=by unfold eF eH;exact xQ g.m _ _
def uf (g:Qf):N:=fE g.m
def iR (g:Qf)(u:Y)(k:Nat):ug:=if u then g.t k else g.f k
def gF (c:Y)(e:Z D)(g:Qf)(u:Y)(k i:Nat):Nat×Z D×Z D×LP×Nat:=let(_,f,n,j):=iR g u k;let b:=12*f;let w:=j i;let d:=w&&&((1<<<b)-1);let a:=i2 c f d e;let h:=w>>>(b+a.length);let(l,m):=vG n f (h&&&63) (h>>>6);(d,a,fw (w>>>b) a,l,m)
def vP (a:Y)(g:Qf)(u:Y)(k i:Nat):Nat×Z D×Z D×LP×Nat:=gF a (eF a g) g u k i
def eA (a:Y)(g:Qf)(u:Y)(k i:Nat):Z N:=(vP a g u k i).2.2.1.map G
def iO (m:Nat)(a:W):W:=(is m).map fun e=>(u3.getD (idxOf a e.1) P).toNat
def hP {c:Type}(m:Nat)(b:Z W)(k:Z W->c):c := List.rec (fun k=>k []) (fun a _ f k=>ip (fun e:Nat×N=>(u3.getD (idxOf a e.1) P).toNat) (is m) fun d=>f fun g=>k (d::g)) b k
lemma k4 {b:Type}(m:Nat)(autos:Z W)(k:Z W->b):hP m autos k=k (autos.map (iO m)):=by induction autos generalizing k with|nil=>rfl| cons a autos c=>change ip _ _ (fun d=>hP m autos fun e=>k (d::e))=_;rw[kg,c];rfl
def uS (b:Y)(g:Qf)(u:Y)(k i:Nat)(d:W):W := let(_,a,_,f):=iR g u k;let c:=DV 12 a;E (f i) fun e=>tq (D3 e c) (tB b a (L e (De (Dd 1 c) 1)) d)
lemma vx (c:Y)(g:Qf)(u:Y)(k i:Nat){d:W}(n:d.all eO=H):uS c g u k i (iO g.m d)=((eA c g u k i).map (ed (d.map eo).reverse)).map A8:=by
 let e:=(d.map eo).reverse;let zf (a:N):Nat:=(ed e a).toNat;have F0:zf P=0:=by change (ed e P).toNat=0;rw[ew,(gg _).1];simp[P]
 have Fg (op a b):zf (if !c&&op==2 then neg a else V op a b)=sE c op (zf a) (zf b):=by
  change (ed e _).toNat=sE c op (ed e a).toNat (ed e b).toNat;rw[vd];split;. rw[ew,iq,ew]
  . rw[ew,iY,ew,ew]
 have f:(eF c g).map (fun w=>zf w.1)=iO g.m d:=by simp only[eF,tY,iO,C4];apply Cy;rintro⟨j,a⟩ hm;obtain⟨o,rfl⟩:=ij hm;exact Az A8 (wY n o)
 unfold uS eA vP gF;rcases iR g u k with⟨p,h,q,l⟩;simp only[R,tM];rw[C4,C4,wQ,<-f,<-xr c zf F0 Fg];rfl
def kO:W->NN|[],a=>a|x::xs,a=>E (Dn a (jT x)) (kO xs)
def kS (a:W):Nat:=kO a 0
def eG (b:Y)(g:Qf)(u:Y)(k:Nat)(c:Z W)(a:PP):Q (W) := cond (Db (iR g u k).1 a.1) none (Option.rec none (fun d=>some (uS b g u k a.1 d)) (kX c a.2))
lemma gS (g:Qf)(u:Y)(k:Nat)(c:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H)(b:∀ idx < (iR g u k).1,if u then u1 J (uf g) k (eA J g u k idx).toFinset else u2 (uf g) k (eA J g u k idx).toFinset){a:PP}{l:W}(h:eG J g u k (g.a.map (iO g.m)) a=some l):∃ xs:Z N,l=xs.map A8/\(if u then u1 J (uf g) k xs.toFinset else u2 (uf g) k xs.toFinset):=by
 unfold eG at h;rw[kB] at h;cases i:Db (iR g u k).1 a.1 with
 | true=>simp only[i,D4] at h;contradiction
 | false=>
   have o:a.1<(iR g u k).1:=by by_contra q;exact Bool.noConfusion (i.symm.trans (Df.mpr (by omega)))
   simp only[i,D2] at h;cases j:g.a[a.2]? with
   | none=>simp[j] at h
   | some f=>
     simp only[B4,j,BU,Dl] at h;obtain⟨n,e⟩:=c f (Dh j);refine⟨(eA J g u k a.1).map (ed (f.map eo).reverse),h.symm.trans (vx J g u k a.1 n),?_⟩;have d:=b a.1 o;cases u;. exact y7 d f n e
     . exact jf d (f.map eo) e
lemma jo (g:Qf)(k:Nat)(c:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H)(b:∀ idx < (g.f k).1,u1 H (uf g) k (eA H g J k idx).toFinset){a:PP}{l:W}(h:eG H g J k (g.a.map (iO g.m)) a=some l):∃ xs:Z N,l=xs.map A8/\u1 H (uf g) k xs.toFinset:=by
 unfold eG at h;rw[kB] at h;cases i:Db (iR g J k).1 a.1 with
 | true=>simp only[i,D4] at h;contradiction
 | false=>
   have n:a.1<(g.f k).1:=by by_contra q;exact Bool.noConfusion (i.symm.trans (Df.mpr (by simp[iR];omega)))
   simp only[i,D2] at h;cases j:g.a[a.2]? with|none=>simp[j] at h | some e=>simp only[B4,j,BU,Dl] at h;have⟨o,d⟩:=c e (Dh j);exact⟨(eA H g J k a.1).map (ed (e.map eo).reverse),h.symm.trans (vx H g J k a.1 o),jf (b a.1 n) (e.map eo) d⟩
abbrev Z0:ug:=(0,0,0,fun _=>0)
abbrev N0:Nat->Q PP:=fun _=>none
abbrev wN (a:Z D):W:=a.map fun w:D=>w.1.toNat
abbrev pM (p:B9):W:=p.w.map (iy p.d.toNat)
def g7:Nat:=(1<<<320)-1
lemma lA:g7=AO.toNat:=by decide +kernel
lemma t2:one.toNat=z4:=by
 apply AF;intro k;rw[tE,AP];by_cases a:k<4096;. simp only[one,BitVec.testBit_toNat,BL,a,B6]
 . rw[BW a,AH (lt_of_lt_of_le one.isLt (Ba (by decide) (by omega)))]
lemma sO {w}(a b:BV w):M a.toNat b.toNat=(a==b):=by rw[E3,DE,Ar];exact Do
lemma lH {w}(a b:BV w):L a.toNat b.toNat=(a&&&b).toNat:=(DZ a b).symm
lemma sR {w}(a b:BV w):Dc a.toNat b.toNat=(a|||b).toNat:=(BitVec.toNat_or a b).symm
lemma sZ {w}(a b:BV w):D9 a.toNat b.toNat=(a^^^b).toNat:=(BitVec.toNat_xor a b).symm
lemma s7 (a:fU):D9 g7 a.toNat=(~~~a).toNat:=by rw[lA,sZ];exact Az A8 (by apply Af;intro j b;simp[b])
lemma t6 (a:N):D9 z4 a.toNat=(neg a).toNat:=by simpa[sE] using vd J 2 a P
lemma u0 (c:Nat)(a b:fU):zN c a.toNat b.toNat=(bv c a b).toNat:=by
 unfold zN;by_cases f:c=0;. subst f;exact lH a b
 by_cases e:c=1;. subst e;exact sR a b
 have k:M c 0=J:=Bp.mpr fun h=>f (Cl h);have i:M c 1=J:=Bp.mpr fun h=>e (Cl h);by_cases g:c=2;. subst g;change D9 _ (L _ _)=_;rw[lH,sZ];congr 1;apply Af;intro j d;simp only[bv,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,AX,AB,Aq,CE,AW,d,B6,AD];cases a.getLsbD j<;>cases b.getLsbD j<;>rfl
 have l:M c 2=J:=Bp.mpr fun h=>g (Cl h);rw[k,i,l];change D9 _ (L _ _)=_;rw[lH,sZ];congr 1;apply Af;intro j d;simp only[bv,f,e,g,AB,Aq,CE,AW,d,B6,AD];cases a.getLsbD j<;>cases b.getLsbD j<;>rfl
lemma t5 (a:t9):D9 a.1.toNat a.2.toNat=(eP J a).toNat:=sZ _ _
lemma si (a:t9):L a.1.toNat (D9 g7 a.2.toNat)=(eP H a).toNat:=by rw[s7,lH];rfl
lemma th (a:t9):L (D9 g7 a.1.toNat) a.2.toNat=(eP H (~~~a.1,~~~a.2)).toNat:=by rw[s7,lH];congr 1;apply Af;intro j b;simp[eP,b]
lemma lS (c:lw)(a:fU):L c.1.toNat (D9 g7 (L c.2.1.toNat a.toNat))=(i7 c a).toNat:=by rw[lH,s7,lH];rfl
lemma se (c:lw)(a b:fU):L c.1.toNat (D9 g7 (Dc (L c.2.1.toNat (Dc a.toNat b.toNat)) (L c.2.2.toNat (L a.toNat b.toNat))))=(sn c a b).toNat:=by rw[sR,lH,lH,lH,sR,s7,lH];rfl
def fX (m:Nat)(l:W):Y:=List.rec J (fun a _ b=>or (M m a) b) l
lemma hV (m:Nat)(l:W):fX m l=H↔m∈l:=by induction l with|nil=>simp[fX]| cons a l b=>change or (M m a) (fX m l)=H↔_;rw[Ai,b,DE,Ab]
def jI (l:W):Nat:=List.rec 0 (fun a _ b=>Dc b (Dd 1 (Dj a 509))) l
def fF (a m:Nat)(l:W):Y:=cond (M (L (D3 a (Dj m 509)) 1) 1) (fX m l) J
lemma gW {a m l}(h:fF a m l=H):fX m l=H:=by unfold fF at h;cases b:M (L (D3 a (Dj m 509)) 1) 1<;>simp_all
def lx (d m:Nat):Y:=or (M m 0) (M m d)
lemma s0 (d a:N):lx d.toNat (iy d.toNat a)=eI d a:=by rw[sF];have e:M (fJ d a).toNat 0=(fJ d a==P):=(by rw[<-sO];simp[P]);rw[lx,e,sO];rfl
def l4 (u:Y)(d:Nat)(a:W)(x:Nat):Y:=or (or (lx d x) (fX x a)) (and u (fX (D9 d x) a))
def gP (u:Y)(d bl:Nat)(a:W)(x:Nat):Y:=or (or (lx d x) (fF bl x a)) (and u (fF bl (D9 d x) a))
lemma tt {u d b a x}(h:gP u d b a x=H):l4 u d a x=H:=by simp only[gP,l4,Ai,X] at h ⊢;rcases h with (h|h)|⟨c,e⟩;exact D5 (D5 h);exact D5 (D6 (gW h));exact D6 ⟨c,gW e⟩
lemma ll (x d:N)(p:Z N):fX x.toNat (p.map (iy d.toNat))=(p.map (fJ d)).any (·==x):=by induction p with|nil=>rfl| cons a l b=>change or (M x.toNat (iy d.toNat a)) (fX x.toNat (l.map (iy d.toNat)))=_;rw[b,sF,sO,As,any_cons,Bool.beq_comm]
lemma lO (d a:N):D9 d.toNat (iy d.toNat a)=(fJ d (neg a)).toNat:=by rw[sF,sZ];congr 1;apply Af;intro j b;simp only[fJ,neg,Aq,CE,AW,b,B6,AD];cases d.getLsbD j<;>cases a.getLsbD j<;>rfl
lemma lh (u:Y)(d a:N)(p:Z N):l4 u d.toNat (p.map (iy d.toNat)) (iy d.toNat a)=em u d p a:=by rw[l4,s0,lO,sF,ll,ll];simp[em,eI]
lemma jX {u d bl p a}(h:gP u d.toNat bl (p.map (iy d.toNat)) (iy d.toNat a)=H):em u d p a=H:=(lh u d a p).symm.trans (tt h)
def s8 (p:Nat->Y)(l:W):Y:=List.rec H (fun x _ a=>and (p x) a) l
lemma tm (p:Nat->Y)(l:W):s8 p l=l.all p:=by induction l with|nil=>rfl| cons x l a=>change and (p x) (s8 p l)=_;rw[a];rfl
def sM (l:W):Y:=List.rec H (fun x a b=>and (not (fX x a)) b) l
lemma sK (l:W):sM l=H↔l.Nodup:=by induction l with|nil=>simp[sM]| cons x a b=>change and (not (fX x a)) (sM a)=H↔_;rw[X,D8,b,B7];simp[<-hV]
lemma sv (xs:W)(a:Nat):kO xs a=a+(xs.map jT).sum:=by induction xs generalizing a with|nil=>simp[kO]| cons x xs b=>simp[kO,R,b,AZ]
lemma sY (a:W):kS a=(a.map jT).sum:=(sv a 0).trans (C1 _)
lemma sp (f:D->Nat){b:Z D}{a:D}(d:a∈b)(c:Y):((gj b a c).map f).sum=(b.map f).sum-cond c 0 (f a):=by have e:=((Dg d).map f).sum_eq;rw[As,DB] at e;cases c<;>simp[gj]<;>omega
lemma sd (f:D->Nat){c:Z D}{a b:D}(h:a∈c)(g:b∈c)(i:a≠b)(e d:Y):((il c a b e d).map f).sum=(c.map f).sum-cond e 0 (f a)-cond d 0 (f b):=by have l:b∈c.erase a:=(DF (Du i)).mpr g;have k:=((Dg h).map f).sum_eq;rw[As,DB] at k;have j:=((Dg g).map f).sum_eq;rw[As,DB] at j;have A:=((Dg l).map f).sum_eq;rw[As,DB] at A;cases e<;>cases d<;>simp[il,gj]<;>omega
lemma lN (p:D->Y){b:Z D}{a:D}(d:a∈b)(c:Y):b.countP p-cond c 0 (p a).toNat=(gj b a c).countP p:=by have e:=(Dg d).countP_eq p;rw[BR] at e;cases c<;>cases f:p a<;>simp[gj,f] at e ⊢<;>omega
abbrev kC:=Nat×W×Nat
def fN (m:Nat)(a:gu):kC:=let d:=(g5 a.1 a.2.1).toNat;(d,(eu (g4 m a)).map (iy d),a.2.2.2.2)
def lg {b:Type}(m:Nat)(l:Z gu)(k:Z kC->b):b:= List.rec (fun k=>k []) (fun a _ c k=>E (g5 a.1 a.2.1).toNat fun d=>ip (iy d) (eu (g4 m a)) fun e=>E a.2.2.2.2 fun g=>c fun f=>k ((d,e,g)::f)) l k
lemma lB {a:Type}(m:Nat)(l:Z gu)(k:Z kC->a):lg m l k=k (l.map (fN m)):=by induction l generalizing k with|nil=>rfl| cons g l b=>change E _ (fun d=>ip (iy d) _ fun c=>E _ fun f=>lg m l fun e=>k ((d,c,f)::e))=_;rw[R,kg,R,b];rfl
lemma lK (d:N)(a:Z D)(i:Nat):L ((wN a).getD i 0) d.toNat=iy d.toNat (a.getD i C).1:=by simp only[wN,A1,B4];cases a[i]? with|none=>simp[C,P,iy]| some v=>rfl
lemma sb (a:Z D)(i:Nat):(wN a).getD i 0=(a.getD i C).1.toNat:=by simp only[wN,A1,B4];cases a[i]? with|none=>simp[C,P]| some v=>rfl
def i9 (g:Y)(d:Nat)(h:Y)(b:Nat)(f:W)(c a:Nat)(e:W):Nat->Q (Y×Nat×W)
 | 0=>some (h,b,f)
 | n+1=>
   cond (M a 0) (some (h,b,f))
    (cond (M (L a 1) 0) (i9 g d h b f (D3 c 12) (D3 a 1) e n) (let op:=L (D3 c 10) 3
     E (L (lF e (L c 31)) d) fun x=>
     cond (and (not g) (M op 2))
      (cond (and (not h) (l4 J d f x)) (E (D9 d x) fun i=>i9 g d H b (i::f) (D3 c 12) (D3 a 1) e n) none)
      (E (L (lF e (L (D3 c 5) 31)) d) fun y=>cond (and (or (Db (Nat.succ op) 2) (and g (Db (Nat.succ op) 4))) (and (l4 g d f x) (l4 g d f y))) (E (zN op x y) fun z=>i9 g d h (Nat.succ b) (z::f) (D3 c 12) (D3 a 1) e n) none)))
lemma sB {o T d v j i n pu k}{r:Z D}(e:Nat)(c:Z N)(q:gD H o T (d,v,e,c))(h:i9 H d.toNat pu e (c.map (iy d.toNat)) j i (wN r) n=some k) : ∃ c',gD H o T (d,v,k.2.1,c')/\k.2.2=c'.map (iy d.toNat):=by
 induction n generalizing j i c e with
 | zero=>simp only[i9,Dl] at h;subst h;exact⟨c,q,rfl⟩
 | succ n y=>
   simp only[i9,Dw,DM,D2] at h;cases w:M i 0 with
   | true=>simp only[w,D4,Dl] at h;subst h;exact⟨c,q,rfl⟩
   | false=>
     simp only[w,D2] at h;cases z:M (L i 1) 0 with
     | true=>simp only[z,D4] at h;exact y e c q h
     | false=>
       simp only[z,D2,R,lk,lK,lh] at h;set p:=L (D3 j 10) 3;set a:=(r.getD (L j 31) C).1;set b:=(r.getD (L (D3 j 5) 31) C).1;cases m:and (or (Db (Nat.succ p) 2) (and H (Db (Nat.succ p) 4))) (and (em H d c a) (em H d c b)) with
       | false=>simp only[m,D2] at h;contradiction
       | true=>simp only[m,D4,tK] at h;simp only[X,Ai,AD,Df,DJ] at m;have u:jp H d c (p,a,b)=H:=(by simp only[jp,tg,m.2.1,m.2.2,Cb,AD,Ai,A6];rcases m.1 with h1|h1;exact D5 (by omega);exact D6 (by omega));have⟨f,l,x,g,nc,lo,s,t,_⟩:=q;obtain⟨x',s',t'⟩:=vn g s t (p,a,b) u;exact y (e+1) (eM (p,a,b)::c) ⟨f,l,x',g,nc,lo,s',t',trivial⟩ h
lemma sq {s T d lb l k n p}{v:Z D}(u:Y)(i:Nat)(c:Z N)(t:fR s T (u,(d,lb,i,c)))(h:i9 J d.toNat u i (c.map (iy d.toNat)) l k (wN v) n=some p) : ∃ c',fR s T (p.1,(d,lb,p.2.1,c'))/\p.2.2=c'.map (iy d.toNat):=by
 induction n generalizing l k u i c with
 | zero=>simp only[i9,Dl] at h;subst h;exact⟨c,t,rfl⟩
 | succ n ih=>
   simp only[i9,Dy,AD,DM,DC] at h;cases h0:M k 0 with
   | true=>simp only[h0,D4,Dl] at h;subst h;exact⟨c,t,rfl⟩
   | false=>
     simp only[h0,D2] at h;cases hm:M (L k 1) 0 with
     | true=>simp only[hm,D4] at h;exact ih u i c t h
     | false=>
       simp only[hm,D2,R,lk,lK,lh] at h;set q:=L (D3 l 10) 3;set a:=(v.getD (L l 31) C).1;cases h2:M q 2 with
       | true=>
         simp only[h2,D4] at h;cases m:and (not u) (em J d c a) with
         | false=>simp only[m,D2] at h;contradiction
         | true=>
           simp only[m,D4,lO] at h;simp only[X,D8] at m;obtain⟨rfl,ha⟩:=m;obtain⟨f,j,bg,g,nc,lo,z,o⟩:=t;have o':f6 J f (jh (e4 f (A a))::bg) (neg a::c):=fun w r=>by rcases Ab.mp r with rfl|r;rw[tf];exact D5 BJ;exact eW _ (o w r)
           rw[show (fJ d (neg a)).toNat=iy d.toNat (neg a) from (sF d (neg a)).symm] at h;exact ih H i (neg a::c) ⟨f,j,_,g,nc,lo,R1.unary z (ee g o ha),o'⟩ h
       | false=>
         simp only[h2,D2,lk,lK,lh] at h;set b:=(v.getD (L (D3 l 5) 31) C).1;cases m:and (Db (Nat.succ q) 2) (and (em J d c a) (em J d c b)) with
         | false=>simp only[m,D2] at h;contradiction
         | true=>
           simp only[m,D4,tK] at h;simp only[X,Df,DJ] at m;obtain⟨f,j,bg,g,nc,lo,z,o⟩:=t;obtain⟨q',x,y,e,hx,hy,_,_⟩:=h8 (u:=J) (D5 (by omega:q<2)) (ee g o m.2.1) (ee g o m.2.2);have o':f6 J f (ez q' x y::bg) (V q a b::c):=fun w r=>by rcases Ab.mp r with rfl|r;rw[tw,gm,e];exact D5 BJ;exact eW _ (o w r)
           exact ih u (i+1) (V q a b::c) ⟨f,j,_,g,nc,lo,R1.two q' z hx hy,o'⟩ h
def lz {h:Type}(u:Y)(d j:Nat)(i g:W):Nat->Nat->Nat->Nat->Nat->(Nat->Nat->Nat->Nat->h)->h:= List.rec (fun _ c v b a k=>k c v b a) (fun w _ l bit c v b a k=>E (L w d) fun m=>j4 (lx d m) fun e=>j4 (or e (or (fF j m i) (and u (fF j (D9 d m) i)))) fun f=>E (Dd bit 1) fun bit'=>E (cond e (Nat.succ c) c) fun c'=>E (cond f v (Nat.succ v)) fun v'=>E (cond f (Dc b bit) b) fun b'=>E (cond e (Dc a bit) a) fun a'=>cond (Db 3 v') (k c' 3 b' a') (l bit' c' v' b' a' k)) g
lemma kJ {m s:Nat}(b:Y)(d:m<1<<<s) : cond b (Dc m (1<<<s)) m<1<<<(s+1)/\(cond b (Dc m (1<<<s)) m).testBit s=b/\∀ t < s,(cond b (Dc m (1<<<s)) m).testBit t=m.testBit t:=by
 have a:1<<<s<1<<<(s+1):=(by rw[Ag,Ag];simp[DL]);have c:m<1<<<(s+1):=lt_trans d a;have e:1<<<(s+1)=2^(s+1):=(by rw[Ag,one_mul]);cases b with
 | false=>refine⟨c,AH (by rw[Ag,one_mul] at d;exact d),fun _ _=>rfl⟩
 | true=>
   refine⟨by change m|||(1<<<s)<1<<<(s+1);rw[e] at c ⊢;exact C9 c (by simpa[Ag] using a),?_,?_⟩
   . change (m|||(1<<<s)).testBit s=H;rw[Ay,Ag,one_mul,Cx];simp
   . intro t f;change (m|||(1<<<s)).testBit t=_;rw[Ay,Ag,one_mul,Cx,BW (by omega:¬s=t)];simp
lemma sG {bt:Type}(u:Y)(d b:Nat)(a wsN:W)(s c v av cM:Nat)(g:av<1<<<s)(hc:cM<1<<<s)(k:Nat->Nat->Nat->Nat->bt) : ∃ c' v' av' cM',lz u d b a wsN (1<<<s) c v av cM k=k c' v' av' cM'/\(3<=v'\/(c'=c+wsN.countP (fun w=>lx d (L w d))/\v'=v+(wsN.map fun w=>cond (gP u d b a (L w d)) 0 1).sum/\(∀ j < wsN.length,av'.testBit (s+j)=gP u d b a (L (wsN.getD j 0) d))/\(∀ j < wsN.length,cM'.testBit (s+j)=lx d (L (wsN.getD j 0) d))/\(∀ t < s,av'.testBit t=av.testBit t)/\(∀ t < s,cM'.testBit t=cM.testBit t))):=by
 induction wsN generalizing s c v av cM with
 | nil=>exact⟨c,v,av,cM,rfl,D6 ⟨by simp,by simp,by simp,by simp,fun _ _=>rfl,fun _ _=>rfl⟩⟩
 | cons w wsN ih=>
   have i:Dd (1<<<s) 1=1<<<(s+1):=(by change (1<<<s)<<<1=1<<<(s+1);rw[Ag,Ag,Ag];simp[DL]);have h:or (lx d (L w d)) (or (fF b (L w d) a) (and u (fF b (D9 d (L w d)) a)))=gP u d b a (L w d):=by unfold gP;cases lx d (L w d)<;>cases fF b (L w d) a<;>rfl
   have q:=kJ (gP u d b a (L w d)) g;have y:=kJ (lx d (L w d)) hc;unfold lz;dsimp only;rw[R,kh,h,kh,R,R,R,R,R,i];cases h3:Db 3 (cond (gP u d b a (L w d)) v (Nat.succ v)) with
   | true=>exact⟨_,3,_,_,rfl,D5 (by omega)⟩
   | false=>
     rw[D2];obtain⟨c',v',av',cM',z,hr⟩:=ih (s+1) _ _ _ _ q.1 y.1;rcases hr with m|⟨p,x,o,r,e,f⟩;. exact⟨c',v',av',cM',z,D5 m⟩
     . exact⟨c',v',av',cM',z,D6 ⟨by rw[p,BR];cases lx d (L w d)<;>simp<;>omega,by rw[x,As,DB];cases gP u d b a (L w d)<;>simp<;>omega,fun j n=>by cases j with|zero=>rw[Dz,e s (by omega),DU];exact q.2.1| succ j=>rw[show s+(j+1)=(s+1)+j by omega,o j (by simp at n;omega)];rfl,
       fun j n=>by cases j with|zero=>rw[Dz,f s (by omega),DU];exact y.2.1| succ j=>rw[show s+(j+1)=(s+1)+j by omega,r j (by simp at n;omega)];rfl,
       fun t l=>(e t (by omega)).trans (q.2.2 t l),fun t l=>(f t (by omega)).trans (y.2.2 t l)⟩⟩
lemma lc (m i:Nat):M (L m (1<<<i)) 0=not (m.testBit i):=by
 have b:(m&&&(1<<<i)).testBit i=m.testBit i:=by rw[Ad,Ag,one_mul,Cx];simp
 cases h:m.testBit i with
 | true=>rw[Dw,Bp];intro c;have d:m&&&(1<<<i)=0:=Cl c;have:=Az (fun v=>v.testBit i) d;rw[b,h] at this;simp at this
 | false=>
   rw[Dy,DE];apply AF;intro j;rw[DN];change (m&&&(1<<<i)).testBit j=J;rw[Ad,Ag,one_mul,Cx];by_cases a:i=j;. subst a;simp[h]
   . simp[a]
lemma lj (m i:Nat):not (M (L m (1<<<i)) 0)=m.testBit i:=by rw[lc,DW]
lemma kt (m i:Nat):cond (M (L m (1<<<i)) 0) 0 1=(m.testBit i).toNat:=by rw[lc];cases m.testBit i<;>rfl
abbrev lu:=Nat×Nat×Nat×Nat×Nat×Nat×W
abbrev iz:=Y×lu
def s9 {g:Type}(l:Z iz)(k:Z lu->g):g:= List.rec (fun k=>k []) (fun j _ h k=>let(_,(d,a,v,f,b,e,c)):=j;E d fun d=>E a fun a=>E v fun v=>E f fun f=>E b fun b=>E e fun e=>f2 c fun c=>h fun i=>k ((d,a,v,f,b,e,c)::i)) l k
lemma sa {g:Type}(l:Z iz)(k:Z lu->g):s9 l k=k (l.map Prod.snd):=by
 induction l generalizing k with|nil=>rfl| cons j l h=>
  rcases j with⟨m,d,a,v,f,b,e,c⟩;change E d (fun d=>E a fun a=>E v fun v=>E f fun f=>E b fun b=>E e fun e=>f2 c fun c=>s9 l fun i=>k ((d,a,v,f,b,e,c)::i))=_;simp only[R,gf,h];rfl
def k0 {j:Type}(l:Z iz)(k:Z iz->Z lu->j):j:= List.rec (fun k=>k [] []) (fun n _ m k=>let(c,(d,b,v,h,e,g,f)):=n;j4 c fun c=>E d fun d=>E b fun b=>E v fun v=>E h fun h=>E e fun e=>E g fun g=>f2 f fun f=>let q:=(d,b,v,h,e,g,f);m fun i a=>k ((c,q)::i) (cond c a (q::a))) l k
lemma l5 {j:Type}(l:Z iz)(k:Z iz->Z lu->j) : k0 l k=k l (l.filterMap fun qp=>if qp.1 then none else some qp.2):=by
 induction l generalizing k with|nil=>rfl| cons qp l m=>
  rcases qp with⟨c,d,a,v,h,e,g,f⟩;change j4 c (fun c=>E d fun d=>E a fun a=>E v fun v=>E h fun h=>E e fun e=>E g fun g=>f2 f fun f=>k0 l fun i b=>k ((c,d,a,v,h,e,g,f)::i) (cond c b ((d,a,v,h,e,g,f)::b)))=_;simp only[kh,R,gf,m];cases c<;>rfl
def lG (u:Y)(a:Nat)(c:Z D)(p:B9)(q:lu):Prop:= let(d,f,v,i,h,g,e):=q;d=p.d.toNat/\a+p.p<=p.b+c.countP (fun w:D=>eI p.d w.1)/\f=p.b+c.countP (fun w:D=>eI p.d w.1)-(a+p.p)/\e=pM p/\v=(c.map fun w:D=>cond (gP u p.d.toNat g e (iy p.d.toNat w.1)) 0 1).sum/\(∀ j < c.length,i.testBit j=gP u p.d.toNat g e (iy p.d.toNat (c.getD j C).1))/\(∀ j < c.length,h.testBit j=eI p.d (c.getD j C).1)
def lm (u k:Y)(b d j a:Nat)(f g:W):Q iz:= E (jI g) fun i=>lz u d i g f 1 0 0 0 0 fun c v m l=>cond (Db 3 v) none (E (Dn j c) fun e=>E (Dn b a) fun h=>cond (not (Db h e)) none (some (k,(d,De e h,v,m,l,i,g))))
lemma lE {u t:Y}{a:Nat}{g:Z D}{p:B9}{k:iz}(h:lm u t a p.d.toNat p.b p.p (wN g) (pM p)=some k) : k.1=t/\lG u a g p k.2:=by
 unfold lm at h;simp only[R] at h;rw[show (1:Nat)=1<<<0 from rfl] at h;obtain⟨c',v',av',z',s,x⟩:=sG u p.d.toNat (jI (pM p)) (pM p) (wN g) 0 0 0 0 0 (by decide) (by decide) _;rw[s] at h;cases n:Db 3 v' with
 | true=>simp only[n,D4] at h;contradiction
 | false=>
   have i:¬(3<=v'):=fun y=>Bool.noConfusion (n.symm.trans (Df.mpr y));have⟨o,r,m,q,_,_⟩:=x.resolve_left i;simp only[n,D2] at h;cases e:Db (Dn a p.p) (Dn p.b c') with
   | false=>simp only[e,Dy,D4] at h;contradiction
   | true=>
     simp only[e,Dw,D2,Dl] at h;subst h;have f:c'=g.countP (fun w:D=>eI p.d w.1):=by rw[o,C1,wN,E1];apply countP_congr;intro w _;exact E3.mp (s0 p.d w.1)
     have e':a+p.p<=p.b+c':=by have:=Df.mp e;simpa only[DQ] using this
     refine⟨rfl,rfl,f▸e',by rw[f];rfl,rfl,by rw[r,C1,wN,C4];rfl,fun j l=>by have:=m j (by simpa[wN] using l);rwa[C1,sb] at this,
      fun j l=>by have:=q j (by simpa[wN] using l);rwa[C1,sb,show L (g.getD j C).1.toNat p.d.toNat=iy p.d.toNat (g.getD j C).1 from rfl,s0] at this⟩
def bQ (h:Y)(e:Nat)(f:W)(a:Z kC)(i b:Nat)(g:W)(c:LP):Z iz:= c.filterMap fun(ei,pmask)=>Option.rec none (fun(d,pm0,lb)=>Option.rec none (fun(pu,paid,pm)=>lm h pu e d lb paid f pm) (i9 h d h 0 pm0 i pmask g b)) (kX a ei)
lemma ly {f:Y}{b:Nat}{g:Qf}{d a:Nat}{h k:Z D}{c:LP}{l:iz}(n:l∈bQ f b (wN k) (g.o.map (fN g.m)) d a (wN h) c) : ∃ ci∈g.o,∃ pmask pu paid pm,i9 f (g5 ci.1 ci.2.1).toNat f 0 ((eu (g4 g.m ci)).map (iy (g5 ci.1 ci.2.1).toNat)) d pmask (wN h) a=some (pu,paid,pm)/\lm f pu b (g5 ci.1 ci.2.1).toNat ci.2.2.2.2 paid (wN k) pm=some l:=by
 obtain⟨⟨ei,pmask⟩,_,he⟩:=Bw.mp n;dsimp only at he;rw[kB] at he;simp only[B4] at he;cases e:g.o[ei]? with
 | none=>simp[e] at he
 | some ci=>
   simp only[e,BU,fN] at he;cases j:i9 f (g5 ci.1 ci.2.1).toNat f 0 ((eu (g4 g.m ci)).map (iy (g5 ci.1 ci.2.1).toNat)) d pmask (wN h) a with
   | none=>rw[j] at he;contradiction
   | some i=>rcases i with⟨pu,paid,pm⟩;rw[j] at he;exact⟨ci,Dh e,pmask,pu,paid,pm,j,he⟩
lemma uU {b:Nat}{g:Qf}{j e:Nat}{s r:Z D}{h:LP}(i:∀ ci∈g.o,t3 H (eu (g4 g.m ci)) (uf g) (g5 ci.1 ci.2.1) ci.2.2.2.2){q:lu}(t:q∈(bQ H b (wN r) (g.o.map (fN g.m)) j e (wN s) h).map Prod.snd) : ∃ p:B9,gD H (h7 g.m) (uf g) p/\lG H b r p q:=by obtain⟨qp,k,rfl⟩:=Aj.mp t;obtain⟨ci,l,_,pu,d,pm,z,u⟩:=ly k;obtain⟨f,a,v,w,x,y⟩:=i ci l;obtain⟨c',n,rfl⟩:=sB 0 (eu (g4 g.m ci)) ⟨f,a,a.map A,v,x,y,Rc.start,w,trivial⟩ z;exact⟨(g5 ci.1 ci.2.1,ci.2.2.2.2,d,c'),n,(lE (p:=(g5 ci.1 ci.2.1,ci.2.2.2.2,d,c')) u).2⟩
lemma sx {b:Nat}{g:Qf}{k c:Nat}{r q:Z D}{d:LP}(e:∀ ci∈g.o,sN (eu (g4 g.m ci)) (uf g) (g5 ci.1 ci.2.1) ci.2.2.2.2){j:iz}(hq:j∈bQ J b (wN q) (g.o.map (fN g.m)) k c (wN r) d) : ∃ p:B9,fR (h7 g.m) (uf g) (j.1,p)/\lG J b q p j.2:=by obtain⟨ci,n,_,pu,i,z,u,x⟩:=ly hq;obtain⟨f,a,y,s,v,t⟩:=e ci n;obtain⟨h',l,rfl⟩:=sq J 0 (eu (g4 g.m ci)) ⟨f,a,a.map A,y,v,t,R1.start,s⟩ u;obtain⟨w,hq'⟩:=lE (p:=(g5 ci.1 ci.2.1,ci.2.2.2.2,i,h')) x;rw[w];exact⟨_,l,hq'⟩
lemma kL {u:Y}{p:B9}{bl:Nat}{l:Z D}(b:(l.map fun w:D=>cond (gP u p.d.toNat bl (pM p) (iy p.d.toNat w.1)) 0 1).sum=0) : (l.map G).all (em u p.d p.w)=H:= Ae.mpr fun w a=>by
 obtain⟨w',a',rfl⟩:=Aj.mp a;have hv:=sum_eq_zero_iff.mp b _ (Qm a')
 cases hnb:gP u p.d.toNat bl (pM p) (iy p.d.toNat w'.1);simp[hnb] at hv;exact jX hnb
lemma sy {u d p z}(h:eI d z=H):em u d p z=H:=by unfold em;change (((eI d z||_)||_)=H);rw[h];rfl
def jx (l:Y)(s:lu)(a b z:Nat)(i h:Y):Y:= let(d,c,v,k,j,n,m):=s;let e:=not (M (L k a) 0);let f:=not (M (L k b) 0);cond (M v (Dn (cond i 0 (cond e 0 1)) (cond h 0 (cond f 0 1)))) (let g:=Dn (cond i 0 (cond (M (L j a) 0) 0 1)) (cond h 0 (cond (M (L j b) 0) 0 1));cond (Db (Nat.succ g) c) (or (and (Db (Dn g 2) c) (and e f)) (E (L z d) fun o=>gP l d n m o)) (cond (Db g c) (lx d (L z d)) J)) J
lemma la {m k c p q i j op g n}(hq:lG m k c p q)(hi:i<c.length)(hj:j<c.length)(hf:i≠j)(nd:(c.map G).Nodup)(h:jx m q (1<<<i) (1<<<j) (V op (c.getD i C).1 (c.getD j C).1).toNat g n=H) : let a:=c.getD i C;let b:=c.getD j C;let z:=V op a.1 b.1;let rest:=(il c a b g n).map G
 rest.all (em m p.d p.w)=H/\
 k+p.p+(!em m p.d p.w z).toNat<p.b+(rest.countP (eI p.d)+if eI p.d z=H then 1 else 0)/\
 (em m p.d p.w z=H\/(em m p.d p.w a.1=H/\em m p.d p.w b.1=H)):=by
 rcases q with⟨d,ht,v,av,cM,bl,pm⟩;obtain⟨rfl,hy,rfl,rfl,rfl,s,h4⟩:=hq;simp only[jx,lj,kt,s i hi,s j hj,h4 i hi,h4 j hj,R] at h;set a:=c.getD i C;set b:=c.getD j C;set z:=V op a.1 b.1;set rest:=il c a b g n;have ha:a∈c:=(by simp[a,Ah hi]);have y:b∈c:=(by simp[b,Ah hj]);have h3:a≠b:=fun eq=>hf ((DG nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp (by simpa[a,b,A1,Ah hi,Ah hj] using Az G eq))
 set e:D->Nat:=fun w=>cond (gP m p.d.toNat bl (pM p) (iy p.d.toNat w.1)) 0 1;cases hu:M (c.map e).sum (Dn (cond g 0 (e a)) (cond n 0 (e b))) with
 | false=>rw[hu] at h;cases h
 | true=>
   have h5:=sd e ha y h3 g n;have hu':=Cl hu;have f:=kL (u:=m) (p:=p) (bl:=bl) (l:=rest) (by change (rest.map e).sum=0;rw[h5];change (c.map e).sum=cond g 0 (e a)+cond n 0 (e b) at hu';omega);have hv:cond g 0 (eI p.d a.1).toNat<=c.countP (fun w:D=>eI p.d w.1):=by cases g;cases hx:eI p.d a.1;simp;exact countP_pos_iff.mpr ⟨a,ha,hx⟩;simp
   have x:=lN (fun w:D=>eI p.d w.1) ha g;have y':b∈gj c a g:=by cases g;exact(DF (Du h3)).mpr y;exact y
   have hz:cond n 0 (eI p.d b.1).toNat<=(gj c a g).countP (fun w:D=>eI p.d w.1):=by cases n;cases hx:eI p.d b.1;simp;exact countP_pos_iff.mpr ⟨b,y',hx⟩;simp
   have t:=lN (fun w:D=>eI p.d w.1) y' n;rw[hu,D4] at h;set rc:=(rest.map G).countP (eI p.d);set dc:=Dn (cond g 0 (eI p.d a.1).toNat) (cond n 0 (eI p.d b.1).toNat);have hr:rc+dc=c.countP (fun w:D=>eI p.d w.1):=by have hs:rc=(gj (gj c a g) b n).countP (fun w:D=>eI p.d w.1):=(by simp only[rc,rest,il,E1];rfl);simp only[dc,DQ];omega
   have hn:L z.toNat p.d.toNat=iy p.d.toNat z:=rfl;rw[hn] at h;have r (hbd:k+p.p+(!em m p.d p.w z).toNat<p.b+(rc+if eI p.d z=H then 1 else 0)):k+p.p+(!em m p.d p.w z).toNat<p.b+((rest.map G).countP (eI p.d)+if eI p.d z=H then 1 else 0):=hbd;cases x:Db (Nat.succ dc) (p.b+c.countP (fun w:D=>eI p.d w.1)-(k+p.p)) with
   | false=>simp only[x,D2] at h;cases t:Db dc (p.b+c.countP (fun w:D=>eI p.d w.1)-(k+p.p)) with|false=>simp only[t,D2] at h;contradiction | true=>simp only[t,D4,s0] at h;have t':=Df.mp t;have o:=sy (u:=m) (p:=p.w) h;exact⟨f,r (by simp only[h,o,Dw,DP,AX];omega),D5 o⟩
   | true=>
     simp only[x,D4,Ai,X,Df,DQ] at h;have x':=Df.mp x;simp only[DJ] at x';rcases h with⟨t',hm,hg⟩|hk;. have:=Bool.toNat_le (!em m p.d p.w z);exact⟨f,r (by omega),D6 ⟨jX hm,jX hg⟩⟩
     . have o:=jX hk;exact⟨f,r (by simp only[o,Dw,DP];omega),D5 o⟩
def kE (f:lu->Y)(a:Z lu):Y:=List.rec J (fun s _ b=>or (f s) b) a
lemma sk {f qs}:kE f qs=H↔∃ s∈qs,f s=H:=by induction qs with|nil=>simp[kE]| cons s qs a=>change or (f s) (kE f qs)=H↔_;rw[Ai,a];simp
def kl (f:iz->Y)(a:Z iz):Y:=List.rec J (fun s _ b=>or (f s) b) a
lemma sH {f qs}:kl f qs=H↔∃ s∈qs,f s=H:=by induction qs with|nil=>simp[kl]| cons s qs a=>change or (f s) (kl f qs)=H↔_;rw[Ai,a];simp
lemma ty {k a p q i j b l g}(n:lG H k a p q)(o:i<a.length)(m:j<a.length)(d:i≠j)(r:(a.map G).Nodup)(c:b<4)(h:jx H q (1<<<i) (1<<<j) (V b (a.getD i C).1 (a.getD j C).1).toNat l g=H) : gk H p k ((il a (a.getD i C) (a.getD j C) l g).map G) (b,(a.getD i C).1,(a.getD j C).1)=H:=by
 obtain⟨t,f,e⟩:=la n o m d r h;simp only[gk,eM,X,A6,BR,t,Cb];refine⟨f,?_⟩;rw[Ai,DW];rcases e with s|⟨u,v⟩;. exact D5 s
 . exact D6 (by simp only[jp,tg,u,v,Ai,A6,AD,Cb];exact D6 c)
lemma lT {u t k a p q i j c s r}(l:u=H\/t=J)(x:lG J k a p q)(y:i<a.length)(v:j<a.length)(m:i≠j)(z:(a.map G).Nodup)(g:c<2)(h:jx J q (1<<<i) (1<<<j) (V c (a.getD i C).1 (a.getD j C).1).toNat s r=H) : sT (t,p) u k ((il a (a.getD i C) (a.getD j C) s r).map G) (c,(a.getD i C).1,(a.getD j C).1)=H:=by
 have⟨hr,f,n⟩:=la x y v m z h;have b:(c==2)=J:=Bp.mpr fun e=>by have:=Ar.mp e;omega
 have o:eb (c,(a.getD i C).1,(a.getD j C).1)=V c (a.getD i C).1 (a.getD j C).1:=(by simp[eb,b]);simp only[sT,o,b,hr,DC,Dy,Cb,X,A6,BR];refine⟨⟨by rcases l with rfl|rfl<;>simp,by cases he:em J p.d p.w (V c (a.getD i C).1 (a.getD j C).1)<;>simp only[he,Dw,Dy,DP,Bool.toNat_true,AX,AB,Ak] at f ⊢<;>exact f⟩,by rw[Ai];rcases n with hz|⟨ha,hb⟩;exact D5 hz;exact D6 (by simp only[Ak,AB,X,A6];exact⟨⟨g,ha⟩,hb⟩)⟩
def kz (f:iz)(a z:Nat)(e:Y):Y:= let(pu,(d,slk,v,av,cM,bl,pm)):=f;cond (and e (not (M v 0))) J (let b:=not (M (L av a) 0);cond (M v (cond e 0 (cond b 0 1))) (let c:=cond e (cond (M (L cM a) 0) 0 1) 0;cond (Db 2 (Dn slk c)) (cond (and (not pu) b) H (E (L z d) fun g=>gP J d bl pm g)) J) J)
lemma td (d a:N):eI d (neg a)=eI d a:=by
 have f (j:Nat):(P).getLsbD j=J:=BitVec.getLsbD_zero;have e:∀ x:N,fJ d (neg x)=P↔fJ d x=d:=fun x=>by
  constructor<;>(intro h;apply Af;intro j b;have:=Az (fun v:N=>v.getLsbD j) h;simp only[fJ,neg,Aq,AW,b,B6,AD,f] at this ⊢;cases g:d.getLsbD j<;>cases i:x.getLsbD j<;>simp only[g,i,Dw,Dy,AD,DM] at this ⊢<;>first|rfl|cases this)
 have c:neg (neg a)=a:=Af fun j b=>by simp[neg,b]
 rw[eI,eI,E3,Ai,Ai,Ar,Ar,Ar,Ar,e a,show (fJ d (neg a)=d↔fJ d a=P) by simpa[c] using (e (neg a)).symm,or_comm]
lemma lQ {k c p z i e}(hq:lG J (k-1) c p z.2)(hi:i<c.length)(h:kz z (1<<<i) (neg (c.getD i C).1).toNat e=H) : sT (z.1,p) H k ((gj c (c.getD i C) e).map G) (2,(c.getD i C).1,P)=H:=by
 rcases z with⟨pu,d,hc,v,av,cM,bl,pm⟩;obtain⟨rfl,hf,rfl,rfl,rfl,y,h2⟩:=hq;simp only[kz,lj,kt,y i hi,h2 i hi,R] at h;set a:=c.getD i C;have ha:a∈c:=(by simp[a,Ah hi]);set f:D->Nat:=fun w=>cond (gP J p.d.toNat bl (pM p) (iy p.d.toNat w.1)) 0 1;cases m:and e (not (M (c.map f).sum 0)) with
 | true=>rw[m] at h;cases h
 | false=>
   rw[m,D2] at h;cases r:M (c.map f).sum (cond e 0 (f a)) with
   | false=>rw[r] at h;cases h
   | true=>
     have x:=sp f ha e;have r':=Cl r;have o:=kL (u:=J) (p:=p) (bl:=bl) (l:=gj c a e) (by change ((gj c a e).map f).sum=0;change (c.map f).sum=cond e 0 (f a) at r';cases e<;>simp only[D4,D2] at x r' ⊢<;>omega);have q:c.countP (fun w:D=>eI p.d w.1)-cond e 0 (eI p.d a.1).toNat=((gj c a e).map G).countP (eI p.d):=(by rw[E1];exact lN (fun w:D=>eI p.d w.1) ha e);have s:(eI p.d a.1).toNat<=c.countP (fun w:D=>eI p.d w.1):=by cases hx:eI p.d a.1;simp;exact countP_pos_iff.mpr ⟨a,ha,hx⟩
     rw[r,D4] at h;cases g:Db 2 (Dn (p.b+c.countP (fun w:D=>eI p.d w.1)-(k-1+p.p)) (cond e (eI p.d a.1).toNat 0)) with
     | false=>rw[g] at h;cases h
     | true=>
       rw[g,D4] at h;have g':=Df.mp g;simp only[DQ] at g';have h3:eb (2,a.1,P)=neg a.1:=(by simp[eb]);simp only[sT,h3,beq_self_eq_true,Ef,Dw,DC,AX,o,Cb,X,A6,BR,td];have n:k+p.p+0<p.b+(((gj c a e).map G).countP (eI p.d)+if eI p.d a.1=H then 1 else 0):=by rw[<-q];cases e<;>cases he:eI p.d a.1<;>simp only[he,D4,D2,Bool.toNat_true,DP,AX,AB] at g' s ⊢<;>omega
       cases j:and (not pu) (gP J p.d.toNat bl (pM p) (iy p.d.toNat a.1)) with|true=>simp only[X,D8] at j;exact⟨⟨by simp[j.1],n⟩,by simp[jX j.2]⟩ | false=>simp only[j,D2] at h;have t:=jX (show gP J p.d.toNat bl (pM p) (iy p.d.toNat (neg a.1))=H from h);exact⟨⟨by simp[t],n⟩,by simp[t]⟩
def fI (l:Nat->Q W)(c:W)(d j x y z h f i:Nat)(g e:Y):Y:= E (Dn i (De (De j (cond g 0 h)) (cond e 0 f))) fun k=>Option.rec J (fun b=>f2 b fun b=>E (jI b) fun a=>and (fF a z b) (and (s8 (fun v=>or (and (not g) (M v x)) (or (and (not e) (M v y)) (fF a v b))) c) (s8 (fun v=>or (M v z) (and (and (or g (not (M v x))) (or e (not (M v y)))) (fF d v c))) b))) (l k)
lemma l6 {k a:Z D}{r:Nat->Q W}{x y j g:Nat}{z:N}{q p:Y}(l:Dn (jT z.toNat) (De (De (kS (wN k)) (cond q 0 j)) (cond p 0 g))=kS ((z::a.map G).map A8))(i:∀ v:N,v∈a.map G↔v∈k.map G/\(v.toNat≠x\/q=H)/\(v.toNat≠y\/p=H))(h:fI r (wN k) (jI (wN k)) (kS (wN k)) x y z.toNat j g (jT z.toNat) q p=H) : ∃ ys,r (kS ((z::a.map G).map A8))=some ys/\∀ xs:Z N,ys=xs.map A8->(z::a.map G).toFinset=xs.toFinset:=by
 simp only[fI,R,l] at h;cases o:r (kS ((z::a.map G).map A8)) with
 | none=>rw[o] at h;cases h
 | some ys=>
   refine⟨ys,rfl,fun xs h3=>?_⟩;rw[o] at h;simp only[gf,tm,X,Ae,Ai,D8] at h
   obtain⟨u,h1,h2⟩:=h;have u':=(hV _ _).mp (gW u);have b {v:N} (hv:v.toNat∈xs.map A8):v∈xs:=by obtain⟨w,m,e⟩:=Aj.mp hv;exact Do.mp e▸m
   subst h3;ext v;simp only[A4,Ab,i];constructor
   . rintro (rfl|⟨hm,f,c⟩)
     . exact b u'
     . obtain⟨w,m,rfl⟩:=Aj.mp hm;rcases h1 w.1.toNat (Qm m) with⟨h0,n⟩|⟨h4,n⟩|hy
       . rcases f with d|rfl;exact Qa (Cl n) d;simp at h0
       . rcases c with d|rfl;exact Qa (Cl n) d;simp at h4
       . exact b ((hV _ _).mp (gW hy))
   . intro hv;rcases h2 v.toNat (Qm hv) with n|⟨⟨f,c⟩,m⟩
     . exact D5 (Do.mp (Cl n))
     . right;obtain⟨w,t,s⟩:=Aj.mp ((hV _ _).mp (gW m));refine⟨Do.mp s▸Qm t,?_,?_⟩
       . rcases f with rfl|d;exact D6 rfl;exact D5 fun e=>by subst e;simp at d
       . rcases c with rfl|d;exact D6 rfl;exact D5 fun e=>by subst e;simp at d
lemma ld {c:Z D}{j:Nat->Q W}{a b:D}{z:N}{f d:Y}(l:(c.map G).Nodup)(i:a∈c)(k:b∈c)(g:a.1≠b.1)(h:fI j (wN c) (jI (wN c)) (kS (wN c)) a.1.toNat b.1.toNat z.toNat (jT a.1.toNat) (jT b.1.toNat) (jT z.toNat) f d=H) : ∃ ys,j (kS ((z::(il c a b f d).map G).map A8))=some ys/\∀ xs:Z N,ys=xs.map A8->(z::(il c a b f d).map G).toFinset=xs.toFinset:= l6 (by simp only[wN,sY,As,DB,C4];change _=jT z.toNat+((il c a b f d).map fun w:D=>jT w.1.toNat).sum;rw[sd _ i k (fun e=>g (Az G e))];rfl)
 (fun v=>by rw[v6 l i k f d];simp[Do.ne]) h
lemma lR {b:Z D}{g:Nat->Q W}{a:D}{z:N}{c:Y}(f:(b.map G).Nodup)(e:a∈b)(h:fI g (wN b) (jI (wN b)) (kS (wN b)) a.1.toNat 0 z.toNat (jT a.1.toNat) 0 (jT z.toNat) c H=H) : ∃ ys,g (kS ((z::(gj b a c).map G).map A8))=some ys/\∀ xs:Z N,ys=xs.map A8->(z::(gj b a c).map G).toFinset=xs.toFinset:= l6 (by simp only[wN,sY,As,DB,C4,D4];change _=jT z.toNat+((gj b a c).map fun w:D=>jT w.1.toNat).sum;rw[sp _ e];rfl)
 (fun v=>by have wn:=f.of_map;simp only[Aj,tR wn,Do.ne,or_true,and_true];exact⟨by rintro⟨w,hw,rfl⟩;exact⟨⟨w,hw.1,rfl⟩,hw.2.imp (fun ne d=>ne (j7 f hw.1 e d)) id⟩,by rintro⟨⟨w,hm,rfl⟩,h'⟩;exact⟨w,⟨hm,h'.imp (fun ne d=>ne (Az G d)) id⟩,rfl⟩⟩) h
abbrev kn:=Nat×Nat×Nat×Nat×PP
def k7 (u:Y)(e f:Nat)(w:D):kn:= let c:=w.1.toNat;let a:=w.2.1.toNat;let b:=w.2.2.toNat;let d:=cond u (L a (D9 g7 b)) (D9 a b);(c,jT c,a,b,d,L e (D9 g7 (L f d)))
def kf {e:Type}(u:Y)(j h:Nat)(i:Z D)(k:Z kn->e):e:= List.rec (fun k=>k []) (fun w _ l k=>E w.1.toNat fun g=>E (jT g) fun d=>E w.2.1.toNat fun c=>E w.2.2.toNat fun a=>E (cond u (L c (D9 g7 a)) (D9 c a)) fun f=>E (L j (D9 g7 (L h f))) fun b=>l fun m=>k ((g,d,c,a,f,b)::m)) i k
lemma kx {i:Type}(u:Y)(b a:Nat)(ws:Z D)(k:Z kn->i):kf u b a ws k=k (ws.map (k7 u b a)):=by
 induction ws generalizing k with|nil=>rfl| cons w ws j=>
  change E w.1.toNat (fun h=>E (jT h) fun f=>E w.2.1.toNat fun e=>E w.2.2.toNat fun c=>E (cond u (L e (D9 g7 c)) (D9 e c)) fun g=>E (L b (D9 g7 (L a g))) fun d=>kf u b a ws fun l=>k ((h,f,e,c,g,d)::l))=_;rw[R,R,R,R,R,R,j];rfl
structure C2 where
 a4:Nat
 cap:Nat
 len:Nat
 wsN:W
 bl:Nat
 tot:Nat
 c1:Nat
 c2:Nat
 c3:Nat
 qs:Z lu
 fl:Nat->Q W
 le1:Y
 le0:Y
 leP:Y
def kc (i a:Nat)(b:W)(g c f h d:Nat)(e:Z lu)(j:Nat->Q W):C2:= let l:=b.length;⟨i,a,l,b,g,c,f,h,d,e,j,Db (De l 1) a,Db l a,Db (Nat.succ l) a⟩
abbrev gO (e:Y)(c:Nat)(b:Z D)(d:Z lu)(f:Nat->Q W):C2:= let a:=ei e b;kc z4 c (wN b) (jI (wN b)) (kS (wN b)) a.1.toNat a.2.1.toNat a.2.2.toNat d f
lemma kj {b a:Type}{o:Q b}{f:b->Q a}{y:a}(h:Option.rec none f o=some y):∃ x,o=some x/\f x=some y:=by cases o with|none=>contradiction| some x=>exact⟨x,rfl,h⟩
lemma kA {b:Z D}{t:N}(a:(wN b).Nodup)(hT':fX t.toNat (wN b)=J) : (b.map G).Nodup/\t∉b.map G:=by
 refine⟨by have h:wN b=(b.map G).map A8:=(by simp[wN]);rw[h] at a;exact a.of_map,
  fun e=>by obtain⟨w,c,d⟩:=Aj.mp e;rw[(hV _ _).mpr (Aj.mpr ⟨w,c,Az A8 d⟩)] at hT';contradiction⟩
lemma l8 (h:Y){r s:Fin 320->K}{c:Z D}{i j p:Nat}(q o:Y)(d:∀ w∈c,ex r s w)(y:(c.map G).Nodup)(hi:i<c.length)(hj:j<c.length)(x:i≠j)(m:U (ji p (c.getD i C) (c.getD j C)).1)(f:(ji p (c.getD i C) (c.getD j C)).1∉c.map G) : let a:=c.getD i C;let b:=c.getD j C;let z:=ji p a b;let rest:=il c a b q o;let e:=z.1::rest.map G
 a∈c/\b∈c/\a.1≠b.1/\e.Nodup/\e.length=1+(c.length-(if q then 0 else 1)-(if o then 0 else 1))/\
 (sg (ei h c) (eP h a.2) (eP h b.2) q o|||eP h z.2)=f8 h (f3 r s) e/\
 M z.1.toNat 0=J/\M z.1.toNat z4=J/\fF (jI (wN c)) z.1.toNat (wN c)=J:=by
 set a:=c.getD i C;set b:=c.getD j C;set z:=ji p a b;set rest:=il c a b q o;set e:=z.1::rest.map G;have u:a∈c:=(by simp[a,Ah hi]);have n:b∈c:=(by simp[b,Ah hj]);have g:a.1≠b.1:=fun k=>x ((DG y (hi:=by simpa using hi) (hj:=by simpa using hj)).mp (by simpa[a,b,A1,Ah hi,Ah hj] using k))
 have l:rest.Sublist c:=wG _ _ _ _ _;refine⟨u,n,g,B7.mpr ⟨fun hm=>f ((l.map _).subset hm),y.sublist (l.map _)⟩,by change (z.1::rest.map G).length=_;rw[AY,AQ,xM _ _ _ _ _ u n (fun k=>g (Az G k)),Aw 1],?_,Bp.mpr fun k=>m.1 (DS (by simpa[P] using Cl k)),
  Bp.mpr fun k=>m.2 (DS ((Cl k).trans t2.symm)),
  Bp.mpr fun n'=>by obtain⟨w,hw,he⟩:=Aj.mp ((hV _ _).mp (gW n'));exact f (Do.mp he▸Qm hw)⟩
 have t:=vI h rest (fun v hv=>d _ (l.subset hv));have rz:=xG h a b u n (fun k=>g (Az G k)) q o;have hf:z.2=f3 r s z.1:=j1 p (d _ u) (d _ n);rw[show f8 h (f3 r s) e=eP h (f3 r s z.1)|||f8 h (f3 r s) (rest.map G) from rfl,<-hf,<-t,rz,Cn];rfl
lemma sI {c:Y}{j:Z D}{a b z:D}{i h:Y}(k:(sg (ei c j) (eP c a.2) (eP c b.2) i h|||eP c z.2)=AO) : ((ei c j).1|||eP c z.2)=AO:=by
 apply Af;intro d f;have e:=Az (fun v:fU=>v.getLsbD d) k;simp only[B1,BL,f,B6] at e ⊢
 cases g:(eP c z.2).getLsbD d;. simp only[g,DC] at e ⊢;cases i<;>cases h<;>simp[sg,i7,sn,Aq] at e<;>first|exact e|exact e.1
 . simp
lemma lZ {u:Y}{c:Z D}(v:(c.map G).Nodup){k:N->N->Nat->Y->Y->Prop}(i:∀ a b d ka kb,eT u d->a∈c.map G->b∈c.map G->k b a (iE d) kb ka->k a b d ka kb)(e:∀ ia ib op (hia:ia<c.length) (hib:ib<c.length),ia < ib->eT u op->∀ ka kb, U (V op (c.getD ia C).1 (c.getD ib C).1)->V op (c.getD ia C).1 (c.getD ib C).1∉c.map G->k (c.getD ia C).1 (c.getD ib C).1 op ka kb) : ∀ a∈c.map G,∀ b∈c.map G,∀ d,eT u d->∀ ka kb,a≠b->V d a b∉c.map G->U (V d a b)->k a b d ka kb:=by
 intro a ha b hb d hd ka kb ne fr pro;obtain⟨g,r,rfl⟩:=Aj.mp ha;obtain⟨h,s,rfl⟩:=Aj.mp hb;obtain⟨ia,hia,l⟩:=DT r;obtain⟨ib,hib,o⟩:=DT s;have ga:c.getD ia C=g:=(by simp[Ah hia,l]);have f:c.getD ib C=h:=(by simp[Ah hib,o]);have m:ia≠ib:=fun t=>ne (by rw[<-ga,<-f,t]);rcases Nat.lt_or_gt_of_ne m with n|q;. simpa only[ga,f] using e ia ib d hia hib n hd ka kb (by simpa only[ga,f] using pro) (by simpa only[ga,f] using fr)
 . apply i g.1 h.1 d ka kb hd ha hb;have p':V (iE d) h.1 g.1∉c.map G:=js hd g.1 h.1▸fr;have j':U (V (iE d) h.1 g.1):=js hd g.1 h.1▸pro;simpa only[ga,f] using e ib ia (iE d) hib hia q (wO hd).1 kb ka (by simpa only[ga,f] using j') (by simpa only[ga,f] using p')
def jy (r:Y)(x:C2)(a:Nat->Nat->Nat->Nat->Nat->Y->Y->Nat->Q Nat)(n o d h i b c p q z:Nat)(s:Nat):Q Nat:= E (cond r (L p (D9 g7 q)) (D9 p q)) fun j=>cond (M (Dc x.c1 j) g7) (j4 (and x.le1 (M (Dc d j) g7)) fun g=>j4 (and x.le0 (M (Dc o j) g7)) fun e=>j4 (and x.le0 (M (Dc n j) g7)) fun f=>cond (or g (or e (or f x.leP))) (E z fun z=>cond (or (M z 0) (M z x.a4)) (some s) (Option.rec none (fun m=>E m fun m=>Option.rec none (fun l=>E l fun l=>Option.rec none (fun k=>E k fun k=>cond x.leP (a h i z b c H H k) (some k)) (cond f (a h i z b c J H l) (some l))) (cond e (a h i z b c H J m) (some m))) (cond g (a h i z b c J J s) (some s)))) (some s)) (some s)
def kY (t p:Y)(x:C2)(l:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Y->Y->Nat->Q Nat)(i n d e o m pa c:Nat)(bs:Z kn):Nat->Nat->Nat->Q Nat:= List.rec (fun _ _ s=>some s) (fun w _ ih j a s=>let(h,k,q,r,pb,f):=w;let g:=l i j n a;E (L x.c1 (D9 g7 (Dc (L x.c2 (Dc pa pb)) (L x.c3 (L pa pb))))) fun b=>E (Nat.succ j) fun j'=>E (Dd a 1) fun a'=>Option.rec none (fun z=>E z fun z=>Option.rec none (fun u=>E u fun u=>cond p (Option.rec none (fun y=>E y fun y=>Option.rec none (fun v=>E v fun v=>ih j' a' v) (jy t x g c f b d h e k (D9 q (L o q)) (D9 r (L m r)) (D9 h (L d h)) y)) (jy t x g c f b d h e k (D9 o (L o q)) (D9 m (L m r)) (D9 d (L d h)) u)) (ih j' a' u)) (jy t x g c f b d h e k (Dc o q) (Dc m r) (Dc d h) z)) (jy t x g c f b d h e k (L o q) (L m r) (L d h) s)) bs
def iD (h c:Y)(x:C2)(b:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Y->Y->Nat->Q Nat)(g:Z kn):Nat->Nat->Nat->Q Nat:= List.rec (fun _ _ s=>some s) (fun w n l i a s=>let(o,e,m,k,j,d):=w;E (Nat.succ i) fun i'=>E (Dd a 1) fun a'=>Option.rec none (fun f=>E f fun f=>l i' a' f) (kY h c x b i a o e m k j d n i' a' s)) g
lemma sL (k:Nat):Dd (1<<<k) 1=1<<<(k+1):=by change (1<<<k)<<<1=1<<<(k+1);rw[Ag,Ag,Ag];simp[DL]
lemma lU {t b x a i g p l r q n k m f s s'}(h:kY t b x a i g p l r q n k m f (1<<<f) s=some s'){d:Nat}(o:d < m.length){e:Nat}(j:e < if b then 4 else 2) : let(ay,kwb,p2,q2,pb,rsB):=m[d];let rsAB:=L x.c1 (D9 g7 (Dc (L x.c2 (Dc n pb)) (L x.c3 (L n pb))))
 ∃ s1 s2,jy t x (a i (f+d) g (1<<<(f+d))) k rsB rsAB p ay l kwb (zN e r p2) (zN e q q2) (zN e p ay) s1=some s2:=by
 induction m generalizing f s d with|nil=>simp at o| cons w y ih=>
  rcases w with⟨ay,kwb,p2,q2,pb,rsB⟩;unfold kY at h;dsimp only at h;rw[R,R,R,sL] at h;have⟨s1,v,h⟩:=kj h;rw[R] at h;obtain⟨s2,u,c⟩:=kj h;rw[R] at c;cases b with
  | false=>
    rw[D2] at c;cases d with
    | zero=>simp only[Dz,DA];rcases (by simp at j;omega:e=0\/e=1) with rfl|rfl;exact⟨s,s1,v⟩;exact⟨s1,s2,u⟩
    | succ d=>simpa only[show f+(d+1)=(f+1)+d by omega,Ds] using ih c (by simp at o;omega)
  | true=>
    rw[D4] at c;have⟨z,h2,c⟩:=kj c;rw[R] at c;obtain⟨s4,h3,c⟩:=kj c;rw[R] at c;cases d with
    | zero=>simp only[Dz,DA];rcases (by simp at j;omega:e=0\/e=1\/e=2\/e=3) with rfl|rfl|rfl|rfl;exact⟨s,s1,v⟩;exact⟨s1,s2,u⟩;exact⟨s2,z,h2⟩;exact⟨z,s4,h3⟩
    | succ d=>simpa only[show f+(d+1)=(f+1)+d by omega,Ds] using ih c (by simp at o;omega)
lemma sC {k f x e l c s s'}(h:iD k f x e l c (1<<<c) s=some s'){a b:Nat}(q:a<b)(j:b<l.length){g:Nat}(i:g < if f then 4 else 2) : let(ax,kwa,p1,q1,pa,rsA):=l[a];let(ay,kwb,p2,q2,pb,rsB):=l[b];let rsAB:=L x.c1 (D9 g7 (Dc (L x.c2 (Dc pa pb)) (L x.c3 (L pa pb))))
 ∃ s1 s2,jy k x (e (c+a) (c+b) (1<<<(c+a)) (1<<<(c+b))) rsA rsB rsAB ax ay kwa kwb (zN g p1 p2) (zN g q1 q2) (zN g ax ay) s1=some s2:=by
 induction l generalizing c s a b with|nil=>simp at j| cons w m o=>
  rcases w with⟨ax,kwa,p1,q1,pa,rsA⟩;unfold iD at h;dsimp only at h;rw[R,R,sL] at h;have⟨s1,p,n⟩:=kj h;rw[R] at n;cases a with
  | zero=>cases b with|zero=>omega| succ d=>simpa only[Dz,show c+(d+1)=(c+1)+d by omega,DA,Ds] using lU p (by simp at j;omega) i
  | succ a=>cases b with|zero=>omega| succ b=>simpa only[show c+(a+1)=(c+1)+a by omega,show c+(b+1)=(c+1)+b by omega,Ds] using o n (by omega) (by simp at j;omega)
lemma lI {e:Y}{d:Z D}{qs fl f i j k m l q q'}{r:Nat->Nat->Nat->Nat->Nat->Y->Y->Nat->Q Nat}(g:1+(d.length-(if m then 0 else 1)-(if l then 0 else 1))<=f)(n:(sg (ei e d) (eP e (d.getD i C).2) (eP e (d.getD j C).2) m l|||eP e (ji k (d.getD i C) (d.getD j C)).2)=AO)(hnz0:M (ji k (d.getD i C) (d.getD j C)).1.toNat 0=J)(hnz1:M (ji k (d.getD i C) (d.getD j C)).1.toNat z4=J)(c:let cov:=ei e d;let w1:=k7 e cov.1.toNat cov.2.1.toNat (d.getD i C);let w2:=k7 e cov.1.toNat cov.2.1.toNat (d.getD j C)
 let rsAB:=L cov.1.toNat (D9 g7 (Dc (L cov.2.1.toNat (Dc w1.2.2.2.2.1 w2.2.2.2.2.1)) (L cov.2.2.toNat (L w1.2.2.2.2.1 w2.2.2.2.2.1))))
 jy e (gO e f d qs fl) r w1.2.2.2.2.2 w2.2.2.2.2.2 rsAB w1.1 w2.1 w1.2.1 w2.2.1 (zN k w1.2.2.1 w2.2.2.1) (zN k w1.2.2.2.1 w2.2.2.2.1) (zN k w1.1 w2.1) q=some q') :
 let a:=d.getD i C;let b:=d.getD j C;let z:=ji k a b
 ∃ s1 s2,r a.1.toNat b.1.toNat z.1.toNat (jT a.1.toNat) (jT b.1.toNat) m l s1=some s2:=by
 set a:=d.getD i C;set b:=d.getD j C;set z:=ji k a b;have y:=sI n;have p:M (Dc (sg (ei e d) (eP e a.2) (eP e b.2) m l).toNat (eP e z.2).toNat) AO.toNat=H:=(by rw[sR,sO,n,beq_self_eq_true]);dsimp only at c;simp only[jy,gO,kc,k7,R,kh,u0,lS,se,vm,wN,AQ] at c;have ep (v:fU×fU):cond e (L v.1.toNat (D9 g7 v.2.toNat)) (D9 v.1.toNat v.2.toNat)=(eP e v).toNat:=by cases e;exact t5 v;exact si v
 rw[ep (bv k a.2.1 b.2.1,bv k a.2.2 b.2.2),show (bv k a.2.1 b.2.1,bv k a.2.2 b.2.2)=z.2 from rfl,ep a.2,ep b.2,lS,lS,se] at c;simp only[lA] at c;rw[sR,sO,y,beq_self_eq_true,D4] at c;set s:=and (Db (De d.length 1) f) (M (Dc (sn (ei e d) (eP e a.2) (eP e b.2)).toNat (eP e z.2).toNat) AO.toNat);set t:=and (Db d.length f) (M (Dc (i7 (ei e d) (eP e b.2)).toNat (eP e z.2).toNat) AO.toNat);set u:=and (Db d.length f) (M (Dc (i7 (ei e d) (eP e a.2)).toNat (eP e z.2).toNat) AO.toNat);set w:=Db (Nat.succ d.length) f;have o:(m=J/\l=J/\s=H)\/(m=H/\l=J/\t=H)\/(m=J/\l=H/\u=H)\/(m=H/\l=H/\w=H):=by
  cases m<;>cases l
  . exact D5 ⟨rfl,rfl,by rw[X,Df];exact⟨by change d.length-1<=f;simp at g;omega,by simpa[sg] using p⟩⟩
  . exact D6 (D6 (D5 ⟨rfl,rfl,by rw[X,Df];exact⟨by simp at g;omega,by simpa[sg] using p⟩⟩))
  . exact D6 (D5 ⟨rfl,rfl,by rw[X,Df];exact⟨by simp at g;omega,by simpa[sg] using p⟩⟩)
  . exact D6 (D6 (D6 ⟨rfl,rfl,Df.mpr (by change d.length+1<=f;simp at g;omega)⟩))
 have x:or s (or t (or u w))=H:=(by rcases o with⟨_,_,h⟩|⟨_,_,h⟩|⟨_,_,h⟩|⟨_,_,h⟩<;>simp[h]);have hnz0':M (V k a.1 b.1).toNat 0=J:=hnz0;have hnz1':M (V k a.1 b.1).toNat z4=J:=hnz1;simp only[x,D4,hnz0',hnz1',DC,D2] at c;have⟨s1,h1,c⟩:=kj c;obtain⟨s2,h2,c⟩:=kj c;obtain⟨s3,h3,h4⟩:=kj c;rcases o with⟨rfl,rfl,h⟩|⟨rfl,rfl,h⟩|⟨rfl,rfl,h⟩|⟨rfl,rfl,h⟩;. rw[h,D4] at h1;exact⟨q,s1,h1⟩
 . rw[h,D4] at h2;exact⟨s1,s2,h2⟩
 . rw[h,D4] at h3;exact⟨s2,s3,h3⟩
 . rw[h,D4] at h4;exact⟨s3,q',h4⟩
lemma kG {j d:Y}{c:Z D}{r s m p p'}{i:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Y->Y->Nat->Q Nat}(n:(c.map G).Nodup){xp:Z N->Prop}(o:let e:=ei j c;iD j d (gO j m c r s) i (c.map (k7 j e.1.toNat e.2.1.toNat)) 0 1 p=some p')
 (l:∀ ia ib op ka kb (g:ia<c.length) (f:ib<c.length),ia < ib->op<(if d then 4 else 2)->U (V op (c.getD ia C).1 (c.getD ib C).1)->V op (c.getD ia C).1 (c.getD ib C).1∉c.map G->(let e:=ei j c;let w1:=k7 j e.1.toNat e.2.1.toNat (c.getD ia C);let w2:=k7 j e.1.toNat e.2.1.toNat (c.getD ib C)
  let rsAB:=L e.1.toNat (D9 g7 (Dc (L e.2.1.toNat (Dc w1.2.2.2.2.1 w2.2.2.2.2.1)) (L e.2.2.toNat (L w1.2.2.2.2.1 w2.2.2.2.2.1))))
  ∃ s1 s2,jy j (gO j m c r s) (i ia ib (1<<<ia) (1<<<ib)) w1.2.2.2.2.2 w2.2.2.2.2.2 rsAB w1.1 w2.1 w1.2.1 w2.2.1 (zN op w1.2.2.1 w2.2.2.1) (zN op w1.2.2.2.1 w2.2.2.2.1) (zN op w1.1 w2.1) s1=some s2)->
  xp (iQ c op (c.getD ia C) (c.getD ib C) ka kb))
 (k:∀ l1 l2:Z N,l1.toFinset=l2.toFinset->xp l1->xp l2) :
 ∀ a∈c.map G,∀ b∈c.map G,∀ op,eT d op->∀ ka kb,a≠b->V op a b∉c.map G->U (V op a b)->xp (eQ (c.map G) a b op ka kb):=
 lZ (u:=d) n (fun a b op ka kb hop _ _ hp=>k _ _ (jU (u:=d) _ n _ _ op hop ka kb).symm hp)
  (fun ia ib op g f hlt hop ka kb hpro hfr=>by
   have hga:c.getD ia C∈c:=(by simp[Ah g]);have hgb:c.getD ib C∈c:=(by simp[Ah f])
   have hne':(c.getD ia C).1≠(c.getD ib C).1:=fun eq=>by have:ia=ib:=(DG n (hi:=by simpa using g) (hj:=by simpa using f)).mp (by simpa[A1,Ah g,Ah f] using eq);omega
   have hop':op < if d then 4 else 2:=by cases d;rcases hop with h|⟨h,_⟩<;>simp_all;rcases eY hop with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩<;>simp
   obtain⟨s1,s2,q'⟩:=sC o hlt (by simpa using f) hop';simp only[C1,get_eq_getElem,DO] at q';rw[show GetElem.getElem c ia g=c.getD ia C by simp[Ah g],show GetElem.getElem c ib f=c.getD ib C by simp[Ah f]] at q'
   exact k _ _ (yd n hga hgb hne' op ka kb) (l ia ib op ka kb g f hlt hop' hpro hfr ⟨s1,s2,q'⟩))
def sm (x:C2)(_ _ bitI bitJ ax ay z kwa kwb:Nat)(b a:Y)(s:Nat):Q Nat:= cond (or (kE (fun q=>jx H q bitI bitJ z b a) x.qs) (or (fF x.bl z x.wsN) (fI x.fl x.wsN x.bl x.tot ax ay z kwa kwb (jT z) b a))) (some s) none
def tp (v b:Nat)(m:Z D)(c:Z kC)(u:Z W)(g:Qf)(k i:Nat):Y:= let(_,d,_,_):=g.f k;let(j,n,l,h,_):=gF H m g J k i;E j fun j=>lP n fun n=>lP l fun l=>ip (fun w:D=>w.1.toNat) l fun a=>E (jI a) fun bl=>ip (fun w:D=>w.1.toNat) n fun r=>E (kS a) fun q=>let e:=ei J l;E e.1.toNat fun s=>E e.2.1.toNat fun t=>E e.2.2.toNat fun y=>s9 (bQ H (De k 1) a c j d r h) fun z=>kf J s t l fun o=>let x:=kc v k a bl q s t y z (fun p=>(g.i k p).bind (eG H g J (De k 1) u));and (sM a) (and (not (fX b a)) (cond (M k 0) H (Option.rec J (fun _=>H) (iD J H x (sm x) o 0 1 0))))
lemma gJ (g:Qf)(k i:Nat)(l:g8 (uf g) (fq fun j=>(eH H g.m j).1) (fq fun j=>(eH H g.m j).2))(h5:∀ ci∈g.o,t3 H (eu (g4 g.m ci)) (uf g) (g5 ci.1 ci.2.1) ci.2.2.2.2)(m:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H)(q:k>0->∀ idx < (g.f (k-1)).1,u1 H (uf g) (k-1) (eA H g J (k-1) idx).toFinset)(c:tp z4 (uf g).toNat (eF H g) (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H) : u1 H (uf g) k (eA H g J k i).toFinset:=by
 unfold tp at c;set rn:=gF H (eF H g) g J k i;set ws:=rn.2.2.1;simp only[R,lM,kg,sa,kx,X,sK,D8] at c;obtain⟨hm,hT',s⟩:=c;obtain⟨u,hT⟩:=kA hm hT';by_cases h0:k=0;. subst k;intro t ht h1;have:t=0:=(by omega);subst this;exact hT (A4.mp (h1.1▸Ao _))
 . have o:0<k:=(by omega);rw[show M k 0=J from Bp.mpr fun e=>h0 (Cl e),D2] at s;cases hj:iD J H _ _ _ 0 1 0 with|none=>rw[hj] at s;contradiction| some st'=>
   have n:∀ w∈ws,ex (fq fun j=>(eH H g.m j).1) (fq fun j=>(eH H g.m j).2) w:=fun w hw=>h9 H _ _ _ _ _ (gU H g) w ((it _ _).subset hw);have h3:∀ hf ys,((g.i k hf).bind (eG H g J (k-1) (g.a.map (iO g.m))))=some ys->∃ xs:Z N,ys=xs.map A8/\u1 H (uf g) (k-1) xs.toFinset:=fun hf ys h=>by have⟨_,_,h2⟩:=At.mp h;exact jo g (k-1) m (q o) h2
   apply vq u hT;intro a ha b hb d hd ka kb ne fr x9 _
   exact kG (xp:=fun ls=>u1 H (uf g) (k-1) ls.toFinset) u hj (fun ia ib op ka kb hia hib hlt hop hpro hfr ⟨_,_,hg'⟩=>by
    set a:=ws.getD ia C;set b:=ws.getD ib C;set z:=ji op a b;set r:=il ws a b ka kb;obtain⟨ha',hb',ho,hp,xc,x1,hi,hc,x5⟩:=l8 J ka kb n u hia hib (by omega) hpro hfr;intro t ht run;have hl:=gz run;change (z.1::r.map G).toFinset.card<=t+1 at hl;rw[Ap hp] at hl;have v:=ie run (uX l);change f8 J _ (z.1::r.map G)=AO at v;rw[<-x1] at v;obtain⟨_,_,x⟩:=lI (by omega) v hi hc hg';unfold sm at x;dsimp only[gO,kc] at x;rw[x5,BT] at x;cases hh:or (kE _ _) (fI _ _ _ _ _ _ _ _ _ _ _ _) with
    | false=>rw[hh] at x;contradiction
    | true=>
      rcases (Ai _ _).mp hh with h4|y;. obtain⟨q',hq',x0⟩:=sk.mp h4;obtain⟨p,x6,hk⟩:=uU h5 hq';exact jJ x6 (show (eM (op,a.1,b.1)::r.map G).Nodup from hp) (ty hk hia hib (by omega) u (by simpa using hop) x0) t ht run
      . obtain⟨ys,x7,hz⟩:=ld u ha' hb' ho y;obtain⟨xs,x4,hn⟩:=h3 _ _ x7;change Lv H (uf g) t (z.1::r.map G).toFinset at run;rw[hz xs x4] at run;exact hn t ht run) (fun _ _ he h=>he▸h) a ha b hb d hd ka kb ne fr x9
def fB (f:Nat->Y)(start:Nat):Nat->Y
 | 0=>H
 | n+1=>f (start+n)&&fB f start n
lemma fP {f c n}(h:fB f c n=H)(i:Nat)(a:c<=i)(b:i<c+n):f i=H:=by
 induction n with
 | zero=>omega
 | succ n d=>
   simp only[fB,X] at h;by_cases e:i=c+n;. simpa[e] using h.1
   . exact d h.2 (by omega)
lemma iH {f d a b}(e:fB f d a=H)(c:fB f (d+a) b=H):fB f d (a+b)=H:=by induction b with|zero=>simpa using e | succ b g=>simp only[fB,X] at c ⊢;exact⟨by simpa[AZ] using c.1,g c.2⟩
def s6 (g:Qf)(f:(Nat->Nat->Y)->Y):Y:= E z4 fun e=>E (uf g).toNat fun h=>lP (eF H g) fun c=>lg g.m g.o fun b=>hP g.m g.a fun d=>f (tp e h c b d g)
lemma lD (g:Qf)(f:(Nat->Nat->Y)->Y):s6 g f=f (tp z4 (uf g).toNat (eF H g) (g.o.map (fN g.m)) (g.a.map (iO g.m)) g):=by simp[s6,R,lM,lB,k4]
def bF (g:Qf)(k st n:Nat):Y:=s6 g fun fk=>fB (fk k) st n
lemma uQ {g k st a b}(h1:bF g k st a=H)(h2:bF g k (st+a) b=H):bF g k st (a+b)=H:=by simp only[bF,lD] at h1 h2 ⊢;exact iH h1 h2
def uk (g:Qf)(k:Nat):Prop:=∀ i < (g.f k).1,tp z4 (uf g).toNat (eF H g) (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H
lemma aF {g k n}(h:bF g k 0 n=H)(e:(g.f k).1=n):uk g k:=fun i hi=>by simp only[bF,lD] at h;exact fP h i (AU _) (by omega)
def uO (g:Qf)(ks:W):Y:=s6 g fun fk=>ks.all fun k=>fB (fk k) 0 (g.f k).1
lemma uP {g ks}(h:uO g ks=H)(k:Nat)(hk:k∈ks):uk g k:=fun i hi=>by simp only[uO,lD] at h;exact fP (Ae.mp h k hk) i (AU _) (by simpa using hi)
def w6 (g:Qf)(a:Nat):Y:=uO g (range (a+1))
lemma v0 {g a}(h:w6 g a=H):∀ k ≤ a,uk g k:=fun k b=>uP h k (AM.mpr (by omega))
def un (g:Qf)(prior:NN):Y:=tH (j9 H g.m) fun arr=>(fT g.m (fun j=>(arr.getD j (0,0)).1)==AO)&&(fT g.m (fun j=>(arr.getD j (0,0)).2)==0)&&g.o.all (fun c=>hZ g.m c prior)&&g.a.all (fun p=>p.all eO&&hG (uf g) (p.map eo))
lemma xl (g:Qf)(h:Nat)(c:NN)(f:∀ q,fL H (eu q) (e6 q) (c q))(b:un g c=H)(n:∀ k ≤ h,uk g k):∀ k ≤ h,∀ idx < (g.f k).1,u1 H (uf g) k (eA H g J k idx).toFinset:=by
 simp only[un,tj,X,Ae,Ar] at b;have a:g8 (uf g) (fq fun j=>(eH H g.m j).1) (fq fun j=>(eH H g.m j).2):=w9 b.1.1.1 b.1.1.2;have e:∀ l∈g.o,t3 H (eu (g4 g.m l)) (uf g) (g5 l.1 l.2.1) l.2.2.2.2:=fun l i=>wT l c f (b.1.2 l i);have d:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H:=fun p s=>by simpa[X] using b.2 p s
 intro k;induction k with|zero=>intro hk idx hidx;exact gJ g 0 idx a e d (by omega) (n 0 hk idx hidx) | succ k r=>intro hk idx hidx;exact gJ g (k+1) idx a e d (fun _=>r (by omega)) (n (k+1) hk idx hidx)
def fV (g:Qf)(k i:Nat)(a:Z N):Y:=decide (i<(g.f k).1)&&jC (eA H g J k i) a
lemma uq {g top prior k i ws}(lower:∀ q,fL H (eu q) (e6 q) (prior q))(geom:un g prior=H)(hA:∀ j ≤ top,uk g j)(le:k<=top)(idx:fV g k i ws=H):u1 H (uf g) k ws.toFinset:=by simp only[fV,X,A6] at idx;rw[<-jd idx.2];exact xl g top prior lower geom hA k le i idx.1
lemma jn {g f i h}(e:∀ q,fL H (eu q) (e6 q) (f q))(c:un g f=H)(n:∀ j ≤ g.cap,uk g j)(d:fV g g.cap i (h7 g.m)=H)(l:eD (uf g)=H)(b:el (uf g) (h7 g.m) (eg g.m h)=H)(k:(eg g.m h).map G=h7 g.m):fL H (h7 g.m) (uf g) (g.cap+1):=by apply xo (eJ _ l) (fs b).1 (fs b).2 _ (uq e c n (BA _) d);intro a ha;apply ga b a;rw[k];exact A4.mpr ha
lemma wr {d:Z D}(e:(d.map G).Nodup){a:D}(g:a∈d):((gj d a J).map G).toFinset=((d.map G).erase a.1).toFinset:=by
 ext v;have h:=e.of_map;simp only[gj,Ak,AB,A4,Aj,h.mem_erase_iff,e.mem_erase_iff];constructor;. rintro⟨w,⟨c,b⟩,rfl⟩;exact⟨fun f=>c (j7 e b g f),w,b,rfl⟩
 . rintro⟨c,w,b,rfl⟩;exact⟨w,⟨fun f=>c (Az G f),b⟩,rfl⟩
abbrev kr:=Nat×Nat×W
abbrev j3 (T:N):LP:=(fO T).map fun p=>(1<<<p.1,p.2)
abbrev g9 (a:LP)(w:N):W:=a.map fun b=>fA b.2 b.1 w.toNat
abbrev kI (T:N)(a:Z N)(i:Nat):Nat:=(ev (en T i) (1<<<i) (a.map A8) 0 0).1&&&(z4^^^(ev (en T i) (1<<<i) (a.map A8) 0 0).2)
def kZ {b:Type}(a:LP)(k:LP->b):b:= List.rec (fun k=>k []) (fun p _ c k=>E (Dd 1 p.1) fun d=>E p.2 fun f=>c fun e=>k ((d,f)::e)) a k
lemma s5 {a:Type}(fms:LP)(k:LP->a):kZ fms k=k (fms.map fun p=>(1<<<p.1,p.2)):=by induction fms generalizing k with|nil=>rfl| cons p fms b=>change E (Dd 1 p.1) (fun e=>E p.2 fun d=>kZ fms fun c=>k ((e,d)::c))=_;rw[R,R,b];rfl
def kP {b:Type}(w d:Nat)(a:LP)(k:W->b):b:= List.rec (fun k=>k []) (fun c _ e k=>E (L (L (D3 w c.1) d) c.2) fun s=>e fun f=>k (s::f)) a k
def k8 {b:Type}(c w:Nat)(a:LP)(k:W->b):b:=E (D9 c w) fun d=>kP w d a k
lemma l9 {b:Type}(w:Nat)(a:LP)(k:W->b):k8 z4 w a k=k (a.map fun ef=>fA ef.2 ef.1 w):=by unfold k8;rw[R];induction a generalizing k with|nil=>rfl| cons ef e c=>change E (fA ef.2 ef.1 w) (fun s=>kP w _ e fun d=>k (s::d))=_;rw[R,c];rfl
def iV {d:Type}(e:Nat)(a:LP)(b:W)(k:Z W->d):d:= List.rec (fun k=>k []) (fun w _ f k=>k8 e w a fun g=>f fun c=>k (g::c)) b k
lemma ki {d:Type}(a:LP)(b:W)(k:Z W->d):iV z4 a b k=k (b.map fun w=>a.map fun ef=>fA ef.2 ef.1 w):=by induction b generalizing k with|nil=>rfl| cons w e f=>change k8 z4 w a (fun g=>iV z4 a e fun c=>k (g::c))=_;rw[l9,f];rfl
def sl {b:Type}(a:LP)(k:Z PP->b):b:= List.rec (fun k=>k []) (fun _ _ c k=>c fun d=>k ((0,0)::d)) a k
lemma su {b:Type}(a:LP)(k:Z PP->b):sl a k=k (a.map fun _=>(0,0)):=by induction a generalizing k with|nil=>rfl| cons _ _ c=>exact c _
def lV {c:Type}(d:W):Z PP->(Z PP->c)->c:= List.rec (fun a k=>k a) (fun s _ e a k=>List.rec (k []) (fun b a' _=>E (Dc b.1 s) fun c1'=>E (Dc b.2 (L b.1 s)) fun c2'=>e a' fun f=>k ((c1',c2')::f)) a) d
lemma tA {e:Type}(w:Nat)(a:LP)(b:Z PP)(c:b.length=a.length)(k:Z PP->e) : lV (a.map fun ef=>fA ef.2 ef.1 w) b k=k (zipWith (fun ef ab=>(ab.1|||fA ef.2 ef.1 w,ab.2|||(ab.1&&&fA ef.2 ef.1 w))) a b):=by
 induction a generalizing b k with
 | nil=>cases b;rfl;simp at c
 | cons ef d f=>
   cases b with|nil=>simp at c| cons ab b'=>
    change E (Dc ab.1 (fA ef.2 ef.1 w)) (fun c1'=>E (Dc ab.2 (L ab.1 (fA ef.2 ef.1 w))) fun c2'=>lV (d.map fun ef=>fA ef.2 ef.1 w) b' fun g=>k ((c1',c2')::g))=_;rw[R,R,f _ (by simp at c;omega)];rfl
def ku {c:Type}(b:Z W):Z PP->(Z PP->c)->c:= List.rec (fun a k=>k a) (fun e _ d a k=>lV e a fun a'=>d a' k) b
lemma lC {g:Type}(a:LP)(d:W)(b:Z PP)(c:b.length=a.length)(k:Z PP->g) : ku (d.map fun w=>a.map fun ef=>fA ef.2 ef.1 w) b k=k (zipWith (fun ef ab=>ev ef.2 ef.1 d ab.1 ab.2) a b):=by
 induction d generalizing b k with
 | nil=>
   have h:zipWith (fun ef ab=>ev ef.2 ef.1 [] ab.1 ab.2) a b=b:=by clear k;induction a generalizing b with|nil=>cases b;rfl;simp at c | cons _ _ e=>cases b;simp at c;simp only[DR];rw[e _ (by simp at c;omega)];rfl
   rw[h];rfl
 | cons w i e=>
   change lV (a.map fun ef=>fA ef.2 ef.1 w) b (fun b'=>ku (i.map fun w=>a.map fun ef=>fA ef.2 ef.1 w) b' k)=_;rw[tA w a b c,e _ (by simp[c])];congr 1;clear e k c;induction a generalizing b with
   | nil=>rfl
   | cons ef f e=>cases b with|nil=>rfl| cons ab b'=>simp only[DR];rw[e b'];simp[ev,R]
def kD {a:Type}(xs:Z a):Nat->Z a:=List.rec (fun _=>[]) (fun x xs b n=>Nat.rec xs (fun m _=>x::b m) n) xs
def gK {d:Type}(c:Z d)(b:Nat)(a:Y):Z d:=cond a c (kD c b)
def f7 {a:Type}(b:Z a)(i j:Nat)(d c:Y):Z a:=gK (gK b j c) i d
lemma gQ {c:Type}(xs:Z c)(a:Nat)(b:Y):gK xs a b=if b then xs else xs.eraseIdx a:=by
 cases b with|true=>rfl| false=>
  simp only[gK,D2,Ak,↓reduceIte];induction xs generalizing a with
  | nil=>cases a<;>rfl| cons x xs d=>cases a with|zero=>rfl| succ n=>change x::kD xs n=_;rw[d];rfl
lemma jL {b:Type}[BEq b][LawfulBEq b]{xs:Z b}(f:xs.Nodup){i:Nat}(c:i<xs.length)(d:b) : xs.eraseIdx i=xs.erase (xs.getD i d):=by
 induction xs generalizing i with
 | nil=>simp at c
 | cons x xs h=>
   have⟨a,j⟩:=B7.mp f;cases i with
   | zero=>simp[eraseIdx_zero]
   | succ i=>
     have e:x≠xs.getD i d:=fun g=>a (g▸by simp[Ah (by simp at c;omega)])
     simp only[eraseIdx_cons_succ,DK,erase_cons,beq_eq_false_iff_ne.mpr e,Ak,↓reduceIte];rw[h j (by simp at c;omega)]
lemma hN {a:Z D}(d:(a.map G).Nodup){i:Nat}(c:i<a.length)(b:Y) : gK a i b=gj a (a.getD i C) b:=by rw[gQ];cases b;simp only[gj,Ak,↓reduceIte];exact jL d.of_map c C;rfl
lemma kV {a:Z D}(g:(a.map G).Nodup){i j:Nat}(m:i<a.length)(f:j<a.length)(hlt:i<j)(c b:Y) : f7 a i j c b=il a (a.getD i C) (a.getD j C) c b:=by
 unfold f7 il;have h:=hN g f b;have l:((gj a (a.getD j C) b).map G).Nodup:=g.sublist ((j6 a _ b).map _);rw[h];cases b with
 | true=>exact hN g m c
 | false=>
   have d:(a.eraseIdx j).getD i C=a.getD i C:=by
    have hlt':i<(a.eraseIdx j).length:=by rw[Di f];omega
    simp only[A1,Ah m,Ah hlt',BS];exact getElem_eraseIdx_of_lt hlt' hlt
   have e:i<(gj a (a.getD j C) J).length:=by rw[<-h,gQ];simp only[Ak,↓reduceIte];rw[Di f];omega
   have k:(gj a (a.getD j C) J).getD i C=a.getD i C:=by rw[<-h,gQ];exact d
   rw[hN l e c,k];cases c;. simp only[gj];exact erase_comm _ _
   . rfl
lemma k5 {a c:Type}(f:a->c)(b:Z a)(i:Nat)(k:Y):gK (b.map f) i k=(gK b i k).map f:=by rw[gQ,gQ];cases k;simp only[Ak,↓reduceIte,eraseIdx_map];simp
lemma iB {d e:Type}(f:d->e)(c:Z d)(i j:Nat)(b a:Y):f7 (c.map f) i j b a=(f7 c i j b a).map f:=by unfold f7;rw[k5,k5]
def kF (T:N)(c:Z N)(a:LP)(b:LP):Prop:= Forall₂ (fun d o=>∃ i < 12,o.1=1<<<i/\d=(1<<<i,en T i)/\o.2=kI T c i) a b
lemma sj (T:N):∀ e∈fO T,e.1<12/\e.2=en T e.1:=by
 intro e he;simp only[fO,Bw,AM] at he;have⟨j,a,o⟩:=he;split at o;. contradiction
 . simp only[Dl] at o;subst o;exact⟨a,rfl⟩
def kT {e:Type}(h:Nat)(c:LP):Z PP->e->(LP->e)->e:= List.rec (fun _ _ b=>b []) (fun g _ j d a b=>List.rec a (fun f d' _=>cond (not (M f.1 g.2)) a (E (L f.1 (D9 h f.2)) fun i=>j d' a fun k=>b ((g.1,i)::k))) d) c
def kH {d:Type}(g:Nat)(a:LP)(e:Z W)(b:d)(c:LP->d):d:= sl a fun z=>ku e z fun f=>kT g a f b c
lemma lL {x:Type}{T:N}(d:Z N){f:LP}(h:∀ e∈f,e.1<12/\e.2=en T e.1)(a:x)(b:LP->x) : let fmsSh:=f.map fun p=>(1<<<p.1,p.2)
 (kH z4 fmsSh (d.map (g9 fmsSh)) a b=a/\jG f (d.map A8)=H)\/
 ∃ o1s,kH z4 fmsSh (d.map (g9 fmsSh)) a b=b o1s/\kF T d fmsSh o1s:=by
 have k:∀ l:LP,zipWith (fun g y=>ev g.2 g.1 (d.map A8) y.1 y.2) l (l.map fun _=>(0,0))=l.map fun g=>ev g.2 g.1 (d.map A8) 0 0:=fun l=>by induction l with|nil=>rfl| cons _ _ r=>rw[As,As,DR,r]
 dsimp only;unfold kH;rw[show d.map (g9 (f.map fun p=>(1<<<p.1,p.2)))=(d.map A8).map fun w=>(f.map fun p=>(1<<<p.1,p.2)).map fun g=>fA g.2 g.1 w by induction d with|nil=>rfl| cons _ _ r=>simp[g9,r],su,lC _ _ _ (by simp),k]
 clear k;induction f generalizing b with
 | nil=>exact D6 ⟨[],rfl,Forall₂.nil⟩
 | cons g i r=>
   rcases g with⟨c,fm⟩;have⟨j,s⟩:=h (c,fm) BJ;dsimp only at j s;subst s;set n:=i.map fun p=>(1<<<p.1,p.2);set q:=n.map fun g=>ev g.2 g.1 (d.map A8) 0 0;set u:=ev (en T c) (1<<<c) (d.map A8) 0 0;simp only[As];rw[show kT z4 ((1<<<c,en T c)::n) (u::q) a b=cond (not (M u.1 (en T c))) a (E (kI T d c) fun o1=>kT z4 n q a fun rs=>b ((1<<<c,o1)::rs)) from rfl];cases z:not (M u.1 (en T c)) with
   | true=>left;exact⟨rfl,by change (not (M u.1 (en T c))||jG i (d.map A8))=H;rw[z];rfl⟩
   | false=>
     rw[D2,R];rcases r (fun e he=>h e (AK _ he)) _ with⟨o,t⟩|⟨o1s,m,v⟩;. left;exact⟨o,by simp[jG] at t ⊢;exact D6 t⟩
     . right;exact⟨(1<<<c,kI T d c)::o1s,m,Forall₂.cons ⟨c,j,rfl,rfl,rfl⟩ v⟩
def jk {a:Type}(c b s p n:Nat)(k:Nat->Nat->a):a:= cond (or (M b 0) (M s 0)) (k p n) (E (L s b) fun u=>cond (M u 0) (k p n) (E (Dc p (Dd u c)) fun p'=>E (Dc n u) fun n'=>k p' n'))
def iS {c:Type}(a:LP):W->Nat->Nat->(Nat->Nat->c)->c:= List.rec (fun _ p n k=>k p n) (fun e _ d b p n k=>List.rec (k p n) (fun s b' _=>jk e.1 e.2 s p n fun p' n'=>d b' p' n' k) b) a
def iL (T:N)(c:Z N)(a:LP)(w:N)(b:kr):Prop:= b.2.2=g9 a w/\(∀ r,b.1.testBit r=H->∃ (d:r<4096) (n:K),ey c.toFinset T w ⟨r,d⟩ n)/\(∀ r,b.2.1.testBit r=H->∃ (d:r<4096) (p:K),ey c.toFinset T w p ⟨r,d⟩)
lemma l7 {bt:Type}{T:N}{c:Z N}(hd:c.Nodup){w:N}(hw:w∈c){a g:LP}(z:kF T c a g)(k:Nat->Nat->bt) : ∃ p n,iS g (g9 a w) 0 0 k=k p n/\iL T c a w (p,n,g9 a w):=by
 let xp (p n:Nat):Prop:=(∀ r,p.testBit r=H->∃ (d:r<4096) (m:K),ey c.toFinset T w ⟨r,d⟩ m)/\(∀ r,n.testBit r=H->∃ (d:r<4096) (q:K),ey c.toFinset T w q ⟨r,d⟩);suffices ∀ (fs os:LP) (p0 n0:Nat) (k':Nat->Nat->bt),kF T c fs os->xp p0 n0->∃ p n,iS os (g9 fs w) p0 n0 k'=k' p n/\xp p n by
  have⟨p,n,he,o⟩:=this a g 0 0 k z ⟨by simp,by simp⟩;exact⟨p,n,he,rfl,o⟩
 intro fs os p0 n0 k' ho;induction ho generalizing p0 n0 k' with
 | nil=>intro o;exact⟨p0,n0,rfl,o⟩
 | @cons ef e rest os' h0 _ ih=>
   intro⟨hp,hn⟩;have⟨i,hi,s,h3,u⟩:=h0;rcases e with⟨sh,o1⟩;dsimp only at s u;subst s;subst u;subst h3;have l:∃ y x,jk (1<<<i) (kI T c i) (fA (en T i) (1<<<i) w.toNat) p0 n0 (fun p' n'=>iS os' (g9 rest w) p' n' k')=iS os' (g9 rest w) y x k'/\xp y x:=by
    unfold jk;cases or (M _ 0) (M _ 0) with
    | true=>exact⟨p0,n0,rfl,hp,hn⟩
    | false=>
      rw[D2,R];cases M _ 0 with
      | true=>exact⟨p0,n0,rfl,hp,hn⟩
      | false=>
        rw[D2,R,R];refine⟨_,_,rfl,fun r b=>?_,fun r b=>?_⟩
        . change (p0|||((fA (en T i) (1<<<i) w.toNat&&&kI T c i)<<<(1<<<i))).testBit r=H at b;rw[Ay,Ai] at b;rcases b with b|j
          . exact hp r b
          . rw[Nat.testBit_shiftLeft,X,A6] at j;have⟨d,p',hl,h⟩:=j5 hd hi hw j.2;rw[Nat.sub_add_cancel j.1] at hl;have f:r<4096:=hl▸p'.isLt;exact⟨f,⟨r-(1<<<i),d⟩,(Fin.ext hl:p'=⟨r,f⟩)▸h⟩
        . change (n0|||(fA (en T i) (1<<<i) w.toNat&&&kI T c i)).testBit r=H at b;rw[Ay,Ai] at b;rcases b with b|hu
          . exact hn r b
          . have⟨d,p',_,h⟩:=j5 hd hi hw hu;exact⟨d,p',h⟩
   have⟨y,x,hs,v⟩:=l;obtain⟨p,n,he,t⟩:=ih y x k' v;exact⟨p,n,hs.trans he,t⟩
def fY (p n:Nat)(a:Z PP):Y:= List.rec J (fun q _ b=>or (and (not (M (L p q.1) 0)) (not (M (L n q.2) 0))) b) a
lemma kR {p n a}(h:fY p n a=H):∃ q∈a,(p&&&q.1)≠0/\(n&&&q.2)≠0:=by
 induction a with
 | nil=>simp[fY] at h
 | cons q d i=>
   unfold fY at h;dsimp only at h;rw[Ai] at h;rcases h with c|g;. simp only[X,D8] at c;exact⟨q,BJ,fun e=>Bool.noConfusion (c.1.symm.trans (DE.mpr e)),fun e=>Bool.noConfusion (c.2.symm.trans (DE.mpr e))⟩
   . obtain⟨q',f',b⟩:=i g;exact⟨q',AK _ f',b⟩
def so {d:Type}(e:LP)(f:Z W):Z PP->d->(Z kr->d)->d:= List.rec (fun _ _ a=>a []) (fun i _ j b c a=>iS e i 0 0 fun p n=>let h:=and (not (M p 0)) (fY p n b);cond h c (j (cond (M p 0) b ((p,n)::b)) c fun g=>a ((p,n,i)::g))) f
lemma tu {bt:Type}{T:N}{g:Z N}(hd:g.Nodup){a i:LP}(hi:kF T g a i)(b:bt)(d:Z kr->bt) : (so i (g.map (g9 a)) [] b d=b/\∀ (c:Nat) {f:N->Nat},c+g.toFinset.card<=g.length+1->(∀ v∈g.toFinset,f v<c)->fQ g.toFinset T f->False)\/∃ pns,so i (g.map (g9 a)) [] b d=d pns/\Forall₂ (iL T g a) g pns:=by
 suffices ∀ (sub:Z N) (seen:Z PP) (kM:Z kr->bt),sub.Nodup->(∀ w∈sub,w∈g)->(∀ q∈seen,∃ w'∈g,w'∉sub/\iL T g a w' (q.1,q.2,g9 a w'))->(so i (sub.map (g9 a)) seen b kM=b/\∀ (c:Nat) {f:N->Nat},c+g.toFinset.card<=g.length+1->(∀ v∈g.toFinset,f v<c)->fQ g.toFinset T f->False)\/∃ pns,so i (sub.map (g9 a)) seen b kM=kM pns/\Forall₂ (iL T g a) sub pns by
  exact this g [] d hd (fun _ h=>h) (fun _ h=>by simp at h)
 intro sub;induction sub with
 | nil=>intro seen kM _ _ _;exact D6 ⟨[],rfl,Forall₂.nil⟩
 | cons w k ih=>
   intro seen kM hnd hsub e;have⟨h4,t⟩:=B7.mp hnd;set kW:Nat->Nat->bt:=fun p n=>cond (and (not (M p 0)) (fY p n seen)) b (so i (k.map (g9 a)) (cond (M p 0) seen ((p,n)::seen)) b fun pns=>kM ((p,n,g9 a w)::pns));obtain⟨p,n,ha,j⟩:=l7 hd (hsub w BJ) hi kW;have s:so i ((w::k).map (g9 a)) seen b kM=iS i (g9 a w) 0 0 kW:=rfl;rw[s,ha];dsimp only[kW];cases o:and (not (M p 0)) (fY p n seen) with
   | true=>
     left;refine⟨rfl,fun c {f} hcard hg jq=>?_⟩;rw[X] at o;obtain⟨q,m,h5,z⟩:=kR o.2;obtain⟨w',hb,h1,l⟩:=e q m;have hk:w≠w':=fun eq=>h1 (eq▸BJ);obtain⟨rp,x⟩:=fi h5;obtain⟨rn,y⟩:=fi z;rw[Ad,X] at x y;obtain⟨_,na,hA⟩:=j.2.1 rp x.1;obtain⟨_,nb,hB⟩:=l.2.1 rp x.2;obtain⟨_,pa,hC⟩:=j.2.2 rn y.1;obtain⟨_,pb,hD⟩:=l.2.2 rn y.2;have h2:f w=f w':=by rw[Ap hd] at hcard;have fw:=hg w (A4.mpr (hsub w BJ));have fw':=hg w' (A4.mpr hb);omega
     exact jq.1 hk hA hB hC hD h2
   | false=>
     rw[D2];have e':∀ q∈cond (M p 0) seen ((p,n)::seen),∃ w'∈g,w'∉k/\iL T g a w' (q.1,q.2,g9 a w'):=fun q m=>by
      cases h0:M p 0 with
      | true=>rw[h0,D4] at m;obtain⟨w',hm,hn,r'⟩:=e q m;exact⟨w',hm,fun hr=>hn (AK _ hr),r'⟩
      | false=>rw[h0,D2] at m;rcases Ab.mp m with rfl|m;exact⟨w,hsub w BJ,h4,j⟩;obtain⟨w',hm,hn,r'⟩:=e q m;exact⟨w',hm,fun hr=>hn (AK _ hr),r'⟩
     rcases ih _ _ t (fun u hu=>hsub u (AK _ hu)) e' with⟨hh,hf⟩|⟨pns,hm,hp⟩;. exact D5 ⟨hh,hf⟩
     . exact D6 ⟨(p,n,g9 a w)::pns,hm,Forall₂.cons j hp⟩
def k3 {c:Type}(a:LP)(b:Z W)(k:Z kr->c):c:= List.rec (fun k=>k []) (fun d _ e k=>iS a d 0 0 fun p n=>e fun f=>k ((p,n,d)::f)) b k
lemma lW {o:Type}{T:N}{d d':Z N}(m:d.Nodup)(e:∀ w∈d',w∈d){a b:LP}(i:kF T d a b)(k:Z kr->o) : ∃ pns,k3 b (d'.map (g9 a)) k=k pns/\Forall₂ (iL T d a) d' pns:=by induction d' generalizing k with|nil=>exact⟨[],rfl,Forall₂.nil⟩ | cons w c r=>obtain⟨p,n,g,h⟩:=l7 m (e w BJ) i (fun p n=>k3 b (c.map (g9 a)) fun l=>k ((p,n,g9 a w)::l));obtain⟨pns,s,j⟩:=r (fun u q=>e u (AK _ q)) _;have f:k3 b ((w::c).map (g9 a)) k=iS b (g9 a w) 0 0 (fun p n=>k3 b (c.map (g9 a)) fun l=>k ((p,n,g9 a w)::l)):=rfl;exact⟨(p,n,g9 a w)::pns,(by rw[f,g];exact s),Forall₂.cons h j⟩
def k9 {d e:Type}(b:d)(a:Z d):Nat->(d->Z d->e)->e:= List.rec (fun _ k=>k b []) (fun x f g n k=>Nat.rec (k x f) (fun m _=>g m fun y c=>k y (x::c)) n) a
def jv {e f:Type}(c:e)(r:Nat):Z e->Nat->Nat->(Z e->Nat->f)->f:= Nat.rec (fun _ _ s k=>k [] s) (fun _ g a n s k=>E (Dj s n) fun b=>E (DH s n) fun i=>k9 c a b fun x d=>g d (De n 1) i fun h s'=>k (x::h) s') r
lemma lp {h gm s:Type}{m:gm->h->Prop}(f:h){gs:Z gm}{xs:Z h}(hf:Forall₂ m gs xs){b:Nat}(o:b<gs.length)(k:h->Z h->s) : ∃ g x gs' xs',k9 f xs b k=k x xs'/\m g x/\Forall₂ m gs' xs'/\gs'.length+1=gs.length/\(∀ u∈gs',u∈gs)/\g∈gs/\(gs.Nodup->g∉gs'/\gs'.Nodup):=by
 induction hf generalizing b k with
 | nil=>simp at o
 | cons p d w=>
   rename_i g1 x1 gs1 xs1
   cases b with
   | zero=>exact⟨g1,x1,gs1,xs1,rfl,p,d,by simp,fun u i=>AK _ i,BJ,fun e=>B7.mp e⟩
   | succ b=>obtain⟨g,x,gs',xs',z,n,hf',q,a,c,j⟩:=w (by simp at o;omega) _;refine⟨g,x,g1::gs',x1::xs',z,n,Forall₂.cons p hf',by simp;omega,fun u i=>by rcases Ab.mp i with rfl|i;exact BJ;exact AK _ (a u i),AK _ c,fun e=>by obtain⟨r,y⟩:=B7.mp e;obtain⟨t,v⟩:=j y;exact⟨fun l=>by rcases Ab.mp l with rfl|l;exact r c;exact t l,B7.mpr ⟨fun l=>r (a g1 l),v⟩⟩⟩
lemma li {t gm bt:Type}{zr:gm->t->Prop}(c:t)(r:Nat){a:Z gm}{xs:Z t}(hf:Forall₂ zr a xs)(v:a.Nodup)(hd:r<=a.length)(s:Nat)(k:Z t->Nat->bt) : ∃ a' xs' s',jv c r xs a.length s k=k xs' s'/\a'.length=r/\a'.Nodup/\(∀ u∈a',u∈a)/\Forall₂ zr a' xs':=by
 induction r generalizing a xs s k with
 | zero=>exact⟨[],[],s,rfl,rfl,nodup_nil,by simp,Forall₂.nil⟩
 | succ r ih=>
   have p:0<a.length:=(by omega);have hb:Dj s a.length<a.length:=Nat.mod_lt s p;have⟨g,x,o,hj,h1,h0,h3,z,m,j,i⟩:=lp c hf hb (fun x e=>jv c r e (De a.length 1) (DH s a.length) fun xs s'=>k (x::xs) s');obtain⟨l,q⟩:=i v;have f:De a.length 1=o.length:=by change a.length-1=o.length;omega
   obtain⟨y,h5,s',h2,h,n,d,h4⟩:=ih h3 q (by omega) (DH s a.length) (fun xs s'=>k (x::xs) s');refine⟨g::y,x::h5,s',?_,by simp[h],B7.mpr ⟨fun hm=>l (d g hm),n⟩,fun u w=>by rcases Ab.mp w with rfl|w;exact j;exact m u (d u w),Forall₂.cons h0 h4⟩
   change E (Dj s a.length) (fun b=>E (DH s a.length) fun s1=>k9 c xs b fun x e=>jv c r e (De a.length 1) s1 fun xs s'=>k (x::xs) s')=_;rw[R,R,h1,f];exact h2
def hJ (l:Z kr)(i:Nat):kr:=List.rec (fun _=>(0,0,[])) (fun a _ b n=>Nat.rec a (fun m _=>b m) n) l i
lemma lX (l:Z kr)(i:Nat):hJ l i=l.getD i (0,0,[]):=by induction l generalizing i with|nil=>cases i<;>rfl| cons a l b=>cases i with|zero=>rfl| succ i=>exact b i
def kv (c d:Nat)(b:Z kr):Nat->Y:= List.rec (fun _=>H) (fun q _ e a=>cond (M a 0) H (and (cond (M (L a 1) 1) (and (not (M (L c q.1) 0)) (not (M (L d q.2.1) 0))) H) (e (D3 a 1)))) b
def ky (d:Z kr):Nat->W->Y:= List.rec (fun _ _=>H) (fun a as f b c=>List.rec H (fun e c' _=>E (Nat.succ b) fun b'=>and (kv a.1 a.2.1 as (D3 e b')) (f b' c')) c) d
def kQ (d:Z kr)(a:W):Y:=ky d 0 a
lemma lY {c b a bs}(h:kv c b bs a=H){d:Nat}(i:d<bs.length)(f:a.testBit d=H) : (c&&&(bs.getD d (0,0,[])).1)≠0/\(b&&&(bs.getD d (0,0,[])).2.1)≠0:=by
 induction bs generalizing a d with
 | nil=>simp at i
 | cons q bs k=>
   change cond (M a 0) H (and (cond (M (L a 1) 1) (and (not (M (L c q.1) 0)) (not (M (L b q.2.1) 0))) H) (kv c b bs (D3 a 1)))=H at h;cases j:M a 0 with
   | true=>have:=Cl j;subst this;simp at f
   | false=>rw[j,D2,X] at h;cases d with|zero=>have l:M (L a 1) 1=H:=DE.mpr ((eU a).mpr f);have g:=h.1;simp only[l,D4,X,D8] at g;exact⟨fun e=>Bool.noConfusion (g.1.symm.trans (DE.mpr e)),fun e=>Bool.noConfusion (g.2.symm.trans (DE.mpr e))⟩ | succ d=>exact k h.2 (by simp at i;omega) (by change (a>>>1).testBit d=H;rw[Av];simpa[Aw 1 d] using f)
lemma sD {d b}(h:kQ d b=H){i j:Nat}(e:j<d.length)(f:i<j)(c:(b.getD i 0).testBit j=H) : ((d.getD i (0,0,[])).1&&&(d.getD j (0,0,[])).1)≠0/\((d.getD i (0,0,[])).2.1&&&(d.getD j (0,0,[])).2.1)≠0:=by
 suffices ∀ (d0:Z kr) (a:Nat) (ns:W) (i j:Nat),ky d0 a ns=H->j<d0.length->i<j->(ns.getD i 0).testBit (a+j)=H->((d0.getD i (0,0,[])).1&&&(d0.getD j (0,0,[])).1)≠0/\((d0.getD i (0,0,[])).2.1&&&(d0.getD j (0,0,[])).2.1)≠0 by
  exact this d 0 b i j h e f (by simpa using c)
 intro d0;induction d0 with
 | nil=>intro _ _ _ _ _ e;simp at e
 | cons x l m=>
   intro a ns i j h e f c;cases ns with
   | nil=>simp at c
   | cons g ns'=>
     change E (Nat.succ a) (fun idx'=>and (kv x.1 x.2.1 l (D3 g idx')) (ky l idx' ns'))=H at h;rw[R,X] at h;cases i with
     | zero=>
       cases j with|zero=>omega| succ k=>
        simp only[DU,DK] at c ⊢;exact lY h.1 (by simp at e;omega) (by change (g>>>(a+1)).testBit k=H;rw[Av];simpa[show a+1+k=a+(k+1) by omega] using c)
     | succ i=>
       cases j with|zero=>omega| succ j=>
        simp only[DK] at c ⊢;exact m (a+1) ns' i j h.2 (by simp at e;omega) (by omega) (by simpa[show a+1+j=a+(j+1) by omega] using c)
def km (d f h g:Nat)(b:LP):W->Y:= List.rec (fun _=>J) (fun e _ c a=>List.rec J (fun s a' _=>cond (or (M e.2 0) (M s 0)) (c a') (E (L s e.2) fun u=>cond (M u 0) (c a') (or (or (not (M (L (L u (D3 d e.1)) g) 0)) (not (M (L (L u (D3 f e.1)) h) 0))) (c a')))) a) b
lemma sA {T:N}{f:Z N}(y:f.Nodup){k:N}(j:k∈f){a g:LP}(t:kF T f a g){q s v u:Nat}(h:km q s v u g (g9 a k)=H) : ∃ (sh r:Nat) (hr:r<4096) (p:K),p.val=r+sh/\ey f.toFinset T k p ⟨r,hr⟩/\(((q>>>sh).testBit r=H/\u.testBit r=H)\/((s>>>sh).testBit r=H/\v.testBit r=H)):=by
 induction t with
 | nil=>simp[km] at h
 | @cons ef e rest os' h0 _ ih=>
   obtain⟨i,hi,l,w,n⟩:=h0;rcases e with⟨sh,o1⟩;dsimp only at l n;subst l;subst n;subst w;rw[g9,As] at h;unfold km at h;dsimp only at h;cases m:or (M _ 0) (M _ 0) with
   | true=>rw[m,D4] at h;exact ih h
   | false=>
     rw[m,D2,R] at h;cases o:M _ 0 with
     | true=>rw[o,D4] at h;exact ih h
     | false=>
       rw[o,D2,Ai] at h;rcases h with z|hr
       . rw[Ai] at z;rcases z with ha|hb
         . rw[D8] at ha;have c:((fA (en T i) (1<<<i) k.toNat&&&kI T f i)&&&(q>>>(1<<<i)))&&&u≠0:=fun e=>Bool.noConfusion (ha.symm.trans (DE.mpr e));have⟨r,hr⟩:=fi c;rw[Ad,X,Ad,X] at hr;obtain⟨b,p,x,d⟩:=j5 y hi j hr.1.1;exact⟨1<<<i,r,b,p,x,d,D5 ⟨hr.1.2,hr.2⟩⟩
         . rw[D8] at hb;have c:((fA (en T i) (1<<<i) k.toNat&&&kI T f i)&&&(s>>>(1<<<i)))&&&v≠0:=fun e=>Bool.noConfusion (hb.symm.trans (DE.mpr e));have⟨r,hr⟩:=fi c;rw[Ad,X,Ad,X] at hr;obtain⟨b,p,x,d⟩:=j5 y hi j hr.1.1;exact⟨1<<<i,r,b,p,x,d,D6 ⟨hr.1.2,hr.2⟩⟩
       . exact ih hr
def sQ (a:LP)(d:Z kr)(c:Z (Nat×PP)):Y:= List.rec H (fun t _ h=>let(e,i,_):=hJ d t.1;let(f,g,_):=hJ d t.2.1;let(_,_,b):=hJ d t.2.2;and (km e f i g a b) h) c
lemma tS {e d g}(h:sQ e d g=H){a b c:Nat}(k:(a,b,c)∈g) : km (d.getD a (0,0,[])).1 (d.getD b (0,0,[])).1 (d.getD a (0,0,[])).2.1 (d.getD b (0,0,[])).2.1 e (d.getD c (0,0,[])).2.2=H:=by
 induction g with
 | nil=>simp at k
 | cons t f l=>
   rcases t with⟨a',b',c'⟩;change and (km (hJ d a').1 (hJ d b').1 (hJ d a').2.1 (hJ d b').2.1 e (hJ d c').2.2) (sQ e d f)=H at h;rw[X] at h;rcases Ab.mp k with i|j;. cases i;simpa only[lX] using h.1
   . exact l h.2 j
lemma ta {c a:Type}{f:c->a->Prop}(j:c)(g:a){b:Z c}{d:Z a}(h:Forall₂ f b d)(i:Nat)(e:i<b.length):f (b.getD i j) (d.getD i g):=by induction h generalizing i with|nil=>simp at e| cons l _ k=>cases i with|zero=>exact l| succ i=>exact k i (by simp at e;omega)
lemma lr {T:N}{g g':Z N}{h u:LP}{d:Z kr}(c:Q9)(l:Nat){f:N->Nat}(hd:g.Nodup)(hnd':g'.Nodup)(m:∀ w∈g',w∈g)(n:g'.length=c.1)(y:Forall₂ (iL T g h) g' d)(hr:kF T g h u)(hc:uj c)(k:l+g.toFinset.card<=g.length+c.2.1+1)(hg:∀ v∈g.toFinset,f v<l)(jq:fQ g.toFinset T f)(h0:kQ d c.2.2.1=H)(h2:sQ u d c.2.2.2=H):False:=by
 rcases c with⟨q,mr,x0,ts⟩;dsimp only at n k h0 h2;have xa:d.length=q:=y.length_eq.symm.trans n;have e:∀ i (t:i<q),iL T g h (g'.getD i P) (d.getD i (0,0,[])):=fun i t=>ta P (0,0,[]) y i (by omega);rw[Ap hd] at k;apply hc (fun a=>f (g'.getD a P))
 . intro a ha;have hl:=hg (g'.getD a P) (A4.mpr (m _ (by simp[Ah (by omega:a<g'.length)])));omega
 . intro i j t hj hy ht;have⟨hh,h3⟩:=sD h0 (by omega) hy ht;obtain⟨rp,x⟩:=fi hh;obtain⟨rn,w⟩:=fi h3;rw[Ad,X] at x w;obtain⟨_,na,hA⟩:=(e i t).2.1 rp x.1;obtain⟨_,nb,hB⟩:=(e j hj).2.1 rp x.2;obtain⟨_,pa,hC⟩:=(e i t).2.2 rn w.1;obtain⟨_,pb,hD⟩:=(e j hj).2.2 rn w.2;have z:g'.getD i P≠g'.getD j P:=fun eq=>by have t':i<g'.length:=(by omega);have hj':j<g'.length:=(by omega);simp only[A1,Ah t',Ah hj',BS] at eq;exact Qa ((DG hnd').mp eq) (by omega)
   exact jq.1 z hA hB hC hD
 . intro a b c' hf ha hb hc' h1;have o:=tS h2 hf;rw[(e c' hc').1] at o;have hx:g'.getD c' P∈g:=m _ (by simp[Ah (by omega:c' < g'.length)]);have⟨sh,r,x1,p,hl,hC,s⟩:=sA hd hx hr o;rcases s with⟨hp,hn⟩|⟨hp,hn⟩
   . rw[Av] at hp;obtain⟨_,na,hA⟩:=(e a ha).2.1 (sh+r) hp;obtain⟨_,pb,hB⟩:=(e b hb).2.2 r hn;exact jq.2 ((Fin.ext (by dsimp only;rw[Aw,<-hl]):(⟨sh+r,by rw[Aw,<-hl];exact p.isLt⟩:K)=p)▸hA) hB hC h1
   . rw[Av] at hp;obtain⟨_,nb,hB⟩:=(e b hb).2.1 (sh+r) hp;obtain⟨_,pa,hA⟩:=(e a ha).2.2 r hn;exact h1▸jq.2 ((Fin.ext (by dsimp only;rw[Aw,<-hl]):(⟨sh+r,by rw[Aw,<-hl];exact p.isLt⟩:K)=p)▸hB) hA hC h1.symm
structure K1 where
 fmsSh:LP
 ess:Z W
 cs:Nat->Q9
 u:Y
 b:C2
def i1 {l:Type}(p:Nat->Q9)(e:LP)(ess':Z W)(g m s:Nat)(k:Z kr)(c:Y)(a:Nat->l)(f:Y->Nat->l):l:= E (Dj s 12) fun b=>let o:=cond (Db (Nat.succ b) 11) b (Dn 11 (Dj (DH s 12) 128));let j:=cond (Db (Nat.succ b) 11) (DH s 12) (DH s 1536);let(q,t,i,r):=p o;cond (and (Db g (Dn m t)) (Db q m)) (E j fun j=>let h:=fun(d:Z kr) (s':Nat)=>f (and (kQ d i) (sQ e d r)) s';cond c (jv (0,0,[]) q k m j h) (jv [] q ess' m j fun n s'=>k3 e n fun d=>h d s')) (a j)
lemma kK {bt:Type}{T:N}{cs:Nat->Q9}{a:Z N}{l:LP}(j s:Nat)(t:Z kr)(b:Y)(g:Nat->bt)(i:Y->Nat->bt)(he:∀ id,uj (cs id))(nd:a.Nodup)(h5:kF T a (j3 T) l)(ha:b=H->Forall₂ (iL T a (j3 T)) a t) : ∃ ok s',(i1 cs l (a.map (g9 (j3 T))) j a.length s t b g i=g s'/\ok=J\/i1 cs l (a.map (g9 (j3 T))) j a.length s t b g i=i ok s')/\(ok=H->∀ (e:Nat) {f:N->Nat},e+a.toFinset.card<=j+1->(∀ v∈a.toFinset,f v<e)->fQ a.toFinset T f->False):=by
 unfold i1;rw[R];set u:=cond (Db (Nat.succ (Dj s 12)) 11) (Dj s 12) (Dn 11 (Dj (DH s 12) 128));set s1:=cond (Db (Nat.succ (Dj s 12)) 11) (DH s 12) (DH s 1536);rcases hcdef:cs u with⟨q,mr,o,ts⟩;dsimp only;cases m:and (Db j (Dn a.length mr)) (Db q a.length) with
 | false=>exact⟨J,s1,D5 ⟨by simp only[u,s1,hcdef,m,D2],rfl⟩,fun h=>Bool.noConfusion h⟩
 | true=>
   have m':=m;simp only[X,Df,DQ] at m';have⟨hm,y⟩:=m';set h0:Z kr->Nat->bt:=fun d s'=>i (and (kQ d o) (sQ l d ts)) s';have h3:∃ r' d s',(cond b (jv (0,0,[]) q t a.length s1 h0) (jv [] q (a.map (g9 (j3 T))) a.length s1 fun z s'=>k3 l z fun d=>h0 d s'))=h0 d s'/\r'.length=q/\r'.Nodup/\(∀ w∈r',w∈a)/\Forall₂ (iL T a (j3 T)) r' d:=by
    cases b with
    | true=>obtain⟨r',d,s',h2,hl',n',c',p'⟩:=li (0,0,[]) q (ha rfl) nd y s1 _;exact⟨r',d,s',h2,hl',n',c',p'⟩
    | false=>
      have k:Forall₂ (fun w es=>es=g9 (j3 T) w) a (a.map (g9 (j3 T))):=forall₂_map_right_iff.mpr (forall₂_same.mpr fun _ _=>rfl);obtain⟨r',z,s',h2,hl',n',c',k'⟩:=li [] q k nd y s1 _;have x:z=r'.map (g9 (j3 T)):=by clear*- k';induction k' with|nil=>rfl| cons h1 _ ih=>simp[h1,ih]
      obtain⟨d,hj,p'⟩:=lW nd c' h5 _;exact⟨r',d,s',by rw[D2,h2,x,hj],hl',n',c',p'⟩
   obtain⟨r',d,s',hh,hl',n',c',p'⟩:=h3;refine⟨and (kQ d o) (sQ l d ts),s',D6 (by simp only[u,s1,hcdef,m,D4,R];exact hh),fun hbk e {f} hcard hg jq=>?_⟩;rw[X] at hbk;exact lr (q,mr,o,ts) e nd n' c' hl' p' h5 (hcdef▸he u) (by dsimp only;omega) hg jq hbk.1 hbk.2
def k6 (x:K1)(k z i j:Nat)(g f:Y)(s:Nat):Q Nat:= k8 x.b.a4 z x.fmsSh fun e=>let ess':=e::f7 x.ess i j g f;kH x.b.a4 x.fmsSh ess' (some s) fun a=>let m:=Dn 1 (De (De x.b.len (cond g 0 1)) (cond f 0 1));let c:=fun(ok:Y) (s':Nat)=>cond ok (some s') none;cond (Db (Nat.succ k) m) (so a ess' [] (some s) fun d=>i1 x.cs a ess' (Nat.succ k) m s d H (fun _=>none) c) (i1 x.cs a ess' (Nat.succ k) m s [] J (fun _=>none) c)
lemma kN {T:N}{cs:Nat->Q9}{u:Y}{k i j:Nat}(p:Z N)(z:N){o n:Y}{s s':Nat}{b:C2}(hk:b.a4=z4)(hd:b.len=p.length)(hl:∀ id,uj (cs id))(ha:o=J->i<p.length)(hb:n=J->j<p.length)(hm:o=J->n=J->i<j)(nd:(z::f7 p i j o n).Nodup)(h:k6 ⟨j3 T,p.map (g9 (j3 T)),cs,u,b⟩ k z.toNat i j o n s=some s') : if u then u1 J T k (z::f7 p i j o n).toFinset else u2 T k (z::f7 p i j o n).toFinset:=by
 set c:=z::f7 p i j o n;have hg':g9 (j3 T) z::f7 (p.map (g9 (j3 T))) i j o n=c.map (g9 (j3 T)):=by simp only[c,As];congr 1;exact iB _ p i j o n
 have h0:Dn 1 (De (De p.length (cond o 0 1)) (cond n 0 1))=c.length:=by
  simp only[c,AY,f7,gQ];cases o<;>cases n<;>simp[D4,D2,AX,AB,Ak,↓reduceIte]
  . have h1:=hb rfl;have h2:=ha rfl;have h3:=hm rfl rfl;rw[Di (by rw[Di h1];omega),Di h1];omega
  . rw[Di (ha rfl)];omega
  . rw[Di (hb rfl)];omega
  . omega
 unfold k6 at h;simp only[hk,hd,l9] at h;rw[show (j3 T).map (fun ef=>fA ef.2 ef.1 z.toNat)=g9 (j3 T) z from rfl,hg',h0] at h;rcases lL c (sj T) (some s) _ with⟨_,hj⟩|⟨ho,w,hi⟩;. cases u;exact wi hj;exact jK hj
 . rw[w] at h;let xp:=if u then u1 J T k c.toFinset else u2 T k c.toFinset;have l:(∀ (a:Nat) {f:N->Nat},a+c.toFinset.card<=k+2->(∀ v∈c.toFinset,f v<a)->fQ c.toFinset T f->False)->xp:=fun hf=>by
    cases u;intro t ht y;obtain⟨a,f,e,b',g⟩:=ya y;exact hf a (by omega) b' g;intro t ht y;obtain⟨a,f,e,b',g⟩:=iN y;exact hf a (by omega) b' g
   have r:∀ (m:Z kr) (d:Y),(d=H->Forall₂ (iL T c (j3 T)) c m)->i1 cs ho (c.map (g9 (j3 T))) (Nat.succ k) c.length s m d (fun _=>none) (fun ok s'=>cond ok (some s') none)=some s'->xp:=fun m d he hc=>by
    obtain⟨ok,s2,w',hf⟩:=kK (Nat.succ k) s m d (fun _=>none) (fun ok s'=>cond ok (some s') none) hl nd hi he;rcases w' with⟨x,_⟩|x;rw[x] at hc;contradiction;rw[x] at hc;cases ok;contradiction;exact l (hf rfl)
   cases q:Db (Nat.succ k) c.length with
   | false=>rw[q,D2] at h;exact r [] J (fun e=>Bool.noConfusion e) h
   | true=>
     rw[q,D4] at h;have q':=Df.mp q;simp only[DJ] at q';rcases tu nd hi (some s) _ with⟨_,hf⟩|⟨m,h4,hp⟩;. exact l (fun a {f} hcard=>hf a (by omega))
     . rw[h4] at h;exact r m H (fun _=>hp) h
def jN (x:K1)(i j a c k h z f g:Nat)(e d:Y)(s:Nat):Q Nat:= cond (or (kE (fun q=>jx J q a c z e d) x.b.qs) (or (fF x.b.bl z x.b.wsN) (fI x.b.fl x.b.wsN x.b.bl x.b.tot k h z f g (jT z) e d))) (some s) (k6 x (De x.b.cap 1) z i j e d s)
lemma ko {t T r y cs u f m s c st st'}(v:∀ id,uj (cs id))(ho:ff T r y)(d:∀ w∈f,ex r y w)(n:(f.map G).Nodup)(o:0<c)(pv:∀ q∈m,∃ pu p,(u=H\/pu=J)/\fR t T (pu,p)/\lG J (c-1) f p q)(lv:∀ tag ys,s tag=some ys->∃ xs:Z N,ys=xs.map A8/\(if u then u1 J T (c-1) xs.toFinset else u2 T (c-1) xs.toFinset))(x:let cov:=ei H f;let ess:=(f.map G).map (g9 (j3 T))
 iD H J (gO H c f m s) (jN ⟨j3 T,ess,cs,u,gO H c f m s⟩) (f.map (k7 H cov.1.toNat cov.2.1.toNat)) 0 1 st=some st') :
 ∀ a∈f.map G,∀ b∈f.map G,∀ op,eT J op->∀ ka kb,a≠b->V op a b∉f.map G->U (V op a b)->if u then u1 J T (c-1) (eQ (f.map G) a b op ka kb).toFinset
  else u2 T (c-1) (eQ (f.map G) a b op ka kb).toFinset:=
 kG (xp:=fun ls=>if u then u1 J T (c-1) ls.toFinset else u2 T (c-1) ls.toFinset) n x (fun ia ib op ka kb hia hib hlt hop hpro hfr ⟨_,_,hg'⟩=>by
  set a:=f.getD ia C;set b:=f.getD ib C;set z:=ji op a b;set rest:=il f a b ka kb;set e:=z.1::rest.map G
  obtain⟨ha,hb,hab1,jnd,lenE,hce,hnz0,hnz1,hnf⟩:=l8 H ka kb d n hia hib (by omega) hpro hfr
  have hop2':op<2:=(by simpa using hop);have hop2:(op==2)=J:=Bp.mpr fun eq=>by have:=Ar.mp eq;omega
  have heb:eb (op,a.1,b.1)=z.1:=(by simp[eb,hop2,z,ji])
  have hgo:∀ (i:e.length<=c) (l:f8 H (f3 r y) e=AO),if u then u1 J T (c-1) e.toFinset else u2 T (c-1) e.toFinset:=fun i l=>by
   rw[lenE] at i;rw[<-hce] at l;have⟨s1,s2,hcb⟩:=lI i l hnz0 hnz1 hg';unfold jN at hcb;dsimp only[gO,kc] at hcb;rw[hnf,BT] at hcb
   cases hpl:or (kE (fun q=>jx J q (1<<<ia) (1<<<ib) z.1.toNat ka kb) m) (fI s (wN f) (jI (wN f)) (kS (wN f)) a.1.toNat b.1.toNat z.1.toNat (jT a.1.toNat) (jT b.1.toNat) (jT z.1.toNat) ka kb) with
   | true=>
     rcases (Ai _ _).mp hpl with hpool|hlink
     . have⟨q,hq,hfc⟩:=sk.mp hpool;obtain⟨pu,p,hup,hfr',hqok⟩:=pv q hq
       have jnd':(eb (op,a.1,b.1)::rest.map G).Nodup:=heb.symm▸jnd
       simpa[heb,e] using vo hfr' jnd' (lT hup hqok hia hib (by omega) n hop2' hfc)
     . obtain⟨ys,hfl,heq⟩:=ld n ha hb hab1 hlink;obtain⟨xs,hxs,himp⟩:=lv _ _ hfl;rwa[heq xs hxs]
   | false=>
     change cond (or (kE _ m) (fI _ _ _ _ _ _ _ _ _ _ _ _)) _ _=_ at hcb;rw[hpl,D2] at hcb
     have hdel:f7 (f.map G) ia ib ka kb=rest.map G:=by rw[iB,kV n hia hib hlt ka kb]
     simpa only[hdel,Nat.sub_eq] using kN (f.map G) z.1 rfl (by simp[kc,wN]) v (fun _=>by simpa using hia) (fun _=>by simpa using hib) (fun _ _=>hlt) (hdel.symm▸jnd) hcb
  cases u;intro k hk g;have j:=tV g;change e.toFinset.card<=k+1 at j;rw[Ap jnd] at j;change e.length<=k+1 at j;exact hgo (by omega) (y5 g ho) k hk g;intro k hk g;have j:=gz g;change e.toFinset.card<=k+1 at j;rw[Ap jnd] at j;change e.length<=k+1 at j;exact hgo (by omega) (ie g (uX fun h1=>(ho h1).2)) k hk g)
  (fun _ _ he h=>by cases u<;>simpa only[he] using h)
def lf (x:K1)(e:Z iz)(i a f z d:Nat)(c:Y)(s:Nat):Q Nat:= cond (or (kl (fun g=>kz g a z c) e) (or (fF x.b.bl z x.b.wsN) (fI x.b.fl x.b.wsN x.b.bl x.b.tot f 0 z d 0 (jT z) c H))) (some s) (k6 x x.b.cap z i 0 c H s)
def l3 (x:K1)(f:Z iz)(i a g e j h c:Nat)(d:Y)(s:Nat):Q Nat:= cond (Db (Nat.succ (Nat.succ x.b.cap)) (Dn 1 (De x.b.len (cond d 0 1)))) (some s) (E (L (D9 g7 j) h) fun k=>cond (not (M (Dc (cond d x.b.c1 c) k) g7)) (some s) (E (D9 x.b.a4 g) fun z=>lf x f i a g z e d s))
def lJ (x:K1)(c:Z iz)(b:Y)(l:Z kn):Nat->Nat->Nat->Q Nat:= List.rec (fun _ _ s=>some s) (fun w _ m i a s=>let(k,e,j,h,_,d):=w;E (Nat.succ i) fun i'=>E (Dd a 1) fun a'=>Option.rec none (fun f=>E f fun f=>Option.rec none (fun g=>E g fun g=>m i' a' g) (cond b (some f) (l3 x c i a k e j h d H f))) (l3 x c i a k e j h d J s)) l
lemma tb {x c a l b s s'}(h:lJ x c a l b (1<<<b) s=some s'){d:Nat}(e:d<l.length) : let(ax,kwa,p1,q1,_,rsA):=l[d]
 (∃ s1 s2,l3 x c (b+d) (1<<<(b+d)) ax kwa p1 q1 rsA J s1=some s2)/\(a=H\/∃ s1 s2,l3 x c (b+d) (1<<<(b+d)) ax kwa p1 q1 rsA H s1=some s2):=by
 induction l generalizing b s d with|nil=>simp at e| cons w g k=>
  rcases w with⟨ax,kwa,p1,q1,m,rsA⟩;unfold lJ at h;dsimp only at h;rw[R,R,sL] at h;obtain⟨s1,j,h⟩:=kj h;rw[R] at h;obtain⟨s2,i,f⟩:=kj h;rw[R] at f;cases d with|zero=>simp only[Dz,DA];refine⟨⟨s,s1,j⟩,?_⟩;cases a;exact D6 ⟨s1,s2,i⟩;exact D5 rfl | succ d=>simpa only[show b+(d+1)=(b+1)+d by omega,Ds] using k f (by simp at e;omega)
lemma t7 {hj T r sr cs b o s g i f st st'}(hl:∀ id,uj (cs id))(ho:ff T r sr)(d:∀ w∈b,ex r sr w)(nd:(b.map G).Nodup)(hi:i<b.length)(pv:∀ qp∈o,∃ p,fR hj T (qp.1,p)/\lG J (g-1) b p qp.2)(lv:∀ tag ys,s tag=some ys->∃ xs:Z N,ys=xs.map A8/\u1 J T g xs.toFinset)(hfr:neg (b.getD i C).1∉b.map G)(j:let cov:=ei H b;let w1:=k7 H cov.1.toNat cov.2.1.toNat (b.getD i C);let ess:=(b.map G).map (g9 (j3 T))
 l3 ⟨j3 T,ess,cs,H,gO H g b [] s⟩ o i (1<<<i) w1.1 w1.2.1 w1.2.2.1 w1.2.2.2.1 w1.2.2.2.2.2 f st=some st') :
 u1 J T g (neg (b.getD i C).1::(gj b (b.getD i C) f).map G).toFinset:=by
 set a:=b.getD i C;have ha:a∈b:=(by simp[a,Ah hi]);set z:=sV a;set e:=gj b a f;set c:=z.1::e.map G;have sub:=j6 b a f;have n:c.Nodup:=B7.mpr ⟨fun hm=>hfr ((sub.map _).subset hm),nd.sublist (sub.map _)⟩;have hz:1+(b.length-cond f 0 1)=c.length:=(by change _=(z.1::e.map G).length;rw[AY,AQ,Aw 1];cases f<;>simp[e,gj,BH ha]);intro k hk run;have l:=gz run;change c.toFinset.card<=k+1 at l;rw[Ap n] at l;have m:=ie run (uX fun hu=>(ho hu).2);have h4:=vI H e (fun v hv=>d _ (sub.subset hv));have rz:=tQ H a ha f;have hf:=v9 (d _ ha);change eP H (f3 r sr z.1)|||f8 true (f3 r sr) (e.map G)=_ at m;change z.2=f3 r sr z.1 at hf;rw[<-hf,<-h4,rz,Cn] at m;dsimp only at j;simp only[l3,gO,kc,k7,D4,R,si,lS,th,t6,wN,AQ] at j;simp only[lA] at j;rw[show Db (Nat.succ (Nat.succ g)) (Dn 1 (De b.length (cond f 0 1)))=false from Bp.mpr fun h1=>by have:=Df.mp h1;change g+2<=1+(b.length-cond f 0 1) at this;omega,D2,show cond f (ei H b).1.toNat (i7 (ei H b) (eP H a.2)).toNat=(if f then(ei H b).1 else i7 (ei H b) (eP H a.2)).toNat by cases f<;>rfl] at j
 have t:M (Dc (if f then(ei H b).1 else i7 (ei H b) (eP H a.2)).toNat (eP H z.2).toNat) AO.toNat=H:=(by rw[sR,sO,m,beq_self_eq_true]);have ht:fF (jI (wN b)) (neg a.1).toNat (wN b)=J:=Bp.mpr fun j'=>by obtain⟨w,hw,he⟩:=Aj.mp ((hV _ _).mp (gW j'));exact hfr (Do.mp he▸Qm hw)
 change cond (not (M (Dc _ (eP H z.2).toNat) AO.toNat)) _ _=some st' at j;simp only[t,Dw,D2] at j;unfold lf at j;dsimp only[gO,kc] at j;rw[ht,BT] at j;cases h2:or (kl (fun qp=>kz qp (1<<<i) (neg a.1).toNat f) o) (fI s (wN b) (jI (wN b)) (kS (wN b)) a.1.toNat 0 (neg a.1).toNat (jT a.1.toNat) 0 (jT (neg a.1).toNat) f H) with
 | true=>
   rcases (Ai _ _).mp h2 with y|x;. obtain⟨qp,hq,hr⟩:=sH.mp y;obtain⟨p,hfr',h5⟩:=pv qp hq;have h3:eb (2,a.1,P)=neg a.1:=(by simp[eb]);have n':(eb (2,a.1,P)::e.map G).Nodup:=(by simpa[h3,c,z,sV] using n);simpa[h3] using vo (u:=H) hfr' n' (lQ h5 hi hr) k hk run
   . obtain⟨ys,hx,hp⟩:=lR nd ha x;obtain⟨xs,hs,hc⟩:=lv _ _ hx;exact hc k hk (hp xs hs▸run)
 | false=>
   change cond (or (kl _ o) (fI _ _ _ _ _ _ _ _ _ _ _ _)) _ _=_ at j;rw[h2,D2] at j;have q:f7 (b.map G) i 0 f H=e.map G:=by rw[iB];change (gK b i f).map G=_;rw[hN nd hi f]
   exact(by simpa only[q,AX,c,z,sV] using kN (b.map G) (neg a.1) rfl (by simp) hl (fun _=>by simpa using hi) (fun h=>Bool.noConfusion h) (fun _ h=>Bool.noConfusion h) (q.symm▸n) j:u1 J T g c.toFinset) k hk run
def t0 (x tN:Nat)(n:Z D)(c:LP)(cs:Nat->Q9)(d:Z kC)(ab:Z W)(g:Qf)(k i:Nat):Y:= let(_,e,_,_):=g.t k;let(l,o,m,h,r):=gF J n g H k i;E l fun l=>E r fun r=>lP o fun o=>lP m fun m=>ip (fun w:D=>w.1.toNat) m fun a=>E (jI a) fun bl=>ip (fun w:D=>w.1.toNat) o fun u=>E (kS a) fun s=>let f:=ei H m;E f.1.toNat fun y=>E f.2.1.toNat fun z=>E f.2.2.toNat fun c3=>s9 (bQ J (De k 1) a d l e u h) fun qs=>kf H y z m fun p=>iV x c a fun v=>let b:=kc x k a bl s y z c3 qs (fun q=>(g.j k q).bind (eG J g H (De k 1) ab));and (sM a) (and (not (fX tN a)) (cond (M k 0) H (Option.rec J (fun _=>H) (iD H J b (jN ⟨c,v,cs,H,b⟩) p 0 1 r))))
def tc (a4 tN:Nat)(h2:Z D)(b:LP)(cs:Nat->Q9)(l:Z kC)(ab:Z W)(g:Qf)(k i:Nat):Y:= let(_,r,_,_):=g.f k;let(q,bk,ws,s,a):=gF J h2 g J k i;E q fun q=>E a fun a=>lP bk fun bk=>lP ws fun ws=>ip (fun w:D=>w.1.toNat) ws fun c=>E (jI c) fun bl=>ip (fun w:D=>w.1.toNat) bk fun h5=>E (kS c) fun z=>let v:=ei H ws;E v.1.toNat fun c1=>E v.2.1.toNat fun c2=>E v.2.2.toNat fun c3=>k0 (bQ J (De k 1) c l q r h5 s) fun p j=>kf H c1 c2 ws fun x=>iV a4 b c fun h=>let bF:=kc a4 k c bl z c1 c2 c3 j (fun o=>(g.i k o).bind (eG J g J (De k 1) ab));let xN:K1:=⟨b,h,cs,H,kc a4 k c bl z c1 c2 c3 [] (fun o=>(g.n k o).bind (eG J g H k ab))⟩;let e:=fun(d:Y) (u:Nat)=>j4 d fun d=>E u fun u=>Option.rec J (fun t=>E t fun t=>cond (M k 0) H (Option.rec J (fun _=>H) (iD H J bF (jN ⟨b,h,cs,J,bF⟩) x 0 1 t))) (lJ xN p d x 0 1 u);and (sM c) (and (not (fX tN c)) (cond (M (L a 1) 0) (e J (D3 a 1)) (kH a4 b h H fun y=>let m:=c.length;cond (M (L (D3 a 1) 1) 1) (cond (Db k m) (so y h [] (e H (D3 a 2)) fun _=>e J (D3 a 2)) (e J (D3 a 2))) (i1 cs y h k m (D3 a 2) [] J (e J) e))))
lemma hO (f:Nat->Q9)(m:∀ id,uj (f id))(g:Qf)(k i:Nat)(e:ff (uf g) (fq fun j=>(eH J g.m j).1) (fq fun j=>(eH J g.m j).2))(h3:∀ ci∈g.o,sN (eu (g4 g.m ci)) (uf g) (g5 ci.1 ci.2.1) ci.2.2.2.2)(l:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H)(n:k>0->∀ idx < (g.t (k-1)).1,u1 J (uf g) (k-1) (eA J g H (k-1) idx).toFinset)(c:t0 z4 (uf g).toNat (eF J g) (j3 (uf g)) f (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H) : u1 J (uf g) k (eA J g H k i).toFinset:=by
 unfold t0 at c;set rn:=gF J (eF J g) g H k i;set ws:=rn.2.2.1;simp only[R,lM,kg,sa,kx,ki,X,sK,D8] at c;obtain⟨he,hT',s⟩:=c;obtain⟨h5,hT⟩:=kA he hT';by_cases h0:k=0;. subst k;intro t ht x;have:t=0:=(by omega);subst this;exact hT (A4.mp (x.1▸Ao _))
 . have r:0<k:=(by omega);rw[show M k 0=J from Bp.mpr fun eq=>h0 (Cl eq),D2] at s;cases z:iD H J _ _ _ 0 1 rn.2.2.2.2 with|none=>rw[z] at s;contradiction| some st'=>
   have q:∀ w∈ws,ex (fq fun j=>(eH J g.m j).1) (fq fun j=>(eH J g.m j).2) w:=fun w hw=>h9 J _ _ _ _ _ (gU J g) w ((it _ _).subset hw);have h1:∀ o ys,((g.j k o).bind (eG J g H (k-1) (g.a.map (iO g.m))))=some ys->∃ xs:Z N,ys=xs.map A8/\(if H then u1 J (uf g) (k-1) xs.toFinset else u2 (uf g) (k-1) xs.toFinset):=fun o ys h=>by have⟨_,_,y⟩:=At.mp h;exact gS g H (k-1) l (n r) y
   have v:(wN ws).map (fun w=>(j3 (uf g)).map fun ef=>fA ef.2 ef.1 w)=(ws.map G).map (g9 (j3 (uf g))):=(by simp[wN,g9,DI])
   set qs:=(bQ J (k-1) (wN ws) (g.o.map (fN g.m)) rn.1 (g.t k).2.1 (wN rn.2.1) rn.2.2.2.1).map Prod.snd;rw[show (ws.map fun w:D=>w.1.toNat).map (fun w=>(j3 (uf g)).map fun ef=>fA ef.2 ef.1 w)=(ws.map G).map (g9 (j3 (uf g))) from v] at z;have hk:∀ q'∈qs,∃ pu p,(H=H\/pu=J)/\fR (h7 g.m) (uf g) (pu,p)/\lG J (k-1) ws p q':=fun q' hq'=>by
    obtain⟨qp,hh,rfl⟩:=Aj.mp hq';obtain⟨p,hi,hc⟩:=sx h3 hh;exact⟨qp.1,p,D5 rfl,hi,hc⟩
   apply vq h5 hT;intro a ha b hb d hd ka kb ne fr hl _;exact ko (u:=H) m e q h5 r hk h1 z a ha b hb d hd ka kb ne fr hl
lemma hY (m:Nat->Q9)(n:∀ id,uj (m id))(g:Qf)(k i:Nat)(o:ff (uf g) (fq fun j=>(eH J g.m j).1) (fq fun j=>(eH J g.m j).2))(x9:∀ ci∈g.o,sN (eu (g4 g.m ci)) (uf g) (g5 ci.1 ci.2.1) ci.2.2.2.2)(z:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H)(hf:∀ idx < (g.t k).1,u1 J (uf g) k (eA J g H k idx).toFinset)(he:k>0->∀ idx < (g.f (k-1)).1,u2 (uf g) (k-1) (eA J g J (k-1) idx).toFinset)(l:tc z4 (uf g).toNat (eF J g) (j3 (uf g)) m (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H) : u2 (uf g) k (eA J g J k i).toFinset:=by
 unfold tc at l;set rn:=gF J (eF J g) g J k i;simp only[R,lM,kg,l5,kx,ki] at l;set T:=uf g;set ab:=g.a.map (iO g.m);set ws:=rn.2.2.1;set e:=ws.map G;set y:=rn.2.2.2.2;set yp:=ei H ws;set h3:=bQ J (De k 1) (wN ws) (g.o.map (fN g.m)) rn.1 (g.f k).2.1 (wN rn.2.1) rn.2.2.2.1;set hv:=h3.filterMap fun qp=>if qp.1 then none else some qp.2;set r:=ws.map (k7 H yp.1.toNat yp.2.1.toNat);set x4:=e.map (g9 (j3 T));rw[show (ws.map fun w:D=>w.1.toNat).map (fun w=>(j3 T).map fun ef=>fA ef.2 ef.1 w)=x4 by simp only[x4,e,g9,C4,DI]] at l
 set bF:=gO H k ws hv (fun xf=>(g.i k xf).bind (eG J g J (De k 1) ab));set xN:K1:=⟨j3 T,x4,m,H,gO H k ws [] (fun xf=>(g.n k xf).bind (eG J g H k ab))⟩;set hi:Y->Nat->Y:=fun ok s1=>j4 ok fun c=>Option.rec J (fun xe=>cond (M k 0) H (Option.rec J (fun _=>H) (iD H J bF (jN ⟨j3 T,x4,m,J,bF⟩) r 0 1 xe))) (lJ xN h3 c r 0 1 s1);have x1:∀ q'∈hv,∃ pu p,(J=H\/pu=J)/\fR (h7 g.m) T (pu,p)/\lG J (k-1) ws p q':=fun q' hq'=>by
  obtain⟨⟨pu,q0⟩,hmem,hu⟩:=Bw.mp hq';cases pu;simp only[Ak,↓reduceIte,Dl] at hu;subst hu;have⟨p,z9,yr⟩:=sx x9 hmem;exact⟨J,p,D6 rfl,z9,yr⟩;simp at hu
 simp only[X,sK,D8] at l;have⟨yo,hT',l⟩:=l;obtain⟨x2,hT⟩:=kA yo hT';have xb:e.Nodup:=x2;have h2:∀ (c:Y) (xj:Nat),(c=H->∀ t ≤ k,∀ (zu:I N) (a:N),e.toFinset=insert a zu->a∈zu->ec a->neg a∉insert a zu->¬Lv J T t (insert (neg a) zu))->hi c xj=H->u2 T k e.toFinset:=fun c xj x0 h=>by
  simp only[hi,kh] at h;cases yn:lJ xN h3 c r 0 1 xj with|none=>rw[yn] at h;contradiction| some xe=>
   rw[yn] at h;dsimp only at h;have s:∀ w∈ws,ex (fq fun j=>(eH J g.m j).1) (fq fun j=>(eH J g.m j).2) w:=fun w hw=>h9 J _ _ _ _ _ (gU J g) w ((it _ _).subset hw);have hh:∀ v ys,((g.n k v).bind (eG J g H k ab))=some ys->∃ xs:Z N,ys=xs.map A8/\u1 J T k xs.toFinset:=fun v ys h=>by have⟨_,_,hl⟩:=At.mp h;exact gS g H k z hf hl
   have xc:∀ (a:D) (ra:a∈ws) (h4:neg a.1∉e) (ka:Y),(ka=J\/(ka=H/\c=J))->u1 J T k (neg a.1::(gj ws a ka).map G).toFinset:=fun a ra h4 ka z7=>by
    obtain⟨ia,hr,zd⟩:=DT ra;have yx:=tb yn (by simpa[r] using hr);obtain⟨_,_,h0⟩:∃ s1 s2,l3 xN h3 (0+ia) (1<<<(0+ia)) (r[ia]'(by simpa[r] using hr)).1 (r[ia]'(by simpa[r] using hr)).2.1 (r[ia]'(by simpa[r] using hr)).2.2.1 (r[ia]'(by simpa[r] using hr)).2.2.2.1 (r[ia]'(by simpa[r] using hr)).2.2.2.2.2 ka s1=some s2:=by cases ka;exact yx.1;exact z7.elim (fun h1=>Bool.noConfusion h1) fun hb=>yx.2.elim (fun hb'=>by rw[hb.2] at hb';contradiction) id
    rw[C1] at h0;simp only[r,xN,DO] at h0;have yv:ws.getD ia C=a:=(by simp[Ah hr,zd]);rw[show ws[ia]=ws.getD ia C by simp[Ah hr]] at h0
    have hc:=t7 n o s x2 hr (fun _ hp=>sx x9 hp) hh (yv.symm▸h4) h0;rwa[yv] at hc
   apply yi x2 hT
   . intro a ha b hb d hd ka kb ne hj hy ho;by_cases h0:k=0
     . subst k;simp[eQ] at ho
     . have hg:0<k:=(by omega);rw[show M k 0=J from Bp.mpr fun eq=>h0 (Cl eq),D2] at h;cases yu:iD H J bF _ r 0 1 xe with|none=>rw[yu] at h;contradiction| some a0=>
       exact ko (u:=J) n o s x2 hg x1 (fun v ys h=>by have⟨_,_,hl⟩:=At.mp h;exact gS g J (k-1) z (he hg) hl) yu a ha b hb d (D5 hd) ka kb ne hj hy
   . intro a ha h4 _ _ _;obtain⟨a,ra,rfl⟩:=Aj.mp ha;exact(by simp only[Bi,e,wr x2 ra]:(neg a.1::e.erase a.1).toFinset=(neg a.1::(gj ws a J).map G).toFinset)▸xc a ra h4 J (D5 rfl)
   . intro a ha h4 _ hn _ t ht zu h5 hk' hz;obtain⟨a,ra,rfl⟩:=Aj.mp ha;cases x0':c
     . have hU:zu=e.toFinset:=(by rw[h5,Cd hk']);exact xc a ra h4 H (D6 ⟨rfl,x0'⟩) t ht ((by simp[gj,hU,e]:insert (neg a.1) zu=(neg a.1::(gj ws a H).map G).toFinset)▸hz)
     . exact x0 x0' t ht zu a.1 h5 hk' hn (h5▸fun hm'=>h4 (A4.mp hm')) hz
 have x3:(∀ (x:Nat) {f:N->Nat},x+e.toFinset.card<=k+1->(∀ v∈e.toFinset,f v<x)->fQ e.toFinset T f->False)->∀ t ≤ k,∀ (zu:I N) (a:N),e.toFinset=insert a zu->a∈zu->ec a->neg a∉insert a zu->¬Lv J T t (insert (neg a) zu):=fun hf t ht zu a xa z5 zb x7 hz=>by
  obtain⟨x,f,d,b,g'⟩:=h6 zb x7 hz;rw[if_pos z5,<-xa] at d;rw[<-xa] at b g';exact hf x (by omega) b g'
 cases h0:M (L y 1) 0 with
 | true=>simp only[h0,D4] at l;exact h2 J (D3 y 1) (fun h=>Bool.noConfusion h) l
 | false=>
   simp only[h0,D2] at l;rcases lL e (sj T) H _ with⟨_,zc⟩|⟨zt,hu,yt⟩;. exact wi zc
   . rw[hu,show (ws.map fun w:D=>w.1.toNat).length=e.length by simp[e]] at l
     cases h1:M (L (D3 y 1) 1) 1 with
     | true=>
       simp only[h1,D4] at l;cases x6:Db k e.length with
       | false=>rw[x6,D2] at l;exact h2 J (D3 y 2) (fun h=>Bool.noConfusion h) l
       | true=>
         rw[x6,D4] at l;have x6':=Df.mp x6;rcases tu xb yt _ _ with⟨yw,hf⟩|⟨_,xp,_⟩;. rw[yw] at l;exact h2 true _ (fun _=>x3 fun x {f} hc=>hf x (by omega)) l
         . rw[xp] at l;exact h2 J _ (fun h=>Bool.noConfusion h) l
     | false=>
       simp only[h1,D2] at l;have⟨ok,s',hu',hf⟩:=kK k (D3 y 2) [] J (hi J) hi n xb yt (fun h=>Bool.noConfusion h);rcases hu' with⟨xg,rfl⟩|xg;. rw[xg] at l;exact h2 false s' (fun h=>Bool.noConfusion h) l
       . rw[xg] at l;exact h2 ok s' (fun x0=>x3 (hf x0)) l
def lq (d:LP)(g:Qf)(f:Nat->Nat->Z D->LP->Z kC->Z W->Y):Y:= E z4 fun i=>E (uf g).toNat fun j=>lP (eF J g) fun e=>kZ d fun b=>lg g.m g.o fun c=>hP g.m g.a fun h=>f i j e b c h
lemma kq (b:LP)(g:Qf)(f:Nat->Nat->Z D->LP->Z kC->Z W->Y) : lq b g f=f z4 (uf g).toNat (eF J g) (b.map fun p=>(1<<<p.1,p.2)) (g.o.map (fN g.m)) (g.a.map (iO g.m)):=by simp[lq,R,lM,s5,lB,k4]
def uK (fms:LP)(cs:Nat->Q9)(g:Qf)(k st n:Nat):Y:=lq fms g fun a4 tN raw fmsSh colsN ab=>fB (t0 a4 tN raw fmsSh cs colsN ab g k) st n
def uL (fms:LP)(cs:Nat->Q9)(g:Qf)(k st n:Nat):Y:=lq fms g fun a4 tN raw fmsSh colsN ab=>fB (tc a4 tN raw fmsSh cs colsN ab g k) st n
lemma u8 {fms cs g k st a b}(h1:uK fms cs g k st a=H)(h2:uK fms cs g k (st+a) b=H):uK fms cs g k st (a+b)=H:=by simp only[uK,kq] at h1 h2 ⊢;exact iH h1 h2
lemma u9 {fms cs g k st a b}(h1:uL fms cs g k st a=H)(h2:uL fms cs g k (st+a) b=H):uL fms cs g k st (a+b)=H:=by simp only[uL,kq] at h1 h2 ⊢;exact iH h1 h2
def ul (fms:LP)(cs:Nat->Q9)(g:Qf)(k:Nat):Prop:=∀ i < (g.t k).1,t0 z4 (uf g).toNat (eF J g) (fms.map fun p=>(1<<<p.1,p.2)) cs (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H
def um (fms:LP)(cs:Nat->Q9)(g:Qf)(k:Nat):Prop:=∀ i < (g.f k).1,tc z4 (uf g).toNat (eF J g) (fms.map fun p=>(1<<<p.1,p.2)) cs (g.o.map (fN g.m)) (g.a.map (iO g.m)) g k i=H
lemma uM {fms cs g k n}(h:uK fms cs g k 0 n=H)(e:(g.t k).1=n):ul fms cs g k:=fun i hi=>by simp only[uK,kq] at h;exact fP h i (AU _) (by omega)
lemma uN {fms cs g k n}(h:uL fms cs g k 0 n=H)(e:(g.f k).1=n):um fms cs g k:=fun i hi=>by simp only[uL,kq] at h;exact fP h i (AU _) (by omega)
def ua (fms:LP)(cs:Nat->Q9)(g:Qf)(ks:W):Y:=lq fms g fun a4 tN raw fmsSh colsN ab=>ks.all fun k=>fB (t0 a4 tN raw fmsSh cs colsN ab g k) 0 (g.t k).1
def ub (fms:LP)(cs:Nat->Q9)(g:Qf)(ks:W):Y:=lq fms g fun a4 tN raw fmsSh colsN ab=>ks.all fun k=>fB (tc a4 tN raw fmsSh cs colsN ab g k) 0 (g.f k).1
lemma uc {fms cs g ks}(h:ua fms cs g ks=H)(k:Nat)(hk:k∈ks):ul fms cs g k:=fun i hi=>by simp only[ua,kq] at h;exact fP (Ae.mp h k hk) i (AU _) (by simpa using hi)
lemma ud {fms cs g ks}(h:ub fms cs g ks=H)(k:Nat)(hk:k∈ks):um fms cs g k:=fun i hi=>by simp only[ub,kq] at h;exact fP (Ae.mp h k hk) i (AU _) (by simpa using hi)
def t1 (a:LP)(c:Nat->Q9)(g:Qf)(b:Nat):Y:=ua a c g (range (b+1))
def tz (a:LP)(c:Nat->Q9)(g:Qf)(b:Nat):Y:=ub a c g (range (b+1))
lemma te {a c g b}(h:t1 a c g b=H):∀ k ≤ b,ul a c g k:=fun k d=>uc h k (AM.mpr (by omega))
lemma t8 {a c g b}(h:tz a c g b=H):∀ k ≤ b,um a c g k:=fun k d=>ud h k (AM.mpr (by omega))
def uo (g:Qf)(prior:NN):Y:=tH (j9 J g.m) fun arr=>(fT g.m (fun j=>(arr.getD j (0,0)).1)==AO)&&(fT g.m (fun j=>(arr.getD j (0,0)).2)==0)&&iG (fun j=>(arr.getD j (0,0)).1) (fun j=>(arr.getD j (0,0)).2)&&g.o.all (fun c=>hZ g.m c prior)&&g.a.all (fun p=>p.all eO&&hG (uf g) (p.map eo))
lemma xB (b:Nat->Q9)(c:∀ id,uj (b id))(g:Qf)(m:Nat)(l:NN)(n:∀ q,fH (eu q) (e6 q) (l q))(f:uo g l=H)(s:∀ k ≤ m,ul (fO (uf g)) b g k)(t:∀ k ≤ m,um (fO (uf g)) b g k):∀ k ≤ m,(∀ idx < (g.t k).1,u1 J (uf g) k (eA J g H k idx).toFinset)/\(∀ idx < (g.f k).1,u2 (uf g) k (eA J g J k idx).toFinset):=by
 simp only[uo,tj,X,Ae,Ar] at f;have a:ff (uf g) (fq fun j=>(eH J g.m j).1) (fq fun j=>(eH J g.m j).2):=fun i=>⟨yk f.1.1.2 i,w9 f.1.1.1.1 f.1.1.1.2 i⟩;have h:∀ v∈g.o,sN (eu (g4 g.m v)) (uf g) (g5 v.1 v.2.1) v.2.2.2.2:=fun v u=>wL v l n (f.1.2 v u);have d:∀ p∈g.a,p.all eO=H/\hG (uf g) (p.map eo)=H:=fun p x=>by simpa[X] using f.2 p x
 intro k;induction k with
 | zero=>
   intro hk;have w:∀ idx < (g.t 0).1,u1 J (uf g) 0 (eA J g H 0 idx).toFinset:=fun idx e=>
    hO b c g 0 idx a h d (by omega) (s 0 hk idx e)
   exact⟨w,fun idx e=>hY b c g 0 idx a h d w (by omega) (t 0 hk idx e)⟩
 | succ k y=>
   intro hk;obtain⟨r,o⟩:=y (by omega);have w:∀ idx < (g.t (k+1)).1,u1 J (uf g) (k+1) (eA J g H (k+1) idx).toFinset:=fun idx e=>
    hO b c g (k+1) idx a h d (fun _=>r) (s (k+1) hk idx e)
   exact⟨w,fun idx e=>hY b c g (k+1) idx a h d w (fun _=>o) (t (k+1) hk idx e)⟩
def gN (g:Qf)(k i:Nat)(a:Z N):Y:=decide (i<(g.f k).1)&&jC (eA J g J k i) a
lemma ur {cores g top prior k i ws}(hcores:∀ id,uj (cores id))(lower:∀ q,fH (eu q) (e6 q) (prior q))(geom:uo g prior=H)(hIT:∀ j ≤ top,ul (fO (uf g)) cores g j)(hIF:∀ j ≤ top,um (fO (uf g)) cores g j)(le:k<=top)(idx:gN g k i ws=H):u2 (uf g) k ws.toFinset:=by simp only[gN,X,A6] at idx;rw[<-jd idx.2];exact(xB cores hcores g top prior lower geom hIT hIF k le).2 i idx.1
lemma vu {l g n i o}(b:∀ id,uj (l id))(h:∀ q,fH (eu q) (e6 q) (n q))(c:uo g n=H)(f:∀ j ≤ g.cap,ul (fO (uf g)) l g j)(k:∀ j ≤ g.cap,um (fO (uf g)) l g j)(e:gN g g.cap i (h7 g.m)=H)(r:eD (uf g)=H)(d:el (uf g) (h7 g.m) (eg g.m o)=H)(p:(eg g.m o).map G=h7 g.m):fH (h7 g.m) (uf g) (g.cap+1):=by apply wl (eJ _ r) (vK g.m) _ (ur b h c f k (BA _) e);intro a ha;apply ga d a;rw[p];exact A4.mpr ha
abbrev vv (m a:Nat):=fH (eu m) (e6 m) a
def ui (entries:LP):=∀ e∈entries,fH (eu e.1) (e6 e.1) e.2
lemma jB {m b c}(h:vv m b)(a:ui c):ui ((m,b)::c):=by
 intro e he;rcases Ab.mp he with rfl|h';. exact h
 . exact a e h'
lemma ue {es}(h:uh H es):ui es:=fun e he=>xD (h e he)
lemma uR (entries:LP)(sound:ui entries)(q:Nat):fH (eu q) (e6 q) (bB entries q):=by unfold bB;cases h:entries.find? (fun a=>a.1==q) with|none=>exact fun _ _ _ _ _=>AU _ | some e=>have c:=E6 h;have b:e.1=q:=Ar.mp (find?_some (p:=fun a:PP=>a.1==q) (a:=e) h);simpa only[BU,BS,b] using sound e c
def vU:Nat->Nat->W
 | 0,_=>[]
 | n+1,v=>if v==0 then [] else(v&&&255)::vU n (v>>>8)
def dA (xs:W):Z (W):=xs.map (vU 12)
def vH:Nat->Nat->PP
 | 0,_=>(0,0)
 | k+1,x=>
   let(z,o):=vH k (x / 3)
   let d:=x%3
   (z*2+(if d==1 then 1 else 0),o*2+(if d==2 then 1 else 0))
def wC (x:Nat):Nat:=(range 12).countP fun i=>x.testBit i
def xu (o:Nat):Nat:=(range 12).foldl (fun a i=>if o.testBit i then a|||sJ i else a) 0
def wK (a:Nat):Nat:=(range 12).foldl (fun b i=>if a.testBit i&&((sJ i&&&a) !=0) then b|||(1<<<i) else b) 0
def uz (m:Nat)(prior:NN):Nat->Nat->Z gu
 | 0,_=>[]
 | n+1,v=>
   let(z,o):=vH 12 (v%531441)
   let free:=m&&&(4095^^^(z|||o))
   let s:=xu o&&&free
   let q:=wK (free&&&(4095^^^s))
   let sc:=wC s
   let zl:=if q==0 then sc-1 else prior q+sc
   (z,o,q,s,zl)::uz m prior n (v / 531441)
def vF:Nat->Nat->W×Nat
 | 0,v=>([],v)
 | n+1,v=>
   let(rest,tail):=vF n (v>>>8)
   ((v&&&255)::rest,tail)
def fG (a:Nat):Nat->Nat->Z (Nat×Nat×W)
 | 0,_=>[]
 | n+1,v=>
   let r:=if(v&&&1)==0 then a else(v>>>1)%4096
   let b:=if(v&&&1)==0 then v>>>1 else v>>>13
   let m:=b%4096
   let k:=(b>>>12)%16
   let(c,d):=vF k (b>>>16)
   (m,r,c)::fG r n d
def gn:Z (Nat×Nat×W)->Y
 | []=>H
 | (m,r,sw)::rest=>t4 m r sw&&gn rest
def vp (ks:LP):Z (Nat×Nat×W)->LP
 | []=>ks
 | (m,r,_)::rest=>(m,bB ks r)::vp ks rest
def uE (ks:LP)(n v:Nat):LP:=vp ks (fG 0 n v)
lemma u6 {u ks n v}(hk:uh u ks)(hok:gn (fG 0 n v)=H):uh u (uE ks n v):=by
 unfold uE;generalize fG 0 n v=cs at hok ⊢;induction cs with
 | nil=>exact hk
 | cons e a b=>rcases e with⟨m,r,c⟩;simp only[gn,X] at hok;exact uu (xJ hok.1 (bS ks hk r)) (b hok.2)
lemma u7 {ks n v}(hk:ui ks)(hok:gn (fG 0 n v)=H):ui (uE ks n v):=by
 unfold uE;generalize fG 0 n v=cs at hok ⊢;induction cs with
 | nil=>exact hk
 | cons e a b=>rcases e with⟨m,r,c⟩;simp only[gn,X] at hok;exact jB (xE hok.1 (uR ks hk r)) (b hok.2)
def ig (c:LP):W->Y
 | []=>H
 | v::rest=>
   let m:=v%4096
   let q:=(v>>>12)%4096
   let d:=(v>>>24)%64
   let b:=v>>>30
   let a:=m^^^q
   gH (j8 a 0) (e6 m) (eu m) (eu q) (e6 q) (eg a b) &&
   eD (e6 m)&&eD (e6 q) &&
   decide ((List.map G (eg a b)).Nodup) &&
   decide (d<=bB c q+(eg a b).length) &&
   ig ((m,d)::c) rest
def aD (ks:LP):W->LP
 | []=>ks
 | v::rest=>aD ((v%4096,(v>>>24)%64)::ks) rest
lemma uG {u ks ds}(hk:uh u ks)(hok:ig ks ds=H):uh u (aD ks ds):=by
 induction ds generalizing ks with
 | nil=>exact hk
 | cons v b c=>
   simp only[ig,X,A6] at hok;have a:(List.map G (eg (v%4096^^^(v>>>12)%4096) (v>>>30))).toFinset.card = (eg (v%4096^^^(v>>>12)%4096) (v>>>30)).length:=(by rw[Ap hok.1.1.2,AQ])
   have d:w5 u (v%4096) ((v>>>24)%64):=yh (v%4096^^^(v>>>12)%4096) (v>>>30) (bS ks hk ((v>>>12)%4096))
    hok.1.1.1.1.1 hok.1.1.1.1.2 hok.1.1.1.2 (a▸hok.1.2)
   exact c (uu d hk) hok.2
lemma uH {ks ds}(hk:ui ks)(hok:ig ks ds=H):ui (aD ks ds):=by
 induction ds generalizing ks with
 | nil=>exact hk
 | cons v b c=>
   simp only[ig,X,A6] at hok;have a:(List.map G (eg (v%4096^^^(v>>>12)%4096) (v>>>30))).toFinset.card = (eg (v%4096^^^(v>>>12)%4096) (v>>>30)).length:=(by rw[Ap hok.1.1.2,AQ])
   have d:vv (v%4096) ((v>>>24)%64):=y0 (v%4096^^^(v>>>12)%4096) (v>>>30) (uR ks hk ((v>>>12)%4096))
    hok.1.1.1.1.1 hok.1.1.1.1.2 hok.1.1.1.2 (a▸hok.1.2)
   exact c (jB d hk) hok.2
lemma ux {coreData:NN}{st len:Nat}(h:(range len).all (fun d=>let c:=uA (coreData (st+d));decide (c.1<=12)&&us c.1 c.2.1 c.2.2.1 c.2.2.2)=H)
 {id:Nat} (hlo:st<=id) (hhi:id<st+len) :
 uj (uA (coreData id)):=by
 have a:=Ae.mp h (id-st) (AM.mpr (by omega));simp only[Nat.add_sub_cancel' hlo,X,A6] at a;exact xh a.1 a.2
lemma uJ {cores g ks}(hints:Nat)(hcv:∀ id,uj (cores id))(hk:ui ks)(hgm:uo g (bB ks)=H)(hT:∀ j ≤ g.cap,ul (fO (uf g)) cores g j)(hF:∀ j ≤ g.cap,um (fO (uf g)) cores g j)(hok:(gN g g.cap 0 (h7 g.m)&&eD (uf g)&&el (uf g) (h7 g.m) (eg g.m hints)&&decide ((eg g.m hints).map G=h7 g.m))=H):ui ((g.m,g.cap+1)::ks):=by simp only[X,A6] at hok;exact jB (vu hcv (uR ks hk) hgm hT hF hok.1.1.1 hok.1.1.2 hok.1.2 hok.2) hk
lemma u4 {g ks}(hints:Nat)(hk:uh H ks)(hok:(un g (bB ks)&&w6 g g.cap&&fV g g.cap 0 (h7 g.m)&&eD (uf g)&&el (uf g) (h7 g.m) (eg g.m hints)&&decide ((eg g.m hints).map G=h7 g.m))=H):uh H ((g.m,g.cap+1)::ks):=by simp only[X,A6] at hok;exact uu (jn (bS ks hk) hok.1.1.1.1.1 (v0 hok.1.1.1.1.2) hok.1.1.1.2 hok.1.1.2 hok.1.2 hok.2) hk
lemma u5 {cores g ks}(hints:Nat)(hcv:∀ id,uj (cores id))(hk:ui ks)(hok:(uo g (bB ks)&&t1 (fO (uf g)) cores g g.cap&&tz (fO (uf g)) cores g g.cap&&gN g g.cap 0 (h7 g.m)&&eD (uf g)&&el (uf g) (h7 g.m) (eg g.m hints)&&decide ((eg g.m hints).map G=h7 g.m))=H):ui ((g.m,g.cap+1)::ks):=by simp only[X,A6] at hok;exact jB (vu hcv (uR ks hk) hok.1.1.1.1.1.1 (te hok.1.1.1.1.1.2) (t8 hok.1.1.1.1.2) hok.1.1.1.2 hok.1.1.2 hok.1.2 hok.2) hk
end
end Engine
namespace FreeInv
open Engine
abbrev K:=uh H
abbrev S:=@sS
abbrev T:=@tW
abbrev U:=@uB
abbrev E (p:PP):NN:=uB fun _=>p
abbrev B:=@bB
abbrev P:=@uE
abbrev p:=@u6
abbrev A:=@aD
abbrev a:=@uG
abbrev R (g:Qf):=@u4 g
def M (m c:Nat) (k:LP) (nb cd:Nat) (u:W) (l:Nat->ug) (x:Nat->Nat->Q PP):Qf:=⟨m,c,uz m (B k) nb cd,dA u,l,fun _=>Z0,x,fun _=>N0,fun _=>N0⟩
def k0:LP:=[]
lemma h0:K k0:=uD
def k1:=(66,1)::k0
lemma h1:K k1:=uu (uy 16777312 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h0
def k2:=P k1 1 0x426282ed0d2d4ce820085
lemma h2:K k2:=p h1 (by decide +kernel)
def k3:=(225,4)::k2
lemma h3:K k3:=R (M 225 3 k2 0 0 [0,30048] (fun| 3=>(1,0,1,T #[15])|_=>Z0) (fun _=>N0)) 90177543 h2 (by decide +kernel)
def k4:=P k3 19 0x8102820434bd33b430a04080c1521a5dda9a14602040a90d2f4eca2810548697a755120828101921c3cbd3c22304080c1421a5d8ca0204060a0810d2eed0630102053438697630c08101820434b315804080c219da5d8aa020410ced2ea54810203087975268081043cba132041da1a59098820406080a10cc36010203054867661982a4310c884080c10103c020ec41c41c3
lemma h4:K k4:=p h3 (by decide +kernel)
def k5:=A k4 [7601004771,7601062129]
lemma h5:K k5:=a h4 (by decide +kernel)
def k6:=P k5 28 0x104232538697a7751608101840323aa04a417804080c18211d552560ba020c108eaa128c5c46084759442e1081021c3cba936078d8084c505c616414686c042f244a2830d2f4d6ed8262131518697a676b78a29280820c33b4bd3dbc449880c58105c6164042965a5040c2608100eaa32340214cc42061708590a566461018a82088434bd33b4b1a08184c101c2164142965548402062a90d2f4eea3420613040708595a584d21028982043cbd3ba39080c5020581d641cec0406280c2e10b22e730203140618075109583681018a028c34bbb399c080c5004219da5dcae04062830ced2ec568201031768696626a10083b434b2933080c5020581d587c040206282eca1e41c7
lemma h6:K k6:=p h5 (by decide +kernel)
def k7:=A k6 [7617847539,0x400018061911d3,0x240062e82ec]
lemma h7:K k7:=a h6 (by decide +kernel)
def k8:=(497,7)::k7
lemma h8:K k8:=R (M 497 6 k7 5 0x361ce63eebd045ae8608af3 [0,34388] (fun| 5=>(1,1,3,T #[519296])| 6=>(1,0,3,T #[73957759])|_=>Z0) (fun| 6=>S 1 1 1 1 1 0 1|_=>N0)) 0x405670007 h7 (by decide +kernel)
def k9:=(498,7)::k8
lemma h9:K k9:=R (M 498 6 k8 3 0xd2a9fc46d3e4c [0,7693441] (fun| 6=>(1,0,2,T #[147711])|_=>Z0) (fun _=>N0)) 0x441670060 h8 (by decide +kernel)
def ka:=(952,8)::k9
lemma ha:K ka:=R (M 952 7 k9 8 0x3b6676bd06d0531b3a532d1eeeff6661868 [0,38996,38723,0x87975343,0x97874353,34643,9798771,8754291,0x4354957483,7705731,8746131,0x5354758493] (fun| 5=>(1,2,3,T #[0xafcc4420])| 6=>(2,1,3,T #[0xc0ff420,0xe0ff460])| 7=>(1,0,3,T #[745046463])|_=>Z0) (fun| 6=>S 1 1 1 4 1 0 1| 7=>S 3 14 2 4 4 0 0x295d84660a5000028a0000680|_=>N0)) 0x3340778000 h9 (by decide +kernel)
def kb:=P ka 64 0x3010214297a8b87aa9180810a1294bc3d45c4ccc8c1048085da5a1aa2e2638c6484a54f0f30ce3832a826b418a14b3b542b330c4865a1aa153c8ee24020872e85e25d91053438697a6b67a692090a9c34bd33b5bc52714040c50e1a5a9ada23a4a08240650ced2f4f6f31a621315196a787673821a9cb53c3c3338d1490cca5a9dd99c3842a2830d2f4ccce851417696a88666722098bb4b542b3510548c4ca1a5e99da1938a32f4e6ae44131538697a7655a10aa434b532a7a14484c90dda1a5a9a139820804064ed3150e9c61040203253867697a794d30821cb3b21d48854e5a1d0e702086a72ced0ec732213151418697637821cb91b5084c5521907e07cac0e2426508a72b496b38a61070628342534094a5b4ac4e08211929cb3b5443c34b0410148ca1a5e99da19582040c106e8a72080a94b4b38608374539054a07599304090993a29c82a205252c98410080c94e19da5e9e53592c2762102043967653ac081021cba1b6040818211d55255cbd020c108eaa08120e5e41060834375509472ea3041a1baca29748418208c90dd542520b98c1046486eb28c5ca608121324375409082e31f19018a80820c34bd3433c08104c61a5e9d9538208040650ced2f4f098e1020439676538d100818a8a0bb4b4341b9080c1025e1d4d684262a90c83d220308731da1d39018c048b23aa05220cb7808184c20251d54442865b8840c26100e92a814b0ba420104131538697a7851e1018c030ca3a882a41f4080c50619da5d8af040870f2e84dc1e7
lemma hb:K kb:=p ha (by decide +kernel)
def kc:=P kb 2 0xc50944869ee25e62383860824042a52f516f0f3926771
lemma hc:K kc:=p hb (by decide +kernel)
def kd:=A kc [7635575259,7652450803,0x18081f81fa,7636501181,7653450471,0x240082e92ed,7671088057]
lemma hd:K kd:=a hc (by decide +kernel)
def ke:=P kd 42 0x41c20a4d09954296d152b93900e2426528caa14b6939a6809364754054a553b39ae908104049ba32d2a02a4bce04082018e51d4c28e1bd021012464c8eaa14aa72dcc10402032538697a784f61890cb43542a7984081820e51d58fe02040872e8778773604283729520503083f10820117e08100c25d0be420ec45dc5db306172409085a576d6180810a13b4b317b173d450e1e9ee65db07c82a70f4f6eb45e501021433297a7b788bb08291943d3ab1f084c552a512dcaf62084a6652d4f70ed0d3c3a6172834295a454774e2098a9c34bd3b2bd04100c881da62a1d39c206484a52ced0ee73a3f58071649540a141b5549d531038c031a1caa050a0dad6a70414080ca5a9ed9f45ca24286652d4f6ced1a1e102053438697a6b68a6d2090a9c34bd33b5bc527880c54041061a5e9a19f100c2e92b4aaba6205197a745760820101929c33b4bd3ca6ba0084c58651d441520fa4432c476a102043967653ad1018a8a0c34bb1be0f9c41c208c95251828d0e5b1c62a90c63d63b7
lemma he:K ke:=p hd (by decide +kernel)
def kf:=A ke [7669260795,7670260463,7670317821,7687881661,0x4000180838d3cf,0x400018093993db]
lemma hf:K kf:=a he (by decide +kernel)
def kg:=(1003,10)::kf
lemma hg:K kg:=R (M 1003 9 kf 8 0x1197905c14cd4e32fed6eb5fa5ca122dbed [0,30224] (fun| 8=>(2,1,3,T #[541062371,0x523b09ff8e3])| 9=>(1,0,3,T #[0xb1a206ff])|_=>Z0) (fun| 9=>S 1 4 2 1 2 0 266|_=>N0)) 0x3301608067 hf (by decide +kernel)
def kh:=(1005,10)::kg
lemma hh:K kh:=R (M 1005 9 kg 9 0x767cf73447ffa781aba98a236ca2652ec3bb8f790 [0,0x95736280] (fun| 6=>(1,3,4,T #[0x4ed528883ce1])| 7=>(2,2,4,T #[0x3ed883ce1,0x2fd503ce1])| 8=>(3,1,4,T #[0x464538bfd461,0x523218bfdce1,0x100387ff4e3])| 9=>(1,0,4,T #[0x1950c8407ff])|_=>Z0) (fun| 7=>S 1 1 1 1 1 0 1| 8=>S 1 3 2 1 2 0 41| 9=>S 2 7 2 1 3 16 0x635900a|_=>N0)) 0x2305608907 hg (by decide +kernel)
def ki:=(1017,11)::kh
lemma hi:K ki:=R (M 1017 10 kh 30 0x12fbb270c41243a77a8bbaa9a6b2881e321b061e05e48b94a62a2aead787bab82d094929c25c6177e21cac22a0cd46720d3710e615e3a139121054ef44236d31e24d56da901512 [0,0x75948360] (fun| 7=>(7,3,5,E (0x1651361070d80a907a03d000,0x17f348539b28277294441e506ee883502ca0afda4e8c39417b949e20d102f41df5a068828817a0fea883441440))| 8=>(18,2,5,U (fun i=> tP #[(0x3c73833553122e42af2792372091cd1821541110cd09204f000,0x6011045895fe83220f40ffc9cd941484108c4bf940f28290bfe4e3ca0a6005ff261e50443817dd107941b28982097f281650740ffc983941496801ffc8c3941024940b0c5bfb409183907fe4c1460a61213027dc9c8881094858c25fda0688140ca43ff938d10238418c09f7441a20782808628c1bfa441440),(0x7d044000,0x144800effd034a1c1243c3127fd07461)] i))| 9=>(11,1,5,E (0x2c527623e2091b918b1431060c408503c000,0x1e7145840c048a4ffd28eeb2442a2ffd38a80551317fe94523c506008918b27fe8c5811404ffa60f0ce8a01413c8ffa50f0301239a37fd1878444009858fff4418c88a10041bfd9414480445086291fe460f1c210c28dfe440))| 10=>(1,0,5,T #[70364169727])|_=>Z0) (fun| 8=>S 3 20 3 1 5 14400 0xdf5b02270241d000001501b| 9=>S 7 32 5 1 5 0x2c8403040 0x1476044d2a68f820004cde20006c70882dc51c280122c00e25a6180| 10=>S 5 28 4 1 5 1310720 0x3364b2925560250010270245288b18c0000e26029|_=>N0)) 0x3305678007 hh (by decide +kernel)
def kj:=(1018,11)::ki
lemma hj:K kj:=R (M 1018 10 ki 16 0x548624f7abf6c1840e6de0f06bdd722a97a03f385eaefcd403f324a086c56632b35a3bbec70 [0,38723] (fun| 8=>(10,2,4,E (0x1c819a16613a1040e20b608a056034000,0xd01bff40d3974c02bef40931641bf540630e80f0fdf4c58a3bfd41d28e81f7d39528e41afd41b1874c029ff41d186ffd05461d300abfd06441))| 9=>(10,1,4,E (0x24c20a1d419c1631210e90ae06c030000,0xea2a2c808647fd396a060c78dff4c5d550a148fff8c3a38b00b06ffa61ea28c08a0a23ff1470c08a0a1bfe947868282163ffd2868e010e81491ffc61f41060340fff461d10730bff441))| 10=>(1,0,4,T #[90404292351])|_=>Z0) (fun| 9=>S 3 16 4 1 4 1286 0x9c116608303890001520900a| 10=>S 4 22 4 1 5 65536 0x191850009d4083100495580cca029221|_=>N0)) 0x3341678060 hi (by decide +kernel)
def kk:=(1782,12)::kj
lemma hk:K kk:=R (M 1782 11 kj 44 0x1221e7041095f5f5623b9e394bc13452105443d39430292acd57c4df3bcfc6c6181adf02bbd86d1c18d742844cc26c202128287a31a838f03e7b2307051a417033ed18cfb882bf0a803cc77ab338d7b5e4e4c07a85655d20d268cfcf9c08f0333446a3e6dfc3b5b [0,38722,38433,0x76964121,0x96762141,30273,0xa5947261,0xa5749261,0x2142a5946271,0xa5649271,0xa5746291,0x4142a5647291] (fun| 7=>(3,4,6,T #[0x50187e549d07ce0460,0xcafd26d04461460,0xaebd424e5d04460])| 8=>(23,3,6,U (fun i=> tP #[(0x3a737833b2fd2a42752371fd1ad16f1401110d30a4075046000,0x4efd24505460eb0777a72e822304141ddfa089c68c1800ab084627774e54e3460ddfa089428c1410777e82230a30501cfda0f9c08c181c005439f6a45a0a84142073fe83a72a105fbd224e54209dfa48a06841aa06fda91471a1047fd275024209ffa46a0484177f495189082060017fc461460420),(0x1da19c1360d008d05e02f000,0x2200defd245004e38068302609080d9df4a138c38e01a0c09824203477d284e30e3ae0029f7a44a0b9c13fd4a228f38277e92283a304ff527d05460)] i))| 9=>(51,2,6,U (fun i=> tP #[(0x4df4aa45b40c3bf3623052b62662211e41a71440ef0a204d000,0x70802bfd41d082140c00a900b7fe82a10428180171516ff505420e0208210f0bffa72a107870680a0204807bff40d083c08340501022e3dfea068410a005c10505ffe38d082005c7c10505ffd38d08381c320827ff146841e0e0d0fff4a3420e8b02077fe812106051c194281801822ff502420e21400d8c820dffe3121066001108685ffd189083230002f022037fc9c084161500811417fe460420),(0x52e4f34854273c93793442dc27c2401dd18813a0f508f048000,0x28a11877fe83a30423c343804022100324dfea0e8c10830e00c021130f7fe82a3042381a0229004c3dfea0a8c1008446322a2ffe9ca8c14230fefd044608d0bc1252488c20722efd0446082811817800c141ff78e3460c19230fff4e3460a0c302f8583002847ee9c68c1e1a028041171affd0146089047a00645ffd285183832830027fe8c28c108aa9a48c82800811ff67023042000e1413fe4a0460c21f041712ffd07420),(0x4dd47043b3d538f33b2e528724a2051c81801330e70a303b000,0x141689082793c10d0c26fe5008e3a2005ffe80271c23c34380402803245ffa009c718ca00809ffa80271c06860984880dbba71871c2021300842a35fea0b9c108f61608984c00f7fa81e707864383ffe28f3820321c0a27ff1469c190e100fff4a34e08015148e13ff4e34a09c00486880b3fc83e304068586038b7fa83e30406c014093fa83e3061608c0b8406880611fba71e30517270eff501c60),(0xfd0a905d000,0x101a2612182035fea0f1c7a261218202eef9c71c7a1c29080d40191eff5008e3)] i))| 10=>(9,1,6,E (0x2bd26120a1c81801380e8098048000,0x1010040613122200d2bff1c70349891842141804ffd38e0693123080dff0e3a4e0c2120080fffce0a488c2820080fff4e0f0c1c6c10008711ff4a0b1234042101c611ffc60b8228488841c011ff460c14242060008fff420))| 11=>(1,0,6,T #[0x81003ff])|_=>Z0) (fun| 8=>S 1 6 2 4 3 0 406847872| 9=>S 9 45 5 4 6 0x45422465c1007 0x3840000032702a6204c020000001c008480000000000170100e80400824468582b194060b20f4be2f82e0c8b44b85211054058340800000| 10=>S 34 162 6 4 8 0x1f9630050e060236020a2b22002a1612001c2d1c250d0c0100010e01020706051605 0x1176ae00007a4f92f0a801f0fc520cc724000008ab0c800000045b740002d0000000000081c08018c25c9339861e17002002d700205104019a970018bec480081226056aaf0302c0570150ac05e8c48254419e164af01a0589322d24402c1702433e6620292ec91084151af80d020061319932076ac299889a08fc0a00004cd10008231742e000d3e0028bc4b4bb29a0e4500010bc3445e12f6b60d41b8d7ba01844293307498049c9c4b620cca000948004a20008880fc2b000000000008942c60251949a0661300f53091ecbc9500108e13c61430ab4b306980705000012| 11=>S 10 60 4 4 6 0x4c314014d0121c0 0x4341c012521826c400005c52354000028885030020769a169a44831200029a51a40800a38400000000048e4d65001148c0000000000082806c73100002cca2b0a0a0911|_=>N0)) 0x12041670960 hj (by decide +kernel)
def kl:=(1914,11)::kk
lemma hl:K kl:=R (M 1914 10 kk 15 0xf7dd08392e65b4c627cf690d72083620d6e339ed0d834e488c5c35e5b6db64d4414023 [0,0x98a654,0xa89631,0xa9865431,8803137,0x8698a6315341,0x86a896314351,0xa94351,0xa5948361,0x31435195a48361,0x315143a5946381,0x95a46381,0x5451438564a391,0x6584a391,0x856493a1,0x544351658493a1] (fun| 8=>(1,2,4,T #[0x27fd07440])| 9=>(3,1,4,T #[0x524e6200a1413ff420,0x6290b280c4493ff440,0x5cc689ff4a0])| 10=>(1,0,4,T #[0x1d950c8408ff])|_=>Z0) (fun| 9=>S 1 1 1 4 1 0 33| 10=>S 5 21 2 4 5 1051660 0x170c7f8e2a2083cb013e72ecca81813729093|_=>N0)) 0x13301688060 hk (by decide +kernel)
def km:=P kl 64 0x1020439676ba6aeb1890aa434b5333de37b4c040854a9a1e5ae62e74608242ed2d5170f5ce701083946551a4b489f938409019324aa1aa525a54f99c244818d0a154696d667ace0c2412708a4a8a74b6b53b654a69837ba08192129533b43cc43ce885c64e119546950d525df0e32464c90b42a2eeec8172634295a4676e30b941ca2952b3af040c10a59daa19b9c62a90d528bf47f540a8b83af92a534c1bdc841094a99da619e78204080612f50cdf8312196a846f30818214b3b5433770410080c94e1a5e9e17d86242a90d52abe61020439743fc3f9a9c353dba5b68810d4e1a5e9d97d42060a90ced52cbbc315486a945d71021cb99fa841d88fb8fb6a94d306f363196a836eb1030c841ba2a2851a9cb6f20185c8ca515281421b5c408262a70d2f4eebf8315486a945db3eb98cb541b6d840c10a59daa19b3c408262a70d2f4eebdc20439733de3db900821bb4b29eb9e7e0189ce9256d1afa46040852f5170d57a501021433297a887b79abb18108828a0c3d3cbdccd579054e19da9edda9bca06242810d5372f1f61060a283749520544397f808304151ba4a902a21cbfa042018a8dd254c9510a5fc820a54e6e7c10523287a756be1098aa544c2b5b840c1490a19da9e5e19f862a90d5289ee77b514387a7b9976c5f304151ba4a902a21c3f897ed020589ce825441dfb080c2e507214acfac20104131538697a785bb20083b197f177c8186420dd295010e1f68408262a70d2f4eeafc3f7
lemma hm:K km:=p hl (by decide +kernel)
def kn:=P km 24 0x1032425276b898a98e9d77aa8909921bb435b54cb4f37041408109da9ae65a33cdbda2064a54d6f0f0cfe3a6172329485a1b5518eb638309049a142d0dac75584140c88109da9ae2625ab99c60204284a54d2f0f713b3a305121427686a6b98ce73fa8828211053dc4c3f2f1014484c21e9ee65e336cfe620e10526c94a8168a93e9c1030524020a7b8978e3e20992953dc43b717944c90a9ee2625df87d00e242c7294a6065693ba65143a7b9975d1f281890d45cae5d8c10480854a5ea2de1e72dc60a2410f4f72d93e77b6021819374a5b054109f953010c0b9ca52d8189829d7c698086064e91d6c50e3b94c0e30465294b6686a93d8e3f7
lemma hn:K kn:=p hm (by decide +kernel)
def ko:=A kn [7687103231,7688020959,7704863727,7721690107,7721698301,7707813567,7707944671,7741597431]
lemma ho:K ko:=a hn (by decide +kernel)
def kp:=(1918,13)::ko
lemma hp:K kp:=R (M 1918 12 ko 14 0x1131d48719027bb8ae6049664b27bf6994dbbf075590f675a66805f02a68d9199be [0,0xa9865431,8803137,0xa94351] (fun| 8=>(1,4,4,T #[0x187dd49d41507107])| 9=>(4,3,4,T #[0x1a282e7dd41507107,0x1e3bf6ebd39f2e3c0987fd49507107,0xf1d7a77edcf8f0e430ac7fd49507107,0x9fdd41521507])| 10=>(10,2,4,E (0x2c726721a1ec1be1530e90bb08d05f000,0x40205d0bdc928c2affa94483e1ae989448d9ff41e41e60dff5209079037ff48541f1c12e35cf4df6a4a2ffee90a83cb3d74db8deba71c0bbfba42a0f206ffa90a83cc1bffa40a0f306ffa90283f1bedae99e38144e7f507107))| 11=>(3,1,4,T #[0x80b7b2215a454933ff107,0x4eb4b62eb4ca302fff507,0x275a62f64c60a2bff907])| 12=>(1,0,4,T #[0x43b2a190813ff])|_=>Z0) (fun| 9=>S 1 1 1 2 1 0 9| 10=>S 1 8 3 2 3 0 0x811000c0000| 11=>S 5 22 4 2 5 19956736 0x50501a31d28c00062e5200330e0c9c98200242| 12=>S 1 6 2 2 3 0 7929907|_=>N0)) 0x12301688960 ho (by decide +kernel)
def kq:=P kp 44 0x60108293a475b1518f9d3048c1183a529920d9a9d77394dda1ad93af82064a4ed4d710cfd7a2043537696b886a68ebb08281910213b535c4c4b575b84100c9dae2a1babc20406080a0ed7131533d3e204397ba49fb30b941ca52abfd3bf4c1450840825a1ede99dab9f8a242872d0f6f4cfcde405132202196a7b6769cfb0828104b53db367b900cae8ebec2040872ced74d5de3061928074a567f618214b9b7f37bd450e1edea579f440a34f7299fa204397ba4adf3038a949c2512018104bf5981c54a4e92099f6db7e82a70f6e9c7e204397ba4abf6bfb038c149a0d2da2a47a7944c90a9ee2625df97d00e2c463294a41691bae5143a7b9975d5f18289043d3dcb66fa0189ce9256d1afb482a70d4f6eb6de30204297a8b86afd304151ba4a902a21c3fa8c5521aa517dcff6410320c748ea86a10fdc2061908374a5404387de102098a9c34bd3baff0810e5ccff8feec083054722eb62fbea604182a37195205131b1abf53ef88284151ba48315a3031b25fba841c20a4d529181df3cf7ea2870f4f732ed8fe5ff
lemma hq:K kq:=p hp (by decide +kernel)
def kr:=A kq [7738483711,7758407423,7759423479,7759439867]
lemma hr:K kr:=a hq (by decide +kernel)
def ks:=(2015,14)::kr
lemma hs:K ks:=R (M 2015 13 kr 32 0x8c729ccf1578ba700f6e4ffad6f284798ffd160b108077dc8b4b1616217ba5cfd77e80558011e02e8cedb97b1f9c253c68ce5d59922d6196da7ad4282d8746e77c7a201de780a7c398ca28 [0,0xa493827160] (fun| 9=>(1,4,5,T #[0x15069ef18a527524482])| 10=>(11,3,5,E (0x32d2f127d1f91aa16b13a0fe0ba07e03f000,0x1506effacea86a49e09e50c08e2e1e0233dfad4a48249e090ce2e1e5e0e408ef2a3dfad4a482494341201edff51f49120e401dbfea3a92241cffd5a751d20aa0cffc5a949d20a028167ff52549120aa0f7bd49d49120a201d7fea429223162837fb564d22462))| 11=>(44,2,5,U (fun i=> tP #[(0x5414f548c4213e338b3332f62a52511ff1ab1500f30b105b000,0x1962c22060bfdea4990580a1696121e2c2209bffd49482c9160e10462c380a157fea92905243281fffea3a416e2c30f0242c3dffea3a41643c389260143dffaa3a41512150fffd49d20a61e2c23040dfdf2489058b00d284218dffea4890501b8b0c31437f7a9224162c3801941037fda9124161c04310348287ffb4e2482c492918b0c4c0457fea423178618509ffea488c5e2c24f02d0c3ffde912316121889e08a287ffb482462),(0x50a4b645b41f3cb3793252ca27623b1e71851380ec0a604f000,0x3045c5130881affd51348e28bc388d60383dffea2291e87381fffa92291e08b8710b1835ffaa4e41c3161371300d5fea91907171611780c8d7ffa9290740d0bc5862e01edff51d20f12141103991bfff49120f99881fffa92241e287870242a35ffaa3e91602c1c243c5844117fea89a450d13810505fff8e45229218c2c205fff4e4522865470a13ffd49138a4b86330e2103dffaa4e4178b09719806aff548c82),(0x3f839f34b2ed2a924020a19c14c0f80a4052000,0x9070a33161103dffaa4c9265c584608c036f7e9249240e8c661c4fca117fea8524993825209ffea86a4980b07088f0e27e509bffd42524a080bffd509493c24662c397064de20adef524124f8b08c11806bf7543124cb8b08c11806bfb542124ca7710c11806bfd541124961c4222601abfd52348f5871088b806b7f547d23)] i))| 12=>(13,1,5,E (0x4193c136230a2c42722271dc18a1380ed0a2051000,0x121c99488e286030afff2492470243a3298445097ffd49243881cb142640415ffc49211422890103fffd238126c508a240593ffd48f5084488580b23ffe41ea114228901647ff4838a05c9143006693fff48a05c50c12077904fff522c222843120388ffe9c5a5c91421c0611fff20a0c2ca9218a00c9ffe90521903c508900c4fff462))| 13=>(1,0,5,T #[0xa4188201bff])|_=>Z0) (fun| 10=>S 1 1 1 1 1 0 1| 11=>S 3 13 4 1 4 0 0x211c894ba43282100180| 12=>S 16 86 6 1 7 0x60043830a3861c00280810220000 0xa99998672669000023000000000002179cc8450800a7d559cb0011008a2516a42c4e130f0000e4120006006889008414e347a08ed000055e00109d2b0115d80b0d00a8039ba19f009e0caa00001aa200076543000000| 13=>S 6 28 4 1 5 1278048 0x765af704408000da73b0a658000191695003587a32|_=>N0)) 0x12301078967 hr (by decide +kernel)
def kt:=(2046,15)::ks
lemma ht:K kt:=R (M 2046 14 ks 40 0x61e3678b8ef1def7ef71e801304d65eb7dd6038c1a640d706df75f03a74fc97aa9ed982f8e77c8525003fbd94b2337872cdc531ce47a491d732ec99b47a9780236a3c22cdb6442be42ea8edd7c4145849eaea9b3c8a8899ebbda4f90a07a75 [0,0xa9865431,0xa594837261,0x95a4637281] (fun| 10=>(3,4,6,T #[0x9c0c04fc3f081a1bce7528524503483,0x2bbdd81528d46483,0xc907bbdd81528d46483])| 11=>(14,3,6,E (0x6775e057d4ef46a3fd3942f42662061b51430da068000,0x461b13094438800803848d0a173ff569d44503c3e0e24330c16f7facca88a07186c4c21a480401c346850a9ffab4ea4241c61b13087100100328284cfff5a552120e2349e0f0016161b77facca909072c6f0b83c0888d3bfd66548483984a230906c2a210080311490a193ff56a52848391c6e270b6d82c06482c2c56efd52351920f4c28402c2c2fefd4a351920f24401f0f77ead1a8c907f097011b9ee0b247ddfa946a3241cf87c2e08742c37bdd4a140d20f95ba485b828e0d0ffb7d46503483ce0f0195080d0dfe7524503483))| 12=>(13,2,6,E (0x4a344a3f538f3202d326d1ff1901320c8062031000,0x4e8ac1c0518d1bffd41148fe12760e0060d7ffa88a0762313809d82182c47ffaa2281e450603307013a24349fff524503e938380162dffea4241e08c424e0608b8b11ffea909076182d8e22931183804dffaa4241d4504c2f07023924349fff5284838c7c6c2c1c00b1feff51920e144b1e47070b02408bbfd46483f0b0c0dc0c1498e23fdd40d20e1037ffa82907081bff541483))| 13=>(3,1,6,T #[0x1085ca0b260411047ff483,0x6478a22041123fff503,0x2345862a0c01a3fff523])| 14=>(1,0,6,T #[0x1c61440c204023ff])|_=>Z0) (fun| 11=>S 1 5 2 2 3 0 1641483| 12=>S 6 23 4 2 5 405805089 0x10d24692289800a4824b1c001084c84a979806687| 13=>S 6 25 4 2 5 5247695 0x2080e60b01ac500031802cb066b80469e4498f4e685| 14=>S 2 7 2 2 3 8 0xcc78a402|_=>N0)) 0x12341678960 hs (by decide +kernel)
def ku:=(3775,15)::kt
lemma hu:K ku:=R (M 3775 14 kt 50 0x1c85dbe51acf210409d558b9e2d5a08269d08a544ed71eed72625ca9f4ade57be023b822c8abe67aba8408d774f821c272f4b13ec0464835b61321369da366ce7fba9610e2040a1ea0cfc42dcbe25243b97799988aed3b0e0b7d2b7280b9a42c725751a34d043555e7e212e1b44ff1a4a289141b5e0b11 [0,0xa95431,0xb75341,0xa9b74351,0xa75210,0xa997b743502010,0x97a742523010,0xa7b732524010,0xba974320,0xb997a741513120,0xa7b79753314120,0xb9a75120,0xa79752421030,9912880,0x97b750412130,0x97a9b720425130,0xb7a752321040,0xba3240,0xa9b950312140,0x97b9a720325140,0xb7a79743211050,0xb92150,0xb9a940213150,0xb79730214150] (fun| 8=>(2,6,6,T #[0xc03fdacd6a5281284e60e6,0x823fdcd588188d6a4e60e6])| 9=>(6,5,6,E (0x2441e21801190ce067000,0xb8188588ff6226235a939839b103c1623f588188d6a4e60e699332c2e07fad5a512509cc1cd8cf75ab6054a139839b884ca0b41fac52940942730734ca9a41703fd6a5281284e60e6))| 10=>(14,4,6,E (0x70969d64760954e4a74003482b824e1b415c0fc06c000,0x18ce20649962787fa512519cd1cd926585c6fe944946a2a7357bbb02a51a8a9cdcb7282e725c50b4300bdebf13c1758cccff6235a939839b96e506017bd6173cef378ae91599fcc46b5273073729cb0c02f7ac2ef17c4f05d62b33f588d6a4e60e6c02f72dca7202e7142d7ade7799d23333f188d6a4e60e6b82d0b2e7b9bc3b5ed22333fd6a9284e60e6c932f10c384f0ff4a24a139839ae0b7c10b3c4f0fc0b5ada2733fd6a5284e60e6c430e0af3dd815284e60e6cbf141e0eb3f58a1284e60e6b82d0b2e7b7ee6b4ae82333fd6a1284e60e6c38d20601e13c3f5281284e60e6))| 11=>(16,3,6,E (0x82d7a172b69261e57e4e544c3c93552d22441d816b0f5076000,0x1410110a806204a084cc862a7fead52511cd0e73b99af13833487f9fc946734734c820442a100a4569010f10cc5cffe5aa4a139a9687885f33637183f3ff4a24a139aa148884a24100a02623108401464ffc5a94a139b9dcc874308832e30670daed22f7bf251a8a9cd0e8611067820ce270f80d66d17bdf528d454e6a12890440511a4d0c52267fead52501cd4b1d94c361cbe181f9ffa512501cd60a1108043c4e1a1d0c4cfff5a94a039a085c24101ac76532787c3157fdd615280e68e4a17d0e52430d3ff56a1280e6e2f1387c2e0f00699feb52730734520fc3e0b5e1c1e1fe7f2509cc1cd0ee270f8110e0b583047cfd4a139839a291383b4a1c1e088ff3f1284e60e6))| 12=>(12,2,6,E (0x4023a03463152b32511f21c115b0ed093031000,0x253170b026d48607fff9288e6c5c4c3c107061bcff39a39a0837fea831cd8b898582bb1a383fffc9427360e262ab4dad468fffea509cd9c4c3c2c1c00c1ef7f51539a0837ffa829cd11d290f8126a43047ffc94073584e0c7622bc9ab0a93ffea501cd29271ca50e2237ff8940736261e160e008070fe7e9cc1cd041bff5410e6))| 13=>(3,1,6,T #[0xb14244418b121870c57ff0e6,0x50b10262c1890e10d185fff4e6,0xb1424441890218f1c57ff8e6])| 14=>(1,0,6,T #[0x1440c20401bff])|_=>Z0) (fun| 9=>S 1 2 2 5 1 0 386| 10=>S 3 14 3 5 4 1025 0x1048300000038cc14041b0e0000001| 11=>S 6 25 4 5 5 540020173 0x20d0d2352280383a88812870c8008ce0b03202826890000780406028088148b| 12=>S 7 33 5 5 6 0x2280040080 0x10b00102c028000d040c06c6d80c01087c098c502200c0c0015be3306181e002084070141a80000200103a01800| 13=>S 5 29 4 5 5 2101251 0x203bf0088060b002b90000000009002078120c002858d000000b581400818000020a80889| 14=>S 6 34 2 5 6 0x56058002 0x2f098581330a1300008200838f0000170b00abcb009692878d9100001b86a3950e00|_=>N0)) 0x120007799a7 ht (by decide +kernel)
def kv:=P ku 40 0x60718293a4b56ffaebfa9db439fdf040c94ada9e1dbef44086a76d2f0f4cff761020304050b6768798a9af9f20a9c35ba7bf105dae0fbf8408262ed2d7150fdf6105032204276a6b89896aef70820193b5c54377788104c54e1a5ede9e37ec40872f7497f6ffd602181a39475b17efd3038c149d2295abf6f8810e5ee92ff9feea242872d6f4cdede41215386b7966f5f0828104b53db36fb8410080c94e19da5ede9eb77c206040a4850d4f2ced6d57fa1020439676ba6bef1890aa434b5333febfbd450edea53df482a70d6e9eee2051a7b94dfd102098a9c34bdbd3c6f7880c545061a9e5ee62fdc40872f7497be315486a947ef7dfc058b139d24a9920084ffe1450e1edea579fc40a34f7299fe204397ba4aff6ffb050c159ba4a902a21a0d7faa028589ced255bfb500e2c547296a406282a95fae60718293a4b56fcf28a1d3dccbaebf9054e1a9edd6dfc62a90d528bfe7ff
lemma hv:K kv:=p hu (by decide +kernel)
def kw:=A kv [7793010687]
lemma hw:K kw:=a hv (by decide +kernel)
def kx:=(3839,17)::kw
lemma hx:K kx:=R (M 3839 16 kw 66 0x41f3acff3de8524a8d09c6933237824610b38c41703e84dc6f82e027c48e7a4f353f40c1aed1c7d703a093ca74293446feacc2b52d219a03d30f2ccf897f340017de78664a23f1f68eed5e4666ddc62ddb173b8ca78f52b388cd14de1ec05b4f8d350abfe52400553edcd19b3792d80f070312ca010a7926a964136dcb63cb538f20404a076220f73cac57b5f0d41c03d47b3be06fe57e4a4341155 [0,0xa9b74351,0xba974320,0xb9a75120,9912880,0x97a9b720425130,0xba3240,0x97b9a720325140] (fun| 10=>(1,6,7,T #[0x157a7de3548da4527d664a1])| 11=>(5,5,7,E (0x1e01941360d3076000,0xa7fadc056ad825284e1f0c06bf9f70d52361149d286be04157eeee0aa4ec2a83a50f88075ebd52369149f59928703b047c083bfd5dc35485254e14a1))| 12=>(32,4,7,U (fun i=> tP #[(0x6f968060f5454c947a42c3c73783072542051b61450f6071000,0x131e0b0fe03c262df77da35485274e1c1b83b4361112ffbed1aa4292a70dc200304ec6006b146720998078266ec58dcfdead1b08a4e943c098ab80650c405dfdea91b08a4e943c4039fbd58f61149d286160cfdf5a5d8b5074a1e004c70c0f7efaa4ec2a83a50c280d7bfdac527d664a1b06e00cc1a813bdfaa4293eb3250f84f0069cd3614e0de2306181306557afda4527d664a1e201af7fb46a4facc9430a035eff6b141f599286c1b803304cc4ef7ea92a0facc94382835eff68541f5992870225bc1613d0782c6bff3b44a509c294303a08f0270027fdd5485254e14a1),(0x74d6b05f45995284d34623d136c3172bd2681f719c12b09e000,0x189b13e03f046430098032a477e7da3548d64527e09c0c4f89bc378530980fc16013005d7e7da3548d64527c238482afefb46a91ac2a4fc0e8b68093025fbf5a618b54950780210abffed0aa4eb2a83f037008581089befd52561b58541f3f67ca55c0023702a447cf7eb12b0dac2a0fc00180481e7ff549585d6150780210b3ffab56c2a83a90e00c142dbfea93b0aa0ea438066167ff56a5884e5521d0dc170be0f12ffbed1aa4272a90c8490c1777f56a5074e5521908c024330513ebfaa4a83a72a90f00e78618005da07088f5ffb6815a94a138601018016e060bf863806264e7fb56ad825284e1)] i))| 13=>(60,3,7,U (fun i=> tP #[(0x8257766dc6546135d25914eb4463c23302ef25e1cd1320a0000,0x100a00124621545184e1f1da06110accdffd5a149d286a30245611a0d804a212442132bfff5485274a1e08a729b84e021f86f0b22fefd845274a1c4037ffec1a93a50e201dffd58d49d286160dfffb16a0e943c0f000c02e0a054086194250610973ffec5a83a50c02800851885514e0a83a1210068bdffd5a541d286aa0d80c0a0b42c298408fffd52541d2878126097e0b8004284a0d0b26fdfd855074a182837ffec0a83a50c5510e278085306e11834449defd49f5992862a88f03c042982b08c1a204ef7ea0facc9438403910843826058082c15070afff552538528780057826121386c116060b27ffd5284e14a1e05410e0981e0013e101102e832ffdd5254e14a1),(0x7746f66b561e59652847a40a3c93592db2551eb1630c8041000,0xc018482c8d20f0f2dc7fdfd41d395487100effeac69caa436e0b8807b87e13800d935a04a9ffd6175a538784e002704f882070c40c89fbf6115a538780dc3281a00341afffd885494e184c100e259102528087f82c0d130cccbfff6155253864e0981600320786dffd5255a13860a0cfffb02ad09c38e1940b010885c36ffead4a509c3c0131c150981a260d0f7ffec2a94270d815fc070dc11098183445ff7b04a509c3c13014085c8a8bfbfaa4293a70c1b0750c56b0086a1d0891fffaa4292a70c0118a001985416a120bc0c2c2b7ffd695054e1c050d8292d0b21c86d3247ffea92a0a9c30b06fffd8b5274a1),(0x84a7c473c6b463159f5274713e13592b72341a4163122092000,0x25782e2387e018108c3b237ff589d615078520609382605802542a237ff549d61507e07800082a2d704c0c23237bf586d61507c02fc0f01826074604644ffeb0bac2a0fc27060b01a0a8538660340133ffec2ab5290f82f41e1980d00190f7ffec42a3a90f5820268802a4202e4b13685e034061e6dfffb0aa8ea43725c709c3107c16024061e4dffdb00a8ea4341a2e0b13182b0010e1e47fffb14a0ea430a288e82d4a0534ea3f41d080f17bffab5283a90dc0fa1a84c31016001e23dff54950752180c009805d0ba12832430f26fffd8550752182837ffec0a83a90c141bffd60541d48603002601782d84a0c25c3c9bffd62139548686c1580234a045d0f85e0f27fff5484e5521),(0x5f857a4fc4573ed3652f528b21c18e0fc088000,0xe00180418c0b303a1079ffd6075a149f8204a11805800b83d1ffef548d64527caf0cc244f1370b01f04c8402c017bf7aa46b2293c22c012b090782effea91ac2a4fc003008f10cee0612d0244ffeb0bad2a0f8021c10228260634ff7b04ad2a0f81d00c122c4c0bfff8c5aa4a83d023e0b04c0c331a7ff18b54950784180ab8c60382c13030c89dffd52759541f8026382e2303604978342326fff589d61507c0d80a303b086161bfff549d61507e078008494a1704c0e1022fbf586d61507)] i))| 14=>(38,2,7,U (fun i=> tP #[(0x7396c664a5db54e4e844c3c73463132e02441ba1420b4033000,0x184070370d0c402043c47ffd52538702180b87b00848640c204dfff5a1387017c0e01090c818408bffab4270c08341c1508e030d8281a10345fffd4a1386b84c3e021813408ff7f5274e1f0602e16c46243581c06113b03071b7ffd654e1c26001c13c4073041b40868afffa92a70d42216c0e01320b81a102657ffd415386241bffeb1270c4837ff5624e1c05c2c14c4627038083037090c419b7ff5674a190542013c1627018408a0e165fffd49d286a11c160700104220e164fffd41d2871589c461f09830a4181981c0177bfd664a1860b1189c0e0027844182caffea70a50c3837ff5604a1),(0x77d7016856165a350748f42539b3232b02381b6135102078000,0x188c3e1b0811c16003e1226fffac2a4f85c38960982c0041022127fffad2a0f8c061b0504818450245fff5a541f0018c10471103408408bffab4a83dc482106e1b0b044ae0a071040a00dfffaa4a83e02f81c06170504818409bffeb2a83e0700108223206211ffffac2a0f40b0602f86c0e00468c8240cbbffeb0a83d81b84c1e18310c80a009bffab5290e130786c16202e011111dff549521be1b1280c16121e830a93fff547521842a17c3601210c4220e1e57ffd41d486a1006e27000bc220d410f2bffe9caa430e0dffd581487016c207b0186c16202e1f81977ffd694e1c05b1187c2602188109937ff5694e1),(0x2611f215b0e8066033000,0x18c0617058881c042045fff5a149e220d4240c258554243051380a00cfffaa4293e1f0813c100700110911fefd645279c4d84c061b0b82c40040655fbf59149e201bffeb1a93c4037ff563527)] i))| 15=>(5,1,7,E (0x20a19c13e0d806a000,0x216204a1a10460208040cafff527868180851082040323ffd41e221e1a120e0a00043c9fff52188890e0d868180840c032bffd38722a26221e120e06002cafff4a1))| 16=>(1,0,7,T #[0x509101c305080c101005fff])|_=>Z0) (fun| 11=>S 1 1 1 3 1 0 1| 12=>S 2 11 3 3 4 0 0x14838514000020220a| 13=>S 15 86 6 3 7 0x410d04584000e080810014103 0x21c002095381e0029006b51000000009753c000000045400178150001382f420440585800000001404a02800d0607000180080ea500064800810ce07400000000000fa449e864000000000e101350e005020506084a9a880d487c000181b0220d6400c0031185c0000113| 14=>S 31 191 6 3 8 0x50d0f000b0e020d0d030005010b00020105001305000603001200140f0907 0x2110a000eac00000d0000310021200193818000021e9ec008907400145080000000085e2b484f9000a6828528b0c336c00000790021c0a43300055002154de6fae4a824018d522f87e32000e60007a0661b4802e762221cb4100095001500035784e370002a85800003168ea108b425e0b100c000838000025c8f0df83000000c990c6699c0096c000d9e9002450ec232cc00000006540089a35968020d00007400b5400f800080c38b810583400462210108909c1a40998189a90000000000508140000038800a969800158000000e40003e4482000000002c00081c00000000000001400000010035682c00025ea| 15=>S 21 94 6 3 7 0x115919044482c591021808050405032a040a1 0x92026202306e860860c8400052805f580000181002820020307c4989800a7617e360f34606a061d0019604c9e0061ab740d00020e1c57d34460011307914c5a5051619e4a089100a0000e0969f0001c046e6e46cc82e140578c82645c070d960163821225407b5c00b18004171110818b42c208804| 16=>S 5 18 3 3 5 38912 0x250303080535a0064b014825b9a14d65|_=>N0)) 0x12001679967 hw (by decide +kernel)
def ky:=P kx 10 0x201c58a8e52d480c50552bff8c0e30527496adff6315486a94fbfeffb058c151ca3ab7fe982860acdd25481510d06bfdcc12304e7694a406286a75fde60718293a4b56fdf20a9c35ba7bf88104c54e1a5ede9e37fc40872f7497fefff
lemma hy:K ky:=p hx (by decide +kernel)
namespace F12
def bk:=M 4095 18 ky 150 0xa975ea62f08ce9df18f5bdfa9c76f9c141ca05e21f94fa5beef7ee414cf41bd2e4045992ede412f097f5f14492dfdc8ab6918fe74c93f33b68e90c946ae6cd376d682cef6a34ec12ed1fb5cf199af0712fb3633748ec57dfa6546b67322a664873b1bac3151e98f3016ea3504e3cc67304004fd2289ffd4d6ea7f430bfedabb7021465d15779b5f955f225d4184bd4ecb30fc3b10074cdae8f61b4288e78c59938b9cdf6b1e549f0af0356b16302dab882bc2519302d6cee0ed2d9a991fca9b6ff5afcdac65e0b3803d4e8a793de267d8fccf11ee2705381211fc1b55e880a47c7659cb41970e8f121caa05e5d0437e8245be3f8f922c096cca03267b99a4f8e55ef6d1970c99832a511280115c31348bcf2cf24d44fb32f7d62743ebc2225b2c72e3679f3f51b80e87cc8fb463a9ebbd786335b72817e48718a7862f3457170de14139e8e7668fb2dae5ddd3fa440e1ec75a0aec7e1f6742ae500c3be1092dbc05497 [0,0xa9865431,0xb7865341,0xa9b74351,0xba974320,0xb997a78641513120,0xa7b7978653314120,0xb9a75120,0xb5a493827160,0x53433120a5b473829160,0x414354209574b382a160,0x7594a382b160,0x54413120b594a3627180,0xa574b3629180,0x95b47362a180,0x3153542075a49362b180] (fun| 12=>(3,6,8,T #[0xf80bc080abef9e02549dc84834e14a1,0x34ebeda8de0567d864834a1,0x756dd030b4fbe5a9de0567d864834a1])| 13=>(47,5,8,U (fun i=> tP #[(0x7bb7416d565c5e55614f44874103562e926f1e816e101087000,0x702f60dc050efff3bc4a92948ac28c38288570b6ffaad5b8e948ac28c382830a42b87b7fd56a5c74a4561461c738162400ffebaa4e9ca948ac28c38e702c0afc0513fedaa8e9c8948ac28c3c12b8a85bf7ddc75674a4521461d8370482bffe6f02b3a52290a30e38057e0907ff6d5474e44a4521461814b9bdd4af0df0313d81f810047d7d55a539158d4851870250400affebbce948ac6a428c3812284c1003bffaaf3a522b1a90a30e04808070838309ffd54e54a4563521461c091c220801fff9539129158d4851870250570affebbce948a86a428c381282b9c5c3bffaaf3a522a1a90a30e0480ae70838389ffe54e44a4543521461),(0x78270968f60959551b4b442d38c3202a622c1b21450d906d000,0x34198aef3b0f7bfca93b80acea488c3d06632b1083d7fdec5ee12a4a72230e073173a0cc42135ff6b17b84a929c88c34c03865c0e9fffbd6b13b4e9488c3e04c0de0503affdef12a4ed3a52230e500b854fffdeb5895a74a4461c0be197c0981412bff7bc4a92b4e9488c3b0003940d203a0531968dc77fd8bda75674a4461a5cd8a85cf7f589da75674a4461e8330698381ebff962770159d291187817b07e02877ff9de25494e5561461e05ec1b80a1dffe7789525391585187817c050a7ffbbceb94948ac28c38288570b6ffaad5b92948ac28c38288570b6ffaad4b92948ac28c3c0be02853ffdde75c94a4561461),(0x99f8bd7e87486b563b5664ec4653b731628319411a0a0000,0x742ba0c594c49d4bb82570bf81f81fa41d332edf7dbc0acfb0ca46943d0be831657125539f03fc0ec25d1ee97156fbbde2549d864e34a1c3563638ddc05d0d60b0daffe589dc05674834a1d5b681dc78ab852d179f7eb52acfb0c90694371ea0cdcb43e75fed42b3ec3241a50e0df121d0ae84f548b29d8da0bd03ba2c55befb78159f61920d287811b0df23877ff9de25494834e14a1e04215de41e47137dfaa93b909069c2943648f814066e2bc1080c503c7df6eee42b2a41a70a50fc0ac8d018e08415e81e36fb7772151520d38528714d8dff0070a34b45d3fdec5ee12a4ab3a30f042859e07f035c28d07882f815c2684be0de27995ffade2549da0567461aa9540763c1f1fff62d6a959d491186a0d73bd8f07e5ffd8b549567524461c6d6383549a03e0460a0d9ffe5aadc0567524461)] i))| 14=>(218,4,8,U (fun i=> (if i<8 then tP #[(0xa779df94086578a7086935fe5644cc4153682c322e1830d6000,0x65e601e044e22da62e8263dffeee5252290a30d0cbcc03c07c089c504c4b08bffd5ca4a4521461a10d98582b18502590ef80f8138f60918e4201b7ffbb8e948a428c3421b05630a04b32f31521df01f02c1231784036fff571d291485186c19c7b048158cb45fffd5674a4521461e118246d60ae27ffeaa3a52290a30d7c05f01b44c0c12c4131fff75515291485186cbfc0704b030d141005047ffdd4e54a4521461d11c7bc0704a03c4b21007ffed4e44a4521461a784783781f81780f8011d00982015ebeaad2ac6a428c301c1bc049efc0fc0a085d141fc9fff54e5563521461e0fe03e07e044f7824e840fc47ffaa722b1a90a30c072f71e747d2026a07e1fffd529158d4851864299e07e05e01e0208004e0ae4fcfaaa4aa1a90a30d7707f00c12c0c744b3b74282727ffd539150d48518704886dc2dcbdc780668e7033c0f48010015ccfff54a4543521461),(0x9bb8fd86f7bf7316765ed5544b041b3812e724e1ad10d081000,0x407783f83197d84706f81690409c13957ff9b80acea428c363dc1a81fa4069502635ffeee2aa3a90a30e0e28305963c6d7e042da43b0264dffeee22a3a90a30f06b8f02b8098a64078df7faa8ea8aa428c36c34532f300057d2080fe0d4131412afff5729395485186b192383d836093a28dfffa9caac8a428c30b3c0b83412f480d0c04c7fbfd54754452146190ecbec03c0fc0903a0c02048effdd8554452146196686e0f60d487824e8a3fffea72aa2290a30da9580f81706b8a82a0400fbffab569c8a428c3059e03e058240966948263dffeae5272290a30c14f03f00f02f0107e0801ff7f55a5391485186bf80f807815a22a620984011fbfaa929c8a428c3658318f781706e9002ba0991fefaa8e9c8a428c3a4129b83d835a120c8dfffaaca9c8a428c3c1f014d1815c4b05fffd5454e4521461),(0xa89a0796f8bf83d7816c460b5894b84363562681e61700b2000,0x1816e0e68d80a0ae2fffeaa2a722b0a30ea0455816e0f60c68580a3fffea92a722b0a30c546a4641a2be0484662f89e4e24dffeee52522b0a30e0598e1a1e029a30bfffab94948ac28c3151841a919068af81211938e27825957ffab94948ac28c305286e052c26c21cefc0285813415caf7fd56a4a45614619e2b8614096e41819a2bc1a62e84e55ffeee4a522b0a30e0598e1a76029a80bfffab92948ac28c33c57012cc28c21c808db83703345509c8a8cbffd5c94a4561461c0b72034c05724017fff55252915851861b30a04b22a840352320c14f02c4f31c21d13c36fff771d291585186100c70d1486c12cc288a8d4b050c804f3c0887713cebffd5c74a4561461c0b708c0536b05717fff551d29158518702dc20cac9004fffd5274a4561461c1405704031cb0671ee0df02345c4f2bff75395291585187050902100c71c7ad1f834d0b13c9ffed4e44a4561461),(0x9e493e89980b77d6ef63d5674b54273a532f2a11d711c09a000,0xc0bb07d5bb52c0c31e24042723fdf549d395585187adf17f817808118259a1e2791f7faa8ea88ac28c3816e1160c09668780a37ffea93aa22b0a30e05b83d830259a1e028dfffaa4aa88ac28c3816e0f60c09668780a37ffea72aa22b0a30e0a6ad9a978171791f025e279b6937ffab94a48ac28c302943761160e82889fe04a2ae77c1b69c0ae67bfeab52922b0a30e0a02bf80f81717f81e279a612013fbfaa92a48ac28c3816e1160d80a69c45437ffeaa3a922b0a30e05b839a360282b8bfffaa8aa48ac28c381760c69c48027ffea72a922b0a30f17f81211e279a50258d7ffab949c8ac28c302943761360e828e77e05c1a0716840ae5fbfeab52722b0a30d7013c12cd48cef0304f087509c900abffd5c94e4561461c0b72034cc0505717fff5525391585186d12d48c7bc0b13c15d08c7ff7d5474e4561461),(0xa7d9bf90f85f7c57156595cb51246c3de32c2941e41320a4000,0x1e11e0fe0c6a5613c1be05a2a67781c55ffcee12a4ab0a30c37828695c1b63de0447d89e4804dffeee4aa3ab0a30c546a464027bc1ae8f04789e6944dffeee2aa3ab0a30f17f8141190ee279b582b8f7ffbb88a8eac28c30de0a1baf06d8f78162782b91f137ffbb94a4eac28c30d9a960a02bf06d8f78111f627920157ffab94a4eac28c3a2bab781904e65648035ffeee2a93ab0a30cf15c30a04bb20c0c13c21d3758272afff771149d585187053c078bf837c0815f13cd308fbfd549545561461c0b708b07c0534604b1bfff549d515585187050d4bc07c0b8bf83412f13cdb89bffd5ca525561461dac12f02dc22c1cd430147fffd5475255614618a8d48c838344f6d1d08f13c15c9bffd5ca4e5561461b06b52e0db20f02b1e40eb4543f27dff55a939558518703345756d09cdd48a86bffd5c94e5561461d3012f02ec1dc04d1701509c8fffd5494e5561461),(0xb65ada9fd96485373c67f5f452b4853df32224c1b312708e000,0x15311c61261401b6331b7ffd62769d2911869c2b22cb05485425f8ab9078020fc1a22c48e1b9ffeb13b4e9488c315dc8053193206e0511007dfff549da74a44618b2c148b1238ca4c4002e0cb0972150552a524103b068278c288e7ffec5ad3a52230dc19516582916247194988017212e42a0aa54a4808e20760d18392cfff58b5a74a4461c148b2ca4c5ecf103b06828322ec1c567ffec4ad3a52230d9445d84985006d8cc6dfff5895a74a4461c168b2c14ca4c5ecf106883e8b028322e5e7ffac4ad3a52230c0bc32a2bb900a632640a22011bffea92b4e9488c3a0d63c83483845a4b90ad25a477ffac4ab3a52230c1be0ae52f00e20034f03238117a0e2b7dff69d59d29118614f42b82b54b94b483880a0bc0f03e45e838cbffedc05674a44618388356104568292570803f7ffec5a93a52230c576108b9256c1d080377ffac5a93a52230c1c41ab0822b41492b8401fbfff62949d291186c208ad0690724ae1006efff58a5274a4461),(0xb62ad4a489ae91486279a70c65a5a84ef45539c2d81d20c5000,0x2c1c91919510a51a15c6efffd8b5454e446191ac1d17251983a15c6efff58b5454e4461857b0724646544294612c1fbfff62551539118615ec1d19510a5189184b07efff5895454e446195082ab07d0626c25046544294227bfff62d4953911860e25c40e45c95082ab07d062504429422fbffd62d4953911868485c11c214e9415286dfff5aa5254e446195082ab07d0626c25046544294227bfff6294953911865420aac1f4189b094119510a5089efff58a5254e4461b4a5ea0145f401c188e22db41ca2e567ffed56c4a52230e84780607d9060b12e03f0f5fffb96b129488c3694bd4028be80351c5b607c84d45cacfffdaa5894a4461c94de8dd4be8bd612a108c11c484c4b0bcfff5aa5894a4461c1cc1bd0be0bd2fe2fd1ee1e841c19c18283b0ab09c16c0f42ffef7095252911869a2cb05485425a2c304c84c153294a97bc40ec1a30a48e11c239fffb17b4e9488c34d82916642a12dc820d107ec7a471838bcfffd89da74a4461),(0xbd3af6a3e96d8af80974b6775c54fd4033512ab1ed14a0a4000,0x7245960a84b90a652952f78e0c81d61413c840373fff62d6a5391186362f60092f900e0c23081d60e8402b3fff6296a53911874b1bc9bb17c97b424c2113c0e91822cc20199ffeb14b529c88c346f0a740f45f50846103e896a9541c567ffad56c4a72230e83f06780590706ea112e03f115fffb96b129c88c30a740f4a545fc194f103e896426a94567ffad52c4a72230c6e4a450c085a6e0c7aa5b0dc1b62a10a0a8657ffae62b4a72230ca6425e83590138126232a214a113dfffb16a929c88c30712e20722e4a6425e835901262214a117dffeb16a929c88c3837a17a0f0b5833c17059c0e507e05613e0142382da847dffdee12a4a72230d29517d3c20ef81416225aa5507139ffeb55b0a9c88c3081aa5a41a3d68fc1a4b80fc457ffee5ac2a72230d1bd29517d3c109a0ed07aa5225c16159ffeb54b0a9c88c35c148b07e04470a4885354a237ffd6a959539118652215ac1f4191949209735088efff58a5654e446197092119652215b41b5089608efff5895654e4461)] i else tP #[(0xacaa249668a87ea7216945d652649840c3442c224e1860e0000,0x3c068bf833c020768395311008edff549d87524461a37841552f01a4781db1e44b82756d2b3ffd6a961d4911868de80bc0504809fc02075101532144aedff549587524461d0a253d07f00e0cf03f01614d4e13c2b9fff62d59d49118636a382a9280f0258f0ae096a0a428d1697bffeb54acea488c341ac7915dcee1468b46fdff549567524461d0ad07188f02b08f01c16d4ea0e8272afffb70159d4911866b270b08d0621446c44e94e82a27bfff62d51d491186c1c9191b113a51a15c6efffd8b54552446191ac1d17251a15d8386efff58b5455244618dc80810b4df40818dc83c038342141f8bafff5c9d8b4e4461f0084b61494a213173fff62d6a93911862384b60e94a133ffd62d6a939118637202042d37d02063f0020ed442300852ebffd72762939118741fc0fc03832cef50897021c8afffdcb58a4e446182c97010a06742c18f816c2bc03833511c80214dafffdc958a4e4461),(0xbd1b43a879a78fa81d75f6a15fb55c4b63fa3252441930ca000,0x10b5e01c1ba4904f83235ffdee12a4ab2230c5e087a5e0e1b15c19e0764041c112557ffae2ec4aa2230cb845e42a0870320c7a5fa2b425c1ba76e8e1126d7ffee2ac4aa2230e3e0cb1ef03f0101820e26cd4326bffd72761d5111876010c0ce8592e105831d8f706f0600c3906a19b5fffb92b0ea888c3a124a7a0fe01c180d5e03a86c28278573ffec5ab3aa2230e84e838c4584781780e0b6a1d07409957ffdb80acea888c3a0dc082e02864364290df88645fffee2a93aa2230e74bf4574ef8338349b02048afff5c9d85544461b07d0626c25047044384b94323bfff62d4955111860e25c40e45cb07d0625044384b9432bbffd62d49551118628b04220b03ca9780f0623538ac25b0a4b6999fffb16b54a488c31458218dd10581e54bc058bda111aa12d83a5b4dcfff58b5aa5244618a2c11e03c19e00c288d52990804f6ffec5aa4a92230e14f0145160863764f62f68446a84094c2fb7fd62d52549118681e10554bc068bf832076c7912d5b6838bcfff5aad87524461),(0xb9eae0a229408767ad71f66258f50d4483b330d25b1700be000,0x3c23c1fc1985254b42bc0fc0383109cacffbd8bda2549461f08f07f06952d0af03f02f0042160e2b3fed62f68952518701e10616bc1b0bcd4ac2b063c0fc08c8347b038daffbdc2549d87461841c0785af06352b0ac18f03e0cd1e8272ebfef70952561d18629d83a37d83780706f0659030a296da617cfffb16a92ace8c3829e01c1ba5b04f83235ffdee12a4ab3a30c5346ff07f0692fd08f02e0d7204132b3ff962768159d1871625ee0ee0c84fe03821e07c1981ce9882666fff2a4ed02b3a30fc230a213c95c200b9fffb17b4aa4e8c34496582a42a12f4838320744f18525d4bcfffd8bda4527461a3c19a3c86103ac1d2ea3e7ffec56d2293a30c20f839a978178040fc12e07115ff7b84a93b088c38a585f8f181de0646865704a4804d7ffee2a93ec2230d7042c5c04285b3c2459606fc07513832c7a19b050e9fff5c5da7584461c5b853f0732ff01f03e0c82582726bffb70159d61118716f14b0bf1e209c8d3058cac902094aafffdc5527584461),(0xa469b89198a57f47556d363b58b4e540536b2ad1fc1560a6000,0x3021c1ac1415b91ece86fffd5245634e14a19f80f81e8f02bf239a621611f7faa92a869c29439cf2382b89289fffaa48a869c294304f808d4bc07c020b012ccfb03c9bffd5ca5234e14a1cf80781f80f8129684784711fefaacea469c2943810e0dc8e6480322fffeab2291a70a50e8609781160a666831c8e3fffeaa2291a70a50eb6607821e05e008926d581e24a4dffeae5a41a70a50e081adf81825e8f7239b8a09917ffab949069c2943999a702b18582598519339078072388ec0c2161b7ffab929069c2943607811c04e406980ae4803fffeaa4a41a70a50e087817849add82e09f80e8f607c0c157dfbb909069c2943040066d4ae37c03c0ac5904c2309ffdd5654834e14a1f03f01646f0201842cb1612523ff7551520d38528724019c10f02f00b0dc0f44912527ffb559120d385287043c07c02d1391c15d04c4948fff55434834e14a1),(0xc2db9faefa329688ce7ec6bd5f451243c37f2a91f714c0a6000,0x1e07e01649a5d033030377dfec32b2271a50cb8c6ec0560da0a8b9097686c9a4f7ffac5aa2271a50c3546c637602b06d0527042e84bb432bbffd62551138d286066c2e102c24a47c07c034368474ba060befbfd865444e34a1f01f00f03b4ed2e8188401fbeff61949138d28616682a0aa82556fc0e8de94aa185ed15a8d15a8dcfff5ab5874834a1fc3cd05c2cd0551bf81299aa700da2b285a25a8529303358f39008ed1a299ffeb52b0e9069430d51b340d8dd80a066c788b505a4b6060befff5895674834a1853d0ae0ad52e52e12d8de86282b0880ed16e0f36fffb70159d20d287c2fc2bc27c228df81d56f41bc07c01436830ccebfda8d864834a1ab7e07e1546fc08a4fe03e008c4a3a567dfad3ec3241a50c4841be85684a0cea97806c6a0768b396a0c19df7eacfb0c906943e05e0de0a6a5613e07a3d81f0264dffcee12a4a70a50c3c080b3c0fc07c0006203c0649f75d5675654e14a1818352f01d1ee4704b82c36d22fff5729491385287c0fc0747bc089000b0d320608fdfd5495244e14a1),(0x79c6d261454a4503622bc21615809a000,0xf0af09f06f0532fb0bc37e07f03f01a102ebefb70159f61928742b41a24dc7bc0f81fc074cdcb5064aefbf567d865234a194384b637602b06d0527024346c4339332fbffd61d51148d28612ec2e06742e062cbf4bec7b478a4781f813436d0e4f8fefbfd865445234a1858b0b819d0bb0a857d0a292c12f01f00a45d3391d3bbeff61939148d2868de8094bfc0115a14d5ee9e88cfff5ab58a4e34a1a37a0252ff0045682a57ba35233ffd6ad62538d287c294bfc038128df84bc0fc050615ecacfbf5abd864e34a1d0bd06f01892612f03f00d2e74c4402bbefd52761938d2864b98dd8088910ba06449c7efff5895644e34a1)] i)))| 15=>(180,3,8,U (fun i=> (if i<8 then tP #[(0x9e19508af8137776d46385b251647a3ce3322a11f513809c000,0x1c2383701e058358a82308045ffd5ab521461a708e0c04f81f00e05c04200272befeab4a90a30f08e03c1b81f00e045300984027efeaa4a90a30f07e01c1b81f02a4004d9681927ffeab3a90a30cb059c1b83b4ae04c7b06d2002657ffd547521461e15c1807703e01c078102c0804effdd85521461e0008e90702c1a124160fbff561548518784706691c0f8052068e04c0c93fff559548518784706e018378152068c1000993fff5515485187304a0a706e0183407d20826d142017fff539548518784707649c0381344a4004c0c93fff559148518784707e01c09a1e0da4004c8fffaa88a428c3905905383b1ee03c0a09e0d824d08bfffa9c8a428c3048a0819e110518bf0001f48209a1608067ffd4a4521461e11c1f83700e07c091d5200264fff5563521461e11c1f83700e07c0a0933b04e4fff5543521461),(0xac89fb92c87e7af70a6635bc50f4693c732b2881e613f0a3000,0xa0560960a80df0be15c2707701e004700e8343afffed3a52230d602812c1501be17c2b84e0ee03c000e83422e75fff5a74a4461aa84117701443c0f8040f22e8382a17fffd61d2911869d52ca542b05700a4188028f0381ecb48ba193bfffab3a52230caf05e0ae01c0d9040f22e1009615fffd49d29118784f08e0fc1b81f01e05c000703f2bbfeab52b0a30f01e11c1f83703e01c0a2782769857ffd5495614618c25f06e13c1da560de044b59dc0e2fffeaa3ab0a30e568ab85707e0dc0b80e0d04e0e0afffaa4eac28c31f09e11c1b06f01a2ad1da340e2bffeaa2ab0a30f0ae11c1b80f00c1ad401384d27ffea92ab0a30c0e15c2783701e07c0a0734507057ffd4e55614618f84f08e0f4578133bc1ad0e0715fff551158518785708e0f13e06515e03835a70272bffea922b0a30f0ae13c1f80c0ee05835a103827ffea722b0a30c0e11c2b84b17e0303b8021609a57ffd4a4561461),(0xce9c37b47a969b89158647a06c65f34d33f633d27b1d50f0000,0x141d09233641c0f8060c41d509190542ffffac4a72230e50328512c21206416429f0be15c1f80f00c1884ea101f477ffac4a72230c2942a83f01c188c58ac16a848651397fffd5a53911860dd0ba0e16a0ce0b05981d90702e01836a134c0ae7ffff5494e4461b218f85701e07c0b8054241c0b0adfffb0a9c88c33205f4c288780f03e0083c8ba0e0a85ffff5854e4461c682c0c859e148dd09f01e0183507d420586efff5854e4461c542b05040aa594a906200a7c098ac166915090c9ffffd5953911860dd0bc161039006288506780a0fa3d059a30573bfffaa2a72230c1ba174283115005486d85c19c1615d8560a0a69410cf0064083e0b11757fffa92a72230cc21802f85e0ba8a4ad701e015130621b22e838a09ffffd6b1291186e05b0160df0285a083c078060ca8814cc9ffeb589488c3c03416428941e11c2a8bf01e0103c0fa0e377ffec4a52230c248ce84700641c0d0740f464150afffeb129488c3640d01c0a3c2f85019e105068ba13e03c002c40f03e86fff5894a4461af0720dd0bc16c8297e2fa3d87820c1983151207b4c0808ffff5494a4461),(0xb0ba5a9aa9078597b370165e5a54ec43a3972e52231720ae000,0x42942a83f00e05c060b54e65a09d0c97fffd59d491186d782c16607e01c099dc16a9c15c9297fffd51d491186cf0aa9c0b380702a41511070402b7ffec2a92230d9e148dc20700059c0f80d4e41e09cbdffeb0aa488c30a702e03c0381b48a9c10013a192bfffab2a92230e0b0318bf0f702e03c0da354e0ae100bfffea8aa488c3700585b04216b80f00c181880e953ffd6b139118728590a7c2b84f07e05c06a12140d40e0cdfffb169c88c3702c853e15c2783f02e03c0e8f54241c66fff58b4e4461c2888f85f09e0e12f80f0003b830a5177ffd6a93911872853e13c1f81703a3cceea120e2b7ffec5272230d074228e78133be01835075424d21a0bfffeb149c88c390ca14f85f09e0e89d9df00c198342cd42377ffac5272230ccf42683f02e07c019dd4241c15d0997fffd5a939118730140ac12f0a221e17c2b80f00c18074201b7ffd6a5391186c8650a7c2b83f02e03c000fd4241c5efffd894e4461),(0xc13b70ad8a278f382c7706545904cc41c36e2b52031510a3000,0x7045fc240c702e03c000ed4341c56fffd87544461e1c2781700e0350c0e8130304efff58754446185284d07e01c0b80c16a86cb409a192ffffab3aa2230db115a1b836c2e85e0b60f41f0386f09650c28c434330649622cc18c78a64165ffffa93aa2230c1210028f080c68b107700e07c0507d430d26efffd8554446185284840a11c0781f0041f50da401343267fff565544461968520a30ba16cbe97b1ea3c08c10a1983382c0c62fc3c83e0b4222dcaffff525544461d816428841e15c2383f02e01c050a54e0d46efffd8b524461b816428841e15c2383f02e01c0e9054e41c6efff58b524461a9701c2908785f08e01c0f060402da5dfff5aa524461d814420f08e0fc0b807030615390717bfff62949118688410c7c2383f02e01c0f80d4e04409ccdffeb14a488c342283f02e01c0781d4e47e838138572ffffab5292230f01c2808785f08e01c0b8194c08015cbfbfea92a488c3643622fe15c0b80703e03539070182f7ffec3a92230ec0b3c2b80703e0353b0602703056fff587524461),(0xa3c9a091f86d7b57196765cf5284813de3372941ed1460a3000,0xe13c1c38702e01c070681304a4cfffdaa5844619f80f000c5837060251e7ffed3ac2230c5b0a7c1f80027e05c078181904acb4bdffeaceb088c35c5b0a61b383b75e03c0381e0c04e094cdffea4eb088c3098390210dfc07804160b483c9dfffb4ab088c37038013083c0780506c1b83029953fff69561118784707033c0b80f03e0009e920742b7ffac52b2230f08e0e06781701e07c0009d240e656fff58956446181dc0b80f03e014902b813699064afffea92ac88c3650552404fc0b80f03a2a0640c15bffd61d59118607702e03c0f805240ae04ca54192bfffaa3ab2230db035c1c39021e03c030606f0e254fff5ac544461e13c2383a14e05c07805430d404cadfffb16a888c3c2784707047c0b8006aa7750d0715bffd62d5111878051e11c1f81700e0207ea1a0e2b7ffec4aa2230f00a3c2383f02e01c06a181f02656fff589544461),(0xa2e9758c780a7796d263a5884cf43339b2f82721c512d09c000,0x2986fe01c2b84f07e0dc0f817014284b4ccfffb16ace8c34c37f00e0fc180cf0264183409d2d2f7ffac4ab3a30c1460ec1813f01e01c0f06013a5ad320c99fffd52559d18780703e0218828e0c25a09c8defeb0eace8c3c2b84f07e0c4be84701e0783207157ffb68159d187870a0a3c0f80e0c0e54782c133ffd6b149d1870a421e17c2b8312be03c03818340805dfffda5527461ac12c28e14843c2f85701e018300e97532fffed2293a30f09e0e1c381f02e03c0007025267ffad56c2230f00ca09781701e000382c01f267ffad4ec2230c1e0fc0412f02e0007da640e0ae56fff549d84461e0407780f000c4038128f3ffd69f611186b0a61b383b75e05c0f8032081c094bdffea4fb088c3c385041e05c078054401c14c99ffeb4bb088c3c1e07701c1808c10b1e0c045fffda7584461c081da07701e0008c10b470c04dfffda5584461),(0xa2097d8e78447a16fa6535964f342439e3062791dd1240a3000,0xe018f85706e07c07803470a61cca9fffb4ab128c3ae0e16b81f02e03c0037873267ffed22c4a30e50c7c2383702e0383411d150b054fff5ac569461cbc2029072e061638060c0b20f8a9ffeb58a928c3c0784707e0c85381f00c195301395bfff62d52518780f08e0fc1810f03e05c010754c2b7ffac5aa4a30e14843c2f84707e0c54a84f00e0583608997fef6895251878063e15c1b81f02e03478070582a7ffad4ec3a30ec80e1042d706e030be0c40ee07c0a8f34c06476fff549d87461e07c0b80f000b40380c0f3ffd69361d187bc0ee03c0306023042d102a937fff69161d186e703e0406380813a3c09c89fffb56b0e8c3c2b83703e05c078005882009c99fffb52b0e8c3c020c070b5c1b80c18e078328f02769866fff5495874619f80f000b5837060181e7ffed22c3a30f00140bc31703e041478082107054fff5ac567461)] i else tP #[(0xa249728cb82477d6d662f58c4f44513ae3162731d01340a3000,0x821c0b84f05e07c078040f6860600997fff551138528781705031c0381f0181f04da702c2bffea92270a50c10e05c2783701e06cea8f40f02657ffd5634e14a1821c0b84f06e07c068f33981e04cafffaa869c2943c0a08706e07c078041381eccc1615fff548d38528608702e07c2609f01a3d03d8b0182bffea41a70a50e50c7c2383702e03c002c60d02654fff5a9d8b461e0028317030a3c070631e04e4cfff5a7d8b461b606b8385ae03c0f8060c0de09ca9ffeb49b168c3940d708e0fc0f8170001c16418153ffd6ab625187870a0c5c0f81700a4003828933ffd69f6251878063e15c1b81f02e01480070532a7ffad2ec4a30db035c1c2d702e03c000706f03e54fff5a4d89461e11c1f8305ce05c0306d200264cfffdab589461e11c1f817000b383690013227ffed52c4a30dc0e004c31702e03c0306c120a254fffda7589461),(0xb10a6a9c491e86c7ba70864459d4c33e93372901f415e0b2000,0x8dd0170ae0dc0781f000594b92695bffd62d38d28637e05c2f83701e07c001652e4f456fff58a4e34a18df8170605484f80f03a3d4b91a95bffd62538d28685d06e03c0b81f00a5cd330782c0805ffff5494e34a1e17c2b8360446f84b80f03e011169717beff61938d28705652e0588381f006494bb078190305ffff5644e34a1a606420702c25c5780f00a1a88a9760f0306ffff5444e34a1e03c0b8070369d4b80c60f0800b0afffea489c6943e42c82ae17c291bf020cd43784a13e03c028b2343f7ffac3a41a50d3a1582b81d52ca5c0a90620032c7a8b32dc1e060ffffeace90694343785f0ae13c211be07e03c01065162f7dfec3241a50f02e03c1b82f03e0103c09b4c05857ffd5494e14a1e13c0382f03e03c08968130304ff7d5674e14a18706e0bc0f80f00e0404c1613ff75595385286003f83705e03c0381f78e0404c1617ff7551538528608702e13c1780f03e0103d920180265fffd5644e14a1),(0xb90acca259738a47e07276795c752147b3d53232711760a7000,0x960a83101904bd138af03c3d4eda85394686ffff5255434e1e05c07be8196498429c857026094afffeac8a869c382f03f03e03c0b8061069d4e42b8252ffffa922a1a70d8a1582a83606033c0f80f0262b4cf0834805877fff5655234e1a34282be0ae8fc0781f0262b4cf083240326ffff5645234e1961440c82ce8fc5781700a1a88b0813e33fffaa2291a70f00140dc178410a3c0f80e0c0f20f4b9ffeb58ace943c0385709e0dc161be07e07c050832d2f7dfab3ec3250c6fc0b85706e01c0f8082ca66934adffeb16a469431bf02e17c1b80703e020b299a7a2b7ffac5291a50c6fc0b83041427c0381d20a668d0adffeb0ea4694342a83702e01c0f80d33c1ecb4160192ffffab3a91a50f0be15c1b02237c21c0381f018a14ccbdf7fb0ca469432c2082361606685e0b031c0997d2fc5f9f30850d44583c9f25fffd51148d286c30b03342d8550a0afc0b80f0086c0b30791d3bfffa72291a50f0225fc0385709e07c040c60f2f655fff5ab4e34a1),(0x32626217d0a3000,0x2b0490b2c1e83e07c25c0b80b4481d8449e1bfffd39158d506d05961606685e0b60f41c16607e05c0286a226850f90fffe9c8a46a83581506261542b05306a0d81b81f01c3c4da9d2343ffffa92ab1a70d6c25d1f81701c3d4e809e102e257fff5445634e1)] i)))| 16=>(38,2,8,U (fun i=> tP #[(0xa309878f185c79e7096415b151b45d3c93202811e211b08b000,0xa0329042810e178460f836018141a181bfffaa4a30de03e0d856120c607816028f01c5dfffb0e8c300bb07c1823c0b018351e038212ffff587461b8140401301f0bc2706c2827c04188360c478fbffd61d18688f61584e0f8360381c18968325fffeace8c358580a032958550a04385e1583e0d0623d06a4087ffea4e8c38561184e0e12e0580e000b01c55fffb088c348518460e11e0580e000b01c1097fffac2230d00a04e1304b85e1584e1183e03804180982c7dffeb088c3d856138460e926038122a0b0325fffeac88c34064238530bc2708c1f00c0b010582237fff544461a03210c2985e158460f802410603e67ffea488c3406c19c2f0ac270783b0147a0c074cfffd39118780d8340c8300a6178461584a2f076038002c07a1fffa52230e1584e1183e0d80a2b8141a0715ffeab0a30d308c1f06c0301c0813834122bffd521461),(0x95b8cc83c7ac70c67c5d85484b84293993092791f31540a0000,0x4eb0ac2707c1b01c0f02038382bfff5634e1c2f09c1f06c0b014361e4e6102bfff5434e1c2f0ac1f06c0d20c0a1e4ce102bfff5234e1df0bc2b02c2706c1413c0f01c003432fff5874a1c0b00c2b09c1b05c0f010e0342bfff5674a1c2f0ac2708c1b050de07c0f01c000c32fbfd864a1c0b0bc2b08c1b00c0f010d8352bfff5234a18330bc2b09c1b01c0f004b8342bfff4e34a186c1985e1584e1180e008b41e57ffe906943816138360a09e0780e000801e57ffa9c2943856138460f83607816028a82855fffb168c3856138460f83607816038001c55ffeb168c38561183e0d81e058024007137ffec4a30c833c2307c1b03c01208300e08c3233fff589461cc1404b0bc2832c2307c1b0004e0d831203afff589461c40ec2b08c1f0648303831150642733fff569461),(0x32e2b222219c116090000,0x30bc2306c1703c00300d48fffd49550709c2307c1b03c0b01c003f038afffd58d5070bc2307c1b00c0f020f83027fff523541c2b09c1b05c0f01c083d0e09fffd5953870ac2707c1701c0f020f03827fff5644e1c2f09c1f05c0d3bc0b00840222bfff5444e1)] i))| 17=>(4,1,8,T #[0x2170a84c220f0607406000d0617fff461,0x190b85426110682c0e03000797fff4a1,0x2170a84c1e0d0581c06000c0817fff4e1,0x217098441e0d0581c02020c0897fff541])| 18=>(1,0,8,T #[0x2c2824201c1814100c080400cfff])|_=>Z0) (fun| 13=>S 3 19 2 4 5 3078 0x6580578c180b2000020114015e34c04f| 14=>S 35 151 6 4 8 0x512c224b0006170364020316061e00331501240b010104570048001c0e03040e0051 0x10221304881c8920aed219b2b7156ce98fc56058049387bbb242f00c1a3ab41281a31a17428ad24b86556890401c0006a88c0520fc4b8c503e0d4470bc00631802257362084110480000049872c1120dc5fa531b4560ef92108e11000e3c2264235e03c002678039d98b63075592315a0280984e7a410c5785919c670009190700c80010612a1480a49204d678008c2a900052c9db07462800883ab44a02b134206337240b606169bde1a68362c000917058000d0000000d442d8190826bb291a511612c1792f6a6150d46c1228282a1| 15=>S 139 695 8 4 10 0x45054a10140903400018030440c028000046b1a003004040883e134200240b014350380b014210383e0082b0000a0581a000010780012c2601400148040dc0306c1b19c0f0600706c2815006150090340000c200142c00826000080f0040ac060040a028000640102c02028200241501c0e00c01008070580800c000e800000020100400000008000001a01800000030003600011000040080100000050020080000c0304004004090000208405 0x31e00bc16084400a631f3bb065393c20a76d182504636f22e05183240770962db000000b020f27000203c106000000000108580c805c00000682e829f28a0008664cb3b24000e02813800000000071dc00011e00000680001720004ae64a80006034051c6a02c05070481a835301a8ee8edea9666100000000000630000150000802528b95a00088201c279e0550d502ac00000085a0000000000012e52c1846ca35b0001b16c4a02f85a739c18e01bc6d83170570e5000114266803c00000010b89130000000e38824b86a031587932e14bc8212400016dc2f00150a30001c9a08f19745ae4b10d603f09773b00008481f6000e0008905f4e4160009b88892410fc446cc9640e800085e80009a21776b5824e12e000a62a5ab2f6164010e15000114306c51b62e304a60c454603909c81802f0037031804c6300005c9f39ab440cb4c0825b4d834a6758410000d7119800076bc0d603d8308003a76000000432e0fff4800001e80060000007e50001c4b0c0c33c000000057c2d47b0000000050808ec14007000026f05ae9936ac0ef00cbe3434ef7c00000001e41482d181c92fa0981258a7431400000023d45b0b80000000106e13d08029b48a626d3c902682ce0c618d48e05481190b700042fe0cfc1188e01c61aa1618af8c3034102a0bc8628000157000000000030f8a6c10800153781fc33b22c8aa805bde0020069000497c001cc48b7bb4834506879e0003956000000226400125e041800397b0320000000000000000000351400001101f01642961ab80f205a06200071c723ea3d02c000010223d827c22421d1948b700000000d102044300c91480bb05b719200000046e610d0c10006cd211d045820846173400004cf14e15d36b3e904f400000000001b216356800041ca39e01285f0d4412991ee5b431c44e0b042880a00001b481f0002620033013db2c08800090606080d40ac029c94c306059a63613032415a08101eed6200001d0320015e8f00048f007137283355ae37198985d03363921cb861c26f80600000053275930564d10284004c2300041d400000000034e4000e688b84d962828a90000001edf354054800056b09a00fc1b413b034eca488e04c0008c80d660a022dc6405a8000000851003f866000000064605c0bbadac5140ec0528cac0be0a3d78821800129f07dc98d0607b200011440047a732d000049c172820ad10511b1800008d80da1160168d9f23c994b2b485f0f80010d205280af30a91300e8000108000c1f19c828e024ae5066b6e509f043c16c000046964e1a01314b683781802e810b00071321a1d2f00023001551260c9a1fed6aaa9cbe825401b7d586bf339b411c5037000001005c848c235893c6dc5f036a41a023f224540336cd16a800006be00068bc3127a2f3085690160220549152a880018ba039ccae02713c0007109a8d0a60000f3b436107c2587191b03273db08042b721012b530b2e83cda97c567b1c000107883a1140008240897c8a9cf6a0847c180000bea000314f0b600046d62d030906c8f18000000886824b86422c4400002f7b4d292b900988e1ce| 16=>S 127 633 8 4 10 0x180381e000001a0000400803409060210040202c4a048280200311811000010040e0442800c010543400c290980005c09030291900301816050060200c0001601c020c0040003e0001d010000b40b0600c0000200c5509c14024000143f0000a03c1600c0e0081703013074040140004801004280100106c010080101c020040101404000130280002800008020200103400008130442300003004000240e 0xad8855514930141820c5034af150818b00a01510852c800009203900062c4286000006404e02406b99e45682780001d6a1040e0a40f9471ba29313a5a9805e4b406901c4c4428c00000000000eb21109cc488000000203523c24ea5a024466211515ed54446455920389b84e015cc9e894dca806800082b452271617989b224e0f409680afd44059c6984eb1aa28e0883d0c22c1280454465e9ce7b07de03a24007c00000075ec00101e60c0073e280000001290f31074000000203200050a800085e00082eb0222e9f532c79ca000000009f0098001e1921d38dc11386da9dc2c8a9000084d751c13721c1a5e1908c049c83f000027fb0900000034dc0008bbc23c0001889ca009e258000128e45400d71500050120450798210281282142017403410703c3c6c0a491784f29a088c002000843cabf76202f000328ec7a00009180000ef00f456125e28800083740d4c54000c53000200b22400000002fcc7a000413812e0730b9424c000133000415628a00083e10e213158b205144e8fc05822aeea021a3230b5c20655605f012a2a603e13404151f4001111000006a06f869000796a0ae000a4f000273011588741ee0e2c32027c4258391023ce005014500b59c681aa71155228de2e11b085925014a742329c13845c001166000095c0000000004153ab00000003a34000000843021000000024e8000047053ca7e07000007f8d001a985e00000059540018a100029b0a820000cdd0162de00081002cc15e06600059140000000001a2c001f95818000025000000045dad6000000042a6098aacda590492ae0001ce0168c1405c025d0a8b6800000021c61220001c8416d85b4a9853c0aa05000088e1e748a6078885825607612ac3742b029600989ec6ac8110a4039418a4bc00043780010ba0650000230d5c04788644d409a00084000000a10430ac488836719eccc816727e00064a8a6233f3a4a890000001ba100035b800003f43502400009190005e7e030000a4a800126f15781d424b070d1305580020de0005a70003e6703d0004538001d1000041440200009910000000016000000029ec7d31c0c9103000089220bc000e34825065800100299380d90640000004c70236000831c87ba781a89d0455000129188d00020c10aa00042660c80a120a02d00000002d77c5e14a04600e800013d897f22841cd651530d18000067d452cc30380010b0c49000e314698836a68480406102221b20ec00088b401243e99a010c1b0010068bd27ec58a3151895829ba35401833c28c11c39a0000ea18081a79d290f78e77a68c5905605a5b39c8e858d6980d84fd17a08155e65300ad4bc7084860533144d41caf406c15000eaaac40e2ac09c0969e3851699febd7025e10000000223c1627952550001a86d48812666e0bd99e1100c0e00ed1681940448b345f| 17=>S 26 129 6 4 8 0x1072315151001010400030b0f05061f0b0113010000011d0103 0x65d82512a2101490d0628d021000003a28004080000568c5c10451051c08c0140000f0005100019f091408000220000010684501811000512e030780000200000000007418000004048201491140ea2e0562a01690e074005d99bb16743c03bae00189659bbb14612888e21464238419b40002f61778c08c004266a0002d011d01604c00145a0307c0c9a5835006ed40de480020e71a836874124090000026bd1502e36650e828b51240444b041a5429806| 18=>S 7 44 3 4 6 0x14045000303 0x2c2900009400000000bb8c0000a3420069000001009be124c1338a8413bc91518bca02b4002b8300001c21|_=>N0)
lemma gm:un bk (B ky)=H:=by decide +kernel
lemma s0:uO bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,16,17,18]=H:=by decide +kernel
lemma a0:bF bk 14 0 73=H:=by decide +kernel
lemma a1:bF bk 14 73 73=H:=by decide +kernel
lemma a2:bF bk 14 146 72=H:=by decide +kernel
lemma b0:bF bk 15 0 60=H:=by decide +kernel
lemma b1:bF bk 15 60 60=H:=by decide +kernel
lemma b2:bF bk 15 120 60=H:=by decide +kernel
lemma ck:∀ k ≤ 18,uk bk k:=by
 intro k hk;by_cases he:k=14;. exact he▸aF (uQ (uQ a0 a1) a2) rfl
 by_cases hf:k=15;. exact hf▸aF (uQ (uQ b0 b1) b2) rfl
 exact uP s0 k (by simp;omega)
end F12
lemma signedRoot:u1 H graph 18 u3.toFinset:=uq (g:=F12.bk) (top:=18) (k:=18) (i:=0) (bS ky hy) F12.gm F12.ck (Nat.le_refl _) (by decide +kernel)
abbrev kAll:=ky
lemma hAll:K kAll:=hy
end FreeInv
namespace OneNot
open Engine
abbrev S:=@sS
abbrev T:=@tW
abbrev U:=@uB
abbrev E (p:PP):NN:=uB fun _=>p
abbrev V:=@vS
abbrev C:=@uz
abbrev D:=@dA
abbrev B:=@bB
abbrev K:=ui
abbrev P:=@uE
abbrev p:=@u7
abbrev A:=@aD
abbrev a:=@uH
def cd:= V (tP #[(0xe550d410c5a0b6a0aea0a7808c306df05ef03fd039a036e026c017c008300630000,0x1597f3f4f87af0f4530220d66b4763d10d35535ba4a054f578661d0b05c03c88051a71d18c66b21d9e46a9eb733efc7d22c942fb443498784793802f10082ae32318ad543338899ea7d0b5565897b7a947c0fc74dce86603c00d88482ce239300704e6a8bcf4181e1e1502981a9b368ac8e27d1d00414d0641c205a6e0eb6364a2e8884049f65278ef4b60256fabf3ae06be5a1e8d5c3971ccf33726ade1a07d80c92993305c0c987a9cdec005d8c302009a55b04068a433bbe7d9db65c9fc00b8144341f43dc28cf2a625712e48773c5668667b6687337cd12f6b24ece19b332f29221c9af96768005d8c20040ae5463a391cd666a1c89dcafd2b5f42f6f562164a0fda11e0d260023309059c531bd9e25cdce4a58379d3b366038d391e6f6d56060d8e6162c9eddb85a6d944c6a0292bbf103d6e3f68dd6501123d2cb49314e64bb15c001761080882c957fb8d2349a72da3b48b90129a4b4ee0c08533391c476230bbed742b550f15edd8bd5f7c96b62164a0783ef80d007a2120c38e8c62b550ecf23d3e17e4edfb7b5ae897b62164a0fc34980f003e4120b38c8c62b550cce23e6b53efa74562dd2f459283f1f34234980f27005b20105dc4871c08a50803fae02bccc563a1d204a6),(0x10100e290dc70d9c0a11099f088b0780071d063f05460387032502ab01bb00f90000,0x8a666dfd7fb60fbfa125a947fdbebcc37f0057f31b72c9fc18e2cb159b4e8e9690c24694f583d86ba344b9d442e2533c9d24c1e658c02b1438c0082b95210415667af02c5af07902537b973448214db13b42f400f07c1b9fe4bbe264e72f9b5326970162a42c39abef75ac20e3f86b38337dc5bdb16b59d904000bb6e1040ccd93741b0bcfc222486cd464d08db509f27c8511891788c4db40307e03717aaf3a6eea04106755044522d3c19d07289f05438e1204d1960000b596040842004db961bafeb1206e64332ee0c15082d3742c5eaed547b1183856690f47f3c777ab95e84eb30f41f4d979b0ca07802c089069c5432348f4f874319cd56ab1a27a4cdf8ec9dcaef5625f2d47c3db85800166100cb8a0c2b35f1e844c1f543a8094dd18c56aa199c43d376bdb12d6e5a9164a3e07ed08f26003d209051c56bb150ecd6723c8b9fa56b623a1b2523df87a17dba5ede8fc7c0299a402ee2dde2e0a37d9fcc37cebaca33e02b35e27c4822edb0982041994fe6b55d1b20ac1877bf4e97a463b13214e977a3fa96a9c003c8c281009e56a7e3e35dcdbf3f9c7434094dfc5ea7a05b4966f1570de5e0610313561d5915f6e8fc7459ac33590acf2053e97ebd6f63d1a9f0d801234a059c78dc17d487cde2a1eaf17685758319add2d1163d900881171183e9d4d971b0f473590ecf2345e17a4cdf93bdd1fbe2341f0f001451a0bb8),(0x1cc21bc91a9a19b317a4144d1251114f10260f2d0e460b3c0a02061502ff020f0000,0x3331a8c2a7907e1e64474a8a81c310b5b92f6c474d09d6602c9400c4c24177151a8622c4abad0f7d07d3a9b2f361161aeb3a08c76b33e2d0bd266fc9dafbe5b90068c403ae2338854542b5d8a8cee663cf01d352b5565cac4bdbd0fbe0019348055c6bf5ba43f0d0a987e78f19905b7bf55b052acbf5b0727e34f9f1affd78b3c3c75aca3d935601031a7379aadad50f3b307658c473c71ec0feb319f8006528206417ca9c9960be03f57c728ae38998bafa25a1855a3ca3c94955ace3240066fc195af8e767ee0175a896ad17464f240bb31595d4ec2860ed06e90b2bf06c620f8d8a4cb2bbe3a7a397a4bee46ce1a481b31e57c05b63d4550287056aea07728329f4433c0000b5960408420048b94f2990a79c787de5b883aaf76dc891d0ada5164a8b28281f7ba86f4e99089868d695dd15cc871980e8a9f6b78fb37d7dd5a4aa86704d23f402d946880082d9518c8d42b588ccbe7e7e95eca159623f1f1d874d4e85eb737a4cd6a05b105061c6441a91b02588278c91f3c5e2b90f7c18b7bf1e9c11ba5ff998141a82e9171680018c2034e6a151b956b3388ec562e733f03f1d93bf81d7527e3a6e743701e80644281771911e0f8fb18cd640d159a4689e933b9ea86a7536584682c00d0c682ae34390a3cc1503b3a52966f7c24fcdaa0c04dcebe10934d04f88dcc58d58b9625626e691b1e75c73e6fbf0a25e74b7161ef8884206ba14003453d76e1e10fccf22ab244ccf006cbe79b38a79f3f8f8cfd8f36d4a41cd6616000052cb0606210020dccc1e20a92a21529caaa7ca8a87d1358a0fbfba881de9c2fa4905036dab2cb53e3080200ac6038e77f81ffb1d799c791d5f97fdc23b73f9a06bb19b63668eebc3d41478d6cd778a2cfa9eebd815fedbf4bc275f6a75f8151a5a85403a7db993fb82e7efab0699c7907e20eda39b81481e59cdcf29e57c9c4151b91fb3f52f125f251e4346201593d2e6ba94e8a7f49563827b9e809db6d7468f27d00000b506080c420056b95d8f7379ba7526714aada897c9413598a6db1e29f9d11dc811f53a207a42357485296e6734d3477d960e56c1528994367d0dfd46a3dddd61105d94f05040c21861aa502e26fb26b6b67d3e89b6781c862a5885384d8cc8acd00002d650303108010ae66ab4217f6efe563ccaf6c5d1a88d330f5746a464a8149e0e00b5301459c4f0f3a2f06061f052b6223edf6f3a8211b3310fe8a7329f8ae0d0578b0196891f78734ef2a7d336dfd593ff8d5c8390be325a7643f6afed3f057c8006c28342017ca),(0x139e127510650f000bd40ab709c008c7079e071e054a04f0049003a0028c015b0000,0x3a763d38a53d9bcd788c8968a0c072122e7641771a2bccbd19e1970d71e8c83c00047101a7346151f8e30d7ce62098b8440a5410e813b1cda343749f3974bf264e7d62256091bca017bf2584cf42e3d3c4085f6cc1905aa68bd14e1061640815c00018c10482f95807082450948c6b839826722e8d08b20501bc77ad8e800edd6a1c036a7d79ad9898f7d0fff1c0080286080f3a974f7adc373e44d69fd74a3cc52a78b05651dabd9fcd63b83f54dcfb4251c75ca39d436c4c9fe64889d330e331411ad1dcce2467d2b48573059087b35924c5e2690a2783dee8759ca53b3f1d5cc32403dc4446e0951b60fb93b023800005acb06040010225cccbf7d6fcf19f8fbe93e7857cb3c8af3b423d108b43aad4cd65174159e0e00c630186dc7e9edf253635f76ba391599cf3222d1684562a9aca2c0b8d51c038c6010bb8a8f4291a8b90f8ea3439f8067a08c76ab559f13b1f93b5ed86f201d10c05dc589fc5fcb7ab8e0ad067acbfda0350d230e8e03ee773938245c88bc664b20e800a2244034e65ffc1ec6dd48ad605d754f82a620169e2ed8b844c9a4a1caf9b164af394cb0f85ec87d2256b31dcb38c0eb972a10f1cdb6d037dbd275fb354be573e3323fee264f84180022c618110532be4d99e71fa6034ab20c426a1e38ab179f1cdf442a304a6e8d463021f91fb735ae81d6b270c452276bdb15e459281e0d002a3120b388c547335aa8623c5abb94ee57f23aaf5583c1f7c0fc74dce84d979b0ca005a3100d389b40eeb9e7b2c1842ffe937327e3622f1e3bfb0ebe12182105c0055d3cb79194c00011c506dce2074aedce1f2cdceba79eefa6d65769db19520f4eece560305b5f09d62fd39c14f90e801c0000308110eba),(0x13cd11c80ff50f0e0e9c0d2c0c290a5609660864072805ff03db0231020601160000,0x147c3fed6e0ad64f34fc2508d03687613f99e9236ff1ed082b0c38c72da401444ffec242c7da2bbf4782efe7593b644af14578ecc06076112698007a186440174ab38cdffcb4819be47dc7496cb5f176bd42dff384cd5470e31fcdf087227d235c26bb1b811e7de58a01c3cf91964e4d82fa3f80c00452c300229955168ee37b50c452375b959bc9d360364a4c674398aeb035800ab302ae2c182219db35c05c95b2820a505a6d61b36a7ff053898e5c388f6f16fb70252323b1572649e4c73497d80c241cedb88bc6e35ea65f1c0080506080fba9deb451dfe74bcb4e74d430f23ad9395d395459f14e3f101f29690101c414167378cabd19f7bf0c558c09b301895483ffaec10ebd9ee02cad6a3aa207e47f0d179e0239d4c81a179e9d70b3b5e0e776ae1e7834002ecc10020532bb5a17f3f733e35f2f6c5511a5d3562b3aea56aa8b91e0e02917298082ce2a0293f1d34273391c33391c456bb158f03f277e95aab06a3d165800326140c38b3ab10865736c3e76f44c428aade66c57950ad25db2b3a113d043335cc4a0a09bd8003888240e39b4f89ab5e6a61c8cd1bf7393f45e1cdd7e2e7a0d231b037f633733554e0ffc001e0c92069cc2ae11547b64e1aa9e71807368551097d01d3a6369dafea137351d37dc612c9bb492965a7aec91d1332923ad4475352ada82e0bec4665990738460961dc009a861a100c6548c95aead5a715f5d48dee2238aa25fbf1f973282ca4916abd5082cedea33bc4b769a65078617b9c19f46886546c000ea50608025950284353069711489cee37bbc88d4374e259bcac1a03618e3274988aeb035800a6302ce39ccc9a22c7cfbf33dfbba6172d1639116013a05792d0933621d6515558000a7040c39),(0x1a301940179f1587155a143a130811850f610da209d6079505b8050902f101dd0000,0xc89e2b599ec8aec4ec95e87e6f499ee3d82910de3e9a95adcb49a60fcb48c9b8383df91f8ee4c5be93eb7506cb17c701122be0cfb7ece05150f0a3e59ef35a85edecc1a3055c56361f083000558c202209255929d17f1918a0252a83479a7a588c3f3295a6065093c1b76b2bfcffa0377c63d9bd9aacd648a41f07e5fdddca103af964bdaf77414913d3e2bc5c30005d8c30200c2543d88514065688a65a1a8a7f8de7617a68d7c9ef5ff9a5928124c7e6336276c183a6a6878002941032e7b41308cb07640b28a3170e4cccf3fdda499d88a2660015f1dab02f0f3e82d61b00016a040db9c4aca8bbb4e552f5593ec034583acb368e48acdcaafb2cff6233092ddf2a3584f83a9b4664d1bf0b93300100708242175111c4d9ec8410ee26567854daa012419fd40e3565f0898188935d49c5d79cda349843974dd24968ee6bbe094cad53dabe9dfd21f6b154dfa1eb569142631018030c24319580ba7f6aa080d537633f333fa7ec80fcf5029c66708078277ad9b7c19af40267655ac646b72120bdd996e1e7ec79db0160015620c1104f2ae6a9620bc03fe67febf75e969e8a36461f6ad5d1d705b8acf1c3f269b4827240409f490601af63c75ee82a37a01e80df6a92df57f2b17e164a861bfa4f8b99beb12f5b00f6330d43c3f4a6ae05281422a20d8cb0ca6740d7a92afb8bbb364a366c20eae2522bbea3da8c81bf6004cd400016b2c18180400a7725c39bf4c1e327ab2f60e4519b0debc2619e4be2fef2327b8304c1af4c94bd695ba1ddc0e1d5440710f8369f9c429bdf667e052fcb7f4f824105ba7c0d9d09ec00016a28081803197dd5612510ea7c350ea2559b5057b39c7fd2119698d086008a9be569f3f08b4950fc3ac4a272e0f48c4b9deefd934c101f9fa52d2000150c2040154ae4eabe2e5a329114cdf89831c6546e23037515210f7181aa38ae5c8dcb2de097ece9cc867f6ee10919fce838a0177324edcfc6be71884bd35306c63c8572312e7eb1141b6b16cf526deb08f379310e65af9000cc50c8403095517088aa1883468230755ef69575abce64d759f13d1d9337e4efe47edc80346201a7156f9a399be6f8ac16ead78d96e2119ac3ad01fb1de906a76d9f90bab59f15597b8aebbea709a058fcc29362f9f3ebb1b12289ad48003a141820154a),(0xd8c0d160b8d09ec07d3075c067f059803d801d30198006f0000,0x93ae127808b733f968ba054485149e27a2507840d0c68a248976bef9dc3cb4934e2d5ee33f50d39484c65f8c95b87f65073f7d1602c09edef615c0598c42249378e05c65e0c2ebd503f222c615c331908edd206a5d265e4bcf5a48629114c88ef09c5d4963e56a2640e9e561837401e22840924aec88befe5c1247f35cd01d54bd9f2784135555bea4f87385963669fdb6339a6dccb6211021eea7fbe5afc36ab7393f3ef34d3b048e14853173a13470002ac610200c2546adc40a2bc20048da8be7d3488537ec5ed6ba119cd647b5d1cc62344f45e7896abe1f680f807f308051c6467539bc642913ef9fadfcfd5aeaa34b431c64d875b8cc448518e0ab8bf51c7d47a9c722c58e9a64ec189e99f4cc8b44e28878042835d3138fb96f2ce276979065125678afcbc691cb0eeebfa88007528100413caa5633608ff9f51e48a7d91acf6748daf0f7ebbc1f51cc2d418b72a027d9db98435b9963ce4cfa970572c177620ff4e8f9eef1aa26a74fd4ffa400550c32200ba5498ffa0f24f02a5f59ee39d9fb1e23fe089b92a221cabc78d6423b9de6832d86c143070d3b9d2a02d8c1106a4e1efd13d084224e8bfe8178804a7)])
def ct (id:Nat):Q9:=if id < 108 then uA (cd id) else (2,0,[2,1],[])
lemma cb0:(List.range 64).all (fun d=>let c:=uA (cd (0+d));decide (c.1<=12)&&us c.1 c.2.1 c.2.2.1 c.2.2.2)=H:=by decide +kernel
lemma cb64:(List.range 44).all (fun d=>let c:=uA (cd (64+d));decide (c.1<=12)&&us c.1 c.2.1 c.2.2.1 c.2.2.2)=H:=by decide +kernel
lemma cv:∀ id, uj (ct id):=by
 intro id; unfold ct; by_cases hlt:id < 108
 . simp only[hlt,ite_true];by_cases h0:id < 64;. exact ux cb0 (by omega) h0
   exact ux cb64 (by omega) hlt
 . simp only[hlt,ite_false];exact cK
def k0:=FreeInv.kAll
lemma h0:K k0:=ue FreeInv.hAll
namespace G1
def bk:Qf:=⟨2046,15,(C 2046 (B k0) 87 0xb6aa1a2288aa0fb606185ce1f1a59f19c94a05e0d6600543ea4ce0535826487889ac4e6a9b3892c50b1bfe65de1b45261edd75679482973c64864ba678b9912351f4acb57f6cb0d5398a9561babce0f1d488173be81fb0aa7a4fa4dc827ce6ff77b86d938d95cef54c20d25bf3df347075b8ee72b6c77c8f39695fe659760912d929d5f682b40f3a26d374839239fd2621246821e4c3c5aaaec0e15d533dbed418b5b8fcb414d75f2b3add8fa88c898e3e77c569f3a393f7e2be1911a9a7632f07aaad0abbd914a3c83dbaf73bbe),D [0,0xa9865431,0xa594837261,0x95a4637281],(fun| 11=>(2,4,7,T #[0x3c06608c0a0013ff8462441480420,0x180730c2170190416ffc584441480420])| 12=>(13,3,7,E (0x7ba7516d862d59e50e4743982f825a1d414e09f000,0x22885e2b0a82017ffea089c6a414d048ac514a04e858ffff5044e3420fa417f657a092284d19098252901e237fea868c484137a284691232ced05818083eff550d105082242b82a4e21181d040b0343fff548d105082242be45433300b04381d04ce91ffd4c3441420a7b0dabae0480e100140ad0cc833e0f3300b505819bffd483441420a7b0dabaece9388cd044da1a0d0fffd083441420a649d7e2c010cf310bc06c102c3fff1105481082ab1382aca22704124048dffe482480420aac4e48c20c14060021e37ff918920108394104045b7c561a03e080e034090307ffe240a402104b2feb78a8590a0530501813040fffc441480420))| 13=>(36,2,7,V (tP #[(0x18c716c0151313ae1256108f0e9d0c140af50a2808e207b6061503c102b2013d0000,0x7afc97f745c3a7da1d9978712418f68e1934ccef83c72a2b89e89f65f6b0137a9fb4c1b45cd56f11270b10526aa7e3f170aaf4338207a44160781810dfff5044208a6f847d501b9c408a526ad4b215cde13c4b8f27ef4e6fdd17cac337e4209023f3c204251f47e2e130cc2f04381dc0d225fffa6221050979e9b4b13d1a66904534dc609d8e4eb9280c15ecfd73b3506596dee8a1112507a254ee0a063522ffd50d0829cfa7881cd68073de24726364238922316e85ea4e8a64a158842c261a1e66077821ac0c080037ffd48d0825a47186108112038ec3f68c7e2b8e19dce9dfd65b7ea93af3f9084bb33304ef0d6d9bf805c8a3a1445c551185c665e821040d2867ffa71a105a8680eafa6d3baf25bb39c589deecaddcaebfeb950d98c3a5420dca82a8db0e2ae111a219f4f93c21f250cc422e13858857319c10e06f034e9bffe986841217210619130b47baf26d3b127c80b6f7e31f95fb0c8d5a3dcfb75405c93990078905b764284a1ad93622857b25297dcfc9117591f9e102128dc332219a60270b0a8304c9d03cbf040e818811fff483420c8723780b6b02c8abd8476decc4712a6084084a1a8304d2819c14be069d0615ffe1068410e0009720a52afa87d2a86a211f5b6602682818109fff502420bb9e08582552f03a9267f87f7e685bec3f74c0d7a87d2a8693f1f8b81c2a910620a060f2fffd209082b1fe624415c39954dc7daa39b9fe35f344e24ee5552119880562e9d4140c400f2bffd189082def6e78bc6cbb77678f7f6ff0fb32f4cab849896e7565f008a00acbb89130cb0177b38200fd88469980009705031a8fffaa428416f428d82362acd465b1c79e601538fecc5c6649619ef1bd3f2c1a9a07bb3239d4b768c3f767def7760b4eb1210f4dc40a50afe4adc7d878e2e2421064890c100ae0922048193ffa902841638a27a7fe43179c337cd5307d27852da76ddf88b82c1415cc208090323ff51050820edf4d5ebf45bfd3e8e3dcb6b5515f80dadd5b3baa92e59ee80d8294683239c908401980b81304031a8fffca40841b693b1c259fade7af997c23c2d6be878c471464d288efff341c421085cbf0491018d47ffe480420),(0x1a44185b16c914ad1372122d10d30f9e0ebc0d180b5a0946081205e2043601fb0000,0x96c48014012e873e10216cebefcef1b198865a15500888571ee7ec74c75fe9a90f1a11ec293ff3e1620a4d50caf53e015b6bd23820b40e2e5fffa822907f47ac7bdae18bfa29ed7606665d8938331a7954f02412814758d634e377e784084a191f2613a4ad7e0a07174895ffe988a41fb1aa8f70a792e5dfc33f2b140d5709691c0b1ceef6718985f9760a38b67f1e6e4d765049d0f446807138fcfa36ea4b0f0cd219800ad86a9d0b60a06208b9dffea06a41f24ca077e55857f48a36b91c2a674a201ef7949d5e0fc02c05250a0742081a0a2e9423ffd38d482d79cd53092ebdd04a1e67729affe2c40d8a2774dd1af50fa550ce602daf0220a07175b13ffea04a4109fbbfdbf57d33b7d06de8934119bede48693c69bbb52ef3b41129223e01cc4d893821ac0c1857ffa92280576f676480b5ca1b360db1b0818cea99a5433a2992804911013e626c3bc10d606002fffd48d40235548158128704d1e50fa5524242209f0de6105031a83cafff522500a1332843a094f7733a24cf89cd519cc22c4baea9ccc98fbc1438cf17209a294d25b911f51448a1b0bcc0c9053581a50afff4e34809691b2480053785f06c6d36296e347e40d3facf81221804508dd497ce7769d2b524dfaa37d2ac363e470203c8b11414d606b62fffd409203d5706da785714c1d3568c23a2fb4ed7250652c91600b269fd216ccbfada3dc004d9a3fcdf68d98fd3573a0113d4ea050cc890c9d86cd449110023d050337ffd1892030cd156c68007c7fa4ebb5978aaa2f259bc6a04842f384a464327e0782089141a3527ffd205203b8b2e5078f2a686954c2900822de1b14612df6c4748ec58e9180523745b1f89111e20a5ddc43b160bc21cb1fc2528e8fde8a440c90e44860da466b1d0623e068237ffd209182bd50449f2314afd588a009a986d778a027e62c723704546d35a3ee551851a835701e8113d4ea4391441048f0ec0c402427ffd1891833b5336b950855c463b8cb11fd06466362650bb927fa9b61651fe0b1af12d4b4c505c8a00fbfda61bc25a763982e0838a19914193135d7908824006274470f81c081c87ffa41a20590f574a21d4dbe278dff16a9d82655a928d5cef3379ca60c30e3ca2b21c473e35ae95849576efe93b9550ac893090882517f151aae41682818f0efff507420),(0xbab08ed058102050000,0x5c340a423cb20d6a82fc5159200dde47a516d14f849dcb44bdfe5a01f245f1105f3862a7cde562974f7583254ddc80b8fb9aa0d95bf6988de1aca79c0ffaa95260cc9a918a0056d340424a2f1d45e0b06bda623ffea08a4710875a98a50dff216d19cfb12cd7ee0017bdc21b420a435f7392b96238678eccf1cd504cd969677fc7477efe315141f95b9616a18e6fcc1846b34127118f89e29a61684b5eb86ca3cbc6cec96c3c614b46fd212a4f270cc9a3d4913228019b2d0109748c2e3b82c1a5ffea48a0757f120db6353686f39f2331f6b0de5d1e548f32baac255bc674060c596b93e01b08901f726614c529c99636451b5961814cd2029765e216f2c4f6b1ef433898945145b4ade1c6fc78ee00bb03869fed34df680293410338c0f6224c8a0056caf5a05881124bc751782c1a9ffea5090745f7f3f4e89b3632fbe4b330a96a45f3a942703680867218267d20098936952f310435b4bc7ce75c8810da908dead8c35a537043d266bc2414c18748fe7483083)]))| 14=>(12,1,7,V (fun _=>(0x31ae2bfe24e91e651c4318e8132910790c9008ed04ed02440000,0x3395d03ff5e0283eda166a48df43bee297e0986d1ef1160f046ccb19405969094b1aa8466499f7f750acc34d993db49101319f4ec9ee06531f12e3beee0ecf273b6a977d8ddc08903dddf96a1f783a55d1d2e4a7d5776aa6d82e170b635e419c8e3fcdfb4566bdf826b388a80d4b4d4340683a75177406f7e2fe66ea379985ada4c74810d7648c9b8d18873437b42b870e564bba26591288845658dcbc1eeeee0814a46ad3517a1685e85880a0b8e9a4141a613ffd48fe9f1fc299313cd0b384d8549f202913c339f1aacae1b03c5c92b6f78aa56ba3ee47d938da22796c22683c86589df0e967f19144b42acdf21f28607d7b3400cc34a0cc92c9321cfb189ea0e169d3775121a68c0ff1cc9d6780d1837f87e5d82a9b7b6ffcf6caa77f1ead6b71762fff6ea408a1e8f195774681d035f843b1f4dce6710a554df216dd361fdc9ab38eaae2fd94157d617ce7548c035c8c4515904249b35eea13bd55e75375c8f2f4dce9724d5d222399bf534c899ab13e1a27d3e7a8aef2b02e06c9c2a14a0e827e1e8f2d7e3343a06abf45c405260d8742e0e089ffea077d25e6376bf8bfc62c1a5b333794f97da545ae167a1c3da4b0a3bb12fa990558655248643a8b24367d94441021140398f748e6b297e220512b6ec6a109316ff828341496d57e76c9fdc7636d7585d2a40876c7e303c28926f2d270f60f54f9f2a3f723eead9ddefadb8d6eb69266824aba8fc98e1b8d1155ef6c84a56257d968c689887f864ec0d81dc5faec64d46a209249d9ce85f3c8334f4d1983f748ed707651996499d155f3c35478fa56178d8b7c58af8671ec7ba1db09be1d7eae2fa6f3b3042c5c6044504abc760a0caffe9079b45f38d55cb5afd135273ab043eac0e3a3f73f56e5ac2a4117cdb2e673cc9835533752af5a499bfedbee62d677a6ed07fdfe47e1042b43d5b94c82af8314121d1fff841da5d16bc6fb9a43e46a72a59a44b3843c2ba7483504564c6711174cad0072605ff1223224c2f3162af68addf04e3f80a295cdec347a476969ab9c87e6be62a220411a4d9bafe25a31e4f040d6830da53d3151ff2d03372486b311f0b989d47ee725e69301f0506163fff501e46a8feb19e064aeccdd6f6ccf9db52561731a06296c7987ba8e1785ccde2d0589a1d3535c384cb68f1a20577460abcb64cabb713d4c8f329ca6dffccfbb610a3cc5153de305ea4785dace5c2839857bc44c463f166fe3459545d894d4f63305ce9ccbf236f77d21aac81114603e132c258f7a3529b3baa478fc234747793d69ef53d2eb83cd582f39ed0327f56eb50e34fd903a023b31359d2614f66a3e37852a0dea4f9e9485928f18dd9a44050d02c7608be0c8ffe8c3084d0087e3ba0b65c0925b36c70532a10ebc3bb078d6ce26e9d3bfe6f0182b340cf0ba1a8b8ea9fe587551fc10ecd31149b221d182ce944dab0fab5bbdd66bc8f2f58861ea86d0de9b183cb997662be080c5c5ffea418f3a69c4493bd9807499c2ac9e548be85b91fff2f22fb38a367189148ffd866064458be5f83a64c27fd0e41b48d04099845af2277e9afff3793cf9f2312550b8cd9a2c20c13801fd6019b7d88257e87adf9c3669a9e4e3c486abccee34f367f28c0ad0de306cd2b474261aeaef8a4a26c2e203e173091046a0657ff500a8703bd452314b117555d36cf5d8bd7c5abaae8143ccbe9fd080af275cf14dd3185f6d24c2066b4e62a96d8b29d44a4c9fbe8a511ae4afdb12227953ed2dd6529e71fb8a5282c1aa54d0749a44c84328e3172bba22a80990b3f4be84073ebd58167ef1b630f3afa9b47c5c342c4608d40c8ffe9016996460d7ac8abf3fb51db129ef9588e74c1087ea3e5c721f50f72b3fc1540cef9f5fea73fedc35a3f38578b7099a15cec7016eeba8d260ed47755578e708fac90056b2e4973610174266962dbfcd8be0987a04e3af3aa4533c103e2f09c17d0c0da165b2528ac10e212299bf8caa77ec49f2d4c45c40502c7608d40c8ffe8c1724a1c260a6524a27b8d5bbe3d2b3fddd22df45e8d5c5926349153fec2ab4396414b0511f0180285b4870c16641248755804580bb196aa4a8477a7f29f17e2d06e9f7ce540924da6a3a2082162f301e060457ff440e3c5239f4aa9440c8d42f0a5ee927c123cf9a1821ed985c5046d9ca66b3e8594fea69fbd716672f341e3b96cb1dc4809c730476af694a5b4eb249c203a2a2e1730325f040657ff420)))| 15=>(1,0,7,T #[0x82d84fffc09540e407fbc76412fa1d48bea274fdf047df20383b15830100546f11fe9795f2968433e825430bc10313ff])|_=>Z0),(fun| 12=>(3,4,7,T #[0x4604a19792eb05a0d1682c23bbf1484e64c5801,0x397b61967208cdb4ba71191522d0c81ed0646ec1031233fd16a441420803,0x8c19a133b05a0d8b8321fbbf1494e64c5803])| 13=>(11,3,7,E (0xba8b1aa4196c7f87445783c22e12010bb000,0xa494c010ca700ae06c102c3fff51060290822060f60bd8e745615783a1a900e53445e82098502f7fe2929cd0079418d9ac289594851d4d0c18073c12688b83a2a11bff1494c5803c6bdf21f4d2dfe4d36c0eb21985954153a54752e344c3eae36ad6bc50e8f05491a4a675e135068a11bbf5464c58039be5755b77b9d2972660ef5f41b04130ffbf4e64c5803d5dabf02229f216b7127af9201a12d8aea0be346141887b379238c6a48b2beee9b1d9d29b534e500e051458328a23bc150618933ff16a420803f19fbcd9bd749e084778a3406e1dd3af4be58ac8196ea1869b4a6ff66c37faaabca4d44c36308d9144ae3a4b305418785fff510508200fec9ad25c9176a4d022e5610fa9f0c10be09170e054237fe29298b00307e68cab5ac1b55d50c2a20f82ce0a9d4da830e02d2b7fe29098b003b43c1f1bc34ee8e2aa4f548a3c0ae0896e2261f7af45314a9027734c2e83608b2944afdfa73262c00c40c1ec180b44851435234c269412062811bff1494e6800))| 14=>(13,2,7,V (fun _=>(0x20c91f641c611a6f18101655140810370c97098e071304ad02620000,0x1fa2cc30714c04047d8cd9b59a3d5a72f2d43e4c6349e58d1913567a88bc63a00012ce02b82818d47fff80a420a2ecd771429fcf4e8951933a3c6a580fe14759c4d47c74f5769f7c91910c67128a4cb757ab2596bf4e60c4593b993ab8b972521c339bc28a103dd2497c62d2c7f39cc73b442e3f3734b9b2fc89aab1bc27ae7995414c187704340b8d7fe2930072a384a424551ee82f4fda8c15fae6b020aad5071fb9e633811e0b15782e79637e1316cd312efeb73fb14a273aba78688220304099afc1a083a45ffaa3c01f86744e254f639ad29e28ccc6c04bc0dbd4e9ebf635ce1179d33e31725f7983de766ec0048a3c2f67b4cce3c02c984b202a29872bfbc9e0ed590f80e60d00c4cc12475e98c18509bff5468038a54d5ea139c7c0af3ca451aba612cf46ec5ae7439ca2ce67de6b64330d5457f28f6d59955845c264ba18301d48ebf06821c97ffe9cd0071837a0e9175dca00ea2c7e6d37aae860b19d34c7be6a9e7a41a6dad0b8c3b0f8c55c227c027e3e203082668e64ae8e70bab99e5b4efa9f434d4325da439492c35f8241874afff4c5803a23256b7a87edbe53f8babd72a740a9eeb954c022a02c1fba3cdbe937b18fb65d76297fc48ccf8c792c71c78c656fca1f2ca30392aa94c14b7ff44d2df7177fbc52c3cc54db279f9ecd6dba45793857c132487735f7cf9d8cffc25a01bf8d5df68c79b8d8ac0b828f0fc61208b452d23b835786d0467ffa20c01ec5fe671df80fe8071af98e881633ea38b8d41e4fcb1eb3fa190cc7eb287d6e2eee2611251b96ecfe0eb1c181c71d028ca78beeb7254dc7e737e250a8bc191a69a1c101c74694f15274ff3404d45913b1f05dc113dfee20d1dd6a7dee2c8680cc3f184845132974aa2e3aafc10010677ffa10401c256cfb1455215c388060164e2269eec9463f0a7a0d7418083e39d6ca26dc850fb00005696ec8b8e0029ed615af7e1e9a60c3d658b273a77054df2f02b62b42fde69b25869a0cf0cf012060491b151659308b9ac0f70434cc60c5e361effc52200719111caa0752886184b038a6b1d8c9157749387fd5e146424b4284f5cc8dd4f8cf6b4cfb7b6aa3e397d5fdc600f8ce7de7c24bb35718580970e4e1e002554948273485a49609dc120c7057ffa62c00f54e80b2e0ac6953eeeaa4dbaaa13d5997e381926e3b1f505b55ce145f7fe30c1bfc864f318ee4c731beba095b7c57f5b23c5ae992556647dd84d0f35a4ce777ccaacc13304031a0b7fe293001f4fd10802d70b7d031f7719be15df0b587fab783f9c99dc0cf7b68a924da773eb301ad5a77694f1fc6c839245879551455976a41bc03ca1eb516d38ba6150b848a7505032bffd39a0026e70cbdda81b77297912b6201948414ee9ca5e209642c85c070666d705520ea7dab1a04d4d135b80ed33bd3d225e35d631ada301f0eae429a2f7e944827d688b57a2970164140cafff441800)))| 15=>(3,1,7,T #[0x55baf88551a3f5de71746272669f6747062706905ba4c83443e2fe4f8d8b27f267d88100c0c21664470cd519146070fd3abdf040b069d664b145ac06b25c20a3d28032ef49c251537ac05db63f099bda155eb2c9fdb5fc8b28d5dbc4aba04e3730450b5538a790793be9fee1c1f16b2ba56253c2f315f04062fff800,0x241949a43755898eddc79cef3acf8433e329fbf1757d30c333d74966fce1ecb5bfcb79cf82be78fc353f17b490acc7932df6977fa6c4c291a71e04cd995a9cba4df04795c38be3a0c7aa8e6a7e72e97fee2ff2a60742fcfb90cf6fafe47b240fb7b071cdf0f4420374c172dfa6222e540c6d151a4d32ea756823b1ade8883a31e9c8ad3668173105065e37ff801,0x1091491653638b580ada0be7c326516519d033fa4542b657581e65d288ae84d8fd5c150a3bce541bdf1fb4baa999051d2622ef5d818e9c24a1c4399a29e66b9775c7a67d3cabbc6b4435f10bdf0dcf44555022627de51ad30ef9c22faad6277dc98688ff00e329bdf67da411241f961a93f76a92e98bc0ef3a1371af204eaf894252d82325b92352e610a493d787109a9fc9e121d8a1807cdd6e5376968fb2eb82ba14271f6ebc501935cbaa66b7fbc4b3125ac1138d0e88b1ade8883a31e9c8ad3628315f05063a37ff803])|_=>Z0),(fun| 12=>S 1 3 2 2 2 0 22578| 13=>S 6 29 4 2 5 0x6560440 0x4d891ec13160001901681db9132a468a280c9a200ac20001e00| 14=>S 16 89 6 2 7 0x180022000187101c00d0010000 0x1db250001f19e691a051f1105a929e00085b41e03000012081d5e3548d045e2610a38719e0d840000000000003600aa814005b220000053e8c2414df000000f906645001118741000d80022c2a00a280248120042c011800002475000002190100180001d| 15=>S 10 46 4 2 6 0xec28001205610e 0x35000000213912f4226a06e310d8cd85c29a155120062769e14caa203294c800047ac5dbb607cec00|_=>N0),(fun| 13=>S 1 7 2 2 3 0 0x80588003| 14=>S 3 16 4 2 4 1280 0x20018901201042828300011e28b| 15=>S 4 18 4 2 5 263172 0x21010002a0698022480a0e487015650b|_=>N0),(fun| 13=>S 2 10 4 2 4 0 0x3b800188027b72e295| 14=>S 2 10 4 2 4 16 0x394d8c5dc8000928e8| 15=>S 3 14 2 2 4 1536 0x190016fd0647ecc05|_=>N0)⟩
def fms:=fO (uf bk)
lemma gm:uo bk (B k0)=H:=by decide +kernel
lemma sT:ua fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]=H:=by decide +kernel
lemma aT:∀ k ≤ 15,ul fms ct bk k:=fun k hk=>uc sT k (by simp;omega)
lemma sF:ub fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,14,15]=H:=by decide +kernel
lemma f0:uL fms ct bk 13 0 18=H:=by decide +kernel
lemma f1:uL fms ct bk 13 18 18=H:=by decide +kernel
lemma aF:∀ k ≤ 15,um fms ct bk k:=by
 intro k hk;by_cases h13:k=13;. exact h13▸uN (u9 f0 f1) rfl
 exact ud sF k (by simp;omega)
end G1
def k1:=(2046,16)::k0
lemma h1:K k1:=uJ 0x12341678960 cv h0 G1.gm G1.aT G1.aF (by decide +kernel)
def k2:=P k1 11 0x29db439fdf040c94ada9e1dbef44086a76d2f0f4cff761020304050b6768798a9af9f20a9c35ba7bf105dae0fbf8408262ed2d7150fdf6105032204276a6b89896aef70820193b5c54377788104c54e1a5ede9e37ec40872f7497f6ffd
lemma h2:K k2:=p h1 (by decide +kernel)
def g0:Qf:=⟨2043,14,(C 2043 (B k2) 40 0x9ad173a60c51279308cb36290e7cf873017f6c73f701bceeb615eb8c055ec5341bf0826d62f6660a0a369eb331dc9d32a45fc6172399e7e9289900a84a85ee52623663739e8eaf378646f28333a70dbfb2df64eee721965df66253238585),D [0,0x98a654,0xa89631,0xa9865431],(fun| 10=>(1,4,6,T #[0xc06017c430f02204401fc5f527507525505])| 11=>(3,3,6,T #[0xd994ba56258608038fff6462461460,0xc1a06e24098640408fedf507525505,0x302e3a0481200bddf527525505])| 12=>(8,2,6,E (0x4833ed35f2d22541be128092000,0x6f8a7ad339121c162309000430693ffea0ea4b74cc133ee0ab3338887043e0247ffa93a82ed9bdc14af6850d40924b8e1e1bf7d495417e91fa8a9f120d74724c046fff5044e3df14f5a670859991b14528b8f5627ffd2091877c53d699d56571365323d0e2c1c9fff462461fa48128671a9949188b8292179627ffd20d106777155d7d554504f4a2444413c8ffe461460))| 13=>(10,1,6,V (fun _=>(0x139311700f970dd10ab70685057c0465031d02480000,0x782df2011eabfda0e3ef089c167a80a4c131b9f63387ecdfb70e8d06e356aa540d5c711d190109815a197b3ab825afa7fc2d995d5f818f3471425a902008a1a70c47ff525ce4162158aa4fc7da8a545568c4a2fb4530f0f16bfa5c5edc3da4fbd38fc98f21ecf26c7380831710fb1a790b218a4f05484e5d988049022bffa82fa57ce3cdd62dd9f252afb3388eb15ebd9bdacac82ef8879c99c00760a9eaac97d41d5c2fcbdbfa16fe99ae55e22a9599602144064c9ffe9c722ce93f2549fd95522e39d2230dea0dd4a8d5e82eed063c8476f9614656c0102eda454e96bdaececcd8d797f481a946186cb71c71e1d01c22ba54b7b0e35086224cc785e3e1077f2e0a5b1cadb3c5320ef80fd3655e2587954d0e24ba5088092fffa61cdb3f390cf18744a5b77dded042fd02e57c9fa73920f37e1ae863614a2d7604557bf1d475691354db58708a0f2e859f8d27afd387d9e39de6994dcfc00484bcbfebd9428344c857c0270f1a569bda67f3e96b05ed8e10735aec0b95f75076dbf115319d2d0dca1061c0fbfdb9575d7339b3bc2878071dc2587a4274a5a5b2748c38510dffe9078234d3cecab9eb4b668e8354a5422b47018da294b0fb25e1143a462134867ff083edbf050ebf1e7d309de104470aab6f606cd230d1d3c71425caa389485c3123c9ffe983425e59cf931f16644ca07df94e7c601fe1a85adf72d34946e127e11a8e284ad9274a1c4163c8ffe8c34d3b01ac3692e7992371ec7033e61da255194b22c9022c47ff441dc8ec6616b0429b38b174c9d8f62399df4e48b9aa6ef1521fd8d4c9807948eb8d609a4bfd3bb01fffa7de990e3ae8ac099d88daa989aacbdfa38d63cf06a2349cba4461c2123ffe460)))| 14=>(1,0,6,T #[0xe19cc4393d9695d6ef1de28138c6b0b566ed722ab9876edb7d5346ccfa3859abb59440f477b952c995be4c8d463daef9f8381465a06522c30841bff])|_=>Z0),(fun| 13=>(3,2,6,T #[0x4057f2bfd49c445ba83472ce57cc29a707cfd723382930c34c74d05b2c9764630f1008749bff144805,0x1f6d70ad92b847bdeed9b793bb26f946ff627f30149781f71e417f2bddf45a5e7b2d9abc66a4927d62c1a5baa02c1e4c32f90cdb09335efb5644a1ca78e084b3f472a672d34b2f0f08645bfe540806,0x14d818714f699a2f258a10acc5ba99c0e4e058285f48530844244c9bff143806])| 14=>(4,1,6,T #[0x41f1fba9dc113a961e766b1f1bd4e0ced3846cc6de87adbe0d36805fb4e8ac460c905216e22cc066f67cbae6d97c5ebfeae88ac5186c11d9a42e1c40437ff801,0xff85eb87e788645787bacd91f00a56693505301c5b6a9a353fc714b68d5082c8b8991c1f6ba2454bf6cb1c38a4e7c9150f5e734f71b4d99af80741bd28b5e6f200923b038507501bf5f2e54b5d0452e25a322bd65f5b5579aac837ea5d03b57428a01b698d92b50cd459286566e530bbaeeda764c14773e66e9c0422b1461b046461d9974a1442647ff803,0x15a3735ee8d76df83a992479e8bcbd49be6ecc837e5292190b52f24e869f38308ff83d8aae7d35772d9b5f6d1cca0563890ea92f34906690b1a578c9f57445628c3608d24bb3481434e3fff805,0x1319622821e817fcae4f7e1ba25e099c8dae7d647964d6401d0ef369b5c7fda8759e657d5d0bc96205e21c1af0348dc24de75b96e6664e76d4f64f31be5eadee36ce4d5317cac98ca52e1c2122fff806])|_=>Z0),(fun| 11=>S 1 1 1 2 1 0 9| 12=>S 2 7 2 2 3 16 637749090| 13=>S 3 12 4 2 4 1546 0x9140060f22b6686090c1| 14=>S 6 36 4 2 6 4362104833 0x144188000007313a00aa844fc1908140063003263000004a001c0570000000|_=>N0),(fun| 14=>S 1 8 2 2 3 0 0x3826088240|_=>N0),(fun| 14=>S 3 9 3 2 4 19 0x2b85b0e44424ca|_=>N0)⟩
def k3:=(2043,15)::k2
lemma h3:K k3:=u5 (cores:=ct) (g:=g0) 0x13301678067 cv h2 (by decide +kernel)
def k4:=P k3 7 0x3050c1193a4ad82a1821a0dfdb9824609cd0a96c0c5010d4efebc82a70d6e9ef6602181a39475b17efd3038c149d2295abf6f88104c54e1a5ede9e37f840872f7497fcff7
lemma h4:K k4:=p h3 (by decide +kernel)
namespace G2
def bk:Qf:=⟨3839,17,(C 3839 (B k4) 86 0x53b7d600e2d4525032278a3631131ad5b4b02bf61f284fb1766bf1bc1941c24c1de2896b6ef4ee33f8e8c6744c9efaf4f635ba7342ce0e79ee1d9993c64f63f2f5d6272cee6b11a1d9471cdf22fdcc200c33fd5311aa68cf97612af97968de6d80c03a73e223d60bef05deaf9fcff4a5e401b4b278fdfb0a9cc7b9aa3410df84aa4234737940a438d2a9a6a11ec13aea55d75a5c8a54be378a7781edac17abbd4dab06f8d0de1a1c18ec361bdfbb2f4bd8d763791746824034937ac26356c2b9c37a9fa64e38f62a244f51a7d),D [0,0xa9b74351,0xba974320,0xb9a75120,9912880,0x97a9b720425130,0xba3240,0x97b9a720325140],(fun| 12=>(1,5,7,T #[0xe015012013e0fe0be050007fd5d5285475254e14a1])| 13=>(6,4,7,E (0x5164403c22ea1e00bb000,0x31404824fb1e63b47588c9cf07e0bc0e9be346fd7f5495074e5521fc1f82f02018058bf5fd4a151d495386e90d9178e810ccc04831e0c0bf81f05e260295fdf552149d385286ecfbb04a9ffd15b55440b015019e43c0f89f07e080940a0285cfdd1ac5254e14a199e4e8e313b712704e09391411c400790e01a033c1f82017017c4c0a43feeaa4292a70a50c2ae5815e2504782f07e0402b8700c4ff5d5475254e14a1))| 14=>(34,3,7,V (tP #[(0x134c1271117210180f270e4e0cea0bf20b1909f108c0072f058f03cc026b01720000,0xa668c8b2ab390866158180a705c0f13c182a1a0145cffe316a4c9c3edde2ceead33e9f59c84330ac0c0579082b81e2783e0812050c9ffc62d49538636294c487055b2553edaf6b8df72a6124a40b644b20180ca6c270871a80383e0782e260a4bfff5485254e1e045254a3ba04c6d2affb82a02e580c015c1f02c38621095fff8a4292a70f8eb007f87bcf8d51142382c6b89e0c05e052e018afdfd51d495386412ddf74260bc9dc5b6d327e5f7091148bd0809a306669b0840ce2782c680f81783e05878293fffd525415386dec482abc5f621cb51f97dc05e40ab8be0ae2783e052e018afffc525415387d13c8bc0893e20a8ca31c1e35c4f03c100a9684257efea4ea0a9c31de39c74f18f2d25ea428047093a571563485414ce545c1f05c0f1291c006fffea90a4e983b0d36603890793e08d63e8b23874b22bc6a0a8aa9ca890ae0789e0f82401233bfff5495074c1b068475a216b0d4419dc127fa9e7133e309381094c510ee2054a1454408c8e361381e1340bc1f058d703c4a9fffaa4293a50ede24cc5f54ef94d8be55bccb4fb0a88ff9b709d591c38118804a12215055389182dc4f058d817c0f0702b0f8d25fffaa4a83a50de751521258ec17c7f358b19fa452ef2f8ece56df20345688480f26940567222c400805199c6f89e0818e0f81829870320547ffd5494e14a1a903f391bc4c71c1c4e48aa54d0e1700f2b23116200c028ccb3887637c4f05c0c15c181702a1ffea94270a50e1d7476b3f9e0923c1cfd204040859981018e2783e0782014afdf549d38528687f107999c6e3231cf9ea40990176b5161824c8c6af17a9d048140631001789e0f82e040a0180b33fdd5254e14a1),(0x163314dd12d410eb0ea70d890c3f0a160919081507620640050b03a5025001450000,0x73398670827f59a1ef6e62cb6464efa49f614a4a32cbd14b5b25f8f3620f35c0f122007e3cffeb1629024f831668f0095e6ead3ec7bf09fe09902b01f9bd374b67e620fdb54f4a3c2000ae8ae923666b00ce9bd911dd0a39b0619ce438203389e0c2661e4533d7f548527127b40f08abda7e5e1c1955222dacd1b68b8d0f823c978972e95eeee671f0428ce882689e6ba8678e645cd8884545519713c170212946619d7ffac50b4a83de6c0737255ede5d2523108cccc59dd4e34c1e1a42e787394a59b3d7b8ed17ef25ac813f14b0359bf03c9f3aee88c5f87125c820088382083e0f703c4f07c104a12193ff8c5aa4a83c8268e77743418134955949157ee60d2021537c4f05cd703c1b0f1800c67ffea92acca0f0ece6f3e2f1c9b4cd1a36023100694f0df1e43bf63c5b2c97e220f37cd703c48801f8f3ffac58a4883f25de1ee837df873bcd8e52a3bd97b3ad2bf18e783a9af3b3a2aff6285efd9e90def136c5e39c192dcfbbf1282665c42be69916643ee439be0789e0c0b8eccf9fd52541c41e1960f4fd42424e54a521e172144321ef35c1e21c0f131d82e77ffea90a4e9cdd3b762bbe034ad91c3878559388eb230e019c4f07887031d80c6fffea92a0e9cd9be1ab768d4b7e0789e0d3b0a00602c8fefd49d49939acd492409476062c278554244451d8769c47b9be27820331ae078361d003fdff5495075219e2fd0d1908916045b0f33cbc0dd47eea87204623c80178d702857121d16a4f997ffac2883a90da17d9b24680dca8ecde6539529484e9cc731502c5c13e8f322ce04d4de3491f03c1f05c4c14afffea909caa4360d090f872720502b221b3faa6aa393bcca702a90095392aa380de1ea6db682b816d52e3bfff1484e5521f3e2d989fd9e7d284b889398d13ece7060b4154df13c17039690a7fefea0e9caa43857df361b0136b4f07610b7f7150a0148651d87421a640fe0b89c6b83e05870320543f7f5485274e1),(0x29801150000,0xea02d57348a55f714637ab0079dc20e8a54d020fb38c148eb4fe339aea19983cd70302f13c11465a85055ffeb142d0a4ff70e6653a31c2ecb4a5bde215dc48e8b9f358441e6f9ae0f820a4281e7ff18b548527)]))| 15=>(66,2,7,V (tP #[(0x202d1e671d0d1b511978171e1533141312a111070e680bbc0900067003d901e20000,0x197529394f8cfa521cdd1d23e3a9ccd1f334f422ccbcbef2bf95e0ba40faace062100afb66f48fccd89026df6120e6f032c16a1c6fff8a4a60e8c860e18966cdcc5646b91edf4c6e3b132949d5dee3d645654844321c8d0e14581c4e0f040a2effeace983182ee93db3e3adc40f245705ac9a4c65f50f1a180684ff7e54f72646f16e10431ecafdb6148a72340a962880b89c160f020033ffea4e9837b04994e2689e2b3a90f9fe719d6733de2b2474a7e3c6ba66d3b555963f23c744e64b556da6405f31651cb7b088c839bc0e25772c1691fff1274c1c67ef9104a5eb7d683ed7df8a02865c015d4e4fdcefa3757d6202b17c431ac43ba88b5a977f4e2e8e676e1a3aaa87d7d56b76c3ce111a4400998d02938a2186071383c1016587fffd41d306f609329c4cc3de3c871ce925146352ea8b0a9b61350dc6907142d4ab2d0adb38d9b3d9a67b7f70aef0752c4e10e88c011acde0712b55dcb0afff883a60cc316635ea338546f8ffa501bb7f92191af7a287c7e45818c1e071382618288fdfa93260dd14aec4c65bb5811f10bf60564c168637847302c3223b5e455dbabb08b1229c5146b1382c0e0c14002fffea4a98322a5419c8e3928bf2f46e8876e7f97052303dd1b358aa3c33f19602e18f111a4400994e46a5838c162707814f828efffa72a60dc315c0353485fcbddc0eadda513c41dcdfe22eaafe2e3103945e007a6f814443aa2a9a0d2f021ab2466789729ebf1ba8f5bdbf9338e73ebfb6c22848c45391c88011451a0c46f070ac4e0b022d02a5fff5274a1d076446e1540467c5a08b5753ca75ab860eb66fc3fd346640bb24461fca4ae4a7b5413fe659c8155d20d26c39882e7577514b8f82114c52a07f9573a90bcbacb28f9d2dec3118e02a219085607122d0f95fff1274a191615526529086d898471a427a5efcb1243513a9755b09ab2f95789261a34bbee6a3d952722fcb0969e8733120df61ff5f6cfbfc614696d2d80d086a1c3ce148c45331988012349c5103a3781c4e0f050a02a3fff5074a1e9a5926208abcc19b95efdefebc983f9c5f2b0d4208b3cdfe2dea8c0c62d9355b0ac13e615a6201b8e3645051e7f77228c786df83cd275ea77e10e01a61740589c3118cc43211ac0e2614b50f95fff1074a1b872bf77a0501c6f0119e04edbec024f0e14d3c95436d0029070cc98326fccd029d6bfc20b4bcf67836de97183aa3465675d4827dbe6b01f8e7877509631532a8b57ab08d183063581c4e0f040a1bf7e2cc9432b51d65d1469c38370364767aa3a7efe65a947ebb211ce956f3686fc7eed41cdcbb2c207340d563ff8e1f824a87688a20a28de270781c10280a57ff5385286fc98a03c4243c1fe9db66049f4cadabc270900a6659da3243d86c1e95ae631f6e47cb6085291a05ae16e2c8235e6cda22cc0e270782050dffd4c14a1),(0x1d2c1c0c1a761822154b133e102e0de50c480ad6090307a9064204ac02bc01a30000,0xb9eda834bc3d8ae7d5629633d507f661639435f423c8b07383c4e0b022d0511dff526521dd1c4cde36be4c47527e14d3d9afe945dbde2ebd4802ecf41b66b3f610f246229c8e0a920a225e0f1382c0cb4147fffd399487956def7924e7a1f11067cdcbc18e4ecad2b24a6b2853f21a34c54b7788d5d251da52a2236a8b8bf9a36bb6060d4059fb59b83e9188a72383915641371ac1e081589c0cb53e8fffd3954861063ebf0281959424143168a9089779a07f39b4e982fad4da9d0f2528be76e576e7522d3a5de4599a70cd50f65b01704460e9cbaa11304c846ae7bdd86a30e763e23705391c0e85030384ce6f13828d08f07814382d0fffaa4a70ceec306b8dd1fb1d438cdfddffea9c8f0c430386fca1bd182cc3e962fdfa3b9f10628ea9cd300a81db0a6bf5f4d6c1a3f8c703b9b1d0ab2006c08b50e57ffc52538666c1b654dd8cd4a1e80341b2db454efb2616872acf2e138edef6a56ef57e57f56589e2e21596ed830e1038d7e26c2910290492f1cc2b7a3905fefad390ad6096edc0828adf29e140901231115877201415265399b0046b1382c0e0c1697ffd4a1386fb74a9ab12a21b404f668d25cf37f91ac15f034ab2dca56e184b68e4b69e5980451f4db4ba5901685e487bbfa7ed9ae4b0cd19c4513b40c443b9b1d0ab2006c0e096c2d2fffe2509c379ce40fb2d5e759837f8670a333ab252234630d1196a9959f3a2ad05de91a3cec74b22190e863071ac4e0b022d0295f7f5274e1d9674cd94b665dd5bb6f7a333adcda2c70f9ae0deaf9ccf148c45391c1605030991c6270781c102c147fffd499386c60f99f49ae95848fd446525c45c144634db4902dafe3104248a21f917fcb74539b3c523114cc64571a0a60c94901c6256b81c10290fffa83270d123b139e318e63a78b44e7582b810f434298702e0a4622998c925391c1e8b31383c082876053fffe9cc9c3a56ff4e03430b524500bfe9b61da2070b7828c19d47225396f2d202db0b231a1c2431383c0e081447dfd39938666a79bba31a9fb143cd8d16f3e5fc4075b068770a0623ef84fb048c45391c090500c000526e3589c1e0b020505a3fff5254e1e54ac8c8bff7255bed4ba42fb508d1d8c1374894bf7633c565f35e190b8124ccf3e408f8c1417a4622998ce4057224dc695e0ac0e27078202a5fff5054e18be92f49289e7f172be5390ae203be593824988c66383d8d62706450f814bfffa72a70c315e12e4279b5d2eaaacc0ce08bd35dbb6cf8bde4c7c991d675e6530248dce03b0a71452c8d1073781c4e0f04001199fff5494c1),(0x1f121bd719a2189e178c1477123b10f90f9f0e700d2c0a380826046e029001360000,0x3931551af32a069fd3a2dc6982e211cf61feb1ccc7ac9b311841a8389105b82ef92c33717149442d0522d28cf3dc7cccba384c7cdbc0a0497d552b2c9350f8bd0b2115f315efd65a7da15e002e03b08f1391c1546c83104c88e4589c160f020043c291fffaa4a73492b4b77a457357cd293ea7895cbad2686d525b0117f1ebb8596d35c3b6d492e5c7c749242535e6bf61ef05104287c7ee9cdbec31c1548a379a209262183853310e67ffc52539aaf3c1efe00385c5e55e95abd512110c86c569c1548b0389c1e081465ffd5a139bc69ccf43d19d7fad00180788c662186273704b12c62181c4e0878b5050ffff1684e692784a96a5d7ebbb6d73b9f7eb2914529c3dc573495887d381ea2d1b7e6ebb623d0b29eaa4e3f29fa55e8259110f753db2c6ec678e65609cc3bd274abd94e74607b58399f6a5aac931209007891888aa37104ca706122c4e0b0383004292fffa9427349ea40139cf26ea8994afa17870db1866440ae8f4fbf830181627bc38190557aff04065e3c95ff06c445cbc404c7c2027fcbe98c4455228de68823d88627050a5ab30dfff89427374608d02f92eddacc552b698d03c00efdce0a4622194e4707b9a8860c018961e088a053fffea4e9cd92a8dbe854a2c9d133b73ea57e174920c9185879629188a6632490e4406183cd6256b811d814ffffa83a737e11869e9cf25da3abef78b788a8be38202cc832fe88d0c8893382c0e27073b0513fbf5264e68077c13a99f9912fd8ffcf425ca59a48080deece1868443a1e0466f13828d60706870019dff5495219706bfe67fba553e413d7e451d3b6b2d50395566dc2e9c29f70e20808aeac4132f3834a51d93f04fa50a83f6fa6e4e790a5c711b9b2e75b360ff8641d11bad136ada2867b23f0f272382a0ee4072a2cdc6b0789c16065a8711a5fff547521d9af940d380083898eaf39ebe3a2261973126a4c294285f35992d8c73a79d646c92e1de6d384fc263616b5bd8165807d98e0747390cd82e358396b150e5fffc51d48705f890e17b32a70890e4dc6f255dab4bbfefbdc510f2c771b24fad3e5beb86d52afc94d31a3e63422eada025863e6f8f2a169e2656cf7f1119d639c495202151c3eb9fa064abe63fad84e59512eb8e2b79fb2d1a4531e236cdfd3675a20b43c91888ac3a39152714590cdc6b0789c16065a8fffd41d486027ab6b926488975dee16b8c0a92c123212ef1a109e5d682d89f248af3aeade818400ba111cf27568c443a39c866c171e8d62704c55a99fff107521cee213bf42f86cb1a47d0f0a2be07b7d033b1d8f610f27238a2912431382044789781c1a1c147fffd519486d7d5ffa19bb3d40746afabe2baf44b57c8090e3d846e914e2881789c1604142d0017fff526521),(0x1f281d3f1ac418d7161a151b13c5113e0de80c560a650805065d038402ad01120000,0xd96defcbc78cb5b030a3d67ad5dddd61c30d9f8ed656a33d899a7e11690cde14cb93ad74266c4b2e01560b21120e6c8190cd6071232218ecbbffab4093ef5ba171de367412f38f2e2a44fdd3d520cef5717c8e70ef6707c3fb7c2f0c9fd5a714fd073e1df7146fdc719d3ed2fe5e8ec6e7d465f4a8db68e3119a44569c23643363ecd60713439d9bfff548127a9f6c483d9180e14b9f7ae380e8372f951ee55119689539536b24bf69dafbe6c9f8b0aa04a90c4c8606c0e5b419354fdd7918e6f3545439005fff8a4093e29a3ec98456d7dfe5bac015d0d3a3161e6dae992536add0aa7f3befbd76639004b6483ce47b62b47bfaad631d2f1239b3bdad3ba72f1f12f780b4a1a740ae47b9c7fcc641a0e25c5c5fdc866f3589c1e088a3f5fd49c49fa953082e5e999c480a1833c9cb18389b2a4221c4860712431d8288bffab3093c60fb40c48912942edd2130e36c5af8bb4d5994ce0ae66a322cd14a33f25ebbb81c4828863b16f7eacc24fc9fa32b5c06b37841036be779b695ac15ec834d6f27c636236fb3ee20505168be97a6d4171be438f3f22761c97d591d5a6e793a5e88e6e3d8167859904631c91643379a1591f0389c10158667ffc5a541f908edad5ac9e89e607c8f3b878c59f7fbe784f1a991cb94250826d22e7edef8da11e7dd33bbd714056695747276bdeed3118be5ded4b8b4c2a22f0c62d04e0d6e28e8c54b643abb02ebc41b675f97cd907315e4e0662b1c8a9331c91643379ac4e0b0383439ffff5495078d1df4f693e5a3c1c875ab305a2d998b8891f920c007bb539249d636c7f6742914ca41379ac191b1335c0e080a67ffd59941e64bd1b8079d0881fa8a45ef69c9d8f1edabfd5e1cb2cda58c5f10a1b86820a53843dfc0e8a62506b78525de884482102066b3781c48006a3b2effead220f5fbb374048eb6068ac3dfbad6966480d21c79996b5ce2e2e0deed9cb48c7096219f017607841c45a89f139d2dbe03386455668f0cf20ede23348e6872991f643360bc0e266b3b37ffea9220febe8fc8b82475f26f6808c2655401c2b21e2c59e1bad9147347f857b32c57e176d84a443240fb67904639bcd4d50e2817ffe29220f236a4b20d3a0520a0cd69dbd52861e7068120ceeb68132b65c8ccd552af600a7fdf67581cf226058b8e6f7c768819d7766bdde244e351f0226e15a7a82fcf7797e15c027813ccb1902227d8e8fb7219bcd60713831d8fe7f507107abcf07bf800e1717957b1c187348443381c48d4760a1effeacc20fa9883a6e01c6fe102aceea115657cc0054c0fd776bd8b7e59974e7fb1701154d8f78797d696d20e433581c48d43e3dffd59441f3b884f9a6d8ebdfad90918bd060e3a39e1939b7d862181c4e0878c3050ffff1694e6),(0x579035d0000,0x17acd64f6a9867aefbbc650e9581c4a73275261ae5588b29c49ec5ac0404aca8d4c4b44945c8b5d3c8746adb33c61d315ccceed00df78e040a00c4e096a281fffe2d0a4fe547169231df9001513efa1e706c2c7514bbeff38f9af79dc01bb627c55d6266c350b5046c1a1aef60d0f300534624bf46c1994e1939be084b0b014393d993cec0b2e30358377023db14df3dc28c4f271a3b6e148a06639158a9391991643379ac1627078143a3fff548527)]))| 16=>(9,1,7,E (0xe19b6dac98547de6f94e62791b5000,0x10752d06dd4d5043512520e671b8b6568cd11e8d23af9ced9225be218b239232a4f5ef5e05e8ed4d10e9fc128094bda1d502ca10f865605e76ae2753d7ddcb1b275446e206f233088e0c91484dcd44c1c14097ffea4fa22735bb3bd6fc65683484dcd40c4a19d8fffe24f14061beb1902eebae197a77bee4b7941ea7da5de6f27546c7b6243674d2cb1bf8da008b135f83091c17939206c5a9b29a698a83b04d37542bfcab4b59b778d784464708a426e6a06260e08bfff507e421c7da909b9a8189353b1fffc41e249f218103353412ba2e33083088c8e0dcd110844c1c0c10519ffe9cd08f07253efa9ea403b27454deda5752dd3986a422d89a6b14695293d22c2a1a9d69c824c449d5e8448c5b60590025302e27eb2e111c22909b831a8982812d2fffd48798e5874233749ec0ea17dcebf9d789960bff9730899209548a8b82cefd032a87b5a20456990d42e9434e98d39fd059027a9f1568cc80a4c2a9ad26df58d97088c8e11484d8d44c1c0c117ffe9c30c22bf14eddbe6684ec47ee9bed0d4dc0c4c1c1160fffe98384a50f583326fb11a17c8df405c3b878a10621a3b4712a47579c6fe713c61af1135f6e65df684464708842406c6a06260e0828dfff4a1))| 17=>(1,0,7,T #[0x81b3404483043fff])|_=>Z0),(fun| 14=>(5,4,7,E (0x83a5e643128e136000,0x2f4a142a6441d8482f1aa55d76d2e064158a04b2d19a85bd666fd5e5d3ac43efa99bb7c5b3c96c48050e73c879b02f0141880ff341238cd45f05e2410f8370f0a20029bfbd52161202d49e68d536c0fd1a99187f1dbfa3ef627f0f83d7ee81c124371e7084408f107cdf9a046e45cc83e017e07c4c3286b0ecfcffea92b0e2d100fc6c44ccfb2a34b1f0b42d97a6bbe0e317cd3a53e8375590664fc201412200fc82e99d3802c13783246514839f5ffd69c5a94a201e5073df342b2e822bfd16232683308887620f9b08ee4407f83c3488fc4f8145b0ca1da19ffd52562059e0066b55911c4e679e0e6442211d43be6f4e046d45e27c131a00de06c39232867f5ff169549507801))| 15=>(75,3,7,V (tP #[(0x165b144e126210c50fdf0ee60dde0c6c0b5a0a300937079e05c804390278014a0000,0x4e883561970f1c704ff4337a6e7e46c26756722ca09609976348a8a8e3ae21f991a8e81ca5d7135da442b0779b0aa9ca8846e411ae0789e080650cfdffc5a541e006d71f12a93ba7f2c9e56b3796b44423bed9dac4b3e0efa9d6e6d0ffbbbf3f5090082ad1d874aae4199a72a24239be2782e078340187c693fffd52541e00744c79aeea500e599b47b4177f61b39dcd3f4f469f9d396f334e3ada904f7d255a8dfa0ef21cda35c4f055a85046ffe2d220f003968741ea4a0b27b816e2b4e545485320c703c1a0e0513bff8b5293400e9e38bd245ec73c96b462f28297297a3d820e0789e08430285d7fc5a549a0065a2f1588f69c667d0f7f764a10291a7290a6418e0789e0d3b028adffc59d49a007c8fc7e15fea0f8176251364c53f237b23ff1a065c91a2bd23f710044190711ae0b81e2783aec0a2a7ff18b4e680199c811f1178013b0f8c4f30627da469c0aa90126a2e0789e0943028bdffc5a539a006142859757e5cc7c94d9ec820a8863b71291a642aa403da8b81e27824d40a2f7ff1684e6801e8beebd8fb64197396173b7c048dd257fec9c0f13c1876050bbbf8b3a73400ee0e903e1955389451ba1d8791323b500282f61d18a3736de7bb19eec9961a72a2e4299a6d1ae07830280041cbdffc5a949600727268e48c9b0abb8a7959b40fab47f1cfeb213b4d1fb973f069335330652ef7651935ce7311e91a73900351a02b89e07830001f2f7ff167525801f1d4488e15e82f27da8d17b11108696ce85629316f569c425757a5234e055c80934da35c1713c1d3e052986effe2d29cb00321c28174a94ecaa47f7e1fdeda20e774e3c1d578ebac28b3ce671bf088e10d741e91a642ae403da6d1ae0b89e069f02935377ff1684e5801fe87c61a6bcd950c6bdf199c127b717fa86167d0c805a6ecde0789e09430289dffc5a53160070a5f12375eb338db81a7432617fe83cb5fe235fb02be6bf8fc032b3781e278307c0a1f7ff1674c5801),(0x1a1d181015ea13c2128d11b010da0fc30e640c7b0a9208cc07ab05db03e901ba0000,0x107f29360a3bd07d34ec2186368ed149ea6b8d029bdb0bda064486bfd30530ed844625ee555a41d9185e158283d6282c110659ce0789e0c0a0c83b267ff588167806d44fec4248147780a1b4cb9d8efac70d5812c0d3de4fe169ea1ae71ed089c9e26a35cbbd2020ee4382a4a8e6f9a4c99c80299a8b82e2523e0f8181587c412fffd52149e01b54e070e949076162f2c257c9f15d4096677fc89c3ea7ea2ea19b04504a3af236625230d03aaa6a796d5438e6f9a48d998c29ca8b89e0b81e0d0081587c410fffd52541e01a4ef8f91a949f44874a2593c11b2348b38195394f271c162125f13c1f02cf81497ffe9caa4300d1fc5d6116aa29d91a459ca700ae2783e0b81014002ffff5254e1806af08d91a440066699c41306bf81e2783e080a0150fffd41538601acb73c382d51d4d4d5ea4b2f585fb35b4f880220e045c0f13c108605113ffac30b4c00c1835c5acddf38f2637df912818d0687eeaaea5187038d242a401de6f89e091ae068708c43275ff169549801a88af33f448f836dca5d19d8cbba371d43d1d979bdd1797d938ae7567c144bb30870c45b5694000220e083c873614435c4f03c18001d993ffac48b3c00d873b26d75fd2f5ce340a4a03821f7c37b16c0af5f73fbc3bc63781f13e4327e0dd7faa787156701de419166408e6e1ae0789e0c008ecddffd52459e0070f946dac9e3158547573f205ee9e0687c032af242fc9ccff864821b908b633a32ca8b044191079b67390e278386b810c83b327ff588167801af81c5e3f80185ded3c793254fb601484e50088320e321c0f13c187605133ffac30b3c00e38514ddca4d59c1e67ece4ed6f9e2f56d824ec1b6e7b0f05ae6c5a69524f1658dcf5c9d067ea7df51fba67c35c0f13c18141d8d3dfac30b3c00cbeda314273fbfcf1decb71b2df111973d6b70fa099ff986b5c3ae68e17f4ce1e7e7f7e1d038cad381503bc853227545cda35c1f020020e6effe2d4a4f003c56e2e2ee1db852aa3f207fee5d919432a7f63ea51121b9f26030accfbae9ba094c47df36fe4082a4a82acaa4761de419ca66a2e6f8248f89e0f8180187c694fffd52149e006693db34a3dd08f77fbda31f7dc85929d24a9c255c40586d6661376772761fb2747b96b300cec6541de439be07890b43f1f7ff16a127801),(0x1c981a4217e1171f14da130811270e760c530a1307d206990455035c02a101d90000,0xd9cc8a32d2fa306abf27e40bd3909c4b73765bba4e7fed85126f5e5e8db1306df71d835dc82cbadd4ecb3e95d24028167d0cd990ab9a0e62215390e6f89e080fe05878d4fdffd5245a201ed8a2fe0946e0921c591cd5cb8673f4eaff238eecd096efdf7888dc4deab4f63ad0ecc050ed9f1a2fa601f323dadf77392a044c33fe27b00220c88208737cd703c48641a8765cffeb0e2d100f1fc5d611a400088321c705c4f031d86a05133ffac30b4403fff163fcfdd749aa018ea53a770d24789dfe57f070a485016e2264c7c2d60537b3aa5753aa72d0a6da27602a6334ee55439a642a0ae9c10922e439be6852e078341cedffc5a94a201f67ec9097cc865d1136a1cf4e919d056aff673e79b1920dd2ef48083b98a0a92e79be40280ab9a67026a6782e240ce0e0561e454bfff5485278079a79e19986eea4b46fb9a3d401763e2b4a54d33f93836b6a7fff521bd54d4f2daa88e55f2015737cd322cc87d4e703c4f0605c0b1da1fffaa4a83c03cecace155115ff9493e7fe0225a497a5daa9515fec7ed1a0e3535894f74aa69288811a6057c6213a0d0ea536f86f4d99275fcc6b43ae9e01980e3624b1a5c6fef100441948853a408ae0789e0f82014b9ffc62d41a01e77fa0bdd826c4b7e6a9dc7dc7a2c8ecdf309991f70fffbc18af7742eb0d5a7eb7a0487039db629d234b8b30e034e0540e87291721cd8a54d707c0d5a839bbff8b5290c03d9966fa0a1ebe7cd5c24402174238f477bb73ada81a8100456b52f49e549c372eb39ca6cb76d39e09a24f245113394e720028174d147c1b37c4f05c0914c3d5a0629fffaa2a90c03cc22aef9a7c08c26c46e7193c191f5b4ba67636795bf555c36b5162b9b1a426a10fcdaac9f6de753c1d2792288991a44052e4abe419ba69afe0b8322b81e26ad47d3fffd41548601f0b20356a103d6d541db99d1cadebe12d2213538157214d017c1915c4a8b56a3e6fffe9caa4300f1f6287066f0e80eb16ee58580085bf855060769ed21c4f919686b1967b6263c6cf08ca6771e44cb8d46d4f1132348f20682444b00d4d3364511fc1703c4f065901697ffea4aa0300f00794cfce23f231ca947e91a642ae408ae0789e0e9a4ec2633fff4e5501807a2b5514e108294d00dc4f07c148a0281657ffea4a9c300f857b23488174c80c27b5f4d703c4f071d80a7fffea0a9c300f5453a641c350fc6707706f2412e7c6fa68161c0ed0a2ddfcd394441f515cf452f711b0d544e70600441c84028e2783e040a0003b2a7ff589167806),(0x1a9719301819172b1666156d144211ac0f980dde0ba3095e071f05130451022a0000,0x4dc256aa714b07fe5406e93b287b91808bf6af12509d9167219c6839e419be090ae278167e2d3bfff4e580b521b2dcf0e0b547535357a92cbd617ecd6d3e200883811703c4f041681444ffeb0d016a437a64ed2341ac22180c066348f81610f13c1f03c102802997ffac2c05a70d15700a76462205021c6b89e0f82e040502cbfffd49602d386551f7c650f190423ba06016034440a703c4f07c16340284267ffea0b0169c35f038bc7f0030bbda78f264a9f6c02909ca0110641c0e382e0789e0f3b028a9ffd61a02d3873aed6caab550faf2bdeece8cc5f85f87405c25e6aa89e21192f46d6a8b62afd05a98f742135de72cc617520895cfc105cdbab1f54ed02a6aaefba2b35122879c8550ec10c6b81e2783e08041efbf58680b4a1d125d526bd782c51e7e5971552ac7a4348a89682d8e899e064d9771e1a31a988c6175aef3b903fcf1bd2d81f492a8e366a2853f4b8381e2783e0804177bf16680b4a1a72ebdde44ae0a69918f40af9df99834cb3c9b494d4785a806b807df352d570b337a7c40110641c08990e0789e0f82028a9ffd61a02d287f104189ddb226ffd86dbf46936eb35b6004b42d9d4355d68859210b7c1310c76947d60a688431e805784cd58a0063bb4025bd7fde636acd8de35c0f13c1f04050f3dfac3405a50d325b9f546fb8928cfa61f17659965ad9754051158b62f1efec76598a6d79d55f307392a34f9d0c8f3ae3c72f0a107ec1ec4101c888410439ae6f89e0b8161c2310cc9ffd6285a601e9f932cc8049349566e95a1283fca7f2cc128c7f61b937a9bbe802f98fb963a957e00c7b8a868275c6662b95a3b52e58de29ec00888226c45cd081c4f05c086421973ffac40b4c03c271c3fb1a5dc14855beac0e77b21af65645bb3b49ed51abe1bea96af86c6fce2d9bd129d65e19cf5a9291e40008838080500500bc4f040008622973ffac38b4c03d408cee745aa0220e071c1703c4c76218144cffeb0c2d300f7dc1458f7e4eff94b2ba90c3b83b14ce2f3b5f4643847a740d6a5b8340d40c7c9698e67202eaca9ceb0e030f07a182a4a11867004188b90e6f89e0b810b489ffd6045a601e70285f70e3d4221a5778451e99db4307e189972a3c11a114a406a3d17b047ef845feb60df996b6604a55e24b995efa800410402e88b9b10382e2781000352e7ff589168807),(0x150b1327105a0f880cfb096806c30408029601cc01020000,0x45cbc6c2154b2b9b795f007de6e0047641501e1ce67af79fa7dd9011916981bb66581f961f31e8384885610f020780a00713c1f0414197ffac4405a93c48430f760081150af36be6d134ba65c3c007f4627218f5354d1a20ca7e470873618fffbc89b7fcea1150bbac17dc12939e8dd04638d5e020ee4170c60503c390a19ce439be6991c672208781e0f82e26288014fffd52202d49f50c49d904f93544c101078101789e0b830a00026fff58680b527d7f05caf61b9c41cd7624d4d170803af0d2e2c5cfb8a684325da17ed4454fa9cad6ce494b3db3f5094eb3396397de308e88e8b2d9e941c6e82d48e8721cdf3424632a280bc4f07c105000197f7ac2405a93d5f2f8b434ce45de670a1746db0d5d8cbe4be17159bb7714f4d2c4178013ac266073a47f67276169bb3e96500a395f8688997d52f36b4db15f03336c4fb92de7b43698f02f565c98a4bd67d98d1453ad185aac84b45c9a4156c911b2d306671d7fce439be6b22e0f89d0f82227ef58480b5278b22f967cbd70b3edb01067641768dc9a553d19bb31a946a7d4ed1f4214b6d5eeed806e15d9572eae03a3e83dad830eb14f653a6407541b033e9221ce3991721cd857cd333c0f13c1f040288e0b217ffac4c05a83c6d8c009ed8b0498c1d498769254628a9895eb7e230aa236bb9d55f1517af9150ef808cfcbaffad003d1b2baf982d58de54c00a587bd9a1b941505b551542b11d99e439be6b1cc8b89e0806e078361e3243fff54980b5078411102125823215f4fd868f552f0a3a810278018e6f0ee0aaaee4095f4416b381e2783e08380c88bffd61a02d41fbfeb249f4912731012f83e0789e09c30f00a2efff58980b4e6effac927d24499c4030e0f81e27826d43c028bbffd62202d39b823b7273b40d062aa59c68a19c6839e410ae0789e099b8b42737fff54580b521)]))| 16=>(61,2,7,V (tP #[(0x21ce1f601c491989188c164e147312dc0ff00e0f0a9008f307a9063e03f201910000,0x2669fe3d9e5dce2e8823eb0a32f321eb6e1f7abfcdf5f68c39c72fcc7c04a9ed2023fe147d1ddaf2fdddccb44bd2689256471320d2a0a567afff9e859229c5166f064bc4e0b02ad1617fff521806cb3f858044f7e3060c12190cab831d8e32ed19c19dbd4b1f409bbaabe17c0ca5c9198a4f96273b00d211c93a10fa6ce30c2be2eaaf6d139e1b81d7c99e5bee9c685e4bc55ac35caa1c7a0ac37b19bc3b48a6539105166c7189c1e07042c33ffe9c300d1124922793886e96be95ea803cd98b3b098fee16b4e851e79ea5c28f9fed7a7b7e9f66760968ee16d3e8d4a96d5838817ebc7d129d54ab39e1cdc8304f5e231dd646c648107cbd7123b4da685981c4e0f040a23ffe94300d67aa168c160eb6357b106dc0e8f4cf35fe5b7219b0d6071382218f7ff1698019f649f98ed000381e42d55834a55617fe62ce3f563b6c3e545ebcd7732bb7d682f0a6d090c6c4560f500996fb08ab2eff05ce271441d042672189c166c3181c1a1e3477ffd5260071017fc0641c2142f57db45c7add35cde2ded88e198803d86a63fbd53cfdf10e2f709a6369fb71a36e381cf4b4fb81d8d6433781438b47fff8a4c00cc83aeb50501aefb7613095b7a7a63a7d6d1c06044c74d43af2be21be6d4691b8bda00e328af219b0d60713831d8f7ff167801be4ab13b294a4f6e0d18c59214eb89d5a49af9ee2f52bf857e5e1dcf9f75e14eaa60ce9a73c5c8ea01443e8cb2f6199b2dfe804879dc5dbb2f08c9ae218a544da269a09f543e1e407dc48a703a9951640319bc4e0f05818d1bfff527801a63840a708d6b46080ff926a2bf4ccccb5d9314a575ff2f93dfe20d88954d1d22994d77fecf81286eaeecdf1f1703b1ac866f03895d8b48fff893c00fb6db409cc2b5a1c93f2875a4d3fd63c8ed5109facd806f92aaf91a9f22fce024c7a3e9a41da017eeddfccffc8dc0651be06e2522e918ed8e740ac8e7300ec032cf8908bcae1806cd7dc2e9d946449fccdff635bfe7a2e60532bda651a245321d4e28b219bc0e2707828d19fff507801ce906946b4199e9c20e3124192a2217bc559aba82be286a5ee67c722488102370f3ac2e49d03b90cde0712b58d2ec8fff883c00dc10cd8a8abd6dce4016758a1028bab58348cbba2ab8448a71451a480630781c4e09860a33ffea4d003fe6d3d8999b8de2e97d82e7fe2f02fdbaa2c941dce3300ed8fa5a7848a6538908d60b0389c1aec145fffd39a006bf82de78c351d13f7a15a27e385dfe06ab9d8a0183fb12e5def5fe15943480f0233c85545be9624a0847b068074a17e59c203f026d1229c5126415900c26f1382c0e0e346fffd4960071795e397c3c4385491440992d31c8513584520820896ddca9d582662fd55e4feffecb9d695da09d2c09ec550a03dc6ffe2ef2236392bf4e4ef48a6539904de081589c1e053f1a33ffe9cb003d7fa248ba6e5a51e58f429030a45c67ca4b9c648bf8c1ec4caa4b636b46f537381f56f09d058cdc0e270782050ffff4c5801),(0x356733352dbe28cc264a2332211b1ca6176f148e10c40bf1097606c504ba01ec0000,0x42f80f674781648fcbadeae060319b1c1dc611c0ab20647cbf7392b5a8373aaf53082aa7c7abe39eaf274029879a3f870cf4d606d08c22190e26f34cdc0e27063b2affeacb00f9a462c70f38a13c9993816689eb5a48dda5e09aeb7097a537e14b3cffd20f21bdadbb9724d60b90ca5a752618fbe7f01ed94da39d5c5208230a658382c1252ec40265e7628646137715e7e062a601744a8b368305c538a93beed5a53a595c91f7cd422c3ec40a357375132fd7fbef904176d171b0660f64f7f46fcc39cf3bd4163e26243c980099daca3e7bb939b14407f72feaf2415afb75f9c30762248a71329bcd6099b89c0e0c3e67ffd49601f2780e5c6fcdba0ce85b2161c2acff2d3d12c1f239bbb890912edc311b1bf67f3bcd1327d46fbd797751d8686ca58a75bbfe78d54e57f5aa614439164ede3eec4295610be29d69e31fb73e88a5f388cc0f894dab57a5c0bb53a670176629ece246ef43c470adfbe39562665fa7b6df883134571b8d360218fd5624db01075338763e860fbc33b5e9b6673c20892299c8669378257e0713830f99fff505807d2f08c56a6ec5273fcbeff9db3f35320f5411d676c3b153919f5bac056a259aeec8da352e7a2faf9e9af19df24d440a5b21237c86809264fd623deea35e096cd8a6ceac66699b89c19143e37ffd39601e09da6a955182870b7fd27ac4bdb7fa1e98e399fcd222b39d6a70c41b72c95abecf287e110399788b1d1694232ce3ad38ce35941f80ed8639f2ead8da83fe24d9f2bbff0813e1c8253b43b8874549d1673bfe089379ac10170389c1ced9a57ffd31601fb1302f439d1a29831cb5f8616105db82da05d125799a233affb0623754a4562dd257906eec9a21829563fee3316f0953c0110c870219b4d2b30389c18ecbbffab0c03d72aa0018728a6bda0a8afedbf44a74d1ac8a3768c0622cf37d30f871b46af7ada8154a01ed6174b2afbadc77d3023904b76129c3dfd5ac5f478547d6b8a70a9094c917019095dc21e0a584542c6b81f13ced3b700c1e3c1396cb0cf2656f81ce091da52c856a9486da9dd6de3e944f67e93f2b6afa020b255af8db82248a73219b4d60f0589c0ced5a67ffd48601f3a50887bd5105fd1d9ed5565f8b59686519e83bb4af6721fba2a07c27083865eefb3f2de9c325c7fb1776a09a93fbe1338124cd5277103beeb5ce055f74688a3dbf0f5ca1930738d206f86369ba1778fdb64f4f617fb971caa75f5558b2e75dff27b6755aa27be680cadbb7117d957d4a1a9e19d7b079d956829a472bf2d54a99a2b8f72d36ebd0784ce6d59ef9310854ef8a8ec44914ca73219bc126b0389c1ceccfffa80c03d7490bd871285309393db89fde3242333880b4abb90201433a2132492a728c8a9d7419ca9303948b0608ff8dfca85ff5cd7ac5d240e84599d205e92fe3d36149a0b4e347c26f6337876914ca73219b0a26b1383c08147667ffd38601f0b1550c58eb130c7c894fedb6579d2af0dc4c1afa7d025002b384c3719b6790d92c6b0bb6ce4cb5b1b35cb1bc9404da90d70ce160d49cff243204e1bcca842ede4d7213aac27f36bd7794d485a8814aa0bde29077eaf4f1df9e7d0fcc502e7fbf78a4cfc24f00d450841126b3782c0e27073b5613fff4c1807a9db6385d78fe14679629647987d0c1a2a575dbcc193d03a247b53ef301cec688a2abb7591a1b32d0384721fa87c8b517d5bcaeb4e97f4471aef69b2497f5f8a8fd7a3b1ec4e0c70956d341ee5318f83a17ae5ac168f607dbb36dea91bba4cc2eef7bd610f7e263bd6559d02de0ac0f0b6da1d09221157322ab950f156242ef9e2f6f8d0a1044914ca71209bc86093581c4e0d141f3bffe94300f4bf67ab0d6ef0f116b7d870ef3853c573cd02bcb3a9fa4f7f5ff43189db7da7dc2d66e6af2104c41d1fb63838be45851baff3088df47b43eb195bc3158f0d03a14c7a38430389c18287635ffc59e01be0f860afdeb8217aa177a9c2876a599dcb9cd1b213b87e2973f28e796a21da1bbe2eb5ac454feef7ede98a671d2f0b25d61e033a9e1060a4567be1ea03acf528e9b8914e26496a2cd8e33589c1e0b031037ffea4f00dbf3b8cc945575f3ff4c30053d9b2d0f5da2bf3b9bd933b51474e052cc2f289f27bcb8c7e330382d6aeb635785fc96306aec0bddccde6b038961c41763fffc49e01a0ee5eeb100b5a01cc15ceea79f222b73741fada7ddfb788dd0f1781fd870cfaa27682f10ab472dd8ddf1884075128ff2abe9b9cfbad00144befdc9a6722ec83296082fede4448a64609c5166c719ac0e270782881bfff507806a128dbbf061193054addf984ac0e1a6a3a06da2627cbb2a3f7b0aa41b295910dfd2d767a4fa5c91b072d26c669d657a13379ac0e256b105d8ffff107806),(0x35e232d62fce2d592adc257e22b3205b1d8018371542124c0f160d23083003470000,0x363123d5f2b070850c0f2ffc9b80ab6519dae0b096df9addb4f57b5ce1fd249e11c869e37b6827077509b9aed37b2b0b2573fd65b5d81016207dbed5177af148d6b00f632a85eb8fa447ce9622710abaec1d70c3b0dc6b0389c1e08143fffe02d2863e6720f2cbc17c97ab7c297f23e73138664934077f73fe84a34ad322ec8357c7b48e70d087bfd411d59cb5ab1478e96b493e022b4fcee9175ee5e6b9bdc4ea43ace3fb8732c09366f60017769a76110c870451bc846b0389c1e081465ffe02d28603fb65642c1f0aa04e0aa8685fbdcd0be1e59b8c38ef1ff5da7a6481d07cf6c94d42c59b4beb4d18607c314314cf30736c4b6eadf8c02a73e222931a4200221c4ce43379ac0e27063b2affead300f301e4c6dcaa7d92acb73e845aefe53c963fcf430ed4082eba5b1a3e9628645e5e2a3900709caf4a7c8e45ebfdf2d6d16b5ccf35e95778189cb9e4b1ab22a470df588b219bcd627078226117ff169807e45ab29ecfb5d7ca6f013bd268ed07fa2a80f4244078777438606a3219154ba2adc4c8a2bd3563abb71018a2e2fbf5b400e8f8e9928c0e47e1eb94d1772a6a24309a4c28a3d629e5a9c19c5c1e87187fa6ba9a294e79d463e532cfe03166f1ab6dc1133911f2fe5fd772e2efd2174d8315d54eca8a1f585c558de0610a77daa598e0678627c767f342bf991858c22456c8c1bcc4d0618fadb8224e267219bcd6270581c1d150e67ffd52601e4c6ece860a59044e2c5afc8e25ef327a6aed9c840027b8ac65f88e938abb43a81e92868b1e974ae22cb593954bf1220bdf85e9feb5b61deeb14b8372826707366a8b4ff842ba7da75c5b704590cde6b034561a1c8fff8a4c03e47110557766143b4158ee4a981e11e45d0c0c30fa87a03ed6701762283680566b8f595cb38816f059a6331e20b561285ceb33e69ce2818455c14088653990cde6b0389c18ecabffab4403eadd503c642ca50eee8367be06ac5cdb21b6e38d565f74536be9e5813fd44234daddb5ab49de90eebb1c47af4bbd1ab7ebbdd7a2e7dcb6169dc72c67de4dc77ee1fa364289698a35b6f8d4e7ef88b219bcd62703821a917ff168807aed8adbef9295a20d317b2f8fe4642fdfd72a83e5c4b8239b64010b588bd9178162f920873aa2238bd97eb80d8f675379016f240ae24426fa011c8f006bbc28d2db1fb3d6388f1c412232f77091f17bcd82b33e079665619f9e3a1eb273115eebab2f5c5ea41d548a222c3c5d9fae05676108469a569078cbb23a67c5c6cffc68bd4944a32a862d15690548bf65cd0c800220248f251044914ca73219bcd60b0389c1ceccfffa94403c84d65fff49df21392a2dd662ec52bdf8a60f6fbd5c56046bbc4c9d2ce9c295c153642f71ea4eeb3e8ad88dd4829ea99111afd0f80d13459b05f97efb5ba228c5cef5b3b7f82c072aa145f9536f25104590cde6b05899db316a4fffc4a201fbd9b62e66d8ba468833e3366d9c43c553f192172b513c34e1b6225be708038f646595788271dfb31e708c5ea13958c0a755ee25ec19d5d72f2fe4d93124411ac385daa4bd5848f84d7eab6e2453828c866d339ac4e0f04052299fff5278078e628c2e38fa2c221079f805416452cf111472ac156d837149b5baa6728ccf6a620701b4baee7f5220f745b5e8e2db3f447b7259e6ec2a7b637a497aa8e11880d80b279ba064943f96732edf88bb62088644d708914ca42219b4e66b0389c18147667ffd41e01f2ee819d99c2233aef063104f1655464251fc029d5a511d793f25ab0ee18502bcaf98f752f4bc794e1635443c0110c870361a566071383050ecbbffab3403d478c094b75e02c475114d7163e61c938d0f09e63c35d93632d2a9d9187ab6c7b7404e513c1c5e35c987da4dfb0dd23766b7bc72e06b7d09ca91d561812eb35f88dd7955cac580d6acb401e30de30a353ef2b9a4a1f67b06f26badd0726654ad98fca11dcbfef4cd8a54dca7236bfaf831f846a337b2d81f96f1818de0036bd362199062075b73aaa71c611245399bcd2670490c4e07073b451bfff52680780719768ef411cd3fd59485cb0a12c0a8553a732f2987ca0141fccf3efcc3df34455f51d4b50058c8f4ccfb54651bc51caba1da6f9be1c68a1cc37c7fda06fd3f51bfce4a31bb66c4c18f04e5b82eb331a0321a0e5be82e69b60cd6dec9249c84ec12e6f0079f378cf0b5dd8838912571e5181de1565a758d23ddc864893b9614d6135740fcafc260608922994de6939824860713839da28dfffa83403d9abef35a7ef78e4f389ca94804d750cb05fb8917cf4606dfded884066956cecb910af6961e81d5df306d561a05f7e48d7ebe6c9df6066dec8909fe4bcf08b88dc7c561a304af6393dbe90bcf0a1744b7d4d6f8862da245329c4de687890c4e0f028a1d99fff4e6807),(0x28232508208c1ec61b2816b614f9139b10110d7d0a05065c02590000,0x61581dda886550e5180ea2ff21600d1b439cbb55b0f931df189d36ea2d92f4562415306a34fd0c3b96a1e212e015b49bf890cfad3447c04c28749b56daf05cd66a81a8266245a1df81fe74872c4a9c4ee643379a8cc880181c4e0f04280299fff80b527e0f02be162e4be9e00031f4ac2d91186499589af62e26c06fd1ddbc607ab62eb6b691df3f88840b1a809602d75d538c3dea2d38045f0ae781f173d6fbff1cae9de5f2924e61f3077e5636f6569d0969d8c40a72eb7d45c7da1eaff7611549fa636077e29ca7f3e8b6fab0388781dcb767bfbc59fd633e0f249b496cc0570221c8cc8b219bcd6071383c1177ff80b527af899d701eb5f8e3d85ab92e471163e71b45cfaa9cc771600f6c503a0bdb27b36ae309c2c1f980ae0443810c866f3581c490c7655ffe02c49e15c668c867f7e0e065d39ce8c72e6008367167bf329f26211f7e7f649a04c338f7b38a24016c32b0f44062c7bdbbbf68bd27506202dac69a1a03f50ce8233fa6da3990f512dc7eecd19b786cc68b942ca8ab131ea552a997b37c72da3656b95d6e13219b1866a3922c0e2707820297fff80b507a55f76f23384674b8b1c80ce957734f32fd227750df9cd31e84afb4fe32992fe4795efaafd6bbd6445f950a900ae0512114e12fd1eae34e7a8c08c96bf2e5af215f83a39a9a2268d96983157c383f6c6d9255f0e16fc9d0b1ec046dd656296ff562dfffd0f8681ed87f3d1c8f82aa469f20f50cee903c926d25b3015c088663922c866f3581c4e0f045dffe02d41fd73379ca2e949abdec8b77080aa52ec1d00be3c5082fc60f80b5f6e54703b45a8c0bd94e40de02b8110ce43379ac0e246a3b26fff01620f9dac26e48211ec41c19ddf3ac06239c3bc51165ca4082a063360453fa207110c160713839d8288fffc05a737cf48d865a10f65cc72d967ec8258492e7f3de5ba70661a62722fc80bfc449e8677d3c8dd04b626793dc14d89b264e8e3862a98708d65add1282b8bc4936b69086e348bd1a3c974cd73a375b489e14aa3815b1225507286170092aa8f735008864381bcd48a2181c4e0f040a32fff0169cd9605131b2cce347c1c0766e9c998f4c5996d8ab64bb306833c1ffb8beafbb7796a3b63477c83e94986294422dd85199dafcb364a2c2d940d9b0fedfdb7a91567408dfb5c0cc6b372cc4e0b022d23fff016a43fd7a15b32dfe62596e99ddf47bf9e936b9b2214c0a285f974f191bb70a96dd88aea8234af9a989f96a7d29293dd3669ef3eb921595b165db70a948da88b75005ff947e6a4528aefb42923334dbc524e9a4eae783376297c33aae7cc4930443822cdc6b072cc0e27042d2efff016a4371747a2534373fbba789cc6210a591fd0238e944eead6bca44c90ba799a061ebd7c0c23079ea3a64690335d36524a9f9394c26e1f432bdb89a42869887a0c7f32bd3903692a26d265091f866545a9cbe47bf237e9a7e3095a525658b24e347c26f633787790cdc8a3589c1e0704140295fff80b4e1b7b3d8bb1d4389332be98a8f217a4fbaa871bb9be0e1acbe38bb923c2eafc4b21b09155aa05a20a2d2231fbfa4d25443e302f700f6b089af6dfb08ac53d92246240793d7715da016e177244cc723f7be0e42e352cb5cf171dfe245b818eb44a4941160fa9aa96d9b2c33aae7cc493044321c9166e352cc0e2707822efff0169c301fdb2b308602c929e34338bba4fe5c8e43645ef331c086aa81aae452dcad4161b133be43b3cabc2a1e75b999ab37104be042797f0dd100b5066e110c870459bc0e27078216157ff80b4c1)]))| 17=>(3,1,7,T #[0x2426e06260e08687fff801,0x26e6a06260e08407fff806,0x3d62ca2809243ee3318426e276426e6a0a06260cec8fff807])|_=>Z0),(fun| 13=>S 1 3 1 3 2 0 369| 14=>S 4 19 3 3 5 65544 0x71a2a01066468808045e202a6d019ac83| 15=>S 19 90 6 3 7 0x71100100c206044410a002c40b1418402 0x14d8680281859b621eb458917e9844c5100000d3a488239985541844d684c958361085800c5018001430120a01c1d0021b110050240040c00000171700080791b300c34ad916b8c96203b12990004703e1400382258914484b7481c8800087c129280b0001983800d2456b0821e0e22| 16=>S 38 242 7 3 8 0xc00300307090801020a020a17010202021014020d01000801060905000d0003030103010001 0x43a0000031300000003c0000003c0001b62543d0e59671b86242592aab14e8b00912981569ed0800000c6400013001c6800422d0f28995e9b0002084e000001274004370000038c00704a2100003483f0650d8000000000070e63e0ce0481b96c014000000010b20200082c000c7000a0400219000a740800822b00160a1d80e33a00048c8101906b4d03db380010d02b81642a8781d86000200e1f92024c1a88738400ed01aab5e0000008600c6c000040000000004173140000000026e00000294d300a08700d00000220800084000005088104340020682ba180059231b81c000000010980011774c00000588000000004bf000ca8000000007000002ee1b0f307000b13052428000002bccc000001084126ace4dcc4000008472c00e5248540021480074a48c13c2f3320b61f8008300021c20d0000021f41100000000000d510080000000000000000| 17=>S 7 32 4 3 5 0x304010440 0xa59612b4a401d988009305180017829506c9c800239400350784893399008358|_=>N0),(fun| 15=>S 2 10 3 3 4 16 0x2100470c0518a04004| 16=>S 29 134 7 3 8 0x50707000d490f060032080273000e090a1e0e0c030002141b00020708 0x20580a00140c0e9064160f61b00000026ce581e626ca681640c080a42582040a1154e40507104488849e4b08b88c378360021883f00111c080260190c01cc27887cb607919875c860e017e5901d91f310110860102ba2e0961db2781343880c4083e0fa00c046300341ac34c3a0bc1741900710800416e0911812423650434a30000660000ac1a05a0a19e812054c2c00000064060000000260188442c0000020a7090001138291387903904b43000000247268834400044a| 17=>S 21 92 6 3 7 0x3a2d559ac38132013801a46062007a3808e 0x65ad8081f33e0306c228a407c4e04894890864fea1a70680ea1053d51089422d89fae20d881479f883a6a54111489083c2c88e1c850d068c006682b00000a220c8a80086009a36858980a85c2e054008921e452d50761300353a2800058000360b00082c25898182882010954120140123c54|_=>N0),(fun| 15=>S 10 50 7 3 6 0xa0000bc5b531df 0x960230790486280009509a0e1a3c4a2ae60c4515124bd412487a002d592b381a94de80054e2b2d322791f1000d8000720ac0f00f0000000000003e0000e822194002165ac| 16=>S 17 88 6 3 7 0x2022800a000850a2c0c3800c00025 0x360000005800026260003092e4c0022f0cf1a0020f000968e4ec002c5ca2c39b23102041000009ac100d4eb0e35f0eedc0003d0520e170dfb77278ea9930b635a22517a3201c340dc06000e33243c00013a9400844d600017000008625600012b98000121a3222125c00d9ca2| 17=>S 2 11 2 3 4 1 0x8801e18c002f14b|_=>N0)⟩
def fms:=fO (uf bk)
lemma gm:uo bk (B k4)=H:=by decide +kernel
lemma sT:ua fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,17]=H:=by decide +kernel
lemma t0:uK fms ct bk 15 0 38=H:=by decide +kernel
lemma t1:uK fms ct bk 15 38 37=H:=by decide +kernel
lemma u0:uK fms ct bk 16 0 31=H:=by decide +kernel
lemma u1:uK fms ct bk 16 31 30=H:=by decide +kernel
lemma aT:∀ k ≤ 17,ul fms ct bk k:=by
 intro k hk;by_cases h15:k=15;. exact h15▸uM (u8 t0 t1) rfl
 by_cases h16:k=16;. exact h16▸uM (u8 u0 u1) rfl
 exact uc sT k (by simp;omega)
lemma sF:ub fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17]=H:=by decide +kernel
lemma f0:uL fms ct bk 15 0 33=H:=by decide +kernel
lemma f1:uL fms ct bk 15 33 33=H:=by decide +kernel
lemma aF:∀ k ≤ 17,um fms ct bk k:=by
 intro k hk;by_cases h15:k=15;. exact h15▸uN (u9 f0 f1) rfl
 exact ud sF k (by simp;omega)
end G2
def k5:=(3839,18)::k4
lemma h5:K k5:=uJ 0x12001679967 cv h4 G2.gm G2.aT G2.aF (by decide +kernel)
def k6:=P k5 3 0x4038b151ca5a9018a0aa57ff181c60a4e92d5bfec62a90d529f7fdff
lemma h6:K k6:=p h5 (by decide +kernel)
def k7:=A k6 [7809787903]
lemma h7:K k7:=a h6 (by decide +kernel)
def k8:=P k7 7 0x3058c151ca3ab7fe982860acdd25481510d06bfdcc12304e7694a406286a75fde60718293a4b56fdf20a9c35ba7bf88104c54e1a5ede9e37fc40872f7497fefff
lemma h8:K k8:=p h7 (by decide +kernel)
namespace G3
def bk:Qf:=⟨4095,19,(C 4095 (B k8) 74 0x491ae549feefb175ce51242c50fe3d5d6a6809065a3d8970052ee47cc8f0dc9da368fd04f2a9ad6ea5da86aa853fd27ceda9311ab84597b1a282c71ed4a30fdd0cee25810156d0e7f6358dede6635aad9bfd837c64cd628e0247b0e1b3d2c238e7f42d703a1eaa5a093ea41878857256cfe5c5349c5aec2ff20e44ad8eecf1d6efe30a442abb4970e4ea4a9b8fb6752cf30f5c9d6de4ebdc8ee80be69358d889b8415f2a19e839e38b3f8cb8b4467),D [0,0xa9865431,0xb7865341,0xa9b74351,0xba974320,0xb997a78641513120,0xa7b7978653314120,0xb9a75120,0xb5a493827160,0x53433120a5b473829160,0x414354209574b382a160,0x7594a382b160,0x54413120b594a3627180,0xa574b3629180,0x95b47362a180,0x3153542075a49362b180],(fun| 15=>(8,4,7,E (0x6925f55424943d030c25e12a000,0x29ea3ee6ec4e93e344760e91fffea4a9c8ac6a834f017a38065cdd89d27c688ec1d2bfffd49551158d38632618e01973762749f1a200800affff5655445234e18819930c3c07017b13a4c80200e18e08cffff5675445234a1b81102d2558a00eb13a4c8921271bc30cffff5495644e34a18a90a1e03880400d02e37865822bfffd52559d20d2867b03db234846dc6eb3b3411d3516f5d705f88f0fa17c5589f08e0b808002bff753952915851864dd1536bfff827fb1014911db9827aebe23c3986d0be12c1b82e020009ffed4e44a4561461))| 16=>(27,3,7,V (tP #[(0x25f3236221061e901b93196f1736158712fc10690f4e0c3909be07d3055502bb0000,0x4b9cf093e8645b9ada8d0db8cd160a0220dbb08e505d52abf2edb82fc7d8fcbc4ebb4458f891145c719a3c7e6567b15a0ee785e6292a1436a1c42a9ad2bc4023c3e36c4f08c2e180cd020025fffd59138d2865b700f5b8ed20917be4de0b48457200a8cfea0617da5512b5c807e06c85c2c60da26fdb9cb38617c34c95372d6a8644a874140488a4294af0bc3b138d0334136d40e060ea5fffd51138d2860cce2171cec954d533eb15c9f52cc3967a6161860201223a9cc4b3f1dc3b005d0e24f9c7c3d548b7fb00842ee98db1ae5c8320a4aa290a3781dd2a0770a0cf118d3134131b40e0687fff5244e34a1d8fa0e3b26473f6e034e6f777f6fb6701b303b2cd61883fd881c4be703aef07a732a07ee13f96ac9b713f274bd37bb07034079038add3301e582d2ac85c6844e74cc73cc50e828c50b98e50fe2387c6e8904784c3182a050043fffab3a41a50d1f527e513c4e2c6583acc9028ca65241488b1ae8e0025ed1c45d85c4bf71cda3029c8ed22844074e4c1e3901442ee1c1ce27930e1850a20ca0bace100037feeab2a70a50c74b9b75efca4772c03bd71e15879a8d2853e73a2de214dfb964e68ef66d9aecc43f0ea55409ab10153c90cfb53d47002886fc2c39c3849c4f2614759c5504db19ff75515385287df6338bb8c1ca06e044cdb6c2a5a27e1f3d67481bd3082d0168be3244614ffedf335ca8110d787e6f84c32b46081123bffab3ab2230d08102d548b18945078d63a129a7120961ce6f76dd261b4940e8f72ee092ccbf67c98030e68ea30d57a7110127863fb742a198645804892a621544b18561c2f40cdd1144e19d4b1b80824a7fff525544461c9d8412ac0f26edb499c1aabd0af1b35c5f93a3333b514f4fc024f58ace17556805f75648704bc84c89f65b6bc580b8d82161850bc110a1254b82728a2261788e1f1aa27844468260f010013fffeaca9c88c3f3d389d063c713cfab2639ead9cbb589dffc85bc3f59c5709d480c05913ffc6b129118663ac3ece8488e7d0c91c79b4a04f12346bc65369923d61e3da26c155e6700db4a51187916b42607b18a818a52673ede9a191c733e3c283673a556585bce0044b78a24d2c542b0a8a6241254422689785e8289c6ba9a0c16637010492fffea929488c3573ee9880138423a175806e45997295ea932231e099ea8c8d92105c054c0bbeb50affa445ea64fffe97e4ca166c73c30a1404e5311e92a1e08f100cb0bc3e3544f0888d06c16020027fffd59d2911876dd02ff30b706a3d46326782a41cfb93995df1d238c9907f7d46e0872e4d7b7d4c69da6181280378d01e839be25880938ac0685634232bffeaa4ab0a30d4711b7631f969edb16f9276b78a8d747af4dc2b65b075eff7b3f517b6d07b4468d2bb9be100913a6ef0e198a1eff726e834425b72f86cb1639d41e2021e1f896820be1183a1701000bfffa9caac28c3fa86fa5ae008b59acd575e28092043cf9c1ae1cd3e0cfad03412492564d6a75def8aeed0d1e6fefa15443822db7d5376886608c49f7500970d267147e1e2021e1f9b6820b6278468b8ac068533ffea722b0a30e1eafa56fbc889dd6390d3f620a60081bd8b0b1cba3ef49fe8e6362ed12fbe53ad341afadf0d353836d6f39e79b43164e9bf5fb4634b38e3d7dd8504ee0ce3ffd91350ba10f11c3f40c4c17c230780d0a57ffd4a4561461),(0x1b3118e9166b142a11bb0f250c8709ca076d04e902870000,0x12232e6ae1dd227886cb252b2ea0f9b87c8b691d6b8cf0b61ad26bfd145a81f3a8cebf003598c42e17167a19b510c400e04287c2347787e6e93682236d285cdb0c3111fffe9c8ac6a83553ace0df220ac21a0c1eaa9662ba5e44f6d8c8b91a1b7c6e6cb5804bd7f5cc8bd9492e5abb59c3ee0f51238e27d5ba7d4cb8c60435443109220751fe179bc2293475b4a370c6083d3ffffa72291aa0c1a87c635f8d060215cc27bd03cb8679caab1eddcaa86a60044e00fe379f30a7cbae1bddbe6660fa85020162198708e05417c384f711c4d0acd9838161940b1a0029fffd49558d386c9b8853700fb1b4413a0989227a0514ea7662a190dc23c3201133d147605ff9a7b914499bdfed74c699a5332b0f679e96fab50c8404c09e4721ee1c17e6f20625b6c3281a151d43fffaa22b1a70e2b8894010eb7dc2f68c91faa7d6106f9d4da3efc7a88af58c00b38f0bddddd61ee7f8a3bffc9e88de41970fcc6e5e6c360bbbea8ab0f4c1f50f82fc70988612ee2389c6811c0983a068d400ffffeacaa469c3fe8e68ba860ce2522de777130f76a7c8a5af86c8222cc3e5ffce5dcafafc000e2675254726ef70d78b39b4fe987ef94acd94bea68ca38882509c3f870b54d698c73880479bc8189a370ca058543fffab2291a70e861883f021fb6c559232581d42fe827bf2236cc3c3fde32d77dcc8270311f9f3557867c3caf022a34029669ef34cbe78eb3faf50adffc82ac47d85fabaa1f8650e1308e70a8ef3743b1340b6d816185e9ffffd51148d387a57158f7f30fde46c24e4a99c149934c6360c1f741c10c497099d5a3b035f756c3b755c563afb70c44a2417c8493f50f91409c9843e18e201103b896831ac0d85a068d4011fffeacea46943e5036dbdbddf72442b5873b72dd2cb44d1ec9b33aaaf0fc96b4465d6bb15486ae34cc772560d46d76ad35e0b79682f1e6ff4943e0c82b6c0242611485385e82936231bea5b4a370c2f52fffea88a46943ed7b11e8dc7c196e68fd27b37fb03d8048b0747910680b108f91b107f365bd68b5d895f9bc0ea106d339860572c4bb26050ec2f26114851a2a638503b886271aa068d60b0343fffa72291a50c0799cb373582e2560b2b932cf8681d276d525867c1219dc7fc71f5224e96a076c1a2f0c5d6e1e6ea929cd0f3e61c7a4b8102a4e285e880544aa290af0a1d81dc4b118d606c6d0540a248ffff5494e34a1)]))| 17=>(22,2,7,V (tP #[(0x43603f763b0036c832d72e7829bf25fa21641db319c6154d106b0c18075d04340000,0x89f5ac9dd8d3c3212d7a1a8213c0d9a5a545111ba3aa5f71efecaa5ded06668f8447f5a1e0999ebaecfaed8217e97ff01539e2b01a04e23c1deeb057192cd0dcc96497884ff2ec9b4800cd8d7d14d0bbbf8cf81507288d1574d5f273353afd7d7f2ba43bdedd3213b8174629e0e6230f9bc4c83088142c30bfffd58d386ef6a76d12959df745564a4ab23e511b11d19f2612f648da5615dffdfb1b8a9ffe86fe0d49da161326894b1179bd391b03bb908cb73f4fede3461a8edc820ff33c8af82aa8823b413bc2a80a1e63117d6eda283b5fefb906ef8cfe7488748457b6370d5c294d15dbe9d2cfe802a9810f71e83912c1d75c97b7aa381a6fbb5301cc2e23378940c091b0c2bfff5234e1b74231babfd0141adc2504613e62571a97ce0d1a039f46dc5fdda9dc3b20b524f3cc67ca38cb2d188af72ff6a69b0755d36c63577c093249ca11d8f9f0381c647169a95baefa40a1c3e07072e7022a60bb2ee40647c00c005b0a3b15e6290f13cd163ced491bf12ba23b8bad40eb2dd2ee3a7a1407e230f89c9a1637acc2431040037fff5674a18d93f81b4bae117fa5afe7d8d5a21898753618d5e493881cf3128a069d16c1aa8b1dd6fab442bd2bd05f8f7f7c4f1d5e0835c28dabc3da59375398db0f0949d9423a5bd8c7e48da64c1b2ca3c26a7d689158ce6587d6dab8c5b3a4a453a6cea56d018e3eab394e465fd2e88f62818c2e2341898d6a5028d8197fffa91a50e40540e0c5b6ce61173f93a7242541d9774de1e278ffc49b07d2019fb70800763805dc2727a541e770ca18df6bf8fda847b453779986bafa2d4477947c19d35d379366c366f0f2d4690ed5c011cb533dc77c93b35ea8f65fbf09f3a9b3d5ac4b52ca747afccbc8c6a3ebcd54e7834d3ff2e6e78557d5b556e046a542985c461f131ac220505032ffff4e34a1c198fe78a01635288b0de8b44520f8f40dc34401193cef8fa48d2e5e0ae14c3ed485e181067f1a8fa003cf86285937961dfb38cd3c325430371ddee6838af45784c323ab0fe2b117bf52051e0aa38ca0794ba327dfa0038a3178b69d79eca98e5ee2c897a0a9226b64ced7b272c2ec6a5e731b98ea74604f0f704167a5dff09bd37fb0b62e42985c461f411b44e1352818619fffa41a50f79926bd569a61f11a7a17ed75c73af1b9e807853af5e42e37870c87fd2453239b6dc5523f2da14e7ad32a446b4bfdd754eca14fdf988982474033ba4abcf40361ab0354a007b1e949db85ecc8c7751e8b9be617092d1c5387f35c4854ead1ff7717a6119e2b278734e171187c4e4f59844140c9fff5385287310d8ee336af06d8f7e6e1e088c33e65be401d5b1d51820f79e72dfa02b15c679e7ba29af9f83e139942c22644630e18e091ccabce63e5a7f88fbe0f5730f54fe32761e355a85c8dbde440e137a8c93168bdf79127c80df6e8f9a9404d24f5d6b0fef904a5de3d5307e85fa1a3195e640b0f175a80da38bd7882eb60c81e91d480942185d066f1288d4c06188d33fff549461be3aef34d68adf51def74d6ae5c9804be6a49690088142582be183ef184581dc5c40afc142671b17a3bf8464665b2b4f17dca6ccab4ba674d2d15618aac88dc79f0f2891b47fe92faa5f7a706ec0407d58a7723cdfc2b0bc2cf9bead1eadd5969b45408941f88c3e6f121150612030c4299fffab3a30c0a303085b87fd5b276ba27ef6634df441e60cd24f7ae542f125b5cfb4b7bf071e204c6b9c40f6b665118ae525e7d23ade775dd49fb6b6b508d7dbc82ed01478a20955f215f22aebfa5fba97bdae57a3d9c69cfaa9026f85cb6f4b83fc97e2763dc15eb634cf7f543594a44a35c461f419b08a27090c42c04cfffd591187170f7d2e9ccea75e3306d291f6f43cdbb5698bf9e3dc11bda6443d24b610b198ef16c71d88144a5e9d262beb74b497d5f126d22a943dbc34491db9dba004675148b42366bad14d5c2d7c9dbc2c78a37f0acc2e331602f7e39da5b6a21c79351e6c88bbb6e45d196644b3836895383a4be1aefd2070d6536802cd417ab0128c30b87d066d13a980ada1867ffea888c37a01a8d6a9aafab57728ac94d23471e273d9616422b29a1aafa4a461fa7b8513b8701eb12f4bf227713dc0fcc323a35e8f23f73a3674e1317b611daf28ae9a6d5f6e73361a3f4adebe4162beef4a87bfd8d1271e861ac011b2445b766f648e83d803c87938b8191c25a45965ab8fa287c7cb760cd9bce966626dcdf6acef3daf844740f904e0834846af04a3cc2e23419b44ea6188d8099fffa92230ec81cf81aea73b7a6e1140696e4b028b0c5918505097886862d5be6496c27d86bcadcbc159cd7890c9694dfed7cb3e12ea3898d9c35d25070c3263338359108813e17b7a59eb9e5e6ca97bd4ae833092034ceadd892e97f7241418ca212d43aee099537650ed5c3c60c0f42c574e07df48fdc3136336acd510944585c461f3689c2431050133fff4e4461fd74214448a80f656dabb4d772fa94ac23a28f80ec478377944c5933867f94144108a01d47dd71818f2aec34a3734da816dacb6d6b7f776adef8848f74f329e69eba73bf38ecbe05f995dee066c804112d924009826a6d3528c165f405a0a893798cd7b4935d2d1729305ca7faa3871c02e849be3ca22d0042107b909d79bdcb44d5e1db42612e171187d026e2784d4ad21867ffe9488c3410215a4002a584edd4922167726c53505b4c97f487bc97da2c4e47ee3a9b109a0c0159fff968102cf5282b003454457d1a2604cccc3f775185bd6df70450906d879dca5caf19a1f1c493dcd9348c246466ab00852b87d066f120bc262a028527ffd5614618876fb9d2d2ed00470647785fd05a28ea719e27e30279c3af0868e11add61b47daf8391c6ab7620a93b64aea477e4d2bff3523c556b72dbcacb258239078f82d14125326152e9161a4824fcbe5a7627c9cfc62d1ede4e775df1bdb42662c45297b3ee9ad57be8e1f450aa02ad9cd4768801898e7eb71cb85c46833789d4e2a028d27ffd521461),(0x166d13680fc30c5e085c03fb0000,0x1f6e31a306a14a0da21ea32b2402b64ec68f2e25460f46ef8c4bcbe6b118432b3ff9ea66c1451c35f302a28fd3f2901a831f0a48f606464a5b149d5f892d3a43fd561d47fcc2e79c5381c2d13431c287f4189c9c2137acd4a36181237fff525541fb04465b615dd030eb6e648849a7c3d281d477349a20d8ce38a33ded75c04d43f8680819bbcf604856307933fcf1e85f6ee76b25de758c9b6530b80fd6d0891d87c64c5755ac0a13228f9c5923bb0ef504d513af56bdd0ab8e7a4f2349b1f474f642f43c1fc3e83378940cda18851197fffab1aa0fc87ddb367b2df5fa610691ac5836e1bd73c0cbbf8eaab78209549be4fd4ea9e24491f8f7f62971e4f33635855da3406f4dd7bda36accb8d4bed37772fcc4f9d42a532ee7bdaffc9e8fd1f6ad7fb18d1a62e22266074f222ff1f74980fe17419bc4c23528186234bfffd48d5079f740660450fdf6936e6c220da8005dfe560acf1ae7aa571ff329a31583482f56eda4773153f89d5a4ba345bf235d763d5fb9df615fa073e81730f808d25a8343bc151edb003a677da2cebab7984298d3b37d854cb8412d1032d0b5e7196d089f04b73b835346652420fb47a2e0e6230f89c9c8137acc2216180037fff5654e18aac5680ed4eb995e72aa09e76272a32ea1348c971ea7bde24d2277a614caab3be1770b905b6aa6ee79526992652b5613c2c61a05cad813043f6ec0afbb325ab034bdd9e11207c1a5aa3bf5e8e28a0ccde6328429755e472866d645c4d5139691182e601b17c9c7f54112e2048ca9331311e646524c4f39cc24756a1cc461f379342e1218b48117fffab2270f923ed671d6d004dfc6bdf96d81234a1c0fb31facc9a9a2c58d7efd463f9e30385756796a0a1df93eb5635bdcb487c3b447939d491745693d1e2faa676b85ee3f0134b878a03f36599216533184ced6f8391460c8a31a238a63c0086bf6b43b8895d26d93b32b46ae95e12b005e8c30a1cc3e6f26b4812da181d2ffff5444e1)]))| 18=>(4,1,7,T #[0x4a4cdaf56272e5af388fbcf93d99b8bdb7583e98363ec705c27d71ad2371b9ccfbeb03d7f1735cf08a991e9962369d512b2200c435a04753832d0f8240653b7df405462b9ea8f6a4ad7181cf5b27b014d742c443d04dc4c254808615fff461,0x501bbd2673dc544d18cc3a64f2e823073a41dde91d2f4ddbb1c60c07fcc2f7aab25f82fbbc8661c49c2b820243aeeb4fc1dc33e0c7f421fd4b08d742c443d044c98dd642548617fff4a1,0x17088f376e75d3e78b7e8d43d63c0e9ee8baecc556d9d296ac1c44aba1459aae4e41f49f530933c54247382bb0cc34c5ff89ad8b007592a2d13374256ca7172a2d1165c0fa791c01b028055ea3ec2c443cdc4c9d642010615fff4e1,0x2387e54028a60112e5ca5c7365096af2d74ad23fea7e1dcf39b621da3512034638b8d56081082a2da6c0b3dc98620d32509c69f62dcc46ad43092b42c3d04dc4c9d6549b0615fff541])| 19=>(1,0,7,T #[0x80e80d89266960a08a4bfff])|_=>Z0),(fun| 16=>(1,4,7,T #[0x1c9b529c980b2f7be58745dbaf55fe1c08c900817401a55986b62d82eccaf1d1b30518d2d4a70c4730535a548ba848ee68d469c2605c5774833e304c81cc99f8bf51f4c200f45a5a4566d29d44a867c619e17c4787f41627c27a9b02850adfbf5a648380c4a1])| 17=>(15,3,7,V (fun _=>(0x2e0d2b87289b24b121561eae1ca417f8155312440ea30b36085b05bd02ff0000,0x19409cbdda4557993aad97e1e71ab1d4802c1911ab7a070b4f1402dd43def8ed8d64ef3961da7d60d68f7df6ab6dd3f30779b656ee66c704265e386938566e08e821fc6b89e4facea4122ffffa92c062a0c1063e55d12503656557b9e0703df31f66ff5a4adadba4effb646a6f25c059926618479f45ef5c08630b978281b6a3c1410cb3431c98fc9b7a088d9e439e372753b5ce75b653b381109882385e839be27a9c31816361f2ffffa91c062a0f0e64a3a94063a2c3131ea3cc14243fb6344e7ef9967dafb6e6476b6a39439ad3fb6b68a83a4f78f253b846e17c741ac092824b9b9b1e9d4008b2b47df9629d7f405e354be10134fd0a31b6aa88867863fb9a0603add91bca57ef14ad984d7f4f7b23703296fdc40215b8843387e8389e4face13a9050abf7eb4d01894366bd0f387014f0c42d2e3777df36d88e82ddd5a3d8a47a1ab7d7e2fdc536e9189db8a2452b36d8821e1eb3fcb9220033b432fbc1441987e218affe120c83361758ba25da816a497902671fadb2f3e351bcc2d85d081730de19c2f11c3f40c4f09d4b030a19fffd20e031287c840376cad0d157ca70b2a194be2446558c102f2697791267c689d7f6ab360df9d0a346cbc5875ef3747f8df2dc7b43d79101a4a1515180fb729bf19408cf70bc470fd07138df278d759c27520a193efd69a0312877e2d05eb99d4f254b62b782a0cb5becb3a6dd4b1ed76bfab039e067f152954e450c0bcbcfefad0187b8e8adea8b7a111c3f41cdf09d4e18da0164dfff5a480c46191ca6d798d583117899195d1a90f733c4d1910cfd0835e29b5bc322a8f2a749db0a9a37fea38c70cb24d7128e140344936a91d4a0647242c7eb225c587b386c4309ef3b6d226e2e828a3a683e355b2c8d001dd2168236ec3308cb7307c7d3b980b14f21940bccf950fc8617347143ae6d51088d5b717eea124bcfd2d2808893c284bc470fd0626cdf09d4c16da61877fff4a480c4618a0f7f06af74373cf60f3bb7fce1881c4677d4f6a77815e6b4faca84cda020f098294c19205cfdbe84c39b13edd9877f381d2c4b2efc528b992215ef1228131600e2387e839b09789e13016170c2a7ffad5c06230c2e6eb3e1ee908073c9799710ccba275c474dfe26cc2c80c5cc7b3ddd7a5992ff4894b50a4b35f459aa3eb64011797d2a6fb1fd938c7e9935b2284aafee26c1953b48c1377945943732190808812147f37d676942b11c0b1b4161877fff5495678019652c47b1c1e4a537728d5197936dd56dae45e0601544ba2dc10122234c55cc56d9c4ca371076378c58cce6174cbe1328ef405a8cf7c617ad658e15666986f53aaf11d5fac49a0281b8f3c28c4480e9d9f993e005778681a588cfb6e64c8074400cb9beb3b461688e058da0b0c37fffab4aa3c00c03e02718e02711b1c132cec06a508264d3eda95a8ce35ad285b16ebe6d5d56e692f8c05b2408b4769f75c06a77477a87cb404451d35e889ed32068b69a522f31f959fa8ab1998d1ad191943af5f1c1ef2db1cab7282263880a308dcdf59da540c470346b0b861bfffd5a949e0076560048ec65909f71008e0c21bdcddb9fd8da1d7e03a358a8b42f2b1dd809be24834130a19d55b19d08a157295aa8e4834e3db15330aec221f66af69866970a694b201009e51788a1787e259ba7b8460b0ca04003bfffa72ab1c00fc46619072600b58d92133b11f64307a5a79cf1caf5f5b6983399e1577913b7c1962d353231bad0cb7a50b34b60084ec769b3cf241dfb7f848c38269d044324c0b0a7b87e839b626856da81c30dfffea88ac7003bb31037e782c08ac732a5fb2b6b7c0e3c9b7d20a7cb07ca3d0548728fdd809449c77a73c5580bf3ce7b152e75aa4aa254b85f0e671bfb8e2166e1b3c4ce729870322c098e17a06239ba4fa9a35b4c30bd37fffaa2291c00c2e6eaa7154f5f5e3cb47fa39cc77334c1ce23a8e110f92ed78f8a8704455470d0f32957afe27f0236afa80969a5a0088114a925f6152702063f8dc953eedf1e3967b2760a5674fe0ce7ce4304c70bc4313cdb4546b0540e185ffff4e4523801)))| 18=>(16,2,7,V (fun _=>(0x3d853a1b367732d32ecc2af425d421911dd01a0a1644125e0ebb0b91082404090000,0x1b755e1f2d7b33f2c718d87844ab5cff0471ce8438e3407024e55809d0f391e2302f643612ac2798d4dd95784a3c87eec697d439f9cf9de11ba2e752b967bc984074a009fdbeba411283ac33517412c135e0b016f7386596e7c4e0870b87d066f1393d66a66d0c0f97fffc062a0df8131529cfea9e2eec00c9386561fd8b29bf8290c1cc3bb42507220f8307192b44127342eb5c14b0680fd73df41d825035ace4915f80a3f47ccbde568a65eedc6278c3c62bdb4ddb52980108976e0b064be1e5c8e64ae194db5020641187a314672db0b87d066c3f89c9eb3533686177ffc062a0e91880105e117b38568189a0c99c103bdc552ea78c1372a8cd9828e08e9d6180605a28f069a77fd9487bc1db98142ebc86bd5b5aeab12375667ce75ce4e16d6206d1cb50918d9b52a647297344a74b169c8d6cae26d5646e3ea2286f92805c900672db0b88c3e6c3989c9eb3090c81177ffc06270d8e8d1f48254b4b6bd8698793a88adce7c6ad7047c0e57bd482d2e0dfb39c63e02bca9eaee6fd08878f49bccc4395802b3a23c5e44c643e1a29980b3c264537101a2e5e5913d3c8a88cd4e0a7b8600ea0d21d78ee165833e4c61c79d4389384bcd6891ad91fb52565bb276de512ac286f110cc3e831393d6613521433fff80c4a1e48ee1c0e15edec78515787ce7aacf0e501fd6752eaa0d3b3505332713f107444ec848a141efd59097bb74d10434df7ef57f7a3c61960cfe3542adb86d6ad407cd1cbd21b57a7de73fe18853275953e7197c233f63b516a92e70b4f655cb5c8df1eaf385581420b6c2e230fa00a627271bd6613530c32fff80c4a1ca3b3d1a797e62cd67ea66a353356f084ed34ef37377ed5140795febaed611aa3b2f858cc136ae82d5597eea82b178a1a823d63ae3fd64bf7d1874b04136991fc183fc49592828876d8bf82654160a1e0ec760c5a29f803c1cc88aaf80d58263c68ab11f8bd1070784a4bcc4bc586f7cb3268702bc1ec0912c84a06d40f840869a2ae53acc5ae7df40719552e85e564666c4e171187d066f1384d482e030c2ffff80c461d6b3afc09fb5604730961fd64d94691c3bad2562ec60355aa9d30a9de3f7726ed9e6a73f32623472363bbf1a71fd0ad1cf8ffca57485a45f4cf16ce0ffc740fd3820de58432729dbf42e246cbca4f30ec950505e4ed9eef58ae3304f6c413f559658c29ddab43c0cc54b3f1351c9a3ae2fa2de25a9ae3b6e171187d066f1384d4c061855fff0188c316a6a31cbfd97e6756f3e84f231bee3ab51dcb9e6ead492cc1f405dacaa830054d0589479b02d25178fc62eea0ea0353d622c0820051eb34d51eba35733594e1e694905779b6cbef6138ec63cd6bbd8316ea7c3cfedd6bb546d306ba9237aed875ee45b39df38a48f87d066f59b4c0ad90b0c27fff56a801ed9797b13689c49660e1d2ce839cff361b06e52e48758a3694e6b72165812e8367b132b8bedd1b7892edc6706dfb77dfd6f120c9ae9365dadd5ba5d5409cc55cf343874fdf7b6c6d594f0b0327bc2855aaaf72993a787a58fbec6ddaf1e8002014f35775c4b29e0fcde272784db217598d41430bfffd59e0062b1bb7fc69924367baab7b9baa87a8305efc2cbc6807e62696b1bed4a8ca0996d72981039989ead66538ddf71618c87becc865957b6d6bb10c6f6665460461585fd78e718a02660b3029d5d5e4f9d5e09218a8388e6bdc15a6258bfef69669216f8385e592dae892a985c3e6f59b4c0ad9050c27fff5478019548e3056c331624be18fcbf8d7b285966943a34b5579fb7c66202e0cf5b8cb0632ee5eead1dc23a0a6bb44a6b74a2c00e3f491e886276e5afff7021b379681817cd36412a4b56880bca75ccd211fd160c8cab68e158d0a6f50aa4c4c84d48f1691272fc5639e1377e00bc2323e17119bd66d3028d414309fffd49e006ecf77bb9cf5b73867ecef274de5246d2c4709940fa894536a16c251ba83da51b3bb839ef48054f523fb101b06613563032dea54b650279defe156e29c3706afd5a3862ccdf611ea15fb477c18d13d80d13bfd7ce2b9b9a20d376b7849ed626e40a23c8b85c461f59b44de1302828617fffa72c00ca76a6249b582fef9c943857c9e34ebfe2e97e98cebbfb754a3cbadd27b6fd68b75cb298e6a87b267fa10d9f77e01f467fa361bc7f7f7a536831d7976e19aa24fe88877bc88dcb1d4f141ec560a6d5f8a3445ce5987b419bc4e136d8d42a061857ffeac7003024aec3763643d1b659d967250f52a7d5cf6cf49fc585ed1e34094e49f11e836a7c034ba73a22e76aac67fed9c3d428329a024fc549c79c3b7434a772bbc83ed2fd68b5671acd4911fa7998ec5cc5bdab1e19bfc36f98b80a36b00c2543188cde275385c1235030c2bfff5238019bb0def538532b521fb32611d9fccd2673ff9547607504db01f3c3729b7322d806dcb09f2ad7df6b0731f482b71a51d72301aa7b3783a72b659f6ddbab53b5eb32c01d620bafeb35daf818fd7baced982edcb9cebbdcbae484f98f636f4120577f372b2a60f20a043f887d5e23cf69ac7aaa4e230f89d4e153784c12061857ffe947003b4e5e01412152a0c45f76a6a93417c915096b896fc4ca122bda0aa062347bf15038c1d030b89b2a431ba6fec27c5e30acf08687bbbbc0e037bad8af7c0c05d89ac0be22a0ff824dee8e7f621491ebb591a6da9c606f7a3dffe3d36625a0da205477834c1fca2e2ac44eef9ce35d36b0e71187cdea70a89c2609030c2ffff483801)))| 19=>(1,1,7,T #[0x331cf902ba278069283df9a9d2900c2e5d3dc699d63f0c43b45a825f29c3ccd408f8fc443cdc4c9d4c2d642410617fff801])|_=>Z0),(fun| 16=>S 3 11 4 4 4 51 0x4de06070101210000281a0200| 17=>S 19 99 5 4 7 0x44097140c8800008081060090d2200285 0x99bd43002610000084268cb800050a28cc170031215400b6601b6f9386a03064000491603c000021b55ae30000000091000130021603656000000034a0c21100023000000000083000000058e80706228c37304320b48d7820c00a347492518018820087705641aeaf10aa2469208cbc35c2c0e885f80100a2ec00| 18=>S 17 104 5 4 7 0xa043b00000182000c0820400104 0x83400000000006d000004b20a00000000130008c00948bb01400000002220000080e8a031890180083c4609426b4005000000026c8911291d948bfa9804000020b441470010abb607e04510000079800000000006a002820000083aa40b68e002120548d003a50000029508204008b2080840063610b5616d0aea826270117004504| 19=>S 7 44 3 4 6 0x14045000303 0x2c2900009400000000bb8c0000a3420069000001009be124c1338a8413bc91518bca02b4002b8300001c21|_=>N0),(fun| 17=>S 1 1 1 4 1 0 1| 18=>S 5 27 4 4 5 9670880 0x85018000086000840e0100016ee0001e1308024141a030786a0200| 19=>S 4 27 5 4 5 1033 0x7000840000281800000010240021c0000000216880020480e05000828200020c00|_=>N0),(fun| 17=>S 6 40 4 4 6 4329308289 0x61c0022004240000006cd2f0c0000385b7078014c00b20000112c2dd000001fca503f2d3c721c96000003cb5| 18=>S 7 32 5 4 5 0x38e1480c3 0x3640000b00148395288380060d6908ee200000da00c30800c1841b120a71d08c9c0dc941003e21| 19=>S 2 13 1 4 4 0 0x5d19610f50000131c0|_=>N0)⟩
def fms:=fO (uf bk)
lemma gm:uo bk (B k8)=H:=by decide +kernel
lemma sT:ua fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19]=H:=by decide +kernel
lemma t8:uK fms ct bk 18 0 16=H:=by decide +kernel
lemma aT:∀ k ≤ 19,ul fms ct bk k:=by
 intro k hk;by_cases h18:k=18;. exact h18▸uM t8 rfl
 exact uc sT k (by simp;omega)
lemma sF:ub fms ct bk [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,19]=H:=by decide +kernel
lemma f6:uL fms ct bk 16 0 27=H:=by decide +kernel
lemma f7:uL fms ct bk 17 0 22=H:=by decide +kernel
lemma aF:∀ k ≤ 19,um fms ct bk k:=by
 intro k hk;by_cases h16:k=16;. exact h16▸uN f6 rfl
 by_cases h17:k=17;. exact h17▸uN f7 rfl
 exact ud sF k (by simp;omega)
end G3
lemma oneNotRoot:u2 graph 19 u3.toFinset:=ur (cores:=ct) (g:=G3.bk) (top:=19) (k:=19) (i:=0) cv (uR k8 h8) G3.gm G3.aT G3.aF (Nat.le_refl _) (by decide +kernel)
end OneNot
lemma edge_iff (x:B->Y):Engine.edge x=H↔Mono.G12Edge x:=by
 constructor
 . intro h;simp[Engine.edge] at h
   rcases h with (((((((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)<;>exact⟨_,_,by decide,h.1,h.2⟩
 . rintro⟨u,v,huv,hu,hv⟩;let y (k:Nat):=x (Fin.ofNat 12 k);have hy (a:B)(ha:x a=H):y a.val=H:=(by simpa[y] using ha)
   replace hu:=hy u hu;replace hv:=hy v hv
   change (y 0&&y 7)||(y 0&&y 11)||(y 1&&y 6)||(y 1&&y 10)||(y 1&&y 11)||(y 2&&y 9)||(y 2&&y 10)||(y 3&&y 8)||(y 3&&y 9)||(y 3&&y 11)||(y 4&&y 7)||(y 4&&y 8)||(y 4&&y 10)||(y 5&&y 6)||(y 5&&y 7)||(y 5&&y 9)=H
   simp only[Mono.qb,Ab,List.not_mem_nil,or_false,Prod.mk.injEq] at huv
   rcases huv with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩<;>(rw[a] at hu;rw[b] at hv;simp[hu,hv])
lemma main:¬PEqualNP.MetaComplexity.HasCircuitSize 12 Engine.edge 20:=
 Engine.threeWaySplit (fun C m s c=>Mono.g12_lb_21 C m s fun x=>by rw[c x,edge_iff]) OneNot.oneNotRoot FreeInv.signedRoot
end PEqualNP.Outside.L_meta_9750
theorem PEqualNP.Outside.L_meta_9750 : (¬ (PEqualNP.MetaComplexity.HasCircuitSize 12 (fun x : Fin 12 → Bool => (x 0 && x 7) || (x 0 && x 11) || (x 1 && x 6) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 9) || (x 2 && x 10) || (x 3 && x 8) || (x 3 && x 9) || (x 3 && x 11) || (x 4 && x 7) || (x 4 && x 8) || (x 4 && x 10) || (x 5 && x 6) || (x 5 && x 7) || (x 5 && x 9)) 20)) := by
  exact PEqualNP.Outside.L_meta_9750.main
