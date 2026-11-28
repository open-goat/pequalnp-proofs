import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18015_aux
namespace Rup
abbrev qv:=Nat×Bool
abbrev q0:=List qv
def w3 (l:qv):qv:=(l.1,!l.2)
def w2 (v:Nat->Bool)(l:qv):Prop:=v l.1=l.2
def Holds (v:Nat->Bool)(c:q0):Prop:=∃l∈c,w2 v l
lemma qs (v:Nat->Bool)(l:qv):w2 v (w3 l)↔¬w2 v l:=by simp only[w2,w3];cases v l.1<;>cases l.2<;>decide
def q2 (v:Nat->Bool)(a:Nat->q0)(n:Nat):Prop:=∀i,i<n->Holds v (a i)
def w0:Nat:=0x8a14b431116b5a84294a4a92652949524c5420a8010c652108529882108f4a5295294a7ad4c4210e74108428cb34624328d15ad6f495054290e7b95262a4c528c96a544220e5239487316b5a10a518c4
def qz:Nat:=0xfe45f1534603d5b078da6563020b
def qx (t:Nat):=(w0>>>(5*t))&&&31
def qw (i:Nat):=(qz>>>(7*i))&&&127
def qh (b c a:Nat):=if (a&&&1)==1 then let d:=qx b;if (a&&&2)==0 then (b,c+1+((a>>>2)&&&15),a>>>6) else if (a&&&4)==0 then (b,c+17+((a>>>3)&&&255),a>>>11) else (b,(a>>>3)&&&((1<<<d)-1),a>>>(3+d)) else if (a&&&2)==0 then let t:=qw ((a>>>2)&&&15);let d:=qx t;(t,(a>>>6)&&&((1<<<d)-1),a>>>(6+d)) else let t:=(a>>>2)&&&127;let d:=qx t;(t,(a>>>9)&&&((1<<<d)-1),a>>>(9+d))
def fN {α} (x:Nat)(k:Nat->α):α:=match x with|0=>k 0|n+1=>k (n+1)
lemma uI {α} (x:Nat)(k:Nat->α):fN x k=k x:=by cases x<;>rfl
def B3 (w:Nat):Nat->Nat×Nat×Nat
 | 0=>qh 128 0 w
 | k+1=>let s:=B3 w k;qh s.1 s.2.1 s.2.2
def qg (k w:Nat):=let s:=B3 w k;s.1|||(s.2.1<<<7)
def AC (a:Nat->Nat)(i:Nat):=fN (a (i / 16)) (qg (i % 16))
def q3 (w:Nat):Nat->Nat->Nat
 | 0,b=>b
 | k+1,b=>if (b&&&1)==0 then q3 w k (b>>>5) else if (b&&&2)==0 then q3 w k (b>>>11) else q3 w k (b>>>(2+w))
def q8 (w b:Nat):Nat->Nat
 | 0=>b
 | r+1=>let x:=q8 w b r;let e:=x&&&15;let f:=if e<15 then e else (x>>>4)&&&255;let b1:=if e<15 then x>>>4 else x>>>12;match f with|0=>b1|c+1=>q3 w c (b1>>>w)
def q9 (w m:Nat):Nat->Nat->Nat->q0
 | 0,_,_=>[]
 | k+1,v,b=>let x:=if (b&&&1)==0 then v+1+((b>>>1)&&&15) else if (b&&&2)==0 then v+17+((b>>>2)&&&511) else (b>>>2)&&&m;let t:=if (b&&&1)==0 then b>>>5 else if (b&&&2)==0 then b>>>11 else b>>>(2+w);(x>>>1,(x&&&1)==1)::q9 w m k x t
def qq (b a:Nat):q0:=let e:=a&&&15;let f:=if e<15 then e else (a>>>4)&&&255;let h:=if e<15 then a>>>4 else a>>>12;match f with|0=>[]|c+1=>let d:=(1<<<b)-1;let g:=h&&&d;(g>>>1,(g&&&1)==1)::q9 b d c g (h>>>b)
def gdc (a B:Nat)(b:Nat->Nat)(d:Nat):q0:=fN (b (d / B)) λ w=>qq a (q8 a w (d % B))
def qp (w n a:Nat):=let b:=w-1;let m:=(1<<<w)-n;let v:=a&&&((1<<<b)-1);if v<m then (v,a>>>b) else ((v<<<1)+((a>>>b)&&&1)-m,a>>>w)
def qj (w n b a:Nat):=if (a&&&1)==1 then qp w n (a>>>1) else if (a&&&2)==2 then (b+1,a>>>2) else if (a&&&4)==0 then (b+2+((a>>>3)&&&7),a>>>6) else (n-1-((a>>>3)&&&7),a>>>6)
def qr (a:Nat):=if (a&&&1)==0 then ((a>>>1)&&&7,a>>>4) else if (a&&&2)==0 then (8+((a>>>2)&&&15),a>>>6) else ((a>>>2)&&&255,a>>>10)
def AY (a:Nat->q0)(c:Nat->Nat)(b:Nat->q0)(n i:Nat):q0:=fN i λ i=>if Nat.blt i n then fN (c i) a else fN (i-n) b
def q1 (e:Nat->Bool)(w:Nat):Nat->Bool
 | 0=>true
 | m+1=>e (qg m w)&&q1 e w m
lemma q7 {d:Nat->Bool}{w m:Nat}(h:q1 d w m=true):∀k,k<m->d (qg k w)=true:=by induction m with|zero=>{intro _ e;omega}|succ m ih=>{simp only[q1,Bool.and_eq_true] at h;intro k e;rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 e) with f|rfl;{exact ih h.2 k f};{exact h.1}}
def q4 (e:Nat->Bool) (f:Nat->Nat):Nat->Bool
 | 0=>true
 | q+1=>fN (f q) (λ w=>q1 e w 16)&&q4 e f q
lemma qc {a:Nat->Bool}{c:Nat->Nat}{q:Nat}(h:q4 a c q=true):∀b,b<q->q1 a (c b) 16=true:=by induction q with|zero=>{intro _ d;omega}|succ q ih=>{simp only[q4,uI,Bool.and_eq_true] at h;intro b d;exact(Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 d)).elim (ih h.2 b) (λ e=>e▸h.1)}
def wD (a:Nat->Bool)(b:Nat->Nat)(n:Nat):=fN (b (n / 16)) (λ w=>q1 a w (n % 16))&&q4 a b (n / 16)
lemma qk {a:Nat->Bool}{b:Nat->Nat}{n:Nat}(h:wD a b n=true):∀i,i<n->a (AC b i)=true:=by simp only[wD,uI,Bool.and_eq_true] at h;intro i f;simp only[AC,uI];by_cases e:i / 16<n / 16;{exact q7 (qc h.2 _ e) _ (Nat.mod_lt i (by decide))};{have d:i / 16=n / 16:=by{omega};rw[d];exact q7 h.1 _ (by omega)}
lemma Dq {v:Nat->Bool}{b:Nat->q0}{g:Nat->Bool}{f:Nat->Nat}{e:Nat->q0}{n:Nat}(a:∀c,g c=true->Holds v (b c))(d:wD g f n=true):q2 v (AY b (AC f) e n) n:=by intro i h;simp only[AY,uI,Nat.blt_eq,h,ite_true];exact a _ (qk d i h)
def ep0N (e:Nat):=[0,0,1,1,2,2,3,3,4,4,5,5,6,7].getD e 0
def ep1N (gi:Fin 4)(e:Nat):=(match gi.1 with|0=>[3,7,4,9,5,6,7,9,7,8,6,9,8,8]|1=>[8,9,4,9,5,6,7,9,7,8,6,9,8,8]|2=>[8,9,3,7,5,6,7,9,7,8,6,9,8,8]|_=>[8,9,3,7,4,9,7,9,7,8,6,9,8,8]).getD e 0
def epN (gi:Fin 4)(s e:Nat):=if s==0 then ep0N e else ep1N gi e
def nGN (gi:Fin 4)(x:Nat):=(match gi.1 with|0=>[136,528,96,641,386,580,292,281,208,42]|1=>[768,528,96,640,386,580,292,280,209,43]|2=>[768,136,96,642,384,580,292,282,209,41]|_=>[768,136,528,642,388,576,288,282,209,45]).getD x 0
def adjB (gi:Fin 4)(x y:Nat):=(nGN gi x).testBit y
def nbrsN (gi:Fin 4)(x:Nat):List Nat:=(match gi.1 with|0=>[[3,7],[4,9],[5,6],[0,7,9],[1,7,8],[2,6,9],[2,5,8],[0,3,4,8],[4,6,7],[1,3,5]]|1=>[[8,9],[4,9],[5,6],[7,9],[1,7,8],[2,6,9],[2,5,8],[3,4,8],[0,4,6,7],[0,1,3,5]]|2=>[[8,9],[3,7],[5,6],[1,7,9],[7,8],[2,6,9],[2,5,8],[1,3,4,8],[0,4,6,7],[0,3,5]]|_=>[[8,9],[3,7],[4,9],[1,7,9],[2,7,8],[6,9],[5,8],[1,3,4,8],[0,4,6,7],[0,2,3,5]]).getD x []
def aMk (gi:Fin 4)(a:Nat):=(match gi.1 with|0=>[28,49,56,67,74,88,134,162,194,263,270,291,298,533,593,773]|1=>[15,29,43,57,75,89,135,163,195,270,298,532,592,644,704,772]|2=>[23,29,51,57,83,89,133,161,193,268,290,296,534,594,644,774]|_=>[39,45,51,57,71,77,83,89,165,197,294,300,594,704,770,770]).getD a 0
def Ba (gi:Fin 4)(a:Nat):=(match gi.1 with|0=>[0x150,0x501,0x540,0x1005,0x1044,0x1140,0x4014,0x4404,0x5004,0x10015,0x10054,0x10405,0x10444,0x40111,0x41101,0x50011]|1=>[0x55,0x151,0x445,0x541,0x1045,0x1141,0x4015,0x4405,0x5005,0x10054,0x10444,0x40110,0x41100,0x44010,0x45000,0x50010]|2=>[0x115,0x151,0x505,0x541,0x1105,0x1141,0x4011,0x4401,0x5001,0x10050,0x10404,0x10440,0x40114,0x41104,0x44010,0x50014]|_=>[0x415,0x451,0x505,0x541,0x1015,0x1051,0x1105,0x1141,0x4411,0x5011,0x10414,0x10450,0x41104,0x45000,0x50004,0x50004]).getD a 0
def A9 (gi:Fin 4)(a:Nat):=(match gi.1 with|0=>[0x2a0,0xa02,0xa80,0x200a,0x2088,0x2280,0x8028,0x8808,0xa008,0x2002a,0x200a8,0x2080a,0x20888,0x80222,0x82202,0xa0022]|1=>[0xaa,0x2a2,0x88a,0xa82,0x208a,0x2282,0x802a,0x880a,0xa00a,0x200a8,0x20888,0x80220,0x82200,0x88020,0x8a000,0xa0020]|2=>[0x22a,0x2a2,0xa0a,0xa82,0x220a,0x2282,0x8022,0x8802,0xa002,0x200a0,0x20808,0x20880,0x80228,0x82208,0x88020,0xa0028]|_=>[0x82a,0x8a2,0xa0a,0xa82,0x202a,0x20a2,0x220a,0x2282,0x8822,0xa022,0x20828,0x208a0,0x82208,0x8a000,0xa0008,0xa0008]).getD a 0
def AX (gi:Fin 4)(x:Nat):=(match gi.1 with|0=>[0x4040,0x40100,0x1400,0x44001,0x14004,0x41010,0x10410,0x10141,0x5100,0x444]|1=>[0x50000,0x40100,0x1400,0x44000,0x14004,0x41010,0x10410,0x10140,0x5101,0x445]|2=>[0x50000,0x4040,0x1400,0x44004,0x14000,0x41010,0x10410,0x10144,0x5101,0x441]|_=>[0x50000,0x4040,0x40100,0x44004,0x14010,0x41000,0x10400,0x10144,0x5101,0x451]).getD x 0
def AW (gi:Fin 4)(x:Nat):=(match gi.1 with|0=>[0x8080,0x80200,0x2800,0x88002,0x28008,0x82020,0x20820,0x20282,0xa200,0x888]|1=>[0xa0000,0x80200,0x2800,0x88000,0x28008,0x82020,0x20820,0x20280,0xa202,0x88a]|2=>[0xa0000,0x8080,0x2800,0x88008,0x28000,0x82020,0x20820,0x20288,0xa202,0x882]|_=>[0xa0000,0x8080,0x80200,0x88008,0x28020,0x82000,0x20800,0x20288,0xa202,0x8a2]).getD x 0
def qd (gi:Fin 4)(x y:Nat):Nat->Nat×Nat
| 0=>(0,0)
| i+1=>if ep0N i==x&&ep1N gi i==y then (i,0) else if ep1N gi i==x&&ep0N i==y then (i,1) else qd gi x y i
def eIx (gi:Fin 4)(x y:Nat):=qd gi x y 14
def kB (I x:Nat):=I.testBit x
def kk (k I x:Nat):=if kB I x then 1 else 2+k
def iNN (gi:Fin 4)(I x:Nat):List Nat:=(nbrsN gi x).filter (kB I)
def eNN (gi:Fin 4)(I x:Nat):List Nat:=(nbrsN gi x).filter (λ y=>!(kB I y))
def xV (m:Nat):=(m&&&1)+((m>>>1)&&&1)+((m>>>2)&&&1)
def vR (s:Nat):=(s / 5,s % 5)
def kI (x j:Nat):Nat:=x*5+j
def kE (x j c:Nat):Nat:=50+(x*5+j)*10+c
def kD (x j c:Nat):Nat:=550+(x*5+j)*10+c
def kQ (t x:Nat):Nat:=1050+t*10+x
def vC (x y:Nat):Nat:=1080+(min x y)*10+(max x y)
def zG (t x y:Nat):Nat:=1180+(t*10+x)*10+y
def AD (t x:Nat):Nat:=1480+t*10+x
def vK (x:Nat):Nat:=1500+x
def xQ (t x j:Nat):Nat:=1510+(t*10+x)*5+j
def kN (s e x:Nat):Nat:=1660+(s*14+e)*10+x
def ur (s e x j:Nat):Nat:=1940+((s*14+e)*10+x)*5+j
def uO (x j:Nat):Nat:=3340+x*5+j
def wW (x j:Nat):Nat:=3390+x*5+j
def yN (b a:Nat):Nat:=3440+b*14+a
def yO (b a:Nat):Nat:=3636+b*14+a
def uK (b a:Nat):Nat:=3832+(min b a)*14+(max b a)
def ux (b a:Nat):Nat:=4028+b*14+a
def uP (e x j:Nat):Nat:=4224+(e*10+x)*5+j
def Cj (e:Nat):Nat:=4924+e
def yK (e b a:Nat):Nat:=4938+(e*5+b)*5+a
def zJ (e x j:Nat):Nat:=5288+(e*10+x)*5+j
def xR (e x j:Nat):Nat:=5988+(e*10+x)*5+j
def zD (e:Nat):Nat:=6688+e
def wM (e z:Nat):Nat:=6716+e*10+z
def yM (e z l:Nat):Nat:=6856+(e*10+z)*5+l
def zH (a b:Nat):Nat:=7742+a*14+b
def zI (x a j:Nat):Nat:=7998+(x*16+a)*5+j
def wj (a l:Nat):Nat:=8798+a*5+l
def vA (a b:Nat):Nat:=9118+a*14+b
def zE (a z l:Nat):Nat:=10014+(a*10+z)*5+l
def yJ (x j y l:Nat):Nat:=11230+((x*5+j)*10+y)*5+l
def yL (x j y l:Nat):Nat:=13730+((x*5+j)*10+y)*5+l
def zF (i y a l:Nat):Nat:=16230+((i*10+y)*3+a)*5+l
def uw (k a x:Nat):q0:=(if 0<k&&a.testBit 0 then [(kQ 0 x,true)] else [])++(if 1<k&&a.testBit 1 then [(kQ 1 x,true)] else [])++(if 2<k&&a.testBit 2 then [(kQ 2 x,true)] else [])
def wq (k I u v a b:Nat)(f:Nat->Nat->qv):q0:=(if u != a&&u != b then (List.range (kk k I u)).map (f u) else [])++(if v != a&&v != b then (List.range (kk k I v)).map (f v) else [])
def yA (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&15,(v>>>8)&&&15)
abbrev qY:=yA
def vTr (gi:Fin 4)(b:List Nat)(a:Nat):=a<b.length&&let t:=yA b a;t.1<14&&t.2.1<10&&t.2.2<10&&!adjB gi t.2.1 t.2.2
def vCx (gi:Fin 4)(d b:List Nat)(a:Nat):=a<b.length&&let c:=qY b a;vTr gi d c.1&&c.2.1<14&&c.2.2<10
def uZ (b:List Nat)(a:Nat):=let v:=b.getD a 0;(v&&&15,(v>>>4)&&&16383,(v>>>18)&&&1023)
def yR (b:List Nat)(a:Nat):=a<b.length&&a<6&&let u:=uZ b a;u.1<14&&u.2.1.testBit u.1
namespace R1
abbrev P (x:Nat):qv:=(x,true)
abbrev M (x:Nat):qv:=(x,false)
abbrev G (k I:Nat)(s:Nat×Nat):Bool:=s.1<10&&s.2<kk k I s.1
abbrev C a b:=[M a,P b]
abbrev W a b:=[M a,M b]
abbrev K a b c:=[M a,M b,P c]
abbrev p2 a b c:=[M a,P b,P c]
abbrev L:=vR
abbrev N:=List.range
abbrev B:=kB
abbrev D:=kk
abbrev F:=kI
abbrev E:=kD
abbrev O:=yA
abbrev R:=kE
abbrev S:=kQ
abbrev V:=iNN
abbrev U:=ep1N
abbrev A:=ep0N
abbrev H:=uK
abbrev Q:=ur
abbrev T:=qY
abbrev X:=nbrsN
abbrev J:=kN
abbrev z3:=uP
abbrev z4:=vTr
abbrev z5:=vC
abbrev z6:=xR
abbrev z9:=wq
abbrev za:=wM
abbrev zb:=Cj
abbrev zc:=vCx
abbrev zd:=yK
abbrev ze:=zF
abbrev zf:=uO
abbrev zg:=eNN
abbrev zh:=aMk
end R1
section B0
open R1
variable (gi:Fin 4)
def ex0 (k I g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let e:=L (r&&&63);let f:=e.1;let h:=e.2;let o:=L (c 3 63);let p:=o.1;let q:=o.2;let s:=D k I;let u:=r&&&15;let v:=r&&&7;let w:=c 6 15;let z:=c 4 15;let Y:=c 3 15;match g with| 4=>M (F u (2+(c 4 7)))::uw k (c 7 7) u| 7=>K (S v Y) (S v (c 7 15)) (z5 Y (c 7 15))| 11=>[M (z5 u z),M (F u (c 11 7)),P (R u (c 8 7) z),P (R u (c 11 7) z)]++(N k).map (λ t=>P (zG t u z))| 12=>(N (s u)).map (λ j=>P (zI u z j))| 15=>C (S u 9) (S (u+1) 9)| 16=>let b:=(c 4 1)==1;[(S u 9,b),(S (u+1) 9,b),P (AD u 9)]| 17=>K (AD v (Y+1)) (S v Y) (S (v+1) Y)| 18=>let b:=(c 7 1)==1;[M (AD v (Y+1)),(S v Y,b),(S (v+1) Y,b),P (AD v Y)]| 21=>M (vK u)::M (F u (1+(c 4 7)))::uw k (c 7 7) u| 24=>M (S v p)::P (vK p)::((N (s p)).filter (λ j=>j != q)).map (λ j=>P (xQ v p j))| 26=>[M (F f h),M (R f h w),M (E f h w),P (vK w)]| 27=>M (F f h)::M (R f h w)::P (E f h w)::(N (s w)).map (λ l=>P (yJ f h w l))| 30=>M (F f h)::M (E f h w)::P (R f h w)::(N (s w)).map (λ l=>P (yL f h w l))| _=>[]
def ex1 (k I g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=L (r&&&63);let m:=h.1;let n:=h.2;let o:=L (f 6 63);let p:=o.1;let t:=o.2;let u:=L (f 5 63);let v:=u.1;let w:=u.2;let z:=r&&&15;let Y:=f 4 15;let Z:=f 1 15;match g with| 36=>[M (F z (f 8 7)),M (F z (f 11 7)),M (E z (f 8 7) Y),M (E z (f 11 7) Y)]| 38=>M (E z 0 Y)::(N (D k I (((X gi) z).getD (f 8 3) 0))).map (λ l=>P (ze z Y (f 8 3) l))| 41=>K (J 0 z Y) (J 1 z Y) (vK Y)| 43=>let s:=r&&&1;let x:=f 5 15;M (J s Z x)::P (J (1-s) Z x)::(N (D k I x)).map (λ j=>P (Q s Z x j))| 44=>W (Q (r&&&1) Z (f 5 15) (f 9 7)) (Q (r&&&1) Z (f 5 15) (f 12 7))| 48=>let s:=r&&&1;let y:=f 11 15;let b:=(f 16 1)==1;[M (Q s Z v w),((if ((f 15 1)==1) then E v w y else R v w y),b),((J (if ((f 15 1)==1) then 1-s else s) Z y),!b)]| 53=>let e:=f 13 15;K (yJ m n p t) (Q (f 12 1) e p t) (Q (f 12 1) e m n)| 54=>let e:=f 13 15;K (yL m n p t) (Q (f 12 1) e p t) (Q (1-(f 12 1)) e m n)| 61=>[M (H z Y),P (yN z Y),P (yO z Y)]| 62=>let q:=L (f 8 63);[M (Q (f 14 1) z q.1 q.2),M (Q (f 15 1) Y q.1 q.2),((if (f 14 1)==(f 15 1) then yN z Y else yO z Y),true)]| _=>[]
def ex2 (k I _m g r:Nat):q0:=let c n m:=(r>>>n)&&&m;let d:=L (c 4 63);let f:=d.1;let h:=d.2;let i:=r&&&15;let j:=c 4 15;match g with| 66=>[P (H i j),P (ux i j),P (ux j i)]| 68=>K (ux i j) (ux j (c 8 15)) (ux i (c 8 15))| 71=>K (z3 i f h) (Q (c 10 1) (c 11 15) f h) (ux i (c 11 15))| 81=>M (zb i)::(N (D k I (A i))).flatMap λ b=>(N (D k I ((U gi) i))).map λ e=>P (zd i b e)| 82=>P (zD i)::(N 10).map (λ z=>P (za i z))| 84=>[M (H i j),M (zD i),P (zD j)]| 85=>let z:=c 8 15;[M (H i j),M (za i z),P (za j z)]| 87=>p2 (yM i f h) (E f h (A i)) (E f h ((U gi) i))| 88=>M (za i j)::P (zb i)::(N (D k I j)).map (λ l=>P (yM i j l))| _=>[]
def ex3 (k I:Nat)(t0 c0 x1:List Nat)(g r:Nat):q0:=let f n m:=(r>>>n)&&&m;let h:=D k I;let m:=z9 k I;let n:=O t0;let o:=T c0;let q:=r&&&15;let u:=r&&&63;let v:=f 4 15;let w:=f 6 15;match g with| 97=>let a:=(f 4 1)==1;let t:=n q;K (J 0 t.1 (if a then t.2.2 else t.2.1)) (J 1 t.1 (if a then t.2.1 else t.2.2)) (zH q t.1)| 98=>let t:=n q;[M (zH q v),M (zD v),P (zb t.1)]++m (A t.1) ((U gi) t.1) t.2.1 t.2.2 (λ z l=>P (z6 v z l))| 101=>let c:=o u;let a:=c.2.1;let b:=c.2.2;let t:=n c.1;[M (zH c.1 a),M (za a b)]++m (A t.1) ((U gi) t.1) t.2.1 t.2.2 (λ z l=>P (z6 a z l))++[P (zb t.1)]++(if b != t.2.1&&b != t.2.2 then [P (vK b)] else [])++(N (h b)).flatMap (λ l=>[P (wj u l),P (zJ a b l)])++((N 14).filter (λ e=>e != a)).map (λ e=>P (vA u e))| 106=>p2 (vA u w) (J 0 w (o u).2.2) (J 1 w (o u).2.2)| 108=>let a:=r&&&7;let um:=uZ x1 a;let am:=um.2.1;let cm:=um.2.2;P (zb um.1)::((N 14).filter (λ e=>am.testBit e)).flatMap (λ e=>P (zD e)::((N 10).filter (λ z=>!(cm.testBit z))).map (λ z=>P (za e z)))++((N 10).filter (λ z=>cm.testBit z)).flatMap (λ z=>(N (h z)).flatMap (λ l=>P (zf z l)::P (zE a z l)::((N 10).filter (λ y=>cm.testBit y)).map (λ y=>P (E z l y))))| 110=>let a:=r&&&7;let am:=(uZ x1 a).2.1;let s:=L (f 3 63);M (zE a s.1 s.2)::((N 14).filter (λ e=>!(am.testBit e))).flatMap (λ e=>[P (Q 0 e s.1 s.2),P (Q 1 e s.1 s.2)])| 126=>M (z5 q v)::(N (h q)).map (λ j=>P (R q j v))++(N (h v)).map (λ l=>P (R v l q))| 127=>let p:=f 4 3;let a:=if p==2 then 1 else 0;let b:=if p==0 then 1 else 2;let y1:=f 6 15;let y2:=f 10 15;let j:=f 14 7;[P (vK q),M (S a q),M (S b q),M (S a y1),P (S b y1),M (S b y2),P (S a y2),M (F q j),P (xQ a q j),P (xQ b q j)]++(if 2<k then [P (F q 4)] else [])| _=>[]
def exS (k I b:Nat)(c d e:List Nat)(a:Nat):q0:=let f:=a&&&127;let r:=a>>>7;if f<64 then if f<32 then ex0 k I f r else ex1 gi k I f r else if f<96 then ex2 gi k I b f r else ex3 gi k I c d e f r
def en0 (k I g r:Nat):Bool:=let e n m:=(r>>>n)&&&m;let f:=L (r&&&63);let h:=f.1;let o:=L (e 3 63);let p:=o.1;let q:=D k I;let s:=G k I;let u:=B I;let v:=r&&&15;let w:=r&&&7;let z:=e 6 15;let N:=e 4 15;let Y:=e 3 15;match g with| 4=>v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&xV (e 7 7)==k-(e 4 7)| 7=>w < k&&Y < (e 7 15)&&(e 7 15)<10| 11=>v<10&&!u v&&N<10&&N != v&&(e 8 7) < (e 11 7)&&(e 11 7) < q v| 12=>v<10&&N<16&&!(((zh gi) N).testBit v)&&(((zh gi) N)&&&(nGN gi) v) != 0| 15=>v+1 < k| 16=>v+1 < k| 17=>w+1 < k&&Y<9| 18=>w+1 < k&&0 < Y&&Y<9| 21=>v<10&&!u v&&(e 4 7) < k&&(e 7 7)<(1<<<k)&&xV (e 7 7)==k-(e 4 7)| 24=>w < k&&p<10&&!u p&&o.2 < q p| 26=>s f&&z<10&&z != h| 27=>s f&&z<10&&z != h&&!u z| 30=>s f&&z<10&&z != h&&!u z| _=>false
def en1 (k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (r&&&63);let f:=c.1;let l:=L (b 6 63);let n:=l.1;let o:=L (b 5 63);let p:=D k I;let s:=G k I;let t:=B I;let u:=r&&&15;let v:=b 4 15;let z:=b 1 15;match g with| 36=>u<10&&!t u&&v<10&&t v&&(b 8 7) < (b 11 7)&&(b 11 7) < p u| 38=>m==1&&u<10&&t u&&v<10&&!t v&&!(adjB gi) u v&&(b 8 3)<3&&(b 8 3)<((X gi) u).length| 41=>u<14&&v<10| 43=>z<14&&(b 5 15)<10| 44=>z<14&&(b 5 15)<10&&(b 9 7) < (b 12 7)&&(b 12 7) < p (b 5 15)| 48=>z<14&&s o&&(b 11 15)<10| 53=>s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14| 54=>s c&&n<10&&n != f&&!t n&&l.2 < p n&&(b 13 15)<14| 61=>u < v&&v<14| 62=>u < v&&v<14&&s (L (b 8 63))| _=>false
def en2 (_gi:Fin 4)(k I m g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=L (b 4 63);let f:=G k I;let h:=r&&&15;let i:=b 4 15;match g with| 66=>h < i&&i<14| 68=>let e:=b 8 15;h<14&&i<14&&e<14&&h != i&&i != e&&h != e| 71=>h<14&&f c&&(b 11 15)<14&&(b 11 15) != h| 81=>h<14| 82=>m>0&&h<14| 84=>m>0&&h<14&&i<14&&h != i| 85=>m>0&&h<14&&i<14&&h != i&&(b 8 15)<10| 87=>m>0&&h<14&&f c| 88=>m>0&&h<14&&i<10| _=>false
def en3 (k I m _q:Nat)(t0 c0 x0:List Nat)(g r:Nat):Bool:=let b n m:=(r>>>n)&&&m;let c:=D k I;let d:=B I;let e:=(zc gi) t0 c0;let h:=(z4 gi) t0;let j:=r&&&15;let n:=b 4 15;let o:=r&&&63;let u:=b 6 15;match g with| 97=>m>0&&h j| 98=>m>0&&h j&&n<14| 101=>m>0&&e o| 106=>m>0&&e o&&u<14&&u != (T c0 o).2.1| 108=>m==1&&yR x0 (r&&&7)| 110=>m==1&&yR x0 (r&&&7)&&G k I (L (b 3 63))| 126=>j < n&&n<10&&!d j&&!d n| 127=>j<10&&!d j&&let p:=b 4 3;((p==0&&1<k)||(0<p&&p<3&&2<k))&&(b 6 15)<10&&(b 10 15)<10&&(b 14 7)<c j| _=>false
end B0
def enabled (gi:Fin 4)(k I a c:Nat)(d e f:List Nat)(b:Nat):Bool:=let g:=b&&&127;let r:=b>>>7;if g<64 then if g<32 then en0 gi k I g r else en1 gi k I a g r else if g<96 then en2 gi k I a g r else en3 gi k I a c d e f g r
abbrev expS:=exS
abbrev enS:=enabled

def uS:Nat:=0x55555
def uR:Nat:=0xAAAAA
def ye:Nat:=0xFFFFF
def qP (m:Nat):Nat:=
  let rec go:Nat->Nat->Nat
  | 0,a=>a
  | i+1,a=>go i (if m.testBit i then a.lor (Nat.shiftLeft 1 (Nat.mul 2 i)) else a)
  go 10 0
def qF (m:Nat):Nat:=(qP m).shiftLeft 1
def wZ (b:Nat):Nat:=((b.land uS).shiftLeft 1).lor ((b.shiftRight 1).land uS)
def qR (a v:Nat):Nat:=(a.shiftRight (Nat.mul 2 v)).land ye
def ug (a u v:Nat):Bool:=!(((qR a u).land (wZ (qR a v))).beq 0)
def gB (a b v:Nat)(p:Bool):Bool:=if v.blt 1940 then a.testBit ((Nat.mul 2 v).add p.toNat) else b.testBit ((Nat.mul 2 (v.sub 1940)).add p.toNat)
def zO (a b v:Nat)(p:Bool):Nat×Nat:=if v.blt 1940 then (a.lor (Nat.shiftLeft 1 ((Nat.mul 2 v).add p.toNat)),b) else (a,b.lor (Nat.shiftLeft 1 ((Nat.mul 2 (v.sub 1940)).add p.toNat)))
def vV (a v m:Nat):Option Nat:=if !(((qR a v).land (wZ m)).beq 0) then none else some (a.lor (m.shiftLeft (Nat.mul 2 v)))
structure OCtx where
  gi:Fin 4
  k:Nat
  I:Nat
  m:Nat
  t:List Nat
  c:List Nat
  x:List Nat
  ie:Nat
  io:Nat
def qU (gi:Fin 4)(k I m:Nat)(t c x:List Nat):OCtx:=fN (qP I) λ ie=>fN (qF I) λ io=>⟨gi,k,I,m,t,c,x,ie,io⟩
def qV (u:Nat):Nat:=Nat.shiftLeft 1 (u.div 10)
def BO (v:Nat):Nat:=if (!(v.blt 50)&&v.blt 1080)||(!(v.blt 1660)&&v.blt 1940) then Nat.shiftLeft 1 (v.div 10) else 0
def bM (u v:Nat):Nat:=(qV u).lor (qV v)
structure wQ where
  e0:List (Nat×Nat×Nat)
  m0:Nat
  e1:List (Nat×Nat×Nat)
  m1:Nat
  e2:List (Nat×Nat×Nat)
  m2:Nat
  e3:List (Nat×Nat×Nat)
  m3:Nat
  e4:List (Nat×Nat×Nat)
  m4:Nat
  e5:List (Nat×Nat×Nat)
  m5:Nat
  e6:List (Nat×Nat×Nat)
  m6:Nat
  e7:List (Nat×Nat×Nat)
  m7:Nat
def BI:wQ:=⟨[],0,[],0,[],0,[],0,[],0,[],0,[],0,[],0⟩
def ut (ps:List (Nat×Nat×Nat))(u v m:Nat):List (Nat×Nat×Nat):=if ps.any (λ p=>p.1.beq u&&p.2.1.beq v) then ps else (u,v,m)::ps
def kX (E:wQ)(u v:Nat):wQ:=
  let u':=if u.blt v then u else v;let v':=if u.blt v then v else u;let m:=bM u' v'
  match (u'.div 10).land 7 with
  | 0=>{E with e0:=ut E.e0 u' v' m,m0:=E.m0.lor m}
  | 1=>{E with e1:=ut E.e1 u' v' m,m1:=E.m1.lor m}
  | 2=>{E with e2:=ut E.e2 u' v' m,m2:=E.m2.lor m}
  | 3=>{E with e3:=ut E.e3 u' v' m,m3:=E.m3.lor m}
  | 4=>{E with e4:=ut E.e4 u' v' m,m4:=E.m4.lor m}
  | 5=>{E with e5:=ut E.e5 u' v' m,m5:=E.m5.lor m}
  | 6=>{E with e6:=ut E.e6 u' v' m,m6:=E.m6.lor m}
  | _=>{E with e7:=ut E.e7 u' v' m,m7:=E.m7.lor m}
def xM (ps:List (Nat×Nat×Nat))(im u v:Nat):List (Nat×Nat×Nat)×Nat:=let m:=bM u v;(ut ps u v m,im.lor m)
structure St where
  a:Nat
  b:Nat
  eqs:wQ
  imps:List (Nat×Nat×Nat)
  im:Nat
  dm:Nat
def uY (a x y:Nat):Nat->Bool
| 0=>false
| j+1=>a.testBit ((Nat.mul 2 (kE x j y)).add 1)||uY a x y j
def vP (a b e z:Nat):Nat->Bool
| 0=>false
| u+1=>(!(u.beq z)&&gB a b (wM e u) true)||vP a b e z u
def xw (a b u v:Nat):Bool:=u.blt 14&&v.blt 14&&!(u.beq v)&&(gB a b (ux u v) true||gB a b (ux v u) true)
def xX (a b u v:Nat):Bool:=u.blt 14&&v.blt 14&&!(u.beq v)&&(gB a b (uK u v) true||gB a b (ux v u) true)
def vJ (C:OCtx)(a b e x j:Nat):Bool:=gB a b (uP e x j) false||(e.blt 14&&x.blt 10&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||gB a b (ur 0 e x j) true||gB a b (ur 1 e x j) true))
def xB (C:OCtx)(a b x j:Nat):Bool:=gB a b (uO x j) false||(x.blt 10&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||!((((qR a (kD x j 0)).land uR).land (C.io.xor (C.io.land (Nat.shiftLeft 1 ((Nat.mul 2 x).add 1))))).beq 0)))
def xD (C:OCtx)(a b x j:Nat):Bool:=gB a b (wW x j) false||(x.blt 10&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||!(((qR a (kD x j 0)).land uR).beq 0)))
def zA (C:OCtx)(a b vr:Nat):Bool:=
  if vr.blt 50 then let x:=vr.div 5;let j:=vr.mod 5;x.blt 10&&j.blt (kk C.k C.I x)&&((!(j.beq 0)&&a.testBit (Nat.mul 2 (kI x (j.sub 1))))||a.testBit (Nat.mul 2 (kE x j x))||(j.beq ((1:Nat).add C.k)&&!(kB C.I x)&&a.testBit ((Nat.mul 2 (vK x)).add 1)))
  else if vr.blt 550 then let i:=vr.sub 50;let s:=i.div 10;let y:=i.mod 10;let x:=s.div 5;let j:=s.mod 5;x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&(a.testBit (Nat.mul 2 (kI x j))||a.testBit (Nat.mul 2 (vC x y)))
  else let i:=vr.sub 550;let s:=i.div 10;let y:=i.mod 10;let x:=s.div 5;let j:=s.mod 5;x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&(a.testBit (Nat.mul 2 (kI x j))||gB a b (wW x j) true||(kB C.I y&&!(x.beq y)&&(gB a b (uO x j) true||!((((qR a (kD x j 0)).land uR).land (uR.xor (Nat.shiftLeft 1 ((Nat.mul 2 y).add 1)))).beq 0)||ug a (kE x j 0) (kD y 0 0))))
def zx (C:OCtx)(a b vr:Nat):Bool:=
  if vr.blt 1940 then
    if vr.blt 1180 then false
    else if vr.blt 1480 then let i:=vr.sub 1180;let t:=i.div 100;let r:=i.mod 100;let x:=r.div 10;let y:=r.mod 10;t.blt C.k&&x.blt 10&&y.blt 10&&!(x.beq y)&&(a.testBit (Nat.mul 2 (kQ t x))||a.testBit ((Nat.mul 2 (kQ t y)).add 1))
    else if vr.blt 1500 then false
    else if vr.blt 1510 then let x:=vr.sub 1500;x.blt 10&&!(kB C.I x)&&((1:Nat).add C.k).blt 5&&a.testBit ((Nat.mul 2 (kI x ((1:Nat).add C.k))).add 1)
    else if vr.blt 1660 then let i:=vr.sub 1510;let t:=i.div 50;let r:=i.mod 50;let x:=r.div 5;let j:=r.mod 5;t.blt C.k&&x.blt 10&&!(kB C.I x)&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||!((((qR a (kQ t 0)).land uR).land (((qR a (kE x j 0)).land uS).shiftLeft 1)).beq 0))
    else false
  else let i:=vr.sub 1940;let se:=i.div 50;let r:=i.mod 50;let x:=r.div 5;let j:=r.mod 5;let s:=se.div 14;let e:=se.mod 14;s.blt 2&&e.blt 14&&x.blt 10&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||a.testBit (Nat.mul 2 (kN s e x))||a.testBit ((Nat.mul 2 (kN ((1:Nat).sub s) e x)).add 1)||gB a b (uO x j) true||gB a b (uP e x j) true||ug a (kE x j 0) (kN s e 0)||ug a (kD x j 0) (kN ((1:Nat).sub s) e 0))
def zn (C:OCtx)(a b vr:Nat):Bool:=
  if vr.blt 3390 then let i:=vr.sub 3340;xB C a b (i.div 5) (i.mod 5)
  else if vr.blt 3440 then let i:=vr.sub 3390;xD C a b (i.div 5) (i.mod 5)
  else if vr.blt 3636 then let i:=vr.sub 3440;let u:=i.div 14;let v:=i.mod 14;u.blt v&&v.blt 14&&(gB a b (uK u v) false||xw a b u v||ug a (kN 0 u 0) (kN 0 v 0)||ug a (kN 1 u 0) (kN 1 v 0))
  else if vr.blt 3832 then let i:=vr.sub 3636;let u:=i.div 14;let v:=i.mod 14;u.blt v&&v.blt 14&&(gB a b (uK u v) false||xw a b u v||ug a (kN 0 u 0) (kN 1 v 0)||ug a (kN 1 u 0) (kN 0 v 0))
  else if vr.blt 4028 then let i:=vr.sub 3832;let u:=i.div 14;let v:=i.mod 14;u.blt v&&v.blt 14&&xw a b u v
  else if vr.blt 4224 then let i:=vr.sub 4028;xX a b (i.div 14) (i.mod 14)
  else if vr.blt 4924 then let i:=vr.sub 4224;let e:=i.div 50;let r:=i.mod 50;vJ C a b e (r.div 5) (r.mod 5)
  else if vr.blt 4938 then false
  else if vr.blt 5288 then let i:=vr.sub 4938;let e:=i.div 25;let r:=i.mod 25;let p:=r.div 5;let q:=r.mod 5;let u:=ep0N e;let w:=ep1N C.gi e;e.blt 14&&p.blt (kk C.k C.I u)&&q.blt (kk C.k C.I w)&&(a.testBit (Nat.mul 2 (kI u p))||a.testBit (Nat.mul 2 (kI w q))||gB a b (ur 0 e u p) true||gB a b (ur 1 e w q) true||ug a (kE u p 0) (kD w q 0)||ug a (kE w q 0) (kD u p 0))
  else if vr.blt 5988 then let i:=vr.sub 5288;let e:=i.div 50;let r:=i.mod 50;let x:=r.div 5;let j:=r.mod 5;e.blt 14&&x.blt 10&&j.blt (kk C.k C.I x)&&(vJ C a b e x j||xB C a b x j)
  else let i:=vr.sub 5988;let e:=i.div 50;let r:=i.mod 50;let x:=r.div 5;let j:=r.mod 5;e.blt 14&&x.blt 10&&j.blt (kk C.k C.I x)&&(vJ C a b e x j||xD C a b x j)
def yZ (C:OCtx)(a b vr:Nat):Bool:=
  if vr.blt 7998 then
    if vr.blt 6716 then false
    else if vr.blt 6856 then let i:=vr.sub 6716;let e:=i.div 10;let z:=i.mod 10;(0:Nat).blt C.m&&e.blt 14&&z.blt 10&&vP a b e z 10
    else if vr.blt 7556 then let i:=vr.sub 6856;let e:=i.div 50;let r:=i.mod 50;let z:=r.div 5;let l0:=r.mod 5;(0:Nat).blt C.m&&e.blt 14&&z.blt 10&&l0.blt (kk C.k C.I z)&&(vJ C a b e z l0||(a.testBit (Nat.mul 2 (kD z l0 (ep0N e)))&&a.testBit (Nat.mul 2 (kD z l0 (ep1N C.gi e)))))
    else false
  else if vr.blt 11230 then
    if vr.blt 8798 then let i:=vr.sub 7998;let x:=i.div 80;let r:=i.mod 80;let c:=r.div 5;let j:=r.mod 5;x.blt 10&&c.blt 16&&j.blt (kk C.k C.I x)&&(a.testBit (Nat.mul 2 (kI x j))||!((((qR a (kE x j 0)).land uR).land (A9 C.gi c)).beq 0))
    else if vr.blt 9118 then let i:=vr.sub 8798;let u:=i.div 5;let l0:=i.mod 5;if (0:Nat).blt C.m&&vCx C.gi C.t C.c u then let cu:=qY C.c u;let tr:=yA C.t cu.1;l0.blt (kk C.k C.I cu.2.2)&&(vJ C a b cu.2.1 cu.2.2 l0||a.testBit ((Nat.mul 2 (kD cu.2.2 l0 tr.2.1)).add 1)||a.testBit ((Nat.mul 2 (kD cu.2.2 l0 tr.2.2)).add 1)||(a.testBit (Nat.mul 2 (kD cu.2.2 l0 (ep0N tr.1)))&&a.testBit (Nat.mul 2 (kD cu.2.2 l0 (ep1N C.gi tr.1))))) else false
    else if vr.blt 10014 then let i:=vr.sub 9118;let u:=i.div 14;let e2:=i.mod 14;if (0:Nat).blt C.m&&vCx C.gi C.t C.c u then let cu:=qY C.c u;e2.blt 14&&!(e2.beq cu.2.1)&&(gB a b (ux cu.2.1 e2) false||xX a b cu.2.1 e2||gB a b (zH cu.1 e2) false||(a.testBit (Nat.mul 2 (kN 0 e2 cu.2.2))&&a.testBit (Nat.mul 2 (kN 1 e2 cu.2.2)))) else false
    else if vr.blt 10314 then let i:=vr.sub 10014;let m0:=i.div 50;let r:=i.mod 50;let z:=r.div 5;let l0:=r.mod 5;if C.m.beq 1&&yR C.x m0&&z.blt 10&&l0.blt (kk C.k C.I z) then let d:=(uZ C.x m0).1;a.testBit (Nat.mul 2 (kD z l0 (ep0N d)))&&a.testBit (Nat.mul 2 (kD z l0 (ep1N C.gi d))) else false
    else false
  else if vr.blt 13730 then let i:=vr.sub 11230;let s1:=i.div 50;let s2:=i.mod 50;let x:=s1.div 5;let j:=s1.mod 5;let y:=s2.div 5;let l0:=s2.mod 5;x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&!(y.beq x)&&!(kB C.I y)&&l0.blt (kk C.k C.I y)&&(a.testBit (Nat.mul 2 (kI y l0))||ug a (kE x j 0) (kE y l0 0)||ug a (kD x j 0) (kD y l0 0))
  else if vr.blt 16230 then let i:=vr.sub 13730;let s1:=i.div 50;let s2:=i.mod 50;let x:=s1.div 5;let j:=s1.mod 5;let y:=s2.div 5;let l0:=s2.mod 5;x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&!(y.beq x)&&!(kB C.I y)&&l0.blt (kk C.k C.I y)&&(a.testBit (Nat.mul 2 (kI y l0))||ug a (kE x j 0) (kD y l0 0)||ug a (kD x j 0) (kE y l0 0))
  else if vr.blt 17730 then let id:=vr.sub 16230;let i:=id.div 150;let r:=id.mod 150;let y:=r.div 15;let r2:=r.mod 15;let n:=r2.div 5;let l0:=r2.mod 5;if C.m.beq 1&&i.blt 10&&kB C.I i&&y.blt 10&&!(kB C.I y)&&!(adjB C.gi i y)&&n.blt 3&&n.blt (nbrsN C.gi i).length then let x:=(nbrsN C.gi i).getD n 0;if l0.blt (kk C.k C.I x) then let e:=(eIx C.gi i x).1;gB a b (xR e x l0) false||vJ C a b e x l0||xD C a b x l0||xB C a b x l0||a.testBit ((Nat.mul 2 (kE x l0 y)).add 1)||!((((qR a (kE x l0 0)).land uS).land (AX C.gi i)).beq 0) else false else false
  else false
def A3 (C:OCtx)(a b:Nat)(l:qv):Bool:=
  let vr:=l.1;let pl:=l.2
  if gB a b vr (!pl) then true
  else if !pl then
    if !(vr.blt 1080)&&vr.blt 1180 then let i:=vr.sub 1080;let x:=i.div 10;let y:=i.mod 10;!(y.blt x)&&y.blt 10&&(uY a x y (kk C.k C.I x)||uY a y x (kk C.k C.I y)) else false
  else if vr.blt 1050 then zA C a b vr
  else if vr.blt 3340 then zx C a b vr
  else if vr.blt 6688 then zn C a b vr
  else yZ C a b vr
def wG:List (Nat×Nat×Nat)->Nat->Nat->Nat->Option (Nat×Nat)
| [],a,_,nd=>some (a,nd)
| (u,v,m)::r,a,dm,nd=>
  if (dm.land m).beq 0 then wG r a dm nd
  else
    let b1:=qR a u;let b2:=qR a v
    if b1.beq b2 then wG r a dm nd
    else if !((b1.land (wZ b2)).beq 0) then none
    else
      let u12:=b1.lor b2
      let nd1:=if u12.beq b1 then nd else nd.lor (qV u)
      let nd2:=if u12.beq b2 then nd1 else nd1.lor (qV v)
      wG r (a.lor ((b1.shiftLeft (Nat.mul 2 v)).lor (b2.shiftLeft (Nat.mul 2 u)))) dm nd2
def vg (e:List (Nat×Nat×Nat))(mk a dm nd:Nat):Option (Nat×Nat):=if (dm.land mk).beq 0 then some (a,nd) else wG e a dm nd
def Aa (E:wQ)(a dm:Nat):Option (Nat×Nat):=
  (vg E.e0 E.m0 a dm 0).bind λ p0=>(vg E.e1 E.m1 p0.1 dm p0.2).bind λ p1=>(vg E.e2 E.m2 p1.1 dm p1.2).bind λ p2=>(vg E.e3 E.m3 p2.1 dm p2.2).bind λ p3=>(vg E.e4 E.m4 p3.1 dm p3.2).bind λ p4=>(vg E.e5 E.m5 p4.1 dm p4.2).bind λ p5=>(vg E.e6 E.m6 p5.1 dm p5.2).bind λ p6=>vg E.e7 E.m7 p6.1 dm p6.2
def wF:List (Nat×Nat×Nat)->Nat->Nat->Nat->Option (Nat×Nat)
| [],a,_,nd=>some (a,nd)
| (u,v,m)::r,a,dm,nd=>
  if (dm.land m).beq 0 then wF r a dm nd
  else
    let b1:=qR a u;let b2:=qR a v;let p1:=b1.land uR;let n2:=b2.land uS
    if !((p1.land (n2.shiftLeft 1)).beq 0) then none
    else
      let c2:=!((p1.land b2).beq p1);let c1:=!((n2.land b1).beq n2)
      if !c1&&!c2 then wF r a dm nd
      else
        let nd1:=if c1 then nd.lor (qV u) else nd
        let nd2:=if c2 then nd1.lor (qV v) else nd1
        wF r (a.lor ((p1.shiftLeft (Nat.mul 2 v)).lor (n2.shiftLeft (Nat.mul 2 u)))) dm nd2
def wY (E:wQ)(imps:List (Nat×Nat×Nat))(im:Nat):Nat->Nat->Nat->Option Nat
| 0,a,_=>some a
| f+1,a,dm=>if dm.beq 0 then some a else (Aa E a dm).bind λ p1=>(if (dm.land im).beq 0 then some p1 else wF imps p1.1 dm p1.2).bind λ p2=>if p2.2.beq 0 then some p2.1 else wY E imps im f p2.1 p2.2
def kR (st:St):Option St:=if st.dm.beq 0 then some st else match wY st.eqs st.imps st.im 10 st.a st.dm with| none=>none| some a'=>some ⟨a',st.b,st.eqs,st.imps,st.im,0⟩
def AV (x y:Nat):Nat->List qv->List qv
| 0,a=>a
| j+1,a=>AV x y j ((kE x j y,false)::a)
def AU (e z:Nat):Nat->List qv->List qv
| 0,a=>a
| u+1,a=>AU e z u (if u.beq z then a else (wM e u,false)::a)
abbrev zW:=List qv->Nat->wQ->List (Nat×Nat×Nat)->Nat->Nat->Option St
def Bt (C:OCtx)(go:zW)(vr:Nat)(r:List qv)(a:Nat)(e:wQ)(i:List (Nat×Nat×Nat))(k d:Nat):Option St:=
  if vr.blt 50 then let x:=vr.div 5;let j:=vr.mod 5;if x.blt 10&&j.blt (kk C.k C.I x) then let q1:=(kE x j x,true)::r;go (if !(j.beq 0) then (kI x (j.sub 1),true)::q1 else q1) a e i k d else go r a e i k d
  else if vr.blt 550 then let i0:=vr.sub 50;let s:=i0.div 10;let y:=i0.mod 10;let x:=s.div 5;let j:=s.mod 5;if x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10 then go ((kI x j,true)::(vC x y,true)::r) a e i k d else go r a e i k d
  else let i0:=vr.sub 550;let s:=i0.div 10;let y:=i0.mod 10;let x:=s.div 5;let j:=s.mod 5;if x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10 then let q1:=(kI x j,true)::r;if kB C.I y&&!(x.beq y) then (vV a (kD x j 0) (uS.xor (Nat.shiftLeft 1 (Nat.mul 2 y)))).bind λ a'=>go ((uO x j,false)::q1) a' (kX e (kE x j 0) (kD y 0 0)) i k (d.lor ((bM (kE x j 0) (kD y 0 0)).lor (qV (kD x j 0)))) else go q1 a e i k d else go r a e i k d
def Br (C:OCtx)(go:zW)(vr:Nat)(r:List qv)(a:Nat)(e:wQ)(i:List (Nat×Nat×Nat))(k d:Nat):Option St:=
  if vr.blt 1940 then
    if !(vr.blt 1180)&&vr.blt 1480 then let i0:=vr.sub 1180;let t:=i0.div 100;let q:=i0.mod 100;let x:=q.div 10;let y:=q.mod 10;if t.blt C.k&&x.blt 10&&y.blt 10&&!(x.beq y) then go ((kQ t x,true)::(kQ t y,false)::r) a e i k d else go r a e i k d
    else if !(vr.blt 1500)&&vr.blt 1510 then let x:=vr.sub 1500;if x.blt 10&&!(kB C.I x)&&((1:Nat).add C.k).blt (kk C.k C.I x) then go ((kI x ((1:Nat).add C.k),false)::r) a e i k d else go r a e i k d
    else if !(vr.blt 1510)&&vr.blt 1660 then let i0:=vr.sub 1510;let t:=i0.div 50;let q:=i0.mod 50;let x:=q.div 5;let j:=q.mod 5;if t.blt C.k&&x.blt 10&&!(kB C.I x)&&j.blt (kk C.k C.I x) then let pi:=xM i k (kQ t 0) (kE x j 0);go ((kI x j,true)::r) a e pi.1 pi.2 (d.lor (bM (kQ t 0) (kE x j 0))) else go r a e i k d
    else go r a e i k d
  else let i0:=vr.sub 1940;let se:=i0.div 50;let q:=i0.mod 50;let x:=q.div 5;let j:=q.mod 5;let s:=se.div 14;let e0:=se.mod 14;if s.blt 2&&e0.blt 14&&x.blt 10&&j.blt (kk C.k C.I x) then go ((kI x j,true)::(kN s e0 x,true)::(kN ((1:Nat).sub s) e0 x,false)::(uO x j,false)::(uP e0 x j,false)::r) a (kX (kX e (kE x j 0) (kN s e0 0)) (kD x j 0) (kN ((1:Nat).sub s) e0 0)) i k (d.lor ((bM (kE x j 0) (kN s e0 0)).lor (bM (kD x j 0) (kN ((1:Nat).sub s) e0 0)))) else go r a e i k d
def Bp (C:OCtx)(go:zW)(vr:Nat)(r:List qv)(a:Nat)(e:wQ)(i:List (Nat×Nat×Nat))(k d:Nat):Option St:=
  if vr.blt 3390 then let i0:=vr.sub 3340;let x:=i0.div 5;let j:=i0.mod 5;if x.blt 10&&j.blt (kk C.k C.I x) then (vV a (kD x j 0) (C.ie.xor (C.ie.land (Nat.shiftLeft 1 (Nat.mul 2 x))))).bind λ a'=>go ((kI x j,true)::r) a' e i k (d.lor (qV (kD x j 0))) else go r a e i k d
  else if vr.blt 3440 then let i0:=vr.sub 3390;let x:=i0.div 5;let j:=i0.mod 5;if x.blt 10&&j.blt (kk C.k C.I x) then (vV a (kD x j 0) uS).bind λ a'=>go ((kI x j,true)::r) a' e i k (d.lor (qV (kD x j 0))) else go r a e i k d
  else if vr.blt 3636 then let i0:=vr.sub 3440;let u:=i0.div 14;let v:=i0.mod 14;if u.blt v&&v.blt 14 then go ((uK u v,true)::r) a (kX (kX e (kN 0 u 0) (kN 0 v 0)) (kN 1 u 0) (kN 1 v 0)) i k (d.lor ((bM (kN 0 u 0) (kN 0 v 0)).lor (bM (kN 1 u 0) (kN 1 v 0)))) else go r a e i k d
  else if vr.blt 3832 then let i0:=vr.sub 3636;let u:=i0.div 14;let v:=i0.mod 14;if u.blt v&&v.blt 14 then go ((uK u v,true)::r) a (kX (kX e (kN 0 u 0) (kN 1 v 0)) (kN 1 u 0) (kN 0 v 0)) i k (d.lor ((bM (kN 0 u 0) (kN 1 v 0)).lor (bM (kN 1 u 0) (kN 0 v 0)))) else go r a e i k d
  else if vr.blt 4028 then let i0:=vr.sub 3832;let u:=i0.div 14;let v:=i0.mod 14;if u.blt v&&v.blt 14 then go ((ux u v,false)::(ux v u,false)::r) a e i k d else go r a e i k d
  else if vr.blt 4224 then let i0:=vr.sub 4028;let u:=i0.div 14;let v:=i0.mod 14;if u.blt 14&&v.blt 14&&!(u.beq v) then go ((ux v u,false)::(uK u v,false)::r) a e i k d else go r a e i k d
  else if vr.blt 4924 then let i0:=vr.sub 4224;let e0:=i0.div 50;let q:=i0.mod 50;let x:=q.div 5;let j:=q.mod 5;if e0.blt 14&&x.blt 10&&j.blt (kk C.k C.I x) then go ((kI x j,true)::(ur 0 e0 x j,false)::(ur 1 e0 x j,false)::r) a e i k d else go r a e i k d
  else if vr.blt 4938 then go r a e i k d
  else if vr.blt 5288 then let i0:=vr.sub 4938;let e0:=i0.div 25;let q:=i0.mod 25;let p:=q.div 5;let t:=q.mod 5;let u:=ep0N e0;let w:=ep1N C.gi e0;if e0.blt 14&&p.blt (kk C.k C.I u)&&t.blt (kk C.k C.I w) then go ((kI u p,true)::(kI w t,true)::(ur 0 e0 u p,false)::(ur 1 e0 w t,false)::r) a (kX (kX e (kE u p 0) (kD w t 0)) (kE w t 0) (kD u p 0)) i k (d.lor ((bM (kE u p 0) (kD w t 0)).lor (bM (kE w t 0) (kD u p 0)))) else go r a e i k d
  else if vr.blt 5988 then let i0:=vr.sub 5288;let e0:=i0.div 50;let q:=i0.mod 50;let x:=q.div 5;let j:=q.mod 5;if e0.blt 14&&x.blt 10&&j.blt (kk C.k C.I x) then go ((uP e0 x j,true)::(uO x j,true)::r) a e i k d else go r a e i k d
  else let i0:=vr.sub 5988;let e0:=i0.div 50;let q:=i0.mod 50;let x:=q.div 5;let j:=q.mod 5;if e0.blt 14&&x.blt 10&&j.blt (kk C.k C.I x) then go ((uP e0 x j,true)::(wW x j,true)::r) a e i k d else go r a e i k d
def Bn (C:OCtx)(go:zW)(vr:Nat)(r:List qv)(a:Nat)(e:wQ)(i:List (Nat×Nat×Nat))(k d:Nat):Option St:=
  if vr.blt 7998 then
    if !(vr.blt 6716)&&vr.blt 6856 then let i0:=vr.sub 6716;let e0:=i0.div 10;let z:=i0.mod 10;go (if (0:Nat).blt C.m&&e0.blt 14&&z.blt 10 then AU e0 z 10 r else r) a e i k d
    else if !(vr.blt 6856)&&vr.blt 7556 then let i0:=vr.sub 6856;let e0:=i0.div 50;let q:=i0.mod 50;let z:=q.div 5;let l0:=q.mod 5;if (0:Nat).blt C.m&&e0.blt 14&&z.blt 10&&l0.blt (kk C.k C.I z) then go ((uP e0 z l0,true)::r) a e i k d else go r a e i k d
    else go r a e i k d
  else if vr.blt 11230 then
    if vr.blt 8798 then let i0:=vr.sub 7998;let x:=i0.div 80;let q:=i0.mod 80;let c:=q.div 5;let j:=q.mod 5;if x.blt 10&&c.blt 16&&j.blt (kk C.k C.I x) then (vV a (kE x j 0) (Ba C.gi c)).bind λ a'=>go ((kI x j,true)::r) a' e i k (d.lor (qV (kE x j 0))) else go r a e i k d
    else if vr.blt 9118 then let i0:=vr.sub 8798;let u:=i0.div 5;let l0:=i0.mod 5;if (0:Nat).blt C.m&&vCx C.gi C.t C.c u then let cu:=qY C.c u;let tr:=yA C.t cu.1;if l0.blt (kk C.k C.I cu.2.2) then go ((uP cu.2.1 cu.2.2 l0,true)::(kD cu.2.2 l0 tr.2.1,false)::(kD cu.2.2 l0 tr.2.2,false)::r) a e i k d else go r a e i k d else go r a e i k d
    else if vr.blt 10014 then let i0:=vr.sub 9118;let u:=i0.div 14;let e2:=i0.mod 14;if (0:Nat).blt C.m&&vCx C.gi C.t C.c u then let cu:=qY C.c u;if e2.blt 14&&!(e2.beq cu.2.1) then go ((ux cu.2.1 e2,true)::(zH cu.1 e2,true)::r) a e i k d else go r a e i k d else go r a e i k d
    else go r a e i k d
  else if vr.blt 13730 then let i0:=vr.sub 11230;let s1:=i0.div 50;let s2:=i0.mod 50;let x:=s1.div 5;let j:=s1.mod 5;let y:=s2.div 5;let l0:=s2.mod 5;if x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&!(y.beq x)&&!(kB C.I y)&&l0.blt (kk C.k C.I y) then go ((kI y l0,true)::r) a (kX (kX e (kE x j 0) (kE y l0 0)) (kD x j 0) (kD y l0 0)) i k (d.lor ((bM (kE x j 0) (kE y l0 0)).lor (bM (kD x j 0) (kD y l0 0)))) else go r a e i k d
  else if vr.blt 16230 then let i0:=vr.sub 13730;let s1:=i0.div 50;let s2:=i0.mod 50;let x:=s1.div 5;let j:=s1.mod 5;let y:=s2.div 5;let l0:=s2.mod 5;if x.blt 10&&j.blt (kk C.k C.I x)&&y.blt 10&&!(y.beq x)&&!(kB C.I y)&&l0.blt (kk C.k C.I y) then go ((kI y l0,true)::r) a (kX (kX e (kE x j 0) (kD y l0 0)) (kD x j 0) (kE y l0 0)) i k (d.lor ((bM (kE x j 0) (kD y l0 0)).lor (bM (kD x j 0) (kE y l0 0)))) else go r a e i k d
  else if vr.blt 17730 then let id:=vr.sub 16230;let i0:=id.div 150;let q:=id.mod 150;let y:=q.div 15;let q2:=q.mod 15;let n:=q2.div 5;let l0:=q2.mod 5;if C.m.beq 1&&i0.blt 10&&kB C.I i0&&y.blt 10&&!(kB C.I y)&&!(adjB C.gi i0 y)&&n.blt 3&&n.blt (nbrsN C.gi i0).length then let x:=(nbrsN C.gi i0).getD n 0;if l0.blt (kk C.k C.I x) then let e0:=(eIx C.gi i0 x).1;(vV a (kE x l0 0) (AW C.gi i0)).bind λ a'=>go ((xR e0 x l0,true)::(uO x l0,true)::(kE x l0 y,false)::r) a' e i k (d.lor (qV (kE x l0 0))) else go r a e i k d else go r a e i k d
  else go r a e i k d
def yV (C:OCtx):Nat->List qv->Nat->Nat->wQ->List (Nat×Nat×Nat)->Nat->Nat->Option St
| 0,_,a,b,eqs,imps,im,dm=>some ⟨a,b,eqs,imps,im,dm⟩
| _,[],a,b,eqs,imps,im,dm=>some ⟨a,b,eqs,imps,im,dm⟩
| f+1,(vr,pl)::r,a,b,eqs,imps,im,dm=>
  if gB a b vr pl then yV C f r a b eqs imps im dm
  else if A3 C a b (vr,pl) then none
  else
    let ab:=zO a b vr pl;let a:=ab.1;let b:=ab.2;let dm:=dm.lor (BO vr)
    let go:zW:=λ q a' e' i' im' dm'=>yV C f q a' b e' i' im' dm'
    if !pl then
      if vr.blt 50 then let x:=vr.div 5;let j:=vr.mod 5;go (if x.blt 10&&(j.add 1).blt (kk C.k C.I x) then (kI x (j.add 1),false)::r else r) a eqs imps im dm
      else if !(vr.blt 1080)&&vr.blt 1180 then let i:=vr.sub 1080;let x:=i.div 10;let y:=i.mod 10;go (if !(y.blt x)&&y.blt 10 then AV y x (kk C.k C.I y) (AV x y (kk C.k C.I x) r) else r) a eqs imps im dm
      else go r a eqs imps im dm
    else if vr.blt 1050 then Bt C go vr r a eqs imps im dm
    else if vr.blt 3340 then Br C go vr r a eqs imps im dm
    else if vr.blt 6688 then Bp C go vr r a eqs imps im dm
    else Bn C go vr r a eqs imps im dm
def BB (l:qv):Bool:=l.2&&((!(l.1.blt 6856)&&l.1.blt 7556)||(!(l.1.blt 8798)&&l.1.blt 10314))
def ue (C:OCtx)(st:St)(l:qv):Option St:=
  if BB l&&!(st.dm.beq 0) then (kR st).bind λ s=>yV C 64 [l] s.a s.b s.eqs s.imps s.im s.dm
  else yV C 64 [l] st.a st.b st.eqs st.imps st.im st.dm
def ws (C:OCtx):List qv->St->Option St
| [],st=>some st
| l::r,st=>(ue C st l).bind λ s=>ws C r s
def wI (C:OCtx):q0->St->Option St
| [],st=>some st
| l::r,st=>(ue C st (w3 l)).bind λ s=>wI C r s
def vZ (C:OCtx):List qv:=
  ((List.range 10).map λ x=>(kI x 0,true))++
  ((List.range 10).flatMap λ x=>
    (if kB C.I x then
      ((List.range C.k).map λ t=>(kQ t x,false))++[(vK x,false)]++
      ((nbrsN C.gi x).flatMap λ y=>((nbrsN C.gi x).filter λ z=>y.blt z).map λ z=>(vC y z,true))++
      ((List.range 10).flatMap λ y=>if adjB C.gi x y then [(kD x 0 y,true)] else if !(x.beq y)&&kB C.I y then [(kD x 0 y,false)] else [])
    else [])++
    (((List.range 10).filter λ y=>x.blt y&&(kB C.I x||kB C.I y)).map λ y=>(vC x y,false))++
    ((List.range (kk C.k C.I x)).map λ j=>(kD x j x,false)))++
  ((List.range 14).flatMap λ e=>let a0:=ep0N e;let a1:=ep1N C.gi e;[(kN 0 e a0,true),(kN 0 e a1,false),(kN 1 e a1,true),(kN 1 e a0,false)])++
  ((List.range 10).flatMap λ x=>if kB C.I x then [] else
    let iN:=iNN C.gi C.I x;let eN:=eNN C.gi C.I x;let cp:=kk C.k C.I x
    ((List.range (min (iN.length+(if eN.isEmpty then 0 else 1)) cp)).map λ h=>(kI x h,true))++
    ((List.range (min iN.length cp)).flatMap λ h=>let y:=iN.getD h 0;let p:=eIx C.gi x y;[(kD x h y,true),(ur p.2 p.1 x h,true)])++
    (if !eN.isEmpty&&iN.length.blt cp then let p:=eIx C.gi x (eN.getD 0 0);[(ur p.2 p.1 x iN.length,true)] else []))
def BD (C:OCtx):Option St:=(ws C (vZ C) ⟨0,0,BI,[],0,0⟩).bind kR
def xY (C:OCtx)(a b:Nat):Option qv->q0->Option (Option qv)
| acc,[]=>some acc
| acc,l::r=>if A3 C a b l then xY C a b acc r else match acc with| none=>xY C a b (some l) r| some p=>if p==l then xY C a b acc r else none
def fU (C:OCtx)(a b:Nat)(c:q0):Option (Option qv):=xY C a b none c
def yE (w n:Nat):Nat->Nat->Nat->Nat
| 0,_,b=>b
| c+1,v,b=>let h:=qj w n v b;yE w n c h.1 h.2
def uy (C:OCtx)(st:St)(cl:q0):Option (Option St):=
  match fU C st.a st.b cl with
  | some none=>some none
  | some (some p)=>some (ue C st p)
  | none=>if st.dm.beq 0 then none else match kR st with
    | none=>some none
    | some st1=>match fU C st1.a st1.b cl with
      | some none=>some none
      | some (some p)=>some (ue C st1 p)
      | none=>none
def uh (C:OCtx)(st:St)(cl:q0):Bool:=
  match fU C st.a st.b cl with
  | some none=>true
  | some (some p)=>match ue C st p with| none=>true| some s1=>(kR s1).isNone
  | none=>if st.dm.beq 0 then false else match kR st with
    | none=>true
    | some st1=>match fU C st1.a st1.b cl with
      | some none=>true
      | some (some p)=>match ue C st1 p with| none=>true| some s1=>(kR s1).isNone
      | none=>false
def q5 (C:OCtx)(B:Nat->q0)(w n:Nat):Nat->Nat->Nat->St->Option Nat
| 0,_,_,_=>none
| 1,v,b,st=>let h:=qj w n v b;if decide (h.1<n) then if uh C st (B h.1) then some h.2 else none else none
| c+2,v,b,st=>let h:=qj w n v b;if decide (h.1<n) then match uy C st (B h.1) with| some none=>some (yE w n (c+1) h.1 h.2)| some (some s)=>q5 C B w n (c+1) h.1 h.2 s| none=>none else none
def yT (C:OCtx)(B:Nat->q0)(w n:Nat):Nat->Nat->Nat->St->Option (Option (St×Nat))
| 0,_,b,st=>match kR st with| none=>some none| some s=>some (some (s,b))
| c+1,v,b,st=>let h:=qj w n v b;if decide (h.1<n) then match uy C st (B h.1) with| some none=>some none| some (some s)=>yT C B w n c h.1 h.2 s| none=>none else none
def qb (C:OCtx)(B:Nat->q0)(w n b:Nat)(st:St):Bool:=let r:=qr b;(q5 C B w n r.1 0 r.2 st).isSome
def vN (C:OCtx)(B:Nat->q0)(w:Nat):Nat->Nat->Nat->St->Bool
| 0,i,h,st=>qb C B w i h st
| m+1,i,h,st=>
  let r:=qr h;let c:=B i
  let nx (h':Nat):Bool:=match c with| [l]=>(match (ue C st l).bind kR with| none=>true| some s=>vN C B w m (i+1) h' s)| _=>vN C B w m (i+1) h' st
  match wI C c st with
  | none=>if r.1.beq 0 then nx r.2 else false
  | some s0=>if r.1.beq 0 then (match kR s0 with| none=>nx r.2| some _=>false) else (match q5 C B w i r.1 0 r.2 s0 with| none=>false| some h'=>nx h')
def qt (gi:Fin 4)(k I m:Nat)(t c x:List Nat)(f:Nat->Nat)(d:Nat->q0)(nb nd w h:Nat):Bool:=
  let C:=qU gi k I m t c x;let B:=AY (exS gi k I m t c x) (AC f) d nb
  if wD (enabled gi k I m 0 t c x) f nb then match BD C with| none=>true| some s0=>let ru:=qr h;(match yT C B w nb ru.1 0 ru.2 s0 with| none=>false| some none=>true| some (some p)=>vN C B w nd nb p.2 p.1) else false

structure OOK (gi:Fin 4)(k I m:Nat)(t c x:List Nat)(v:Nat->Bool):Prop where
 o0:k<=3
 o1:∀a,a<10->v (kI a 0)=true
 o2:∀a j,a<10->j<kk k I a->v (kI a j)=true->v (kE a j a)=true
 o3:∀a j,a<10->j+1<kk k I a->v (kI a (j+1))=true->v (kI a j)=true
 o4:∀a j y,a<10->j<kk k I a->y<10->v (kE a j y)=true->v (kI a j)=true
 o5:∀a j y,a<10->j<kk k I a->y<10->v (kE a j y)=true->v (vC a y)=true
 o6:∀a t0,a<10->kB I a=true->t0<k->v (kQ t0 a)=false
 o7:∀a y,a<y->y<10->(kB I a=true\/kB I y=true)->v (vC a y)=false
 o8:∀i y z,i<10->kB I i=true->y<z->z<10->adjB gi i y=true->adjB gi i z=true->v (vC y z)=true
 o9:∀t0 a y,t0<k->a<10->y<10->a≠y->v (zG t0 a y)=true->v (kQ t0 a)=true/\v (kQ t0 y)=false
 oa:∀a c0 j,a<10->c0<16->j<kk k I a->v (zI a c0 j)=true->v (kI a j)=true/\∀y,y<10->(aMk gi c0).testBit y=true->v (kE a j y)=false
 ob:∀a,a<10->kB I a=true->v (vK a)=false
 oc:∀a,a<10->kB I a=false->v (vK a)=true->v (kI a (1+k))=false
 od:∀t0 a j,t0<k->a<10->kB I a=false->j<kk k I a->v (xQ t0 a j)=true->v (kI a j)=true/\∀y,y<10->v (kQ t0 y)=true->v (kE a j y)=true
 oe:∀a j,a<10->j<kk k I a->v (kD a j a)=false
 of:∀a j y,a<10->j<kk k I a->y<10->v (kD a j y)=true->v (kI a j)=true
 og:∀a j y,a<10->j<kk k I a->y<10->kB I y=true->a≠y->v (kD a j y)=true->v (uO a j)=false/\(∀d,d<10->d≠y->v (kD a j d)=false)/\(∀d,d<10->v (kE a j d)=v (kD y 0 d))
 oh:∀a y,a<10->kB I a=true->y<10->(adjB gi a y=true->v (kD a 0 y)=true)/\(kB I y=true->a≠y->v (kD a 0 y)=false)
 oi:∀s e,s<2->e<14->v (kN s e (epN gi s e))=true/\v (kN s e (epN gi (1-s) e))=false
 oj:∀s e a j,s<2->e<14->a<10->j<kk k I a->v (ur s e a j)=true->v (kI a j)=true/\v (kN s e a)=true/\v (kN (1-s) e a)=false/\v (uO a j)=false/\v (uP e a j)=false/\(∀y,y<10->v (kE a j y)=v (kN s e y))/\(∀y,y<10->v (kD a j y)=v (kN (1-s) e y))
 ok:∀a,a<10->kB I a=false->(∀h,h<(iNN gi I a).length+(if (eNN gi I a).isEmpty then 0 else 1)->h<kk k I a->v (kI a h)=true)/\(∀h,h<(iNN gi I a).length->h<kk k I a->let y:=(iNN gi I a).getD h 0;let p:=eIx gi a y;v (kD a h y)=true/\v (ur p.2 p.1 a h)=true)/\((eNN gi I a).isEmpty=false->(iNN gi I a).length<kk k I a->let p:=eIx gi a ((eNN gi I a).getD 0 0);v (ur p.2 p.1 a (iNN gi I a).length)=true)
 ov:∀a j,a<10->j<kk k I a->(v (uO a j)=true->v (kI a j)=true)/\(v (wW a j)=true->v (kI a j)=true/\∀y,y<10->v (kD a j y)=false)
 om:∀b a,b<a->a<14->(v (yN b a)=true->v (uK b a)=true/\(∀y,y<10->v (kN 0 b y)=v (kN 0 a y))/\(∀y,y<10->v (kN 1 b y)=v (kN 1 a y)))/\(v (yO b a)=true->v (uK b a)=true/\(∀y,y<10->v (kN 0 b y)=v (kN 1 a y))/\(∀y,y<10->v (kN 1 b y)=v (kN 0 a y)))
 on:∀b a,b<14->a<14->b≠a->(v (uK b a)=true->v (ux b a)=false)/\(v (ux b a)=true->v (ux a b)=false/\v (uK b a)=false)
 oo:∀e a j,e<14->a<10->j<kk k I a->(v (uP e a j)=true->v (kI a j)=true/\v (ur 0 e a j)=false/\v (ur 1 e a j)=false)/\(v (zJ e a j)=true->v (uP e a j)=true/\v (uO a j)=true)/\(v (xR e a j)=true->v (uP e a j)=true/\v (wW a j)=true)
 op:∀e b a,e<14->b<kk k I (ep0N e)->a<kk k I (ep1N gi e)->v (yK e b a)=true->v (kI (ep0N e) b)=true/\v (kI (ep1N gi e) a)=true/\v (ur 0 e (ep0N e) b)=false/\v (ur 1 e (ep1N gi e) a)=false/\(∀y,y<10->v (kE (ep0N e) b y)=v (kD (ep1N gi e) a y))/\(∀y,y<10->v (kE (ep1N gi e) a y)=v (kD (ep0N e) b y))
 oq:0<m->(∀e z z2,e<14->z<10->z2<10->z≠z2->v (wM e z)=true->v (wM e z2)=false)/\(∀e z l0,e<14->z<10->l0<kk k I z->v (yM e z l0)=true->v (uP e z l0)=true/\(v (kD z l0 (ep0N e))=true\/v (kD z l0 (ep1N gi e))=true))
 or:0<m->∀u,u<64->vCx gi t c u=true->let cu:=qY c u;let tr:=yA t cu.1;(∀l0,l0<kk k I cu.2.2->v (wj u l0)=true->v (uP cu.2.1 cu.2.2 l0)=true/\v (kD cu.2.2 l0 tr.2.1)=false/\v (kD cu.2.2 l0 tr.2.2)=false/\(v (kD cu.2.2 l0 (ep0N tr.1))=true\/v (kD cu.2.2 l0 (ep1N gi tr.1))=true))/\(∀e2,e2<14->e2≠cu.2.1->v (vA u e2)=true->v (ux cu.2.1 e2)=true/\v (zH cu.1 e2)=true/\(v (kN 0 e2 cu.2.2)=true\/v (kN 1 e2 cu.2.2)=true))
 os:m=1->∀a,yR x a=true->∀z l0,z<10->l0<kk k I z->v (zE a z l0)=true->let d:=(uZ x a).1;v (kD z l0 (ep0N d))=true\/v (kD z l0 (ep1N gi d))=true
 ot:∀a j y l0,a<10->j<kk k I a->y<10->y≠a->kB I y=false->l0<kk k I y->(v (yJ a j y l0)=true->v (kI y l0)=true/\(∀d,d<10->v (kE a j d)=v (kE y l0 d))/\(∀d,d<10->v (kD a j d)=v (kD y l0 d)))/\(v (yL a j y l0)=true->v (kI y l0)=true/\(∀d,d<10->v (kE a j d)=v (kD y l0 d))/\(∀d,d<10->v (kD a j d)=v (kE y l0 d)))
 ou:m=1->∀i y n l0,i<10->kB I i=true->y<10->kB I y=false->adjB gi i y=false->n<3->n<(nbrsN gi i).length->let x0:=(nbrsN gi i).getD n 0;l0<kk k I x0->v (zF i y n l0)=true->v (xR (eIx gi i x0).1 x0 l0)=true/\v (uO x0 l0)=true/\v (kE x0 l0 y)=false/\(∀d,d<10->adjB gi i d=true->v (kE x0 l0 d)=true)
abbrev Unsat (gi:Fin 4)(k I m s:Nat)(t c x:List Nat):Prop:=∀(v:Nat->Bool),(∀a,enabled gi k I m s t c x a=true->Holds v (exS gi k I m t c x a))->OOK gi k I m t c x v->False
section OS
abbrev ul (C:OCtx)(v:Nat->Bool):=OOK C.gi C.k C.I C.m C.t C.c C.x v
lemma sA {a b:Bool}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma sO {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma sN {a:Bool}:((!a)=true)=(a=false):=Bool.not_eq_true' a
lemma sD {p:Prop}[Decidable p]:(decide p=true)=p:=decide_eq_true_eq
lemma tA {a b i:Nat}:(a&&&b).testBit i=(a.testBit i&&b.testBit i):=Nat.testBit_land a b i
lemma tO {a b i:Nat}:(a|||b).testBit i=(a.testBit i||b.testBit i):=Nat.testBit_lor a b i
lemma tX {a b i:Nat}:(a^^^b).testBit i=(a.testBit i^^b.testBit i):=Nat.testBit_xor a b i
lemma t2 {n i:Nat}:(2^n).testBit i=decide (n=i):=Nat.testBit_two_pow
lemma sL {a b:Nat}:a<<<b=a*2^b:=Nat.shiftLeft_eq a b
lemma oM {a:Nat}:1*a=a:=Nat.one_mul a
lemma nL {a b:Nat}:(¬a<b)↔b<=a:=Nat.not_lt
lemma mC {α}{a b:α}{l:List α}:(a∈b::l)↔(a=b\/a∈l):=List.mem_cons
lemma Ar {α}{a:α}{l:List α}:a∈a::l:=List.mem_cons_self
lemma As {α}{a:α}(b:α){l:List α}(h:a∈l):a∈b::l:=List.mem_cons_of_mem b h
lemma bF:(false=true)=False:=Bool.false_eq_true
lemma nF:(!false)=true:=Bool.not_false
lemma nT:(!true)=false:=Bool.not_true
lemma iT {α}(a b:α):(if True then a else b)=a:=ite_true a b
lemma iF {α}(a b:α):(if False then a else b)=b:=ite_false a b
lemma tL {a b i:Nat}:(a<<<b).testBit i=(decide (i>=b)&&a.testBit (i-b)):=Nat.testBit_shiftLeft a
lemma tR {a b i:Nat}:(a>>>b).testBit i=a.testBit (b+i):=Nat.testBit_shiftRight a
lemma lR {a n:Nat}:a∈List.range n↔a<n:=List.mem_range
lemma lM {α β}{f:α->β}{l:List α}{b:β}:b∈l.map f↔∃a∈l,f a=b:=List.mem_map
lemma zR {α β}{f:α->List β}{l:List α}{b:β}:b∈l.flatMap f↔∃a∈l,b∈f a:=List.mem_flatMap
lemma AZ {α}{a:α}{s t:List α}:a∈s++t↔a∈s\/a∈t:=List.mem_append
lemma Cd {α}{p:α->Bool}{a:α}{l:List α}:a∈l.filter p↔a∈l/\p a=true:=List.mem_filter
lemma At {α}{a b:α}:a∈[b]↔a=b:=List.mem_singleton
@[local simp] lemma xO (a b:Nat):a.add b=a+b:=rfl
@[local simp] lemma kJ (a b:Nat):a.sub b=a-b:=rfl
@[local simp] lemma wT (a b:Nat):a.mul b=a*b:=rfl
@[local simp] lemma kK (a b:Nat):a.div b=a/b:=rfl
@[local simp] lemma kL (a b:Nat):a.mod b=a % b:=rfl
@[local simp] lemma yX (a b:Nat):a.lor b=a|||b:=rfl
@[local simp] lemma wA (a b:Nat):a.land b=a&&&b:=rfl
@[local simp] lemma zP (a b:Nat):a.xor b=a^^^b:=rfl
@[local simp] lemma vY (a b:Nat):a.shiftLeft b=a<<<b:=rfl
@[local simp] lemma B9 (a b:Nat):a.shiftRight b=a>>>b:=rfl
lemma xJ {a b:Nat}:a.beq b=true↔a=b:=Iff.of_eq Nat.beq_eq
lemma qN {a b:Nat}:a.beq b=false↔a≠b:=by rw[←Bool.not_eq_true,Nat.beq_eq]
lemma kd {a b:Nat}:a.blt b=true↔a<b:=Iff.of_eq Nat.blt_eq
lemma vO {a b:Nat}:a.blt b=false↔b<=a:=by rw[←Bool.not_eq_true,Nat.blt_eq,nL]
def kW (v:Nat->Bool)(a b:Nat):Prop:=(∀x (p:Bool),x<1940->a.testBit (2*x+p.toNat)=true->v x=p)/\(∀x (p:Bool),1940<=x->b.testBit (2*(x-1940)+p.toNat)=true->v x=p)
def uk (v:Nat->Bool)(ps:List (Nat×Nat×Nat)):Prop:=∀p∈ps,p.1+10<=1940/\p.2.1+10<=1940/\∀y<10,v (p.1+y)=v (p.2.1+y)
def xF (v:Nat->Bool)(E:wQ):Prop:=uk v E.e0/\uk v E.e1/\uk v E.e2/\uk v E.e3/\uk v E.e4/\uk v E.e5/\uk v E.e6/\uk v E.e7
def wU (v:Nat->Bool)(imps:List (Nat×Nat×Nat)):Prop:=∀p∈imps,p.1+10<=1940/\p.2.1+10<=1940/\∀y<10,v (p.1+y)=true->v (p.2.1+y)=true
def uu (v:Nat->Bool)(st:St):Prop:=kW v st.a st.b/\xF v st.eqs/\wU v st.imps
abbrev uv {α}(Q:α->Prop)(o:Option α):Prop:=(o=none->False)/\∀x,o=some x->Q x
lemma ud {α}{Q:α->Prop}{x}(h:Q x):uv Q (some x):=⟨(λ e=>nomatch e),fun _ e=>(by cases e;exact h)⟩
lemma kz {P:Prop}[Decidable P]{α}{Q:α->Prop}{a b:Option α}(h1:P->uv Q a)(h2:¬P->uv Q b):uv Q (if P then a else b):=by by_cases h:P<;>simp[h];{exact h1 h};{exact h2 h}
lemma qH {α β}{Q:α->Prop}{R:β->Prop}{o:Option α}{f:α->Option β}(ho:uv Q o)(hf:∀x,Q x->uv R (f x)):uv R (o.bind f):=by cases o with|none=>exact⟨(λ _=>ho.1 rfl),fun _ e=>nomatch e⟩|some x=>exact hf x (ho.2 x rfl)
lemma kG {P:Prop}[Decidable P]{a b:Bool}(h:(if P then a else b)=true):(P/\a=true)\/(¬P/\b=true):=by by_cases hp:P<;>simp[hp] at h ⊢<;>exact h
lemma qC {v l q}(hl:w2 v l)(hq:∀x∈q,w2 v x):∀x∈l::q,w2 v x:=λ _ hx=>(mC.mp hx).elim (λ e=>e▸hl) (hq _)
lemma xI {k I x:Nat}(o0:k<=3):kk k I x<=5:=by unfold kk;split<;>omega
lemma AF {e:Nat}(he:e<14):ep0N e<10:=(by decide +kernel:∀u:Fin 14,ep0N u.1<10) ⟨e,he⟩
lemma AE {gi:Fin 4}{e:Nat}(he:e<14):ep1N gi e<10:=(by decide +kernel:∀g:Fin 4,∀u:Fin 14,ep1N g u.1<10) gi ⟨e,he⟩
lemma Ao {gi:Fin 4}{i n:Nat}(hi:i<10)(hn:n<(nbrsN gi i).length):(nbrsN gi i).getD n 0<10:=by
 have h:∀g:Fin 4,∀u:Fin 10,∀j:Fin 5,j.1<(nbrsN g u.1).length->(nbrsN g u.1).getD j.1 0<10:=by decide +kernel
 have hl:∀g:Fin 4,∀u:Fin 10,(nbrsN g u.1).length<5:=by decide +kernel
 exact h gi ⟨i,hi⟩ ⟨n,Nat.lt_trans hn (hl gi ⟨i,hi⟩)⟩ hn
lemma An {gi:Fin 4}{i y:Nat}(hi:i<10)(hy:y∈nbrsN gi i):y<10/\adjB gi i y=true:=by
 have h:∀g:Fin 4,∀u:Fin 10,(nbrsN g u.1).all (λ z=>decide (z<10)&&adjB g u.1 z)=true:=by decide +kernel
 simpa[sA,sD] using List.all_eq_true.mp (h gi ⟨i,hi⟩) y hy
lemma BM {gi:Fin 4}{a b:Nat}(ha:a<10)(hb:b<10):(eIx gi a b).1<14:=(by decide +kernel:∀g:Fin 4,∀u v:Fin 10,(eIx g u.1 v.1).1<14) gi ⟨a,ha⟩ ⟨b,hb⟩
lemma qL (x j y:Nat):kE x j 0+y=kE x j y:=by unfold kE;omega
lemma qJ (x j y:Nat):kD x j 0+y=kD x j y:=by unfold kD;omega
lemma qE (s e y:Nat):kN s e 0+y=kN s e y:=by unfold kN;omega
lemma BH (t y:Nat):kQ t 0+y=kQ t y:=by unfold kQ;omega
lemma qK {x j:Nat}(hx:x<10)(hj:j<5):kE x j 0+10<=1940:=by unfold kE;omega
lemma qI {x j:Nat}(hx:x<10)(hj:j<5):kD x j 0+10<=1940:=by unfold kD;omega
lemma qB {s e:Nat}(hs:s<2)(he:e<14):kN s e 0+10<=1940:=by unfold kN;omega
lemma BG {t:Nat}(ht:t<3):kQ t 0+10<=1940:=by unfold kQ;omega
lemma xP {v a b x p}(hb:kW v a b)(h:gB a b x p=true):v x=p:=by unfold gB at h;split at h<;>rename_i c<;>[exact hb.1 x p (kd.mp c) (by simpa using h);exact hb.2 x p (by rw[kd,nL] at c;exact c) (by simpa using h)]
lemma up {v a b x}(hb:kW v a b)(hx:x<1940)(hv:v x=true)(ht:a.testBit (Nat.mul 2 x)=true):False:=by have:=hb.1 x false hx (by simpa using ht);rw[hv] at this;cases this
lemma yW {v a b x}(hb:kW v a b)(hx:x<1940)(hv:v x=false)(ht:a.testBit ((Nat.mul 2 x).add 1)=true):False:=by have:=hb.1 x true hx (by simpa using ht);rw[hv] at this;cases this
lemma wH {v a b x p}(hb:kW v a b)(hv:v x=p)(hg:gB a b x (!p)=true):False:=by have:=xP hb hg;rw[hv] at this;cases p<;>cases this
lemma Bj {v a b x p}(hb:kW v a b)(hv:v x=p):kW v (zO a b x p).1 (zO a b x p).2:=by
 unfold zO;split<;>rename_i c
 · refine⟨fun y q hy h=>?_,hb.2⟩;simp only[yX,vY,xO,wT,tO,sL,oM,t2,sO,sD] at h
   rcases h with h1|h2;· exact hb.1 y q hy h1
   · have ex:x=y:=by cases p<;>cases q<;>simp[Bool.toNat] at h2<;>omega
     have ep:p=q:=by cases p<;>cases q<;>simp[Bool.toNat] at h2 ⊢<;>omega
     subst ex;subst ep;exact hv
 · refine⟨hb.1,fun y q hy h=>?_⟩;rw[kd,nL] at c
   simp only[yX,vY,xO,wT,kJ,tO,sL,oM,t2,sO,sD] at h
   rcases h with h1|h2;· exact hb.2 y q hy h1
   · have ex:x=y:=by cases p<;>cases q<;>simp[Bool.toNat] at h2<;>omega
     have ep:p=q:=by cases p<;>cases q<;>simp[Bool.toNat] at h2 ⊢<;>omega
     subst ex;subst ep;exact hv
lemma uD' {x:Nat}(h:x≠0):∃k,x.testBit k=true:=by
 by_contra hn;push Not at hn;apply h;apply Nat.eq_of_testBit_eq;intro k;simp[Bool.eq_false_iff.mpr (hn k)]
lemma uD {x:Nat}(h:!(x.beq 0)=true):∃k,x.testBit k=true:=by
 cases hx:x.beq 0;{exact uD' (qN.mp hx)};{rw[hx] at h;cases h}
lemma vS {n k:Nat}(hl:n<2^20)(o0:¬k<20):n.testBit k=false:=Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by omega) (by omega:20<=k)))
lemma Ap (k:Nat):ye.testBit k=decide (k<20):=by by_cases o0:k<20;{exact ((by decide +kernel:∀u:Fin 20,ye.testBit u.1=true) ⟨k,o0⟩).trans (by simp[o0])};{simp[o0,vS (by decide +kernel:ye<2^20) o0]}
lemma uf (k:Nat):uS.testBit k=decide (k<20/\k % 2=0):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀u:Fin 20,uS.testBit u.1=decide (u.1 % 2=0)) ⟨k,o0⟩};{simp[o0,vS (by decide +kernel:uS<2^20) o0]}
lemma uC (k:Nat):uR.testBit k=decide (k<20/\k % 2=1):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀u:Fin 20,uR.testBit u.1=decide (u.1 % 2=1)) ⟨k,o0⟩};{simp[o0,vS (by decide +kernel:uR<2^20) o0]}
lemma AL (gi:Fin 4){c:Nat}(hc:c<16)(k:Nat):(Ba gi c).testBit k=(decide (k<20/\k % 2=0)&&(aMk gi c).testBit (k/2)):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀g:Fin 4,∀a:Fin 16,∀u:Fin 20,(Ba g a.1).testBit u.1=(decide (u.1 % 2=0)&&(aMk g a.1).testBit (u.1/2))) gi ⟨c,hc⟩ ⟨k,o0⟩};{simp[o0,vS ((by decide +kernel:∀g:Fin 4,∀a:Fin 16,Ba g a.1<2^20) gi ⟨c,hc⟩) o0]}
lemma BP (gi:Fin 4){c:Nat}(hc:c<16)(k:Nat):(A9 gi c).testBit k=(decide (k<20/\k % 2=1)&&(aMk gi c).testBit (k/2)):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀g:Fin 4,∀a:Fin 16,∀u:Fin 20,(A9 g a.1).testBit u.1=(decide (u.1 % 2=1)&&(aMk g a.1).testBit (u.1/2))) gi ⟨c,hc⟩ ⟨k,o0⟩};{simp[o0,vS ((by decide +kernel:∀g:Fin 4,∀a:Fin 16,A9 g a.1<2^20) gi ⟨c,hc⟩) o0]}
lemma Bv (gi:Fin 4){i:Nat}(hi:i<10)(k:Nat):(AX gi i).testBit k=(decide (k<20/\k % 2=0)&&adjB gi i (k/2)):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀g:Fin 4,∀a:Fin 10,∀u:Fin 20,(AX g a.1).testBit u.1=(decide (u.1 % 2=0)&&adjB g a.1 (u.1/2))) gi ⟨i,hi⟩ ⟨k,o0⟩};{simp[o0,vS ((by decide +kernel:∀g:Fin 4,∀a:Fin 10,AX g a.1<2^20) gi ⟨i,hi⟩) o0]}
lemma Ai (gi:Fin 4){i:Nat}(hi:i<10)(k:Nat):(AW gi i).testBit k=(decide (k<20/\k % 2=1)&&adjB gi i (k/2)):=by by_cases o0:k<20;{simpa[o0] using (by decide +kernel:∀g:Fin 4,∀a:Fin 10,∀u:Fin 20,(AW g a.1).testBit u.1=(decide (u.1 % 2=1)&&adjB g a.1 (u.1/2))) gi ⟨i,hi⟩ ⟨k,o0⟩};{simp[o0,vS ((by decide +kernel:∀g:Fin 4,∀a:Fin 10,AW g a.1<2^20) gi ⟨i,hi⟩) o0]}
lemma yD (a v k:Nat):(qR a v).testBit k=(decide (k<20)&&a.testBit (2*v+k)):=by unfold qR;simp only[wA,B9,wT,tA,tR,Ap,Bool.and_comm]
lemma kY {a v k:Nat}(h:(qR a v).testBit k=true):k<20/\a.testBit (2*v+k)=true:=by simpa[yD,sA,sD] using h
lemma yC (b k:Nat):(wZ b).testBit k=if k<20 then b.testBit (if k % 2=0 then k+1 else k-1) else false:=by
 unfold wZ;simp only[yX,vY,wA,B9,tO,tL,tA,tR,uf]
 by_cases o0:k<20
 · simp only[o0,iT];by_cases hp:k % 2=0
   · simp[hp,Nat.add_comm 1 k];intro h1 _ h2 h3;omega
   · have h1:k≥1:=(by omega);have h2:k-1<20/\(k-1) % 2=0:=(by omega);simp[hp,h1,h2]
 · simp[o0];intro h1 _ h2;omega
lemma kZ {v a b u w}(hb:kW v a b)(hu:u+10<=1940)(hw:w+10<=1940)(he:∀y<10,v (u+y)=v (w+y))(hc:ug a u w=true):False:=by
 obtain⟨k,o0⟩:=uD hc;simp only[wA,tA,sA] at o0
 obtain⟨hk20,h1⟩:=kY o0.1;simp only[yC,hk20,iT] at o0;obtain⟨_,h2⟩:=kY o0.2
 let y:=k/2;have hy:y<10:=by omega
 by_cases hp:k % 2=0
 · simp only[hp,iT] at h2
   have w1:=hb.1 (u+y) false (by omega) ((by simp[Bool.toNat,y];omega:2*u+k=2*(u+y)+false.toNat)▸h1)
   have w2:=hb.1 (w+y) true (by omega) ((by simp[Bool.toNat,y];omega:2*w+(k+1)=2*(w+y)+true.toNat)▸h2)
   have:=he y hy;rw[w1,w2] at this;cases this
 · simp only[hp,iF] at h2
   have w1:=hb.1 (u+y) true (by omega) ((by simp[Bool.toNat,y];omega:2*u+k=2*(u+y)+true.toNat)▸h1)
   have w2:=hb.1 (w+y) false (by omega) ((by simp[Bool.toNat,y];omega:2*w+(k-1)=2*(w+y)+false.toNat)▸h2)
   have:=he y hy;rw[w1,w2] at this;cases this
lemma vE {v a b u m}(hb:kW v a b)(hu:u+10<=1940)(hm20:∀k,20<=k->m.testBit k=false)(hmok:∀y<10,∀q:Bool,m.testBit (2*y+q.toNat)=true->v (u+y)=q):uv (λ a'=>kW v a' b) (vV a u m):=by
 unfold vV;apply kz
 · intro hc;refine⟨fun _=>?_,fun _ e=>nomatch e⟩
   obtain⟨k,o0⟩:=uD hc;simp only[wA,tA,sA] at o0
   obtain⟨hk20,h1⟩:=kY o0.1;simp only[yC,hk20,iT] at o0;let y:=k/2;have hy:y<10:=by omega
   by_cases hp:k % 2=0
   · simp only[hp,iT] at o0
     have w1:=hb.1 (u+y) false (by omega) ((by simp[Bool.toNat,y];omega:2*u+k=2*(u+y)+false.toNat)▸h1)
     have w2:=hmok y hy true ((by simp[Bool.toNat,y];omega:k+1=2*y+true.toNat)▸o0.2);rw[w1] at w2;cases w2
   · simp only[hp,iF] at o0
     have w1:=hb.1 (u+y) true (by omega) ((by simp[Bool.toNat,y];omega:2*u+k=2*(u+y)+true.toNat)▸h1)
     have w2:=hmok y hy false ((by simp[Bool.toNat,y];omega:k-1=2*y+false.toNat)▸o0.2);rw[w1] at w2;cases w2
 · intro _;apply ud;refine⟨fun x p hx ht=>?_,hb.2⟩
   simp only[yX,vY,wT,tO,tL,sO,sA,sD] at ht
   rcases ht with h1|⟨hge,h2⟩;· exact hb.1 x p hx h1
   · have hlt:2*x+p.toNat-2*u<20:=by by_contra hg;rw[hm20 _ (by omega)] at h2;cases h2
     have hxu:u<=x:=by cases p<;>simp[Bool.toNat] at hge<;>omega
     let y:=x-u;have hy:y<10:=by cases p<;>simp[Bool.toNat] at hlt<;>omega
     exact (by omega:u+y=x)▸hmok y hy p ((by cases p<;>simp[Bool.toNat,y]<;>omega:2*x+p.toNat-2*u=2*y+p.toNat)▸h2)
lemma AK (m n a k:Nat):(qP.go m n a).testBit k=(a.testBit k||(decide (k<2*n/\k % 2=0)&&m.testBit (k/2))):=by
 induction n generalizing a with
 | zero=>simp[qP.go]
 | succ n ih=>
   simp only[qP.go,ih];by_cases hm:m.testBit n=true
   · simp only[hm,iT,yX,vY,wT,tO,sL,oM,t2]
     by_cases o0:k=2*n;· subst o0;simp[hm]
     · have he:decide (k<2*(n+1)/\k % 2=0)=decide (k<2*n/\k % 2=0):=by simp only[decide_eq_decide];omega
       have hne:decide (2*n=k)=false:=decide_eq_false (λ h=>o0 h.symm)
       simp[hne,he]
   · simp only[hm]
     by_cases o0:k=2*n;· subst o0;simp[hm]
     · have he:decide (k<2*(n+1)/\k % 2=0)=decide (k<2*n/\k % 2=0):=by simp only[decide_eq_decide];omega
       simp[he]
lemma xK (m k:Nat):(qP m).testBit k=(decide (k<20/\k % 2=0)&&m.testBit (k/2)):=by unfold qP;rw[AK];simp
lemma AJ (m k:Nat):(qF m).testBit k=(decide (k<20/\k % 2=1)&&m.testBit (k/2)):=by
 unfold qF;simp only[vY,tL,xK]
 by_cases o0:k<20/\k % 2=1
 · have h1:k≥1:=(by omega);have h2:k-1<20/\(k-1) % 2=0:=(by omega);have h3:(k-1)/2=k/2:=(by omega);simp[o0,h1,h2,h3]
 · simp only[o0,decide_false,Bool.false_and];exact Bool.eq_false_iff.mpr (λ hm=>by simp at hm;omega)
lemma Bd {v b eqs a dm nd}(hb:kW v a b)(heq:uk v eqs):uv (λ p=>kW v p.1 b) (wG eqs a dm nd):=by
 induction eqs generalizing a dm nd with
 | nil=>exact ud (Q:=λ p:Nat×Nat=>kW v p.1 b) hb
 | cons p r ih=>
   rcases p with ⟨u,w,m⟩;have hp:=heq (u,w,m) Ar;dsimp only at hp;have hr:uk v r:=λ q hq=>heq q (As _ hq)
   simp only[wG];apply kz;· intro _;exact ih hb hr
   · intro _;apply kz;· intro _;exact ih hb hr
     · intro _;apply kz;· intro hc;exact⟨(λ _=>kZ hb hp.1 hp.2.1 hp.2.2 hc),fun _ e=>nomatch e⟩
       · intro _;refine ih ⟨fun x q hx ht=>?_,hb.2⟩ hr
         simp only[yX,vY,wT,tO,tL,sO,sA,sD] at ht
         rcases ht with h0|(⟨hge,h1⟩|⟨hge,h2⟩);· exact hb.1 x q hx h0
         · obtain⟨hk20,ha⟩:=kY h1;have hxw:w<=x:=by cases q<;>simp[Bool.toNat] at hge<;>omega
           let y:=x-w;have hy:y<10:=by cases q<;>simp[Bool.toNat] at hk20<;>omega
           have w1:=hb.1 (u+y) q (by omega) ((by cases q<;>simp[Bool.toNat,y]<;>omega:2*u+(2*x+q.toNat-2*w)=2*(u+y)+q.toNat)▸ha)
           rw[←(by omega:w+y=x),←hp.2.2 y hy];exact w1
         · obtain⟨hk20,ha⟩:=kY h2;have hxu:u<=x:=by cases q<;>simp[Bool.toNat] at hge<;>omega
           let y:=x-u;have hy:y<10:=by cases q<;>simp[Bool.toNat] at hk20<;>omega
           have w2:=hb.1 (w+y) q (by omega) ((by cases q<;>simp[Bool.toNat,y]<;>omega:2*w+(2*x+q.toNat-2*u)=2*(w+y)+q.toNat)▸ha)
           rw[←(by omega:u+y=x),hp.2.2 y hy];exact w2
lemma un {v b e mk a dm nd}(hb:kW v a b)(he:uk v e):uv (λ p=>kW v p.1 b) (vg e mk a dm nd):=
 kz (λ _=>ud (Q:=λ p:Nat×Nat=>kW v p.1 b) hb) (λ _=>Bd hb he)
lemma zZ {v b E a dm}(hb:kW v a b)(he:xF v E):uv (λ p=>kW v p.1 b) (Aa E a dm):=
 qH (un hb he.1) λ _ h0=>qH (un h0 he.2.1) λ _ h1=>qH (un h1 he.2.2.1) λ _ h2=>qH (un h2 he.2.2.2.1) λ _ h3=>qH (un h3 he.2.2.2.2.1) λ _ h4=>qH (un h4 he.2.2.2.2.2.1) λ _ h5=>qH (un h5 he.2.2.2.2.2.2.1) λ _ h6=>un h6 he.2.2.2.2.2.2.2
lemma Bc {v b imps a dm nd}(hb:kW v a b)(himp:wU v imps):uv (λ p=>kW v p.1 b) (wF imps a dm nd):=by
 induction imps generalizing a dm nd with
 | nil=>exact ud (Q:=λ p:Nat×Nat=>kW v p.1 b) hb
 | cons p r ih=>
   rcases p with ⟨u,w,m⟩;have hp:=himp (u,w,m) Ar;dsimp only at hp;have hr:wU v r:=λ q hq=>himp q (As _ hq)
   simp only[wF];apply kz;· intro _;exact ih hb hr
   · intro _;apply kz
     · intro hc;refine⟨fun _=>?_,fun _ e=>nomatch e⟩
       obtain⟨k,o0⟩:=uD hc;simp only[wA,vY,tA,tL,uC,uf,yD,sA,sD] at o0
       obtain⟨⟨⟨hk20,h1⟩,_,hodd⟩,hge1,⟨_,h2⟩,_,_⟩:=o0;let y:=k/2;have hy:y<10:=by omega
       have w1:=hb.1 (u+y) true (by omega) ((by simp[Bool.toNat,y];omega:2*u+k=2*(u+y)+true.toNat)▸h1)
       have w2:=hb.1 (w+y) false (by omega) ((by simp[Bool.toNat,y];omega:2*w+(k-1)=2*(w+y)+false.toNat)▸h2)
       have:=hp.2.2 y hy w1;rw[w2] at this;cases this
     · intro _;apply kz;· intro _;exact ih hb hr
       · intro _;refine ih ⟨fun x q hx ht=>?_,hb.2⟩ hr
         simp only[yX,vY,wA,wT,tO,tL,tA,uC,uf,sO,sA,sD] at ht
         rcases ht with h0|(⟨hge,hs,h20,hodd⟩|⟨hge,hs,h20,hev⟩);· exact hb.1 x q hx h0
         · have hq:q=true:=by cases q;{simp[Bool.toNat] at hge hodd;omega};{rfl}
           subst hq;have hxw:w<=x:=by simp[Bool.toNat] at hge;omega
           let y:=x-w;have hy:y<10:=by simp[Bool.toNat] at h20;omega
           have w1:=hb.1 (u+y) true (by omega) ((by simp[Bool.toNat,y];omega:2*u+(2*x+true.toNat-2*w)=2*(u+y)+true.toNat)▸(kY hs).2)
           exact (by omega:w+y=x)▸hp.2.2 y hy w1
         · have hq:q=false:=by cases q;{rfl};{simp[Bool.toNat] at hge hev;omega}
           subst hq;have hxu:u<=x:=by simp[Bool.toNat] at hge;omega
           let y:=x-u;have hy:y<10:=by simp[Bool.toNat] at h20;omega
           have w2:=hb.1 (w+y) false (by omega) ((by simp[Bool.toNat,y];omega:2*w+(2*x+false.toNat-2*u)=2*(w+y)+false.toNat)▸(kY hs).2)
           cases hvx:v x;{rfl};{have:=hp.2.2 y hy ((by omega:u+y=x).symm▸hvx);rw[w2] at this;cases this}
lemma Ab {v b E imps im f a dm}(hb:kW v a b)(heq:xF v E)(himp:wU v imps):uv (λ a'=>kW v a' b) (wY E imps im f a dm):=by
 induction f generalizing a dm with
 | zero=>exact ud (Q:=λ a'=>kW v a' b) hb
 | succ f ih=>simp only[wY];exact kz (λ _=>ud (Q:=λ a'=>kW v a' b) hb) λ _=>qH (zZ hb heq) λ p1 h1=>qH (kz (λ _=>ud (Q:=λ p:Nat×Nat=>kW v p.1 b) h1) λ _=>Bc h1 himp) λ p2 h2=>kz (λ _=>ud (Q:=λ a'=>kW v a' b) h2) λ _=>ih h2
lemma kV {v st}(hs:uu v st):uv (uu v) (kR st):=by
 unfold kR;exact kz (λ _=>ud hs) λ _=>by cases h:wY st.eqs st.imps st.im 10 st.a st.dm with| none=>exact⟨(λ _=>(Ab hs.1 hs.2.1 hs.2.2).1 h),fun _ e=>nomatch e⟩| some a'=>exact ud ⟨(Ab hs.1 hs.2.1 hs.2.2).2 a' h,hs.2.1,hs.2.2⟩
lemma AM {v ps u w m}(h:uk v ps)(h1:u+10<=1940)(h2:w+10<=1940)(hp:∀y<10,v (u+y)=v (w+y)):uk v (ut ps u w m):=by
 unfold ut;split;{exact h};{intro q hq;rcases mC.mp hq with rfl|h';exact⟨h1,h2,hp⟩;exact h q h'}
lemma qG {v E u w}(h:xF v E)(h1:u+10<=1940)(h2:w+10<=1940)(hp:∀y<10,v (u+y)=v (w+y)):xF v (kX E u w):=by
 unfold kX;dsimp only
 have h':(if u.blt w then u else w)+10<=1940/\(if u.blt w then w else u)+10<=1940/\∀y<10,v ((if u.blt w then u else w)+y)=v ((if u.blt w then w else u)+y):=by split<;>[exact⟨h1,h2,hp⟩;exact⟨h2,h1,fun y hy=>(hp y hy).symm⟩]
 split<;>refine⟨?_,?_,?_,?_,?_,?_,?_,?_⟩<;>first|exact h.1|exact h.2.1|exact h.2.2.1|exact h.2.2.2.1|exact h.2.2.2.2.1|exact h.2.2.2.2.2.1|exact h.2.2.2.2.2.2.1|exact h.2.2.2.2.2.2.2|exact AM (by first|exact h.1|exact h.2.1|exact h.2.2.1|exact h.2.2.2.1|exact h.2.2.2.2.1|exact h.2.2.2.2.2.1|exact h.2.2.2.2.2.2.1|exact h.2.2.2.2.2.2.2) h'.1 h'.2.1 h'.2.2
lemma zL {v imps im u w}(himp:wU v imps)(h1:u+10<=1940)(h2:w+10<=1940)(hp:∀y<10,v (u+y)=true->v (w+y)=true):wU v (xM imps im u w).1:=by
 unfold xM ut;dsimp only;split;{exact himp};{intro q hq;rcases mC.mp hq with rfl|h';exact⟨h1,h2,hp⟩;exact himp q h'}
lemma xL {v a b x y n}(hb:kW v a b)(hx:x<10)(hn:n<=5)(hy:y<10)(h:uY a x y n=true):∃j<n,v (kE x j y)=true:=by
 induction n with| zero=>simp[uY] at h| succ n ih=>
   simp only[uY,sO] at h;rcases h with h1|h2
   · exact⟨n,by omega,hb.1 (kE x n y) true (by unfold kE;omega) (by simpa using h1)⟩
   · obtain⟨j,hj,hv⟩:=ih (by omega) h2;exact⟨j,by omega,hv⟩
lemma zK {v a b e z n}(hb:kW v a b)(h:vP a b e z n=true):∃u<n,u≠z/\v (wM e u)=true:=by
 induction n with| zero=>simp[vP] at h| succ n ih=>
   simp only[vP,sO,sA,sN,qN] at h
   rcases h with ⟨hne,hg⟩|h2;{exact⟨n,by omega,hne,xP hb hg⟩};{obtain⟨u,hu,hne,hv⟩:=ih h2;exact⟨u,by omega,hne,hv⟩}
lemma xo {C:OCtx}{v a b u w}(hO:ul C v)(hb:kW v a b)(h:xw a b u w=true):v (uK u w)=false:=by
 unfold xw at h;simp only[sA,sO,kd,sN,qN] at h
 obtain⟨⟨⟨hu,hw⟩,hne⟩,h1|h2⟩:=h
 · exact (hO.on u w hu hw hne).2 (xP hb h1) |>.2
 · rw[(by unfold uK;omega:uK u w=uK w u)];exact (hO.on w u hw hu hne.symm).2 (xP hb h2) |>.2
lemma yH {C:OCtx}{v a b u w}(hO:ul C v)(hb:kW v a b)(h:xX a b u w=true):v (ux u w)=false:=by
 unfold xX at h;simp only[sA,sO,kd,sN,qN] at h
 obtain⟨⟨⟨hu,hw⟩,hne⟩,h1|h2⟩:=h
 · exact (hO.on u w hu hw hne).1 (xP hb h1)
 · exact (hO.on w u hw hu hne.symm).2 (xP hb h2) |>.1
lemma uV {C:OCtx}{v a b e x j}(hO:ul C v)(hb:kW v a b)(h:vJ C a b e x j=true):v (uP e x j)=false:=by
 unfold vJ at h;simp only[sO,sA,kd] at h
 rcases h with h0|⟨⟨⟨he,hx⟩,hj⟩,h1⟩;· exact xP hb h0
 · have hj5:j<5:=Nat.lt_of_lt_of_le hj (xI hO.o0);cases hv:v (uP e x j);· rfl
   · have ha:=(hO.oo e x j he hx hj).1 hv
     rcases h1 with (hL|hR0)|hR1;{exact (up hb (by unfold kI;omega) ha.1 hL).elim};{exact (wH hb ha.2.1 hR0).elim};{exact (wH hb ha.2.2 hR1).elim}
lemma xA {C:OCtx}{v a b x j}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(h:xB C a b x j=true):v (uO x j)=false:=by
 unfold xB at h;simp only[sO,sA,kd] at h
 rcases h with h0|⟨⟨hx,hj⟩,h1⟩;· exact xP hb h0
 · have hj5:j<5:=Nat.lt_of_lt_of_le hj (xI hO.o0);cases hv:v (uO x j);· rfl
   · rcases h1 with hL|hO1;· exact (up hb (by unfold kI;omega) ((hO.ov x j hx hj).1 hv) hL).elim
     · obtain⟨k0,hk0⟩:=uD hO1;simp only[wA,zP,vY,xO,wT,tA,tX,uC,hIo,AJ,sL,oM,t2,sA,sD] at hk0
       obtain⟨⟨hs,hk20,hodd⟩,hxr⟩:=hk0;let y:=k0/2;have hy:y<10:=by omega
       have hiy:kB C.I y=true:=by unfold kB;cases hI:C.I.testBit y<;>simp[hI,hk20,hodd,y] at hxr ⊢
       have hxy:x≠y:=by intro he;subst he;have o0:2*y+1=k0:=(by omega);simp[hk20,hodd,o0,y] at hxr
       have hop:=hb.1 (kD x j y) true (by unfold kD;omega) ((by unfold kD;simp[Bool.toNat,y];omega:2*kD x j 0+k0=2*kD x j y+true.toNat)▸(kY hs).2)
       have hnf:=(hO.og x j y hx hj hy hiy hxy hop).1;rw[hv] at hnf;cases hnf
lemma xC {C:OCtx}{v a b x j}(hO:ul C v)(hb:kW v a b)(h:xD C a b x j=true):v (wW x j)=false:=by
 unfold xD at h;simp only[sO,sA,kd] at h
 rcases h with h0|⟨⟨hx,hj⟩,h1⟩;· exact xP hb h0
 · have hj5:j<5:=Nat.lt_of_lt_of_le hj (xI hO.o0);cases hv:v (wW x j);· rfl
   · have hem:=(hO.ov x j hx hj).2 hv
     rcases h1 with hL|hO1;· exact (up hb (by unfold kI;omega) hem.1 hL).elim
     · obtain⟨k0,hk0⟩:=uD hO1;simp only[wA,tA,uC,sA,sD] at hk0
       obtain⟨hs,hk20,hodd⟩:=hk0;let y:=k0/2;have hy:y<10:=by omega
       have hop:=hb.1 (kD x j y) true (by unfold kD;omega) ((by unfold kD;simp[Bool.toNat,y];omega:2*kD x j 0+k0=2*kD x j y+true.toNat)▸(kY hs).2)
       rw[hem.2 y hy] at hop;cases hop
lemma Az {C:OCtx}{v a b vr}(hO:ul C v)(hb:kW v a b)(hr:vr<1050)(hw:v vr=true)(hf:zA C a b vr=true):False:=by
 unfold zA at hf;rcases kG hf with ⟨h50,hf⟩|⟨h50,hf⟩
 · rw[kd] at h50;simp only[sA,sO,kd,sN,qN,xJ,xO,kJ,kK,kL] at hf
   set x:=vr/5;set j:=vr % 5;have hj5:j<5:=(by omega);rw[(by unfold kI;omega:vr=kI x j)] at hw
   rcases hf.2 with (⟨hj0,hp⟩|hs)|⟨⟨hjk,hni⟩,hhm⟩
   · exact up hb (by unfold kI;omega) (hO.o3 x (j-1) hf.1.1 (by omega) (by simpa[Nat.sub_add_cancel (by omega:1<=j)] using hw)) hp
   · exact up hb (by unfold kE;omega) (hO.o2 x j hf.1.1 hf.1.2 hw) hs
   · exact yW hb (by unfold vK;omega) (by cases hh:v (vK x);{rfl};{have:=hO.oc x hf.1.1 hni hh;rw[←hjk,hw] at this;cases this}) hhm
 · rw[kd,nL] at h50;rcases kG hf with ⟨h550,hf⟩|⟨h550,hf⟩
   · rw[kd] at h550;simp only[sA,sO,kd,kJ,kK,kL] at hf
     set x:=(vr-50)/10/5;set j:=(vr-50)/10 % 5;set y:=(vr-50) % 10;have hj5:j<5:=(by omega)
     rw[(by unfold kE;omega:vr=kE x j y)] at hw
     rcases hf.2 with hL|hC
     · exact up hb (by unfold kI;omega) (hO.o4 x j y hf.1.1.1 hf.1.1.2 hf.1.2 hw) hL
     · exact up hb (by unfold vC;omega) (hO.o5 x j y hf.1.1.1 hf.1.1.2 hf.1.2 hw) hC
   · rw[kd,nL] at h550;simp only[sA,sO,kd,sN,qN,kJ,kK,kL] at hf
     set x:=(vr-550)/10/5;set j:=(vr-550)/10 % 5;set y:=(vr-550) % 10;have hj5:j<5:=(by omega)
     rw[(by unfold kD;omega:vr=kD x j y)] at hw
     rcases hf.2 with (hL|hEm)|⟨⟨hiy,hne⟩,AB⟩
     · exact up hb (by unfold kI;omega) (hO.of x j y hf.1.1.1 hf.1.1.2 hf.1.2 hw) hL
     · have:=((hO.ov x j hf.1.1.1 hf.1.1.2).2 (xP hb hEm)).2 y hf.1.2;rw[hw] at this;cases this
     · have hin:=hO.og x j y hf.1.1.1 hf.1.1.2 hf.1.2 hiy hne hw
       rcases AB with (hFr|hOt)|hCf
       · exact wH hb hin.1 hFr
       · obtain⟨k0,hk0⟩:=uD' hOt;simp only[wA,zP,vY,xO,wT,tA,tX,uC,sL,oM,t2,sA,sD] at hk0
         obtain⟨⟨hs,hk20,hodd⟩,hxr⟩:=hk0;let d:=k0/2;have hd:d<10:=(by omega)
         have hdy:d≠y:=by intro he;have o0:2*y+1=k0:=(by omega);simp[hk20,hodd,o0] at hxr
         have h2:=hb.1 (kD x j d) true (by unfold kD;omega) ((by unfold kD;simp[Bool.toNat,d];omega:2*kD x j 0+k0=2*kD x j d+true.toNat)▸(kY hs).2)
         rw[hin.2.1 d hd hdy] at h2;cases h2
       · exact kZ hb (qK hf.1.1.1 hj5) (qI hf.1.2 (by omega)) (λ d hd=>by rw[qL,qJ];exact hin.2.2 d hd) hCf
lemma Ay {C:OCtx}{v a b vr}(hO:ul C v)(hb:kW v a b)(hr1:1050<=vr)(hr2:vr<3340)(hw:v vr=true)(hf:zx C a b vr=true):False:=by
 unfold zx at hf;rcases kG hf with ⟨h1940,hf⟩|⟨h1940,hf⟩
 · rw[kd] at h1940;rcases kG hf with ⟨_,hf⟩|⟨h1180,hf⟩;· cases hf
   rw[kd,nL] at h1180;rcases kG hf with ⟨h1480,hf⟩|⟨h1480,hf⟩
   · rw[kd] at h1480;simp only[sA,sO,kd,sN,qN,kJ,kK,kL] at hf
     set t:=(vr-1180)/100;set x:=(vr-1180) % 100/10;set y:=(vr-1180) % 100 % 10
     rw[(by unfold zG;omega:vr=zG t x y)] at hw;have hd:=hO.o9 t x y hf.1.1.1.1 hf.1.1.1.2 hf.1.1.2 hf.1.2 hw
     have o0:=hO.o0;rcases hf.2 with h1|h2;{exact up hb (by unfold kQ;omega) hd.1 h1};{exact yW hb (by unfold kQ;omega) hd.2 h2}
   · rw[kd,nL] at h1480;rcases kG hf with ⟨_,hf⟩|⟨h1500,hf⟩;· cases hf
     rw[kd,nL] at h1500;rcases kG hf with ⟨h1510,hf⟩|⟨h1510,hf⟩
     · rw[kd] at h1510;simp only[sA,kd,sN,kJ,xO] at hf
       set x:=vr-1500;rw[(by unfold vK;omega:vr=vK x)] at hw;exact yW hb (by unfold kI;omega) (hO.oc x hf.1.1.1 hf.1.1.2 hw) hf.2
     · rw[kd,nL] at h1510;rcases kG hf with ⟨h1660,hf⟩|⟨_,hf⟩;swap;· cases hf
       rw[kd] at h1660;simp only[sA,sO,kd,sN,kJ,kK,kL] at hf
       set t:=(vr-1510)/50;set x:=(vr-1510) % 50/5;set j:=(vr-1510) % 50 % 5;have hj5:j<5:=(by omega)
       rw[(by unfold xQ;omega:vr=xQ t x j)] at hw;have hr:=hO.od t x j hf.1.1.1.1 hf.1.1.1.2 hf.1.1.2 hf.1.2 hw
       rcases hf.2 with hL|hC;· exact up hb (by unfold kI;omega) hr.1 hL
       · obtain⟨k0,hk0⟩:=uD' (qN.mp hC);simp only[wA,vY,tA,tL,uC,uf,sA,sD] at hk0
         obtain⟨⟨hs1,hk20,hodd⟩,hge1,hs2,_,_⟩:=hk0;let y:=k0/2;have hy:y<10:=(by omega);have o0:=hO.o0
         have w1:=hb.1 (kQ t y) true (by unfold kQ;omega) ((by unfold kQ;simp[Bool.toNat,y];omega:2*kQ t 0+k0=2*kQ t y+true.toNat)▸(kY hs1).2)
         have w2:=hb.1 (kE x j y) false (by unfold kE;omega) ((by unfold kE;simp[Bool.toNat,y];omega:2*kE x j 0+(k0-1)=2*kE x j y+false.toNat)▸(kY hs2).2)
         have:=hr.2 y hy w1;rw[w2] at this;cases this
 · rw[kd,nL] at h1940;simp only[sA,sO,kd,kJ,kK,kL] at hf
   set s:=(vr-1940)/50/14;set e:=(vr-1940)/50 % 14;set x:=(vr-1940) % 50/5;set j:=(vr-1940) % 50 % 5;have hj5:j<5:=(by omega)
   rw[(by unfold ur;omega:vr=ur s e x j)] at hw;have hr:=hO.oj s e x j hf.1.1.1.1 hf.1.1.1.2 hf.1.1.2 hf.1.2 hw
   rcases hf.2 with (((((hL|hE1)|hE2)|hFr)|hAf)|hC1)|hC2
   · exact up hb (by unfold kI;omega) hr.1 hL
   · exact up hb (by unfold kN;omega) hr.2.1 hE1
   · exact yW hb (by unfold kN;omega) hr.2.2.1 hE2
   · exact wH hb hr.2.2.2.1 hFr
   · exact wH hb hr.2.2.2.2.1 hAf
   · exact kZ hb (qK hf.1.1.2 hj5) (qB hf.1.1.1.1 hf.1.1.1.2) (λ y hy=>by rw[qL,qE];exact hr.2.2.2.2.2.1 y hy) hC1
   · exact kZ hb (qI hf.1.1.2 hj5) (qB (by omega) hf.1.1.1.2) (λ y hy=>by rw[qJ,qE];exact hr.2.2.2.2.2.2 y hy) hC2
lemma Ax {C:OCtx}{v a b vr}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(hr1:3340<=vr)(hr2:vr<6688)(hw:v vr=true)(hf:zn C a b vr=true):False:=by
 unfold zn at hf;rcases kG hf with ⟨h3390,hf⟩|⟨h3390,hf⟩
 · rw[kd] at h3390;simp only[kJ,kK,kL] at hf;have:=xA hO hb hIo hf;rw[(by unfold uO;omega:vr=uO ((vr-3340)/5) ((vr-3340) % 5))] at hw;rw[hw] at this;cases this
 · rw[kd,nL] at h3390;rcases kG hf with ⟨h3440,hf⟩|⟨h3440,hf⟩
   · rw[kd] at h3440;simp only[kJ,kK,kL] at hf;have:=xC hO hb hf;rw[(by unfold wW;omega:vr=wW ((vr-3390)/5) ((vr-3390) % 5))] at hw;rw[hw] at this;cases this
   · rw[kd,nL] at h3440;rcases kG hf with ⟨h3636,hf⟩|⟨h3636,hf⟩
     · rw[kd] at h3636;simp only[sA,sO,kd,kJ,kK,kL] at hf
       set u:=(vr-3440)/14;set w:=(vr-3440) % 14;rw[(by unfold yN;omega:vr=yN u w)] at hw
       have hg:=(hO.om u w hf.1.1 hf.1.2).1 hw;rcases hf.2 with ((h1|h2)|h3)|h4
       · exact wH hb hg.1 h1
       · have:=xo hO hb h2;rw[hg.1] at this;cases this
       · exact kZ hb (qB (by omega) (by omega)) (qB (by omega) hf.1.2) (λ y hy=>by rw[qE,qE];exact hg.2.1 y hy) h3
       · exact kZ hb (qB (by omega) (by omega)) (qB (by omega) hf.1.2) (λ y hy=>by rw[qE,qE];exact hg.2.2 y hy) h4
     · rw[kd,nL] at h3636;rcases kG hf with ⟨h3832,hf⟩|⟨h3832,hf⟩
       · rw[kd] at h3832;simp only[sA,sO,kd,kJ,kK,kL] at hf
         set u:=(vr-3636)/14;set w:=(vr-3636) % 14;rw[(by unfold yO;omega:vr=yO u w)] at hw
         have hg:=(hO.om u w hf.1.1 hf.1.2).2 hw;rcases hf.2 with ((h1|h2)|h3)|h4
         · exact wH hb hg.1 h1
         · have:=xo hO hb h2;rw[hg.1] at this;cases this
         · exact kZ hb (qB (by omega) (by omega)) (qB (by omega) hf.1.2) (λ y hy=>by rw[qE,qE];exact hg.2.1 y hy) h3
         · exact kZ hb (qB (by omega) (by omega)) (qB (by omega) hf.1.2) (λ y hy=>by rw[qE,qE];exact hg.2.2 y hy) h4
       · rw[kd,nL] at h3832;rcases kG hf with ⟨h4028,hf⟩|⟨h4028,hf⟩
         · rw[kd] at h4028;simp only[sA,kd,kJ,kK,kL] at hf
           rw[(by unfold uK;omega:vr=uK ((vr-3832)/14) ((vr-3832) % 14))] at hw;have:=xo hO hb hf.2;rw[hw] at this;cases this
         · rw[kd,nL] at h4028;rcases kG hf with ⟨h4224,hf⟩|⟨h4224,hf⟩
           · rw[kd] at h4224;simp only[kJ,kK,kL] at hf;rw[(by unfold ux;omega:vr=ux ((vr-4028)/14) ((vr-4028) % 14))] at hw;have:=yH hO hb hf;rw[hw] at this;cases this
           · rw[kd,nL] at h4224;rcases kG hf with ⟨h4924,hf⟩|⟨h4924,hf⟩
             · rw[kd] at h4924;simp only[kJ,kK,kL] at hf;rw[(by unfold uP;omega:vr=uP ((vr-4224)/50) ((vr-4224) % 50/5) ((vr-4224) % 50 % 5))] at hw;have:=uV hO hb hf;rw[hw] at this;cases this
             · rw[kd,nL] at h4924;rcases kG hf with ⟨_,hf⟩|⟨h4938,hf⟩;· cases hf
               rw[kd,nL] at h4938;rcases kG hf with ⟨h5288,hf⟩|⟨h5288,hf⟩
               · rw[kd] at h5288;simp only[sA,sO,kd,kJ,kK,kL] at hf
                 set e:=(vr-4938)/25;set p:=(vr-4938) % 25/5;set q:=(vr-4938) % 25 % 5
                 rw[(by unfold yK;omega:vr=yK e p q)] at hw;have hs:=hO.op e p q hf.1.1.1 hf.1.1.2 hf.1.2 hw
                 have hu:=AF hf.1.1.1;have hw1:=AE (gi:=C.gi) hf.1.1.1;have hp5:p<5:=(by omega);have hq5:q<5:=(by omega)
                 rcases hf.2 with ((((hL1|hL2)|hR1)|hR2)|hC1)|hC2
                 · exact up hb (by unfold kI;omega) hs.1 hL1
                 · exact up hb (by unfold kI;omega) hs.2.1 hL2
                 · exact wH hb hs.2.2.1 hR1
                 · exact wH hb hs.2.2.2.1 hR2
                 · exact kZ hb (qK hu hp5) (qI hw1 hq5) (λ y hy=>by rw[qL,qJ];exact hs.2.2.2.2.1 y hy) hC1
                 · exact kZ hb (qK hw1 hq5) (qI hu hp5) (λ y hy=>by rw[qL,qJ];exact hs.2.2.2.2.2 y hy) hC2
               · rw[kd,nL] at h5288;rcases kG hf with ⟨h5988,hf⟩|⟨h5988,hf⟩
                 · rw[kd] at h5988;simp only[sA,sO,kd,kJ,kK,kL] at hf
                   set e:=(vr-5288)/50;set x:=(vr-5288) % 50/5;set j:=(vr-5288) % 50 % 5
                   rw[(by unfold zJ;omega:vr=zJ e x j)] at hw;have ha:=(hO.oo e x j hf.1.1.1 hf.1.1.2 hf.1.2).2.1 hw
                   rcases hf.2 with h1|h2;{have:=uV hO hb h1;rw[ha.1] at this;cases this};{have:=xA hO hb hIo h2;rw[ha.2] at this;cases this}
                 · rw[kd,nL] at h5988;simp only[sA,sO,kd,kJ,kK,kL] at hf
                   set e:=(vr-5988)/50;set x:=(vr-5988) % 50/5;set j:=(vr-5988) % 50 % 5
                   rw[(by unfold xR;omega:vr=xR e x j)] at hw;have ha:=(hO.oo e x j hf.1.1.1 hf.1.1.2 hf.1.2).2.2 hw
                   rcases hf.2 with h1|h2;{have:=uV hO hb h1;rw[ha.1] at this;cases this};{have:=xC hO hb h2;rw[ha.2] at this;cases this}
lemma Aw {C:OCtx}{v a b vr}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(hr1:6688<=vr)(hw:v vr=true)(hf:yZ C a b vr=true):False:=by
 unfold yZ at hf;rcases kG hf with ⟨h7998,hf⟩|⟨h7998,hf⟩
 · rw[kd] at h7998;rcases kG hf with ⟨_,hf⟩|⟨h6716,hf⟩;· cases hf
   rw[kd,nL] at h6716;rcases kG hf with ⟨h6856,hf⟩|⟨h6856,hf⟩
   · rw[kd] at h6856;simp only[sA,kd,kJ,kK,kL] at hf
     set e:=(vr-6716)/10;set z:=(vr-6716) % 10;rw[(by unfold wM;omega:vr=wM e z)] at hw
     obtain⟨z2,hz2,hne,hv2⟩:=zK hb hf.2;have:=(hO.oq hf.1.1.1).1 e z z2 hf.1.1.2 hf.1.2 hz2 hne.symm hw;rw[hv2] at this;cases this
   · rw[kd,nL] at h6856;rcases kG hf with ⟨h7556,hf⟩|⟨_,hf⟩;swap;· cases hf
     rw[kd] at h7556;simp only[sA,sO,kd,kJ,kK,kL] at hf
     set e:=(vr-6856)/50;set z:=(vr-6856) % 50/5;set l0:=(vr-6856) % 50 % 5;have hl5:l0<5:=(by omega)
     rw[(by unfold yM;omega:vr=yM e z l0)] at hw;have hh:=(hO.oq hf.1.1.1.1).2 e z l0 hf.1.1.1.2 hf.1.1.2 hf.1.2 hw
     rcases hf.2 with hAf|⟨hO0,hO1⟩
     · have:=uV hO hb hAf;rw[hh.1] at this;cases this
     · have hu:=AF hf.1.1.1.2;have hv':=AE (gi:=C.gi) hf.1.1.1.2
       rcases hh.2 with h0|h1;{exact up hb (by unfold kD;omega) h0 hO0};{exact up hb (by unfold kD;omega) h1 hO1}
 · rw[kd,nL] at h7998;rcases kG hf with ⟨h11230,hf⟩|⟨h11230,hf⟩
   · rw[kd] at h11230;rcases kG hf with ⟨h8798,hf⟩|⟨h8798,hf⟩
     · rw[kd] at h8798;simp only[sA,sO,kd,kJ,kK,kL] at hf
       set x:=(vr-7998)/80;set c:=(vr-7998) % 80/5;set j:=(vr-7998) % 80 % 5;have hj5:j<5:=(by omega)
       rw[(by unfold zI;omega:vr=zI x c j)] at hw;have ha:=hO.oa x c j hf.1.1.1 hf.1.1.2 hf.1.2 hw
       rcases hf.2 with hL|hM;· exact up hb (by unfold kI;omega) ha.1 hL
       · obtain⟨k0,hk0⟩:=uD hM;simp only[wA,tA,uC,BP C.gi hf.1.1.2,sA,sD] at hk0
         obtain⟨⟨hs,hk20,hodd⟩,_,hmk⟩:=hk0;let y:=k0/2;have hy:y<10:=(by omega)
         have w1:=hb.1 (kE x j y) true (by unfold kE;omega) ((by unfold kE;simp[Bool.toNat,y];omega:2*kE x j 0+k0=2*kE x j y+true.toNat)▸(kY hs).2)
         rw[ha.2 y hy hmk] at w1;cases w1
     · rw[kd,nL] at h8798;rcases kG hf with ⟨h9118,hf⟩|⟨h9118,hf⟩
       · rw[kd] at h9118;rcases kG hf with ⟨hvc,hf⟩|⟨_,hf⟩;swap;· cases hf
         simp only[sA,kd,kJ,kK,kL] at hvc hf
         set u:=(vr-8798)/5;set l0:=(vr-8798) % 5;have hl5:l0<5:=(by omega);have hu64:u<64:=(by omega)
         rw[(by unfold wj;omega:vr=wj u l0)] at hw;have hef:=(hO.or hvc.1 u hu64 hvc.2).1 l0 hf.1 hw
         have hctx:=hvc.2;simp only[vCx,vTr,sA,sD,and_assoc] at hctx
         obtain⟨_,_,he0,hta,htb,_,_,hz10⟩:=hctx;have hu0:=AF he0;have hu1:=AE (gi:=C.gi) he0
         simp only[sO,sA] at hf
         rcases hf.2 with ((hAf|hTa)|hTb)|⟨hO0,hO1⟩
         · have:=uV hO hb hAf;rw[hef.1] at this;cases this
         · exact yW hb (by unfold kD;omega) hef.2.1 hTa
         · exact yW hb (by unfold kD;omega) hef.2.2.1 hTb
         · rcases hef.2.2.2 with h0|h1;{exact up hb (by unfold kD;omega) h0 hO0};{exact up hb (by unfold kD;omega) h1 hO1}
       · rw[kd,nL] at h9118;rcases kG hf with ⟨h10014,hf⟩|⟨h10014,hf⟩
         · rw[kd] at h10014;rcases kG hf with ⟨hvc,hf⟩|⟨_,hf⟩;swap;· cases hf
           simp only[sA,sO,kd,sN,qN,kJ,kK,kL] at hvc hf
           set u:=(vr-9118)/14;set e2:=(vr-9118) % 14;have hu64:u<64:=(by omega)
           rw[(by unfold vA;omega:vr=vA u e2)] at hw
           have hes:=(hO.or hvc.1 u hu64 hvc.2).2 e2 hf.1.1 hf.1.2 hw
           have hctx:=hvc.2;simp only[vCx,sA,sD,and_assoc] at hctx;have hz10:=hctx.2.2.2
           rcases hf.2 with ((hL1|hL2)|hBc)|⟨hE0,hE1⟩
           · exact wH hb hes.1 hL1
           · have:=yH hO hb hL2;rw[hes.1] at this;cases this
           · exact wH hb hes.2.1 hBc
           · rcases hes.2.2 with h0|h1;{exact up hb (by unfold kN;omega) h0 hE0};{exact up hb (by unfold kN;omega) h1 hE1}
         · rw[kd,nL] at h10014;rcases kG hf with ⟨h10314,hf⟩|⟨_,hf⟩;swap;· cases hf
           rw[kd] at h10314;rcases kG hf with ⟨hvm,hf⟩|⟨_,hf⟩;swap;· cases hf
           simp only[sA,kd,xJ,kJ,kK,kL] at hvm hf
           set m0:=(vr-10014)/50;set z:=(vr-10014) % 50/5;set l0:=(vr-10014) % 50 % 5;have hl5:l0<5:=(by omega)
           rw[(by unfold zE;omega:vr=zE m0 z l0)] at hw;have hm:=hO.os hvm.1.1.1 m0 hvm.1.1.2 z l0 hvm.1.2 hvm.2 hw
           have hmk:=hvm.1.1.2;simp only[yR,sA,sD,and_assoc] at hmk
           have hu0:=AF hmk.2.2.1;have hu1:=AE (gi:=C.gi) hmk.2.2.1
           rcases hm with h0|h1;{exact up hb (by unfold kD;omega) h0 hf.1};{exact up hb (by unfold kD;omega) h1 hf.2}
   · rw[kd,nL] at h11230;rcases kG hf with ⟨h13730,hf⟩|⟨h13730,hf⟩
     · rw[kd] at h13730;simp only[sA,sO,kd,sN,qN,kJ,kK,kL] at hf
       obtain⟨⟨⟨⟨⟨⟨hx,hj⟩,hy⟩,hne⟩,hni⟩,hl⟩,hd⟩:=hf
       set x:=(vr-11230)/50/5;set j:=(vr-11230)/50 % 5;set y:=(vr-11230) % 50/5;set l0:=(vr-11230) % 50 % 5
       have hj5:j<5:=(by omega);have hl5:l0<5:=(by omega);rw[(by unfold yJ;omega:vr=yJ x j y l0)] at hw
       have hs:=(hO.ot x j y l0 hx hj hy hne hni hl).1 hw
       rcases hd with (hL|hC1)|hC2
       · exact up hb (by unfold kI;omega) hs.1 hL
       · exact kZ hb (qK hx hj5) (qK hy hl5) (λ d hd=>by rw[qL,qL];exact hs.2.1 d hd) hC1
       · exact kZ hb (qI hx hj5) (qI hy hl5) (λ d hd=>by rw[qJ,qJ];exact hs.2.2 d hd) hC2
     · rw[kd,nL] at h13730;rcases kG hf with ⟨h16230,hf⟩|⟨h16230,hf⟩
       · rw[kd] at h16230;simp only[sA,sO,kd,sN,qN,kJ,kK,kL] at hf
         obtain⟨⟨⟨⟨⟨⟨hx,hj⟩,hy⟩,hne⟩,hni⟩,hl⟩,hd⟩:=hf
         set x:=(vr-13730)/50/5;set j:=(vr-13730)/50 % 5;set y:=(vr-13730) % 50/5;set l0:=(vr-13730) % 50 % 5
         have hj5:j<5:=(by omega);have hl5:l0<5:=(by omega);rw[(by unfold yL;omega:vr=yL x j y l0)] at hw
         have ho:=(hO.ot x j y l0 hx hj hy hne hni hl).2 hw
         rcases hd with (hL|hC1)|hC2
         · exact up hb (by unfold kI;omega) ho.1 hL
         · exact kZ hb (qK hx hj5) (qI hy hl5) (λ d hd=>by rw[qL,qJ];exact ho.2.1 d hd) hC1
         · exact kZ hb (qI hx hj5) (qK hy hl5) (λ d hd=>by rw[qJ,qL];exact ho.2.2 d hd) hC2
       · rw[kd,nL] at h16230;rcases kG hf with ⟨h17730,hf⟩|⟨_,hf⟩;swap;· cases hf
         rw[kd] at h17730;rcases kG hf with ⟨hc,hf⟩|⟨_,hf⟩;swap;· cases hf
         rcases kG hf with ⟨hl,hf⟩|⟨_,hf⟩;swap;· cases hf
         simp only[sA,kd,xJ,sN,kJ,kK,kL] at hc hl
         obtain⟨⟨⟨⟨⟨⟨⟨hm1,hi⟩,hii⟩,hy⟩,hniy⟩,hnadj⟩,hn3⟩,hnlen⟩:=hc
         set i:=(vr-16230)/150;set y:=(vr-16230) % 150/15;set n:=(vr-16230) % 150 % 15/5;set l0:=(vr-16230) % 150 % 15 % 5
         rw[(by unfold zF;omega:vr=zF i y n l0)] at hw
         have hif:=hO.ou hm1 i y n l0 hi hii hy hniy hnadj hn3 hnlen hl hw
         set x:=(nbrsN C.gi i).getD n 0;have hx10:=Ao hi hnlen;have hl5:l0<5:=(by omega);have he14:=BM (gi:=C.gi) hi hx10
         simp only[sO,kJ,kK,kL] at hf
         rcases hf with ((((hAe|hAf)|hEm)|hFr)|hLy)|hNb
         · exact wH hb hif.1 hAe
         · have:=uV hO hb hAf;rw[((hO.oo _ x l0 he14 hx10 hl).2.2 hif.1).1] at this;cases this
         · have:=xC hO hb hEm;rw[((hO.oo _ x l0 he14 hx10 hl).2.2 hif.1).2] at this;cases this
         · have:=xA hO hb hIo hFr;rw[hif.2.1] at this;cases this
         · exact yW hb (by unfold kE;omega) hif.2.2.1 hLy
         · obtain⟨k0,hk0⟩:=uD hNb;have hnb:=Bv C.gi hi k0;dsimp only[i] at hnb
           simp only[wA,tA,uf,hnb,sA,sD] at hk0
           obtain⟨⟨hs,hk20,hev⟩,_,hadj⟩:=hk0;let d:=k0/2;have hd:d<10:=(by omega)
           have w1:=hb.1 (kE x l0 d) false (by unfold kE;omega) ((by unfold kE;simp[Bool.toNat,d];omega:2*kE x l0 0+k0=2*kE x l0 d+false.toNat)▸(kY hs).2)
           rw[hif.2.2.2 d hd hadj] at w1;cases w1
lemma Av {C:OCtx}{v a b l}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(hf:A3 C a b l=true):¬w2 v l:=by
 rcases l with ⟨vr,pl⟩;intro hw;change v vr=pl at hw;unfold A3 at hf;dsimp only at hf
 rcases kG hf with ⟨hgb,_⟩|⟨_,hf⟩;· exact wH hb hw hgb
 cases pl
 · simp only[nF,iT] at hf
   rcases kG hf with ⟨hr,hf⟩|⟨_,hf⟩;swap;· cases hf
   simp only[sA,sO,sN,kd,vO,kJ,kK,kL] at hr hf
   set x:=(vr-1080)/10;set y:=(vr-1080) % 10;have hx:x<10:=(by omega)
   have he1:vC x y=vr:=by unfold vC;omega
   have he2:vC y x=vr:=by unfold vC;omega
   rcases hf.2 with h1|h2
   · obtain⟨j,hj,hlv⟩:=xL hb hx (xI hO.o0) hf.1.2 h1;have:=hO.o5 x j y hx hj hf.1.2 hlv;rw[he1,hw] at this;cases this
   · obtain⟨j,hj,hlv⟩:=xL hb hf.1.2 (xI hO.o0) hx h2;have:=hO.o5 y j x hf.1.2 hj hx hlv;rw[he2,hw] at this;cases this
 · simp only[nT,bF,iF] at hf
   rcases kG hf with ⟨h1,hf⟩|⟨h1,hf⟩;· exact Az hO hb (kd.mp h1) hw hf
   rw[kd,nL] at h1;rcases kG hf with ⟨h2,hf⟩|⟨h2,hf⟩;· exact Ay hO hb h1 (kd.mp h2) hw hf
   rw[kd,nL] at h2;rcases kG hf with ⟨h3,hf⟩|⟨h3,hf⟩;· exact Ax hO hb hIo h2 (kd.mp h3) hw hf
   rw[kd,nL] at h3;exact Aw hO hb hIo h3 hw hf
lemma yG {v x y n a}(ha:∀l∈a,w2 v l)(h:∀j<n,v (kE x j y)=false):∀l∈AV x y n a,w2 v l:=by
 induction n generalizing a with| zero=>exact ha| succ n ih=>exact ih (qC (h n (by omega)) ha) (λ j hj=>h j (by omega))
lemma Af {v e z n a}(ha:∀l∈a,w2 v l)(h:∀u<n,u≠z->v (wM e u)=false):∀l∈AU e z n a,w2 v l:=by
 induction n generalizing a with| zero=>exact ha| succ n ih=>
   simp only[AU];apply ih _ (λ u hu hne=>h u (by omega) hne)
   split;{exact ha};{rename_i hne;rw[xJ] at hne;exact qC (h n (by omega) hne) ha}
abbrev xN (v:Nat->Bool)(b:Nat)(go:zW):Prop:=∀{q a eqs imps im dm},kW v a b->xF v eqs->wU v imps->(∀l∈q,w2 v l)->uv (uu v) (go q a eqs imps im dm)
lemma Bs {C:OCtx}{v b go vr r a eqs imps im dm}(hO:ul C v)(hgo:xN v b go)(hb:kW v a b)(heq:xF v eqs)(himp:wU v imps)(hr:∀l∈r,w2 v l)(h1050:vr<1050)(hh:v vr=true):uv (uu v) (Bt C go vr r a eqs imps im dm):=by
 unfold Bt;refine kz (λ h50=>?_) λ h50=>kz (λ h550=>?_) λ h550=>?_
 · rw[kd] at h50;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kK,kL] at hc;simp only[kJ,kK,kL];set x:=vr/5;set j:=vr % 5;rw[(by unfold kI;omega:vr=kI x j)] at hh
   have hq1:=qC (l:=(kE x j x,true)) (hO.o2 x j hc.1 hc.2 hh) hr;apply hgo hb heq himp;split;swap;· exact hq1
   rename_i hj0;rw[sN,qN] at hj0
   exact qC (l:=(kI x (j-1),true)) (hO.o3 x (j-1) hc.1 (by omega) (by simpa[Nat.sub_add_cancel (by omega:1<=j)] using hh)) hq1
 · rw[kd,nL] at h50;rw[kd] at h550;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;simp only[kJ,kK,kL];set x:=(vr-50)/10/5;set j:=(vr-50)/10 % 5;set y:=(vr-50) % 10;have hj5:j<5:=(by omega)
   rw[(by unfold kE;omega:vr=kE x j y)] at hh
   exact hgo hb heq himp (qC (hO.o4 x j y hc.1.1 hc.1.2 hc.2 hh) (qC (hO.o5 x j y hc.1.1 hc.1.2 hc.2 hh) hr))
 · rw[kd,nL] at h550;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set x:=(vr-550)/10/5;set j:=(vr-550)/10 % 5;set y:=(vr-550) % 10;have hj5:j<5:=(by omega)
   rw[(by unfold kD;omega:vr=kD x j y)] at hh;have hq1:=qC (l:=(kI x j,true)) (hO.of x j y hc.1.1 hc.1.2 hc.2 hh) hr
   refine kz (λ hiy=>?_) (λ _=>hgo hb heq himp hq1)
   simp only[sA,sN,qN,kJ,kK,kL] at hiy;have hin:=hO.og x j y hc.1.1 hc.1.2 hc.2 hiy.1 hiy.2 hh
   refine qH (vE hb (qI hc.1.1 hj5)
     (λ k0 hk0=>by simp only[zP,vY,wT,kJ,kL,tX,uf,sL,oM,t2];have h1:¬(k0<20/\k0 % 2=0):=(by omega);simp[h1];omega)
     (λ d hd q ht=>by
       simp only[zP,vY,wT,kJ,kK,kL,tX,uf,sL,oM,t2] at ht ⊢;cases q
       · simp only[Bool.toNat] at ht;have h20:2*d<20/\(2*d) % 2=0:=(by omega)
         have hne:d≠y:=by intro he;have h2e:2*((vr-550) % 10)=2*d:=(by omega);simp[h20,h2e] at ht
         rw[qJ];exact hin.2.1 d hd hne
       · simp[Bool.toNat] at ht;omega))
     λ a' ha'=>hgo ha' (qG heq (qK hc.1.1 hj5) (qI hc.2 (by omega)) λ d hd=>by rw[qL,qJ];exact hin.2.2 d hd) himp (qC hin.1 hq1)
lemma Bq {C:OCtx}{v b go vr r a eqs imps im dm}(hO:ul C v)(hgo:xN v b go)(hb:kW v a b)(heq:xF v eqs)(himp:wU v imps)(hr:∀l∈r,w2 v l)(h1050:1050<=vr)(h3340:vr<3340)(hh:v vr=true):uv (uu v) (Br C go vr r a eqs imps im dm):=by
 unfold Br;refine kz (λ h1940=>?_) λ h1940=>?_
 · rw[kd] at h1940;refine kz (λ hrng=>?_) λ _=>kz (λ hrng=>?_) λ _=>kz (λ hrng=>?_) λ _=>hgo hb heq himp hr
   · simp only[sA,sN,kd,vO] at hrng;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,sN,qN,kJ,kK,kL] at hc;simp only[kJ,kK,kL]
     set t:=(vr-1180)/100;set x:=(vr-1180) % 100/10;set y:=(vr-1180) % 100 % 10;rw[(by unfold zG;omega:vr=zG t x y)] at hh
     have hd:=hO.o9 t x y hc.1.1.1 hc.1.1.2 hc.1.2 hc.2 hh;exact hgo hb heq himp (qC hd.1 (qC hd.2 hr))
   · simp only[sA,sN,kd,vO] at hrng;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,sN,kJ,xO] at hc;simp only[kJ,xO]
     set x:=vr-1500;rw[(by unfold vK;omega:vr=vK x)] at hh;exact hgo hb heq himp (qC (hO.oc x hc.1.1 hc.1.2 hh) hr)
   · simp only[sA,sN,kd,vO] at hrng;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,sN,kJ,kK,kL] at hc;simp only[kJ,kK,kL]
     set t:=(vr-1510)/50;set x:=(vr-1510) % 50/5;set j:=(vr-1510) % 50 % 5;have hj5:j<5:=(by omega);have o0:=hO.o0
     rw[(by unfold xQ;omega:vr=xQ t x j)] at hh;have hrs:=hO.od t x j hc.1.1.1 hc.1.1.2 hc.1.2 hc.2 hh
     exact hgo hb heq (zL himp (BG (t:=t) (by omega)) (qK hc.1.1.2 hj5) λ y hy hv1=>by rw[qL];exact hrs.2 y hy (BH t y▸hv1)) (qC hrs.1 hr)
 · rw[kd,nL] at h1940;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;simp only[kJ,kK,kL]
   set s:=(vr-1940)/50/14;set e:=(vr-1940)/50 % 14;set x:=(vr-1940) % 50/5;set j:=(vr-1940) % 50 % 5;have hj5:j<5:=(by omega)
   rw[(by unfold ur;omega:vr=ur s e x j)] at hh;have hra:=hO.oj s e x j hc.1.1.1 hc.1.1.2 hc.1.2 hc.2 hh
   have he1:=qG heq (qK hc.1.2 hj5) (qB hc.1.1.1 hc.1.1.2) λ y hy=>by rw[qL,qE];exact hra.2.2.2.2.2.1 y hy
   have he2:=qG he1 (qI hc.1.2 hj5) (qB (s:=1-s) (e:=e) (by omega) hc.1.1.2) λ y hy=>by rw[qJ,qE];exact hra.2.2.2.2.2.2 y hy
   exact hgo hb he2 himp (qC hra.1 (qC hra.2.1 (qC hra.2.2.1 (qC hra.2.2.2.1 (qC hra.2.2.2.2.1 hr)))))
lemma Bo {C:OCtx}{v b go vr r a eqs imps im dm}(hO:ul C v)(hIe:C.ie=qP C.I)(hgo:xN v b go)(hb:kW v a b)(heq:xF v eqs)(himp:wU v imps)(hr:∀l∈r,w2 v l)(h3340:3340<=vr)(h6688:vr<6688)(hh:v vr=true):uv (uu v) (Bp C go vr r a eqs imps im dm):=by
 unfold Bp;refine kz (λ h3390=>?_) λ h3390=>kz (λ h3440=>?_) λ h3440=>kz (λ h3636=>?_) λ h3636=>kz (λ h3832=>?_) λ h3832=>kz (λ h4028=>?_) λ h4028=>kz (λ h4224=>?_) λ h4224=>kz (λ h4924=>?_) λ h4924=>kz (λ _=>hgo hb heq himp hr) λ h4938=>kz (λ h5288=>?_) λ h5288=>kz (λ h5988=>?_) λ h5988=>?_
 · rw[kd] at h3390;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set x:=(vr-3340)/5;set j:=(vr-3340) % 5;have hj5:j<5:=(by omega)
   rw[(by unfold uO;omega:vr=uO x j)] at hh
   refine qH (vE hb (qI hc.1 hj5)
     (λ k0 hk0=>by simp only[zP,wA,tX,tA,hIe,xK];have h1:¬(k0<20/\k0 % 2=0):=(by omega);simp[h1])
     (λ y hy q ht=>by
       simp only[zP,wA,vY,wT,kJ,kK,kL,tX,tA,hIe,xK,sL,oM,t2] at ht ⊢;cases q
       · simp only[Bool.toNat] at ht;have h20:2*y<20/\(2*y) % 2=0:=(by omega)
         have hiy:kB C.I y=true:=by unfold kB;cases hI:C.I.testBit y<;>simp[hI,h20] at ht ⊢
         have hxy:x≠y:=by intro he;simp[he,h20,x] at ht
         rw[qJ];cases hv1:v (kD x j y);{rfl};{have:=(hO.og x j y hc.1 hc.2 hy hiy hxy hv1).1;rw[hh] at this;cases this}
       · simp[Bool.toNat] at ht))
     λ a' ha'=>hgo ha' heq himp (qC ((hO.ov x j hc.1 hc.2).1 hh) hr)
 · rw[kd,nL] at h3390;rw[kd] at h3440;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set x:=(vr-3390)/5;set j:=(vr-3390) % 5;have hj5:j<5:=(by omega)
   rw[(by unfold wW;omega:vr=wW x j)] at hh;have hem:=(hO.ov x j hc.1 hc.2).2 hh
   refine qH (vE hb (qI hc.1 hj5)
     (λ k0 hk0=>by rw[uf];have h1:¬(k0<20/\k0 % 2=0):=(by omega);simp[h1])
     (λ y hy q ht=>by simp only[kJ,kK,kL];rw[uf,sD] at ht;cases q;{rw[qJ];exact hem.2 y hy};{simp[Bool.toNat] at ht}))
     λ a' ha'=>hgo ha' heq himp (qC hem.1 hr)
 · rw[kd,nL] at h3440;rw[kd] at h3636;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;simp only[kJ,kK,kL];set u:=(vr-3440)/14;set w:=(vr-3440) % 14;rw[(by unfold yN;omega:vr=yN u w)] at hh
   have hg:=(hO.om u w hc.1 hc.2).1 hh
   have he1:=qG heq (qB (s:=0) (e:=u) (by omega) (by omega)) (qB (s:=0) (e:=w) (by omega) hc.2) λ y hy=>by rw[qE,qE];exact hg.2.1 y hy
   have he2:=qG he1 (qB (s:=1) (e:=u) (by omega) (by omega)) (qB (s:=1) (e:=w) (by omega) hc.2) λ y hy=>by rw[qE,qE];exact hg.2.2 y hy
   exact hgo hb he2 himp (qC hg.1 hr)
 · rw[kd,nL] at h3636;rw[kd] at h3832;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;simp only[kJ,kK,kL];set u:=(vr-3636)/14;set w:=(vr-3636) % 14;rw[(by unfold yO;omega:vr=yO u w)] at hh
   have hg:=(hO.om u w hc.1 hc.2).2 hh
   have he1:=qG heq (qB (s:=0) (e:=u) (by omega) (by omega)) (qB (s:=1) (e:=w) (by omega) hc.2) λ y hy=>by rw[qE,qE];exact hg.2.1 y hy
   have he2:=qG he1 (qB (s:=1) (e:=u) (by omega) (by omega)) (qB (s:=0) (e:=w) (by omega) hc.2) λ y hy=>by rw[qE,qE];exact hg.2.2 y hy
   exact hgo hb he2 himp (qC hg.1 hr)
 · rw[kd,nL] at h3832;rw[kd] at h4028;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set u:=(vr-3832)/14;set w:=(vr-3832) % 14
   have h1:=(hO.on u w (by omega) hc.2 (by omega)).1 ((by unfold uK;omega:vr=uK u w)▸hh)
   have h2:=(hO.on w u hc.2 (by omega) (by omega)).1 ((by unfold uK;omega:vr=uK w u)▸hh)
   exact hgo hb heq himp (qC h1 (qC h2 hr))
 · rw[kd,nL] at h4028;rw[kd] at h4224;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,sN,qN,kJ,kK,kL] at hc;set u:=(vr-4028)/14;set w:=(vr-4028) % 14
   have ho:=(hO.on u w hc.1.1 hc.1.2 hc.2).2 ((by unfold ux;omega:vr=ux u w)▸hh)
   exact hgo hb heq himp (qC ho.1 (qC ho.2 hr))
 · rw[kd,nL] at h4224;rw[kd] at h4924;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-4224)/50;set x:=(vr-4224) % 50/5;set j:=(vr-4224) % 50 % 5
   have ha:=(hO.oo e x j hc.1.1 hc.1.2 hc.2).1 ((by unfold uP;omega:vr=uP e x j)▸hh)
   exact hgo hb heq himp (qC ha.1 (qC ha.2.1 (qC ha.2.2 hr)))
 · rw[kd,nL] at h4938;rw[kd] at h5288;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-4938)/25;set p:=(vr-4938) % 25/5;set t:=(vr-4938) % 25 % 5
   have hs:=hO.op e p t hc.1.1 hc.1.2 hc.2 ((by unfold yK;omega:vr=yK e p t)▸hh)
   have hu:=AF hc.1.1;have hw1:=AE (gi:=C.gi) hc.1.1;have hp5:p<5:=(by omega);have ht5:t<5:=(by omega)
   have he1:=qG heq (qK hu hp5) (qI hw1 ht5) λ y hy=>by rw[qL,qJ];exact hs.2.2.2.2.1 y hy
   have he2:=qG he1 (qK hw1 ht5) (qI hu hp5) λ y hy=>by rw[qL,qJ];exact hs.2.2.2.2.2 y hy
   exact hgo hb he2 himp (qC hs.1 (qC hs.2.1 (qC hs.2.2.1 (qC hs.2.2.2.1 hr))))
 · rw[kd,nL] at h5288;rw[kd] at h5988;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-5288)/50;set x:=(vr-5288) % 50/5;set j:=(vr-5288) % 50 % 5
   have ha:=(hO.oo e x j hc.1.1 hc.1.2 hc.2).2.1 ((by unfold zJ;omega:vr=zJ e x j)▸hh)
   exact hgo hb heq himp (qC ha.1 (qC ha.2 hr))
 · rw[kd,nL] at h5988;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-5988)/50;set x:=(vr-5988) % 50/5;set j:=(vr-5988) % 50 % 5
   have ha:=(hO.oo e x j hc.1.1 hc.1.2 hc.2).2.2 ((by unfold xR;omega:vr=xR e x j)▸hh)
   exact hgo hb heq himp (qC ha.1 (qC ha.2 hr))
lemma Bm {C:OCtx}{v b go vr r a eqs imps im dm}(hO:ul C v)(hgo:xN v b go)(hb:kW v a b)(heq:xF v eqs)(himp:wU v imps)(hr:∀l∈r,w2 v l)(h6688:6688<=vr)(hh:v vr=true):uv (uu v) (Bn C go vr r a eqs imps im dm):=by
 unfold Bn;refine kz (λ h7998=>?_) λ h7998=>kz (λ h11230=>?_) λ h11230=>kz (λ h13730=>?_) λ h13730=>kz (λ h16230=>?_) λ h16230=>kz (λ h17730=>?_) λ _=>hgo hb heq himp hr
 · rw[kd] at h7998;refine kz (λ hrng=>?_) λ _=>kz (λ hrng=>?_) λ _=>hgo hb heq himp hr
   · simp only[sA,sN,kd,vO] at hrng;apply hgo hb heq himp;split;swap;· exact hr
     rename_i hc;simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-6716)/10;set z:=(vr-6716) % 10
     exact Af hr λ z2 hz2 hne=>(hO.oq hc.1.1).1 e z z2 hc.1.2 hc.2 hz2 hne.symm ((by unfold wM;omega:vr=wM e z)▸hh)
   · simp only[sA,sN,kd,vO] at hrng;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,kJ,kK,kL] at hc;set e:=(vr-6856)/50;set z:=(vr-6856) % 50/5;set l0:=(vr-6856) % 50 % 5
     exact hgo hb heq himp (qC ((hO.oq hc.1.1.1).2 e z l0 hc.1.1.2 hc.1.2 hc.2 ((by unfold yM;omega:vr=yM e z l0)▸hh)).1 hr)
 · rw[kd,nL] at h7998;rw[kd] at h11230
   refine kz (λ h8798=>?_) λ h8798=>kz (λ h9118=>?_) λ h9118=>kz (λ h10014=>?_) λ _=>hgo hb heq himp hr
   · rw[kd] at h8798;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,kJ,kK,kL] at hc;set x:=(vr-7998)/80;set c:=(vr-7998) % 80/5;set j:=(vr-7998) % 80 % 5;have hj5:j<5:=(by omega)
     have ha:=hO.oa x c j hc.1.1 hc.1.2 hc.2 ((by unfold zI;omega:vr=zI x c j)▸hh)
     refine qH (vE hb (qK hc.1.1 hj5)
       (λ k0 hk0=>by simp only[kJ,kK,kL];rw[AL C.gi hc.1.2];have h1:¬(k0<20/\k0 % 2=0):=(by omega);simp[h1])
       (λ y hy q ht=>by simp only[kJ,kK,kL] at ht ⊢;rw[AL C.gi hc.1.2,sA,sD] at ht;cases q;{simp only[Bool.toNat] at ht;rw[qL];exact ha.2 y hy (by simpa using ht.2)};{simp[Bool.toNat] at ht}))
       λ a' ha'=>hgo ha' heq himp (qC ha.1 hr)
   · rw[kd,nL] at h8798;rw[kd] at h9118;refine kz (λ hvc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,kJ,kK] at hvc;refine kz (λ hl=>?_) (λ _=>hgo hb heq himp hr)
     rw[kd] at hl;simp only[kJ,kK,kL] at hl ⊢;set u:=(vr-8798)/5;set l0:=(vr-8798) % 5;have hu64:u<64:=(by omega)
     have hef:=(hO.or hvc.1 u hu64 hvc.2).1 l0 hl ((by unfold wj;omega:vr=wj u l0)▸hh)
     exact hgo hb heq himp (qC hef.1 (qC hef.2.1 (qC hef.2.2.1 hr)))
   · rw[kd,nL] at h9118;rw[kd] at h10014;refine kz (λ hvc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,kJ,kK] at hvc;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
     simp only[sA,kd,sN,qN,kJ,kK,kL] at hc;simp only[kJ,kK,kL];set u:=(vr-9118)/14;set e2:=(vr-9118) % 14;have hu64:u<64:=(by omega)
     have hes:=(hO.or hvc.1 u hu64 hvc.2).2 e2 hc.1 hc.2 ((by unfold vA;omega:vr=vA u e2)▸hh)
     exact hgo hb heq himp (qC hes.1 (qC hes.2.1 hr))
 · rw[kd,nL] at h11230;rw[kd] at h13730;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,sN,qN,kJ,kK,kL] at hc
   obtain⟨⟨⟨⟨⟨hx,hj⟩,hy⟩,hne⟩,hni⟩,hl⟩:=hc
   set x:=(vr-11230)/50/5;set j:=(vr-11230)/50 % 5;set y:=(vr-11230) % 50/5;set l0:=(vr-11230) % 50 % 5
   have hj5:j<5:=(by omega);have hl5:l0<5:=(by omega);have hs:=(hO.ot x j y l0 hx hj hy hne hni hl).1 ((by unfold yJ;omega:vr=yJ x j y l0)▸hh)
   have he1:=qG heq (qK hx hj5) (qK hy hl5) λ d hd=>by rw[qL,qL];exact hs.2.1 d hd
   have he2:=qG he1 (qI hx hj5) (qI hy hl5) λ d hd=>by rw[qJ,qJ];exact hs.2.2 d hd
   exact hgo hb he2 himp (qC hs.1 hr)
 · rw[kd,nL] at h13730;rw[kd] at h16230;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,sN,qN,kJ,kK,kL] at hc
   obtain⟨⟨⟨⟨⟨hx,hj⟩,hy⟩,hne⟩,hni⟩,hl⟩:=hc
   set x:=(vr-13730)/50/5;set j:=(vr-13730)/50 % 5;set y:=(vr-13730) % 50/5;set l0:=(vr-13730) % 50 % 5
   have hj5:j<5:=(by omega);have hl5:l0<5:=(by omega);have ho:=(hO.ot x j y l0 hx hj hy hne hni hl).2 ((by unfold yL;omega:vr=yL x j y l0)▸hh)
   have he1:=qG heq (qK hx hj5) (qI hy hl5) λ d hd=>by rw[qL,qJ];exact ho.2.1 d hd
   have he2:=qG he1 (qI hx hj5) (qK hy hl5) λ d hd=>by rw[qJ,qL];exact ho.2.2 d hd
   exact hgo hb he2 himp (qC ho.1 hr)
 · rw[kd,nL] at h16230;rw[kd] at h17730;refine kz (λ hc=>?_) (λ _=>hgo hb heq himp hr)
   simp only[sA,kd,xJ,sN,kJ,kK,kL] at hc
   obtain⟨⟨⟨⟨⟨⟨⟨hm1,hi⟩,hii⟩,hy⟩,hniy⟩,hnadj⟩,hn3⟩,hnlen⟩:=hc
   refine kz (λ hl=>?_) (λ _=>hgo hb heq himp hr);rw[kd] at hl;simp only[kJ,kK,kL] at hl
   set i:=(vr-16230)/150;set y:=(vr-16230) % 150/15;set n:=(vr-16230) % 150 % 15/5;set l0:=(vr-16230) % 150 % 15 % 5
   have hif:=hO.ou hm1 i y n l0 hi hii hy hniy hnadj hn3 hnlen hl ((by unfold zF;omega:vr=zF i y n l0)▸hh)
   set x:=(nbrsN C.gi i).getD n 0;have hx10:=Ao hi hnlen;have hl5:l0<5:=(by omega)
   refine qH (vE hb (qK hx10 hl5)
     (λ k0 hk0=>by simp only[kJ,kK];rw[Ai C.gi hi];have h1:¬(k0<20/\k0 % 2=1):=(by omega);simp[h1])
     (λ d hd q ht=>by
       simp only[kJ,kK,kL] at ht ⊢;rw[Ai C.gi hi,sA,sD] at ht;cases q;{simp[Bool.toNat] at ht}
       · simp only[Bool.toNat] at ht;rw[qL];exact hif.2.2.2 d hd ((by omega:(2*d+1)/2=d)▸ht.2)))
     λ a' ha'=>hgo ha' heq himp (qC hif.1 (qC hif.2.1 (qC hif.2.2.1 hr)))
lemma Ag {C:OCtx}{v f q a b eqs imps im dm}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)
   (hb:kW v a b)(heq:xF v eqs)(himp:wU v imps)(hq:∀l∈q,w2 v l):uv (uu v) (yV C f q a b eqs imps im dm):=by
 induction f generalizing q a b eqs imps im dm with
 | zero=>exact ud (Q:=uu v) ⟨hb,heq,himp⟩
 | succ f ih=>
   cases q with
   | nil=>exact ud (Q:=uu v) ⟨hb,heq,himp⟩
   | cons hd r=>
     rcases hd with ⟨vr,pl⟩;have hh:v vr=pl:=hq (vr,pl) Ar;have hr:∀l∈r,w2 v l:=λ l hl=>hq l (As _ hl)
     simp only[yV];refine kz (λ _=>ih hb heq himp hr) λ _=>kz (λ hif=>⟨(λ _=>Av hO hb hIo hif hh),fun _ e=>nomatch e⟩) λ _=>?_
     have hb':=Bj hb hh
     have hgo:xN v (zO a b vr pl).2 (λ q a' e' i' im' dm'=>yV C f q a' (zO a b vr pl).2 e' i' im' dm'):=λ ha he hi hq'=>ih ha he hi hq'
     cases pl
     · simp only[nF,iT];refine kz (λ h50=>?_) λ _=>kz (λ hrng=>?_) λ _=>hgo hb' heq himp hr
       · rw[kd] at h50;apply hgo hb' heq himp;split;swap;· exact hr
         rename_i hc;simp only[sA,kd,xO,kK,kL] at hc
         refine qC ?_ hr;change v (kI (vr.div 5) ((vr.mod 5).add 1))=false;simp only[xO,kK,kL]
         cases hv1:v (kI (vr/5) (vr % 5+1));{rfl};{have:=hO.o3 (vr/5) (vr % 5) hc.1 hc.2 hv1;rw[(by unfold kI;omega:kI (vr/5) (vr % 5)=vr),hh] at this;cases this}
       · simp only[sA,sN,kd,vO] at hrng;apply hgo hb' heq himp;split;swap;· exact hr
         rename_i hc;simp only[sA,sN,kd,vO,kJ,kK,kL] at hc
         set x:=(vr-1080)/10;set y:=(vr-1080) % 10;have hx:x<10:=(by omega)
         refine yG (yG hr λ j hj=>?_) λ l0 hl0=>?_
         · cases hv1:v (kE x j y);{rfl};{have:=hO.o5 x j y hx hj hc.2 hv1;rw[(by unfold vC;omega:vC x y=vr),hh] at this;cases this}
         · cases hv1:v (kE y l0 x);{rfl};{have:=hO.o5 y l0 x hc.2 hl0 hx hv1;rw[(by unfold vC;omega:vC y x=vr),hh] at this;cases this}
     · simp only[nT,bF,iF]
       refine kz (λ h1=>Bs hO hgo hb' heq himp hr (kd.mp h1) hh) λ h1=>?_
       rw[kd,nL] at h1
       refine kz (λ h2=>Bq hO hgo hb' heq himp hr h1 (kd.mp h2) hh) λ h2=>?_
       rw[kd,nL] at h2
       refine kz (λ h3=>Bo hO hIe hgo hb' heq himp hr h2 (kd.mp h3) hh) λ h3=>?_
       rw[kd,nL] at h3
       exact Bm hO hgo hb' heq himp hr h3 hh
lemma qS {C:OCtx}{v st l}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hs:uu v st)(hl:w2 v l):uv (uu v) (ue C st l):=
 kz (λ _=>qH (kV hs) λ _ hs'=>Ag hO hIe hIo hs'.1 hs'.2.1 hs'.2.2 (qC hl λ _ h=>nomatch h)) (λ _=>Ag hO hIe hIo hs.1 hs.2.1 hs.2.2 (qC hl λ _ h=>nomatch h))
lemma yU {C:OCtx}{v ls st}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hs:uu v st)(hl:∀l∈ls,w2 v l):uv (uu v) (ws C ls st):=by
 induction ls generalizing st with| nil=>exact ud hs| cons l r ih=>
   simp only[ws];exact qH (qS hO hIe hIo hs (hl l Ar)) λ s' hs'=>ih hs' (λ x hx=>hl x (As _ hx))
lemma Ah {C:OCtx}{v c st}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hs:uu v st)(hc:¬Holds v c):uv (uu v) (wI C c st):=by
 induction c generalizing st with| nil=>exact ud hs| cons l r ih=>
   simp only[wI];exact qH (qS hO hIe hIo hs ((qs v l).2 λ h=>hc ⟨l,Ar,h⟩)) λ s' hs'=>ih hs' λ ⟨x,hx,hw⟩=>hc ⟨x,As _ hx,hw⟩
lemma C6 {C:OCtx}{v}(hO:ul C v):∀l∈vZ C,w2 v l:=by
 intro l hl;unfold vZ at hl;simp only[AZ] at hl
 rcases hl with ((h0|h1)|h2)|h3
 · obtain⟨x,hx,rfl⟩:=lM.mp h0;exact hO.o1 x (lR.mp hx)
 · obtain⟨x,hx,hm⟩:=zR.mp h1;have hx10:=lR.mp hx;simp only[AZ] at hm
   rcases hm with (hA|hB)|hC
   · split at hA;swap;· cases hA
     rename_i hix;simp only[AZ] at hA;rcases hA with ((hR|hH)|hAc)|hIo
     · obtain⟨t0,ht,rfl⟩:=lM.mp hR;exact hO.o6 x t0 hx10 hix (lR.mp ht)
     · simp only[At] at hH;subst hH;exact hO.ob x hx10 hix
     · obtain⟨y,hy,hm2⟩:=zR.mp hAc;obtain⟨z,hz,rfl⟩:=lM.mp hm2;simp only[Cd,kd] at hz
       have hy':=An hx10 hy;have hz':=An hx10 hz.1;exact hO.o8 x y z hx10 hix hz.2 hz'.1 hy'.2 hz'.2
     · obtain⟨y,hy,hm2⟩:=zR.mp hIo;have hy10:=lR.mp hy;split at hm2
       · rename_i had;simp only[At] at hm2;subst hm2;exact (hO.oh x y hx10 hix hy10).1 had
       · split at hm2;swap;· cases hm2
         rename_i _ hne;simp only[sA,sN,qN] at hne;simp only[At] at hm2;subst hm2
         exact (hO.oh x y hx10 hix hy10).2 hne.2 hne.1
   · obtain⟨y,hy,rfl⟩:=lM.mp hB;simp only[Cd,lR,sA,sO,kd] at hy;exact hO.o7 x y hy.2.1 hy.1 hy.2.2
   · obtain⟨j,hj,rfl⟩:=lM.mp hC;exact hO.oe x j hx10 (lR.mp hj)
 · obtain⟨e,he,hm⟩:=zR.mp h2;have he14:=lR.mp he
   have h0:=hO.oi 0 e (by omega) he14;have h1:=hO.oi 1 e (by omega) he14
   simp only[epN,beq_self_eq_true,iT,show (1==0)=false by rfl,bF,iF] at h0 h1
   simp only[mC,List.not_mem_nil,or_false] at hm;rcases hm with rfl|rfl|rfl|rfl;exact h0.1;exact h0.2;exact h1.1;exact h1.2
 · obtain⟨x,hx,hm⟩:=zR.mp h3;have hx10:=lR.mp hx;split at hm;· cases hm
   rename_i hni;have hp:=hO.ok x hx10 (Bool.eq_false_iff.mpr hni);simp only[AZ] at hm
   rcases hm with (hL|AB)|hEl
   · obtain⟨h0,hh,rfl⟩:=lM.mp hL;rw[lR,Nat.lt_min] at hh;exact hp.1 h0 hh.1 hh.2
   · obtain⟨h0,hh,hm2⟩:=zR.mp AB;rw[lR,Nat.lt_min] at hh;have hp2:=hp.2.1 h0 hh.1 hh.2
     simp only[mC,List.not_mem_nil,or_false] at hm2;rcases hm2 with rfl|rfl;exact hp2.1;exact hp2.2
   · split at hEl;swap;· cases hEl
     rename_i hc;simp only[sA,sN,kd] at hc;simp only[At] at hEl;subst hEl;exact hp.2.2 hc.1 hc.2
lemma BC {C:OCtx}{v}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I):uv (uu v) (BD C):=
 qH (yU hO hIe hIo ⟨⟨fun _ _ _ h=>(by simp at h),fun _ _ _ h=>(by simp at h)⟩,⟨(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h),(λ _ h=>nomatch h)⟩,fun _ h=>nomatch h⟩ (C6 hO)) λ _ hs=>kV hs
lemma BE {C:OCtx}{v a b acc c res}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(hfu:xY C a b acc c=some res):∀l∈c,w2 v l->some l=res\/some l=acc:=by
 have hkeep:∀(u:qv)(bs:q0),xY C a b (some u) bs=some res->res=some u:=by
   intro u bs;induction bs with| nil=>intro h;simp[xY] at h;exact h.symm| cons y ys iy=>
     intro h;simp only[xY] at h;split at h;{exact iy h};{split at h;{exact iy h};{cases h}}
 induction c generalizing acc with| nil=>intro _ hl;cases hl| cons x xs ih=>
   simp only[xY] at hfu;split at hfu
   · rename_i hif;intro l hl hw;rcases mC.mp hl with rfl|hl';{exact (Av hO hb hIo hif hw).elim};{exact ih hfu l hl' hw}
   · cases acc with
     | none=>
       intro l hl hw;rcases mC.mp hl with rfl|hl'
       · exact Or.inl (hkeep l xs hfu).symm
       · rcases ih hfu l hl' hw with h1|h2;{exact Or.inl h1};{exact Or.inl (h2.trans (hkeep x xs hfu).symm)}
     | some p=>
       rcases hpeq:p==x with _|_
       · simp[hpeq] at hfu
       · simp only[hpeq,iT] at hfu;have he:p=x:=beq_iff_eq.mp hpeq;subst he
         intro l hl hw;rcases mC.mp hl with rfl|hl';{exact Or.inr rfl};{exact ih hfu l hl' hw}
lemma A6 {C:OCtx}{v a b c res}(hO:ul C v)(hb:kW v a b)(hIo:C.io=qF C.I)(hd:Holds v c)(hfu:fU C a b c=some res):∃l,some l=res/\w2 v l:=by
 obtain⟨l,hl,hw⟩:=hd;rcases BE hO hb hIo hfu l hl hw with h1|h2;{exact⟨l,h1,hw⟩};{cases h2}
lemma w4 {C:OCtx}{v st cl}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hs:uu v st)(hd:Holds v cl):
   (uy C st cl=some none->False)/\∀s',uy C st cl=some (some s')->uu v s':=by
 unfold uy;cases hfu:fU C st.a st.b cl with
 | some res=>{obtain⟨l,he,hw⟩:=A6 hO hs.1 hIo hd hfu;subst he;dsimp only;cases hos:ue C st l with| none=>exact⟨(λ _=>(qS hO hIe hIo hs hw).1 hos),fun _ e=>nomatch e⟩| some s'=>exact⟨(λ e=>nomatch e),fun _ e=>(by cases e;exact (qS hO hIe hIo hs hw).2 s' hos)⟩}
 | none=>{dsimp only;split;{exact⟨(λ e=>nomatch e),fun _ e=>nomatch e⟩};{cases hsy:kR st with| none=>exact⟨(λ _=>(kV hs).1 hsy),fun _ e=>nomatch e⟩| some st1=>{dsimp only;have hs1:=(kV hs).2 st1 hsy;cases hfu1:fU C st1.a st1.b cl with| none=>exact⟨(λ e=>nomatch e),fun _ e=>nomatch e⟩| some res=>{obtain⟨l,he,hw⟩:=A6 hO hs1.1 hIo hd hfu1;subst he;dsimp only;cases hos:ue C st1 l with| none=>exact⟨(λ _=>(qS hO hIe hIo hs1 hw).1 hos),fun _ e=>nomatch e⟩| some s'=>exact⟨(λ e=>nomatch e),fun _ e=>(by cases e;exact (qS hO hIe hIo hs1 hw).2 s' hos)⟩}}}}
lemma vT {C:OCtx}{v st cl}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hs:uu v st)(hd:Holds v cl)(h:uh C st cl=true):False:=by
 unfold uh at h;cases hfu:fU C st.a st.b cl with
 | some res=>{obtain⟨l,he,hw⟩:=A6 hO hs.1 hIo hd hfu;subst he;simp only[hfu] at h;cases hos:ue C st l with| none=>exact (qS hO hIe hIo hs hw).1 hos| some s1=>{simp only[hos,Option.isNone_iff_eq_none] at h;exact (kV ((qS hO hIe hIo hs hw).2 s1 hos)).1 h}}
 | none=>{simp only[hfu] at h;split at h;{cases h};{cases hsy:kR st with| none=>exact (kV hs).1 hsy| some st1=>{have hs1:=(kV hs).2 st1 hsy;simp only[hsy] at h;cases hfu1:fU C st1.a st1.b cl with| none=>simp[hfu1] at h| some res=>{obtain⟨l,he,hw⟩:=A6 hO hs1.1 hIo hd hfu1;subst he;simp only[hfu1] at h;cases hos:ue C st1 l with| none=>exact (qS hO hIe hIo hs1 hw).1 hos| some s1=>{simp only[hos,Option.isNone_iff_eq_none] at h;exact (kV ((qS hO hIe hIo hs1 hw).2 s1 hos)).1 h}}}}}
lemma qm {C:OCtx}{v f w n}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(h:q2 v f n)(i d g:Nat)(st:St)(j:Nat)(hs:uu v st)(hc:q5 C f w n i d g st=some j):False:=by
 induction i generalizing d g st with| zero=>simp[q5] at hc| succ k ih=>
   cases k with
   | zero=>{simp only[q5] at hc;split at hc;{rename_i hlt;rw[sD] at hlt;split at hc;{rename_i hsl;exact vT hO hIe hIo hs (h _ hlt) hsl};{cases hc}};{cases hc}}
   | succ q=>{simp only[q5] at hc;split at hc;{rename_i hlt;rw[sD] at hlt;have hst:=w4 hO hIe hIo hs (h _ hlt);cases hr:uy C st (f (qj w n d g).1) with| none=>simp[hr] at hc| some res=>cases res with| none=>exact hst.1 hr| some s'=>{simp only[hr] at hc;exact ih _ _ s' (hst.2 s' hr) hc}};{cases hc}}
lemma Bl {C:OCtx}{v f w n}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(h:q2 v f n)(c d g:Nat)(st:St)(hs:uu v st):
   (yT C f w n c d g st=some none->False)/\∀p,yT C f w n c d g st=some (some p)->uu v p.1:=by
 induction c generalizing d g st with
 | zero=>{simp only[yT];cases hsy:kR st with| none=>exact⟨(λ _=>(kV hs).1 hsy),fun _ e=>nomatch e⟩| some s=>exact⟨(λ e=>nomatch e),fun _ e=>(by cases e;exact (kV hs).2 s hsy)⟩}
 | succ c ih=>{simp only[yT];split;{rename_i hlt;rw[sD] at hlt;have hst:=w4 hO hIe hIo hs (h _ hlt);cases hr:uy C st (f (qj w n d g).1) with| none=>exact⟨(λ e=>nomatch e),fun _ e=>nomatch e⟩| some res=>cases res with| none=>exact⟨(λ _=>hst.1 hr),fun _ e=>nomatch e⟩| some s'=>exact ih _ _ s' (hst.2 s' hr)};{exact⟨(λ e=>nomatch e),fun _ e=>nomatch e⟩}}
lemma AI {C:OCtx}{v B w m i h st}(hO:ul C v)(hIe:C.ie=qP C.I)(hIo:C.io=qF C.I)(hq2:q2 v B i)(hs:uu v st)(hc:vN C B w m i h st=true):False:=by
 induction m generalizing i h st with
 | zero=>{simp only[vN,qb,Option.isSome_iff_exists] at hc;obtain⟨_,h1⟩:=hc;exact qm hO hIe hIo hq2 _ _ _ st _ hs h1}
 | succ m ih=>
   simp only[vN] at hc
   have hBi:Holds v (B i):=by
     by_contra hnh;have hn:=Ah hO hIe hIo hs hnh;cases hnc:wI C (B i) st with
     | none=>exact hn.1 hnc
     | some s0=>{simp only[hnc] at hc;split at hc;{cases hsy:kR s0 with| none=>exact (kV (hn.2 s0 hnc)).1 hsy| some _=>simp[hsy] at hc};{cases hq5:q5 C B w i (qr h).1 0 (qr h).2 s0 with| none=>simp[hq5] at hc| some j=>exact qm hO hIe hIo hq2 _ _ _ s0 j (hn.2 s0 hnc) hq5}}
   have hq2':q2 v B (i+1):=λ j hj=>(Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj)).elim (hq2 j) (λ e=>e▸hBi)
   have hst:∀h',(match B i with| [l]=>(match (ue C st l).bind kR with| none=>true| some s'=>vN C B w m (i+1) h' s')| _=>vN C B w m (i+1) h' st)=true->False:=by
     intro h' hx;cases hci:B i with
     | nil=>{simp only[hci] at hx;exact ih hq2' hs hx}
     | cons l ls=>cases ls with
       | nil=>{simp only[hci] at hx hBi;have hwl:w2 v l:=by{obtain⟨x,hx1,hw⟩:=hBi;rcases At.mp hx1 with rfl;exact hw};have hob:=qH (qS hO hIe hIo hs hwl) λ _ hs'=>kV hs';cases hos:(ue C st l).bind kR with| none=>exact hob.1 hos| some s'=>{simp only[hos] at hx;exact ih hq2' (hob.2 s' hos) hx}}
       | cons _ _=>{simp only[hci] at hx;exact ih hq2' hs hx}
   cases hnc:wI C (B i) st with
   | none=>{simp only[hnc] at hc;split at hc;{exact hst _ hc};{cases hc}}
   | some s0=>{simp only[hnc] at hc;split at hc;{cases hsy:kR s0 with| none=>{simp only[hsy] at hc;exact hst _ hc}| some _=>simp[hsy] at hc};{cases hq5:q5 C B w i (qr h).1 0 (qr h).2 s0 with| none=>simp[hq5] at hc| some h'=>{simp only[hq5] at hc;exact hst h' hc}}}
end OS
lemma sc {gi k I m t c x}(f:Nat->Nat)(d:Nat->q0)(nb nd w h:Nat)(hqt:qt gi k I m t c x f d nb nd w h=true):Unsat gi k I m 0 t c x:=by
 intro v hEn hO;unfold qt at hqt
 have hIe:(qU gi k I m t c x).ie=qP (qU gi k I m t c x).I:=by simp[qU,uI]
 have hIo:(qU gi k I m t c x).io=qF (qU gi k I m t c x).I:=by simp[qU,uI]
 have hO':OOK (qU gi k I m t c x).gi (qU gi k I m t c x).k (qU gi k I m t c x).I (qU gi k I m t c x).m (qU gi k I m t c x).t (qU gi k I m t c x).c (qU gi k I m t c x).x v:=by simpa[qU,uI] using hO
 split at hqt;swap;· cases hqt
 rename_i hall;have hq2:=Dq hEn hall (e:=d);have his:=BC hO' hIe hIo
 cases hi0:BD (qU gi k I m t c x) with| none=>exact his.1 hi0| some s0=>
   simp only[hi0] at hqt;have hru:=Bl (w:=w) hO' hIe hIo hq2 (qr h).1 0 (qr h).2 s0 (his.2 s0 hi0)
   cases hru0:yT (qU gi k I m t c x) (AY (exS gi k I m t c x) (AC f) d nb) w nb (qr h).1 0 (qr h).2 s0 with
   | none=>simp[hru0] at hqt| some res=>
     simp only[hru0] at hqt;cases res with| none=>exact hru.1 hru0| some p=>exact AI hO' hIe hIo hq2 (hru.2 p hru0) hqt
end Rup

section
private abbrev tS (n:Nat):=Finset (Fin n)
private abbrev tX (n:Nat):=Fin n->Bool
private abbrev tY (n:Nat):=Fin n->Nat
private abbrev tK:=Finset Nat
private abbrev tL:=List Bool
private abbrev tJ:=Nat×Bool
private abbrev tG:=Bool×Nat×Nat
private abbrev tF:=Finset
open List renaming all_eq_true->p0,any_cons->p1,any_eq_true->p2,getD_eq_getElem?_getD->p3,getElem?_append_left->p4,getElem?_eq_getElem->p5,getElem?_map->p6,getElem_of_mem->p7,length_ofFn->p8,length_singleton->p9,length_take->p10,map_append->p11,map_cons->p12,map_nil->p13,mem_cons_self->p14,mem_filter->p15,mem_map->p16,mem_range->p17,mem_toFinset->p18,nodup_append->p19,range->p20,toFinset_card_of_nodup->p21
open Nat renaming find->p22,find_min->p23,find_spec->p24,not_lt->p25,one_shiftLeft->p26,testBit_or->p27,zero_testBit->p28
open Finset renaming card_eq_one->p29,card_filter->p30,card_filter_add_card_filter_not->p31,card_image_of_injOn->p32,card_image_of_injective->p33,card_le_card->p34,card_sdiff_add_card_eq_card->p35,disjoint_left->p36,eq_empty_of_forall_notMem->p37,filter_filter->p38,image_nonempty->p39,inter_subset_right->p40,le_max'->p41,max'_mem->p42,mem_insert->p43,mem_sigma->p44,mem_toList->p45,one_lt_card->p46,range->p47,singleton_injective->p48,singleton_subset_iff->p49,sum_add_distrib->p50,sum_congr->p51,sum_eq_zero->p52,univ->p53
open Bool renaming eq_false_iff->p54,false->p55,false_and->p56,false_or->p57,noConfusion->p58,not_eq_false->p59,not_not->p60,not_true->p61,or_assoc->p62,true->p63,true_and->p64
open Prod renaming fst->p65
open Sum (inl inr)
open List renaming length->tD
namespace DagTools
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (mem_coe mem_biUnion sum_subset mem_product filter_congr univ)
namespace A0
abbrev RT:=@Relation.ReflTransGen
abbrev rC:=@Relation.ReflTransGen.cases_head
abbrev rI:=@Relation.ReflTransGen.head_induction_on
abbrev sI:=@Nat.strong_induction_on
abbrev oF:=@List.ofFn
lemma lL{a b c:Nat}:a<b->b<=c->a<c:=lt_of_lt_of_le
lemma dT{p:Prop}[Decidable p]:(decide p=p63)=p:=decide_eq_true_eq
lemma m0{α}[DecidableEq α](a:α):a∈({a}:tF α):=Finset.mem_singleton_self a
noncomputable abbrev cP:=@Classical.decPred
lemma bA{a b:Bool}:((a&&b)=p63)=(a=p63/\b=p63):=Bool.and_eq_true a b
lemma bO{a b:Bool}:((a||b)=p63)=(a=p63\/b=p63):=Bool.or_eq_true a b
abbrev EP:=@Equiv.Perm
lemma mF{α}{s:tF α}{p}[DecidablePred p]{a}:a∈s.filter p<->a∈s/\p a:=Finset.mem_filter
lemma mS{α}[DecidableEq α]{a b:α}:a∈({b}:tF α)<->a=b:=Finset.mem_singleton
lemma mR{n m:Nat}:n∈p47 m<->n<m:=Finset.mem_range
lemma mI{α}[DecidableEq α]{s t:tF α}{a}:a∈s∩t<->a∈s/\a∈t:=Finset.mem_inter
lemma mU{α}[Fintype α](a:α):a∈(p53:tF α):=Finset.mem_univ a
lemma mD{α}[DecidableEq α]{s t:tF α}{a}:a∈s\t<->a∈s/\a∉t:=Finset.mem_sdiff
lemma mG{α β}[DecidableEq β]{f:α->β}{s:tF α}{b}:b∈s.image f<->∃a∈s,f a=b:=Finset.mem_image
lemma mN{α}[DecidableEq α]{s t:tF α}{a}:a∈s∪t<->a∈s\/a∈t:=Finset.mem_union
lemma nE{α}(a:α):a∉(∅:tF α):=Finset.notMem_empty a
abbrev U0:=Σ _:Nat,Nat
abbrev rH:=@Relation.ReflTransGen.head
abbrev rR:=@Relation.ReflTransGen.refl
abbrev rK:=@Relation.ReflTransGen.cases_tail
abbrev rT:=@Relation.ReflTransGen.tail
abbrev fE:=@Finset.eq_empty_iff_forall_notMem
abbrev fS:=@Finset.sum_filter_add_sum_filter_not
abbrev fN:=@Finset.not_nonempty_iff_eq_empty
abbrev fU:=@Finset.card_union_of_disjoint
abbrev fI:=@Finset.inter_subset_left
abbrev lP:=@List.length_pos_of_ne_nil
abbrev lR:=List.finRange
abbrev lS:=@List.mem_singleton
abbrev nA:=@Nat.add_sub_cancel_left
abbrev nL:=@Nat.le_add_right
abbrev bF:=Bool.false_eq_true
abbrev lA:=@List.length_append
abbrev lO:=@List.foldl_cons
abbrev o1:=@Or.inl
abbrev o2:=@Or.inr
abbrev nZ:=@Nat.zero_le
abbrev nO:=@Nat.zero_lt_one
abbrev nT:=@Nat.lt_of_lt_of_le
lemma fw{α}(a:α):({a}:tF α).card=1:=Finset.card_singleton a
abbrev fz:=@Finset.card_pos
abbrev gk:=@Finset.not_nonempty_empty
abbrev g5:=p47
abbrev g6:=@List.mem_append
abbrev g8:=@Finset.card_eq_zero
abbrev gI:=@Finset.filter_eq_empty_iff
abbrev hC:=@List.mem_finRange
abbrev hE:=@Finset.single_le_sum
abbrev hD:=@dite_eq_left
abbrev hF:=@Sum.inl.injEq
abbrev hG:=@List.getElem_append_left
abbrev hH:=@List.getElem_append_right
abbrev hI:=@Option.some.injEq
abbrev hJ:=@Nat.not_lt_zero
abbrev hK:=@List.length_replicate
abbrev hL:=@List.getElem_mem
abbrev hN:=@Finset.card_le_card_of_injOn
abbrev hO:=@Finset.card_filter_le
end A0
section
open A0
def xp:Bool->Bool->Bool->Bool
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[simp] lemma wV(a b:Bool):xp p63 a b=(a&&b):=rfl
@[simp] lemma A5(a b:Bool):xp p55 a b=(a||b):=rfl
abbrev qD:=List (tG)
abbrev Dag:=qD
def gZ(D:qD)(j:Nat):Bool:=(D.getD j (p55,0,0)).1
def yx(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.1
def yf(D:qD)(j:Nat):Nat:=(D.getD j (p55,0,0)).2.2
def zp(w:tL)(g:tG):tL:=w++[xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55)]
def wl(D:qD)(w:tL):tL:=D.foldl zp w
def fO(D:qD){n:Nat}(x:tX n)(w:Nat):Bool:=(wl D (oF x)).getD w p55
abbrev val(D:qD){n:Nat}:=@fO D n
def q0(n:Nat)(D:qD):Prop:=∀j,j<(tD D)->yx D j<n+j/\yf D j<n+j/\yx D j≠yf D j
def qg(D:qD)(w:Nat):tK:=(g5 (tD D)).filter (λ j=>yx D j=w\/yf D j=w)
def kS (D:qD)(w:Nat):Nat:=(qg D w).card
def b5(n:Nat)(D:qD):Prop:=∀w,w+1<n+(tD D)->1<=kS D w
def fV(n:Nat)(D:qD):Prop:=q0 n D/\b5 n D/\D≠[]
abbrev BX:=fV
def qb(n:Nat)(D:qD):Nat:=n+(tD D)-1
def q9{n:Nat}(v:Fin n):tX n:=λ i=>decide (i=v)
def fM(n:Nat)(D:qD)(w:Nat):tS n:=univ.filter (λ v=>fO D (q9 v) w=p63)
abbrev Be:=fM
def q6(D:qD)(K:tK):Nat:=∑ w∈K,(kS D w-1)
def kO(n:Nat)(D:qD):tK:=g5 (n+(tD D)-1)
def yr(n:Nat)(D:qD):Nat:=q6 D (kO n D)
def fJ(n:Nat)(D:qD):Nat:=q6 D ((kO n D).filter (λ w=>(fM n D w).Nonempty))
def vD (n:Nat)(D:qD):Nat:=q6 D ((kO n D).filter (λ w=>¬(fM n D w).Nonempty))
def kl(n:Nat)(D:qD):tK:=(g5 (n+(tD D))).filter (λ w=>2<=kS D w)
def fX(n:Nat)(D:qD):tS n:=(kl n D).biUnion (fM n D)
def kH (n:Nat)(D:qD):Finset (Fin n):=univ \ fX n D
def qQ(n:Nat)(D:qD):tF U0:=(kO n D).sigma (λ w=>g5 (kS D w-1))
def ww(n:Nat)(D:qD):tF U0:=(qQ n D).filter (λ u=>(fM n D u.1).Nonempty)
def jw(D:qD):tF (tJ):=g5 (tD D)×ˢ p53
def fC(D:qD)(e:tJ):Nat:=if e.2=p63 then yf D e.1 else yx D e.1
def qc(n:Nat)(D:qD)(K:tK):tF (tJ):=(jw D).filter (λ e=>fC D e∈K/\n+e.1∉K)
def w5(n:Nat)(D:qD)(K:tK):tK:=(g5 (tD D)).filter (λ j=>n+j∈K/\yx D j∈K/\yf D j∈K)
def z8(n:Nat)(K:tK):tK:=K.filter (λ w=>w<n)
def q2(n:Nat)(D:qD)(T:tS n):tK:=(g5 (n+(tD D))).filter (λ w=>(fM n D w∩T).Nonempty)
def q4(n:Nat)(D:qD)(x y:Fin n):tK:=(g5 (n+(tD D))).filter (λ w=>x∈fM n D w/\y∉fM n D w)
def gN(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=kS D (b v)/\fM n D (b v)={v}
abbrev B5:=gN
def qh(n:Nat)(D:qD)(b:tY n):tF U0:=(fX n D).image (λ v=>(⟨b v,0⟩:U0))
def kP (n:Nat)(D:qD)(b:Fin n->Nat):Finset (U0):=ww n D \ qh n D b
section
variable (D:qD)(j:Nat)(h:j<(tD D))
include D j h
lemma xd :gZ D j=(D[j]).1:=by simp[gZ,p5 h]
lemma xe :yx D j=(D[j]).2.1:=by simp[yx,p5 h]
lemma xf :yf D j=(D[j]).2.2:=by simp[yf,p5 h]
end
lemma km(g:tG)(D:qD)(w:tL):wl (g::D) w=wl D (zp w g):=rfl
lemma vi(D E:qD)(w:tL):wl (D++E) w=wl E (wl D w):=by simp[wl,List.foldl_append]
lemma zf(w:tL)(g:tG):(zp w g).length=w.length+1:=by simp[zp]
lemma jk(D:qD):∀w:tL,(wl D w).length=w.length+(tD D):=by induction D with|nil=>{intro w;simp[wl]}|cons g D ih=>{intro w;rw[km,ih,zf];simp;omega}
lemma jo(w:tL)(g:tG)(i:Nat)(h:i<w.length):(zp w g).getD i p55=w.getD i p55:=by simp[zp,p4 h]
lemma jx(D:qD):∀(w:tL) (i:Nat),i<w.length->(wl D w).getD i p55=w.getD i p55:=by induction D with|nil=>{intro w i _;rfl}|cons g D ih=>{intro w i h;rw[km,ih _ _ (by rw[zf];omega),jo _ _ _ h]}
lemma b6(w:tL)(i:Nat)(h:w.length<=i):w.getD i p55=p55:=by simp[List.getElem?_eq_none h]
lemma zq(w:tL)(g:tG):(zp w g).getD w.length p55=xp g.1 (w.getD g.2.1 p55) (w.getD g.2.2 p55):=by simp[zp]
lemma kn(D:qD)(w:tL)(j:Nat)(a:j<(tD D)):(wl D w).getD (w.length+j) p55=xp (gZ D j) ((wl (D.take j) w).getD (yx D j) p55) ((wl (D.take j) w).getD (yf D j) p55):=by have c:D=D.take j++D[j]::D.drop (j+1):=by{simp};have d:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};rw[xd D j a,xe D j a,xf D j a];conv_lhs=>{rw[c,vi,km]};rw[jx _ _ _ (by rw[zf,d];omega),<-d,zq]
lemma zg(D:qD)(w:tL)(j i:Nat)(a:i<w.length+j)(c:j<=(tD D)):(wl (D.take j) w).getD i p55=(wl D w).getD i p55:=by have d:D=D.take j++D.drop j:=by{simp};have g:(wl (D.take j) w).length=w.length+j:=by{rw[jk,p10];omega};conv_rhs=>{rw[d,vi]};rw[jx (D.drop j) (wl (D.take j) w) i (by rw[g];exact a)]
section
variable (D:qD){n:Nat}(x:tX n)
include D n x
lemma qa(i:Nat)(h:i<n):fO D x i=x ⟨i,h⟩:=by unfold fO;rw[jx _ _ _ (by simpa using h)];simp[h]
lemma z0(w:Nat)(h:n+(tD D)<=w):fO D x w=p55:=by unfold fO;exact b6 _ _ (by rw[jk];simpa using h)
lemma xx(k w:Nat)(a:w<n+k)(c:k<=(tD D)):fO (D.take k) x w=fO D x w:=by unfold fO;exact zg D _ k w (by simpa using a) c
end
lemma qu{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(j:Nat)(a:j<(tD D)):fO D x (n+j)=xp (gZ D j) (fO D x (yx D j)) (fO D x (yf D j)):=by obtain⟨g,d,-⟩:=c j a;have h:=kn D (oF x) j a;simp only[p8] at h;unfold fO;rw[h,zg D _ j _ (by simpa using g) a.le,zg D _ j _ (by simpa using d) a.le]
lemma jy{n:Nat}{D:qD}(c:q0 n D)(x:tX n)(f:Nat->Bool)(a:∀i (h:i<n),f i=x ⟨i,h⟩)(d:∀j,j<(tD D)->f (n+j)=xp (gZ D j) (f (yx D j)) (f (yf D j))):∀w,w<n+(tD D)->fO D x w=f w:=by intro w;induction w using sI with|_ w ih=>{intro q;by_cases l:w<n;{rw[qa D x w l,a w l]};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};obtain⟨p,m,-⟩:=c j g;rw[qu c x j g,d j g,ih _ p (by omega),ih _ m (by omega)]}}
abbrev ko:=Bool ⊕ Nat
def qv(W:tL):ko->Bool
 | inl b=>b
 | inr k=>W.getD k p55
def wz(m:List ko)(i:Nat):ko:=m.getD i (inl p55)
def wf(t:Bool):ko->ko->ko ⊕ (Nat×Nat)
 | inl a,r=>inl (if a=t then r else inl a)
 | inr i,inl b=>inl (if b=t then inr i else inl b)
 | inr i,inr j=>if i=j then inl (inr i) else inr (i,j)
def w9:GateOp->Bool
 | GateOp.and=>p63
 | _=>p55
def qi(n:Nat)(st:List ko×qD)(g:Gate):List ko×qD:=match g.inputs with|[]=>(st.1++[inl (w9 g.op)],st.2)|[a]=>(st.1++[wz st.1 a],st.2)|a::b::_=>match wf (w9 g.op) (wz st.1 a) (wz st.1 b) with|inl r=>(st.1++[r],st.2)|inr p=>(st.1++[inr (n+st.2.length)],st.2++[(w9 g.op,p.1,p.2)])
def jp(B:Nat):ko->Prop
 | inl _=>True
 | inr k=>k<B
def v6(n:Nat)(st:List ko×qD):Prop:=q0 n st.2/\∀r∈st.1,jp (n+st.2.length) r
lemma xg{B a:Nat}(h:B<=a)(r:ko)(c:jp B r):jp a r:=by rcases r with b|k;{trivial};{exact lL c h}
lemma yg(W:tL)(m:List ko)(i:Nat):qv W (wz m i)=(m.map (qv W)).getD i p55:=by simp only[wz,p3,p6];cases m[i]?<;>rfl
lemma zh(B:Nat)(m:List ko)(a:∀r∈m,jp B r)(i:Nat):jp B (wz m i):=by simp only[wz,p3];rcases h:m[i]? with _|r;{trivial};{exact a r (List.mem_of_getElem? h)}
lemma vs(W:tL)(g:tG)(r:ko)(a:jp W.length r):qv (zp W g) r=qv W r:=by rcases r with b|k;{rfl};{exact jo W g k a}
lemma x5(t:Bool)(W:tL)(a b r:ko)(h:wf t a b=inl r):qv W r=xp t (qv W a) (qv W b):=by rcases a with a|i;{simp only[wf,hF] at h;subst h;cases t<;>cases a<;>simp[qv]};{rcases b with b|j;{simp only[wf,hF] at h;subst h;cases t<;>cases b<;>simp[qv]};{simp only[wf] at h;split_ifs at h with hij;simp only[hF] at h;subst h;subst hij;cases t<;>simp[qv]}}
lemma xh(B:Nat)(t:Bool)(a b r:ko)(c:jp B a)(d:jp B b)(h:wf t a b=inl r):jp B r:=by rcases a with a|i;{simp only[wf,hF] at h;subst h;split_ifs;{exact d};{trivial}};{rcases b with b|j;{simp only[wf,hF] at h;subst h;split_ifs;{exact c};{trivial}};{simp only[wf] at h;split_ifs at h;simp only[hF] at h;subst h;exact c}}
lemma x6(t:Bool)(a b:ko)(p:Nat×Nat)(h:wf t a b=inr p):a=inr p.1/\b=inr p.2/\p.1≠p.2:=by rcases a with a|i;{simp[wf] at h};{rcases b with b|j;{simp[wf] at h};{simp only[wf] at h;split_ifs at h with hij;cases h;exact⟨rfl,rfl,hij⟩}}
section
variable (op:GateOp)(a:op∈({GateOp.and,GateOp.or}:Set GateOp))
include op a
lemma xz :op.eval []=w9 op:=by rcases a with rfl|rfl<;>rfl
lemma b3(u:Bool):op.eval [u]=u:=by rcases a with rfl|rfl<;>simp[GateOp.eval]
lemma x7(u v:Bool):op.eval [u,v]=xp (w9 op) u v:=by rcases a with rfl|rfl<;>simp[GateOp.eval,w9]
end
lemma v7(D E:qD)(k:Nat)(h:k<(tD D)):(D++E).getD k (p55,0,0)=D.getD k (p55,0,0):=by simp[p4 h]
lemma kp(D:qD)(g:tG):(D++[g]).getD (tD D) (p55,0,0)=g:=by simp[]
lemma vz{n:Nat}{D:qD}(d:q0 n D)(t:Bool)(i j:Nat)(c:i<n+(tD D))(a:j<n+(tD D))(l:i≠j):q0 n (D++[(t,i,j)]):=by intro k m;simp only[lA,p9] at m;by_cases h:k<(tD D);{simp only[yx,yf,v7 D _ k h];exact d k h};{have g:k=(tD D):=by{omega};subst g;simp only[yx,yf,kp];exact⟨c,a,l⟩}
lemma k1{n:Nat}{D:qD}(a:q0 n D)(k:Nat):q0 n (D.take k):=by intro j g;simp only[p10] at g;have d:j<k:=by{omega};have c:j<(tD D):=by{omega};have e:(D.take k).getD j (p55,0,0)=D.getD j (p55,0,0):=by{simp[d]};simp only[yx,yf,e];exact a j c
lemma kq(n:Nat)(st:List ko×qD)(g:Gate)(d:g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2)(h:v6 n st):v6 n (qi n st g)/\(qi n st g).2.length<=st.2.length+1/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(qi n st g).1.map (qv (wl (qi n st g).2 (oF x)))=w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]:=by obtain⟨m,D⟩:=st;obtain⟨op,L⟩:=g;obtain⟨q,v⟩:=d;obtain⟨J,l⟩:=h;dsimp only at J l q v ⊢;rcases L with _|⟨a,_|⟨b,_|⟨c,P⟩⟩⟩;{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;trivial}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,qv,xz op q]}⟩};{exact⟨⟨J,λ r j=>by{simp only[qi,g6,lS] at j;rcases j with j|rfl;exact l r j;exact zh _ m l a}⟩,by simp[qi],λ x w y=>by{subst y;simp only[qi,p11,p12,p13,b3 op q,yg]}⟩};{have H:=zh _ m l a;have z:=zh _ m l b;rcases hc:wf (w9 op) (wz m a) (wz m b) with r|p;{exact⟨⟨by simpa only[qi,hc] using J,λ K j=>by{simp only[qi,hc,g6,lS] at j ⊢;rcases j with j|rfl;exact l K j;exact xh _ _ _ _ _ H z hc}⟩,by simp[qi,hc],λ x w y=>by{subst y;simp only[qi,hc,p11,p12,p13,x7 op q,x5 _ (wl D (oF x)) _ _ _ hc,yg]}⟩};{obtain⟨R,Q,M⟩:=x6 _ _ _ _ hc;rw[R] at H;rw[Q] at z;exact⟨⟨by simpa only[qi,hc] using vz J (w9 op) p.1 p.2 H z M,λ K j=>by{simp only[qi,hc,g6,lS,lA,p9] at j ⊢;rcases j with j|rfl;exact xg (by omega) K (l K j);show n+(tD D)<n+((tD D)+1);omega}⟩,by simp[qi,hc],λ x w y=>by{subst y;have u:=jk D (oF x);rw[p8] at u;have hW':wl (D++[(w9 op,p.1,p.2)]) (oF x)=zp (wl D (oF x)) (w9 op,p.1,p.2):=by{rw[vi];rfl};have X:m.map (qv (zp (wl D (oF x)) (w9 op,p.1,p.2)))=m.map (qv (wl D (oF x))):=List.map_congr_left (λ r j=>vs _ _ r (u.symm▸l r j));have U:(zp (wl D (oF x)) (w9 op,p.1,p.2)).getD (n+(tD D)) p55=xp (w9 op) ((m.map (qv (wl D (oF x)))).getD a p55) ((m.map (qv (wl D (oF x)))).getD b p55):=by{rw[<-u,zq,<-yg,<-yg,R,Q];rfl};simp only[qi,hc,hW',p11,p12,p13,X,qv,U,x7 op q]}⟩}};{simp at v}
lemma kr(n:Nat)(a:List Gate)(c:∀g∈a,g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2):∀st:List ko×qD,v6 n st->v6 n (a.foldl (qi n) st)/\(a.foldl (qi n) st).2.length<=st.2.length+a.length/\∀(x:tX n) (w:tL),st.1.map (qv (wl st.2 (oF x)))=w->(a.foldl (qi n) st).1.map (qv (wl (a.foldl (qi n) st).2 (oF x)))=a.foldl (λ w g=>w++[g.op.eval (g.inputs.map λ i=>w.getD i p55)]) w:=by induction a with|nil=>{exact λ st h=>⟨h,by simp,λ _ _ d=>d⟩}|cons g a ih=>{intro st h;obtain⟨q,v,p⟩:=kq n st g (c g (by simp)) h;obtain⟨m,u,l⟩:=ih (λ r j=>c r (by simp[j])) _ q;exact⟨m,by{simp only[lO,List.length_cons];omega},λ x w d=>by{simp only[lO];exact l x _ (p x w d)}⟩}
lemma b7(n:Nat)(x:tX n):((p20 n).map inr).map (qv (wl ([]:qD) (oF x)))=oF x:=by apply List.ext_getElem;{simp};{intro i a c;simp only[List.length_map,List.length_range] at a;simp[qv,wl,a]}
lemma z3{n:Nat}(C:Circuit)(a:Monotone2 C):(∃b:Bool,∀x:tX n,C.eval (oF x)=b)\/(∃i:Fin n,∀x:tX n,C.eval (oF x)=x i)\/(∃D:qD,q0 n D/\D≠[]/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x)):=by obtain⟨⟨v,l⟩,d,c⟩:=kr n C.gates a ((p20 n).map inr,([]:qD)) ⟨λ j z=>absurd z (by simp),λ r g=>by{simp only[p16,p17] at g;obtain⟨k,hk,rfl⟩:=g;simpa[jp] using hk}⟩;generalize C.gates.foldl (qi n) ((p20 n).map inr,([]:qD))=st at v l d c;obtain⟨m,D⟩:=st;dsimp only at v l d c;have p:∀x:tX n,C.eval (oF x)=qv (wl D (oF x)) (wz m C.output):=λ x=>by{rw[yg,c x (oF x) (b7 n x)];rfl};have hk:=zh _ m l C.output;rcases g:wz m C.output with b|k;{exact .inl ⟨b,λ x=>by{rw[p x,g];rfl}⟩};{rw[g] at hk;have hk':k<n+(tD D):=hk;by_cases q:k<n;{exact .inr (.inl ⟨⟨k,q⟩,λ x=>by{rw[p x,g];exact qa D x k q}⟩)};{have u:(D.take (k-n+1)).length=k-n+1:=by{rw[p10];omega};exact .inr (.inr ⟨D.take (k-n+1),k1 v _,λ h=>by{rw[h] at u;simp at u},by{simp only[List.length_nil,Nat.zero_add] at d;unfold Circuit.size;omega},λ x=>by{have y:qb n (D.take (k-n+1))=k:=by{unfold qb;rw[u];omega};rw[y,xx D x (k-n+1) k (by omega) (by omega),p x,g];rfl}⟩)}}
lemma zi{D:qD}{w:Nat}(h:kS D w=0)(j:Nat)(a:j<(tD D)):yx D j≠w/\yf D j≠w:=by unfold kS qg at h;rw[g8,gI] at h;have:=h (mR.2 a);tauto
def v8(c a:Nat):Nat:=if c<a then a-1 else a
def qw(c w:Nat):Nat:=if w<c then w else w+1
def y0(n j:Nat)(D:qD):qD:=(D.eraseIdx j).map (λ g=>(g.1,v8 (n+j) g.2.1,v8 (n+j) g.2.2))
lemma yb(n j:Nat)(D:qD)(a:j<(tD D)):(y0 n j D).length=(tD D)-1:=by simp[y0,List.length_eraseIdx,a]
lemma k2(n j:Nat)(D:qD)(k:Nat)(c:qw j k<(tD D)):gZ (y0 n j D) k=gZ D (qw j k)/\yx (y0 n j D) k=v8 (n+j) (yx D (qw j k))/\yf (y0 n j D) k=v8 (n+j) (yf D (qw j k)):=by have e:(y0 n j D).getD k (p55,0,0)=((D.getD (qw j k) (p55,0,0)).1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.1,v8 (n+j) (D.getD (qw j k) (p55,0,0)).2.2):=by{simp only[y0,p3,p6,List.getElem?_eraseIdx];unfold qw at c ⊢;split_ifs at c ⊢<;>simp[p5 c]};unfold gZ yx yf;rw[e];exact⟨rfl,rfl,rfl⟩
section
variable {n:Nat}{D:qD}(g:q0 n D)(j:Nat)(c:j<(tD D))(d:kS D (n+j)=0)
include n D g j c d
lemma jq :q0 n (y0 n j D):=by intro k u;rw[yb n j D c] at u;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};have h:(k<j/\qw j k=k)\/(j<=k/\qw j k=k+1):=by{unfold qw;split_ifs<;>omega};obtain⟨r,q,i⟩:=g _ hk';obtain⟨ra,p⟩:=zi d _ hk';obtain⟨-,m,l⟩:=k2 n j D k hk';rw[m,l];generalize qw j k=k' at *;generalize yx D k'=a at *;generalize yf D k'=b at *;refine⟨?_,?_,?_⟩<;>unfold v8<;>split_ifs<;>omega
lemma xi(x:tX n)(w:Nat)(h:w<n+((tD D)-1)):fO (y0 n j D) x w=fO D x (qw (n+j) w):=by refine jy (jq g j c d) x (λ u=>fO D x (qw (n+j) u)) (λ i l=>by{show fO D x (qw (n+j) i)=_;rw[show qw (n+j) i=i by{unfold qw;split_ifs<;>omega}];exact qa D x i l}) (λ k y=>by{rw[yb n j D c] at y;have hk':qw j k<(tD D):=by{unfold qw;split_ifs<;>omega};obtain⟨q,v,r⟩:=k2 n j D k hk';obtain⟨ra,p⟩:=zi d _ hk';have m:∀a,a≠n+j->qw (n+j) (v8 (n+j) a)=a:=λ a z=>by{unfold qw v8;split_ifs<;>omega};show fO D x (qw (n+j) (n+k))=_;rw[show qw (n+j) (n+k)=n+qw j k by{unfold qw;split_ifs<;>omega},q,v,r,m _ ra,m _ p];exact qu g x _ hk'}) w (by{rw[yb n j D c];exact h})
end
section
variable {n:Nat}(F:(tX n)->Bool)(a:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\F x≠F y)
include n F a
lemma x8 :∀(s:Nat) (D:qD),(tD D)=s->q0 n D->D≠[]->(∀x:tX n,fO D x (qb n D)=F x)->∃D':qD,fV n D'/\D'.length<=s/\∀x:tX n,fO D' x (qb n D')=F x:=by intro s;induction s using sI with|_ s ih=>{intro D r z q K;have Q:0<(tD D):=lP q;by_cases U:b5 n D;{exact⟨D,⟨z,U,q⟩,r.le,K⟩};{obtain⟨w,P,d⟩:∃w,w+1<n+(tD D)/\kS D w=0:=by_contra λ v=>U (λ w P=>by_contra λ h0=>v ⟨w,P,by omega⟩);by_cases m:w<n;{obtain⟨x,y,L,H⟩:=a ⟨w,m⟩;exact absurd (by{rw[<-K x,<-K y];have p:qb n D≠w:=by{unfold qb;omega};have l:=jy z y (λ u=>if u=w then y ⟨w,m⟩ else fO D x u) (λ i R=>by{by_cases c:i=w;subst c;simp;simp only[c,ite_false];rw[qa D x i R];exact L ⟨i,R⟩ (λ h=>c (congrArg Fin.val h))}) (λ j g=>by{obtain⟨ha,Z⟩:=zi d j g;have M:n+j≠w:=by{omega};simp only[M,ha,Z,ite_false];exact qu z x j g}) (qb n D) (by{unfold qb;omega});simp only[p,ite_false] at l;exact l.symm}) H};{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have g:j<(tD D):=by{omega};have J:=yb n j D g;obtain⟨D',h1,h2,h3⟩:=ih ((tD D)-1) (by omega) (y0 n j D) J (jq z j g d) (λ h=>by{rw[h] at J;simp at J;omega}) (λ x=>by{have Y:qb n (y0 n j D)=n+((tD D)-1)-1:=by{unfold qb;rw[J]};have X:qw (n+j) (n+((tD D)-1)-1)=qb n D:=by{unfold qw qb;split_ifs<;>omega};rw[Y,xi z j g d x _ (by omega),X];exact K x});exact⟨D',h1,by omega,h3⟩}}}
lemma yt(D:qD)(d:q0 n D)(c:D≠[])(g:∀x:tX n,fO D x (qb n D)=F x):∃D':qD,fV n D'/\D'.length<=(tD D)/\∀x:tX n,fO D' x (qb n D')=F x:=x8 F a (tD D) D rfl d c g
end
lemma zy{n:Nat}(C:Circuit)(a:Monotone2 C)(g:∀b:Bool,∃x:tX n,C.eval (oF x)≠b)(d:∀i:Fin n,∃x:tX n,C.eval (oF x)≠x i)(c:∀i:Fin n,∃x y:tX n,(∀k,k≠i->x k=y k)/\C.eval (oF x)≠C.eval (oF y)):∃D:qD,fV n D/\(tD D)<=C.size/\∀x:tX n,fO D x (qb n D)=C.eval (oF x):=by rcases z3 (n:=n) C a with ⟨b,p⟩|⟨i,m⟩|⟨D,q,j,l,r⟩;{obtain⟨x,h⟩:=g b;exact absurd (p x) h};{obtain⟨x,h⟩:=d i;exact absurd (m x) h};{obtain⟨D',v,z,u⟩:=yt (λ x=>C.eval (oF x)) c D q j r;exact⟨D',v,by omega,u⟩}
section
variable {n:ℕ} {D:qD}
lemma ql{w:Nat}:w∈kO n D↔w+1<n+(tD D):=by unfold kO;rw[mR];omega
lemma qf(j:Nat):fC D (j,p55)=yx D j:=by simp[fC]
lemma qo(j:Nat):fC D (j,p63)=yf D j:=by simp[fC]
lemma qz(a:q0 n D)(w:Nat)(h:n+(tD D)<=w+1):kS D w=0:=by unfold kS qg;rw[g8,gI];intro j d;have c:=mR.1 d;have:=a j c;omega
lemma wk(a:q0 n D){w:Nat}(h:1<=kS D w):w+1<n+(tD D):=by by_contra c;have:=qz a w (by omega);omega
lemma yo(P:tJ->Prop) [DecidablePred P]:((jw D).filter P).card=∑ j∈g5 (tD D),((if P (j,p55) then 1 else 0)+(if P (j,p63) then 1 else 0)):=by rw[p30,jw,Finset.sum_product];refine p51 rfl (λ j _=>?_);rw[Fintype.sum_bool,add_comm]
lemma ks:(jw D).card=2*(tD D):=by simp[jw,Finset.card_product,Nat.mul_comm]
lemma xq(d:q0 n D)(e:tJ)(a:e∈jw D):fC D e+1<n+(tD D):=by obtain⟨j,c⟩:=e;have g:j<(tD D):=by{simpa[jw] using a};have:=d j g;cases c;{rw[qf];omega};{rw[qo];omega}
lemma k3(a:q0 n D)(w:Nat):kS D w=((jw D).filter (λ e=>fC D e=w)).card:=by rw[yo,kS,qg,p30];refine p51 rfl (λ j c=>?_);have:=(a j (mR.1 c)).2.2;rw[qf,qo];split_ifs<;>omega
lemma zd(a:q0 n D)(K:tK):∑ w∈K,kS D w=((jw D).filter (λ e=>fC D e∈K)).card:=by rw[Finset.card_eq_sum_card_fiberwise (f:=fC D) (s:=(jw D).filter (λ e=>fC D e∈K)) (t:=K) (λ e c=>mem_coe.2 (mF.1 (mem_coe.1 c)).2)];refine p51 rfl (λ w d=>by{rw[k3 a,p38];congr 1;ext e;simp only[mF];exact⟨λ⟨c,rfl⟩=>⟨c,d,rfl⟩,λ⟨c,_,h⟩=>⟨c,h⟩⟩})
lemma yp{K:tK}(a:∀w∈K,1<=kS D w):q6 D K+K.card=∑ w∈K,kS D w:=by rw[q6,Finset.card_eq_sum_ones,<-p50];exact p51 rfl (λ w c=>Nat.sub_add_cancel (a w c))
lemma vj(h:fV n D):yr n D+n=(tD D)+1:=by obtain⟨d,j,a⟩:=h;have:=lP a;have:=yp (λ w g=>j w (ql.1 g));have:∑ w∈kO n D,kS D w=2*(tD D):=by{rw[zd d,Finset.filter_true_of_mem (λ e i=>ql.2 (xq d e i)),ks]};have:(kO n D).card=n+(tD D)-1:=Finset.card_range _;unfold yr;omega
lemma jz(n:Nat)(D:qD):yr n D=fJ n D+vD n D:=by unfold yr fJ vD q6;exact (fS _ _ _).symm
lemma vk(h:fV n D)(w:Nat)(c:w<n+(tD D)):RT (λ a b=>b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)) w (qb n D):=by obtain⟨l,m,-⟩:=h;generalize hk:n+(tD D)-w=k;induction k using sI generalizing w with|_ k ih=>{by_cases g:w+1=n+(tD D);{rw[show w=qb n D by{unfold qb;omega}]};{obtain⟨j,i⟩:=fz.1 (m w (by omega));simp only[qg,mF,mR] at i;have:=l j i.1;exact rH (b:=n+j) ⟨by omega,by omega,by simpa using i.2⟩ (ih (n+(tD D)-(n+j)) (by omega) (n+j) (by omega) rfl)}}
lemma w3{v:Fin n}{w:Nat}:v∈fM n D w↔fO D (q9 v) w=p63:=by simp[fM]
lemma x9(c:q0 n D)(x y:tX n)(a:∀i,x i=p63->y i=p63)(w:Nat):fO D x w=p63->fO D y w=p63:=by induction w using sI with|_ w ih=>{by_cases g:w<n;{rw[qa D x w g,qa D y w g];exact a _};{by_cases m:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have d:j<(tD D):=by{omega};obtain⟨l,h,-⟩:=c j d;rw[qu c x j d,qu c y j d];have:=ih _ l;have:=ih _ h;cases gZ D j<;>simp only[wV,A5,bA,bO]<;>tauto};{rw[z0 D x w (by omega)];simp}}}
lemma wc(D:qD)(i:Fin n):fM n D i.1={i}:=by ext v;rw[w3,qa D (q9 v) i.1 i.2];simp[q9,eq_comm]
lemma xn(D:qD)(w:Nat)(h:n+(tD D)<=w):fM n D w=∅:=by ext v;simp[w3,z0 D (q9 v) w h]
lemma yy(c:q0 n D)(j:Nat)(a:j<(tD D)):fM n D (n+j)=if gZ D j=p63 then fM n D (yx D j)∩fM n D (yf D j) else fM n D (yx D j)∪fM n D (yf D j):=by ext v;rw[w3,qu c _ j a];cases gZ D j<;>simp[w3]
lemma v9(h:fV n D)(K:tK)(c:K⊆kO n D)(a:∀j,j<(tD D)->n+j∈K->yx D j∈K\/yf D j∈K):(qc n D K).card+(w5 n D K).card=(z8 n K).card+q6 D K:=by obtain⟨p,q,-⟩:=h;have d:∀w∈K,w+1<n+(tD D):=λ w g=>ql.1 (c g);have J:q6 D K+K.card=((jw D).filter (λ e=>fC D e∈K)).card:=by{rw[<-zd p,yp (λ w g=>q w (d w g))]};have r:=p31 (s:=(jw D).filter (λ e=>fC D e∈K)) (λ e:tJ=>n+e.1∈K);rw[p38,p38] at r;have H:((jw D).filter (λ e=>fC D e∈K/\n+e.1∈K)).card=((g5 (tD D)).filter (λ j=>n+j∈K)).card+(w5 n D K).card:=by{rw[yo,w5,p30,p30,<-p50];refine p51 rfl (λ j l=>?_);have:=a j (mR.1 l);rw[qf,qo];by_cases m:n+j∈K<;>by_cases y:yx D j∈K<;>by_cases v:yf D j∈K<;>simp_all};have z:K.card=(z8 n K).card+((g5 (tD D)).filter (λ j=>n+j∈K)).card:=by{rw[<-p31 (s:=K) (λ w=>w<n),z8];congr 1;have i:K.filter (λ w=>¬w<n)=((g5 (tD D)).filter (λ j=>n+j∈K)).image (λ j=>n+j):=by{ext w;simp only[mF,mG,mR];exact⟨λ⟨g,u⟩=>⟨w-n,⟨by{have:=d w g;omega},by rwa[Nat.add_sub_cancel' (by omega)]⟩,by omega⟩,λ⟨j,⟨_,l⟩,h⟩=>⟨h▸l,by omega⟩⟩};rw[i,p33 _ (add_right_injective n)]};unfold qc;omega
lemma vt(T:tS n)(a:fM n D (qb n D)∩T=∅):q2 n D T⊆kO n D:=by intro w d;simp only[q2,mF,mR] at d;rw[ql];by_contra g;have c:w=qb n D:=by{unfold qb;omega};rw[c,a] at d;exact gk d.2
lemma jl(D:qD)(T:tS n):(z8 n (q2 n D T)).card=T.card:=by have c:z8 n (q2 n D T)=T.image (λ v:Fin n=>v.1):=by{ext w;simp only[z8,q2,mF,mR,mG];constructor;{rintro⟨⟨-,v,a⟩,d⟩;have g:fM n D w={⟨w,d⟩}:=wc D ⟨w,d⟩;rw[g,mI,mS] at a;exact⟨v,a.2,by rw[a.1]⟩};{rintro⟨v,a,rfl⟩;refine⟨⟨by have:=v.2;omega,v,?_⟩,v.2⟩;rw[wc];simp[a]}};rw[c,p33 _ Fin.val_injective]
lemma z4(h:fV n D)(T:tS n)(a:fM n D (qb n D)∩T=∅):(qc n D (q2 n D T)).card+(w5 n D (q2 n D T)).card=T.card+q6 D (q2 n D T):=by rw[<-jl D T];refine v9 h _ (vt T a) (λ j g i=>by{obtain⟨m,l,-⟩:=h.1 j g;simp only[q2,mF,mR] at i ⊢;obtain⟨v,c⟩:=i.2;rw[mI,yy h.1 j g] at c;split_ifs at c with ht;{rw[mI] at c;exact .inl ⟨by omega,v,mI.2 ⟨c.1.1,c.2⟩⟩};{rw[mN] at c;exact c.1.elim (λ d=>.inl ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩) (λ d=>.inr ⟨by omega,v,mI.2 ⟨d,c.2⟩⟩)}})
lemma va(h:fV n D)(x y:Fin n)(c:x≠y)(a:x∉fM n D (qb n D)):(qc n D (q4 n D x y)).card+(w5 n D (q4 n D x y)).card=1+q6 D (q4 n D x y):=by have m:q4 n D x y⊆kO n D:=λ w i=>by{simp only[q4,mF,mR] at i;rw[ql];by_contra r;have:w=qb n D:=by{unfold qb;omega};exact a (this▸i.2.1)};have p:z8 n (q4 n D x y)={x.1}:=by{ext w;simp only[z8,q4,mF,mR,mS];exact⟨λ⟨⟨_,d,_⟩,i⟩=>by{rw[wc D ⟨w,i⟩,mS] at d;rw[d]},λ h=>h▸⟨⟨by{have:=x.2;omega},by{rw[wc];exact m0 x},by{rw[wc,mS];exact λ r=>c r.symm}⟩,x.2⟩⟩};have q:=v9 h _ m (λ j v z=>by{obtain⟨K,J,-⟩:=h.1 j v;simp only[q4,mF,mR] at z ⊢;obtain⟨-,d,g⟩:=z;rw[yy h.1 j v] at d g;split_ifs at d g with ht;{rw[mI] at d g;exact if l:y∈fM n D (yx D j) then .inr ⟨by omega,d.2,λ r=>g ⟨l,r⟩⟩ else .inl ⟨by omega,d.1,l⟩};{rw[mN] at d g;exact d.elim (λ u=>.inl ⟨by omega,u,λ r=>g (.inl r)⟩) (λ u=>.inr ⟨by omega,u,λ r=>g (.inr r)⟩)}});rwa[p,fw] at q
lemma xr{u:U0}:u∈qQ n D↔u.1∈kO n D/\u.2+1<kS D u.1:=by rw[qQ,p44,mR];constructor<;>rintro⟨a,c⟩<;>exact⟨a,by omega⟩
lemma wh(n:Nat)(D:qD)(p:Nat->Prop) [DecidablePred p]:((qQ n D).filter (λ u=>p u.1)).card=q6 D ((kO n D).filter p):=by have a:(qQ n D).filter (λ u=>p u.1)=((kO n D).filter p).sigma (λ w=>g5 (kS D w-1)):=by{ext u;simp only[qQ,mF,p44];tauto};rw[a,Finset.card_sigma,q6];simp
lemma k4(n:Nat)(D:qD):(ww n D).card=fJ n D:=by unfold ww fJ;exact wh n D (λ w=>(fM n D w).Nonempty)
lemma zz{v:Fin n}:v∈fX n D↔∃w,2<=kS D w/\v∈fM n D w:=by simp only[fX,kl,mem_biUnion,mF,mR];constructor;{rintro⟨w,⟨-,c⟩,a⟩;exact⟨w,c,a⟩};{rintro⟨w,c,a⟩;refine⟨w,⟨?_,c⟩,a⟩;by_contra d;rw[xn D w (by omega)] at a;exact nE v a}
lemma zb{v:Fin n}:v∈kH n D↔∀w,v∈fM n D w->kS D w<=1:=by rw[kH,mD,zz];constructor;{rintro⟨-,h⟩ w a;by_contra d;exact h ⟨w,by omega,a⟩};{intro h;refine⟨mU v,?_⟩;rintro⟨w,a,c⟩;have:=h w c;omega}
lemma wg{v:Fin n}{T:tS n}:(({v}:tS n)∩T).Nonempty↔v∈T:=by constructor;{rintro⟨u,a⟩;rw[mI,mS] at a;exact a.1▸a.2};{intro h;exact⟨v,mI.2 ⟨m0 v,h⟩⟩}
lemma zr(b:tY n)(a:gN n D b):Set.InjOn (λ v=>(⟨b v,0⟩:U0)) (fX n D:Set (Fin n)):=by intro v i g c j;have d:b v=b g:=congrArg Sigma.fst j;have h:=(a v i).2;rw[d,(a g c).2] at h;exact (p48 h).symm
lemma yl(c:q0 n D)(b:tY n)(a:gN n D b):qh n D b⊆ww n D:=by intro u g;obtain⟨v,d,rfl⟩:=mG.1 g;obtain⟨j,h⟩:=a v d;have i:1<=kS D (b v):=by{omega};rw[ww,mF,xr];refine⟨⟨ql.2 (wk c i),?_⟩,?_⟩;{show 0+1<kS D (b v);omega};{show (fM n D (b v)).Nonempty;rw[h];exact Finset.singleton_nonempty v}
lemma ke(b:tY n)(a:gN n D b):(qh n D b).card=(fX n D).card:=p32 (zr b a)
lemma kf(c:q0 n D)(b:tY n)(a:gN n D b):(kP n D b).card+(fX n D).card=fJ n D:=by rw[<-ke b a,<-k4];exact p35 (yl c b a)
lemma jm(c:q0 n D)(b:tY n)(a:gN n D b)(T:tS n):q6 D (q2 n D T)=(T∩fX n D).card+((kP n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by have H:q6 D (q2 n D T)=((qQ n D).filter (λ u=>(fM n D u.1∩T).Nonempty)).card:=by{rw[wh n D (λ w=>(fM n D w∩T).Nonempty)];symm;refine sum_subset (λ w g=>by{rw[mF] at g;have:=ql.1 g.1;exact mF.2 ⟨mR.2 (by omega),g.2⟩}) (λ w g j=>by{rw[q2,mF] at g;have m:w∉kO n D:=λ hc=>j (mF.2 ⟨hc,g.2⟩);rw[ql] at m;simp[qz c w (by omega)]})};have z:(qQ n D).filter (λ u=>(fM n D u.1∩T).Nonempty)=(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)∪(kP n D b).filter (λ u=>(fM n D u.1∩T).Nonempty):=by{ext u;have i:=yl c b a;simp only[kP,ww,mN,mF,mD];exact⟨λ d=>if p:u∈qh n D b then .inl ⟨p,d.2⟩ else .inr ⟨⟨⟨d.1,d.2.mono fI⟩,p⟩,d.2⟩,λ| .inl d=>⟨(mF.1 (i d.1)).1,d.2⟩| .inr d=>⟨d.1.1.1,d.2⟩⟩};have r:(qh n D b).filter (λ u=>(fM n D u.1∩T).Nonempty)=(T∩fX n D).image (λ v=>(⟨b v,0⟩:U0)):=by{rw[qh,Finset.filter_image];congr 1;ext v;simp only[mF,mI];exact⟨λ⟨h,l⟩=>⟨by rwa[(a v h).2,wg] at l,h⟩,λ⟨q,h⟩=>⟨h,by rwa[(a v h).2,wg]⟩⟩};rw[H,z,fU (Finset.disjoint_filter_filter (show Disjoint (qh n D b) (kP n D b) from Finset.disjoint_sdiff)),r,p32 ((zr b a).mono (Finset.coe_subset.2 p40))]
end
def gL{n:Nat}(a:EP (Fin n))(w:Nat):Nat:=if h:w<n then (a ⟨w,h⟩).1 else w
def ui {n:Nat}(a:EP (Fin n))(D:qD):qD:=D.map (λ g=>(g.1,gL a g.2.1,gL a g.2.2))
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma yh{w:Nat}(h:w<n):gL a w=(a ⟨w,h⟩).1:=by simp[gL,h]
lemma qt{w:Nat}(h:n<=w):gL a w=w:=by simp[gL,p25.2 h]
lemma qy{m:Nat}(c:n<=m)(w:Nat):gL a w<m↔w<m:=by by_cases h:w<n;{rw[yh a h];have:=(a ⟨w,h⟩).2;constructor<;>intro<;>omega};{rw[qt a (p25.1 h)]}
lemma yz(w:Nat):gL a⁻¹ (gL a w)=w:=by by_cases h:w<n;{rw[yh a h,yh a⁻¹ (a ⟨w,h⟩).2];simp};{rw[qt a (p25.1 h),qt a⁻¹ (p25.1 h)]}
lemma BV'(w:Nat):gL a (gL a⁻¹ w)=w:=by simpa using yz a⁻¹ w
end
lemma AQ{n:Nat}(c:EP (Fin n)){a b:Nat}:gL c a=gL c b↔a=b:=by refine⟨λ h=>?_,congrArg _⟩;have:=congrArg (gL c⁻¹) h;rwa [yz,yz] at this
lemma wR{n:Nat}(a:EP (Fin n))(D:qD):(ui a D).length=(tD D):=by simp[ui]
lemma ba{n:Nat}(c:EP (Fin n))(D:qD)(j:Nat)(a:j<(tD D)):gZ (ui c D) j=gZ D j:=by rw[xd _ j (by rw[wR];exact a),xd D j a];simp[ui]
section
variable {n:Nat}(a:EP (Fin n))
include n a
lemma kt(D:qD)(j:Nat)(c:j<(tD D)):yx (ui a D) j=gL a (yx D j):=by rw[xe _ j (by rw[wR];exact c),xe D j c];simp[ui]
lemma ku(D:qD)(j:Nat)(c:j<(tD D)):yf (ui a D) j=gL a (yf D j):=by rw[xf _ j (by rw[wR];exact c),xf D j c];simp[ui]
lemma j3{D:qD}(c:q0 n D):q0 n (ui a D):=by intro j d;rw[wR] at d;obtain⟨l,i,g⟩:=c j d;rw[kt a D j d,ku a D j d];exact⟨(qy a (nL n j) _).2 l,(qy a (nL n j) _).2 i,λ h=>g ((AQ a).1 h)⟩
lemma fH{D:qD}(c:q0 n D)(x:tX n)(w:Nat):fO (ui a D) x (gL a w)=fO D (λ i=>x (a i)) w:=by by_cases h:w<n+(tD D);{refine (jy (j3 a c) x (λ l=>fO D (λ i=>x (a i)) (gL a⁻¹ l)) (λ i g=>by{show fO D (λ i=>x (a i)) (gL a⁻¹ i)=x ⟨i,g⟩;rw[yh a⁻¹ g,qa D _ _ (a⁻¹ ⟨i,g⟩).2];simp}) (λ j d=>by{rw[wR] at d;show fO D (λ i=>x (a i)) (gL a⁻¹ (n+j))=_;rw[qt a⁻¹ (nL n j),ba a D j d,kt a D j d,ku a D j d,yz,yz,qu c _ j d]}) (gL a w) (by{rw[wR];exact (qy a (nL _ _) w).2 h})).trans (by{show fO D (λ i=>x (a i)) (gL a⁻¹ (gL a w))=_;rw[yz]})};{have hw':=p25.1 h;rw[qt a (le_trans (nL _ _) hw'),z0 _ _ _ (by{rw[wR];exact hw'}),z0 _ _ _ hw']}
lemma wa(D:qD)(w:Nat):kS (ui a D) (gL a w)=kS D w:=by unfold kS qg;rw[wR];congr 1;apply filter_congr;intro j c;have hj':=mR.1 c;rw[kt a D j hj',ku a D j hj',AQ,AQ]
lemma kv{D:qD}(c:b5 n D):b5 n (ui a D):=by rcases eq_or_ne D [] with rfl|g;{exact c};{intro d j;rw[wR] at j;have i:=lP g;rw[<-BV' a d,wa];apply c;by_cases h:d<n;{have:=(qy a⁻¹ le_rfl d).2 h;omega};{rw[qt a⁻¹ (p25.1 h)];exact j}}
lemma CG{D:qD}(h:fV n D):fV n (ui a D):=⟨j3 a h.1,kv a h.2.1,by simpa[ui] using h.2.2⟩
lemma xa{D:qD}(d:q0 n D)(c:D≠[])(x:tX n):fO (ui a D) x (qb n (ui a D))=fO D (λ i=>x (a i)) (qb n D):=by have g:=lP c;have e:qb n (ui a D)=gL a (qb n D):=by{rw[qt a (by unfold qb;omega)];simp[qb,wR]};rw[e,fH a d]
lemma k5(v:Fin n):(λ i=>q9 v (a i))=q9 (a⁻¹ v):=by funext i;simp only[q9,decide_eq_decide];constructor;{intro h;rw[<-h];simp};{intro h;rw[h];simp}
end
lemma vh{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D)(w:Nat):fM n (ui c D) (gL c w)=(fM n D w).image c:=by ext v;simp only[fM,mF,mU,true_and,mG];rw[fH c d,k5];constructor;{intro h;exact⟨c⁻¹ v,h,by simp⟩};{rintro⟨a,g,rfl⟩;simpa using g}
namespace A0r
abbrev rL:=@wR
abbrev rS:=@vh
abbrev tI:=@BV'
abbrev gq:=@AQ
end A0r
open A0r
lemma ym{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):fX n (ui c D)=(fX n D).image c:=by ext v;simp only[fX,mem_biUnion,mG,kl,mF,mR];constructor;{rintro⟨h,⟨hw',g⟩,j⟩;obtain⟨w,rfl⟩:∃w,h=gL c w:=⟨gL c⁻¹ h,(tI c h).symm⟩;rw[rS c d,mG] at j;obtain⟨a,i,rfl⟩:=j;rw[wa] at g;rw[rL,qy c (nL _ _)] at hw';exact⟨a,⟨w,⟨hw',g⟩,i⟩,rfl⟩};{rintro⟨a,⟨w,⟨l,g⟩,i⟩,rfl⟩;refine⟨gL c w,⟨?_,?_⟩,?_⟩;{rw[rL];exact (qy c (nL _ _) w).2 l};{rw[wa];exact g};{rw[rS c d];exact Finset.mem_image_of_mem _ i}}
lemma CJ{n:Nat}(c:EP (Fin n)){D:qD}(d:q0 n D):kH n (ui c D)=(kH n D).image c:=by ext v;simp only[kH,ym c d,mD,mU,true_and,mG];constructor;{intro h;exact⟨c⁻¹ v,λ i=>h ⟨c⁻¹ v,i,by simp⟩,by simp⟩};{rintro⟨a,l,rfl⟩ ⟨b,j,g⟩;exact l (c.injective g▸j)}
lemma vu(n:Nat)(D:qD):(kH n D).card+(fX n D).card=n:=by have h:=p35 (Finset.subset_univ (fX n D));rw[Finset.card_univ,Fintype.card_fin] at h;exact h
def yi{n:Nat}(G:Fin n->Fin n->Prop)(x:tX n):Prop:=∃u v:Fin n,G u v/\x u=p63/\x v=p63
def gK(n:Nat)(G:Fin n->Fin n->Prop)(D:qD):Prop:=∀x:tX n,fO D x (qb n D)=p63↔yi G x
abbrev uz:=gK
def w6{n:Nat}(G:Fin n->Fin n->Prop):Prop:=(∀u v,G u v->G v u)/\(∀u,¬G u u)/\(∀v w,v≠w->∃z,G v z/\¬G w z)/\(∀u v,∃a,G u a/\a≠v)
def q5(n:Nat)(D:qD)(a b:Nat):Prop:=b<n+(tD D)/\n<=b/\(yx D (b-n)=a\/yf D (b-n)=a)
def q1{n:Nat}(u z:Fin n):tX n:=λ i=>decide (i=u)||decide (i=z)
def wm{n:Nat}(v:Fin n)(x:tX n):tX n:=λ i=>decide (i=v)||x i
def yc{n:Nat}(A:tS n):tX n:=λ i=>decide (i∈A)
lemma yu{α:Type}{r p:α->α->Prop}(h:∀a b,r a b->p a b){a b:α}(c:RT r a b):RT p a b:=by induction c with|refl=>{exact .refl}|tail _ d ih=>{exact rT ih (h _ _ d)}
section
variable {n:ℕ} {G:Fin n->Fin n->Prop} {D:qD}
lemma jr(v:Fin n)(x:tX n):∀k,k≠v->x k=wm v x k:=by intro k c;simp[wm,c]
lemma vb(v:Fin n)(x:tX n):wm v x v=p63:=by simp[wm]
lemma kg{x:tX n}{u:Fin n}(a:x u=p63):∀i,q9 u i=p63->x i=p63:=by intro i c;simp only[q9,dT] at c;rw[c];exact a
lemma q3(d:q0 n D){u:Fin n}{w:Nat}(c:u∈fM n D w){x:tX n}(a:x u=p63):fO D x w=p63:=x9 d (q9 u) x (kg a) w (w3.1 c)
lemma wx{v:Fin n}{w:Nat}(a:v∈fM n D w):w<n+(tD D):=by by_contra c;rw[xn D w (by omega)] at a;exact nE v a
section
variable (Q:q0 n D){j:Nat}(A:j<(tD D))
include Q j A
lemma qm(d:gZ D j=p63):fM n D (n+j)=fM n D (yx D j)∩fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma yj(d:gZ D j=p55):fM n D (n+j)=fM n D (yx D j)∪fM n D (yf D j):=by rw[yy Q j A];simp[d]
lemma Bf(d:gZ D j=p63)(s:Bool):fM n D (n+j)⊆fM n D (fC D (j,s)):=by rw[qm Q A d];cases s;{rw[qf];exact fI};{rw[qo];exact p40}
lemma w7(s:Bool):fC D (j,s)<n+j:=by obtain⟨g,d,-⟩:=Q j A;cases s;{rw[qf];exact g};{rw[qo];exact d}
lemma xj(s:Bool):fC D (j,s)≠fC D (j,!s):=by obtain⟨-,-,d⟩:=Q j A;cases s;{simpa[fC] using d};{simpa[fC] using d.symm}
end
lemma qs{j:Nat}(a:j<(tD D))(s:Bool):q5 n D (fC D (j,s)) (n+j):=by refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}
lemma y3{a b:Nat}:q5 n D a b↔∃j s,j<(tD D)/\b=n+j/\fC D (j,s)=a:=by constructor;{rintro⟨h,g,c|c⟩;{exact⟨b-n,p55,by omega,by omega,by rw[qf];exact c⟩};{exact⟨b-n,p63,by omega,by omega,by rw[qo];exact c⟩}};{rintro⟨j,s,d,rfl,rfl⟩;refine⟨by omega,by omega,?_⟩;rw[nA];cases s;{exact .inl (qf j).symm};{exact .inr (qo j).symm}}
lemma wb(c:q0 n D){a b:Nat}(h:q5 n D a b):a<b:=by obtain⟨i,g,d⟩:=h;have:=c (b-n) (by omega);omega
lemma wr{a c:Nat}(h:q5 n D a c):c-n∈qg D a:=by unfold qg;rw[mF,mR];exact⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma zs{a c:Nat}(h:q5 n D a c):1<=kS D a:=fz.2 ⟨_,wr h⟩
lemma qj{a c h:Nat}(g:q5 n D a c)(d:q5 n D a h)(i:kS D a=1):c=h:=by have l:=wr g;have j:=wr d;obtain⟨r,m⟩:=p29.1 (show (qg D a).card=1 from i);rw[m,mS] at l j;have:=g.2.1;have:=d.2.1;omega
lemma wn(g:q0 n D)(x y:tX n)(v:Fin n)(d:∀k,k≠v->x k=y k)(w:Nat)(c:fO D x w≠fO D y w):RT (λ a b=>q5 n D a b/\fO D x b≠fO D y b) v.1 w:=by induction w using sI with|_ w ih=>{by_cases l:w<n;{rw[qa D x w l,qa D y w l] at c;have i:(⟨w,l⟩:Fin n)=v:=by_contra λ hc=>c (d _ hc);rw[<-i]};{by_cases h:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};obtain⟨z,u,-⟩:=g j m;have q:=c;rw[qu g x j m,qu g y j m] at q;by_cases r:fO D x (yx D j)=fO D y (yx D j);exact rT (ih _ u λ p=>q (by rw[r,p])) ⟨⟨h,by omega,.inr (by rw[nA])⟩,c⟩;exact rT (ih _ z r) ⟨⟨h,by omega,.inl (by rw[nA])⟩,c⟩};{exact absurd (by rw[z0 D x w (by omega),z0 D y w (by omega)]) c}}}
def kw(n:Nat)(D:qD)(b v:Nat):Prop:=b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v (qb n D)
lemma k6(j:q0 n D)(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b:Nat)(d:kw n D b v.1)(i:fO D x b=fO D y b):fO D x (qb n D)=fO D y (qb n D):=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;exact m (congrArg (λ f=>fO D f (qb n D)) (funext λ k=>if hk:k=v then hk▸i else g k hk))};{exact d (yu (λ _ _ h=>⟨h.1,λ hc=>h.2 (hc▸i)⟩) (wn j x y v g _ m))}
def q7(n:Nat)(D:qD)(a b:Nat):Prop:=RT (λ a c=>q5 n D a c/\kS D a=1) a b
lemma wp(d:q0 n D){v b:Nat}(h:q7 n D v b):kw n D b v:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c g _ ih=>{by_cases m:b=a;{exact .inl m};{right;intro q;rcases rC q with j|⟨r,p,i⟩;{have y:=qz d a (by rw[j];unfold qb;omega);have u:=g.2;omega};{have l:c=r:=qj g.1 p.1 g.2;subst l;rcases ih with rfl|ih;{exact p.2 rfl};{exact ih i}}}}
lemma z9(a:q0 n D)(v:Fin n):∀w,v∈fM n D w->(∀u,u<w->v∈fM n D u->kS D u<=1)->q7 n D v.1 w:=by intro w;induction w using sI with|_ w ih=>{intro h d;by_cases p:w<n;{have:=wc D ⟨w,p⟩;rw[this,mS] at h;rw[h];exact .refl};{have r:=wx h;obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have m:j<(tD D):=by{omega};have g:∀s:Bool,v∈fM n D (fC D (j,s))->q7 n D v.1 (n+j):=λ s i=>by{have c:q5 n D (fC D (j,s)) (n+j):=qs m s;have hlt':=w7 a m s;have:=zs c;have:=d _ hlt' i;exact rT (ih _ hlt' i (λ u y=>d u (by omega))) ⟨c,by omega⟩};rw[yy a j m] at h;split_ifs at h with ht;exact g p55 (by{rw[qf];exact (mI.1 h).1});rcases mN.1 h with l|l;exact g p55 (by{rw[qf];exact l});exact g p63 (by{rw[qo];exact l})}}
lemma wd(d:w6 G)(v:Fin n):¬yi G (q9 v):=by rintro⟨a,c,g,h,hc⟩;simp only[q9,dT] at h hc;rw[h,hc] at g;exact d.2.1 _ g
lemma yv{u v:Fin n}(a:G u v):yi G (q1 u v):=⟨u,v,a,by simp[q1],by simp[q1]⟩
lemma qn(a:w6 G)(c:gK n G D):fM n D (qb n D)=∅:=fE.2 (λ v d=>wd a v ((c _).1 (w3.1 d)))
lemma yw(i:w6 G)(g:q0 n D)(h:gK n G D)(v:Fin n)(b:Nat)(d:kw n D b v.1):fM n D b⊆{v}:=by intro u M;rw[mS];by_contra L;obtain⟨p,l,q,-⟩:=i;obtain⟨z,K,m⟩:=q v u (Ne.symm L);have r:=k6 g _ _ v (jr v (q1 u z)) b d (by rw[q3 g M (by simp[q1]),q3 g M (by simp[wm,q1])]);have P:=(h (wm v (q1 u z))).2 ⟨v,z,K,vb v _,by simp[wm,q1]⟩;rw[<-r] at P;obtain⟨a,c,j,y,hc⟩:=(h _).1 P;simp only[q1,bO,dT] at y hc;rcases y with rfl|rfl<;>rcases hc with rfl|rfl;{exact l _ j};{exact m j};{exact m (p _ _ j)};{exact l _ j}
lemma vl(d:w6 G)(a:q0 n D)(g:gK n G D)(v:Fin n)(c:v∈fX n D):∃b,2<=kS D b/\fM n D b={v}/\q7 n D v.1 b:=by classical have h:∃w,2<=kS D w/\v∈fM n D w:=zz.1 c;obtain⟨p,l⟩:=p24 h;have i:q7 n D v.1 (p22 h):=z9 a v _ l (λ u m j=>by{have:=p23 h m;by_contra q;exact this ⟨by omega,j⟩});exact⟨p22 h,p,Finset.Subset.antisymm (yw d a g v _ (wp a i)) (p49.2 l),i⟩
def zt(n:Nat)(D:qD)(b:tY n):Prop:=∀v∈fX n D,2<=kS D (b v)/\fM n D (b v)={v}/\q7 n D v.1 (b v)
lemma zj(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,zt n D b:=by classical have h:∀v:Fin n,∃b,v∈fX n D->2<=kS D b/\fM n D b={v}/\q7 n D v.1 b:=by{intro v;by_cases g:v∈fX n D;{obtain⟨b,i⟩:=vl c a d v g;exact⟨b,λ _=>i⟩};{exact⟨0,λ h=>absurd h g⟩}};choose b i using h;exact⟨b,λ v g=>i v g⟩
lemma j4{b:tY n}(a:zt n D b):gN n D b:=λ v c=>⟨(a v c).1,(a v c).2.1⟩
lemma CA(c:w6 G)(a:q0 n D)(d:gK n G D):∃b:tY n,gN n D b:=by obtain⟨b,g⟩:=zj c a d;exact⟨b,j4 g⟩
lemma Bh{v:Fin n}:v∈kH n D↔v∉fX n D:=by simp[kH]
lemma vm(d:q0 n D){v:Fin n}(c:v∈kH n D){w:Nat}(a:v∈fM n D w):q7 n D v.1 w:=z9 d v w a (λ u _ g=>zb.1 c u g)
lemma Bi(g:w6 G)(a:q0 n D)(h:gK n G D){v:Fin n}(d:v∈kH n D){w:Nat}(c:v∈fM n D w):fM n D w={v}:=Finset.Subset.antisymm (yw g a h v w (wp a (vm a d c))) (p49.2 c)
lemma q8{v:Fin n}{w:Nat}:w∈q2 n D {v}↔v∈fM n D w:=by simp only[q2,mF,mR];constructor;{rintro⟨-,u,a⟩;rw[mI,mS] at a;exact a.2▸a.1};{intro h;exact⟨wx h,v,mI.2 ⟨h,m0 v⟩⟩}
lemma we{v:Fin n}{e:tJ}:e∈qc n D (q2 n D {v})↔e.1<(tD D)/\v∈fM n D (fC D e)/\v∉fM n D (n+e.1):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,q8]
lemma v1{v:Fin n}(a:v∈kH n D):q6 D (q2 n D {v})=0:=by unfold q6;refine p52 (λ w c=>?_);have:=zb.1 a w (q8.1 c);omega
lemma y4(i:w6 G)(c:q0 n D)(g:gK n G D){u v:Fin n}(d:G u v):∃j,j<(tD D)/\gZ D j=p63/\fO D (q1 u v) (n+j)=p63/\u∉fM n D (n+j)/\v∉fM n D (n+j)/\∃s:Bool,u∈fM n D (fC D (j,s))/\v∉fM n D (fC D (j,s))/\v∈fM n D (fC D (j,!s))/\u∉fM n D (fC D (j,!s)):=by classical have y:∃w,fO D (q1 u v) w=p63/\u∉fM n D w/\v∉fM n D w:=⟨qb n D,(g _).2 (yv d),by{rw[qn i g];simp},by{rw[qn i g];simp}⟩;obtain⟨l,p,m⟩:=p24 y;have q:∀a,a<p22 y->fO D (q1 u v) a=p63->u∈fM n D a\/v∈fM n D a:=λ a Q R=>by_contra λ hc=>by{rw[not_or] at hc;exact p23 y Q ⟨R,hc.1,hc.2⟩};generalize p22 y=w at l p m q;have Y:w<n+(tD D):=by{by_contra hc;rw[z0 D _ w (by omega)] at l;cases l};have Z:n<=w:=by{by_contra hc;rw[qa D _ w (by omega)] at l;have X:fM n D w={⟨w,by omega⟩}:=wc D ⟨w,by omega⟩;rw[X,mS] at p m;simp only[q1,bO,dT] at l;rcases l with h|h;exact p h.symm;exact m h.symm};obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have J:j<(tD D):=by{omega};obtain⟨Q,U,-⟩:=c j J;have H:=l;have A:=p;have B:=m;rw[qu c _ j J] at l;rw[yy c j J] at p m;cases ht:gZ D j;{rw[ht] at l p m;simp only[A5,bO] at l;simp only[bF,ite_false,mN,not_or] at p m;rcases l with h|h;{rcases q _ Q h with z|z;exact (p.1 z).elim;exact (m.1 z).elim};{rcases q _ U h with z|z;exact (p.2 z).elim;exact (m.2 z).elim}};{rw[ht] at l p m;simp only[wV,bA] at l;simp only[ite_true,mI,not_and] at p m;refine⟨j,J,ht,H,A,B,?_⟩;rcases q _ Q l.1 with P|P;{have M:=p P;have K:=(q _ U l.2).resolve_left M;exact⟨p55,P,λ h=>m h K,K,M⟩};{have M:=m P;have L:=(q _ U l.2).resolve_right M;exact⟨p63,L,M,P,λ h=>p h L⟩}}
lemma qe(c:w6 G)(h:fV n D)(d:gK n G D){v:Fin n}(g:v∈kH n D):∃e:tJ,e.1<(tD D)/\gZ D e.1=p63/\fM n D (fC D e)={v}/\fM n D (n+e.1)=∅/\(∀a,G v a->a∈fM n D (fC D (e.1,!e.2)))/\qc n D (q2 n D {v})={e}/\w5 n D (q2 n D {v})=∅:=by have R:=h.1;have P:=z4 h {v} (by{rw[qn c d];simp});rw[v1 g,fw] at P;have i:∀a,G v a->∃j s,j<(tD D)/\gZ D j=p63/\(j,s)∈qc n D (q2 n D {v})/\a∈fM n D (fC D (j,!s)):=λ a m=>by{obtain⟨j,X,ht,-,M,-,s,h1,-,Z,-⟩:=y4 c R d m;exact⟨j,s,X,ht,we.2 ⟨X,h1,M⟩,Z⟩};obtain⟨a0,Q,-⟩:=c.2.2.2 v v;obtain⟨K,s0,H,u,p,-⟩:=i a0 Q;have q:(qc n D (q2 n D {v})).card=1:=by{have:=fz.2 ⟨_,p⟩;omega};obtain⟨e,J⟩:=p29.1 q;rw[J,mS] at p;subst p;have M:=we.1 (J▸m0 _);have l:fM n D (fC D (K,s0))={v}:=Bi c R d g M.2.1;exact⟨(K,s0),H,u,l,p37 (λ x U=>M.2.2 ((mS.1 (l▸Bf R H u s0 U))▸U)),λ a m=>by{obtain⟨j,s,-,-,L,Y⟩:=i a m;rw[J,mS,Prod.mk.injEq] at L;obtain⟨rfl,rfl⟩:=L;exact Y},J,g8.1 (by omega)⟩
lemma j5(c:w6 G)(h:fV n D)(g:gK n G D){u v:Fin n}(d:G u v):u∈fX n D\/v∈fX n D:=by by_contra hc;rw[not_or] at hc;obtain⟨R,-,-,-,-,q,l,-⟩:=qe c h g (Bh.2 hc.1);obtain⟨Q,-,-,p,-,-,i,-⟩:=qe c h g (Bh.2 hc.2);obtain⟨j,K,-,-,y,r,s,P,-,M,-⟩:=y4 c h.1 g d;have J:(j,s)∈qc n D (q2 n D {u}):=we.2 ⟨K,P,y⟩;have H:(j,!s)∈qc n D (q2 n D {v}):=we.2 ⟨K,M,r⟩;rw[l,mS] at J;rw[i,mS] at H;subst J;subst H;obtain⟨a,m,z⟩:=c.2.2.2 u v;have L:a∈fM n D (fC D (j,!s)):=q a m;rw[p,mS] at L;exact z L
lemma vv{A:tS n}(d:∀a∈A,∀b∈A,¬G a b):¬yi G (yc A):=by rintro⟨a,c,g,h,hc⟩;simp only[yc,dT] at h hc;exact d a h c hc g
lemma vc(h:w6 G)(c:q0 n D)(g:gK n G D)(A:tS n)(i:∀a∈A,∀b∈A,¬G a b)(x:Fin n)(d:∃a∈A,G x a):∃j s,j<(tD D)/\gZ D j=p63/\x∈fM n D (fC D (j,s))/\x∉fM n D (n+j)/\Disjoint (fM n D (fC D (j,s))) A:=by by_contra H;have m:∀j s,j<(tD D)->gZ D j=p63->x∈fM n D (fC D (j,s))->x∉fM n D (n+j)->fO D (yc A) (fC D (j,s))=p63/\fO D (wm x (yc A)) (fC D (j,s))=p63:=λ j s p y q R=>by{obtain⟨a,K,J⟩:=Finset.not_disjoint_iff.1 (λ Z=>H ⟨j,s,p,y,q,R,Z⟩);exact⟨q3 c K (by simp[yc,J]),q3 c K (by simp[wm,yc,J])⟩};have P:∀w,x∉fM n D w->fO D (yc A) w=fO D (wm x (yc A)) w:=λ w=>by{induction w using sI with|_ w ih=>{intro r;by_cases M:w<n;{rw[qa D _ w M,qa D _ w M];rw[wc D ⟨w,M⟩,mS] at r;exact jr x _ _ (λ hc=>r hc.symm)};by_cases Y:w<n+(tD D);{obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by omega⟩;have p:j<(tD D):=by{omega};obtain⟨L,Q,-⟩:=c j p;rw[qu c _ j p,qu c _ j p];cases y:gZ D j;{rw[yj c p y,mN,not_or] at r;rw[ih _ L r.1,ih _ Q r.2]};{have v:=r;rw[qm c p y,mI,not_and] at v;by_cases l:x∈fM n D (yx D j);{have q:=m j p55 p y (l) r;rw[qf] at q;rw[ih _ Q (v l),q.1,q.2]};by_cases u:x∈fM n D (yf D j);{have q:=m j p63 p y (u) r;rw[qo] at q;rw[ih _ L l,q.1,q.2]};{rw[ih _ L l,ih _ Q u]}}};{rw[z0 D _ w (by omega),z0 D _ w (by omega)]}}};obtain⟨a,L,l⟩:=d;exact vv i ((g _).1 (P (qb n D) (qn h g▸nE x)▸(g _).2 ⟨x,a,l,vb x _,by simp[wm,yc,L]⟩))
def fD(n:Nat)(D:qD)(x:Fin n):tF (tJ):=qc n D (q2 n D {x})
def qZ (e:Nat×Bool):Nat×Bool:=(e.1,!e.2)
lemma Bg{x:Fin n}{e:tJ}:e∈fD n D x↔e.1<(tD D)/\x∈fM n D (fC D e)/\x∉fM n D (n+e.1):=we
lemma Bk(e:tJ):qZ (qZ e)=e:=by simp[qZ]
lemma uL{e f:tJ}(h:e.1=f.1):f=e\/f=qZ e:=by obtain⟨j,s⟩:=e;obtain⟨k,t⟩:=f;simp only at h;subst h;cases s<;>cases t<;>simp[qZ]
lemma uU(c:q0 n D){x:Fin n}{e:tJ}(a:e∈fD n D x):gZ D e.1=p63:=by obtain⟨g,d,h⟩:=Bg.1 a;by_contra i;rw[Bool.not_eq_true] at i;apply h;rw[yj c g i,mN];obtain⟨j,s⟩:=e;cases s;{left;simpa[fC] using d};{right;simpa[fC] using d}
namespace A0b
abbrev sM:=@Bg
abbrev sA:=@uU
abbrev sP:=@Bi
abbrev sU:=@Bf
abbrev sE:=@Bh
lemma sK{g:Nat}{s:Bool}:qZ (g,!s)=(g,s):=by cases s<;>rfl
lemma sX{D:qD}{g w:Nat}(h:yx D g=w\/yf D g=w):∃s,fC D (g,s)=w:=h.elim (λ h=>⟨p55,h⟩) (λ h=>⟨p63,h⟩)
end A0b
open A0b
lemma xt(a:w6 G)(h:fV n D)(c:gK n G D)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+q6 D (q2 n D {x}):=by have d:=z4 h {x} (by rw[qn a c];simp);rwa [fw] at d
lemma z5(d:w6 G)(c:q0 n D)(g:gK n G D){x y:Fin n}(a:G x y):∃e,e∈fD n D x/\qZ e∈fD n D y/\y∉fM n D (fC D e)/\x∉fM n D (fC D (qZ e))/\fO D (q1 x y) (n+e.1)=p63:=by obtain⟨j,m,-,h,l,i,s,u,r,q,p⟩:=y4 d c g a;exact⟨(j,s),sM.2 ⟨m,u,l⟩,sM.2 ⟨m,q,i⟩,r,p,h⟩
lemma qk(c:q0 n D){R:Nat->Nat->Prop}(d:∀a b,R a b->q5 n D a b){a b:Nat}(h:RT R a b):a<=b:=by induction h with|refl=>{exact le_refl _}|tail _ g ih=>{exact le_trans ih (le_of_lt (wb c (d _ _ g)))}
lemma j6(d:q0 n D){x:Fin n}(g:w5 n D (q2 n D {x})=∅){j:Nat}(c:j<(tD D))(a:x∈fM n D (n+j)):gZ D j=p55/\¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by have h:¬(x∈fM n D (yx D j)/\x∈fM n D (yf D j)):=by{intro m;have i:j∈w5 n D (q2 n D {x}):=by{rw[w5,mF,mR];exact⟨c,q8.2 a,q8.2 m.1,q8.2 m.2⟩};rw[g] at i;exact nE _ i};refine⟨?_,h⟩;by_contra l;rw[p59] at l;rw[qm d c l,mI] at a;exact h a
lemma j7(c:w6 G)(h:fV n D)(d:gK n G D)(b:tY n)(a:gN n D b)(x:Fin n):(fD n D x).card+(w5 n D (q2 n D {x})).card=1+(({x}:tS n)∩fX n D).card+((kP n D b).filter (λ u=>x∈fM n D u.1)).card:=by have m:=xt c h d x;have l:=jm h.1 b a {x};have j:(kP n D b).filter (λ u=>(fM n D u.1∩{x}).Nonempty)=(kP n D b).filter (λ u=>x∈fM n D u.1):=by{refine filter_congr (λ u _=>?_);constructor;{rintro⟨y,g⟩;rw[mI,mS] at g;exact g.2▸g.1};{intro i;exact⟨x,mI.2 ⟨i,m0 x⟩⟩}};rw[j] at l;omega
section
variable (Q:q0 n D)
include Q
lemma qd(x:tX n){j:Nat}(a:j<(tD D))(s:Bool):fO D x (n+j)=xp (gZ D j) (fO D x (fC D (j,s))) (fO D x (fC D (j,!s))):=by rw[qu Q x j a];cases s;{simp[fC]};{cases gZ D j<;>simp[fC,Bool.and_comm,Bool.or_comm]}
lemma vn{v b t:Nat}(h:q7 n D v b)(g:b<=t):b=v\/¬RT (λ a c=>q5 n D a c/\c≠b) v t:=by induction h using rI with|refl=>{exact .inl rfl}|@head a c i l ih=>{by_cases p:b=a;{exact .inl p};{right;intro u;rcases rC u with y|⟨z,r,j⟩;{have J:=wb Q i.1;have H:=qk Q (λ _ _ q=>q.1) l;omega};{have m:c=z:=qj i.1 r.1 i.2;subst m;rcases ih with rfl|ih;{exact r.2 rfl};{exact ih j}}}}
lemma kh(x y:tX n)(v:Fin n)(g:∀k,k≠v->x k=y k)(b t:Nat)(d:b=v.1\/¬RT (λ a c=>q5 n D a c/\c≠b) v.1 t)(i:fO D x b=fO D y b):fO D x t=fO D y t:=by by_contra m;rcases d with rfl|d;{rw[qa D x _ v.2,qa D y _ v.2] at i;have l:x=y:=by{funext k;by_cases p:k=v;{rw[p];exact i};{exact g k p}};exact m (by rw[l])};{exact d (yu (λ a c h=>⟨h.1,λ hc=>h.2 (by rw[hc];exact i)⟩) (wn Q x y v g _ m))}
lemma j8{a c q:Nat}(hc:q7 n D a c)(d:RT (q5 n D) a q):RT (q5 n D) c q\/(q7 n D q c/\q≠c):=by revert d;induction hc using rI with|refl=>{exact λ d=>.inl d}|@head a v h i ih=>{intro d;rcases rC d with l|⟨r,u,j⟩;{right;have z:=wb Q h.1;have y:=qk Q (λ _ _ p=>p.1) i;refine⟨?_,by omega⟩;rw[<-l];exact rH h i};{have m:v=r:=qj h.1 u h.2;subst m;exact ih j}}
lemma vd(v:Fin n){j:Nat}(c:j<(tD D))(s:Bool)(g:q7 n D v.1 (fC D (j,!s)))(i:kS D (fC D (j,!s))=1)(x y:tX n)(d:∀k,k≠v->x k=y k):fO D x (fC D (j,s))=fO D y (fC D (j,s)):=by by_contra z;have M:=yu (λ _ _ h=>h.1) (wn Q x y v d _ z);have:=w7 Q c s;have:=w7 Q c (!s);rcases j8 Q g M with H|⟨H,P⟩;{rcases rC H with q|⟨A,u,l⟩;exact xj Q c s q.symm;have r:=qj (qs c (!s)) u i;subst r;have:=qk Q (λ _ _ h=>h) l;omega};{rcases rC H with q|⟨L,u,l⟩;exact P q;have r:=qj (qs c s) u.1 u.2;subst r;have:=qk Q (λ _ _ h=>h.1) l;omega}
end
lemma ze(g:w6 G)(c:q0 n D)(h:gK n G D){i:Fin n}(d:i∈kH n D){b:Nat}(a:q7 n D i.1 b)(j:2<=kS D b):fM n D b=∅:=by have l:=yw g c h i b (wp c a);refine p37 (λ x m=>?_);have p:=l m;rw[mS] at p;have q:=zb.1 d b (p▸m);omega
lemma j9{a t:Nat}(c:RT (q5 n D) a t):q7 n D a t\/∃b,q7 n D a b/\2<=kS D b:=by induction c using rI with|refl=>{exact .inl rR}|@head a j d _ ih=>{by_cases h:kS D a=1;{rcases ih with g|⟨b,g,i⟩;{exact .inl (rH ⟨d,h⟩ g)};{exact .inr ⟨b,rH ⟨d,h⟩ g,i⟩}};{have:=zs d;exact .inr ⟨a,rR,by omega⟩}}
lemma yd(c:q0 n D){b:Nat}(d:2<=kS D b)(a:fM n D b=∅):b∈(kO n D).filter (λ w=>¬(fM n D w).Nonempty):=mF.2 ⟨ql.2 (wk c (w:=b) (by omega)),by rw[a];exact gk⟩
lemma y7(d:q0 n D)(a:vD n D=0){b:Nat}(c:2<=kS D b):(fM n D b).Nonempty:=by by_contra g;rw[fN] at g;have h:kS D b-1<=∑ w∈(kO n D).filter (λ w=>¬(fM n D w).Nonempty),(kS D w-1):=hE (f:=λ w=>kS D w-1) (λ _ _=>nZ _) (yd d c g);unfold vD q6 at a;omega
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(B:vD n D=0){i:Fin n}(M:i∈kH n D)
include K H C B i M
lemma v3{w:Nat}(c:RT (q5 n D) i.1 w):q7 n D i.1 w:=by rcases j9 c with l|⟨b,l,p⟩;{exact l};{have m:=y7 H.1 B p;rw[ze K H.1 C M l p] at m;exact absurd m gk}
lemma zv:q7 n D i.1 (qb n D):=v3 K H C B M (vk H i.1 (by have:=i.2;omega))
end
lemma zk{x y:Fin n}{w:Nat}:w∈q4 n D x y↔x∈fM n D w/\y∉fM n D w:=by simp only[q4,mF,mR];exact⟨λ h=>h.2,λ h=>⟨wx h.1,h⟩⟩
lemma y5{x y:Fin n}{e:tJ}:e∈qc n D (q4 n D x y)↔e.1<(tD D)/\(x∈fM n D (fC D e)/\y∉fM n D (fC D e))/\¬(x∈fM n D (n+e.1)/\y∉fM n D (n+e.1)):=by simp only[qc,jw,mF,mem_product,mR,mU,and_true,zk]
lemma vp(g:q0 n D)(b:tY n)(d:gN n D b){x y:Fin n}(a:x≠y)(c:x∈fX n D):q6 D (q4 n D x y)=1+((kP n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by have K:q6 D (q4 n D x y)=((qQ n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)).card:=by{rw[wh n D (λ w=>x∈fM n D w/\y∉fM n D w)];symm;refine sum_subset (λ w p=>zk.2 (mF.1 p).2) (λ w p l=>by{have q:w∉kO n D:=λ hc=>l (mF.2 ⟨hc,zk.1 p⟩);rw[ql] at q;simp[qz g w (by omega)]})};have J:(qQ n D).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1)={(⟨b x,0⟩:U0)}∪(kP n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=by{ext u;have j:=yl g b d;simp only[kP,ww,mN,mF,mD,mS];exact⟨λ h=>if r:u∈qh n D b then .inl (by{obtain⟨v,z,rfl⟩:=mG.1 r;have i:=h.2.1;rw[(d v z).2,mS] at i;rw[i]}) else .inr ⟨⟨⟨h.1,⟨x,h.2.1⟩⟩,r⟩,h.2⟩,λ| .inl h=>h▸⟨(mF.1 (j (mG.2 ⟨x,c,rfl⟩))).1,by{rw[(d x c).2];exact m0 x},by{rw[(d x c).2,mS];exact λ hc=>a hc.symm}⟩| .inr h=>⟨h.1.1.1,h.2⟩⟩};have H:(⟨b x,0⟩:U0)∉(kP n D b).filter (λ u=>x∈fM n D u.1/\y∉fM n D u.1):=λ hc=>(mD.1 (mF.1 hc).1).2 (mG.2 ⟨x,c,rfl⟩);rw[K,J,Finset.singleton_union,Finset.card_insert_of_notMem H];omega
lemma vw(c:q0 n D){x y:Fin n}(a:x≠y){w:Nat}(d:x∈fM n D w/\y∈fM n D w):∃j s,j<(tD D)/\gZ D j=p55/\x∈fM n D (n+j)/\y∈fM n D (n+j)/\x∈fM n D (fC D (j,s))/\y∉fM n D (fC D (j,s))/\y∈fM n D (fC D (j,!s))/\x∉fM n D (fC D (j,!s)):=by classical have l:∃u,x∈fM n D u/\y∈fM n D u:=⟨w,d⟩;obtain⟨m,p⟩:=p24 l;have i:∀u<p22 l,¬(x∈fM n D u/\y∈fM n D u):=λ _ J=>p23 l J;generalize p22 l=f at m p i;have L:=wx m;have Q:n<=f:=by{by_contra hc;have K:fM n D f={⟨f,by omega⟩}:=wc D ⟨f,by omega⟩;rw[K,mS] at m p;exact a (m.trans p.symm)};obtain⟨j,rfl⟩:∃j,f=n+j:=⟨f-n,by omega⟩;have H:j<(tD D):=by{omega};obtain⟨P,M,-⟩:=c j H;have q:=i _ P;have z:=i _ M;cases ht:gZ D j;{have h1':=m;have h2':=p;rw[yj c H ht,mN] at h1' h2';refine⟨j,?_⟩;rcases h1' with v|r;{have h:=λ hc=>q ⟨v,hc⟩;have g:=h2'.resolve_left h;exact⟨p55,H,ht,m,p,v,h,g,λ hc=>z ⟨hc,g⟩⟩};{have g:=λ hc=>z ⟨r,hc⟩;have h:=h2'.resolve_right g;exact⟨p63,H,ht,m,p,r,g,h,λ hc=>q ⟨hc,h⟩⟩}};{rw[qm c H ht,mI] at m p;exact absurd ⟨m.1,p.1⟩ q}
section
variable (K:w6 G)(H:fV n D)(C:gK n G D)(b:tY n)(P:gN n D b)
include K H C b P
lemma v4{x c z:Fin n}(a:x≠c)(m:x∈fX n D)(d:∀u∈kP n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(p:x∈fM n D w/\c∈fM n D w)(j:G x z)(g:¬G c z):q6 D (q4 n D x c)=1/\w5 n D (q4 n D x c)=∅/\(qc n D (q4 n D x c)).card=2/\∃e∈qc n D (q4 n D x c),gZ D e.1=p55/\c∈fM n D (n+e.1):=by have hS:=H.1;have r:q6 D (q4 n D x c)=1:=by{rw[vp hS b P a m,gI.2 (λ u y hc=>hc.2 (d u y hc.1)),Finset.card_empty]};have h4:=va H x c a (qn K C▸nE x);rw[r] at h4;obtain⟨U,R,h3,Z,Y,Q,B,A,-,-⟩:=vw hS a p;have M:(U,R)∈qc n D (q4 n D x c):=y5.2 ⟨h3,⟨B,A⟩,λ hc=>hc.2 Q⟩;obtain⟨j2,s2,h1,-,X,N,h6⟩:=vc K hS C {c,z} (λ u y v J=>by{simp only[p43,mS] at y J;rcases y with rfl|rfl<;>rcases J with rfl|rfl;{exact K.2.1 _};{exact g};{exact λ hc=>g (K.1 _ _ hc)};{exact K.2.1 _}}) x ⟨z,by simp,j⟩;have h5:(j2,s2)∈qc n D (q4 n D x c):=y5.2 ⟨h1,⟨X,λ hc=>p36.1 h6 hc (by simp)⟩,λ hc=>N hc.1⟩;have:=p46.2 ⟨_,M,_,h5,λ L=>N ((Prod.mk.inj L).1▸Y)⟩;exact⟨r,g8.1 (by omega),by omega,(U,R),M,Z,Q⟩
lemma bb{x c:Fin n}(a:x≠c)(i:x∈fX n D)(d:∀u∈kP n D b,x∈fM n D u.1->c∈fM n D u.1){w:Nat}(j:x∈fM n D w/\c∈fM n D w):∃e0,∀e∈fD n D x,e≠e0->c∈fM n D (fC D e):=by classical obtain⟨z,p,J⟩:=K.2.2.1 x c a;obtain⟨-,-,X,Q,y,q,-⟩:=v4 K H C b P a i d j p J;obtain⟨e0,B⟩:=p29.1 (show ((qc n D (q4 n D x c)).erase Q).card=1 by rw[Finset.card_erase_of_mem y,X]);refine⟨e0,λ e A r=>by_contra λ L=>?_⟩;obtain⟨Y,U,R⟩:=sM.1 A;exact r (mS.1 (B▸Finset.mem_erase.2 ⟨λ v=>Bool.false_ne_true (q▸v▸sA H.1 A),y5.2 ⟨Y,⟨U,L⟩,λ hc=>R hc.1⟩⟩))
end
end
end
end DagTools
class GIdx (gi:outParam (Fin 4)):Prop where ok:True
def k7T (gi:Fin 4):List (Nat×Nat):=(match gi.1 with|0=>[(0,3),(0,7),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]|1=>[(0,8),(0,9),(1,4),(1,9),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]|2=>[(0,8),(0,9),(1,3),(1,7),(2,5),(2,6),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)]|_=>[(0,8),(0,9),(1,3),(1,7),(2,4),(2,9),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9),(6,8),(7,8)])
def Bu (gi:Fin 4):List Nat:=(match gi.1 with|0=>[1,2,4,8,16,32,64,128,256,512,3,5,6,10,12,17,20,24,33,34,40,48,65,66,72,80,130,132,160,192,257,258,260,264,288,513,516,528,576,640,768,7,14,21,28,35,42,49,56,67,74,81,88,134,162,194,259,261,262,266,268,289,290,296,517,529,532,577,592,644,704,769,772,263,270,291,298,533,593,773]|1=>[1,2,4,16,32,64,256,512,3,5,17,33,65,6,10,34,66,130,258,20,260,516,48,80,528,288,576,768,7,11,35,67,131,21,49,81,14,134,262,42,74,266,162,290,194,532,772,592,15,135,43,75,163,195,270,298]|2=>[1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,20,24,33,34,40,48,65,66,72,80,129,132,160,192,258,260,264,288,514,516,528,576,640,768,7,13,19,21,22,25,28,35,41,49,50,56,67,73,81,82,88,133,161,193,262,268,290,296,518,530,532,578,592,644,704,770,772,23,29,51,57,83,89,534,594,774]|_=>[1,2,4,8,16,32,64,128,256,512,3,5,6,9,12,17,18,24,33,34,36,40,48,65,66,68,72,80,129,132,160,192,258,260,264,288,514,528,576,640,768,7,13,19,25,35,37,38,41,44,49,50,56,67,69,70,73,76,81,82,88,133,161,164,193,196,262,268,290,292,296,530,578,592,704,770,39,45,51,57,71,77,83,89,165,197,294,300,594])
def wO (gi:Fin 4)(e:Fin 14):Fin 10:=Fin.ofNat 10 ((k7T gi).getD e.val (0,0)).1
def wN (gi:Fin 4)(e:Fin 14):Fin 10:=Fin.ofNat 10 ((k7T gi).getD e.val (0,0)).2
def x4 (gi:Fin 4)(s:Bool)(e:Fin 14):Fin 10:=if s then wN gi e else wO gi e
def Ce (gi:Fin 4)(u v:Fin 10):List (Fin 14)->Fin 14×Bool
| []=>(0,false)
| e::rest=>if wO gi e==u&&wN gi e==v then (e,false) else if wN gi e==u&&wO gi e==v then (e,true) else Ce gi u v rest
def zC (gi:Fin 4)(u v:Fin 10):=Ce gi u v (List.finRange 14)
abbrev us (gi:Fin 4)(u v:Fin 10):Prop:=(Rup.nGN gi u.1).testBit v.1=true
def BU (a:List Nat)(v:Fin 10):Fin 10:=Fin.ofNat 10 (a.getD v.1 0)
def Ci:Equiv.Perm (Fin 10):=Equiv.refl (Fin 10)
def Dg:Equiv.Perm (Fin 10):=⟨BU [0,3,2,1,7,5,6,4,8,9],BU [0,3,2,1,7,5,6,4,8,9],by decide +kernel,by decide +kernel⟩
def A8 (gi:Fin 4)(a:Fin 2):Equiv.Perm (Fin 10):=if gi.1==1&&a.1==1 then Dg else Ci
def Bx (gi:Fin 4)(a:Fin 2)(m:Nat):Nat:=(List.finRange 10).foldl (λ c v=>if m.testBit v.1 then c|||(1<<<(A8 gi a v).1) else c) 0
def Bz (gi:Fin 4)(m:Nat):Bool:=(k7T gi).all (λ e=>!(m.testBit e.1&&m.testBit e.2))
def Bb (gi:Fin 4)(m:Nat):Bool:=m==0||!Bz gi m||(List.finRange 2).any (λ a=>(Bu gi).elem (Bx gi a m))
def AP (gi:Fin 4)(lo:Nat):Nat->Bool
| 0=>true
| n+1=>Bb gi lo&&AP gi (lo+1) n
lemma Cx:∀(gi:Fin 4)(u v:Fin 10),us gi u v->x4 gi (zC gi u v).2 (zC gi u v).1=u/\x4 gi (!(zC gi u v).2) (zC gi u v).1=v:=by decide +kernel
lemma wL:∀gi:Fin 4,DagTools.w6 (us gi):=by unfold DagTools.w6;decide +kernel
lemma C3:∀(gi:Fin 4)(u v:Fin 10),us gi u v↔(u.1,v.1)∈k7T gi\/(v.1,u.1)∈k7T gi:=by decide +kernel
lemma Cw:∀(gi:Fin 4)(e:Fin 14),us gi (wO gi e) (wN gi e):=by decide +kernel
lemma wK:∀gi:Fin 4,(6,8)∈k7T gi:=by decide +kernel
lemma uQ:∀(gi:Fin 4)(a:Fin 2)(i j:Fin 10),us gi (A8 gi a i) (A8 gi a j)↔us gi i j:=by decide +kernel
lemma Cy:∀gi:Fin 4,(List.range 16).all (λ b=>AP gi (b*64) 64)=true:=by decide +kernel
lemma Au:∀gi:Fin 4,(k7T gi).all (λ p=>decide (p.1<10/\p.2<10))=true:=by decide +kernel
section GraphSec
variable {gi:Fin 4} [hGI:GIdx gi]
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (card_le_univ nodup_toList univ)
open List (Nodup)
open DagTools
abbrev V:=Fin 10
abbrev wE:=Fin 14
section
open DagTools.A0
abbrev qO:=tJ
abbrev Slot:=qO
abbrev k7 {gi:Fin 4} [GIdx gi]:=k7T gi
def gJ(x:Fin 10->Bool):Prop:=∃u v:Fin 10,(u.1,v.1)∈k7/\x u=p63/\x v=p63
def fL(C:Circuit):Prop:=∀x:Fin 10->Bool,C.eval (oF x)=p63↔gJ x
abbrev wv {gi:Fin 4} [GIdx gi] (v:V):=Rup.nGN gi v.1
abbrev qW {gi:Fin 4} [GIdx gi] (u v:V):=us gi u v
end
namespace A1
abbrev EI:=wE
abbrev SL:=fV 10
abbrev PB:=gN 10
abbrev SC:=gK 10 qW
end A1
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1
abbrev kT {gi:Fin 4} [GIdx gi] (e:EI):=wO gi e
abbrev kU {gi:Fin 4} [GIdx gi] (e:EI):=wN gi e
abbrev wX {gi:Fin 4} [GIdx gi] (s:Bool)(e:EI):=x4 gi s e
def kF(s:Bool)(p:qO):qO:=(p.1,xor s p.2)
omit [GIdx gi] in @[simp] lemma zN(p:qO):kF p55 p=p:=by rcases p with ⟨g,b⟩;simp[kF]
omit [GIdx gi] in @[simp] lemma Ac(p:qO):kF p63 p=qZ p:=by rcases p with ⟨g,b⟩;cases b<;>rfl
omit [GIdx gi] in lemma AS(s:Bool)(p:qO):kF (!s) p=qZ (kF s p):=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
omit [GIdx gi] in lemma fK(s t:Bool)(p:qO):kF s (kF t p)=kF (xor s t) p:=by rcases p with ⟨g,b⟩;cases s<;>cases t<;>cases b<;>rfl
omit [GIdx gi] in lemma uT(s:Bool){p q:qO}(h:kF s p=kF s q):p=q:=by rcases p with ⟨g,c⟩;rcases q with ⟨d,a⟩;cases s<;>cases c<;>cases a<;>simp[kF] at h ⊢<;>exact h
abbrev fW {gi:Fin 4} [GIdx gi]:=zC gi
abbrev uJ:=fW
lemma wt(u v:V)(h:qW u v):wX (fW u v).2 (fW u v).1=u/\wX (!(fW u v).2) (fW u v).1=v:=Cx gi u v h
lemma uG:w6 qW:=wL gi
namespace A1b
abbrev G0:=uG
end A1b
open A1b
lemma ja:∀u v:V,qW u v↔(u.1,v.1)∈k7\/(v.1,u.1)∈k7:=C3 gi
lemma xk(e:EI):qW (kT e) (kU e):=Cw gi e
lemma xm(x:V->Bool):gJ x↔yi qW x:=by constructor;{rintro⟨u,v,e,d,c⟩;exact⟨u,v,(ja u v).2 (o1 e),d,c⟩};{rintro⟨u,v,a,d,c⟩;rcases (ja u v).1 a with e|e;{exact⟨u,v,e,d,c⟩};{exact⟨v,u,e,c,d⟩}}
lemma xu:¬gJ (λ _=>p55):=by rintro⟨_,_,_,h,_⟩;contradiction
lemma k8(i:V):¬gJ (q9 i):=λ h=>wd G0 i ((xm _).1 h)
lemma vX(C:Circuit)(c:Monotone2 C)(a:fL C):∃D:qD,SL D/\(tD D)<=C.size/\SC D:=by obtain⟨D,l,le,m⟩:=zy (n:=10) C c (by{intro b;cases b;{refine⟨λ _=>p63,?_⟩;rw[Ne,p59];exact (a _).2 ⟨6,8,wK gi,rfl,rfl⟩};{exact⟨λ _=>p55,λ h=>xu ((a _).1 h)⟩}}) (by{intro i;exact⟨q9 i,λ h=>k8 i ((a _).1 (by rw[h];simp[q9]))⟩}) (by{intro i;obtain⟨j,g,_⟩:=G0.2.2.2 i i;refine⟨q9 j,q1 i j,?_,?_⟩;{intro k d;simp[q1,q9,d]};{intro h;exact k8 j ((a _).1 (h.trans ((a _).2 ((xm _).2 (yv g)))))}});exact⟨D,l,le,λ x=>by rw[m,a];exact xm x⟩
def kM (m:Nat):Finset V:=univ.filter (λ v=>m.testBit v.val)
abbrev AA(T:tF V):Prop:=∀a∈T,∀b∈T,¬qW a b
def zw(a:EP V):Prop:=∀i j,qW (a i) (a j)↔qW i j
abbrev gA:=Ci
abbrev zU {gi:Fin 4} [GIdx gi]:=A8 gi
lemma bd:zw gA:=by intro i j;rfl
lemma vB(a:Fin 2):zw (zU a):=uQ gi a
lemma yS{D:qD}(h:SL D)(d:SC D)(c:EP V)(a:zw c):SC (ui c D):=by intro x;rw[xa c h.1 h.2.2,d];constructor;{rintro⟨u,v,g,j,i⟩;exact⟨c u,c v,(a _ _).2 g,j,i⟩};{rintro⟨u,v,g,j,i⟩;refine⟨c.symm u,c.symm v,(a _ _).1 (by simpa using g),by simpa using j,by simpa using i⟩}
omit [GIdx gi] in lemma yn(a:EP V)(D:qD)(c:D≠[]){w:Nat}:gL a w∈kO 10 (ui a D)↔w∈kO 10 D:=by have g:0<(tD D):=lP c;simp only[kO,mR,rL];by_cases d:w<10;{rw[yh a d];have:=(a ⟨w,d⟩).2;omega};{rw[qt a (by omega)]}
def gn(a:EP V)(b:V->Nat)(v:V):Nat:=gL a (b (a.symm v))
abbrev uM:=gn
omit [GIdx gi] in lemma CI(a:EP V){D:qD}(c:q0 10 D){b:V->Nat}(d:PB D b):PB (ui a D) (gn a b):=by intro v h;rw[ym a c] at h;obtain⟨u,i,rfl⟩:=mG.1 h;have g:=d u i;simp only[gn,Equiv.symm_apply_apply];refine⟨by rw[wa];exact g.1,?_⟩;rw[rS a c,g.2,Finset.image_singleton]
omit [GIdx gi] in lemma CH(a:EP V){D:qD}(h:SL D)(b:V->Nat)(u:U0):(⟨gL a u.1,u.2⟩:U0)∈kP 10 (ui a D) (gn a b)↔u∈kP 10 D b:=by rcases u with ⟨w,i⟩;simp only[kP,mD,ww,qQ,mF,p44,mR,qh,mG,ym a h.1,yn a D h.2.2,wa,rS a h.1,p39,Sigma.mk.inj_iff,heq_eq_eq];exact⟨λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨v,j,c⟩=>d ⟨a v,⟨v,j,rfl⟩,by simpa[gn] using ⟨congrArg (gL a) c.1,c.2⟩⟩⟩,λ⟨⟨⟨l,hr⟩,g⟩,d⟩=>⟨⟨⟨l,hr⟩,g⟩,λ⟨_,⟨v,j,rfl⟩,c⟩=>d ⟨v,j,by{simp only[gn,Equiv.symm_apply_apply] at c;exact⟨(gq a).1 c.1,c.2⟩}⟩⟩⟩
def gP(D:qD)(a:EI->qO):Prop:=∀s e,kF s (a e)∈fD 10 D (wX s e)/\wX (!s) e∉fM 10 D (fC D (kF s (a e)))
abbrev Df:=gP
lemma uW{D:qD}(c:q0 10 D)(a:SC D):∃edge:EI->qO,gP D edge:=by classical have j:∀e:EI,∃p:qO,p∈fD 10 D (kT e)/\qZ p∈fD 10 D (kU e)/\kU e∉fM 10 D (fC D p)/\kT e∉fM 10 D (fC D (qZ p)):=by{intro e;obtain⟨p,i,h,g,d,_⟩:=z5 G0 c a (xk e);exact⟨p,i,h,g,d⟩};choose edge hedge using j;refine⟨edge,λ s e=>?_⟩;cases s;{simpa[wX,zN] using ⟨(hedge e).1,(hedge e).2.2.1⟩};{simpa[wX,Ac] using ⟨(hedge e).2.1,(hedge e).2.2.2⟩}
def vG(c:EP V)(a:EI->qO)(e:EI):qO:=let p:=fW (c.symm (kT e)) (c.symm (kU e));kF p.2 (a p.1)
lemma uo(c:EP V)(a:EI->qO)(e:EI):(vG c a e).1=(a (fW (c.symm (kT e)) (c.symm (kU e))).1).1:=rfl
omit [GIdx gi] in lemma jb(a:EP V){D:qD}{p:qO}(c:p.1<(tD D)):fC (ui a D) p=gL a (fC D p):=by rcases p with ⟨g,s⟩;cases s<;>simp[fC,kt a D g c,ku a D g c]
omit [GIdx gi] in lemma ki(a:EP V){D:qD}(c:q0 10 D){x:V}{p:qO}:p∈fD 10 (ui a D) (a x)↔p∈fD 10 D x:=by simp only[sM,rL];constructor;{rintro⟨hlt,i,h⟩;rw[jb a hlt,rS a c] at i;have d:10<=10+p.1:=by{omega};rw[<-qt a d,rS a c] at h;refine⟨hlt,?_,?_⟩;{obtain⟨y,j,g⟩:=mG.1 i;exact a.injective g▸j};{intro l;exact h (mG.2 ⟨x,l,rfl⟩)}};{rintro⟨hlt,i,h⟩;refine⟨hlt,?_,?_⟩;{rw[jb a hlt,rS a c];exact mG.2 ⟨x,i,rfl⟩};{have d:10<=10+p.1:=by{omega};rw[<-qt a d,rS a c];rintro l;obtain⟨y,j,g⟩:=mG.1 l;exact h (a.injective g▸j)}}
omit [GIdx gi] in lemma B1{D:qD}(h:SL D)(a:(tD D)<=18)(b:V->Nat)(c:PB D b):(kP 10 D b).card+vD 10 D+1<=(kH 10 D).card:=by have j:=vj h;have i:=jz 10 D;have g:=vu 10 D;have d:=kf h.1 b c;omega
lemma vo{D:qD}(h:SL D)(c:SC D):AA (kH 10 D):=by intro a l b j i;rcases j5 G0 h c i with g|d;{exact (sE.1 l) g};{exact (sE.1 j) d}
abbrev CS {gi:Fin 4} [GIdx gi]:=Bu gi
abbrev zQ {gi:Fin 4} [GIdx gi]:=Bx gi
omit [GIdx gi] in lemma za(n k:Nat):(1<<<n).testBit k=decide (n=k):=by rw[p26,Nat.testBit_two_pow]
lemma k9(a:Fin 2)(m:Nat)(L:List V)(c:Nat)(k:Nat):(L.foldl (λ s v=>if m.testBit v.1 then s|||(1<<<(zU a v).1) else s) c).testBit k=(c.testBit k||L.any (λ v=>m.testBit v.1&&decide ((zU a v).1=k))):=by induction L generalizing c with|nil=>{simp}|cons v d ih=>{simp only[lO,p1,ih];by_cases g:m.testBit v.1=p63;{simp only[g,ite_true,p64,p27,za,p62]};{simp only[g,bF,ite_false,p56,p57]}}
lemma uF(a:Fin 2)(m:Fin 1024):kM (zQ a m.1)=(kM m.1).image (zU a):=by ext u;simp only[kM,zQ,Bx,mF,mU,true_and,mG,k9,p28,p57,p2,hC,bA,dT];constructor;{rintro⟨v,d,c⟩;exact⟨v,d,Fin.ext c⟩};{rintro⟨v,d,rfl⟩;exact⟨v,d,rfl⟩}
abbrev jc {gi:Fin 4} [GIdx gi]:=Bz gi
abbrev zc {gi:Fin 4} [GIdx gi]:=Bb gi
abbrev wu {gi:Fin 4} [GIdx gi]:=AP gi
lemma v5:(p20 16).all (λ b=>wu (b*64) 64)=p63:=Cy gi
lemma jd(a n m:Nat)(h:wu a n=p63)(c:a<=m)(d:m<a+n):zc m=p63:=by induction n generalizing a with|zero=>{omega}|succ n ih=>{simp only[wu,AP,bA] at h;by_cases g:m=a;{subst g;exact h.1};{exact ih (a+1) h.2 (by omega) (by omega)}}
lemma je{m:Nat}(a:AA (kM m)):jc m=p63:=by unfold jc Bz;rw[p0];intro e d;have c:e.1<10/\e.2<10:=of_decide_eq_true (p0.1 (Au gi) e d);cases h:m.testBit e.1<;>cases g:m.testBit e.2;rfl;rfl;rfl;exact absurd ((ja ⟨e.1,c.1⟩ ⟨e.2,c.2⟩).2 (.inl d)) (a ⟨e.1,c.1⟩ (mF.2 ⟨mU _,h⟩) ⟨e.2,c.2⟩ (mF.2 ⟨mU _,g⟩))
lemma uB(m:Fin 1024)(d:m.1≠0)(c:AA (kM m.1)):∃a:Fin 2,zQ a m.1∈CS:=by have j:=jd ((m.1/64)*64) 64 m.1 (p0.1 v5 (m.1/64) (p17.2 (by omega))) (by omega) (by omega);simp only[zc,Bb,je c,p61,Bool.or_false,bO,beq_iff_eq,p2,hC,true_and,List.elem_eq_mem,dT] at j;exact j.resolve_left d
omit [GIdx gi] in lemma kj(S:tF V)(L:List V)(a:Nat)(k:Nat):(L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) a).testBit k=(a.testBit k||L.any (λ v=>decide (v∈S)&&decide (v.1=k))):=by induction L generalizing a with|nil=>{simp}|cons v c ih=>{simp only[lO,p1,ih];by_cases d:v∈S;{simp only[d,ite_true,decide_true,p64,p27,za,p62]};{simp only[d,ite_false,decide_false,p56,p57]}}
omit [GIdx gi] in lemma kx(S:tF V)(L:List V)(c:Nat)(a:c<2^10):L.foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) c<2^10:=by induction L generalizing c with|nil=>{exact a}|cons v d ih=>{simp only[lO];by_cases g:v∈S;{simp only[g,ite_true];apply ih;apply Nat.or_lt_two_pow a;rw[p26];exact Nat.pow_lt_pow_right (by omega) v.2};{simp only[g,ite_false];exact ih c a}}
omit [GIdx gi] in lemma vF(S:tF V):∃m:Fin 1024,kM m.1=S:=by let n:Nat:=(lR 10).foldl (λ s v=>if v∈S then s|||(1<<<v.1) else s) 0;refine⟨⟨n,kx S (lR 10) 0 (by omega)⟩,?_⟩;ext v;simp only[kM,mF,mU,true_and,n,kj,p28,p57,p2,hC,bA,dT];exact⟨λ⟨u,d,a⟩=>Fin.ext a▸d,λ c=>⟨v,c,rfl⟩⟩
def fF(D:qD)(x:V):Nat:=(fD 10 D x).card
def qX(k I:Nat)(x:V):Nat:=if I.testBit x.1 then 1 else 2+k
def gQ(D:qD)(x:V)(j:Nat):Prop:=j<fF D x
abbrev AO:=gQ
def yB(D:qD)(x c:V):Prop:=∃w,x∈fM 10 D w/\c∈fM 10 D w
def zB(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(wv x).testBit y.1&&I.testBit y.1)
def yQ(I:Nat)(x:V):List V:=(lR 10).filter (λ y=>(wv x).testBit y.1&&!I.testBit y.1)
def yF(a:EI->qO)(x y:V):qO:=let p:=fW x y;kF p.2 (a p.1)
def wS(I:Nat)(a:EI->qO)(x:V):List qO:=let c:=zB I x;let d:=yQ I x;c.map (yF a x)++match d with|[]=>[]|y::_=>[yF a x y]
def yk(D:qD)(w:Nat):Nat:=∑ v∈fM 10 D w,2^v.1
def zl(D:qD):Option U0->Nat
 | none=>0
 | some u=>yk D u.1
def Ch(D:qD)(k I:Nat)(d:V->Nat->qO)(g:EI->qO)(c:V->Nat)(a:Fin k->Option U0):Prop:=PB D c/\(∀u∈kP 10 D c,∃t:Fin k,a t=some u)/\(∀t u,a t=some u->u∈kP 10 D c)/\(∀i h u,a i=some u->a h=some u->i=h)/\(∀i h:Fin k,i.1<h.1->zl D (a i)<=zl D (a h))/\(∀x,fF D x<=qX k I x)/\(∀x j,d x j∈fD 10 D x)/\(∀x m l,m<fF D x->l<fF D x->d x m=d x l->m=l)/\(∀x e,e∈fD 10 D x->∃j<fF D x,d x j=e)/\gP D g/\(∀x:V,¬I.testBit x.1->∀r,(hr:r<(wS I g x).length)->r<fF D x/\d x r=(wS I g x)[r])
end
namespace A2
abbrev G1:=Ch
abbrev L5{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.1
abbrev L6{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.1
abbrev L7{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.1
abbrev L8{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.1
abbrev L9{D k I W E F O}(g:G1 D k I W E F O):=g.2.2.2.2.2.2.2.2.2.1
end A2
section
open DagTools.A0 DagTools.A0r DagTools.A0b A1 A1b A2
lemma Ae{D:qD}{a:EI->qO}(c:gP D a){x y:V}(i:qW x y):yF a x y∈fD 10 D x/\qZ (yF a x y)∈fD 10 D y:=by have d:=wt x y i;unfold yF;have h:=(c (fW x y).2 (fW x y).1).1;have g:=(c (!(fW x y).2) (fW x y).1).1;rw[d.1] at h;rw[d.2,AS] at g;exact⟨h,g⟩
lemma z6{D:qD}(h:SL D)(g:SC D){I:Nat}(c:kM I=kH 10 D){a:EI->qO}(d:gP D a)(x:V):(wS I a x).Nodup/\∀p∈wS I a x,p∈fD 10 D x:=by have i:∀y∈zB I x,qW x y/\y∈kH 10 D:=λ y v=>by{simp only[zB,p15,hC,true_and,bA] at v;exact⟨v.1,c▸mF.2 ⟨mU _,v.2⟩⟩};have j:∀y∈yQ I x,qW x y/\y∉kH 10 D:=λ y v=>by{simp only[yQ,p15,hC,true_and,bA,Bool.not_eq_true'] at v;exact⟨v.1,by{rw[<-c,kM,mF];simp[v.2]}⟩};have u:∀y∈zB I x,fM 10 D (fC D (qZ (yF a x y)))={y}:=λ y v=>sP G0 h.1 g (i y v).2 (sM.1 (Ae d (i y v).1).2).2.1;have H:((zB I x).map (yF a x)).Nodup:=Nodup.map_on (λ M h0 L Z U=>p48 (((u M h0).symm.trans (U.symm▸u L Z)))) ((List.nodup_finRange 10).filter _);constructor;{unfold wS;cases r:yQ I x with|nil=>{simpa using H}|cons y _=>{refine p19.2 ⟨H,List.nodup_singleton _,λ p h3 q hq U=>?_⟩;simp only[lS] at hq;subst hq U;obtain⟨z,hz,Q⟩:=p16.1 h3;have ⟨hxy,hyn⟩:=j y (r▸p14);have l:=(sM.1 (Ae d hxy).2).2.1;rw[<-Q,u z hz,mS] at l;exact hyn (l▸(i z hz).2)}};{intro p m;unfold wS at m;rcases g6.1 m with Y|X;{obtain⟨y,v,rfl⟩:=p16.1 Y;exact (Ae d (i y v).1).1};{cases r:yQ I x with|nil=>{simp[r] at X}|cons y _=>{simp only[r,lS] at X;subst X;exact (Ae d (j y (r▸p14)).1).1}}}
lemma jn{D:qD}(h:SL D)(d:SC D){I:Nat}(c:kM I=kH 10 D){a:EI->qO}(g:gP D a)(x:V):(wS I a x).length<=fF D x:=by obtain⟨j,i⟩:=z6 h d c g x;rw[<-p21 j];exact p34 (λ p l=>i p (p18.1 l))
def b4(I:Nat)(x:V):Nat:=(zB I x).length+if (yQ I x).isEmpty then 0 else 1
lemma vx(I:Nat)(a:EI->qO)(x:V):(wS I a x).length=b4 I x:=by unfold wS b4;cases yQ I x<;>simp
section
variable {D:qD}(H:SL D)(S:SC D){k I:Nat}(M:kM I=kH 10 D){b:V->Nat}(P:PB D b)(K:(kP 10 D b).card<=k)
include D H S k I M b P K
lemma jf(x:V):fF D x<=qX k I x:=by unfold qX fF;by_cases l:I.testBit x.1=p63;{simp only[l,ite_true];have j:x∈kH 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨p,_,_,_,_,_,m,_⟩:=qe G0 H S j;change fD 10 D x={p} at m;rw[m,fw]};{simp[l];have i:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});have:=hO (kP 10 D b) (λ u=>x∈fM 10 D u.1);have:=j7 G0 H S b P x;simp only[fw] at i;omega}
lemma xc(x:V)(d:I.testBit x.1=p55)(g:2+k<b4 I x):False:=by obtain⟨l,m⟩:=uW H.1 S;have q:=jn H S M m x;rw[vx] at q;have p:=jf H S M P K x;simp only[qX,d,bF,ite_false] at p;omega
lemma Do{d:EI->qO}(l:gP D d):∃(wire:V->Nat->qO) (order:Fin k->Option U0),G1 D k I wire d b order:=by classical let R:=(kP 10 D b).toList;let A:=R.mergeSort (λ u v=>decide (yk D u.1<=yk D v.1));have U:A.Perm R:=List.mergeSort_perm R _;have h7:A.length=(kP 10 D b).card:=U.length_eq.trans (Finset.length_toList _);have h4:A.Nodup:=U.nodup_iff.2 (nodup_toList _);have hf:A.Pairwise (λ u v=>yk D u.1<=yk D v.1):=(List.pairwise_mergeSort (le:=λ u v:U0=>decide (yk D u.1<=yk D v.1)) (λ _ _ _ h1 h2=>decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))) (λ _ _=>by simp[Nat.le_total]) R).imp of_decide_eq_true;let C:List (Option U0):=List.replicate (k-A.length) none++A.map some;have X:C.length=k:=by{simp[C,h7];omega};let order:Fin k->Option U0:=λ t=>C[t.1]'(X.symm▸t.2);let L (x:V):List qO:=if I.testBit x.1 then [] else wS I d x;have Z (x:V):(L x).Nodup:=by{unfold L;split;exact .nil;exact (z6 H S M l x).1};have Y (x:V):∀p∈L x,p∈fD 10 D x:=by{unfold L;split;simp;exact (z6 H S M l x).2};let J (x:V):List qO:=L x++((fD 10 D x) \ (L x).toFinset).toList;have h3 (x:V):(J x).Nodup:=p19.2 ⟨Z x,nodup_toList _,λ p hp q hq h5=>by{subst h5;exact (mD.1 (p45.1 hq)).2 (p18.2 hp)}⟩;have N (x:V) (p:qO):p∈J x↔p∈fD 10 D x:=by{simp only[J,g6,p45,mD,p18];exact⟨λ| .inl h1=>Y x p h1| .inr h2=>h2.1,λ h1=>if hp:p∈L x then .inl hp else .inr ⟨h1,hp⟩⟩};have B (x:V):(J x).length=fF D x:=by{rw[<-p21 (h3 x)];congr 1;ext p;simp[N]};let wire (x:V) (j:Nat):qO:=if hj:j<(J x).length then (J x)[j] else (J x)[0]'(by{rw[B];obtain⟨y,xy,_⟩:=G0.2.2.2 x x;obtain⟨p,hp,_⟩:=z5 G0 H.1 S xy;exact fz.2 ⟨p,hp⟩});refine⟨wire,order,P,?_,?_,?_,?_,jf H S M P K,?_,?_,?_,l,?_⟩;{intro u hu;obtain⟨ht,f1,rfl⟩:=p7 (U.mem_iff.2 (p45.2 hu));exact⟨⟨k-A.length+ht,by omega⟩,by{simp only[order,C];rw[hH (by simp)];simp}⟩};{intro t u hw;have Q:some u∈C:=hw▸hL _;simp only[C,g6,List.mem_replicate,p16] at Q;rcases Q with ⟨_,hh⟩|⟨v,hv,h5⟩;cases hh;cases h5;exact p45.1 (U.mem_iff.1 hv)};{intro t1 t2 u h1 h2;have f2:∀t:Fin k,order t=some u->k-A.length<=t.1:=λ t ht=>by{by_contra c;simp only[order,C] at ht;rw[hG (by{simp;omega}),List.getElem_replicate] at ht;cases ht};have:=f2 t1 h1;have:=f2 t2 h2;simp only[order,C] at h1 h2;rw[hH (by{simp;omega})] at h1 h2;simp only[hK,List.getElem_map,hI] at h1 h2;have:=(Nodup.getElem_inj_iff h4).1 (h1.trans h2.symm);exact Fin.ext (by omega)};{intro t1 t2 c;have hg:C.Pairwise (λ a b=>zl D a<=zl D b):=by{rw[List.pairwise_append];refine⟨List.pairwise_replicate.2 (.inr (Nat.le_refl 0)),List.pairwise_map.2 hf,?_⟩;intro a ha _ _;rw[List.eq_of_mem_replicate ha];exact nZ _};exact List.pairwise_iff_getElem.1 hg t1.1 t2.1 (X.symm▸t1.2) (X.symm▸t2.2) c};{intro x j;unfold wire;split<;>exact (N x _).1 (hL _)};{intro x j1 j2 hm hl h5;rw[<-B x] at hm hl;simp only[wire,hm,hl,hD] at h5;exact (Nodup.getElem_inj_iff (h3 x)).1 h5};{intro x e he;obtain⟨j,hj,rfl⟩:=p7 ((N x e).2 he);exact⟨j,B x▸hj,by simp[wire,hj]⟩};{intro x hy r hr;have hd:L x=wS I d x:=by{simp[L,hy]};have c:r<(J x).length:=by{simp only[J,lA,hd];omega};exact⟨B x▸c,by{simp only[wire,c,hD,J];rw[hG (hd▸hr)];simp[hd]}⟩}
end
def kA(D:qD){k:Nat}(a:Fin k->Option U0)(t:Nat)(x:V):Prop:=∃c:t<k,match a ⟨t,c⟩ with|none=>False|some u=>x∈fM 10 D u.1
def gR(D:qD)(x:V):Prop:=1<=(w5 10 D (q2 10 D {x})).card
abbrev wJ:=gR
def qA(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (qZ (a x j)))
def uj(D:qD)(a:V->Nat->qO)(x:V)(j:Nat)(y:V):Prop:=gQ D x j/\y∈fM 10 D (fC D (a x j))
def vW(D:qD){k:Nat}(c:V->Nat->qO)(a:Fin k->Option U0)(t:Nat)(x:V)(j:Nat):Prop:=gQ D x j/\∀y:V,kA D a t y->uj D c x j y
def ra(D:qD)(a:V->Nat->qO)(c:EI->qO)(s:Bool)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\a x j=kF s (c e)
def gT(D:qD)(a:V->Nat->qO)(c:EI->qO)(x:V)(j:Nat):Prop:=gQ D x j/\∀(e:EI) (s:Bool),a x j≠kF s (c e)
abbrev BF:=gT
def gU(D:qD)(a:V->Nat->qO)(x:V)(j:Nat):Prop:=gQ D x j/\fM 10 D (fC D (qZ (a x j)))=∅
abbrev Di:=gU
def vQ(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=gQ D x j/\(c e).1<(a x j).1
def Cu(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=vQ D a c e x j/\gT D a c x j
def AN(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(x:V)(j:Nat):Prop:=vQ D a c e x j/\gU D a x j
lemma AB{D:qD}(h:SL D)(c:SC D){x:V}(a:x∈kH 10 D):¬gR D x:=by obtain⟨_,_,_,_,_,_,_,d⟩:=qe G0 h c a;simp[gR,d]
lemma ka{D:qD}{a:V->Nat->qO}{c:EI->qO}(g:gP D c){x:V}{j:Nat}(d:gU D a x j):gT D a c x j:=by refine⟨d.1,λ e s i=>?_⟩;have l:=(g (!s) e).1;rw[AS,<-i] at l;have h:=(sM.1 l).2.1;rw[d.2] at h;exact nE _ h
lemma Cs{D:qD}(g:q0 10 D)(d:SC D){x y:V}(c:x∈kH 10 D)(a:x≠y):¬yB D x y:=by rintro⟨w,hxw,hyw⟩;have h:=sP G0 g d c hxw;rw[h,mS] at hyw;exact a hyw.symm
section
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
lemma Dp(h:SL D)(d:SC D)(c:G1 D k I W E F O){x y:V}(a:yB D x y):(∃j<qX k I x,uj D W x j y)\/(∃l<qX k I y,uj D W y l x):=by obtain⟨w0,v,U⟩:=a;let S:=(g5 (10+(tD D))).filter (λ w=>x∈fM 10 D w/\y∈fM 10 D w);have M:S.Nonempty:=⟨w0,mF.2 ⟨mR.2 (wx v),v,U⟩⟩;set w:=S.max' M;have ⟨H,hxw,hyw⟩:=mF.1 (p42 S M);have:=mR.1 H;have z:w+1<10+(tD D):=by{have p:w≠qb 10 D:=λ h0=>nE x (qn G0 d▸h0▸hxw);unfold qb at p;omega};obtain⟨g,hg⟩:=fz.1 (nT nO (h.2.1 w z));obtain⟨q,Q⟩:=mF.1 hg;have hg_lt':=mR.1 q;obtain⟨s,K⟩:=sX Q;have J:=K▸w7 h.1 hg_lt' s;have m:¬(x∈fM 10 D (10+g)/\y∈fM 10 D (10+g)):=λ r=>by{have:=p41 S (10+g) (mF.2 ⟨mR.2 (by omega),r⟩);omega};by_cases u:x∈fM 10 D (10+g);{obtain⟨l,i,X⟩:=L8 c y (g,s) (sM.2 ⟨hg_lt',K▸hyw,λ hy=>m ⟨u,hy⟩⟩);exact .inr ⟨l,lL i (L5 c y),i,X▸K▸hxw⟩};{obtain⟨j,i,Y⟩:=L8 c x (g,s) (sM.2 ⟨hg_lt',K▸hxw,u⟩);exact .inl ⟨j,lL i (L5 c x),i,Y▸K▸hyw⟩}
lemma C1{x y:V}{j:Nat}(h:uj D W x j y):gQ D x j:=h.1
lemma Cz(c:G1 D k I W E F O){x:V}{j:Nat}(a:gQ D x j):uj D W x j x:=⟨a,(sM.1 (L6 c x j)).2.1⟩
lemma C2(c:G1 D k I W E F O){x y:V}{j:Nat}(a:uj D W x j y):yB D x y:=⟨fC D (W x j),(sM.1 (L6 c x j)).2.1,a.2⟩
lemma By(c:q0 10 D)(a:SC D)(x:V):gQ D x 0:=by obtain⟨y,d,_⟩:=G0.2.2.2 x x;obtain⟨p,g,_⟩:=z5 G0 c a d;exact fz.2 ⟨p,g⟩
lemma Da(d:G1 D k I W E F O)(a:kM I=kH 10 D){t:Nat}{x:V}(c:I.testBit x.1=p63):¬kA D O t x:=by rintro⟨p,g⟩;cases j:O ⟨t,p⟩ with|none=>{rw[j] at g;exact g}|some u=>{rw[j] at g;have:=mR.1 (p44.1 (mF.1 (mD.1 (d.2.2.1 ⟨t,p⟩ u j)).1).1).2;exact (sE.1 (a▸mF.2 ⟨mU _,c⟩)) (zz.2 ⟨u.1,by omega,g⟩)}
lemma CM{t:Nat}{x y:V}(a:kA D O t x)(c:kA D O t y):yB D x y:=by obtain⟨g,a⟩:=a;obtain⟨_,c⟩:=c;cases d:O ⟨t,g⟩ with|none=>{rw[d] at a;exact a.elim}|some u=>{rw[d] at a c;exact⟨u.1,a,c⟩}
lemma Dw(h:SL D)(d:SC D){i a b:V}(c:i∈kH 10 D)(j:qW i a)(g:qW i b):yB D a b:=by obtain⟨e,_,_,_,_,l,_,_⟩:=qe G0 h d c;exact⟨fC D (e.1,!e.2),l a j,l b g⟩
lemma ky(a:G1 D k I W E F O)(x:V):haveI:=cP (λ t:Fin k=>kA D O t.1 x);((p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x)).card=((kP 10 D F).filter (λ u=>x∈fM 10 D u.1)).card:=by classical let S:=(p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x);let T:=(kP 10 D F).filter (λ u=>x∈fM 10 D u.1);have g:∀t∈S,∃u∈T,O t=some u:=λ t L=>by{obtain⟨_,c⟩:=(mF.1 L).2;cases p:O t with|none=>{rw[p] at c;exact c.elim}|some u=>{rw[p] at c;exact⟨u,mF.2 ⟨a.2.2.1 t u p,c⟩,rfl⟩}};have Y:=hN (λ t=>(O t).getD ⟨0,0⟩) (λ t L=>by{obtain⟨u,h,p⟩:=g t L;simpa[p] using h}) (λ R K Q J d=>by{obtain⟨v,_,m⟩:=g R K;obtain⟨P,_,l⟩:=g Q J;simp only[m,l,Option.getD_some] at d;exact a.2.2.2.1 R Q v m (d▸l)});have X:T.card<=S.card:=by{by_cases U:k=0;{subst U;have M:T=∅:=fE.2 (λ u h=>(a.2.1 u (mF.1 h).1).elim (λ t _=>t.elim0));simp[M]};choose f hf using a.2.1;refine hN (λ u=>if h:u∈kP 10 D F then f u h else ⟨0,Nat.pos_of_ne_zero U⟩) (λ u h=>by{have ⟨j,y⟩:=mF.1 h;simp only[j,hD];exact mF.2 ⟨mU _,(f u j).2,by simpa[hf u j] using y⟩}) (λ v H P z d=>by{have r:=(mF.1 H).1;have q:=(mF.1 z).1;simp only[r,q,hD] at d;exact Option.some.inj ((hf v r).symm.trans (d▸hf P q))})};change S.card=T.card;omega
omit [GIdx gi] in lemma sC{x:V}{d:Nat}{S:tF (Fin k)}[DecidablePred (λ t:Fin k=>kA D O t.1 x)](i:S.card=k-d)(u:d+1<=((p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x)).card):∃t∈S,kA D O t.1 x:=by by_contra l;push Not at l;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x);have m:(S∪C).card<=k:=by{simpa using card_le_univ (S∪C)};rw[fU (p36.2 λ t r p=>l t r (mF.1 p).2)] at m;omega
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)
include H S G
lemma wo(x:V):haveI:=cP (λ t:Fin k=>kA D O t.1 x);fF D x+(w5 10 D (q2 10 D {x})).card<=2+((p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x)).card:=by classical have i:=j7 G0 H S F G.1 x;have d:=p34 (fI:({x}:tF V)∩fX 10 D⊆{x});simp only[fw] at d;have g:=ky G x;change ((p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x)).card=_ at g;unfold fF;omega
lemma CB(x:V)(d:Nat)(A:tF (Fin k))(i:A.card=k-d)(a:gQ D x (2+d)):∃t∈A,kA D O t.1 x:=by classical have q:=wo H S G x;exact sC i (by{unfold gQ at a;change _<=2+_ at q;omega})
lemma Dc(x:V)(a:gR D x):¬gQ D x (1+k):=by classical intro g;have i:=wo H S G x;let C:=(p53:tF (Fin k)).filter (λ t:Fin k=>kA D O t.1 x);have:C.card<=k:=by{simpa using card_le_univ C};unfold gQ at g;unfold gR at a;change _<=2+C.card at i;omega
lemma De(x:V)(d:Nat)(A:tF (Fin k))(j:A.card=k-d)(c:gR D x)(a:gQ D x (1+d)):∃t∈A,kA D O t.1 x:=by classical have r:=wo H S G x;exact sC j (by{unfold gQ at a;unfold gR at c;change _<=2+_ at r;omega})
lemma CF(p:kM I=kH 10 D){x c:V}(m:x≠c)(q:I.testBit x.1=p55){j l:Nat}(d:j<l)(a:gQ D x l)(g:yB D x c):uj D W x j c\/uj D W x l c\/∃t:Fin k,kA D O t.1 x/\¬kA D O t.1 c:=by by_contra P;push Not at P;obtain⟨J,A,K⟩:=P;have y:x∈fX 10 D:=by_contra λ Q=>by{have U:=sE.2 Q;rw[<-p,kM,mF] at U;simp[q] at U};obtain⟨w,hw⟩:=g;obtain⟨e0,X⟩:=bb G0 H S F G.1 m y (λ u hu Y=>by{obtain⟨t,ht⟩:=G.2.1 u hu;obtain⟨_,L⟩:=K t ⟨t.2,by simpa[ht] using Y⟩;simpa[ht] using L}) hw;have v:=lt_trans d a;have z:W x j≠W x l:=λ h1=>Nat.ne_of_lt d (L7 G x j l v a h1);by_cases R:W x j=e0;exact A ⟨a,X (W x l) (L6 G x l) (λ h2=>z (R.trans h2.symm))⟩;exact J ⟨v,X (W x j) (L6 G x j) R⟩
lemma Dh(x:V)(A:Nat)(d:AA (kM A))(i:∃a∈kM A,qW x a):∃j<qX k I x,gQ D x j/\∀c∈kM A,¬uj D W x j c:=by obtain⟨g,s,hlt,_,v,y,u⟩:=vc G0 H.1 S (kM A) d x i;obtain⟨j,p,r⟩:=L8 G x (g,s) (sM.2 ⟨hlt,v,y⟩);exact⟨j,lL p (L5 G x),p,λ c S q=>p36.1 u (r▸q.2) S⟩
end
omit [GIdx gi] in lemma xb(S:tF V)(m:Nat)(a:∀v∈S,v.1<m):∑ v∈S,2^v.1<2^m:=by induction m generalizing S with|zero=>{simp[fE.2 λ v g=>hJ _ (a v g)]}|succ m ih=>{rw[<-fS S (λ v:V=>v.1<m)];have:=ih (S.filter (λ v=>v.1<m)) (λ v g=>(mF.1 g).2);have:∑ v∈S.filter (λ v=>¬v.1<m),2^v.1<=2^m:=by{by_cases j:(S.filter (λ v=>¬v.1<m)).Nonempty;{obtain⟨p,d⟩:=j;have c:p.1=m:=by{have:=a p (mF.1 d).1;have:=(mF.1 d).2;omega};have i:S.filter (λ v=>¬v.1<m)={p}:=by{ext v;simp only[mS];exact⟨λ g=>Fin.ext (by{have:=a v (mF.1 g).1;have:=(mF.1 g).2;omega}),λ h=>h▸d⟩};rw[i,Finset.sum_singleton,c]};{rw[fN.1 j];simp}};rw[Nat.pow_succ];omega}
lemma Cb(g:G1 D k I W E F O){t:Nat}(c:t+1<k)(x:V)(a:∀y:V,x.1<y.1->(kA D O t y↔kA D O (t+1) y))(d:kA D O t x):kA D O (t+1) x:=by classical by_contra K;let C (s:Nat):=univ.filter (λ v:V=>kA D O s v);have i:∀(s:Nat)(r:s<k),zl D (O ⟨s,r⟩)=∑ v∈C s,2^v.1:=λ s r=>by{cases X:O ⟨s,r⟩ with|none=>{have:C s=∅:=by{ext v;simp[C,kA,X]};simp[zl,this]}|some u=>{have:C s=fM 10 D u.1:=by{ext v;simp[C,kA,r,X]};simp[zl,yk,this]}};let A:=univ.filter (λ v:V=>kA D O t v);let B:=univ.filter (λ v:V=>kA D O (t+1) v);have p:∑ v∈A,2^v.1<=∑ v∈B,2^v.1:=by{rw[<-i t (by omega),<-i (t+1) c];exact g.2.2.2.2.1 ⟨t,by omega⟩ ⟨t+1,c⟩ (by simp)};rw[<-fS A (λ v=>x.1<v.1),<-fS B (λ v=>x.1<v.1)] at p;have m:A.filter (λ v=>x.1<v.1)=B.filter (λ v=>x.1<v.1):=by{ext v;simp only[A,B,mF,mU,true_and];exact⟨λ⟨Q,q⟩=>⟨(a v q).1 Q,q⟩,λ⟨Q,q⟩=>⟨(a v q).2 Q,q⟩⟩};rw[m] at p;have P:2^x.1<=∑ v∈A.filter (λ v=>¬x.1<v.1),2^v.1:=hE (f:=λ v:V=>2^v.1) (λ _ _=>nZ _) (mF.2 ⟨mF.2 ⟨mU _,d⟩,Nat.lt_irrefl _⟩);have L:=xb (B.filter (λ v=>¬x.1<v.1)) x.1 (λ v U=>by{have:=mF.1 U;have:=(mF.1 this.1).2;have:v.1≠x.1:=λ h=>K (Fin.ext h▸this);omega});omega
def b8(D:qD)(x:V)(a b:Nat):Prop:=q5 10 D a b/\x∈fM 10 D a/\x∈fM 10 D b
section
variable (Q:q0 10 D){x:V}(M:w5 10 D (q2 10 D {x})=∅){a b c:Nat}
include Q x M a b c
omit [GIdx gi] in lemma vy(d:b8 D x a c)(g:b8 D x b c):a=b:=by have l:=d.1.2.1;have j:c-10<(tD D):=by{have:=d.1.1;omega};have m:=j6 Q M j (by simpa[Nat.add_sub_of_le l] using d.2.2);rcases d.1.2.2 with u|r<;>rcases g.1.2.2 with q|p;{exact u.symm.trans q};{exact (m.2 ⟨u.symm▸d.2.1,p.symm▸g.2.1⟩).elim};{exact (m.2 ⟨q.symm▸g.2.1,r.symm▸d.2.1⟩).elim};{exact r.symm.trans p}
omit [GIdx gi] in lemma kb(h:RT (b8 D x) a c)(g:RT (b8 D x) b c):RT (b8 D x) a b\/RT (b8 D x) b a:=by induction h with|refl=>{exact .inr g}|@tail u c q l ih=>{rcases rK g with rfl|⟨d,r,p⟩;{exact .inl (rT q l)};{have m:u=d:=vy Q M l p;subst m;exact ih r}}
end
lemma jg(h:SL D)(a:SC D){x:V}(c:w5 10 D (q2 10 D {x})=∅):∀(d:Nat) (g:Nat) (s:Bool),g<(tD D)->(tD D)-g<=d->x∈fM 10 D (fC D (g,s))->∃e∈fD 10 D x,fM 10 D (fC D (g,s))⊆fM 10 D (fC D e)/\(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e))):=by intro d;induction d with|zero=>{intro _ _ _ _ _;omega}|succ d ih=>{intro g s K P X;by_cases i:x∈fM 10 D (10+g);{have L:=j6 h.1 c K i;have u:fM 10 D (fC D (g,s))⊆fM 10 D (10+g):=by{rw[yj h.1 K L.1];cases s<;>simp[fC]};have m:10+g+1<10+(tD D):=by{have:10+g≠qb 10 D:=λ R=>wd G0 x ((a (q9 x)).1 (w3.1 (R▸i)));unfold qb at this;omega};obtain⟨H,z⟩:=fz.1 (nT nO (h.2.1 (10+g) m));simp only[qg,mF,mR] at z;obtain⟨J,p⟩:=sX z.2;have M:g<H:=by{have:=h.1 H z.1;cases J<;>simp[fC] at p<;>omega};obtain⟨e,U,q,r⟩:=ih H J z.1 (by omega) (p▸i);refine⟨e,U,u.trans (p▸q),.inr ⟨i,?_⟩⟩;rcases r with rfl|⟨y,j⟩;rw[p];exact .head ⟨⟨by omega,by omega,by simpa using z.2⟩,i,y⟩ j};{exact⟨(g,s),sM.2 ⟨K,X,i⟩,Finset.Subset.refl _,.inl rfl⟩}}
lemma uA(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:kA D O t x)(hM:w5 10 D (q2 10 D {x})=∅):∃u:U0,∃ht:t<k,O ⟨t,ht⟩=some u/\∃j1 j2:Nat,j1<fF D x/\j2<fF D x/\j1≠j2/\vW D W O t x j1/\vW D W O t x j2/\RT (b8 D x) u.1 (fC D (W x j1))/\RT (b8 D x) u.1 (fC D (W x j2)):=by obtain⟨ht,v⟩:=c;cases p:O ⟨t,ht⟩ with|none=>{rw[p] at v;exact v.elim}|some u=>{rw[p] at v;have X:=d.2.2.1 ⟨t,ht⟩ u p;have fc:2<=kS D u.1:=by{have:=mR.1 (p44.1 (mF.1 (mD.1 X).1).1).2;omega};obtain⟨g1,L,g2,K,R⟩:=(p46 (s:=qg D u.1)).1 (by{unfold kS at fc;omega});simp only[qg,mF,mR] at L K;obtain⟨s1,J⟩:=sX L.2;obtain⟨s2,H⟩:=sX K.2;obtain⟨e1,hi,h3,f7⟩:=jg h l hM (tD D) g1 s1 L.1 (by omega) (J▸v);obtain⟨e2,hg,h0,f6⟩:=jg h l hM (tD D) g2 s2 K.1 (by omega) (H▸v);have h5:e1≠e2:=λ hf=>by{subst hf;rcases f7 with rfl|⟨_,g⟩<;>rcases f6 with hh|⟨_,h2⟩;{exact R (congrArg p65 hh)};{have:=qk h.1 (λ _ _ h=>h.1) h2;rw[J] at this;have:=w7 h.1 K.1 s2;omega};{subst hh;have:=qk h.1 (λ _ _ h=>h.1) g;rw[H] at this;have:=w7 h.1 L.1 s1;omega};{have hu:∀z U Z Y,z<(tD D)->U<(tD D)->z≠U->fC D (z,Z)=u.1->fC D (U,Y)=u.1->RT (b8 D x) (10+z) (10+U)->False:=λ z U Z Y fb fa f8 f5 Q h4=>by{rcases rK h4 with hf|⟨w,hw,q⟩;exact f8 (by omega);have:=qk h.1 (λ _ _ h=>h.1) hw;have:=w7 h.1 fb Z;have M:=j6 h.1 hM fa q.2.2;have m:=q.1.2.2;rw[nA] at m;cases Y<;>simp[fC] at Q<;>rcases m with hA|hB;{omega};{exact M.2 ⟨Q.symm▸v,hB.symm▸q.2.1⟩};{exact M.2 ⟨hA.symm▸q.2.1,Q.symm▸v⟩};{omega}};rcases kb h.1 hM g h2 with fe|fd;exact hu g1 g2 s1 s2 L.1 K.1 R J H fe;exact hu g2 g1 s2 s1 K.1 L.1 R.symm H J fd}};obtain⟨j1,he,h9⟩:=L8 d x e1 hi;obtain⟨j2,hd,h8⟩:=L8 d x e2 hg;have r:∀j e,j<fF D x->W x j=e->fM 10 D u.1⊆fM 10 D (fC D e)->vW D W O t x j:=λ j e hj hwe ha=>⟨hj,λ y ⟨_,h7⟩=>⟨hj,hwe▸ha (by{rw[p] at h7;exact h7})⟩⟩;have mkRT:∀g s e,g<(tD D)->(yx D g=u.1\/yf D g=u.1)->fC D (g,s)=u.1->(e=(g,s)\/(x∈fM 10 D (10+g)/\RT (b8 D x) (10+g) (fC D e)))->RT (b8 D x) u.1 (fC D e):=λ g s e hg hq hf hc=>by{rcases hc with rfl|⟨hx,hrt⟩;{rw[hf]};{exact .head ⟨⟨by omega,by omega,by simpa using hq⟩,v,hx⟩ hrt}};exact⟨u,ht,p,j1,j2,he,hd,λ hje=>h5 (h9.symm.trans (hje▸h8)),r j1 e1 he h9 (J▸h3),r j2 e2 hd h8 (H▸h0),h9▸mkRT g1 s1 e1 L.1 L.2 J f7,h8▸mkRT g2 s2 e2 K.1 K.2 H f6⟩}
lemma CE(h:SL D)(l:SC D)(d:G1 D k I W E F O){t:Nat}{x:V}(c:kA D O t x)(i:¬gR D x)(a:Nat):∃j<qX k I x,j≠a/\vW D W O t x j:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});obtain⟨_,_,_,j1,j2,he,hd,hne,r1,r2,_,_⟩:=uA h l d c hM;by_cases g:j1=a;{exact⟨j2,lL hd (L5 d x),λ hm=>hne (g.trans hm.symm),r2⟩};{exact⟨j1,lL he (L5 d x),g,r1⟩}
lemma CL(h:SL D)(l:SC D)(d:G1 D k I W E F O){t1 t2:Nat}{x y1 y2:V}{j:Nat}(c1:kA D O t1 x)(c2:kA D O t2 x)(hy1:kA D O t1 y1)(hn2:¬kA D O t2 y1)(hy2:kA D O t2 y2)(hn1:¬kA D O t1 y2)(i:¬gR D x)(hj:gQ D x j)(hr1:¬vW D W O t1 x j)(hr2:¬vW D W O t2 x j):5<=fF D x:=by have hM:w5 10 D (q2 10 D {x})=∅:=g8.1 (by{unfold gR at i;omega});have hsub:∀{a b},RT (b8 D x) a b->fM 10 D a⊆fM 10 D b:=λ r=>by{induction r with|refl=>{exact Finset.Subset.refl _}|@tail u v _ s ih=>{have l0:=s.1.2.1;have j0:v-10<(tD D):=by{have:=s.1.1;omega};have m:=j6 h.1 hM j0 (by simpa[Nat.add_sub_of_le l0] using s.2.2);have hv:fM 10 D v=fM 10 D (yx D (v-10))∪fM 10 D (yf D (v-10)):=(by simpa[Nat.add_sub_of_le l0] using yj h.1 j0 m.1);refine ih.trans ?_;rw[hv];rcases s.1.2.2 with hu|hu;{rw[hu];exact Finset.subset_union_left};{rw[hu];exact Finset.subset_union_right}}};obtain⟨u1,ht1,p1,a1,a2,ha1,ha2,ha12,ra1,ra2,ta1,ta2⟩:=uA h l d c1 hM;obtain⟨u2,ht2,p2,b1,b2,hb1,hb2,hb12,rb1,rb2,tb1,tb2⟩:=uA h l d c2 hM;have h12:∀a b,RT (b8 D x) u1.1 (fC D (W x a))->RT (b8 D x) u2.1 (fC D (W x b))->a≠b:=λ a b ta tb hab=>by{subst hab;rcases kb h.1 hM ta tb with h1|h2;{obtain⟨_,hy1m⟩:=hy1;rw[p1] at hy1m;exact hn2 ⟨ht2,by rw[p2];exact hsub h1 hy1m⟩};{obtain⟨_,hy2m⟩:=hy2;rw[p2] at hy2m;exact hn1 ⟨ht1,by rw[p1];exact hsub h2 hy2m⟩}};have:=h12 a1 b1 ta1 tb1;have:=h12 a1 b2 ta1 tb2;have:=h12 a2 b1 ta2 tb1;have:=h12 a2 b2 ta2 tb2;have:j≠a1:=λ e=>hr1 (e▸ra1);have:j≠a2:=λ e=>hr1 (e▸ra2);have:j≠b1:=λ e=>hr2 (e▸rb1);have:j≠b2:=λ e=>hr2 (e▸rb2);have:j<fF D x:=hj;omega
lemma B8(a:q0 10 D)(c:G1 D k I W E F O)(x:V)(j:Nat):¬qA D W x j x:=by rintro⟨_,d⟩;have h:=L6 c x j;have ⟨hlt,hx1,hxn⟩:=sM.1 h;have i:=sA a h;apply hxn;rw[qm a hlt i,mI];rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at hx1 d;cases s<;>simp[fC,qZ] at hx1 d ⊢;{exact⟨hx1,d⟩};{exact⟨d,hx1⟩}
section
variable (Q:q0 10 D)(G:G1 D k I W E F O){x y:V}{j:Nat}
include Q G x y j
lemma Cc(c:uj D W x j y)(a:qA D W x j y):gR D y:=by rcases c with ⟨_,c⟩;rcases a with ⟨_,a⟩;have m:=L6 G x j;have i:=(sM.1 m).1;have l:y∈fM 10 D (yx D (W x j).1)/\y∈fM 10 D (yf D (W x j).1):=by{rcases hwe:W x j with ⟨g,s⟩;rw[hwe] at c a;cases s<;>simp[fC,qZ] at c a ⊢;exact⟨c,a⟩;exact⟨a,c⟩};exact fz.2 ⟨_,mF.2 ⟨mR.2 i,q8.2 (by{rw[qm Q i (sA Q m),mI];exact l}),q8.2 l.1,q8.2 l.2⟩⟩
lemma CC(c:uj D W x j y)(a:¬qA D W x j y):∃l<qX k I y,gQ D y l/\W y l=W x j:=by rcases c with ⟨i,c⟩;have p:=L6 G x j;have q:=(sM.1 p).1;obtain⟨l,h,m⟩:=L8 G y (W x j) (sM.2 ⟨q,c,λ r=>a ⟨i,sU Q q (sA Q p) (!(W x j).2) r⟩⟩);exact⟨l,lL h (L5 G y),h,m⟩
lemma CT(a:qA D W x j y)(c:¬uj D W x j y):∃l<qX k I y,gQ D y l/\W y l=qZ (W x j):=by rcases a with ⟨i,a⟩;have q:=L6 G x j;have m:=(sM.1 q).1;obtain⟨l,h,p⟩:=L8 G y (qZ (W x j)) (sM.2 ⟨m,a,λ u=>c ⟨i,sU Q m (sA Q q) (W x j).2 u⟩⟩);exact⟨l,lL h (L5 G y),h,p⟩
end
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O)(M:kM I=kH 10 D)
include H S G M
lemma A4{y:V}(d:I.testBit y.1=p63):fD 10 D y={W y 0}/\∀a,qW y a->a∈fM 10 D (fC D (qZ (W y 0))):=by have p:y∈kH 10 D:=M▸mF.2 ⟨mU _,d⟩;obtain⟨e,_,_,_,_,m,j,_⟩:=qe G0 H S p;change fD 10 D y={e} at j;have l:=mS.1 (j▸L6 G y 0);rw[l];exact⟨j,m⟩
lemma Cf{x y:V}(d:x≠y)(g:I.testBit y.1=p63){j:Nat}(a:qA D W x j y):qZ (W x j)=W y 0:=by have r:=L6 G x j;have m:=(sM.1 r).1;have q:qZ (W x j)∈fD 10 D y:=sM.2 ⟨m,a.2,λ z=>d (mS.1 (sP G0 H.1 S (M▸mF.2 ⟨mU _,g⟩) (sU H.1 m (sA H.1 r) (W x j).2 z)▸(sM.1 r).2.1))⟩;rwa[(A4 H S G M g).1,mS] at q
lemma C7{x y:V}(g:x≠y)(l:I.testBit y.1=p63){j:Nat}(c:qA D W x j y):¬gT D W E x j:=by intro r;obtain⟨a,z,_⟩:=G0.2.2.2 y y;set p:=fW y a;have u:kF p.2 (E p.1)∈fD 10 D y:=by{simpa[p,(wt y a z).1] using (L9 G p.2 p.1).1};rw[(A4 H S G M l).1,mS] at u;exact r.2 p.1 (!p.2) (by rw[AS,u,<-Cf H S G M g l c,Bk])
lemma C8{i j:V}(g:I.testBit i.1=p63)(l:I.testBit j.1=p63)(_hne:i≠j):¬qA D W i 0 j:=by rintro⟨_,r⟩;have y:i∈kH 10 D:=M▸mF.2 ⟨mU _,g⟩;have u:j∈kH 10 D:=M▸mF.2 ⟨mU _,l⟩;obtain⟨a,v,_⟩:=G0.2.2.2 i i;have p:=(A4 H S G M g).2 a v;rw[sP G0 H.1 S u r,mS] at p;subst a;exact (j5 G0 H S v).elim (sE.1 y) (sE.1 u)
end
lemma Db(h:SL D)(m:SC D)(H:vD 10 D=0)(r:G1 D k I W E F O)(J:kM I=kH 10 D){i y d:V}(K:I.testBit i.1=p63)(j:¬qW i y)(p:qW i d)(q:qA D W i 0 y):∃l<qX k I d,AN D W E (fW i d).1 d l/\gT D W E d l/\¬uj D W d l y/\∀x2:V,qW i x2->uj D W d l x2/\¬qA D W d l x2:=by have fj:i∈kH 10 D:=J▸mF.2 ⟨mU _,K⟩;have hx:=zv G0 h m H fj;obtain⟨L,hq,fb,he,hg,_,h6,_⟩:=qe G0 h m fj;have g3:W i 0=L:=by{simpa[fD,h6] using (L6 r) i 0};have U:(E (fW i d).1).1=L.1:=by{have hW:=(L9 r (fW i d).2 (fW i d).1).1;rw[(wt i d p).1] at hW;simp only[fD,h6,mS] at hW;simpa[kF] using congrArg p65 hW};have M:∀w,fO D (λ _:V=>p55) w=p55:=λ w=>if z:w<10+(tD D) then jy h.1 _ (λ _=>p55) (λ _ _=>rfl) (λ j _=>by cases gZ D j<;>rfl) w z else z0 D _ w (by omega);have Y:RT (q5 10 D) i.1 (10+L.1):=(yu (λ _ _ h=>h.1) (wn h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (fC D L) (by{rw[w3.1 (he▸m0 i),M];decide}))).tail (qs hq L.2);have h7:q7 10 D (10+L.1) (qb 10 D):=by{rcases j8 h.1 hx Y with g9|⟨fy,_⟩;{have:=qk h.1 (λ _ _ h=>h) g9;have:=lP h.2.2;rw[show 10+L.1=qb 10 D by{unfold qb at *;omega}];exact .refl};{exact fy}};have hf:fO D (q1 i y) (10+L.1)=p63:=by{rw[qd h.1 _ hq L.2,fb,wV,q3 h.1 (he▸m0 i) (by simp[q1]),q3 h.1 (by simpa[g3,qZ] using q.2) (by simp[q1])];rfl};have f4:fO D (q1 i y) (qb 10 D)=p55:=by{cases hv:fO D (q1 i y) (qb 10 D);rfl;exfalso;obtain⟨a,b,fc,ha,hb⟩:=(m _).1 hv;simp only[q1,bO,dT] at ha hb;rcases ha with rfl|rfl<;>rcases hb with rfl|rfl;{exact G0.2.1 _ fc};{exact j fc};{exact j (G0.1 _ _ fc)};{exact G0.2.1 _ fc}};have fk:∀{a b},q7 10 D a b->fO D (q1 i y) a=p63->fO D (q1 i y) b=p55->∃u v,q7 10 D a u/\q5 10 D u v/\kS D u=1/\fO D (q1 i y) u=p63/\fO D (q1 i y) v=p55:=by{intro a b gc;induction gc using rI with|refl=>{intro h1 h2;rw[h1] at h2;cases h2}|@head a c f7 _ ih=>{intro ha hb;cases hs:fO D (q1 i y) c;{exact⟨a,c,.refl,f7.1,f7.2,ha,hs⟩};{obtain⟨u,v,ga,B⟩:=ih hs hb;exact⟨u,v,.head f7 ga,B⟩}}};obtain⟨u,v,h5,ff,fa,fr,h9⟩:=fk h7 hf f4;obtain⟨g,s,P,rfl,rfl⟩:=y3.1 ff;have h4:gZ D g=p63/\fO D (q1 i y) (fC D (g,!s))=p55:=by{rw[qd h.1 _ P s,fr] at h9;cases fs:gZ D g;simp[fs] at h9;exact⟨rfl,by simpa[fs,wV] using h9⟩};have f9:L.1<g:=by{have:=qk h.1 (λ _ _ h=>h.1) h5;have:=w7 h.1 P s;omega};have Z:q7 10 D i.1 (10+L.1):=by{rcases j9 Y with ge|⟨b,gd,fx⟩;exact ge;exact absurd (ze G0 h.1 m fj gd fx▸y7 h.1 H fx) gk};have Q:q7 10 D i.1 (fC D (g,s)):=Z.trans h5;have hy:=Q.tail ⟨qs P s,fa⟩;have X:fM 10 D (fC D (g,s))=∅:=by{have hn:=kh h.1 (q9 i) (λ _=>p55) i (λ _ hk=>by simp[q9,hk]) (10+L.1) (fC D (g,s)) (vn h.1 Z (qk h.1 (λ _ _ h=>h.1) h5)) (by{rw[M];exact p54.2 (λ ht=>nE i (hg▸w3.2 ht))});rw[M] at hn;exact fE.2 λ z hz=>p58 ((w3.1 hz).symm.trans ((mS.1 (yw G0 h.1 m i _ (wp h.1 Q) hz))▸hn))};have f1:∀x2,qW i x2->x2∈fM 10 D (fC D (g,!s))/\x2∉fM 10 D (10+g):=λ x2 fd=>by{have hp:fO D (q1 i x2) (10+g)≠fO D (q9 x2) (10+g):=λ fl=>by{have fu:=k6 h.1 (q1 i x2) (q9 x2) i (λ _ hk=>by simp[q1,q9,hk]) (10+g) (wp h.1 hy) fl;rw[(m _).2 (yv fd),p54.2 (λ ht=>wd G0 x2 ((m _).1 ht))] at fu;cases fu};have fh:=x9 h.1 (q9 x2) (q1 i x2) (kg (by simp[q1])) (10+g);have ⟨R,hh⟩:fO D (q1 i x2) (10+g)=p63/\fO D (q9 x2) (10+g)=p55:=by{cases f6:fO D (q1 i x2) (10+g)<;>cases f5:fO D (q9 x2) (10+g)<;>first|exact⟨rfl,rfl⟩|exact absurd (f6.trans f5.symm) hp|exact absurd (fh f5) (by{rw[f6];decide})};rw[qd h.1 _ P s,h4.1,wV,bA] at R;have fn:=vd h.1 i P (!s) (by simpa[p60] using Q) (by simpa[p60] using fa) (q1 i x2) (q9 x2) (λ _ hk=>by simp[q1,q9,hk]);exact⟨w3.2 (fn▸R.2),λ hm=>p58 ((w3.1 hm).symm.trans hh)⟩};obtain⟨l,h3,hl⟩:=L8 r d (g,!s) (sM.2 ⟨P,(f1 d p).1,(f1 d p).2⟩);have hd:gU D W d l:=⟨h3,by{rw[hl,sK];exact X}⟩;exact⟨l,lL h3 (L5 r d),⟨⟨h3,by{rw[U,hl];exact f9}⟩,hd⟩,ka (L9 r) hd,λ⟨_,hj⟩=>p58 ((q3 h.1 (hl▸hj) (x:=q1 i y) (by simp[q1])).symm.trans h4.2),λ x2 fd=>⟨⟨h3,hl▸(f1 x2 fd).1⟩,λ⟨_,ho⟩=>nE x2 (by{rw[hl,sK,X] at ho;exact ho})⟩⟩
end
def es(D:qD)(a:EI->qO)(s:Bool)(e:EI)(x:V):Prop:=x∈fM 10 D (fC D (kF s (a e)))
def yY(a:EI->qO)(d c:EI):Prop:=(a d).1<(a c).1
def uc(a:EI->qO)(d c:EI):Prop:=(a d).1=(a c).1
def jh(D:qD)(u v:V)(g:Nat):Prop:=g<(tD D)/\gZ D g=p63/\∃s:Bool,u∈fM 10 D (fC D (g,s))/\v∉fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s))/\u∉fM 10 D (fC D (g,!s))
def fZ(D:qD)(a:EI->qO)(e:EI):Prop:=∃g,g≠(a e).1/\jh D (kT e) (kU e) g
abbrev Cg:=fZ
def Ad(D:qD)(a:V->Nat->qO)(c:EI->qO)(e:EI)(d g:Nat):Prop:=gQ D (kT e) d/\gQ D (kU e) g/\(a (kT e) d).1≠(c e).1/\a (kU e) g=qZ (a (kT e) d)
def wy(D:qD)(x:V->Bool)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fO D x a=p63/\fO D x b=p63) d c
def zm(D:qD)(d c:Nat):Prop:=RT (λ a b=>q5 10 D a b/\fM 10 D a=∅/\kS D a=1) d c
def xv(D:qD)(b:Nat):Prop:=fM 10 D b=∅/\2<=kS D b
def gS(D:qD)(a:Nat):Prop:=zm D a (qb 10 D)/\fM 10 D (qb 10 D)=∅
abbrev BZ:=gS
def yI(D:qD)(a:Nat):Prop:=vD 10 D=1/\∃b0,zm D a b0/\xv D b0
def gX(D:qD)(a:Nat)(z:V):Prop:=∃r,zm D a r/\z∈fM 10 D r/\∀t∈fM 10 D r,z<=t
abbrev B4:=gX
def xE(D:qD)(a:V->Nat->qO)(c:EI->qO)(d:EI)(z:V)(l:Nat):Prop:=vQ D a c d z l/\(qA D a z l (kT d)\/qA D a z l (kU d))
def kc(D:qD)(c:EI->qO)(d:EI)(a b:V)(h:Nat):Prop:=h<(tD D)/\wy D (q1 (kT d) (kU d)) (10+(c d).1) (10+h)/\fO D (q1 a b) (10+h)=p55
noncomputable def wi(D:qD)(c:EI->qO)(d:EI)(a b:V):Nat:=open Classical in if hex:∃h,kc D c d a b h then p22 hex else 0
def bc(D:qD)(c:EI->qO)(d:EI)(a b:V)(g:EI):Prop:=fZ D c d\/(fO D (q1 a b) (10+(c d).1)=p63/\wy D (q1 (kT d) (kU d)) (10+(c d).1) (10+(c g).1)/\wy D (q1 (kT d) (kU d)) (10+(c g).1) (10+wi D c d a b)/\(c g).1<wi D c d a b)
def wC(D:qD)(c:V->Nat->qO)(d:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(l:Nat):Prop:=vQ D c d i g l/\¬qA D c g l a/\¬qA D c g l b/\(qA D c g l (kT h)\/qA D c g l (kU h))
def wB(D:qD)(c:EI->qO)(h:EI)(a b:V)(i:EI)(g:V)(d:EI):Prop:=yY c i d/\(es D c p55 d g\/es D c p63 d g)/\bc D c h a b d
def uE(D:qD)(w:V->Nat->qO)(e:EI->qO)(d:EI)(am:Nat)(z:V)(l:Nat):Prop:=(qA D w z l (kT d)\/qA D w z l (kU d))/\∃e':EI,!am.testBit e'.1/\∃s:Bool,ra D w e s e' z l
section
open Finset (min'_mem min'_le)
variable {D:qD} {k I:Nat} {W:V->Nat->qO} {E:EI->qO} {F:V->Nat} {O:Fin k->Option U0}
abbrev AR:=wy
abbrev EC:=zm
abbrev s2:=@q1 10
omit [GIdx gi] in lemma sF(h:q0 10 D){u a b:V}{w:Nat}(m:u∈fM 10 D w)(e:u=a\/u=b)(v:fO D (s2 a b) w=p55):False:=by cases (q3 h m (x:=s2 a b) (by rcases e with rfl|rfl<;>simp[q1])).symm.trans v
omit [GIdx gi] in lemma ji(a:q0 10 D){u v:V}{g:Nat}(c:jh D u v g):∃s:Bool,(g,s)∈fD 10 D u/\(g,!s)∈fD 10 D v/\u∈fM 10 D (fC D (g,s))/\v∈fM 10 D (fC D (g,!s)):=by obtain⟨d,p,s,m,i,l,j⟩:=c;exact⟨s,sM.2 ⟨d,m,λ h=>j (sU a d p (!s) h)⟩,sM.2 ⟨d,l,λ h=>i (sU a d p s h)⟩,m,l⟩
lemma CV{e:EI}{a c:Nat}(d:Ad D W E e a c):¬ra D W E p55 e (kT e) a:=λ g=>d.2.2.1 (by rw[g.2,zN])
lemma CU{e:EI}{c a:Nat}(d:Ad D W E e c a):¬ra D W E p63 e (kU e) a:=λ g=>by have i:(W (kU e) a).1=(W (kT e) c).1:=by{rw[d.2.2.2];rfl};have h:(W (kU e) a).1=(E e).1:=by{rw[g.2,Ac];rfl};exact d.2.2.1 (i.symm.trans h)
lemma BY{e:EI}{c a:Nat}(d:Ad D W E e c a)(y:V):(uj D W (kU e) a y↔qA D W (kT e) c y)/\(uj D W (kT e) c y↔qA D W (kU e) a y):=by have _:=d.1;have _:=d.2.1;constructor<;>(simp only[uj,qA,d.2.2.2,Bk];tauto)
section
variable (Q:q0 10 D)
include Q
lemma Dd(a:G1 D k I W E F O){e:EI}(c:fZ D E e):∃ju<qX k I (kT e),∃jv<qX k I (kU e),Ad D W E e ju jv:=by obtain⟨g,m,r⟩:=c;obtain⟨s,l,j,_,_⟩:=ji Q r;obtain⟨ju,i,p⟩:=L8 a (kT e) (g,s) l;obtain⟨jv,h,q⟩:=L8 a (kU e) (g,!s) j;exact⟨ju,lL i (L5 a _),jv,lL h (L5 a _),i,h,by rw[p];exact m,by rw[p,q];rfl⟩
lemma fG(a:gP D E)(e:EI):jh D (kT e) (kU e) (E e).1:=by have d:=a p55 e;have h:=a p63 e;rw[zN] at d;rw[Ac] at h;obtain⟨g,j,_⟩:=sM.1 d.1;obtain⟨_,i,_⟩:=sM.1 h.1;exact⟨g,sA Q d.1,(E e).2,by simpa[wX,x4] using j,by simpa[wX,x4] using d.2,by simpa[wX,x4,qZ] using i,by simpa[wX,x4,qZ] using h.2⟩
omit [GIdx gi] in lemma qp{x:V->Bool}{a b:Nat}(h:AR D x a b):a<=b:=qk Q (λ _ _ d=>d.1) h
omit [GIdx gi] in lemma vq(u v:V):∀w:Nat,fO D (s2 u v) w=p63->u∉fM 10 D w->v∉fM 10 D w->∃g,jh D u v g/\AR D (s2 u v) (10+g) w:=by intro w;induction w using sI with|ind w ih=>{intro q l i;by_cases A:w<10;{rw[qa D _ w A] at q;simp only[q1,bO,dT] at q;rcases q with L|L;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) l;exact absurd (w3.2 (by{rw[qa D _ w A,q9,L];simp})) i};by_cases m:w-10<(tD D);{set j:=w-10;let X:=yx D j;let Y:=yf D j;have c:w=10+j:=by{omega};have:=Q j m;have y:=c▸qs m p55;have r:=c▸qs m p63;have p:=q;rw[c,qu Q _ j m] at q;cases P:gZ D j;{rw[P,A5,bO] at q;rw[c,yj Q m P,mN,not_or] at l i;rcases q with z|d;obtain⟨g,K,J⟩:=ih (X) (by omega) z l.1 i.1;exact⟨g,K,J.tail ⟨y,z,p⟩⟩;obtain⟨g,K,J⟩:=ih (Y) (by omega) d l.2 i.2;exact⟨g,K,J.tail ⟨r,d,p⟩⟩};{rw[P,wV,bA] at q;by_cases U:u∉fM 10 D (X)/\v∉fM 10 D (X);{obtain⟨g,K,J⟩:=ih (X) (by omega) q.1 U.1 U.2;exact⟨g,K,J.tail ⟨y,q.1,p⟩⟩};by_cases R:u∉fM 10 D (Y)/\v∉fM 10 D (Y);{obtain⟨g,K,J⟩:=ih (Y) (by omega) q.2 R.1 R.2;exact⟨g,K,J.tail ⟨r,q.2,p⟩⟩};rw[c,qm Q m P,mI] at l i;have ha':u∈fM 10 D (X)\/v∈fM 10 D (X):=by{tauto};have hb':u∈fM 10 D (Y)\/v∈fM 10 D (Y):=by{tauto};refine⟨j,⟨m,P,?_⟩,c▸.refl⟩;rcases ha' with M|z;{have H:=λ h=>l ⟨M,h⟩;have d:=hb'.resolve_left H;exact⟨p55,M,λ h=>i ⟨h,d⟩,d,H⟩};{have d:=λ h=>i ⟨z,h⟩;have H:=hb'.resolve_right d;exact⟨p63,H,d,z,λ h=>l ⟨h,H⟩⟩}}};{rw[z0 D _ w (by omega)] at q;cases q}}
lemma y8{e:EI}(a:¬fZ D E e){w:Nat}(h:fO D (s2 (kT e) (kU e)) w=p63)(d:kT e∉fM 10 D w)(c:kU e∉fM 10 D w):AR D (s2 (kT e) (kU e)) (10+(E e).1) w:=by obtain⟨g,m,l⟩:=vq Q (kT e) (kU e) w h d c;have:g=(E e).1:=by{by_contra j;exact a ⟨g,j,m⟩};rwa [this] at l
lemma jt(c:SC D){e:EI}(a:¬fZ D E e):AR D (s2 (kT e) (kU e)) (10+(E e).1) (qb 10 D):=by have g:=qn G0 c;exact y8 Q a ((c _).2 (yv (xk e))) (by rw[g];exact nE _) (by rw[g];exact nE _)
omit [GIdx gi] in lemma y6{x:V->Bool}{z:V}{a b:Nat}(h:AR D x a b)(c:z∈fM 10 D a)(d:z∉fM 10 D b):∃g s,g<(tD D)/\10+g<=b/\fO D x (10+g)=p63/\AR D x a (fC D (g,s))/\z∈fM 10 D (fC D (g,s))/\z∉fM 10 D (10+g)/\AR D x (10+g) b:=by induction h using rI with|refl=>{exact absurd c d}|@head u v l p ih=>{by_cases m:z∈fM 10 D v;{obtain⟨g,s,P,M,L,K,J,H,y⟩:=ih m;exact⟨g,s,P,M,L,rH l K,J,H,y⟩};{obtain⟨g,s,r,rfl,rfl⟩:=y3.1 l.1;exact⟨g,s,r,qp Q p,l.2.2,rR,c,m,p⟩}}
omit [GIdx gi] in lemma w8{a b:Nat}(c:EC D a b):a<=b:=qk Q (λ _ _ h=>h.1) c
end
section
variable {R:Nat->Nat->Prop}(Q:q0 10 D)(Y:∀x y,R x y->q5 10 D x y){a c q:Nat}(M:EC D a c)(N:RT R a q)
include R Q Y a c q M N
omit [GIdx gi] in lemma y9:RT R c q\/(EC D a q/\EC D q c/\q≠c):=by induction M using rI with|refl=>{exact .inl N}|@head u v j m ih=>{rcases rC N with rfl|⟨r,p,l⟩;{have:=wb Q j.1;have:=w8 Q m;exact .inr ⟨rR,rH j m,by omega⟩};{have:r=v:=qj (Y _ _ p) j.1 j.2.2;subst this;rcases ih l with K|⟨J,H,z⟩;exact .inl K;exact .inr ⟨rH j J,H,z⟩}}
omit [GIdx gi] in lemma qx(h:c<=q):RT R a c/\RT R c q:=by induction M using rI with|refl=>{exact⟨rR,N⟩}|@head u v m r ih=>{rcases rC N with rfl|⟨z,l,p⟩;{have:=wb Q m.1;have:=w8 Q r;omega};{have:z=v:=qj (Y _ _ l) m.1 m.2.2;subst this;obtain⟨J,H⟩:=ih p;exact⟨rH l J,H⟩}}
omit [GIdx gi] in lemma qr(i:q<=c):EC D a q:=by rcases y9 Q Y M N with m|⟨p,_,_⟩;{have:=qk Q Y m;have l:q=c:=by{omega};rw[l];exact M};{exact p}
end
section
variable (Q:q0 10 D)
include Q
omit [GIdx gi] in lemma z7{a d c:Nat}(m:EC D a d)(l:EC D a c)(i:¬(fM 10 D d=∅/\kS D d=1))(g:¬(fM 10 D c=∅/\kS D c=1)):d=c:=by rcases y9 Q (λ _ _ h=>h.1) m l with v|⟨_,u,q⟩;{rcases rC v with rfl|⟨_,p,_⟩;{rfl};{exact absurd p.2 i}};{rcases rC u with r|⟨_,p,_⟩;{exact absurd r q};{exact absurd p.2 g}}
omit [GIdx gi] in lemma vr(c:D≠[]):kS D (qb 10 D)=0:=by by_contra d;have g:=wk Q (w:=qb 10 D) (by omega);have h:=lP c;unfold qb at g;omega
omit [GIdx gi] in lemma CO{w:Nat}{c a:V}(i:gX D w c)(g:gX D w a):c=a:=by obtain⟨y,u,l,p⟩:=i;obtain⟨v,r,j,m⟩:=g;have q:=z7 Q u r (λ h=>by rw[h.1] at l;exact nE _ l) (λ h=>by rw[h.1] at j;exact nE _ j);subst q;exact le_antisymm (p a j) (m c l)
end
omit [GIdx gi] in lemma CY{d c:EI}(a:uc E d c)(g:gS D (10+(E d).1)):gS D (10+(E c).1):=by unfold uc at a;rw[<-a];exact g
omit [GIdx gi] in lemma CZ{d c:EI}{z:V}(a:uc E d c)(g:gX D (10+(E d).1) z):gX D (10+(E c).1) z:=by unfold uc at a;rw[<-a];exact g
section
variable (H:SL D)(S:SC D)
include H S
lemma yq(c:vD 10 D<=1):∀d w,w<10+(tD D)->qb 10 D-w=d->gS D w\/yI D w\/∃z:V,gX D w z:=by intro d;induction d using sI with|ind d ih=>{intro w P M;by_cases j:(fM 10 D w).Nonempty;{exact .inr (.inr ⟨(fM 10 D w).min' j,w,rR,min'_mem _ j,min'_le _⟩)};rw[fN] at j;by_cases p:w=qb 10 D;{exact .inl ⟨p▸rR,qn G0 S⟩};have:=lP H.2.2;have q:w+1<10+(tD D):=by{unfold qb at p;omega};have L:=H.2.1 w q;by_cases v:2<=kS D w;{exact .inr (.inl ⟨by{by_cases J:vD 10 D=0;exact absurd (y7 H.1 J v) (j▸gk);omega},w,rR,j,v⟩)};have m:kS D w=1:=by{omega};obtain⟨g,i⟩:=fz.1 (show 0<(qg D w).card by{unfold kS at m;omega});simp only[qg,mF,mR] at i;have l:q5 10 D w (10+g):=⟨by omega,by omega,by{rw[nA];exact i.2}⟩;have:=wb H.1 l;have y:q5 10 D w (10+g)/\fM 10 D w=∅/\kS D w=1:=⟨l,j,m⟩;rcases ih (qb 10 D-(10+g)) (by{unfold qb at M ⊢;omega}) (10+g) (by omega) rfl with ⟨hch,hso⟩|⟨u,b0,hcb,his⟩|⟨z,r,hcr,hzr,hmin⟩;{exact .inl ⟨.head y hch,hso⟩};{exact .inr (.inl ⟨u,b0,.head y hcb,his⟩)};{exact .inr (.inr ⟨z,r,.head y hcr,hzr,hmin⟩)}}
lemma vU(c:vD 10 D<=1)(g:gP D E)(a:EI):gS D (10+(E a).1)\/yI D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=yq H S c _ (10+(E a).1) (by have i:=(sM.1 (g p55 a).1).1;rw[zN] at i;omega) rfl
lemma B2(g:vD 10 D=0)(d:gP D E)(a:EI):gS D (10+(E a).1)\/∃z:V,gX D (10+(E a).1) z:=by rcases vU H S (by omega) d a with i|l|j;{exact .inl i};{exact absurd l.1 (by omega)};{exact .inr j}
lemma CN(j:G1 D k I W E F O){c:EI}{z:V}(d:gX D (10+(E c).1) z)(a:¬fZ D E c):∃l<qX k I z,xE D W E c z l:=by classical set u:=kT c;set v:=kU c;obtain⟨r,hcr,hzr,_⟩:=d;have L:=(qx H.1 (λ _ _ d=>d.1) hcr (jt H.1 S a) (by{have:=wx hzr;have:=lP H.2.2;unfold qb;omega})).2;have hb:∃g,g<(tD D)/\fO D (s2 u v) (10+g)=p63/\z∉fM 10 D (10+g)/\∃s:Bool,AR D (s2 u v) r (fC D (g,s))/\z∈fM 10 D (fC D (g,s)):=by{obtain⟨g,s,h1,_,h3,h4,h5,h6,_⟩:=y6 H.1 L hzr (by{rw[qn G0 S];exact nE _});exact⟨g,h1,h3,h6,s,h4,h5⟩};set g0:=p22 hb;obtain⟨m,J,A,s,K,p⟩:=p24 hb;have hW:(g0,s)∈fD 10 D z:=sM.2 ⟨m,p,A⟩;have M:=sA H.1 hW;obtain⟨l,q,h7⟩:=L8 j z (g0,s) hW;have Z:r<10+g0:=lt_of_le_of_lt (qp H.1 K) (w7 H.1 m s);refine⟨l,lL q (L5 j z),⟨q,by{have:=w8 H.1 hcr;rw[h7];dsimp;omega}⟩,?_⟩;set y:=fC D (g0,!s);rw[show (qA D W z l u\/qA D W z l v)↔(u∈fM 10 D y\/v∈fM 10 D y) by simp[qA,gQ,q,h7,qZ,y]];by_contra Y;push Not at Y;have h8:fO D (s2 u v) y=p63:=by{rw[qd H.1 _ m s,M,wV,bA] at J;exact J.2};have R:z∉fM 10 D y:=λ Q=>A <| by{rw[qm H.1 m M,mI];cases s<;>simp only[fC,y,Bool.not_false,p61] at p Q ⊢;exact⟨p,Q⟩;exact⟨Q,p⟩};rcases y9 H.1 (λ _ _ d=>d.1) hcr (y8 H.1 a h8 Y.1 Y.2) with ha|⟨_,h0,U⟩;{obtain⟨g1,s1,h1,h2,h3,h4,h5,h6,_⟩:=y6 H.1 ha hzr R;have hk:y<10+p22 hb:=w7 H.1 m (!s);exact p23 hb (by omega:g1<p22 hb) ⟨h1,h3,h6,s1,h4,h5⟩};{rcases rC h0 with he|⟨_,h9,X⟩;exact U he;have:=w8 H.1 (qj h9.1 (qs m (!s)) h9.2.2▸X);omega}
end
lemma ve(d:SC D){a b:V}(c:¬qW a b):fO D (s2 a b) (qb 10 D)=p55:=by cases j:fO D (s2 a b) (qb 10 D) with|false=>{rfl}|true=>{exfalso;obtain⟨x,y,g,i,h⟩:=(d (s2 a b)).1 j;simp only[q1,bO,dT] at i h;rcases i with rfl|rfl<;>rcases h with rfl|rfl;{exact G0.2.1 _ g};{exact c g};{exact c (G0.1 _ _ g)};{exact G0.2.1 _ g}}
section
variable (H:SL D)(S:SC D){d:EI}{a b:V}(U:¬qW a b)(N:¬fZ D E d)
include H S d a b U N
lemma ya:kc D E d a b (wi D E d a b)/\∀w<10+wi D E d a b,AR D (s2 (kT d) (kU d)) (10+(E d).1) w->fO D (s2 a b) w=p63:=by classical have v:=lP H.2.2;have q:10+((tD D)-1)=qb 10 D:=by{unfold qb;omega};have p:∃g,kc D E d a b g:=⟨(tD D)-1,by omega,q▸jt H.1 S N,q▸ve S U⟩;rw[show wi D E d a b=p22 p by{unfold wi;exact hD p}];refine⟨p24 p,λ w z u=>?_⟩;have:=qp H.1 u;have m:w-10<p22 p:=by{omega};have l:10+(w-10)=w:=by{omega};cases y:fO D (s2 a b) w;exact absurd ⟨lt_trans m (p24 p).1,l.symm▸u,l.symm▸y⟩ (p23 p m);rfl
lemma zo{s:Bool}(g:AR D (s2 (kT d) (kU d)) (10+(E d).1) (fC D (wi D E d a b,s))):gZ D (wi D E d a b)=p63/\a∉fM 10 D (fC D (wi D E d a b,!s))/\b∉fM 10 D (fC D (wi D E d a b,!s))/\(kT d∈fM 10 D (fC D (wi D E d a b,!s))\/kU d∈fM 10 D (fC D (wi D E d a b,!s))):=by set y:=wi D E d a b;obtain⟨⟨m,u,z⟩,hmin⟩:=ya H S U N;have p:=w7 H.1 m s;have hvf':=z;rw[qd H.1 _ m s,hmin _ p g] at hvf';have J:gZ D y=p63:=by{cases A:gZ D y;rw[A,A5] at hvf';simp at hvf';rfl};have l:fO D (s2 a b) (fC D (y,!s))=p55:=by{rw[J,wV,p64] at hvf';exact hvf'};have q:fO D (s2 (kT d) (kU d)) (10+y)=p63:=by{rcases rK u with M|⟨_,_,P⟩;exact absurd (lt_of_le_of_lt (qp H.1 g) p) (M▸lt_irrefl _);exact P.2.2};have r:fO D (s2 (kT d) (kU d)) (fC D (y,!s))=p63:=by{rw[qd H.1 _ m s,J,wV,bA] at q;exact q.2};refine⟨J,λ R=>sF H.1 R (.inl rfl) l,λ Q=>sF H.1 Q (.inr rfl) l,by_contra λ v=>?_⟩;push Not at v;exact p58 ((hmin _ (w7 H.1 m (!s)) (y8 H.1 N r v.1 v.2)).symm.trans l)
lemma x3(A:fO D (s2 a b) (10+(E d).1)=p63):gZ D (wi D E d a b)=p63:=by obtain⟨⟨_,m,q⟩,_⟩:=ya H S U N;rcases rK m with u|⟨_,r,v⟩;{rw[<-u,q] at A;cases A};{obtain⟨g,s,_,y,p⟩:=y3.1 v.1;have z:g=wi D E d a b:=by{omega};rw[z] at p;subst p;exact (zo H S U N r).1}
end
lemma C0(H:SL D)(S:SC D)(B:vD 10 D=0)(G:G1 D k I W E F O){d:EI}{am cm:Nat}(hd:am.testBit d.1=p63)(hnsec:¬fZ D E d)(hstay:∀e:EI,am.testBit e.1=p63->¬gS D (10+(E e).1))(hpick:∀e:EI,am.testBit e.1=p63->∀z:V,cm.testBit z.1=p55->¬gX D (10+(E e).1) z)(hfree:∀z:V,cm.testBit z.1=p63->∀l<qX k I z,¬gT D W E z l)(hopp:∀z:V,cm.testBit z.1=p63->∀l<qX k I z,∀y:V,cm.testBit y.1=p63->¬qA D W z l y)(hesc:∀z:V,cm.testBit z.1=p63->∀l<qX k I z,¬uE D W E d am z l):False:=by set x:=s2 (kT d) (kU d);let Good (w:Nat):Prop:=(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D w)\/(∃e:EI,am.testBit e.1=p63/\EC D (10+(E e).1) w);have hstep:{a b:Nat}->{e:EI}->am.testBit e.1=p63->EC D (10+(E e).1) a->q5 10 D a b->(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)\/EC D (10+(E e).1) b:=by{intro a b e he hza hab;rcases B2 H S B (L9 G) e with hs|⟨z,hzx⟩;{exact absurd hs (hstay e he)};{have hzc:cm.testBit z.1=p63:=by{cases hcb:cm.testBit z.1;{exact absurd hzx (hpick e he z hcb)};{rfl}};obtain⟨r,hzr,hzmr,_⟩:=hzx;rcases y9 H.1 (λ _ _ h=>h.1) hzr hza with hra|⟨_,har,hne⟩;{rcases rC hra with rfl|⟨_,hr,_⟩;{exact .inl ⟨z,hzc,hzmr⟩};{rw[hr.2.1] at hzmr;exact absurd hzmr (nE z)}};{rcases rC har with rfl|⟨c,ha,_⟩;{exact absurd rfl hne};{have hcb:c=b:=qj ha.1 hab ha.2.2;exact .inr (hza.tail ⟨hab,ha.2.1,ha.2.2⟩)}}}};have hGood:∀w,AR D x (10+(E d).1) w->Good w:=by{intro w;induction w using sI with|ind b ih=>{intro har;rcases rK har with rfl|⟨a,hara,hstep_ab⟩;{exact .inr ⟨d,hd,rR⟩};{have hga:Good a:=ih a (wb H.1 hstep_ab.1) hara;have hfrom_z:(∃z:V,cm.testBit z.1=p63/\z∈fM 10 D a)->Good b:=by{rintro⟨z,hzc,hza⟩;obtain⟨g,s,hg,rfl,rfl⟩:=y3.1 hstep_ab.1;by_cases hzb:z∈fM 10 D (10+g);{exact .inl ⟨z,hzc,hzb⟩};{have hW:(g,s)∈fD 10 D z:=sM.2 ⟨hg,hza,hzb⟩;have hA:=sA H.1 hW;obtain⟨l,hl,hWl⟩:=L8 G z (g,s) hW;have hlcap:l<qX k I z:=lL hl (L5 G z);have hnf:=hfree z hzc l hlcap;have ⟨e',s',he'⟩:∃e' s',W z l=kF s' (E e'):=by{unfold gT at hnf;push Not at hnf;exact hnf hl};have hge':(E e').1=g:=by{have:=congrArg p65 (hWl.symm.trans he');cases s'<;>simpa[kF] using this.symm};set y:=fC D (g,!s);have hOy:fO D x y=p63:=by{have hOb:=hstep_ab.2.2;rw[qd H.1 x hg s,hA,wV,bA] at hOb;exact hOb.2};have hy_eq:fC D (qZ (W z l))=y:=by{rw[hWl];rfl};by_cases hopp_uv:kT d∈fM 10 D y\/kU d∈fM 10 D y;{have hopp':qA D W z l (kT d)\/qA D W z l (kU d):=hopp_uv.imp (λ h=>⟨hl,hy_eq.symm▸h⟩) (λ h=>⟨hl,hy_eq.symm▸h⟩);have ham':am.testBit e'.1=p63:=by{cases hbit:am.testBit e'.1;{exact absurd ⟨hopp',e',by simp[hbit],s',hl,he'⟩ (hesc z hzc l hlcap)};{rfl}};exact .inr ⟨e',ham',by{rw[hge'];exact rR}⟩};{push Not at hopp_uv;have hgy:Good y:=ih y (w7 H.1 hg (!s)) (y8 H.1 hnsec hOy hopp_uv.1 hopp_uv.2);rcases hgy with ⟨z',hz'c,hz'y⟩|⟨e'',he'',hze''⟩;{exact absurd ⟨hl,hy_eq.symm▸hz'y⟩ (hopp z hzc l hlcap z' hz'c)};{rcases hstep he'' hze'' (qs hg (!s)) with ⟨z'',hz''c,hz''y⟩|hzb'';{exact absurd ⟨hl,hy_eq.symm▸hz''y⟩ (hopp z hzc l hlcap z'' hz''c)};{exact .inr ⟨e'',he'',hzb''⟩}}}}};rcases hga with hza|⟨e,he,hza⟩;{exact hfrom_z hza};{rcases hstep he hza hstep_ab.1 with hza'|hzb';{exact hfrom_z hza'};{exact .inr ⟨e,he,hzb'⟩}}}}};rcases hGood (qb 10 D) (jt H.1 S hnsec) with ⟨z,_,hzq⟩|⟨e,he,hze⟩;{rw[qn G0 S] at hzq;exact nE z hzq};{exact hstay e he ⟨hze,qn G0 S⟩}
lemma Dt(h:SL D)(i:SC D)(j:gP D E){c:EI}{a b:V}(d:¬qW a b)(g:(es D E p55 c a/\es D E p63 c b)\/(es D E p55 c b/\es D E p63 c a)):bc D E c a b c:=by by_cases q:fZ D E c;{exact .inl q};{right;have p:=fG h.1 j c;have l:fO D (s2 a b) (10+(E c).1)=p63:=by{rw[qd h.1 _ p.1 (E c).2,p.2.1,wV];have K:fC D ((E c).1,(E c).2)=fC D (kF p55 (E c)):=by{simp[zN]};have J:fC D ((E c).1,!(E c).2)=fC D (kF p63 (E c)):=by{simp[Ac,qZ]};rw[K,J];rcases g with ⟨y,v⟩|⟨v,y⟩<;>{rw[q3 h.1 y (by simp[q1]),q3 h.1 v (by simp[q1])];rfl}};obtain⟨⟨_,m,r⟩,_⟩:=ya h i d q;have H:=qp h.1 m;have z:(E c).1≠wi D E c a b:=λ u=>by{rw[u,r] at l;cases l};exact⟨l,rR,m,by omega⟩}
section
variable (H:SL D)(S:SC D)(G:G1 D k I W E F O){d:EI}{a b:V}(U:¬qW a b)
include H S G d a b U
lemma zu(g:¬fZ D E d){s:Bool}(j:AR D (s2 (kT d) (kU d)) (10+(E d).1) (fC D (wi D E d a b,s)))(i:fM 10 D (fC D (wi D E d a b,s))=∅):∃z:V,(z=kT d\/z=kU d)/\z≠a/\z≠b/\∃l<qX k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by set M:=wi D E d a b;have v:=(ya H S U g).1.1;obtain⟨ht,X,B,R⟩:=zo H S U g j;have A:fM 10 D (10+M)=∅:=fE.2 λ c P=>nE _ (i▸sU H.1 v ht s P);have y:∀{z:V},z=kT d\/z=kU d->z∈fM 10 D (fC D (M,!s))->∃z:V,(z=kT d\/z=kU d)/\z≠a/\z≠b/\∃l<qX k I z,gQ D z l/\(W z l).1=M/\gU D W z l:=λ {z} L r=>by{obtain⟨l,u,Q⟩:=L8 G z (M,!s) (sM.2 ⟨v,r,A▸nE _⟩);exact⟨z,L,λ Y=>X (by{rw[Y] at r;exact r}),λ Y=>B (by{rw[Y] at r;exact r}),l,lL u (L5 G z),u,by rw[Q],u,by{rw[Q,sK];exact i}⟩};exact R.elim (y (.inl rfl)) (y (.inr rfl))
lemma qq(j:¬fZ D E d){m:Nat}(_hws_lt:m<10+wi D E d a b)(i:AR D (s2 (kT d) (kU d)) (10+(E d).1) m)(A:AR D (s2 (kT d) (kU d)) m (10+wi D E d a b))(r:EC D m (10+wi D E d a b)):∃z:V,(z=kT d\/z=kU d)/\z≠a/\z≠b/\∃l<qX k I z,gQ D z l/\(W z l).1=wi D E d a b/\gU D W z l:=by rcases rK r with Q|⟨p,K,y⟩;{omega};{obtain⟨g,s,_,M,B⟩:=y3.1 y.1;have P:g=wi D E d a b:=by{omega};rw[P] at B;exact zu H S G U j (B▸i.trans (qx H.1 (λ _ _ L=>L.1) K A (le_of_lt (wb H.1 y.1))).1) (B▸y.2.1)}
lemma vf(i:¬fZ D E d)(p:fO D (s2 a b) (10+(E d).1)=p63){m:Nat}(_hws_lt:m<10+wi D E d a b)(q:AR D (s2 (kT d) (kU d)) (10+(E d).1) m)(j:AR D (s2 (kT d) (kU d)) m (10+wi D E d a b)){c:V}(v:gX D m c):EC D m (10+wi D E d a b)\/(c≠a/\c≠b/\gR D c)\/(∃l<qX k I c,gQ D c l/\m<10+(W c l).1/\((¬qA D W c l a/\¬qA D W c l b/\(qA D W c l (kT d)\/qA D W c l (kU d)))\/gT D W E c l))\/(∃e3:EI,m<10+(E e3).1/\(es D E p55 e3 c\/es D E p63 e3 c)/\bc D E d a b e3):=by set hs:=wi D E d a b;obtain⟨r,hcr,hd,_⟩:=v;by_cases hm:10+hs<=r;{exact .inl (qr H.1 (λ _ _ hp=>hp.1) hcr j hm)};obtain⟨X,Z⟩:=qx H.1 (λ _ _ hp=>hp.1) hcr j (by omega);by_cases J:c∈fM 10 D (10+hs);{obtain⟨⟨Q,_,h3⟩,_⟩:=ya H S U i;have hf:=mI.1 (qm H.1 Q (x3 H S U i p)▸J);exact .inr (.inl ⟨λ he=>sF H.1 J (.inl he) h3,λ he=>sF H.1 J (.inr he) h3,fz.2 ⟨hs,mF.2 ⟨mR.2 Q,q8.2 J,q8.2 hf.1,q8.2 hf.2⟩⟩⟩)};obtain⟨g,s,L,_,h8,Y,M,h7,h5⟩:=y6 H.1 Z hd J;have hW:(g,s)∈fD 10 D c:=sM.2 ⟨L,M,h7⟩;obtain⟨l,A,P⟩:=L8 G c (g,s) hW;have B:m<10+g:=by{have:=w8 H.1 hcr;have:=qp H.1 Y;have:=w7 H.1 L s;omega};have K:=(q.trans X).trans Y;by_cases ha:g=hs;{subst ha;obtain⟨_,hl,hk,hi⟩:=zo H S U i K;exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inl (by simpa[qA,gQ,A,P,qZ] using And.intro hl (And.intro hk hi))⟩))};by_cases h6:gT D W E c l;{exact .inr (.inr (.inl ⟨l,lL A (L5 G c),A,P▸B,.inr h6⟩))};have ⟨e3,s3,hb⟩:∃e3 s3,W c l=kF s3 (E e3):=by{unfold gT at h6;push Not at h6;exact h6 A};have h2:(E e3).1=g:=by{simpa[kF,P] using (congrArg p65 hb).symm};have h4:fO D (s2 (kT d) (kU d)) (fC D (g,s))=p63:=by{rw[qd H.1 _ L s,sA H.1 hW,wV,bA] at h8;exact h8.1};have R:es D E s3 e3 c:=by{unfold es;rw[<-hb,P];exact M};exact .inr (.inr (.inr ⟨e3,by omega,by{cases s3;exact .inl R;exact .inr R},.inr ⟨p,h2.symm▸K.tail ⟨qs L s,h4,h8⟩,h2.symm▸h5,by omega⟩⟩))
lemma Dr{j:EI}(i:bc D E d a b j)(g:gS D (10+(E j).1)):fZ D E d\/∃z:V,(z=kT d\/z=kU d)/\z≠a/\z≠b/\∃l<qX k I z,AN D W E j z l:=by rcases i with q|⟨_,K,r,v⟩;{exact .inl q};{by_cases q:fZ D E d;{exact .inl q};{right;have:=(ya H S U q).1.1;have:=lP H.2.2;obtain⟨z,Q,P,M,l,y,u,J,L⟩:=qq H S G U q (by omega) K r (qr H.1 (λ _ _ R=>R.1) g.1 r (by{unfold qb;omega}));exact⟨z,Q,P,M,l,y,⟨u,J▸v⟩,L⟩}}
lemma Ds{A:EI}{c:V}(m:bc D E d a b A)(j:gX D (10+(E A).1) c):fZ D E d\/(∃z:V,(z=kT d\/z=kU d)/\z≠a/\z≠b/\∃l<qX k I z,AN D W E A z l)\/(c≠a/\c≠b/\gR D c)\/(∃l<qX k I c,wC D W E d a b A c l\/Cu D W E A c l)\/(∃e3:EI,e3≠A/\wB D E d a b A c e3):=by rcases m with v|⟨Q,B,y,J⟩;{exact o1 v};{by_cases v:fZ D E d;{exact o1 v};{rcases vf H S G U v Q (by omega) B y j with K|hm|⟨l,u,r,h2,R⟩|⟨e3,C,X,Z⟩;{obtain⟨z,P,h1,h0,l,u,r,M,Y⟩:=qq H S G U v (by omega) B y K;exact o2 (o1 ⟨z,P,h1,h0,l,u,⟨r,by{rw[M];exact J}⟩,Y⟩)};{exact o2 (o2 (o1 hm))};{exact o2 (o2 (o2 (o1 ⟨l,u,R.elim (λ⟨ha,hb,P⟩=>o1 ⟨⟨r,by omega⟩,ha,hb,P⟩) (λ h3=>o2 ⟨⟨r,by omega⟩,h3⟩)⟩)))};{exact o2 (o2 (o2 (o2 ⟨e3,λ he=>by{rw[he] at C;omega},by{unfold yY;omega},X,Z⟩)))}}}
end
end
end
end GraphSec
end
abbrev CellKill (gi:Fin 4)(k I m s:Nat):Prop:=∃t c x:List Nat,Rup.Unsat gi k I m s t c x
section P3Closed
lemma Dk:∀(gi:Fin 4)(e:Fin 14),Fin.ofNat 10 (Rup.ep0N e.1)=wO gi e/\Fin.ofNat 10 (Rup.ep1N gi e.1)=wN gi e/\Rup.ep0N e.1<10/\Rup.ep1N gi e.1<10:=by decide +kernel
lemma BJ:∀(gi:Fin 4)(s:Fin 2)(e:Fin 14),Fin.ofNat 10 (Rup.epN gi s.1 e.1)=x4 gi (s.1==1) e:=by decide +kernel
lemma BS:∀(gi:Fin 4)(u v:Fin 10),Rup.adjB gi u.1 v.1=true <->us gi u v:=by decide +kernel
lemma Al:∀(gi:Fin 4)(x:Fin 10),(Rup.nbrsN gi x.1).map (Fin.ofNat 10)=(List.finRange 10).filter (λ y=>(Rup.nGN gi x.1).testBit y.1):=by decide +kernel
lemma Bw:∀(gi:Fin 4)(u:Fin 10)(k:Fin 3),k.1<(Rup.nbrsN gi u.1).length->(Rup.nbrsN gi u.1).getD k.1 0<10/\us gi u (Fin.ofNat 10 ((Rup.nbrsN gi u.1).getD k.1 0)):=by decide +kernel
lemma BK:∀(gi:Fin 4)(u v:Fin 10),us gi u v->(Rup.eIx gi u.1 v.1).1<14/\(Rup.eIx gi u.1 v.1).2<2/\Fin.ofNat 14 (Rup.eIx gi u.1 v.1).1=(zC gi u v).1/\((Rup.eIx gi u.1 v.1).2==1)=(zC gi u v).2:=by decide +kernel
lemma BR:∀(gi:Fin 4)(u:Fin 16),∀a∈kM (Rup.aMk gi u.1),∀b∈kM (Rup.aMk gi u.1),¬us gi a b:=by decide +kernel
lemma BQ:∀(gi:Fin 4)(u:Fin 10)(v:Fin 16),((Rup.aMk gi v.1)&&&Rup.nGN gi u.1)≠0->∃w∈kM (Rup.aMk gi v.1),us gi u w:=by decide +kernel
lemma Aj:∀(gi:Fin 4)(u:Fin 10),∀y∈Rup.nbrsN gi u.1,y<10:=by decide +kernel
end P3Closed
namespace P3
abbrev CK {gi:Fin 4} [GIdx gi]:=CellKill gi
open DagTools
open Rup
open PEqualNP.Outside.L_meta_18015_aux renaming Ch->V0,AO->V1,zU->V2,Cf->V3,yY->V4,zQ->V5,wS->V6,yF->V7,uo->V8,CH->V9,kA->Va,kF->Vb,AS->Vc
open DagTools renaming BX->Vd,kH->Ve,kP->Vf,qZ->Vg,Bk->Vh,Bg->Vi
section P3G
variable {gi:Fin 4} [GIdx gi]
abbrev ep1N {gi:Fin 4} [GIdx gi]:=Rup.ep1N gi
abbrev epN {gi:Fin 4} [GIdx gi]:=Rup.epN gi
abbrev nGN {gi:Fin 4} [GIdx gi]:=Rup.nGN gi
abbrev adjB {gi:Fin 4} [GIdx gi]:=Rup.adjB gi
abbrev Vn {gi:Fin 4} [GIdx gi]:=Rup.nbrsN gi
abbrev Vj {gi:Fin 4} [GIdx gi]:=Rup.aMk gi
abbrev Vk {gi:Fin 4} [GIdx gi]:=Rup.eIx gi
abbrev Vm {gi:Fin 4} [GIdx gi]:=Rup.iNN gi
abbrev Vl {gi:Fin 4} [GIdx gi]:=Rup.eNN gi
abbrev vTr {gi:Fin 4} [GIdx gi]:=Rup.vTr gi
abbrev vCx {gi:Fin 4} [GIdx gi]:=Rup.vCx gi
abbrev ex1 {gi:Fin 4} [GIdx gi]:=Rup.ex1 gi
abbrev ex2 {gi:Fin 4} [GIdx gi]:=Rup.ex2 gi
abbrev ex3 {gi:Fin 4} [GIdx gi]:=Rup.ex3 gi
abbrev exS {gi:Fin 4} [GIdx gi]:=Rup.exS gi
abbrev en0 {gi:Fin 4} [GIdx gi]:=Rup.en0 gi
abbrev en1 {gi:Fin 4} [GIdx gi]:=Rup.en1 gi
abbrev en2 {gi:Fin 4} [GIdx gi]:=Rup.en2 gi
abbrev en3 {gi:Fin 4} [GIdx gi]:=Rup.en3 gi
abbrev enabled {gi:Fin 4} [GIdx gi]:=Rup.enabled gi
abbrev expS {gi:Fin 4} [GIdx gi]:=Rup.expS gi
abbrev enS {gi:Fin 4} [GIdx gi]:=Rup.enS gi
open List renaming mem_map->Vo,length_map->Vp,range->Vq
open Nat renaming reduceLT->Vr
abbrev Ei:=wE
abbrev Ws:=V->Nat->Slot
abbrev Es:=Ei->Slot
abbrev Os k:=Fin k->Option (Σ _:Nat,Nat)
abbrev LN:=List Nat
abbrev F(x:Nat):V:=Fin.ofNat 10 x
abbrev J(e:Nat):Ei:=Fin.ofNat 14 e
noncomputable def bP(P:Prop):Bool:=@decide P (Classical.propDecidable P)
omit [GIdx gi] in @[local simp] lemma bt{P:Prop}:bP P=true <->P:=@decide_eq_true_iff P (Classical.propDecidable P)
omit [GIdx gi] in @[local simp] lemma bf{P:Prop}:bP P=false <->¬P:=@decide_eq_false_iff_not P (Classical.propDecidable P)
omit [GIdx gi] in lemma sA{a b}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
omit [GIdx gi] in lemma sD{p} [Decidable p]:(decide p=true)=p:=decide_eq_true_eq
omit [GIdx gi] in lemma sQ{α} [BEq α] [LawfulBEq α] {a b:α}:(a==b)=true <->a=b:=beq_iff_eq
omit [GIdx gi] in lemma sN{α} [BEq α] [LawfulBEq α] {a b:α}:(a != b)=true <->a≠b:=bne_iff_ne
omit [GIdx gi] in lemma sB{a}:((!a)=true)=(a=false):=Bool.not_eq_true' a
omit [GIdx gi] in lemma sC{a b c:Prop}:(a/\b)/\c <->a/\b/\c:=and_assoc
omit [GIdx gi] in lemma sT{α}{a b:α}:(if True then a else b)=a:=ite_true a b
omit [GIdx gi] in lemma sF{α}{a b:α}:(if False then a else b)=b:=ite_false a b
abbrev mo{a b:Nat} (h:a<b):=Nat.mod_eq_of_lt h
abbrev T{P Q:Prop} (h:P <->Q):=h.1
abbrev W{P Q:Prop} (h:P <->Q):=h.2
omit [GIdx gi] in lemma xZ{x}(h:x<10):(F x).1=x:=mo h
omit [GIdx gi] in lemma xS{x y}(hx:x<10)(hy:y<10)(h:x≠y):F x≠F y:=λ q=>h (by rw[<-xZ hx,<-xZ hy,q])
omit [GIdx gi] in lemma vL(x:V):F x.1=x:=Fin.ext (mo x.2)
omit [GIdx gi] in lemma yP(e:Ei):J e.1=e:=Fin.ext (mo e.2)
omit [GIdx gi] in lemma aM(n r:Nat):r&&&(2^n-1)<2^n:=by rw[Nat.and_two_pow_sub_one_eq_mod];exact Nat.mod_lt _ (Nat.two_pow_pos n)
omit [GIdx gi] in lemma a1(r:Nat):r&&&1<2:=aM 1 r
omit [GIdx gi] in lemma a4(r:Nat):r&&&15<16:=aM 4 r
omit [GIdx gi] in lemma a6(r:Nat):r&&&63<64:=aM 6 r
omit [GIdx gi] in lemma uX{s}(h:s<2):((1-s)==1)=!(s==1):=by rcases (by omega:s=0\/s=1) with rfl|rfl<;>rfl
abbrev mF{α p} [DecidablePred p] {s:Finset α} {a}:=@Finset.mem_filter α p _ s a
abbrev mU{α} [Fintype α]:=@Finset.mem_univ α _
abbrev mG{α β} [DecidableEq β] {f:α->β} {s a}:=@Finset.mem_image α β _ f s a
abbrev lR{n m}:=@List.mem_range n m
abbrev lF{α p} {l:List α} {a}:=@List.mem_filter α p l a
omit [GIdx gi] in lemma uq{n x}(h:x<n):∃u:Fin n,u.1=x:=⟨⟨x,h⟩,rfl⟩
lemma eN{e}(h:e<14):F (ep0N e)=kT (J e)/\F (ep1N e)=kU (J e)/\ep0N e<10/\ep1N e<10:=by obtain⟨u,rfl⟩:=uq h;simpa[yP] using Dk gi u
abbrev xU{e} (h:e<14):=(eN h).1
abbrev xT{e} (h:e<14):=(eN h).2.1
abbrev xH{e} (h:e<14):=(eN h).2.2.1
abbrev xG{e} (h:e<14):=(eN h).2.2.2
lemma Ck{s e}(d:s<2)(he:e<14):F (epN s e)=wX (s==1) (J e):=by obtain⟨u,rfl⟩:=uq d;obtain⟨v,rfl⟩:=uq he;simpa[yP] using BJ gi u v
lemma Cl{s e}(he:e<14):epN s e<10:=by unfold epN Rup.epN;split<;>[exact xH he;exact xG he]
lemma zV{x y}(d:x<10)(hy:y<10):Rup.adjB gi x y=true <->qW (F x) (F y):=by obtain⟨u,rfl⟩:=uq d;obtain⟨v,rfl⟩:=uq hy;simpa[vL] using BS gi u v
omit [GIdx gi] in lemma AH(k I){x}(d:x<10):kk k I x=qX k I (F x):=by unfold kk kB qX;simp[mo d]
omit [GIdx gi] in lemma c5{k I x j}(h:j<kk k I x)(_:k<=3:=by omega):j<5:=by unfold kk at h;split at h<;>omega
omit [GIdx gi] in lemma Ct{k I j}{z:V}(h:j<qX k I z)(_:k<=3:=by omega):j<5:=c5 (by rw[AH k I z.2,vL];exact h)
omit [GIdx gi] in lemma iB{I x}(d:x<10)(h:kB I x=true):I.testBit (F x).1=true:=by rw[xZ d];exact h
omit [GIdx gi] in lemma nB{I x}(d:x<10)(h:kB I x=false):I.testBit (F x).1=false:=by rw[xZ d];exact h
lemma Am(x:V):(Vn x.1).map F=(List.finRange 10).filter (λ y=>(wv x).testBit y.1):=Al gi x
lemma Ca{i n}(d:i<10)(h3:n<3)(hn:n<(Vn i).length):(Vn i).getD n 0<10/\qW (F i) (F ((Vn i).getD n 0))/\n<3:=by obtain⟨u,rfl⟩:=uq d;have k:=Bw gi u ⟨n,h3⟩ hn;exact⟨k.1,(vL u).symm▸k.2,h3⟩
lemma A7{x y}(d:x<10)(hy:y<10)(f:qW (F x) (F y)):(Vk x y).1<14/\(Vk x y).2<2/\J (Vk x y).1=(uJ (F x) (F y)).1/\((Vk x y).2==1)=(uJ (F x) (F y)).2:=by obtain⟨u,rfl⟩:=uq d;obtain⟨v,rfl⟩:=uq hy;simpa[vL] using BK gi u v (by simpa[vL] using f)
lemma Dv{a}(d:a<16):AA (kM (Vj a)):=by obtain⟨u,rfl⟩:=uq d;exact BR gi u
lemma Du{x a}(d:x<10)(f:a<16)(h:((Vj a)&&&nGN x)≠0):∃v∈kM (Vj a),qW (F x) v:=by obtain⟨u,rfl⟩:=uq d;obtain⟨v,rfl⟩:=uq f;simpa[vL] using BQ gi u v h
lemma Ak{x}(d:x<10):∀y∈Vn x,y<10:=by obtain⟨u,rfl⟩:=uq d;exact Aj gi u
lemma nF{x}(d:x<10)(p:Nat->Bool)(q:V->Bool)(hp:∀y<10,p y=q (F y)):((Vn x).filter p).map F=(List.finRange 10).filter (λ y=>(wv (F x)).testBit y.1&&q y):=by have f:=Am (F x);simp only[Fin.val_ofNat,mo d] at f;rw[show (Vn x).filter p=(Vn x).filter (q ∘ F) from List.filter_congr λ y hy=>hp y (Ak d y hy),<-List.filter_map,f,List.filter_filter];exact List.filter_congr λ _ _=>Bool.and_comm _ _
lemma C9 I {x}(hx:x<10):(Vm I x).map F=zB I (F x):=nF hx (kB I) (λ y=>I.testBit y.1) λ y hy=>by simp[kB,mo hy]
lemma Dj I {x}(hx:x<10):(Vl I x).map F=yQ I (F x):=nF hx (λ y=>!kB I y) (λ y=>!I.testBit y.1) λ y hy=>by simp[kB,mo hy]
omit [GIdx gi] in lemma B7{k m}(hk:k<=3)(d:m<1<<<k):((Finset.univ:Finset (Fin k)).filter (λ t=>m.testBit t.1)).card=xV m:=by have q:∀a:Fin 4,∀b:Fin 8,b.1<1<<<a.1->((Finset.univ:Finset (Fin a.1)).filter (λ t=>b.1.testBit t.1)).card=xV b.1:=(by decide +kernel);exact q ⟨k,by omega⟩ ⟨m,by interval_cases k<;>omega⟩ d
namespace EP
omit [GIdx gi] in lemma sL(a b:Nat):a+b-a=b:=Nat.add_sub_cancel_left a b
omit [GIdx gi] in lemma d1{a b m:Nat}(h:b<m:=by omega):(a*m+b)/m=a:=by rw[Nat.mul_comm,Nat.mul_add_div (by omega),Nat.div_eq_of_lt h,Nat.add_zero]
omit [GIdx gi] in lemma m1{a b m:Nat}(h:b<m:=by omega):(a*m+b) % m=b:=by rw[Nat.mul_comm,Nat.mul_add_mod,mo h]
abbrev C b (P Q:Nat->Prop) (i:Nat):=cond (i.blt b) (P i) (Q i)
omit [GIdx gi] in lemma cT{a b}{P Q:Nat->Prop}(h:a<b:=by omega):C b P Q a=P a:=by simp[C,Nat.blt_eq,h]
omit [GIdx gi] in lemma cF{a b}{P Q:Nat->Prop}(h:b<=a:=by omega):C b P Q a=Q a:=by simp[C,Nat.blt_eq,Nat.not_lt.2 h]
def s0 n (f:Nat->Prop) i:=f (i-n)
def s1 n u (f:Nat->Nat->Prop) i:=f ((i-n)/u) ((i-n) % u)
def s2 n u v (f:Nat->Nat->Nat->Prop) i:=f ((i-n)/v/u) ((i-n)/v % u) ((i-n) % v)
def s3 n u v w (f:Nat->Nat->Nat->Nat->Prop) i:=f ((i-n)/w/v/u) ((i-n)/w/v % u) ((i-n)/w % v) ((i-n) % w)
omit [GIdx gi] in lemma b0 a {n f}:s0 n f (n+a)=f a:=by rw[s0,sL]
omit [GIdx gi] in lemma b1 a b {n u f}(_:b<u:=by omega):s1 n u f (n+a*u+b)=f a b:=by rw[s1,Nat.add_assoc,sL,d1,m1]
omit [GIdx gi] in lemma b2 a b c {n u v f}(_:b<u/\c<v:=by omega):s2 n u v f (n+(a*u+b)*v+c)=f a b c:=by rw[s2,Nat.add_assoc,sL,d1,m1,d1,m1]
omit [GIdx gi] in lemma b3 a b c d {n u v w f}(_:b<u/\c<v/\d<w:=by omega):s3 n u v w f (n+((a*u+b)*v+c)*w+d)=f a b c d:=by rw[s3,Nat.add_assoc,sL,d1,m1,d1,m1,d1,m1]
omit [GIdx gi] in lemma l{i b}{P Q:Nat->Prop}{R}(h:P i=R)(_:i<b:=by omega):C b P Q i=R:=(cT (a:=i) (b:=b)).trans h
omit [GIdx gi] in lemma r{i b}{P Q:Nat->Prop}{R}(h:Q i=R)(_:b<=i:=by omega):C b P Q i=R:=(cF (a:=i) (b:=b)).trans h
abbrev U3{α} (t:LN) d (f:Ei->V->V->α):=let v:=yA t d;f (J v.1) (F v.2.1) (F v.2.2)
abbrev Uc{α} (t c:LN) (f:Ei->V->V->Ei->V->α) d:=let u:=qY c d;U3 t u.1 f (J u.2.1) (F u.2.2)
abbrev Um{α} (b:LN) a (f:Ei->Nat->α):=let u:=uZ b a;f (J u.1) u.2.1
abbrev BL D {k} w (o:Os k):=C 1080 (C 550 (C 50 (λ i=>V1 D (F (i/5)) (i % 5)) (s2 50 5 10 λ x j c=>uj D w (F x) j (F c))) (C 1050 (s2 550 5 10 λ x j c=>qA D w (F x) j (F c)) (s1 1050 10 λ t x=>Va D o t (F x)))) (C 1480 (C 1180 (s1 1080 10 λ x y=>yB D (F x) (F y)) (s2 1180 10 10 λ t x y=>Va D o t (F x)/\¬Va D o t (F y))) (C 1500 (s1 1480 10 λ t x=>∀v:V,x<=v.1->(Va D o t v <->Va D o (t+1) v)) (C 1510 (s0 1500 λ x=>wJ D (F x)) (s2 1510 10 5 λ t x j=>vW D w o t (F x) j))))
abbrev Co D w e:=C 3636 (C 3340 (C 1940 (s2 1660 14 10 λ s a x=>es D e (s==1) (J a) (F x)) (s3 1940 14 10 5 λ s a x j=>ra D w e (s==1) (J a) (F x) j)) (C 3390 (s1 3340 5 λ x j=>BF D w e (F x) j) (C 3440 (s1 3390 5 λ x j=>Di D w (F x) j) (s1 3440 14 λ a b=>e (J a)=e (J b))))) (C 4224 (C 3832 (s1 3636 14 λ a b=>e (J a)=Vg (e (J b))) (C 4028 (s1 3832 14 λ a b=>uc e (J a) (J b)) (s1 4028 14 λ a b=>V4 e (J a) (J b)))) (C 4924 (s2 4224 10 5 λ a x j=>vQ D w e (J a) (F x) j) (C 4938 (s0 4924 λ a=>Cg D e (J a)) (s2 4938 5 5 λ a u v=>Ad D w e (J a) u v))))
abbrev Cn D w e t:=C 7556 (C 6702 (C 5988 (s2 5288 10 5 λ a x j=>Cu D w e (J a) (F x) j) (C 6688 (s2 5988 10 5 λ a x j=>AN D w e (J a) (F x) j) (s0 6688 λ a=>BZ D (10+(e (J a)).1)))) (C 6716 (λ _=>False) (C 6856 (s1 6716 10 λ a z=>B4 D (10+(e (J a)).1) (F z)) (s2 6856 10 5 λ a z l=>xE D w e (J a) (F z) l)))) (C 7720 (λ _=>False) (C 7742 (λ _=>False) (C 7966 (s1 7742 14 λ d a=>U3 t d (bc D e) (J a)) (λ _=>False))))
abbrev Cm D w e t c (b:LN):=C 10334 (C 9118 (C 8798 (s2 7998 16 5 λ x a j=>V1 D (F x) j/\∀y∈kM (Vj a),¬uj D w (F x) j y) (s1 8798 5 λ d l=>Uc t c (wC D w e) d l)) (C 10014 (s1 9118 14 λ d a=>Uc t c (wB D e) d (J a)) (s2 10014 10 5 λ a z l=>Um b a (uE D w e) (F z) l))) (C 13730 (C 11230 (λ _=>False) (s3 11230 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=w (F x) j)) (C 16230 (s3 13730 5 10 5 λ x j y l=>V1 D (F x) j/\V1 D (F y) l/\w (F y) l=Vg (w (F x) j)) (s3 16230 10 3 5 λ a y n l=>let x:=(Vn a).getD n 0;AN D w e (J (Vk a x).1) (F x) l/\BF D w e (F x) l/\¬uj D w (F x) l (F y)/\∀z:V,qW (F a) z->uj D w (F x) l z)))
def eP(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k):Nat->Prop:=C 5288 (C 1660 (BL D w o) (Co D w e)) (C 7998 (Cn D w e t) (Cm D w e t c b))
lemma p0(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:BL D w o n=P)(eq:i=n:=by rfl)(_:n<1660:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cT,h]
lemma p1(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:Co D w e n=P)(eq:i=n:=by rfl)(_:1660<=n/\n<5288:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cT,cF,h]
lemma p2(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:Cn D w e t n=P)(eq:i=n:=by rfl)(_:5288<=n/\n<7998:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cT,h]
lemma p3(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat){n P}(h:Cm D w e t c b n=P)(eq:i=n:=by rfl)(_:7998<=n:=by omega):eP D w e t c b o i <->P:=by rw[eq,eP,cF,cF,h]
omit [GIdx gi] in lemma zY{P:Nat->Nat->Prop}(s:∀a b,P a b->P b a){x y}:P (min x y) (max x y) <->P x y:=by by_cases h:x<=y;{simp[Nat.min_eq_left h,Nat.max_eq_right h]};{simp only[Nat.min_eq_right (by omega:y<=x),Nat.max_eq_left (by omega:y<=x)];exact⟨s _ _,s _ _⟩}
end EP
noncomputable def zM(D:Dag)(w:Ws)(e:Es)(t c b:LN){k}(o:Os k)(i:Nat):Bool:=bP (EP.eP D w e t c b o i)
section Ev
open EP
variable {D:Dag} {w:Ws} {e:Es} {t c b:LN} {k:Nat} {o:Os k}
lemma v0{x j}(_:x<10/\j<5:=by constructor<;>first|assumption|omega):eP D w e t c b o (kI x j) <->V1 D (F x) j:=by rw[kI,eP,cT,cT,BL,cT,cT,cT,d1,m1]
abbrev v1{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (kE x j y) (l (l (r (b2 x j y))))
abbrev v2{x j y} (_:x<10/\j<5/\y<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p0 D w e t c b o (kD x j y) (l (r (l (b2 x j y))))
abbrev v3{a x} (_:a<3/\x<10:=by omega):=p0 D w e t c b o (kQ a x) (l (r (r (b1 a x))))
abbrev v4{x y} (_:x<10/\y<10:=by omega):=(p0 D w e t c b o (vC x y) (r (l (l (b1 (min x y) (max x y)))))).trans (zY (P:=λ a b=>yB D (F a) (F b)) λ _ _ ⟨z,p,q⟩=>⟨z,q,p⟩)
abbrev v5{a x y} (_:a<3/\x<10/\y<10:=by omega):=p0 D w e t c b o (zG a x y) (r (l (r (b2 a x y))))
abbrev v6{a x} (_:a<2/\x<10:=by omega):=p0 D w e t c b o (AD a x) (r (r (l (b1 a x))))
abbrev v7{x} (_:x<10:=by first|assumption|omega):=p0 D w e t c b o (vK x) (r (r (r (l (b0 x)))))
abbrev v8{a x j} (_:a<3/\x<10/\j<5:=by omega):=p0 D w e t c b o (xQ a x j) (r (r (r (r (b2 a x j)))))
abbrev v9{s a x} (_:s<2/\a<14/\x<10:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (kN s a x) (l (l (l (b2 s a x))))
abbrev u0{s a x j} (_:s<2/\a<14/\x<10/\j<5:=by refine⟨?_,?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (ur s a x j) (l (l (r (b3 s a x j))))
abbrev u1{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (uO x j) (l (r (l (b1 x j))))
abbrev u2{x j} (_:x<10/\j<5:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (wW x j) (l (r (r (l (b1 x j)))))
abbrev u3{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (yN a d) (l (r (r (r (b1 a d)))))
abbrev u4{a d} (_:a<14/\d<14:=by omega):=p1 D w e t c b o (yO a d) (r (l (l (b1 a d))))
abbrev u5{a d} (_:a<14/\d<14:=by omega):=(p1 D w e t c b o (uK a d) (r (l (r (l (b1 (min a d) (max a d))))))).trans (zY (P:=λ a b=>uc e (J a) (J b)) λ _ _=>Eq.symm)
abbrev u6{a d} (_:a<14/\d<14:=by constructor<;>first|assumption|omega):=p1 D w e t c b o (ux a d) (r (l (r (r (b1 a d)))))
abbrev u7{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p1 D w e t c b o (uP a x j) (r (r (l (b2 a x j))))
abbrev u8{a} (_:a<14:=by first|assumption|omega):=p1 D w e t c b o (Cj a) (r (r (r (l (b0 a)))))
abbrev u9{a u v} (_:a<14/\u<5/\v<5:=by omega):=p1 D w e t c b o (yK a u v) (r (r (r (r (b2 a u v)))))
abbrev t0{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (zJ a x j) (l (l (l (b2 a x j))))
abbrev t1{a x j} (_:a<14/\x<10/\j<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p2 D w e t c b o (xR a x j) (l (l (r (l (b2 a x j)))))
abbrev t2{a} (_:a<14:=by first|assumption|omega):=p2 D w e t c b o (zD a) (l (l (r (r (b0 a)))))
abbrev t4{a z} (_:a<14/\z<10:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (wM a z) (l (r (r (l (b1 a z)))))
abbrev t5{a z l0} (_:a<14/\z<10/\l0<5:=by omega):=p2 D w e t c b o (yM a z l0) (l (r (r (r (b2 a z l0)))))
abbrev y2{d a} (_:d<16/\a<14:=by constructor<;>first|assumption|omega):=p2 D w e t c b o (zH d a) (r (r (r (l (b1 d a)))))
abbrev y4{x a j} (_:x<10/\a<16/\j<5:=by omega):=p3 D w e t c b o (zI x a j) (l (l (l (b2 x a j))))
abbrev y5{d l0} (_:d<64/\l0<5:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (wj d l0) (l (l (r (b1 d l0))))
abbrev y6{d a} (_:d<64/\a<14:=by constructor<;>first|assumption|omega):=p3 D w e t c b o (vA d a) (l (r (l (b1 d a))))
abbrev y7{a z l0} (_:a<6/\z<10/\l0<5:=by refine⟨?_,?_,?_⟩<;>first|assumption|omega):=p3 D w e t c b o (zE a z l0) (l (r (r (b2 a z l0))))
abbrev y9{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (yJ x j y l0) (r (l (r (b3 x j y l0))))
abbrev x0{x j y l0} (_:x<10/\j<5/\y<10/\l0<5:=by omega):=p3 D w e t c b o (yL x j y l0) (r (r (l (b3 x j y l0))))
abbrev x1{a y n l0} (_:a<10/\y<10/\n<3/\l0<5:=by omega):=p3 D w e t c b o (zF a y n l0) (r (r (r (b3 a y n l0))))
abbrev Hp(P:Nat->Prop):=Holds (λ i=>bP (P i))
section Hc
variable {P:Nat->Prop}
omit [GIdx gi] in lemma R{a}(h:P a):Hp P [(a,true)]:=⟨_,.head _,bt.2 h⟩
omit [GIdx gi] in lemma j0{a}(h:¬P a):Hp P [(a,false)]:=⟨_,.head _,bf.2 h⟩
omit [GIdx gi] in lemma G{a c}(h:P a->Hp P c):Hp P ((a,false)::c):=(Classical.em (P a)).elim (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩) (λ q=>⟨_,.head _,bf.2 q⟩)
omit [GIdx gi] in lemma jT{a c}(h:¬P a->Hp P c):Hp P ((a,true)::c):=(Classical.em (P a)).elim (λ q=>⟨_,.head _,bt.2 q⟩) (λ q=>let ⟨l,hl,hy⟩:=h q;⟨l,.tail _ hl,hy⟩)
abbrev B{a b} (h:P a->P b):=G λ q=>R (h q)
abbrev Z{a b} (h:P a->¬P b):=G λ q=>j0 (h q)
abbrev j3{a b c} (h:P a->P b->P c):=G λ p=>B (h p)
abbrev k3{a b c} (h:P a->P b->¬P c):=G λ p=>Z (h p)
abbrev zT{a b c} (h:P a->¬P b->Hp P c):=G λ p=>jT (h p)
abbrev BA{a b c} (h:P a->P b->Hp P c):=G λ p=>G (h p)
abbrev C4{a b c} (h:¬P a->¬P b->Hp P c):=jT λ p=>jT (h p)
abbrev xW{a b c d} (h:P a->P b->¬P c->Hp P d):=G λ p=>zT (h p)
omit [GIdx gi] in lemma cb{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->q):Hp P [(a,false),(b,true)]:=B λ h=>hb.2 (f (ha.1 h))
omit [GIdx gi] in lemma cz{a b}{p q:Prop}(ha:P a <->p)(hb:P b <->q)(f:p->¬q):Hp P [(a,false),(b,false)]:=Z λ h k=>f (ha.1 h) (hb.1 k)
omit [GIdx gi] in lemma c3{a b c}{p q r:Prop}(ha:P a <->p)(hb:P b <->q)(hc:P c <->r)(f:p->q->r):Hp P [(a,false),(b,false),(c,true)]:=j3 λ h k=>hc.2 (f (ha.1 h) (hb.1 k))
omit [GIdx gi] in lemma jI{a b c}{p:Bool}(h:P a->(P b <->P c)):Hp P [(a,false),(b,p),(c,!p)]:=G λ q=>match p with|false=>G λ r=>R ((h q).1 r)|true=>jT λ r=>j0 λ s=>r ((h q).2 s)
omit [GIdx gi] in lemma jQ{a b c}{p:Bool}(h:(P a <->P b)->P c):Hp P [(a,p),(b,p),(c,true)]:=by cases p;{exact G λ a=>G λ b=>R (h ⟨λ _=>b,λ _=>a⟩)};{exact jT λ a=>jT λ b=>R (h ⟨λ x=>absurd x a,λ x=>absurd x b⟩)}
omit [GIdx gi] in lemma jL{c1 c2}:Hp P c1->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_left _ hl,hy⟩
omit [GIdx gi] in lemma jR{c1 c2}:Hp P c2->Hp P (c1++c2)|⟨l,hl,hy⟩=>⟨l,List.mem_append_right _ hl,hy⟩
omit [GIdx gi] in lemma jG{n} {f:Nat->Nat}:(∃j<n,P (f j))->Hp P ((Vq n).map λ j=>(f j,true))
 | ⟨j,hj,q⟩=>⟨_,Vo.2 ⟨j,lR.2 hj,rfl⟩,bt.2 q⟩
omit [GIdx gi] in lemma C5{n} {f g:Nat->Nat}:(∃j<n,P (f j)\/P (g j))->Hp P ((Vq n).flatMap λ j=>[(f j,true),(g j,true)])
 | ⟨j,hj,h⟩=>h.elim (λ p=>⟨(f j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩) (λ p=>⟨(g j,true),List.mem_flatMap.2 ⟨j,lR.2 hj,by simp⟩,bt.2 p⟩)
end Hc
lemma jM{m x}(hk:k<=3)(hx:x<10)(h:∃i:Fin k,m.testBit i.1=true/\Va D o i.1 (F x)):Holds (zM D w e t c b o) (uw k m x):=by obtain⟨⟨i,d⟩,f,j⟩:=h;have q:=W (v3 (D:=D) (w:=w) (e:=e) (t:=t) (c:=c) (b:=b) (o:=o)) j;unfold uw;rcases (by omega:i=0\/i=1\/i=2) with rfl|rfl|rfl;{exact jL (jL (by simp[d,f];exact R q))};{exact jL (jR (by simp[d,f];exact R q))};{exact jR (by simp[d,f];exact R q)}
lemma jU{I eo x y}{f:Nat->Nat->Nat}(d:eo<14)(h:∃z:V,(z=kT (J eo)\/z=kU (J eo))/\z≠F x/\z≠F y/\∃l<qX k I z,eP D w e t c b o (f z.1 l)):Holds (zM D w e t c b o) (wq k I (ep0N eo) (ep1N eo) x y λ z l=>(f z l,true)):=by obtain⟨z,n,m,j,l,hl,i⟩:=h;have p u (hu:u<10) (he:F u=z):Holds (zM D w e t c b o) (if u != x&&u != y then (Vq (kk k I u)).map λ l=>(f u l,true) else []):=by{have ha:u≠x:=λ q=>m (by rw[<-he,q]);have v:u≠y:=λ q=>j (by rw[<-he,q]);simp[ha,v];exact jG ⟨l,by rw[AH k I hu,he];exact hl,by rw[<-he,xZ hu] at i;exact i⟩};rcases n with rfl|rfl;{exact jL (p _ (xH d) (xU d))};{exact jR (p _ (xG d) (xT d))}
end Ev
def BT(D:Dag):Nat->Prop
 | 0=>True
 | 1=>vD 10 D=0
 | _=>False
def Cv(_D:Dag) (_e:Es) {k} (_o:Os k):Nat->Prop
 | 0=>True
 | _=>False
omit [GIdx gi] in lemma Aq{D I x}(q:kM I=Ve 10 D)(d:x<10)(h:kB I x=true):F x∈Ve 10 D:=by rw[<-q];exact mF.2 ⟨mU _,iB d h⟩
omit [GIdx gi] in lemma BW(s:Bool)(p:Slot):Vb s (Vg p)=Vb (!s) p:=by rcases p with ⟨g,b⟩;cases s<;>cases b<;>rfl
omit [GIdx gi] in lemma AT(s:Bool)(p:Slot):(Vb s p).1=p.1:=by cases s<;>rfl
def ub(I x:Nat):LN:=Vm I x++(Vl I x).take 1
lemma xl I {x}(hx:x<10)(e:Es):V6 I e (F x)=(ub I x).map λ y=>V7 e (F x) (F y):=by dsimp only[V6,ub];rw[List.map_append,<-C9 I hx,List.map_map];congr 1;have q:=Dj I hx;cases h:Vl I x<;>rw[h] at q<;>rw[<-q]<;>rfl
lemma CP{I x}(d:x<10)(e:Es):(V6 I e (F x)).length=(Vm I x).length+(if (Vl I x).isEmpty then 0 else 1):=by rw[xl I d,Vp,ub,List.length_append];cases Vl I x<;>rfl
abbrev pR(D:Dag) (w:Ws) (e:Es) (x r y:Nat):=y<10/\qW (F x) (F y)/\V1 D (F x) r/\w (F x) r=V7 e (F x) (F y)
section Pin
variable {D:Dag} {k I x r:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} (L:V0 D k I w e br o)
include L
lemma B6(f:x<10)(h:kB I x=false)(i:r<(ub I x).length):pR D w e x r (ub I x)[r]:=by have hp:r<(V6 I e (F x)).length:=by{rw[xl I f,Vp];exact i};have hn:=L.2.2.2.2.2.2.2.2.2.2 (F x) (by rw[nB f h];decide) r hp;have j:(ub I x)[r]∈Vn x:=(List.mem_append.1 (List.getElem_mem i)).elim (λ d=>(lF.1 d).1) (λ d=>(lF.1 (List.mem_of_mem_take d)).1);have m:F (ub I x)[r]∈(Vn x).map F:=Vo.2 ⟨_,j,rfl⟩;have h3:=Am (F x);simp only[Fin.val_ofNat,mo f] at h3;rw[h3,lF] at m;refine⟨Ak f _ j,m.2,hn.1,hn.2.trans ?_⟩;simp only[xl I f,List.getElem_map]
lemma CQ(h:x<10)(d:kB I x=false)(f:r<(Vm I x).length):pR D w e x r ((Vm I x).getD r 0):=by have hl:r<(ub I x).length:=by{unfold ub;simp;omega};have i:(Vm I x).getD r 0=(ub I x)[r]:=by{rw[List.getD_eq_getElem _ _ f];simp[ub,List.getElem_append_left f]};simpa only[i] using B6 L h d hl
lemma CR(i:x<10)(f:kB I x=false)(h:(Vl I x).isEmpty=false):pR D w e x (Vm I x).length ((Vl I x).getD 0 0):=by cases d:Vl I x with|nil=>{simp[d] at h}|cons y m=>{have hl:(Vm I x).length<(ub I x).length:=by{unfold ub;rw[d];simp};have j:(ub I x)[(Vm I x).length]=y:=(by simp[ub,d]);simpa only[j,List.getD_cons_zero] using B6 L i f hl}
end Pin
abbrev QT t d:=let v:=yA t d;v.1<14/\v.2.1<10/\v.2.2<10/\¬qW (F v.2.1) (F v.2.2)
lemma qT{t d}(h:vTr t d=true):QT t d:=by simp only[vTr,Rup.vTr,sA,sD,sB,sC] at h;obtain⟨_,a,b,c,d⟩:=h;exact⟨a,b,c,λ q=>by rw[(zV b c).2 q] at d;cases d⟩
lemma qC{t c d}(h:vCx t c d=true):let u:=qY c d;u.1<16/\u.2.1<14/\u.2.2<10/\QT t u.1:=by simp only[vCx,Rup.vCx,sA,sD,sC] at h;exact⟨a4 _,h.2.2.1,h.2.2.2,qT h.2.1⟩
omit [GIdx gi] in lemma qM{b a}(h:yR b a=true):a<6/\(uZ b a).1<14/\(uZ b a).2.1.testBit (uZ b a).1=true:=by simp only[yR,sA,sD,sC] at h;exact⟨h.2.1,h.2.2.1,h.2.2.2⟩
section Sound
variable {D:Dag} {k I P N:Nat} {w:Ws} {e:Es} {br:V->Nat} {o:Os k} {U X Y:LN} (H:Vd 10 D) (A:uz 10 qW D) (K:k<=3) (Q:kM I=Ve 10 D) (L:V0 D k I w e br o) (M:BT D P) (S:Cv D e o N)
abbrev H0 D w e U X Y {k} (o:Os k):=Holds (zM D w e U X Y o)
lemma cN{x}(d:x<10){j}(f:j<qX k I (F x)):j<kk k I x:=by rw[AH k I d];exact f
abbrev Lc(L:V0 D k I w e br o):=L.2.2.2.2.2.1
abbrev Li(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.1
abbrev Lw(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.1
abbrev Le(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.1
abbrev Lp(L:V0 D k I w e br o):=L.2.2.2.2.2.2.2.2.2.2
lemma zX{z l a}(h:qA D w (F z) l (kT (J a))\/qA D w (F z) l (kU (J a)))(hz:z<10:=by first|assumption|omega)(hl:l<5:=by first|assumption|omega)(ha:a<14:=by first|assumption|omega):H0 D w e U X Y o [(kD z l (ep0N a),true),(kD z l (ep1N a),true)]:=jT λ n=>h.elim (λ j=>absurd ((v2 ⟨hz,hl,xH ha⟩).2 (by rw[xU ha];exact j)) n) (λ i=>R ((v2 ⟨hz,hl,xG ha⟩).2 (by rw[xT ha];exact i)))
variable {g r:Nat}
include H A K Q L M S

omit M S in lemma z0 (_:g<16)(q:en0 k I g r=true):H0 D w e U X Y o (ex0 k I g r):=by
  interval_cases g<;>(simp only[ex0,en0,Rup.ex0,Rup.en0,sA,sD,sQ,sN,sB,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · apply G;intro i;have d:=(B7 K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=CB H A L (F _) _ _ d (T v0 i);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩
  · exact c3 v3 v3 v4 CM
  · have:=c5 q.2.2.2.2.2;apply xW;intro d m j;apply jT;intro i;rcases CF H A L Q (xS q.1 q.2.2.1 q.2.2.2.1.symm) (nB q.1 q.2.1) q.2.2.2.2.1 (T v0 m) (T v4 d) with p|n|⟨t,h,f⟩;{exact absurd (W v1 p) j};{exact absurd (W v1 n) i};{exact jG ⟨t.1,t.2,W v5 ⟨h,f⟩⟩}
  · have ⟨j,i,h,d⟩:=Dh H A L (F _) (Vj ((r>>>4)&&&15)) (Dv q.2.1) (Du q.1 q.2.1 q.2.2.2);have f:=cN q.1 i;exact jG ⟨j,f,(y4 ⟨q.1,q.2.1,(c5 f)⟩).2 ⟨h,d⟩⟩
  · exact cb v3 v3 (Cb L q (F 9) (λ y d=>by have:=y.2;simp at d;omega))
omit Q M S in lemma z1 (_:16<=g)(_:g<32)(q:en0 k I g r=true):H0 D w e U X Y o (ex0 k I g r):=by
  interval_cases g<;>(simp only[ex0,en0,Rup.ex0,Rup.en0,sA,sD,sQ,sN,sB,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · exact jQ λ d=>W v6 λ v h=>by{have f:v=F 9:=Fin.ext (by have:=v.2;simp;omega);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))}
  · exact j3 λ d h=>W v3 (Cb L q.1 (F _) (λ y f=>T v6 d y (by rw[xZ (by omega)] at f;omega)) (T v3 h))
  · apply G;intro i;exact jQ λ d=>W v6 λ v j=>by{by_cases h:v.1=((r>>>3)&&&15);{have f:v=F ((r>>>3)&&&15):=Fin.ext (by rw[xZ (by omega)];exact h);rw[f];exact (v3).symm.trans (d.trans (v3 ⟨(by omega),(by omega)⟩))};{exact T v6 i v (by omega)}}
  · apply BA;intro i j;have d:=(B7 K q.2.2.2.1).trans q.2.2.2.2;have ⟨t,h,f⟩:=De H A L (F _) _ _ d (T v7 i) (T v0 j);exact jM K q.1 ⟨t,(mF.1 h).2,f⟩
  · apply zT;intro d m;have ⟨j,p,f,i⟩:=CE H A L (T v3 d) (λ n=>m (W v7 n)) (vR ((r>>>3)&&&63)).2;have h:=cN q.2.1 p;exact⟨(xQ (r&&&7) (vR ((r>>>3)&&&63)).1 j,true),Vo.2 ⟨j,lF.2 ⟨lR.2 h,by simp[f]⟩,rfl⟩,bt.2 ((v8 ⟨(by omega),q.2.1,(c5 h)⟩).2 i)⟩
  · have:=c5 q.2.1;exact G λ _=>j3 λ f d=>W v7 (Cc H.1 L (T v1 f) (T v2 d))
  · have u:=c5 q.2.1;apply xW;intro j f h;have ⟨l,p,i,m⟩:=CC H.1 L (T v1 f) (λ n=>h (W v2 n));have d:=cN q.2.2.1 p;exact jG ⟨l,d,(y9 ⟨q.1,u,q.2.2.1,(c5 d)⟩).2 ⟨T v0 j,i,m⟩⟩
  · have u:=c5 q.2.1;apply xW;intro j d h;have ⟨l,p,i,n⟩:=CT H.1 L (T v2 d) (λ m=>h (W v1 m));have f:=cN q.2.2.1 p;exact jG ⟨l,f,(x0 ⟨q.1,u,q.2.2.1,(c5 f)⟩).2 ⟨T v0 j,i,n⟩⟩
omit S in lemma z2 (_:32<=g)(_:g<48)(q:en1 k I P g r=true):H0 D w e U X Y o (ex1 k I g r):=by
  have hE:=Le L;interval_cases g<;>(simp only[ex1,en1,Rup.ex1,Rup.en1,sA,sD,sQ,sB,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · have ⟨h1,h2,h,z,h5,h6⟩:=q;have:=c5 h6;have f:(r&&&15)≠((r>>>4)&&&15):=λ p=>by{rw[p,z] at h2;exact Bool.noConfusion h2};apply BA;intro n m;exact Z λ j i=>by{have v:=V3 H A L Q (xS h1 h f) (iB h z) (T v2 j);have u:=V3 H A L Q (xS h1 h f) (iB h z) (T v2 i);have d:=congrArg Vg (v.trans u.symm);rw[Vh,Vh] at d;have a0:=Li L (F (r&&&15)) _ _ (T v0 n) (T v0 m) d;omega}
  · have ⟨h1,n,h3,h4,_,h6,h3lt,h7⟩:=q;have a3:vD 10 D=0:=by{rw[h1] at M;exact M};have ⟨f,d,i⟩:=Ca n h3lt h7;have v:¬qW (F (r&&&15)) (F ((r>>>4)&&&15)):=λ ha=>by{rw[(zV n h4).2 ha] at h6;exact Bool.noConfusion h6};apply G;intro h;have ⟨l,hl,a2,z,u,m⟩:=Db H A a3 L Q (iB n h3) v d (T v2 h);have j:=cN f hl;have a0:=(A7 n f d).2.2.1;exact jG ⟨l,j,(x1 ⟨n,h4,i,(c5 j)⟩).2 ⟨by rw[a0];exact a2,z,u,λ x2 p=>(m x2 p).1⟩⟩
  · exact j3 λ f d=>W v7 (by{have ⟨j,i,h⟩:=Lw L (kT (J (r&&&15))) (e (J (r&&&15))) (by simpa[wX,x4,Vb] using (hE false (J (r&&&15))).1);exact Cc H.1 L ⟨i,by rw[h];simpa[es,Vb] using T v9 f⟩ ⟨i,by rw[h];simpa[es,Vb,Vg] using T v9 d⟩})
  · let b0:=(r&&&1)==1;let z:=J ((r>>>1)&&&15);let x0:=F ((r>>>5)&&&15);let p0:=Vb b0 (e z);have hs:(r&&&1)<2:=a1 _;apply zT;intro v u;have f:=(hE b0 z).1;have i:=(Vi.1 f).1;have h:x0∉Be 10 D (10+p0.1):=λ n=>u (W v9 (by rw[uX hs];have d:=Bf H.1 i (uU H.1 f) (!p0.2) n;rw[show (p0.1,!p0.2)=Vb (!b0) (e z) by rw[Vc];rfl] at d;exact d));have ⟨j,hj,p⟩:=Lw L x0 _ (Vi.2 ⟨i,T v9 v,h⟩);have m:=cN q.2 (lt_of_lt_of_le hj (Lc L _));exact jG ⟨j,m,(u0 ⟨hs,q.1,q.2,(c5 m)⟩).2 ⟨hj,p⟩⟩
  · have:(r&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact Z λ f d=>by{have ⟨i,m⟩:=T u0 f;have ⟨h,j⟩:=T u0 d;have:=Li L (F _) _ _ i h (m.trans j.symm);omega}
omit H A Q L M S in lemma z3 (_:48<=g)(_:g<64)(q:en1 k I P g r=true):H0 D w e U X Y o (ex1 k I g r):=by
  interval_cases g<;>(simp only[ex1,en1,Rup.ex1,Rup.en1,sA,sD,sQ,sN,sB,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · have i:(r&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact jI λ j=>by{have ⟨d,f⟩:=T u0 j;by_cases h:((r>>>15)&&&1)=1;{simp only[h,sT];refine (v2).trans (Iff.trans ?_ (v9).symm);simp only[qA,es,d,f,<-Vc,<-uX i,true_and]};{simp only[h,sF];refine (v1).trans (Iff.trans ?_ (v9).symm);simp only[uj,es,d,f,true_and]}}
  · have:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ j i=>by{have ⟨f,_,h⟩:=T y9 j;have ⟨_,d⟩:=T u0 i;exact W u0 ⟨f,h.symm.trans d⟩}
  · have j:((r>>>12)&&&1)<2:=a1 _;have:=c5 q.2.1;have:=c5 q.2.2.2.2.2.1;exact j3 λ n m=>by{have ⟨h,_,i⟩:=T x0 n;have ⟨_,f⟩:=T u0 m;have d:=congrArg Vg (i.symm.trans f);rw[Vh] at d;exact W u0 ⟨h,by rw[uX j,Vc];exact d⟩}
  · apply zT;intro d f;rcases uL (T u5 d).symm with i|h;{exact absurd (W u3 i) f};{exact R (W u4 h)}
  · have:((r>>>14)&&&1)<2:=a1 _;have:((r>>>15)&&&1)<2:=a1 _;have:=c5 q.2.2.2;exact j3 λ j i=>by{have d:=(T u0 j).2.symm.trans (T u0 i).2;have h:((r>>>14)&&&1)=0\/((r>>>14)&&&1)=1:=(by omega);have f:((r>>>15)&&&1)=0\/((r>>>15)&&&1)=1:=(by omega);rcases h with h|h<;>rcases f with f|f<;>simp only[h,f] at d ⊢;{exact W u3 (uT false d)};{exact W u4 (by simpa[Vb,Vg] using d)};{exact W u4 (by change Vb true _=Vb false _ at d;rw[Ac,zN] at d;have h'':=congrArg Vg d;rwa[Vh] at h'')};{exact W u3 (uT true d)}}
omit H A Q L M S in lemma z4 (_:64<=g)(_:g<80)(q:en2 k I P g r=true):H0 D w e U X Y o (ex2 k I P g r):=by
  interval_cases g<;>(simp only[ex2,en2,Rup.ex2,Rup.en2,sA,sD,sN,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · apply C4;intro d f;have a:(e (J _)).1≠(e (J _)).1:=λ i=>d (W u5 i);have b:¬(e (J _)).1<(e (J _)).1:=λ h=>f (W u6 h);exact R (W u6 (by unfold V4;omega))
  · exact c3 u6 u6 u6 Nat.lt_trans
  · have:((r>>>10)&&&1)<2:=a1 _;have:=c5 q.2.2.1;exact j3 λ i f=>W u6 (by have h:=(T u7 i).2;have d:=congrArg Prod.fst (T u0 f).2;rw[AT] at d;unfold V4;omega)
omit Q S in lemma z5 (_:80<=g)(_:g<96)(q:en2 k I P g r=true):H0 D w e U X Y o (ex2 k I P g r):=by
  have hE:=Le L;interval_cases g<;>(simp only[ex2,en2,Rup.ex2,Rup.en2,sA,sD,sN,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · apply G;intro h;have ⟨j,p,i,n,m⟩:=Dd H.1 L (T u8 h);have f:j<kk k I (ep0N (r&&&15)):=by{rw[AH k I (xH q),xU q];exact p};have d:i<kk k I (ep1N (r&&&15)):=by{rw[AH k I (xG q),xT q];exact n};exact⟨(yK (r&&&15) j i,true),List.mem_flatMap.2 ⟨j,lR.2 f,Vo.2 ⟨i,lR.2 d,rfl⟩⟩,bt.2 ((u9 ⟨q,(c5 f),(c5 d)⟩).2 m)⟩
  · apply jT;intro f;rcases P with _|_|_|_;{omega};{rcases B2 H A M hE (J _) with d|⟨z,h⟩;{exact absurd (W t2 d) f};{exact jG ⟨z.1,z.2,W t4 (by rw[vL];exact h)⟩}};{exact M.elim};{exact M.elim}
  · exact c3 u5 t2 t2 CY
  · exact c3 u5 t4 t4 CZ
  · have:=c5 q.2.2.2;exact G λ d=>zX (T t5 d).2
  · apply zT;intro j f;have ⟨l,m,h⟩:=CN H A L (T t4 j) (λ i=>f (W u8 i));have d:=cN q.2.2 m;exact jG ⟨l,d,(t5 ⟨q.2.1,q.2.2,(c5 d)⟩).2 h⟩
omit Q M S in lemma z6 (_:96<=g)(_:g<101)(q:en3 k I P N U X Y g r=true):H0 D w e U X Y o (ex3 k I U X Y g r):=by
  have hE:=Le L;have:=a4 r;interval_cases g<;>(simp only[ex3,en3,Rup.ex3,Rup.en3,sA,sD,sQ,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · have ⟨j,n,m,i⟩:=qT q.2;exact j3 λ h f=>W y2 (Dt H A hE i (by{by_cases d:((r>>>4)&&&1)=1;{simp only[d,sT] at h f;exact Or.inr ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩};{simp only[d,sF] at h f;exact Or.inl ⟨T (v9 (s:=0)) h,T (v9 (s:=1)) f⟩}}))
  · have ⟨n,_,_,m⟩:=qT q.2.1;apply xW;intro p i j;rcases Dr H A L m (T y2 p) (T t2 i) with hs|⟨z,h,f,d,l,v,u⟩;{exact absurd (W u8 hs) j};{exact jU n ⟨z,h,f,d,l,v,(t1 ⟨q.2.2,z.2,(Ct v)⟩).2 (by rw[vL];exact u)⟩}
omit Q M S in lemma z7 (_:101<=g)(_:g<108)(q:en3 k I P N U X Y g r=true):H0 D w e U X Y o (ex3 k I U X Y g r):=by
  have:=a6 r;interval_cases g<;>(simp only[ex3,en3,Rup.ex3,Rup.en3,sA,sD,sN,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · have ⟨b8,h,j,a9,_,_,a3⟩:=qC q.2;apply BA;intro b6 a2;rcases Ds H A L a3 (T y2 b6) (T t4 a2) with hs|⟨z,a0,v,u,l,p,b7⟩|⟨b5,b4,a7⟩|⟨l,p,a8⟩|⟨n,a5,f⟩;{exact jL (jL (jL (jR (R (W u8 hs)))))};{exact jL (jL (jL (jL (jU a9 ⟨z,a0,v,u,l,p,(t1 ⟨h,z.2,(Ct p)⟩).2 (by rw[vL];exact b7)⟩))))};{apply jL;apply jL;apply jR;split_ifs with i;{exact R (W v7 a7)};{exact absurd ⟨λ m=>b5 (by rw[m]),λ m=>b4 (by rw[m])⟩ i}};{have d:=cN j p;have:=c5 d;exact jL (jR (C5 ⟨l,d,a8.imp (y5 ⟨(a6 r),(c5 d)⟩).2 (t0 ⟨h,j,(c5 d)⟩).2⟩))};{have hne':n.1≠(qY X (r&&&63)).2.1:=λ m=>a5 (by rw[<-yP n,m]);exact jR ⟨(vA (r&&&63) n.1,true),Vo.2 ⟨n.1,lF.2 ⟨lR.2 n.2,by simp[hne']⟩,rfl⟩,bt.2 (W y6 (by rw[yP];exact f))⟩}
  · have ⟨_,_,i,_,_,_,_⟩:=qC q.2.1;apply zT;intro h j;rcases (T y6 h).2.1 with f|d;{exact absurd (W (v9 (s:=0)) f) j};{exact R (W (v9 (s:=1)) d)}
omit Q S in lemma z8 (_:108<=g)(_:g<115)(q:en3 k I P N U X Y g r=true):H0 D w e U X Y o (ex3 k I U X Y g r):=by
  interval_cases g<;>(simp only[ex3,en3,Rup.ex3,Rup.en3,sA,sD,sQ,sC] at q ⊢;try exact Bool.noConfusion q)
  · have ⟨hm1,hvm⟩:=q;subst hm1;have ⟨ha6,hd14,hdbit⟩:=qM hvm;by_contra hnh;have hns:¬Cg D e (J (uZ Y (r&&&7)).1):=λ hs=>hnh ⟨_,List.mem_cons_self ..,bt.2 (W (u8 hd14) hs)⟩;have hstay:∀e0:Ei,(uZ Y (r&&&7)).2.1.testBit e0.1=true->¬BZ D (10+(e e0).1):=λ e0 he0 hs=>hnh ⟨(zD e0.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_self ..⟩)),bt.2 (W (t2 e0.2) (by rwa[yP]))⟩;have hpick:∀e0:Ei,(uZ Y (r&&&7)).2.1.testBit e0.1=true->∀z:V,(uZ Y (r&&&7)).2.2.testBit z.1=false->¬B4 D (10+(e e0).1) z:=λ e0 he0 z hz hp=>hnh ⟨(wM e0.1 z.1,true),List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨e0.1,lF.2 ⟨lR.2 e0.2,he0⟩,List.mem_cons_of_mem _ (Vo.2 ⟨z.1,lF.2 ⟨lR.2 z.2,by simp[hz]⟩,rfl⟩)⟩)),bt.2 (W (t4 ⟨e0.2,z.2⟩) (by rwa[yP,vL]))⟩;have hfree:∀z:V,(uZ Y (r&&&7)).2.2.testBit z.1=true->∀l<qX k I z,¬BF D w e z l:=λ z hz l hl hf=>by{have hlN:l<kk k I z.1:=cN z.2 (by rwa[vL]);exact hnh ⟨(uO z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_self ..⟩⟩)),bt.2 (W (u1 ⟨z.2,c5 hlN⟩) (by rwa[vL]))⟩};have hopp:∀z:V,(uZ Y (r&&&7)).2.2.testBit z.1=true->∀l<qX k I z,∀y:V,(uZ Y (r&&&7)).2.2.testBit y.1=true->¬qA D w z l y:=λ z hz l hl y hy ho=>by{have hlN:l<kk k I z.1:=cN z.2 (by rwa[vL]);exact hnh ⟨(kD z.1 l y.1,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (Vo.2 ⟨y.1,lF.2 ⟨lR.2 y.2,hy⟩,rfl⟩))⟩⟩)),bt.2 (W (v2 ⟨z.2,c5 hlN,y.2⟩) (by rwa[vL,vL]))⟩};have hesc:∀z:V,(uZ Y (r&&&7)).2.2.testBit z.1=true->∀l<qX k I z,¬uE D w e (J (uZ Y (r&&&7)).1) (uZ Y (r&&&7)).2.1 z l:=λ z hz l hl hm=>by{have hlN:l<kk k I z.1:=cN z.2 (by rwa[vL]);exact hnh ⟨(zE (r&&&7) z.1 l,true),List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨z.1,lF.2 ⟨lR.2 z.2,hz⟩,List.mem_flatMap.2 ⟨l,lR.2 hlN,List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩)),bt.2 (W (y7 ⟨ha6,z.2,c5 hlN⟩) (by rwa[vL]))⟩};exact C0 H A M L (by rwa[Fin.val_ofNat,mo hd14]) hns hstay hpick hfree hopp hesc
  · have ⟨_,hvm,hz,hl⟩:=q;have ⟨ha6,_,_⟩:=qM hvm;have hl5:=c5 hl;apply G;intro hm;obtain⟨_,e',he',s,hra⟩:=T (y7 ⟨ha6,hz,hl5⟩) hm;cases s;{exact⟨(ur 0 e'.1 (vR ((r>>>3)&&&63)).1 (vR ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[yP] using hra))⟩};{exact⟨(ur 1 e'.1 (vR ((r>>>3)&&&63)).1 (vR ((r>>>3)&&&63)).2,true),List.mem_flatMap.2 ⟨e'.1,lF.2 ⟨lR.2 e'.2,he'⟩,by simp⟩,bt.2 (W (u0 ⟨by omega,e'.2,hz,hl5⟩) (by simpa[yP] using hra))⟩}
omit Q M S in lemma za (_:115<=g)(_:g<128)(q:en3 k I P N U X Y g r=true):H0 D w e U X Y o (ex3 k I U X Y g r):=by
  interval_cases g<;>(simp only[ex3,en3,Rup.ex3,Rup.en3,sA,sD,sQ,sB,sC] at q ⊢;first|exact Bool.noConfusion q|(have q_:=q;repeat have ⟨_,q_⟩:=(q_:_/\_)))
  · apply G;intro i;rcases Dp H A L (T v4 i) with ⟨j,n,d⟩|⟨l,m,d⟩;{have h:=cN (by omega) n;exact jL (jG ⟨j,h,(v1 ⟨(by omega),(c5 h),q.2.1⟩).2 d⟩)};{have f:=cN q.2.1 m;exact jR (jG ⟨l,f,(v1 ⟨q.2.1,(c5 f),(by omega)⟩).2 d⟩)}
  · have ⟨hx,hni,hp,hy1,hy2,hjc⟩:=q;have hj5:=c5 hjc;have ht1:(if ((r>>>4)&&&3)=2 then 1 else 0)<3:=(by split_ifs<;>omega);have ht2:(if ((r>>>4)&&&3)=0 then 1 else 2)<3:=(by split_ifs<;>omega);exact jT λ hm=>G λ c1=>G λ c2=>G λ h1=>jT λ hn2=>G λ h2=>jT λ hn1=>G λ hj=>jT λ hr1=>jT λ hr2=>by{have h5:=CL H A L (T v3 c1) (T v3 c2) (T v3 h1) (λ u=>hn2 (W v3 u)) (T v3 h2) (λ u=>hn1 (W v3 u)) (λ u=>hm (W v7 u)) (T v0 hj) (λ u=>hr1 (W v8 u)) (λ u=>hr2 (W v8 u));split_ifs with hk;{exact R (W v0 (by show 4<fF D (F (r&&&15));omega))};{have hc:=L.2.2.2.2.2.1 (F (r&&&15));unfold qX at hc;rw[xZ hx] at hc;dsimp only[R1.B,kB] at hni;rw[hni] at hc;simp only[Bool.false_eq_true,ite_false] at hc;omega}}
omit S in lemma zS(c:Nat)(q:enS k I P N U X Y c=true):H0 D w e U X Y o (expS k I P U X Y c):=by
  unfold expS Rup.expS Rup.exS;unfold enS Rup.enS Rup.enabled at q;dsimp only at q ⊢;have d:c&&&127<128:=aM 7 c;generalize c&&&127=g at d q ⊢
  split_ifs at q ⊢ with a b e
  · exact if f:g<16 then z0 H A K Q L f q else z1 H A K L (by omega) b q
  · exact if f:g<48 then z2 H A K Q L M (by omega) f q else z3 K (by omega) a q
  · exact if f:g<80 then z4 K (by omega) f q else z5 H A K L M (by omega) e q
  · exact if f:g<101 then z6 H A K L (by omega) f q else if f:g<108 then z7 H A K L (by omega) f q else if f:g<115 then z8 H A K L M (by omega) f q else za H A K L (by omega) d q
omit H A K Q L M S in lemma wP {p q:Prop}(h:p↔q):bP p=bP q:=by simp only[bP];congr 1;exact propext h
omit M S in lemma vI:OOK gi k I P U X Y (zM D w e U X Y o):=by
  have hE:=Le L
  refine⟨K,
    (λ a ha=>bt.2 (W (v0 ⟨ha,by omega⟩) (By H.1 A (F a)))),
    (λ a j ha hj h=>by have:=c5 hj;exact bt.2 (W v1 (Cz L (T v0 (bt.1 h))))),
    (λ a j ha hj h=>by have:=c5 hj;exact bt.2 (W v0 (Nat.lt_of_succ_lt (T v0 (bt.1 h))))),
    (λ a j y ha hj hy h=>by have:=c5 hj;exact bt.2 (W v0 (C1 (T v1 (bt.1 h))))),
    (λ a j y ha hj hy h=>by have:=c5 hj;exact bt.2 (W v4 (C2 L (T v1 (bt.1 h))))),
    (λ a t0 ha hi ht=>bf.2 λ h=>Da L Q (iB ha hi) (T v3 h)),
    (λ a y hay hy hi=>bf.2 λ h=>hi.elim (λ ha=>Cs H.1 A (Aq Q (by omega) ha) (xS (by omega) hy (by omega)) (T v4 h)) (λ hiy=>Cs H.1 A (Aq Q hy hiy) (xS hy (by omega) (by omega)) (let ⟨z,p,q⟩:=T v4 h;⟨z,q,p⟩))),
    (λ i y z hi hii hyz hz hiy hiz=>bt.2 (W v4 (Dw H A (Aq Q hi hii) ((zV hi (by omega)).1 hiy) ((zV hi hz).1 hiz)))),
    (λ t0 a y ht ha hy _ h=>by have hd:=T v5 (bt.1 h);exact⟨bt.2 (W v3 hd.1),bf.2 λ q=>hd.2 (T v3 q)⟩),
    (λ a c0 j ha hc hj h=>by have:=c5 hj;have hv:=T y4 (bt.1 h);exact⟨bt.2 (W v0 hv.1),fun y hy htb=>bf.2 λ q=>hv.2 (F y) (mF.2 ⟨mU _,by rw[xZ hy];exact htb⟩) (T v1 q)⟩),
    (λ a ha hi=>bf.2 λ h=>AB H A (Aq Q ha hi) (T v7 h)),
    (λ a ha _ h=>bf.2 λ q=>Dc H A L (F a) (T v7 (bt.1 h)) (T v0 q)),
    (λ t0 a j ht ha _ hj h=>by have:=c5 hj;have hr:=T v8 (bt.1 h);exact⟨bt.2 (W v0 hr.1),fun y hy hr'=>bt.2 (W v1 (hr.2 (F y) (T v3 (bt.1 hr'))))⟩),
    (λ a j ha hj=>by have:=c5 hj;exact bf.2 λ h=>B8 H.1 L (F a) j (T v2 h)),
    (λ a j y ha hj hy h=>by have:=c5 hj;exact bt.2 (W v0 (T v2 (bt.1 h)).1)),
    (λ a j y ha hj hy hiy hne h=>by
      have hj5:=c5 hj;have ho:=T v2 (bt.1 h)
      refine⟨bf.2 λ hf=>C7 H A L Q (xS ha hy hne) (iB hy hiy) ho (T u1 hf),
        λ d hd hdy=>bf.2 λ h2=>by have hi:=Bi uG H.1 A (Aq Q hy hiy) ho.2;have h2':=(T v2 h2).2;rw[hi,Finset.mem_singleton] at h2';exact xS hd hy hdy h2',
        λ d hd=>wP (by have hbar:=V3 H A L Q (xS ha hy hne) (iB hy hiy) ho;have hd':=congrArg Vg hbar.symm;rw[Vh] at hd';have hl0:=By H.1 A (F y);refine (v1 ⟨ha,hj5,hd⟩).trans (Iff.trans ?_ (v2 ⟨hy,by omega,hd⟩).symm);simp only[uj,qA,ho.1,hl0,hd',true_and])⟩),
    (λ a y ha hi hy=>⟨fun had=>bt.2 (W v2 ⟨By H.1 A (F a),(A4 H A L Q (iB ha hi)).2 (F y) ((zV ha hy).1 had)⟩),fun hiy hne=>bf.2 λ h=>C8 H A L Q (iB ha hi) (iB hy hiy) (xS ha hy hne) (T v2 h)⟩),
    (λ s e hs he=>⟨bt.2 ((v9 ⟨hs,he,Cl he⟩).2 (by rw[Ck hs he];exact (Vi.1 (hE _ (J e)).1).2.1)),bf.2 λ h=>by have h':=(v9 ⟨hs,he,Cl he⟩).1 h;rw[Ck (by omega) he,uX hs] at h';exact (hE _ (J e)).2 h'⟩),
    (λ s e a j hs he ha hj h=>by
      have hj5:=c5 hj;have hra:=T (u0 ⟨hs,he,ha,hj5⟩) (bt.1 h)
      refine⟨bt.2 (W v0 hra.1),bt.2 (W (v9 ⟨hs,he,ha⟩) (by rw[es,←hra.2];exact (Vi.1 (L.2.2.2.2.2.2.1 _ _)).2.1)),
        bf.2 (λ q=>by have i:=T (v9 ⟨by omega,he,ha⟩) q;rw[uX hs,es,Vc,←hra.2] at i;exact B8 H.1 L (F a) j ⟨hra.1,i⟩),
        bf.2 (λ hf=>(T u1 hf).2 (J e) _ hra.2),
        bf.2 (λ haf=>by have h1:=(T u7 haf).2;have h2:=congrArg Prod.fst hra.2;rw[AT] at h2;omega),
        λ y hy=>wP ((v1 ⟨ha,hj5,hy⟩).trans (Iff.trans (by simp only[uj,es,hra.1,hra.2,true_and]) (v9 ⟨hs,he,hy⟩).symm)),
        λ y hy=>wP ((v2 ⟨ha,hj5,hy⟩).trans (Iff.trans (by simp only[qA,es,hra.1,hra.2,←Vc,←uX hs,true_and]) (v9 (s:=1-s) ⟨by omega,he,hy⟩).symm))⟩),
    (λ a ha hni=>⟨
      λ h0 hh hhc=>by have:=c5 hhc;have d:h0<(V6 I e (F a)).length:=(by rw[CP ha];exact hh);exact bt.2 (W v0 (Lp L (F a) (by rw[nB ha hni];decide) h0 d).1),
      λ h0 hh hhc=>by have:=c5 hhc;have ⟨hy,had,hl,hw⟩:=CQ L ha hni hh;have ⟨pe,ps,hj,hi⟩:=A7 ha hy had;exact⟨bt.2 (W v2 ⟨hl,by rw[hw];exact (Vi.1 (Ae hE had).2).2.1⟩),bt.2 (W (u0 ⟨ps,pe,ha,this⟩) ⟨hl,by rw[hw,V7,hj,hi]⟩)⟩,
      λ hne hhc=>by have:=c5 hhc;have ⟨hy,had,hl,hw⟩:=CR L ha hni hne;have ⟨pe,ps,hj,hi⟩:=A7 ha hy had;exact bt.2 (W (u0 ⟨ps,pe,ha,this⟩) ⟨hl,by rw[hw,V7,hj,hi]⟩)⟩),
    (λ a j ha hj=>by have:=c5 hj;exact⟨fun h=>bt.2 (W v0 (T u1 (bt.1 h)).1),fun h=>by have he:=T u2 (bt.1 h);exact⟨bt.2 (W v0 he.1),fun y hy=>bf.2 λ ho=>by have d:=(T v2 ho).2;rw[he.2] at d;exact Finset.notMem_empty _ d⟩⟩),
    (λ b a hba ha=>⟨
      λ h=>by have hg:=T u3 (bt.1 h);exact⟨bt.2 (W u5 (congrArg Prod.fst hg)),fun y hy=>wP ((v9 (s:=0) ⟨by omega,by omega,hy⟩).trans (by unfold es;rw[hg];exact (v9 (s:=0) ⟨by omega,ha,hy⟩).symm)),fun y hy=>wP ((v9 (s:=1) ⟨by omega,by omega,hy⟩).trans (by unfold es;rw[hg];exact (v9 (s:=1) ⟨by omega,ha,hy⟩).symm))⟩,
      λ h=>by have hg:=T u4 (bt.1 h);exact⟨bt.2 (W u5 (by unfold uc;rw[hg];rfl)),fun y hy=>wP ((v9 (s:=0) ⟨by omega,by omega,hy⟩).trans (by unfold es;rw[hg,BW];exact (v9 (s:=1) ⟨by omega,ha,hy⟩).symm)),fun y hy=>wP ((v9 (s:=1) ⟨by omega,by omega,hy⟩).trans (by unfold es;rw[hg,BW];exact (v9 (s:=0) ⟨by omega,ha,hy⟩).symm))⟩⟩),
    (λ b a hb ha hne=>⟨
      λ h=>bf.2 λ hlt=>by have h1:=T u5 (bt.1 h);have h2:=T u6 hlt;unfold uc at h1;unfold V4 at h2;omega,
      λ h=>by have h1:=T u6 (bt.1 h);exact⟨bf.2 λ h2=>by have h2':=T u6 h2;unfold V4 at h1 h2';omega,bf.2 λ h2=>by have h2':=T u5 h2;unfold uc at h2';unfold V4 at h1;omega⟩⟩),
    (λ e a j he ha hj=>by
      have:=c5 hj
      exact⟨fun h=>by have ha':=T u7 (bt.1 h);exact⟨bt.2 (W v0 ha'.1),bf.2 λ hr=>by have d:=congrArg Prod.fst (T (u0 ⟨by omega,he,ha,this⟩) hr).2;rw[AT] at d;have:=ha'.2;omega,bf.2 λ hr=>by have d:=congrArg Prod.fst (T (u0 ⟨by omega,he,ha,this⟩) hr).2;rw[AT] at d;have:=ha'.2;omega⟩,
        λ h=>by have hf:=T t0 (bt.1 h);exact⟨bt.2 (W u7 hf.1),bt.2 (W u1 hf.2)⟩,
        λ h=>by have he':=T t1 (bt.1 h);exact⟨bt.2 (W u7 he'.1),bt.2 (W u2 he'.2)⟩⟩),
    (λ e b a he hb ha h=>by
      have hb5:=c5 hb;have ha5:=c5 ha;have hs:=T u9 (bt.1 h)
      exact⟨bt.2 ((v0 ⟨xH he,hb5⟩).2 (by rw[xU he];exact hs.1)),bt.2 ((v0 ⟨xG he,ha5⟩).2 (by rw[xT he];exact hs.2.1)),
        bf.2 λ hr=>CV hs (by rw[←xU he];exact (u0 ⟨by omega,he,xH he,hb5⟩).1 hr),
        bf.2 λ hr=>CU hs (by rw[←xT he];exact (u0 ⟨by omega,he,xG he,ha5⟩).1 hr),
        λ y hy=>wP ((v1 ⟨xH he,hb5,hy⟩).trans (by rw[xU he,(BY hs (F y)).2,←xT he];exact (v2 ⟨xG he,ha5,hy⟩).symm)),
        λ y hy=>wP ((v1 ⟨xG he,ha5,hy⟩).trans (by rw[xT he,(BY hs (F y)).1,←xU he];exact (v2 ⟨xH he,hb5,hy⟩).symm))⟩),
    (λ _=>⟨
      λ e z z2 he hz hz2 hne h=>bf.2 λ h2=>xS hz hz2 hne (CO H.1 (T t4 (bt.1 h)) (T t4 h2)),
      λ e z l0 he hz hl h=>by have hl5:=c5 hl;have hh:=T t5 (bt.1 h);exact⟨bt.2 (W u7 hh.1),hh.2.elim (λ h0=>Or.inl (bt.2 ((v2 ⟨hz,hl5,xH he⟩).2 (by rw[xU he];exact h0)))) (λ h1=>Or.inr (bt.2 ((v2 ⟨hz,hl5,xG he⟩).2 (by rw[xT he];exact h1))))⟩⟩),
    (λ _ u hu hvc=>by
      have ⟨hcu1,he1,hx2,htr1,htr2,htr3,_⟩:=qC hvc
      exact⟨fun l0 hl h=>by have hl5:=c5 hl;have hf:=T (y5 ⟨hu,hl5⟩) (bt.1 h);exact⟨bt.2 (W (u7 ⟨he1,hx2,hl5⟩) hf.1),bf.2 λ ho=>hf.2.1 (T (v2 ⟨hx2,hl5,htr2⟩) ho),bf.2 λ ho=>hf.2.2.1 (T (v2 ⟨hx2,hl5,htr3⟩) ho),hf.2.2.2.elim (λ h0=>Or.inl (bt.2 ((v2 ⟨hx2,hl5,xH htr1⟩).2 (by rw[xU htr1];exact h0)))) (λ h1=>Or.inr (bt.2 ((v2 ⟨hx2,hl5,xG htr1⟩).2 (by rw[xT htr1];exact h1))))⟩,
        λ e2 he2 _ h=>by have hs:=T (y6 ⟨hu,he2⟩) (bt.1 h);exact⟨bt.2 (W (u6 ⟨he1,he2⟩) hs.1),bt.2 (W (y2 ⟨hcu1,he2⟩) hs.2.2),hs.2.1.elim (λ h0=>Or.inl (bt.2 (W (v9 ⟨by omega,he2,hx2⟩) h0))) (λ h1=>Or.inr (bt.2 (W (v9 ⟨by omega,he2,hx2⟩) h1)))⟩⟩),
    (λ _ a hvm z l0 hz hl h=>by have ⟨ha6,hd14,_⟩:=qM hvm;have hl5:=c5 hl;have hm:=T (y7 ⟨ha6,hz,hl5⟩) (bt.1 h);exact hm.1.elim (λ h0=>Or.inl (bt.2 ((v2 ⟨hz,hl5,xH hd14⟩).2 (by rw[xU hd14];exact h0)))) (λ h1=>Or.inr (bt.2 ((v2 ⟨hz,hl5,xG hd14⟩).2 (by rw[xT hd14];exact h1))))),
    (λ a j y l0 ha hj hy _ _ hl=>by
      have hj5:=c5 hj;have hl5:=c5 hl
      exact⟨fun h=>by have ⟨f1,f2,f3⟩:=T y9 (bt.1 h);exact⟨bt.2 (W v0 f2),fun d hd=>wP ((v1 ⟨ha,hj5,hd⟩).trans (Iff.trans (by simp only[uj,f1,f2,f3,true_and]) (v1 ⟨hy,hl5,hd⟩).symm)),fun d hd=>wP ((v2 ⟨ha,hj5,hd⟩).trans (Iff.trans (by simp only[qA,f1,f2,f3,true_and]) (v2 ⟨hy,hl5,hd⟩).symm))⟩,
        λ h=>by have ⟨f1,f2,f3⟩:=T x0 (bt.1 h);exact⟨bt.2 (W v0 f2),fun d hd=>wP ((v1 ⟨ha,hj5,hd⟩).trans (Iff.trans (by simp only[uj,qA,f1,f2,f3,Vh,true_and]) (v2 ⟨hy,hl5,hd⟩).symm)),fun d hd=>wP ((v2 ⟨ha,hj5,hd⟩).trans (Iff.trans (by simp only[uj,qA,f1,f2,f3,true_and]) (v1 ⟨hy,hl5,hd⟩).symm))⟩⟩),
    (λ _ i y n l0 hi _ hy _ _ hn3 hnlen hl h=>by
      have ⟨hx10,had,_⟩:=Ca hi hn3 hnlen;have hl5:=c5 hl;have hf:=T x1 (bt.1 h)
      exact⟨bt.2 ((t1 ⟨(A7 hi hx10 had).1,hx10,hl5⟩).2 hf.1),bt.2 (W u1 hf.2.1),bf.2 λ q=>hf.2.2.1 (T v1 q),fun d hd had2=>bt.2 (W v1 (hf.2.2.2 (F d) ((zV hi hd).1 had2)))⟩)⟩

end Sound
section K
variable {D:Dag} {k I mode sym:Nat} {b:V->Nat} {e:Es}
abbrev Gk D k I m b e:=Vd 10 D/\uz 10 qW D/\k<=3/\kM I=Ve 10 D/\B5 10 D b/\(Vf 10 D b).card<=k/\Df D e/\BT D m
lemma kC(p:CK k I mode sym)(g:Gk D k I mode b e)(_j:∀w o,V0 D k I w e b o->Cv D e o sym):False:=by obtain⟨h,d,f,q,i,m,v,n⟩:=g;obtain⟨w,o,L⟩:=Do h d q i m v;obtain⟨t,c,x,u⟩:=p;exact u (zM D w e t c x o) (zS h d f q L n) (vI h d f q L)
abbrev k0(hK:CK k I mode 0) (g:Gk D k I mode b e):=kC hK g λ _ _ _=>trivial
end K
end P3G
end P3
section MainSec
open DagTools P3 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
structure CD where
  p:Nat
  t:List Nat
  c:List Nat
  x:List Nat
  bw:List Nat
  dw:List Nat
  h:Nat
def c0 (p:Nat)(bw dw:List Nat)(h:Nat):CD:=⟨p,[],[],[],bw,dw,h⟩
def c2 (p:Nat)(bw:List Nat)(dw h:Nat):CD:=⟨p,[],[],[],bw,[dw],h⟩
def c5 (p b dw h:Nat):CD:=⟨p,[],[],[],[b],[dw],h⟩
def c6 (p b h:Nat):CD:=⟨p,[],[],[],[b],[],h⟩
def c1 (p:Nat)(t c x bw dw:List Nat)(h:Nat):CD:=⟨p,t,c,x,bw,dw,h⟩
def c4 (p:Nat)(t c x bw:List Nat)(dw h:Nat):CD:=⟨p,t,c,x,bw,[dw],h⟩
def Cq (d:CD):=d.p&&&3
def Cp (d:CD):=(d.p>>>2)&&&1
def Dn (d:CD):=((d.p>>>3)&&&15)+1
def Cr (d:CD):=(d.p>>>7)&&&1023
def Dm (d:CD):=(d.p>>>17)&&&4095
def Dl (d:CD):=d.p>>>29
def cdKey (d:CD):Nat×Nat×Nat:=(Cq d,Cr d,Cp d)
def BN (n:Nat):Nat:=if n<=2 then 1 else if n<=4 then 2 else if n<=8 then 3 else if n<=16 then 4 else if n<=32 then 5 else if n<=64 then 6 else if n<=128 then 7 else if n<=256 then 8 else if n<=512 then 9 else 10
def CW (l:List Nat)(i:Nat):Nat:=l.getD i 0
def CX (ab:Nat)(l:List Nat):Nat->Rup.q0:=Rup.gdc ab 16 (l.getD · 0)
def AG (gi:Fin 4)(d:CD):Bool:=let nb:=Dm d;let nd:=Dl d;Rup.qt gi (Cq d) (Cr d) (Cp d) d.t d.c d.x (CW d.bw) (CX (Dn d) d.dw) nb nd (BN (nb+nd)) d.h
def chkL (gi:Fin 4)(ds:List CD):Bool:=ds.all (AG gi)
lemma chkL_sound {gi:Fin 4}{ds:List CD}(h:chkL gi ds=true):∀e∈ds.map cdKey,CellKill gi e.1 e.2.1 e.2.2 0:=by
  intro e he;obtain⟨d,hd,rfl⟩:=List.mem_map.mp he;exact⟨d.t,d.c,d.x,Rup.sc _ _ _ _ _ _ (List.all_eq_true.mp h d hd)⟩
def vH (I:Nat):Nat:=((List.finRange 10).filter (λ v:V=>I.testBit v.1)).length
lemma uN (I:Nat):vH I=(kM I).card:=by unfold vH kM;rw[←List.toFinset_card_of_nodup ((List.nodup_finRange 10).filter _)];congr 1;ext v;simp
def vM (gi:Fin 4)(cells:List (Nat×Nat×Nat))(I:Nat):Bool:=have:GIdx gi:=⟨trivial⟩;let c:=vH I;decide (1<=c/\c<=4)&&(cells.elem (c-1,I,0)||(decide (c=1)&&cells.elem (0,I,1))||(decide (2<=c)&&(cells.elem (c-2,I,0)||(List.finRange 10).any (λ x:V=>!I.testBit x.1&&decide (2+(c-2)<b4 I x)))&&cells.elem (c-1,I,1)))
def coverOk (gi:Fin 4)(cells:List (Nat×Nat×Nat)):Bool:=(Bu gi).all (vM gi cells)
lemma main_of_coverOk (gi:Fin 4)(cells:List (Nat×Nat×Nat))(hcov:coverOk gi cells=true)(hkill:∀e∈cells,CellKill gi e.1 e.2.1 e.2.2 0):¬(∃C:Circuit,Monotone2 C/\C.size<=18/\(∀x:Fin 10->Bool,C.eval (List.ofFn x)=true↔∃u v:Fin 10,(u.1,v.1)∈k7T gi/\x u=true/\x v=true)):=by
  have:GIdx gi:=⟨trivial⟩;rintro⟨C,hM,h7,h3⟩;obtain⟨D0,d,h1,i⟩:=vX C hM h3;have p:=le_trans h1 h7;obtain⟨b0,h5⟩:=CA uG d.1 i;have h8:=B1 d p b0 h5;obtain⟨m,hm⟩:=vF (kH 10 D0)
  have h4:m.1≠0:=λ h0=>by have e:(kH 10 D0).card=0:=(by rw[←hm,h0];decide +kernel);omega
  obtain⟨a,z⟩:=uB m h4 (by rw[hm];exact vo d i);let σ:=zU a;let D:=ui σ D0;let b:=uM σ b0
  have h:BX 10 D:=CG σ d;have hc:uz 10 qW D:=yS d i σ (vB a);have hb:B5 10 D b:=CI σ d.1 h5
  have h6:(kP 10 D b).card+vD 10 D+1<=(kH 10 D).card:=B1 h (by rw[wR];exact p) b hb
  obtain⟨e,hE⟩:=uW h.1 hc;have j:kM (zQ a m.1)=kH 10 D:=by rw[uF a m,hm,CJ σ d.1]
  generalize zQ a m.1=I at z j;rw[←j] at h6;let R:=(kP 10 D b).card;have hco:=List.all_eq_true.mp hcov I z;unfold vM at hco
  have hcard:(kM I).card=vH I:=(uN I).symm;simp only[Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,List.elem_eq_mem,List.any_eq_true,Bool.not_eq_true'] at hco
  obtain⟨⟨hc1,hc4⟩,hbr⟩:=hco;have gm {k mode}(hk:k<=3)(hR:R<=k)(hMd:BT D mode):Gk D k I mode b e:=⟨h,hc,hk,j,hb,hR,hE,hMd⟩
  rcases hbr with (hbf|⟨hc_eq1,hk1⟩)|⟨⟨hc2,hlow⟩,hhi⟩
  · exact k0 (hkill _ hbf) (gm (by omega) (by omega) trivial)
  · exact k0 (hkill _ hk1) (gm (by omega) (by omega) (by omega:vD 10 D=0))
  · by_cases hR:R<=vH I-2
    · rcases hlow with hlowc|⟨x,_,hx0,hxb⟩;{exact k0 (hkill _ hlowc) (gm (by omega) hR trivial)};{exact xc h hc j hb hR x hx0 hxb}
    · exact k0 (hkill _ hhi) (gm (by omega) (by omega) (by omega:vD 10 D=0))
def g11Edges:List (Nat×Nat):=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
lemma ua:∀(gi:Fin 4)(u v:Fin 10),(edgeGraph 11 g11Edges).Adj (Fin.succAbove ⟨gi.1,by omega⟩ u) (Fin.succAbove ⟨gi.1,by omega⟩ v)↔(u.1,v.1)∈k7T gi\/(v.1,u.1)∈k7T gi:=by decide +kernel
lemma uH (gi:Fin 4)(x:Fin 10->Bool):graphFun (edgeGraph 11 g11Edges) ∅ (Fin.insertNth ⟨gi.1,by omega⟩ Bool.false x)=true↔∃u v:Fin 10,(u.1,v.1)∈k7T gi/\x u=true/\x v=true:=by
  simp only[graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  constructor
  · rintro⟨a,b,hab,ha,hb⟩;have ha1:a≠⟨gi.1,by omega⟩:=(by intro h;subst h;simp at ha);have hb1:b≠⟨gi.1,by omega⟩:=(by intro h;subst h;simp at hb)
    obtain⟨u,rfl⟩:=Fin.exists_succAbove_eq ha1;obtain⟨v,rfl⟩:=Fin.exists_succAbove_eq hb1;rw[Fin.insertNth_apply_succAbove] at ha hb
    rcases (ua gi u v).1 hab with h|h;{exact⟨u,v,h,ha,hb⟩};{exact⟨v,u,h,hb,ha⟩}
  · rintro⟨u,v,huv,hu,hv⟩;exact⟨Fin.succAbove ⟨gi.1,by omega⟩ u,Fin.succAbove ⟨gi.1,by omega⟩ v,(ua gi u v).2 (Or.inl huv),by simpa using hu,by simpa using hv⟩
lemma g11_lb_of_all4 (h4:∀gi:Fin 4,¬(∃C:Circuit,Monotone2 C/\C.size<=18/\(∀x:Fin 10->Bool,C.eval (List.ofFn x)=true↔∃u v:Fin 10,(u.1,v.1)∈k7T gi/\x u=true/\x v=true))):∀(v:Fin 11)(C:Circuit),v.val<4->Monotone2 C->C.size<=18->∃x:Fin 10->Bool,C.eval (List.ofFn x)≠graphFun (edgeGraph 11 g11Edges) ∅ (v.insertNth Bool.false x):=by
  intro v C hv hM hS;by_contra h;push Not at h;rcases v with ⟨vn,hvn⟩;apply h4 ⟨vn,hv⟩;exact⟨C,hM,hS,fun x=>by rw[h x];exact uH ⟨vn,hv⟩ x⟩
end MainSec
section DataSec
open DagTools P3 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
namespace DS
abbrev TLB (gi:Fin 4):=¬(∃C:Circuit,Monotone2 C/\C.size<=18/\(∀x:Fin 10->Bool,C.eval (List.ofFn x)=true↔∃u v:Fin 10,(u.1,v.1)∈k7T gi/\x u=true/\x v=true))
abbrev u:=c0
abbrev v:=c1
abbrev x:=c2
abbrev w:=c4
abbrev y:=c5
abbrev z:=c6
abbrev G0:Fin 4:=⟨0,by decide⟩
abbrev G1:Fin 4:=⟨1,by decide⟩
abbrev G2:Fin 4:=⟨2,by decide⟩
abbrev G3:Fin 4:=⟨3,by decide⟩
abbrev Q (g:Fin 4)(d:List CD):=chkL g d=true
def d00:List CD:=[v 0xb833403fe [2375,2376,2441,2442,2443,2445] [1682,674,690,706] [135512077] [0x565820820820b4b04104104124c4,0x320b20b7b759982c82a6240410416144,0x1b490483501df41e415660b20b30864,0x5b41175041a4526904136d211c0,0x292410b60826da0822e208281a7225c0,0x6bc9329b68a2c6b14594504142140,0xe45730f620c25d7b2431aa18d836e0821ac145d00,0x8b1691490966e208a18c107124588,0x28a2927837b40253ae38f404201f13ce222ed88,0x57b2a66b58c97b0593767ec1750142f324144f0,0x21d44dc206cb997b0459ca6a26b294ad37bec,0x560824d236e539180513360ca20c57b54,0x1920801a4a164a58bbc55a445924ac185557d8,0xf43dc73175041d41f41e41d451010,0x884b255086287b643189b1362920c0795c50,0x192b4f721276c8af621736a94a1e4aa1e32a3db74bd8852d645dbd089f2226b2242dc6cc,0xca763ddd6ffa367f2e4704164d6ebf95c832f8d5d714565b884bf0a54d3104becd3eda,0x10413414a502082082082082946,0x6c4dd43242dd8b2d66d0b0961ec1f600f604de6a5b4a,0x470ed1a47981b13710c1d7d04d9c4bd4e760,0x2ea3ccd14730c09da6cde1fa088bdb63ed9b60,0x14105904534105d04104d0411c,0x74504d16504135d14114114d1c,0x74114145914114905d0413599c,0x6584180311600c35fa858a27504504186365dc,0x1ba13d3a13c4393c3b13e3abc6e80d90208396] [0x296fe1083df3e8025aa0f9e14e79820fb026750a6dc4107980d02615922b7422f8d6eae108bec06dd16eae108b635bab8422db01af4002410220048503058012120536b7425ff0024408b7c00909095308b7c0090c22df065bc0090c22df065bc56801222dd5c2116dde900245,0x2216f8c5c10a581f9a8bf1fe34215f0600c0d17002267d5ed89ab0bbfdba95d4000c841d6bf6b880166297937521ffe0b3bba8c802ac0157d5cc65232ba10aea055f57367dfc42b579373af5ce09f3184230a229a2de21094211494e4d0b8f59625b1845a60b3b900ecc5122004443f424410a180d02615333efebc9d9d7ae6b199349e41e387d1331c506437430057d5e4dc3e8998f0843743059de9888015650657002d24019083f333a107c4b8422f896eae108be32520c420f8c1fbb00232,0x2e137203420f3004a40847c00b896e84cde0096606420f30036381a0d949990853407ee15ba1333f61002f408be108bec01288ae842b1045f600804116c24b42168b00a59083f3c0296420ff027f4,0x217be074210b00364430bc418f1842a23bca7066b0863d62150211331a05bf4a43c3d6ebb908e4c0e3f005472082108c2fb7522ea0422285f6eea042260044aa6235d487878332e04f9802abae148210ab8165a0010842c00d8c0174384221add6e2121d9510666e08900b7e16eb71090ec199b02dfc0185814841fe006c7a456cd020f116eae108ce3,0x2bd0bcbc0a8420200d084224288d6e84df9a821408211c4c1086460843c0128c00d84211f003621489c418f1842c239e2e0bf580d033f48239d6eae108e6c09fd50bdfb4260852c0cad4216b02dec00d8c216b02a006c68b5410a981900365,0x6438173c2173c2c2008801844210700402085610856c0180990db0856c0180c0a842010150840c0184dcf0b0856273c2c215b00413] 0x204470bfdb3f4ede84bbbddcd2b695187d942bfa09d24d0065d13cc8b86d12468bc08547fa06478bdddbf6ed68ebb3e7cdab497985db3168a76934219f44838cd3a460c4005c77af4ef2a7a3b069713db3d402ec0c202158002f498b421c1ced29e75793331c106b0dfd6ee9bf5ed14f80851f19b0005c6f4af89e151ce72fc4707acbad5e1c1916178db5618347a335923988042d83d6d5b2691876c511c2fc16497458de7859d21c258bcec7a38a2465e01627ba01de62d05092f4386a10baac7e43c1ef05bf504685d3ba3c6192e3326ddfa5e21f56e98950848679fd46aa399614188cad99e248037321579050c84acdba4e89970189852177b53cd683de8385ff860856d4f433dccd0c31da3fe3544d8fe23f868a898e3e80dfd0818000215fd2f394a5193ece1b46a3a640e0810f480ee0f4f4bc8812cea4e020577daf58a01524f92a33d124811b8240008f1ef75e017b416192781113e4882e1346a08f8d6476afdbb370131425bec9b2368108f0fa4c702a9a7c133007efebdf34b86c6b6addd33d03b16253f69ba348311e0f5805594209600f1d926437ed17cdd361b86d82622426cb609123013443e17c9227a76910ebeb79db66580569460921c76f05a998e473a165b1162f0ff8a66a1a71988899e42015fb6c502ada8c120297e9ce4dd1a1d8e76f91683d9227a7df700af2941262035374890f2fd285fa76d8627eb4a10ae1f78157d4a0913dda8a5719969379e4111e3406efa74512d635387340fbe7893f4104dc201665482507869f0dc51be4513fdb6b87c37f9477c168b11876f68a60b7c483ec95138c0cf380679bc4713f9a8388c6a0b77e7792cd7a7e5378f0922fbb8e951489c20b7692b00df2c88287de02136cd96406544007a6d302b525c53c482907ad568536250101ee733eca170272097f7917481e5a8c46484ff068d85c00c15da34b6204840426e340cb25e1f446c9b0baecf9b91848a6cde1e6ed3627c1f78305feccd25b05bcedf2745b900ae1fbbdbf0f2e860e78b070b068c0056f56d4784db84ae2491c04eb1082795d902afd14b429ba2302f78691d24439ff30b0da4bcaa3d8a069f0a9823e3846bbe859f30762ff8400fbe84191297e5a93a2e9f61d1588f989a68e24dcb23b43f3c27cadda9440cc0889c66c94f3c87703bc6e521b107c13a3df88f1e94e3acbad3c94c4c443e37fd487a6c463f7063295033be4796c249a29476018c7faae6941440be5ce78d4af99925e9222947cb106fde04087182b15e9017d6e12ad07d2ae690ac15f48e0eecd1c645da5cf4d902241135a84c7f7bcb930cd53a68103113fd2567ef28885aa59ecbfc08cb10a8da57a0e7cd0763df5898a52783125d0d1bdb0da8e979be80494e3f987070e934050bd25994568961bb4ff54854de6a966859fa63e762e648a52b018a9a9ebda75ebc9f01cacc8178d0d128a3804b525f863dca8dc5ec1624caa277c416479861126cb9c850310a6380946cf948ca507abc560d0147b46fa4caa27fc41796e43839fa1f38d375c8090e0621cc50328c8f3a5741a75f9624cd0c03633ed22e8fc32110a6781c5173e72f4560d11ef74b5a14b38501537d7790e0a21ccd0528a8f48ac1bf7db4d98725ff65cf69d7a577dfe7c4cfdaec43e7002278296d35484bde02ef99920513f11fcaf89d72212888f9f13790d8e201455a467f020932e4d2518bd6e736ea712a8399a2e1714529d9e74cc04513886905a3a76d197a22739925fa0c4a8017edadda301bcfdb2d04ee66b7a9c659039e26489cbf0abdedfe5f5bc3ee2afe2e296e79f58cde51dfcd20b6cf73011f838b7d03d87e874dc5e8d8028a5540633144efbe2c132896db2acae113333e0046cd9b0c4205d35952531800c6f03b154372d3d8ff316d635bdd9537b1cbd11825773d78423751257a02223570018d98a55a444205b11f31c972e8c51cdd7704f4f5ad273dc05ad32b3d32731e88529c4d4332c526b808c1e13687de9312d8a4d9128a9cbf0dd203f9da3bc31c6005c2c59f455a712b89406039668254800497171147213333c5213d0036c93c3cd1411a3b5a8578cfc0358a70354bb444fb366cb51f09139c29f412d36d07467a8ff166e11069935ce63b82e8bd1679b96e08af5373eb2452f35c485ce5e6364c70314d963ca00a4384a14d52ba5e0294004136cc74898e802e3f6aabcca0028e6767a4448b1cd58ca0038221e800c1be25e876eacf853442242ba002ca8767acf025d000414e6d15c98e270e5dd69ad66d249,x 0x1607a10f5 [0x60d038fe82b1a641c00ecb8ec6240410450412084,0x79ea0ac2592485304118c3141062009ecb42240,0x1ec6040d8839dcc0e3ad64ec31996a4bfce8b1d755da228,0xdf441c2482b3b61acdc67a3efd4d50] 0x2f08041101a0104b3bee0e2b00be6210b00824210b07ef805e305ed805e20d20b2f00bc6505b0d20b2f00bc8211300bc4211307f3805e3 0xe50801915dd5b902d469216c0709143b08219426a1c03aeeede8439a98480a119d8a13ebcc8ab410a4499b5392449afe40af08aa2eb7c1460d0afa0102b110cb427c5b908010509e298803f208075d10ac5963406d5f098c41f9045b611568214c24441f9042a948ce243b210220a0,x 0x605b02e6 [0x206bc51b620c8360017e60b1890105818adac524c4,0x37d475db02528e20420163ac79f20e406b60d7ea8b2f414c0,0x2588b5e66933df7598a3ec3586484e35914] 0x12fc2b752fe5a3c1 0x2f9bac8996c8cbd4290487c8a00020c23c1405cc835199b3749278954f97a8d22c03f555c00a620d3e10f584f83ee0a0e6d2,x 0xc04c2171 [0xaf606c69a282a724ad90b2003b777083aa09012412104,0x60e698131554536dad361131c7e9276fd3414846500,0x5b180cb5d296099594] 0x13a81eb9024eab00a844eab07445100b108d839732755805e2 0x315c9068200561a1a1ac6f87af75629149e1aa6ed4e06f28fe6289a387c51f365828616be233a360bdc94ce38e9e2b4eca3d4d1ee0,x 0x803f0865 [0x29140d34429fa09a66473e8d073e44180e62404d20c4,0x1c80b1697066c33bda6880b3087b6ce460bdb9ea5428] 0xee86840204b1d04604a2 0x2c70678f5ae54d91c95ce975906fddc85ba473a5906116f9389749a516e754c53f9b3b5d6510717e950,x 0x80442459 [0x1e3045c81075ec5585365050e42b81303ba89010452144,0xb6326463539602c51a7b196a028d8a0bd8a24c565a48,0x75be8c] 0xcac412c40dc610b0372 0x7a0b5fc2f8115b44d26072f3f18d77777296c13552c5dc0b0a91c38071f7734f59598405277c90,x 0x804a187d [0x7ee7350681471063ec83801fdc309010412412084,0x1f7ec488025eda960c652514033096289b84104dc8,0x363ade9988ca150] 0x85b01005f10840100551 0xbd957b9f13d7be7c4d60cc3460ea3bb6ce0af615dc414ca2eba3699a4d6308edc5418d6b8c90,x 0x604221f1 [0x51b0b62ad053e5ec25fa41481ec989051410412084,0x55609a32a677308f5351676a978a08d830a3384248,0x4dcc] 0x846100463f75b108d826b3 0xa595711f47212c51e8b69860d57def4cd95239ac915f6e78c146585cc332d8de9c5d3c760,x 0x803c515e [0x491ded949e74ed185341a790c80320905157db5304d2504,0x6c183ec45c8bc3d8c2817b87d8a4d04c6003e0d6d8d648] 0x84019f415bb3ea4b767d74053 0x2a4db7bbe32d39f83655e6c651d4d51df13e1cce679a506a775f61b7d760,x 0xc0381461 [0x9412d63ec7d9c9010f418f341a7913004c09010412184,0x3d883116d832754c0a630c660dad5019a2c] 0x1a081d030e81b1d510e58690c34181 0x4439dbb3cdef3c916937e974524bfec49b634ae149d19a53416a5478,x 0x80301171 [0x727ec90620bdd7b0f65ed029e4448130240451452084,0xd83399a50c37370656a810e648] 0xef60221104a0c0b291245840d3 0xdcf1f39b7d9c1b4bce317b2bda1def562f779599cdad6a96,x 0x402c11c1 [0xaf69729285970a0f196b4f61242293c2590f2049890524120c4,0x2bb4919aacef60193d4] 0x943b61 0x5de3bb4f1f7595563d53ec296955ef746e276,y 0x201b4059 0x17b3a588439aaa1ab6253147484107cd13401120c4 0x8441 0x4b2dd49e06dacfcdfa7156916,u 0x220270 [0x3ac1188b3966c30a9933ea676b004c81da00fd14588,0x4bcc] [] 0xede9b439fa76648650,z 0x1c2070 0x363ac999cb3618c0fad9dac1731f66a6324148 0x6d357fdb2f6de8590,z 0xe0c71 0xfa322561e951e9b0dc845e0021c4 0x129bfd9e0,z 0xe18f1 0xfa322561e951e9b11c845e0021c4 0x129bfd9e0,z 0x86171 0x8f3148a0d2104 0x15180,z 0x902f1 0xca6154840d4020c4 0x59980,z 0x68070 0x5069030dc8 0x2960,z 0x60a70 0x106fa30e08 0x2960,z 0x628f1 0x7a5445e0021c4 0x2960,z 0x50870 0x1c19b0c 0xd40]
def d01:List CD:=[u 0x9c14c83ff [0x9596492f2c525698a092d2c50452904,0x385beb0416560aa19090455962824b5ba5c4,0x5b05046e086336d5435da8906803a0832c24,0x3df26863611b8d3571c405d8316914941900,0x3183e8b11def01c32de067e087b171bf60f73625c0,0xb0e01e42420407de8284f1242580b15148,0x11342e37c68ae305b18a4949802eb73392502e38,0xa25ecd0591a34a3dd624b541f792f6eaca8,0x86b15d66bd803181020628e059dcc02c8f17854,0x3d12cbf8261d16f00d90b1f74ad8c2f61ee3daa286b5c90,0x3971ba965fa745ba639fa369f8971bc] [0x2dda2a10d2600c4200c42121d803110171e00c440c40114823eb062008a7048b847d605c78031205da6009c50413a145eb756e84dfaa145eb756e84dfe0596a8517add5ba137f81832c80110a400884065bc80110dfe4b00442,0x4f3f385e3e014ae83f7606aae08784141fbb01a033ac1397819de004c6fb7ecd1508684424ce668540e16581078cca68a84341d150868c1160d6e852fe107a6fb666ac9a1a20da10798162c0435e00984176f8434105dbea0868380bdd11575bab75dc847d3405d688abadd5baee423e98011040cb700442,0x5d0610af80261f0216b02e3c013107685e3e008a810420380d0855c0130db083bfe009861747842d92186eb756e84e8e065aab756eae108fac0b8d68a84346068f8026205c4e8e4216cc6527086f2a2a6941fbb004c4043c20a0fdd80cea85e3e014ae83f760086a8161add5bab8422e3019d60bc7dc109d85d033b5,0x13f412842a6009a819dfd9810b68ac042d9918883bf9addc02a8421053c16779820fb027bc0135802842bf4004242001084335bb584cda41dfd502d70b11c21a7a92009aa163ff14109de75004d6077fc013081dff004c240a5c06f02103019d501a10ad822c180d084fc116301b14,0x10de20efc210dc280869230435103bf0b7d077e2bfa137e4009c2c641df8812842a90210042a9a04024215502a1f012c08544] 0x36f35731bfdf8b7bb9f022ce88207180edf273b318c749b04952b3790a06be237b25913dced8b2ed03f11f7e0018cbd84873d2398fd3f5d22c8c081de8f51d66b7cda231ae8a9e826029cfd48ab345917eaa1b1e7fe1830b95a300469d03aa0f360f3d1e0a004226efe5e1defeed153dfcd64a231a966ea2f739177d2dec4e10f1dc51a2e94ca4a235ef38107324db9dc3a24767b47a4e8d2a832798d1dbc18e32e459e734e59b3c5b98eec2d73a07c702420b478c71552e6cd2d5693c3adf3e57f386e4315fb9d68f1d6df020a14699f512a7c9d0456eb3bef4cfd0e255436a6f2d8cc8b9742e3c050e452ccddeac8b3381aea2a4ed3ccfddf46973681fedec7dc9fbad05f59fb6aaf49daa7cf6b42c757f07de43f8a1812a88f1c35f27d1e40fdaa7ba9591e9ea10ad37f03f7b29997b4fb41444f8f9408006353c0e6b573823c186f3eb207f539f20e629ec75da424c142b4e451084e10cddfea38274f3410b9d4b1d1e8505e991891501c608210205e78c7fbee09f015dec8f9962295227bdbc097a0ee4a0ae9e9b0b5d1caf7e1147feaafbe98e5eacd4a46ae2f84ccb3405ea9c413b3023168663a72321e5c2f47467f5ff2f0ea218d0deca2ed5b1375f648dd9ec945409cf7b298943110c789ddb4ab93ae5231286f4198dae6c557662dd56449165084027da2b8d63168a3ca71f587938e16a83bef9fc007ae768a0086e68d224428eb8d21c224f1e6713e5cea9f36386b3c2cabe4e7057babe14be10031dafba8569e74eba542f7e0cac1c795806e9f8d7420de158a4f97222c8733fa3634458f9a911375f6ddc8668af79163100a315643080bd411e26a7004cf037604a87e5b380c3be3d6fbf023c50d290438467c4610573fa145a65cca8b5c4a4db9a26e1fae27c684205ef37f163a10bbee3281189a5a205ca849b3d4c08106f8708357410312040825ca41120408074f43fb9448102018372abc08118848b5400a54c5b94487da9696a36372b568400cc73b4d49a2141843b9e32842178917b63a10ba0a56842c0,u 0x3e0a09577 [0x2dcc95a6282f8c505718a0b631412984,0x40d3fb98238fbdb0d3c13c77ec9171106823721a40e1c4,0x908101f0278c3d93887b1435fa483111b4f85a40,0x27ed6342eb7c6c4db1953802cb7b392502cb1e2042,0xdda9e1da9f005dd3126baa14aa332638d805260b1d5f60c268] [0x34b78bcbf4810aabd26aa886b31797e842d620086a2f2f022215300c082f2f001110a980605001110a983f6410b78060210b58584215818584213f18584200c43110862206018881880452858f82e3c031180d07eb80443,0x85b130857253a017666216b0086406442190b89c42d96842d10868c17b10bcac42d90060105201148171e0a402298847c0301041108f80603179780910ab80604] 0x7a067a89a86748d30d9c2a2b784d503b4b6e6c9e29424df40020de1438b52c301081e82820558f30a72585d62b7454cce8a5214a08e41580a01bb84401000473ed9a1d7afa2d88e0af610558fd1bd4e2765846ee62210c30e130047fcc0a68fded70b1c4dd45210b86bf95571d304dd1f9c040111d45c73be74bb8f5e7292c72f877c76960d05734a39db04574dc19c56e8f0f7d7c3bb66332e5c24f1b06842b8ec403188b6358d2ebc2cf221acc94f8e7f5792503eaecec64269c2213d9035f094c05354175cff3d9c2d38c5725ce8b15ff55bc25511be851e1955c11dc8dd62c71c1a677b49b5226dc4838e1513fd3ee2ba57063553a000437e1513c89755891df413c083830d649b01006509f28301004ced206f010044eaef74120200e735d8c0401984040180,u 0x2c09328f7 [0x5e60ba99015f66b7b5d6f8d7d826b5304d28c4,0x3ad9a7ad835f4a256e7d8f34435a06bf52c641c0106a4,0x100940b20b8e0181080d8534575829113c736969e00,0x859347a6c50405e7b99b6a1b7650a8c4fb732a306e6824a,0x506bf306bf2e7478d96b6b3e8c1161ac58d10] [0x16800d10749001a7243dba1a6ec189c90f6e8b76568867c12fa680cc18883a3a7a21aca05feb8445e606d5042c888431b08432e0843c0129c042c90859c01310842c02c15b110b1804f38693db110b183314,0x10b0222f0441d080d109e4b7455794006883a3] 0x215144fc4083b63f5d103c82ecc40504d1ee2b1b3e1a0f4f8b58e76318e74c6142d9161e711a68233504ac5b7779074caa18c0b0754154fa1eb3b173dd6f637f8ec20ef222355095cc953443175e1088228c0813d2c4ad9036f1fcfc13aed3188b6ccc8efae36910b6c80c48711b6d8b216e752b6739aac68945184b2644952c005d05b3acd1b6d590e01db2e951de684036df00c48751b6c8020f8440d6c89100ba4006c581d44bb4f68afbb1534,x 0x1a0860e76 [0xfedbd82eba8901157582082d6c10412584,0x358c90d43f621f873f6fd8030061ad058e0e20a0b20540,0x826a32949a098c2071e808403e2f6087301788a5ace08,0x83143db60cbf600c01ea0f262d1241adb52c3fb7694,0x1cc0fd4c0fe4dcc] 0x10b430de310b442114442c08858c1651004d113ad804d2108b804d28513add5c223db0596a610a84699700844b744ea92dd13ab83593 0x80a2ce604f12bb175375aec557c0c1c5ce090c42badd7a55822089418608acb5f3cb2c8999080ac01e4037e1a1aa0c677e14063cefc0ac051417c65df3c9cad48918660798bc8a1871e26c38f860af8c174eac3d13503291c2663385e4e09090830a87e0116b61a9667ea9429877048ca3b6b004173ce4890ef9af60,x 0x1807a8376 [0x1c908a04b1e0aa0905041056992d8c90412504,0xd873f790723adb0d3cde73de2886b411b8e321a40,0x284839b1765ed6e611a5196b119faa1a094c007daa0be5d88,0x4a83748a37808d05d3cad8c543d8038595450] 0x84220f700844215444d408037183e58042211f422b0056ebb911f46b75dc88fac1faa0060134b580602 0x35afe2570a205e6c5751f452817dcb8c3424a682701d751f8dcf186e0004b413a000176a80c5001412817d07282a830370e0540bf839620015da4d400191da64853330bac3d1fe5ba1bb04d09b0019710940000be839406ba18e51214bf42d54082002947f883907478368e200be200473030821b30800050,x 0x1004082f2 [0x107e8b10c3b7dd7c87b050460179822b630452504,0x9907e9187f1e2631298a9ea8ae34754414656c5050dec96c1d88] 0x178a86f1460854b2cb6217ef88404bc518994277a26508c060de28c0211430a1 0x4e8c0b8b6c695f57d14c90f9b67db7be88e0a2475551bc44cd5c0c616c891f86b408d677c1eb4f1ef4446e050de4c8d67cd894c90f5855ddf2c5273a57c5dd537c9896615772c5c0,x 0xa0470271 [0x689902f6b04458fb40178242b80ea3a809051492004,0xd8637b543846c12b028b059e8ba823c435fa18c608,0x20c45b60c] 0x1a08128303c7384011088341 0x3709f68f8e59a4514c0505b3ba0e30b6bd839669145301416cee834d9b2cdd5b0a5d2c7045b3670c53bacd9e2f449eae8c58,x 0x60388171 [0x505018e09fa14fd84008410f973201001490492004,0x7a662325d97b3b9871766c1e860b28eaa28] 0x8431fabb804b2108d804b2 0x3b66b943ab5d6d7915552c3ad3ae8db58f5ef77cb2eb58572c99bc6b679f75185fecf1b7ac9a3ffb8a252,x 0x60540a75 [0xd0f62647a1ad067e3cc838019dbb090104104520c4,0xe6cadbc33918166cada351d7681426b03788fbe4e48,0x246ee24ccdd9b8caf62a6b4d10] 0x21e30804b1108d804b2 0x1f935a68bc651c5673c1f795c38ab9e181c53098c66f0e20a3c46581507581f19d94086a2af2663c7cd0,x 0xa03c91f2 [0x6202d1c815867e8cb716915067e43c812e645f6dcc12584,0x1d89f185f328b395a351f3412d860129c7002100fb588] 0x369113f03a64856e89d1c1969add13f383f53 0x30bd18562c616e552f30d3270be7e150d71951b59f0aa9a847059fef14185db359974f60,x 0x80330af2 [0x81c408474c14720adcfb421f9d320e006066b5304d24c4,0xa0c7e61c3f1f46025ef6d9c8a50682630] 0x275044ea60130a05e094881 0x19bc94eb479eed78b6513e9e77c6ffdb2bbe9bcdae25b69a3db37a4aeb379c30de29a352,x 0x803c955a [0x60c434f3cf1e23c490c60a08c0022b630452504,0xeb3014c81e22b03451e5007c18c15c642cdc8] 0x846102e1042104c1 0x651ce95fbab6584da59eeb96ab63674704146c754fb9e12625bb78d52c5e0,x 0x804382f2 [0x2646a08e3b07c87b411c05f608a0b5b04924c4,0xba8e38616f638ce451e0b30094e388108799218c9c8,0x3c4c] 0x10ae301b040210804c1 0x236732517d5010d696156b3d315c70613b795b2eec2f955bb74d145b694,x 0x40390a59 [0x1c624f12445899022c3da02a03a89010411452044,0x24ded9b0c16690d506099bcb365464505aecc8] 0x83a18361 0x5648edf6c9b037bde78de4bb4ad615793f6be75e338de58,x 0x402a4371 [0x145111b19d80280b64ed6d8530860042293d00400d0492004,0x8c987731c0c14414] 0x3eae080041 0x199db971bbca6d25735bddda7fdb8a422ae54,x 0x202780de [0x2020f6b06aa86ad889e1804a71c40848e434e7cadefb411f9068035b25c4,0x1e265735e50] 0x8421 0x264a7ec77937adbc2cb7d5ce2b14,z 0x200170 0x5b19610c4dad0c2467ec699ab4a180b644cb1f27ec248 0x2da9a7bcdc75dab0610,z 0x1f0070 0x2b84219220cdd9b0c3d6e8727981541873c4188 0x15da3cc6acc59d0,z 0xe80f1 0xf1312561d551d5b11c845d0021c4 0x129bfd9e0,z 0xc9171 0x9a3a32c40282452104 0x1b3d1c0,z 0x81c71 0x25463dc8465c02244 0x59980,z 0x88671 0x1ca61d8841d8021c4 0x59980,z 0x94271 0xca6154840d4020c4 0x59980,z 0x610f0 0xb066e318c8 0x2960,z 0x62c71 0x7a5445e0021c4 0x2960]
def d02:List CD:=[u 0x60142077e [0x410413561820826b331410412504,0x402800ec15e600d95f60b20b20b7b6f6a8246244,0x3656d140139368a4ea0834823d4121140,0xa0fbc83cf38d1bd4506924141d40,0x830e602f9542986b142d8208b91dee8d87361d80,0x28286a62924a60eb3b40253aeb0e004201f1216f608,0x43017ed348c39a00a02b4defb1d76a1b20aa28,0x17b00906b7aa238ca19b3d51a61534104d9554,0x17907517dd4c5af3f41e41f7d1450,0x3084f2c84f10e4f92bfa92cd36850e7084311626d24607bf7d90d0,0x27427c] [0x103fbadd5c211c48b7427d7040534285eaa842a9a0f78a0f7e1084483df847312e108e6c00d8c09f8507bf003727dd5c23989f7605f757472108e610b6340847241d5c29b71041e604c2a832b821083d3,0x10a175bab8423db004355c26742158e60a82140df7536a61f41087f851420094efba9b9e16870d8647fa0843c09d5dec430c8fd1420421e0832fc85cf0b1859c4b6f0ed7fac832e604eb0832dd0211b004a402210878198e00949805488420e059684b8a0d838162e0096a832bdf906c1e5e8162aa0caf40846fca8206e00a8ca24c108781712321b7954028421e07ef8025300108472,0x21184602b0bcbc0184d61c7662108b8238e4008860037108421085810858c10b480884219041fe006c40342108806842160a466a083cc1014d0657085824195c2163040534195c14841e9802e8708593] 0x15bcaca2c02e810b63ad86d1f76fd002dd1b7588d4e7c6db594d4457a7f07c9548bf4e0a3521fdfacae8bd4ee36ee3a40ce8357508fc1077e1b8e78811caa8e90e7a2835601eed432fe6a8c8471fa15aa102f6a2e3348d5e14ac5f4bc70102fcf6404f5d13f54589c849dc772d350ebc0c5f002059c5c4cc68e797577557f17f335a722eaa67a74f93a6bf58808d135116c59e7018637fbd8fb1908a5f9dd54ec66c5f3b800fd3b917a0bee6e14f6c762cc65962bd12cd439f86d54e92406d8eb27374b8d0dbfa0d9b180b759a46dd1b817bf06b368f0d7688ef859ccc5d878f01c212e8c7cdc5b3af0c34449ad2a25067a494e6b4ce362891f4da1270d3b7a425607be04118a5dff771895598fb748232b31f7e9e04116f6d163737f8e07dceeeff4e9780910a37a8f198e555b2b7f290c7d1b041043a65fdb7e15e918976ff0e2fc2b71f11b7b7f3ec7bbbf48c32016d1f71d000c8b8f5a562020f2ad6a26e3a4631a553408748df0e2c17c602e556f62e672d539b0d13840869b168422467f0aef88b1b03c6a14224748d08f90a30266c14109d01b0675ec6fac7d5af62ed1daaaf3b0228a32cd95431573eed647d3ece87878ec4888b68f0680e3c400000201abc18d408f5ce7d0c94354f7f0c325760478c96a5b9db976581823d5363ba7a853bf4d2da1635bd9c65f06e0d08fb4ce9971ba2e35f4aca3beb2197462edf00877e35cc27eb034d633272c079d83c44853b0f5e678603cec870564ef7e21fe60df63acc2405115f800c86ef1df554130a6497e00323becb6d33a22f2e0d4f1af9dc103cd61fdfa61e660e566ae50369c851cebe7642852ec9a091c24f02fe1a301c0,u 0x3c0d30aff [0x228ad6c55d628af4c15f66b5304d28c4,0xf344299281af1750d61cc83803d5f60ba9909e144,0xf63cd11a608a8a444e7c0db4e7cd620fa254c144dc0,0x7a6c0cd6a6094f802dcc1402502c82e3806042,0x3d2c133059db789b2a03b05975d05d9a4a88970,0x1e8037d181ee69c2c8a3342dd1bd44586b0c907b58,0x2db70abf5f6a0e7fea750f9870f88717873a3c] [0x42c0842c606ce5d242e841f9c212e495fdd785a178f88c10cd0feebaa0a85e3e2304333a850342f1f104353042c6009a52b7810b1812fa452d6210659a452c610b180269a395bbd1421ad16eadd0983302210864044210f035938a3ad6eadd098341487c2ed3086b3,0x4338821084e201a109e410d8200a8210d5802a1035084ec0130c21ab0359c0150e0e85e3e2086a483a178f881684272801032107f813da48218882dbf08bcc0e2cc2c4f08422] 0x2f8116eb44f81bcf4c8b973575725e565ef470ea1666dd3e00189e7a685bb9abeb8efeb3f7410c1d51400b829f4103f3d342ddcd5f9609fc990b9f3b03434e88295ce571994ef48b7559a00b508829f03f3f08b957b782bb0ed646504082b09b5517f3d08c34469d4ee459a02c4e702b09b755d230383c69b6ae15772dd60400f490937937f531bc73b52456d1e77020fd002e26dd43c8708c36c7d691dc2cc893beb400a5591903000919b3890bcb0301cea7800805695d0edc3446929e39572d0d69a65db41a63365284085f09dbe00d901ad9cd5fcf8ca106509db400d901add37a3531589b45200eee240af1059b45200eee1eb440756c5148200eec08b16f675df04800027124dff143e83305b520fe9c400ac26c06b551ff0c815a78143853377009006bc1d23b7691f6b834140801243f47f4101148710430025c06b7526d4cc05050ab1d919c951b1511612ecd7446bb13eccfdaea4d21dbb67e22614,u 0x320a491ff [0x1415e60b73057982f8c55f60b631412984,0x18f45b12fcf1e131691490c6823f0d643c800832e24,0x1e8278c3d93880b2d628391defbdc2f3c35e8b665c0,0x7a4edd9551dcdb5953803804a05c71c820210203e,0xed4f824c7dd230e7e821ed404001b8ac02c8d1db2ca60a8,0x798965fc] [0x11342f2fe10810a981faba8d59a0340ccf004c50ba065b80221a8d02a9d406a8728171e0085015178420e05c668615d9d01a066690342f1f08a8104206065ae10d6204421588210f51ab340d1d2b884356a356681a3aa22be20cf2c21a1012ff004e20846c068199980d0856d46acd03475086f1,0x2b0c401886036c412fc62685e5e10ae610af8205104218842d8c4aa686cfadd09d74] 0x1ca849f871d2452c9fa0af1e0906b0cb02045aa6b19200bcb055de6b096158c9416ade19afb81bf57e43b90c4bb465c6009e6631a29a97911dc6d90a9a2019eaf591ab87c4041106ea069ef3a96b312dc9c8e71b9a97135876962021ac5aab1a215bc571cf52016d253b007aa5457a040186fdb03c501fbabc44b81385600f74b2bf517206345c931005f4f240cfa2545cd4487bde258f50057fa6e40adaf80821bc0db4f00c89080cc48083ad3c6ebad81baaf4f001721891e3a2376c057c114de02f813502a20cf05d5480e25ca64cd02283b4854aee41f1483dd92f2f9fdf60,u 0x2807c2576 [0x2636c8480018f70824041256d82dac10492504,0x1398230477bd7bdb113c13d60cfb0e60a0f1f922240,0x103736d2961ef51a5bdf612f860129c7002100f82d825ae648,0x27427cd4aab69507620df46013c47d9362fd5c509a58] [0xd3c89a79c422158d369009108d8397c02a21a79c42c60e5ccd3ce0154855ee211c818883cc02a19a79c02b173c1ccefeb85488857c198b6a63e1b1e2f2f9fa211b01a101700951ee5304065ee4b34f38793386c78a5ec1ade01290d3cf94442c1885b1,0xf263ee4b0f264015056eb291245840d4] 0x268f9e045fc575ea3e0040097c861d918b137ba234bb201730d7911433e7102f5e114860cc8da432cad50b4562d6e11408f018ac7ac8906d903676c1079aa0504502d837f25d1bf88e36908c600d6458c631ae291010431914846440ee67a68f9e045e4a1ea30f874bbc008018d877aadcef488d3810010c658400c871b67d0a029d94435b0409d226070f83a263c5b9de875f0d0e4286533127840,x 0x1c07818f6 [0xb5907003a0cb890145658209ad2c104d24c4,0x16b0923ddf7defd621f82895b8e600f541e786b21e40,0x128b3087decc651dfb243440e204201f1fbd47d821ed208,0x246f6cdc61838f66fa76d34401895888d4] 0xd64442c09488c42c17a0cca68858c1aca085a1121c22b0856eb71121c6b75b8890ec1fba00601121f806025bab8448760ccd002b0add13ab83593 0x8aafcfe5868200dc6a6aa4557e7f2a00fc6fd049d4d748e21e07c5cff19803988aadae25d488187a574c084ad3b32b235c4fadd8e815628c304196023ce081beac0a33bf16655e35cd066540479c1a10e00df560204677ec43158f11212c542db7001beb304408140a33f1208100b5f11b33d3244400c73e2760,x 0x120680665 [0xd1b62a0afed0f7e90b2003bef6ea240410412144,0x1b147a6f388fb342d8228b11e81bb4945580,0x842188b5b181efd94ffbe8e48133696aad0c37b66d4,0x2d8b0c40c] 0x200a113020966930209017851cd817891cd80dca00a39b1f99a11302f121131fce05e3 0x28205032d907a809c3e1020b48010336d71a6178d41040054188cfdd8bb6ba6d8bdc0230d305ba0a688199140006f556745f0021195050d30732280ba3da2eb20dc83580e86478a5a39df04d1c8709e6cc9c4c044ca09a10e3872be145b4df6e242b6153c9a0,x 0xa0544275 [0x3b71ec05a10dc0588bb485801fdc3090114104120c4,0x108138094856c545022cb58a3afd341a7d14588,0xc9831166ecdc64cfc974281b7b4a58] 0x17c5708922c1cb980551108980402f6e988442 0xbe41ac20387c492d48bbe51417510104b50ce19c26ddadaec98fd54a0835423157b2ab557d4434714067294423f1c5f8d0,x 0x60502c66 [0x4f700c79983405f911204c190124d58608ad8c125c4,0x37b5b9804cdbd2a3428457081c408403e55a1f242cdc8465c0,0x58df4606b1165ae09afb44d0] 0x13a82b753aa54881 0xa085582fda6d3c9311b79ad70eb2a29abc525c2bb7ae3859d66aa0e2787f7c7048639b6a03cdf1c180,x 0xa0368572 [0x76616c298c90d4a725194e38d047021566292d4c525c4,0x793520278fcdd663571740d235173400fbd08] 0x9d6156a2758ba140f426c1a3143641 0x7c4b777bf2f1dbccf8d524bfeb746d9e95dae995f13cb26377ac70c735e48dbb3079b4e180,x 0xe0462861 [0xe6908203da2f1c7da051d3d907004c09010451412084,0x1e33499d8e13918706b4292a7b5610490c608ccc8,0x64a9bb4c] 0x13aa1ba10a0e8508d8eac84dc23b311d9e04b2 0x1853772f0808ae9d078a7756eb58aa2b335c763e36daf651361517396082355c71308b12d9c96,x 0xa03d285e [0xa477b6617e28bc712681af2c641c00ea2404d5a64b632604,0xed33d244586b163440c9fab391881c408418de08] 0x9ac1341f102b0add9ad27e01 0x272dc6a474cfeeb7c90e568aaf865dd10d5b384d07f14166e365a3745079b7252,x 0x402e81de [0x6bb3b987321a74e98ec98e3411fa9320d00556d92d8c92504,0x13733dd9fbbe650d90c50] 0x4cb0add9972 0x3d5a67caa716db86fa6d73bf6bebcdf6a94db32546bbdea75ed360,x 0xc03b2071 [0xb1d9e8a3acf18c1038fc188b40d790ae03a890114520c4,0x41beb3618b6c158d8a46082f2cd9501592c] 0x290c2521048d10832a1f3178726c02419a081 0x455b7beab8cf245a341959cc524ba7dd4d94d05a77d31852d4c769b5e8,x 0x802d605e [0x2d3047a82901ad835e34fd186b40d406262b5324524c4,0x42c41a6c829ea40e2042] 0x83b185915bb3464b7668f25f3 0x153cb7cdea7f4545d5c31cad155dfda46efe0aabb59b2,x 0x602a945e [0xb8c91e66e472c33f0c7e4f9419c06160b631412584,0x93016b1a0ef2803e] 0x10b620842b7674732d3 0x6d3ea2b971bbdc9e569beafed2377f3849aeed60,y 0x201a9059 0x1aed31bda48c3bca2fb11789b91bad0760012184 0x8421 0xbd774d3c0a4f36f3f6a2d916,x 0x20242571 [0x965471709fbf4248a3616d079e414812a241450452084,0x2ab5bd8] 0x7dd61 0x1e77e6e0cdb9afa8c5656f6e96,z 0x141571 0xdedd562645264b329fa1241eb452402104 0x26acfb139c90,z 0xe02f0 0x9708436c19123040c588 0x5d4b1e0,z 0xe0af1 0xfa322561e951e9b11c845e0021c4 0x129bfd9e0,z 0xd6071 0x8b79bcc362824520c4 0x1b3d1c0,z 0x88371 0x10a60988411802104 0x59980,z 0x92871 0x15461e08416002144 0x59980,z 0x60370 0x706b631148 0x2960,z 0x620f0 0x106fa30208 0x2960,z 0x78271 0x57d4455802144 0x2960]
def d03:List CD:=[v 0x5216c21fe [2376] [] [] [0x4105618208a082d2c10450452484,0xc827005da7b041982c82ccc1ef6a82404161c4,0x3d26d136087340d3803369342980307520e40,0x450523cd8dbbf6c3c7c4098214d59401c7342600,0x10807c16c0187b1e6883297b07505584248,0x2516608d1051d1a99638354504b631495c30094eb8e2042,0xd552d83095b2a67731c96384499a04d17454,0xf79107e87b8e7e87b0f7e842820289224656e97798,0x4094b29405803f61f469ca0ac4d9c8c0f63efd8d90,0xa48ad46e486ec9adc42db49d32f923736af7adecaa1d8d99d5433d4c99c31a2d640c2b2,0xcf5c40980bf7da42dc8d6f7ed6dba4370b6821aa4d4a,0x6e84f4e84f0e84f9018a061a59c] [0x427dd5c65291f7530bcbfc467215032ee00bd2c16387d1919c185fde224400b1e033f3c2408424f9aa382bc4d8c8ce1374e8fd03b18612c610617c6680d0397c00b047df58733058ebc4da054e2346467099bc185f80011de21b0427607de9019fae136210a280244a441e39040042117039340238041ac8c2aa77041e1c333eb7600846823fe6eb757084866068aa0f1d80261035002e2,0x859c80094610b383d002d3a04229011084521486c0e9b004d31486c211303a6c013501e3853c83c710090844c0128d4c83c713dba6a641e38d827b5e31c62070c2259b8765e18f1e495aa0fddccd27b5e400b39f57b609ec62070c2259b8765f924a88427fbe400b2c04b04f61f50e8c40e25ed8765e52741087830bea4eaa549dd020d400b04fc6527085b260b1c3e8c8ce1917904690421e0c2fab5cfc5002ce,0x13951084410ba3c216c800b84013061b07004c286c1c6823004c3200251042264004a3] 0x36a85ecabc7078b752f8ff36d3800379a5f2f1f690de1a3e3d29e280008dfb0af4af06f3080434075d3dd80a008e00aa8c2b0a2288a0a1002c1a16b2342f9aef5a829f4b1b53a2c374e7fb73fd0059497d2ad51d10508540da84f557a0379f8de2cc61ae3d1e1ce75b1513bac1c4a3ad228828c2db7418c039a79df8285998cd4244808ed490613509d989010291c6a5555c0476446cb67e9934ecce7624c74a5254e010bc7ca06a6ef49b5098c1bcb2a93ab8cdf0fbf68ec29340e81f9e523136e2a8aec8c98f85e16adfcd2a3781bb915d3fd5a3e0b596688056dd545ce56f22a3fe046e7dca147bc147627646bb401bdd7def97bb8d97a6b0b2b342ea1226b73f91a57f970b20fabff74c9e46cb53585951de45703daecaf50a4c635b55a6c3fd6620280baf267d388892a2af3712bbb1befacd68e390f7bafd2d1732333f6c0079d13d683a9557407d437525c188a3c0529561e8b82e6421f348b8214a025e04083a91bcfeeed25d4c6d767f4f890733f76a74414be66444cde3484804978f87178f7b26338305ec819f6c016a0eb3a7243e2edf5ac9bd9199fd426078a2c86747872f630023444dad60400c7a481e850f098fb9d7fd78e0a2c8be9199fddc4077d2b8e1cdc184de1dac482ccd9a3d4612547b8a9f067ad552891503945da4d0d273405990c672ca2d2cdd0a539fb5221d443166564a2b37b1d3d92782b312023186c36a494c0040dd94,u 0x420da1576 [0xeede1f20ba09010455a62822b531492504,0x351b329d879e49d3b47480b0f6823f1409d2088b21180,0x4b58a0ea1cc11710f60821afd24188,0xc82a8a096c6492983b704a75d61c008403e27d08,0x8c69431c8286c05dfb47d40664e8fd88edd0579ac68,0x161ac5af62fbe86b50d064e5246f24ac998137558,0x4e84f2c84f8dba56b20ed594a0b22873116d8305a0d0] [0x8471f36bf3c32c92210b183f9414bfa841e6080d3cdafcf0f108c6210ad8331330c13c42be012921b1620f712200b121b17810866224017179b5f9e1e0180e0cafaa40301c196f54806035ba27ec80260add13f7841f3,0x32384646081500944215f02a0128c1ad605402519a781e781872f22acb8346216a206cb9e16e10a26214700c25cf0b10b3835ac0302019e7858844f7028e604220f3040340679e162160b1cc215704a080679ece2005a62e8310af804a3,0x601] 0x9d018733501078f956e4344471585fc99501ac571c0c1751c25cab1896783941c0468c9425407761203de78f42da8e0ec780012163328de83808e4a12a03bb0901ff3c7a16d47078340290b19946bd39707540c632208b381589933e34e44a0b580989d3966c0a29888ad8f81989b20ad608f39e5cd32044e44a38d96a87335010d39c8b56237c73ebd05d84b76ebe4c66063c4022654766ec3f3f08d633930c58b20930089948b51ec1d6802ed0f83c7048884522537a2757c1c0c7e1d4c455ce3c004008f00861760f68e03168411101dd879d0875d977515808edc27c899467c5a5415d044665077370f9d07c386340c454c410824c022651cd8ce480274061e6be10bd811c5a5235f4995014454a71e74809530e04e336ebf40888450083222d7c87265454cf1e7784713303ddf025136efc8408884562e5a11ffc62de01fac05d28e031684100458027500c651765cdebf210222116b285947fc1d564a7c1dc61e7869d02071628019c03112de4dcd0a243a0071af2d23883590c801aa98d12860f5844400a3740063bbf824cca533bbf110b0fd4cc59c2,u 0x300a4437e [0x6f6a824045045596482082d2c12412504,0x15cc698130401a069d1a4137507d20d406f70a64,0x810807c16db99be8db2491323bdb329d854e74cd45140,0x59570acb5a26b286b595efd50d0d2c99c1db8257ac38,0x1161cd2e60fbf795e7b0f7ef3e8218a009a34a58,0x35c64c] [0xe08522099ac00b89de6729a839789d6f124266b0037748ac74232f0aa0072a1195801714800b891a85e0f20850c086d7e2801c140d1e83abadd6521194a83abadd65211958130aa0cc66842148d06630c59c2168d0663003825ba1336400c02b74266f022f3,0x20f4406841e10423081210841f089f75f1352be3295820e33dba614afa820ffc5a00bec2083c2] 0xbf2a790659d48fafe3c1219504afba59b0ba20a7866a2cc90d91dcdc1074e9a2c0412a07bb69b63c607b71d0da49e80c79b3e3a11287c17cb63d79a64002c9b9a0898f5d240a9ab8a5b31fb342fe382819c95bcf20a786d49d8b22644a8e42fb7918b4318d7756832adc8741434f1d7f289e68c1498204082a61d0271845ca48fc19b5a691c33a59b93c175362e6aa640d37a435d12890fd27773c4e8972c8e3c3ad8484b20dc1180306f8d4c481ae3998484055730435123cd3cad03d0b1b54f4b6e556836b1568c16d121ba9a76df611df858656878e0c407a4f9b26449d16c4608c9764560,u 0x2209f82ff [0x2c624157db6b157dbeb0415e60b6b0412944,0xa1ac9c80d6d2bf615febce7be7d11681af1c641b00eaa4,0x2ebaccdd312502c82c82a3806042e5d88,0x5514596c1760bac82c82c9a17dbfb5e60b7329b0,0xeab78b233d0061ef1dfb9acbd864801b25632c558d4] [0x10ae210a6210cc20070210d6210cf801c140ffe9742f0f304292c0ffe9742f0f0856c0a89507d056ee9108e2342f6d6ee9108e240bc3c1f788210841f7b003a28a44c00e880b6f003a2,0x8401] 0xd4be25b46fc18b13c7a697bd060e895798e93140c2f69498056471c39efe82600fdd79e3d46613d034c0f4ccbc2ab056836396bf5f6f3f898a38e1a1a5357e0ba879028801ec4262b9e6d0056077bf1e26d81606c36f417d09339700ecae77e10c1117b0401a6ee6a5d880679b5018bdcb0f4207b104e2022c39b046751e23b54f7c3a4117b04014486f86a6ef5ec100495ec10062bb458,x 0x1408e0375 [0x834f142989b21140f5bdfb083aa09010410412104,0x22cb58a18cdf46d922c40530278d7b34142100,0x10902665cc12a66ad28601056d9e35814aa6b058d8a3d08,0x8ad3a0cb5905b19610c45d202d9491820c39d7b0791c90,0x6afd2da2f7ba5be5ee94b7d6cc0d6] 0x62391c473804123084021079805f2c46d9a0821629bc472609a706a00d9842060178842060fd700bc6b8446812e111a182053 0x18302d06967839bb83ae981f5e2cb9602c1ee872feb7d61dac80222821483c3082abb9b786086280188b028841e09d06b660c6970373f6a93e865617d30c1e157bdbb9cd58601b155c5b838302d0ed6627ade5776169e00681ee4d4356f40b6fe208196c05518021a32296057a4486e4108314b58c62421826daf74,x 0xc08401e5 [0x2afd410fdbe87320e40e76e82404104104120c4,0x22280b640c4dd28fa14c12e610407b2c73ec942100,0xc9c32b640cbd94b3b981069acc19734454cd688d8ec828,0x89b1641ac3988bf40d88b49183efd9f7c83c97b0c50,0x6c8ab698aa2d6] 0x1784046204a1a42604a241d604a2421602c2 0x2f19614ecd661e980dfd688b9287c230913d360c801002c2dc0b409178116dcc0400417aa468087142990cc9bed45a11c03e07bd454d981a510b7b816700fceb80acad1202a0050781b6108115302620631020e8ab16c6f22a88c394a8238e8620a942,x 0x605003d9 [0x2bda0f3c51960ac259a41a81ec9890504104120c4,0x4bded4581b365496ac64501ac099212c0d873f458845240,0xe0d6c62ab04d594b3b989694] 0x9f8417c60eb05e2 0x477da4870bac463ae453a0a7b6d606eac150b18dbca3c182158a080e312d544182b55ace2d86526c93a3c11cd9630a5f4e2d90,x 0x40506071 [0x60fd1f68047607c901204c09012410410412004,0x215b09e47d94bf490c7ea214fd08206d8fb44a00,0x1c19bb371996eb1ab301988554] 0xca50fbd81 0x8ae9a0d49759d44200104565d40d0ccab012dd083d1f028019970742ac45b647d37795a9cd6,x 0xa04e615e [0xa36cca74075ccadfa3ecd4013911204c19215b60b532604,0xef65ecee622ee882917584c61038810807c16eb9803740086a500,0x80fd1f6e8fbdb7b0050] 0x2988480bfa12dd9e125bb3364b7666f21b3 0xcdc67277c658e1c89b5180128262e7cd748b3839afdf69265af98a8941a7dc55ab84c121dadb60,x 0x805028de [0x31a0b1c14e641c00ecb9eea24049156d8ad8c125c4,0x7b4d10526ded6d61d95207102100fb910690434f1cc1cfb421c0,0x1637b66e303de8b37d6010] 0x216861106e8f85b204c1 0x1f44ba0d3271d098d714095d3e89022570c6d81dd536c65312896142a0626cbd279251c1a0,x 0xa02d08f2 [0xe45123440e20423a690415b9f6843f220c06066b5304d24c4,0x2831f9870fc7d19492b7414] 0x36a220eb009842164605e094881 0x17cb94d459ed4f6ef5ff8dc7927199d57bcae9e9b6945b4d7deb4cc4e186e69a172,x 0x603c865e [0x20c58869dbb0edd197fc87b050460171822b630452504,0x78994c7e43da868063405480d04b61804a71c4084a0dd88] 0x2cb1a8619be1 0x85bdd99855636ad9606a75e46e6ce37cbc636bdd8791eecdf1590,x 0x603690de [0x2fb0e660c188699fb0cfd196fc87b050460175b730452504,0x3c4c12608c29a2a02092b1804a71c408403e] 0x9d015bb3a24b7674732d3 0xeb92eef78a12e76d944f95f86aceaeeec6371bfbfe2f4cd60,x 0x402c0549 [0x12ad86ee5141369bb766324128ca72020004124d2004,0x15da48c7558706ea70a14] 0xb061a1 0x2d33b388577f32a5aef385b2bbbaadb9de52294,x 0x402e4161 [0x4aac545016e0d8d35409801076d1450c004d0492004,0x1ae32617b3b9895784b4414] 0x17f039a41 0x727a7d6d11a6eea4aeed95534638496d96b2e54,y 0x6020915e 0x1330b6a2a003e6c6b2434d3d869e78f3d893411805d6d8c92584 0x9f815bb3f24b767e73f53 0xab4e37a5d6ee57cd7fb5c354fbfc46ab60,y 0x20208261 0x1569030bdb2ac336a337627b1e604c358b102a2cbd0460052104 0x13aa1 0xf4efb9684b37c9aa768ae6,z 0xe00f0 0x429cd24677b4918051c8 0x75739e0,z 0xe0470 0x429cd24677b491804dc8 0x75739e0,z 0xe8471 0xf1312561d551d5b0dc845d0021c4 0x129bfd9e0,z 0xc9471 0x321b1ec4a281412184 0x1b3d1c0,z 0x881f1 0x62b4018411c02104 0x59980,z 0x920f1 0xde6294840d4020c4 0x59980,z 0x601f0 0x1f464e34a18 0x2960,z 0x61870 0x106fa30e08 0x2960,z 0x780f1 0x391444dc020c4 0x2960]
def d04:List CD:=[u 0x4811e11f6 [0x41141596282282d2c104114124c4,0x490d642300e821cc1567eb03e416f6c8246244,0x47b36d0450a62a0cfcd945045a5121d00,0x13280304b5820820c46a30a7ded879e69d345240,0x804a75d61c008403e0b628f3007882884b05a08,0xf568fd8e9fb059059daa2825ad82492983b704a,0x39638dbd9433bd80565cc3d8a12c79babe510501992c,0xd5a48cf47dd23e41e7d0479a6282328fb8958,0x387279872797427b7b0e84f8ca5fec42f6d49643b6f95ac8bb5641cc5c405be8c] [0x521f10ad8061310b62102b009a50657912cde8211b0b2b8f9035902ef6b8a201e234138f26c4010679e16ba44219f3c2c431e3108d8602c06804d718f5bd10e81c80252f3c2c63c747a32e43016034026c7dc2c4236068cfd8762ef6bf3c2c59a1715e51c50ea72e6f888eaf085ea8c7ac42088ff3c2c96f0113f4852771797add8421cb7009adcf032072cc03024196f5480603173d8840c2e83f54,0x42160184816883dc0309f3c0c16883dc030a0846c03094199e60b84286081568211b00c26064420e104020277b2d50fff5c2248b0d96ddedf880b9a0bc793601440105e8211b009662158442b60180812883cc0301e5110ad80603ca2215b0867806040e5d80602,0x2164402588061110b380612] 0x6fd0b543b6cb6d91e90009761061d22025f8631dee1e7ef612cdd0910e4e31af7339e9ee47d577aa7930fe8efc8c28531d21c008e3bd8ce966e212a0b0a80000725d5151a06da6c33f21cdae4408fa481d140448a383429c631c97be0731b5c9eb5f7f0a2e62c5814d1f21648e4c6b558326808d0a6230cbdebdf03db1b3a57339a03a7c38d771d7291363e44e8806c2600472e5dec735593452b89198e635f931e25184f5d0e0f77bf30e4c640400389b411d71dac33d832ef7c11717823f5781b03996451ea5673d35ef075793cc9911966a0919dc2802ef76397b8e253447e6e5e3ce86b2c0b30743e384ba1d8c74f8af621a936e91b6e88bbddf02045debc99d2f19020a74dba6031677f2dee0f00e4b9ab045c14eeac2ebec81c5bdecd23ee0e0286b2a1b0d7121bb0604ce6b8e73e3476eccc359a9ef765d13570588585049d471b441e4439021aeea6aeca90a60a7b017f54006fe0cb2705b2cfb1a2038b5ec633c78eae4e87647d3d5f2e0df9f319e9c83ee3e8cebe8bf9d8894d23eed362e60d21c02ce9543f0d974e3a4116e988f3e0de362578cf4eae4e5086ff45ee835bfa91f61bebd7b98cbb746ad889a0460eace88ebd3a55ee83d178bd6e56bd7db8b6f1b79c3da0bb5ba7e37e10e7a283ea02f3a5fedd94d19fbb0059f9f2f0a547481df5c5e2f4d79d83427ba5df2aab5c988c314c6c30d32a68f72,u 0x520f0877f [0x3415d62b6b15758af4c5157582d8c529c4,0x2e2486b411b821eed016490a8002cf83f76a864,0x825b8238f058238f098e315867e08e30278dfb41e40,0x390908101f0278cde4b18a1ac91623bdf7b86580,0xbadf1b136c6294f802c82dce1302502cc2a38,0x3362b28a59b65ac6415f6efa09730561436ba5b0,0x1efb34c5583ec2cf2a1201ed6f61904d9554,0x4ea374a83732b3ff44b8de498741bca610] [0x4378847d8a3d085b2622fe7ea0dde4198f63a04cf04442e833059083ec2ea85f0101c882fd701a10a28178ba3d085b30bc5cc024214b0bacb407fdcf88437600846178ba5900090840c0c1d8f882901a107f813faa021a738a03464f550042741efc1480d083fc068135b27d0bc5c410a585d02db65bab7570847d605c6ab756eae108fac0b8f00446,0x5d9e10ac6138582c21056008560608124153f842195fdb4a10af8196a00d085520a9fc210f034730bcbc21a30ba0340fd556ebb909c235baee4270b0408409c2c01108270b0409c0110d6e84e1944a56b74270cc216f00602,0x43109c2109c2c10c482f17204201f390bc5c210f030046247c2f2f027e30842c10c48216b043120c91c216b00433] 0x727455df03274f3cdbcfa4d4d6b3b41628e9299de300fe4bde471c16382306901b1d3d98802c2ed06723dcfa76b1fe32c0c087d0dc1823df429ad67682c71d2533bca833a1a8f302000e2ee6387f69800488860878d8312ecfdfbd12dce50c440798086186d267ae6de5ef89bf54f58c2f59d0c01103e6011735a5db36f3f7b7e4cf6c173041e90d1856977f043c886e3b4db75a65833b0606c0040007c64df69a7139f80dda4f4869cbd9627e0603dfc33161768338c6043a77789d6f810b0404241e7d99d3fefe1ccb7a106581c051f50196f3fd742ce5f54f61c0ea87bc9be812bbaef75401a4d6b3b22083d2355a434440ddd3319a8338cc2aeee9603006069670a6da8e5e258dac27efd4dac27ef890502a6da8e5f0576100bfb227bf995d5851879811e47ded95ddc0603fd76f29d1ec9c445dd2c2e168f0c419d0c080010c50275a58e035ce08791ae57aefc02d013d4388d5c1690d792384002148371205141a8c017817a8c837a9703c403359d0cc2086315a58e035e7d6081b376719cdabc05ed1baf45100c2f59d4b73943dbc5690d79a00004674a463d235bea7450811113158e037821e49e5407724cd0aa98c67d122de7400303501d713342aac955d444935a758204935a0,u 0x2609a0af6 [0x2c82ea24045045156182dac10412584,0x186330680bfd49f41b451e622c81601d7770c64,0x5a5ac45e23ec1151486a1f80b61d79830e6fcc5421c0,0x4da20815b2f6d4b1c973546db5bc117947a6c81c408403e,0x39f202c13266ecdc61be85b36d5510] [0x2931b29124583f94108622e8f10b646997108403f70f819108382cd45ba26af04f4707c35bab84471250026143c9cd0460130c00c191bef836840cc58369c026180904cf804c383e18267c02618e08c3c760b7ccc882df2066380562,0x34ca2699710ac4a292fc211c1db29124583f97] 0xe3a10480bebd3cb7b4bebc94c69628cf22658515e4101fc6006e879d3598fd14ade5a0e66b5981158430c288adf31daf751d8dd76ce581000c3bf95d6246dd9d68412b40ceb69a050f05c3ef1316242ec8da8412b41cfb79a050d05b5a5ba3135cab1c1410a694f9995d37d898bea2af075a693a8bfa09f181ac1ddb5865ea89d87bf6f0bda92afc6e31f3d32107710895e7271d6329c6261449226795898cb7a9103448c659d789ca444cbb22115118cbd22c6962403b04c62403e9a7536dc1200a0,u 0x240a802f5 [0x183a907003bb75bdbaea2404104104120c4,0x398739f60e248218d10a681c707124121d40,0xc4527d0a608bee20f22f20e400b46180,0x2bb2f6d43012c45a3a89372668c11a20a3db61e28e69c8,0x1a0ae108622cd0f6a86b371842fdaf7a8fb1090,0x3170ad60c62c64c] [0x107e2693f00804210b05978040316999c5e3e0fd907e93e3e108dfac261e6a402fb80541076d805421089804021089804a21dd189c12bc9dc211ba07a15fbc9d9331e18879fc1db60c401bc0846c0683abc02a25e4ec9b015e4ec9b112e1121983313,0x4210ae111c582673] 0x1c672e729f814cf8681a9676ba2514c72d0b6ce095ce302768ea32a9833bc31b786180834a5a089ce8a00decea60cde0edc0860535e389125f95370e182290d34bcd75885f1ba34e68132da96157a480001db048b4a3031ad0bb39fb6e01473a09318c33d3053990119ae079f4810c6fd7aecb74cf8513ad44495938668b779c848651a237e98156e6be04d461c0c3274000fc6447ee08002b6d479caea960,x 0x1e07b0a76 [0x666e82ea240410455b628ad4c10412544,0xb0afc09eba0c358222d035fc8218c10e641c010a64,0x54cbdda33918c0253ae38810885e22883c7d04dc8,0x20f1246cac4cf7d9a787ba17e97b0c90] 0x9ce15ba273c96e89cfc1959f9a7e10c8391661ab206770a10a5838f3482210885d0e21648f888562f70d8a514eb86c745badc447160cad002609a501f7259a50234a188e4234a180562 0x1258a18276c1fbcd722cc431b354d4d200c63c009b3dbe91228a0899544a8cf04a80068c65847d95e263a3162452f5f215672d3875ac65420c0844a644c6329916aa9258a18276c1b91359b35dcb0eb58cb8c67a56731953218d00057a642dd72197d23f18c0164ac658d8230041672d3b163007a08204f21f008022d12,x 0xe06e20f5 [0x1283af0f640f90e640c80eedfdba890104504120c4,0x2830650490d61cc1e7d041c81071cc1425c0,0x6586b37181ecbdcab3f6a020a4dbd99b4a585b6eca928a3608,0x465c441ba0bc4c] 0x2588392117d21cca4e3e50210b00b8f683b25ec4211b072f80543340d804b2341188422 0x673a16ef8c9a997782558b6c538736895d9e39b0c55c3c91fd74208b53745d159762841604b806db775af4c031c27abae7c1017c5749af0a0c3331d6424202e48b9c9d0a6e963d39d061026b43a8d703c980,x 0x60614266 [0x5404f9a1ac836001666a8641495b62b6b04124c4,0x28e20422d7efa287b144480d6c1af0d622f7d86b40d40,0x36d58607baf642cbdea30f6092094b0cacdf51d76c095038] 0x13442b753465a501 0x6f36117193d9a54cb417c00cf075116e9bb194742426a45abbd7028d24916d80be04037424e0ea955dfef09e8c26122e2f2,x 0x604f20e6 [0x1173e1ad035e36c857017d82ea240455f62b5b14524c4,0xa082c8a3aed81281da8e2042117aa63241480d6c1af46140,0x30db59d0cf4c9d2b2010] 0x12fc2b752fe5a3c1 0x32accd15f05a0cfb70000015cf12c405d4674cd717c30b693e178cfb740600573decb6bbde239db50707312,x 0x80445059 [0xa8cb24188ea66a129cd225000f7282404514120c4,0xd830a99dcc1b28717674a928596ecf1405b2e6a9d335108,0x15c64c] 0xe686118611b21a22061 0x5a330b6e12ba0f70c8f276c9974843cef741f077237db259a5544d1c0b210cb3c4453ad37c57edf258e410,x 0xa0328772 [0xfb1f6b58c90d4a724e9e1315074017d8adac525c4,0x52e278fcdd661918b2cab4b94782c] 0x13ac2275b00984b744eb97426c1a312dd13af83473 0x623faddab164dceb7fec9f3ccb2ae25cbd250772ca1ee7f9650b29fb2271f6aa2b2879cd1c0,x 0x80438071 [0x6b3750521176e82bff7503642180ea2404104120c4,0x3b1066ecd8617b391864bd92b43632ce552314023acdc8,0x3c4c] 0x8e3100962dc44711659e1 0x17b1953bc8df1543690759e18335e51ed1f6458994dadb0ede72115574fb62f447bba0,x 0x4045825e [0xe73d8220f541180f86a8240455d6082dac12544,0x12c15a84817b491876e094eb0e2042e4b987b0458869940,0x3c4c9a50] 0x4200add9a92 0x1744bdd8e294f85c66d522b8a6336f6b6530739ba8be924456131f6d6d4,x 0x803483f2 [0x83f4588619f8b8921ad0460179822b630452504,0x1d84e19c4f2520788acad1e5196b1d88] 0x17f60454c6080c80210add13a3832d3 0xb6ad2692ebf6fade89ede64968feaf5ef89e583caf6b39b7fa6153d6f60,x 0x602e1c5e [0x1f3eb2166e4332fc35e830068438130640581b6b04125c4,0x1f466ba0d94405997b8054] 0x9d615bb3ae4b7675f3473 0x355bed7b53b8cff59d733a377caa5975c4e1a6ff055df360,x 0x402728da [0x10dd0520710213d30821983e895b9f6843f220c0606dcc125c4,0x1ea60183d4] 0x844104c1 0x6d5f26bbe4f1b39dbadfe7aee7943992,u 0x2500f5 [0x11867a3eee197b10104a188454051c845cf97b210c00492104,0x10bc4c] [] 0x9bfd89431e7da35d55690,x 0x20240771 [0x25951698130c65ec648a3616d079e434812a241410412104,0x2ab5bd8] 0x7dd61 0x1e77fbc94336b77f518ae6f6a96,z 0x1c1070 0x363ac11adb36184cfa59dcc1731f64a6b14188 0x3373bb2d3f6d14590,z 0xe08f1 0xfa322561e951e9b11c845e0021c4 0x129bfd9e0,z 0xe0e71 0xfa322561e951e9b0dc845e0021c4 0x129bfd9e0,z 0x85171 0x26363d08465002244 0x59980,z 0x890f1 0x180615c8419c02184 0x59980,z 0x60870 0x106fa30e08 0x2960,z 0x60670 0x706b630e48 0x2960,z 0x64270 0x306d830608 0x2960,z 0x44070 0x12960e08 0xd40]
def d10:List CD:=[v 0x13435407f7 [2441,2444] [144,1680,2448,672,688,704] [] [0x822bd30410455b6082d8c10412984,0x6e60b20901041056d820820b63045a504,0x82bac55410750415d6083a82e864,0x6a08b4822820da09216c104121140,0xd222f0183a822da2e2082486b41180,0x1e2c11b7034fef7e2c1e751792435b08dc1465c0,0x10f008084080f89f6d0062e202c41f25ecd88,0x53e00b20b2eabb741382502c82c82c38,0x32eba0ec5dbb22a386e2bdb057d82d8c12a30,0x4a5864104134c1a30aa80828832d58ee0a8,0xb89218c1109040952400e50b692e5036080357d8,0x2db2d530be8388a0e22838933afd2090,0x542588b244189b140180314458a22c500193aa6,0x3b606b69bc299b0a39bf85abd96af45aab224d05df454425be8c,0x3575c3ddb852a70532e0021a17b937b00bb34ffa35836b183fc106b841df7c1cf740d6,0x2b25879ee28f69cfee6d2fcf4b949f0918917b938513ef4e4f057f2b4,0x8208a0820820820851b7497d4a7e74b794a31e,0xe7c8ab336655204104904114104295b46,0x22ccdaa399628c952666c459331d6aaccda23042ae0,0xe307959622cd9a1311666d4dab333688c1e52720,0x1534104504100710988b33668c174666e0060,0x4514954504114d0453451449c,0x4914515504514905114124d9c,0x249341041151041245241556dc,0x7a018a061860412452414492451609c,0x324fe43fe81041041032c40c3dfbefbefa418a,0xa129f82cc22fc438dc4da5304058745b864a3c] [0x413442399486c4134423a7b77d6eae12d22197040ac0578211cc16c042398df0c5d96174420a0cf0c03191484c6786018cc30984201add153b884216174198e0129c42d88e8611d0d803622ded8dd22340f8055234f7804e2,0x1a7bc5e5e004203441e31a7bc5e5e001a08441e34261d6eb7129221a544730c21a1842f8037200b9fc42b988471208442808472c0847219e78847219e78847c02098a0c7eb756eae111998201703b8108e7eddf34f7f955680488447,0x34f58f2622022d3f10840c16fa8ba0c421a70b0980425aaa064008843c2c22886dc02a11a7ac76b1081c941ac379a2dd5bab8447b620086c0fd70088469ef1797a842821a7bc0aa842821a7bc557e210d4869ef108842c92fc285c5e5e111b10043710b24bf334543e20da20f3008530a1f5bb8054888415,0x216497dabd69a4780f0ac5e5e1b7700814336b100110b2821070084437c3176981110828507737042ce01097fc96507730868c02129804884135bb8054c8841c021a97151a0735baca4f4886bc196a8ba0c460a2a143c760e9de1ad6b756eb2911ed832d6aaa06400a910f1d83a76174188de022a143c760e9e0d08b27c418542fe5e620e9e1d410b3838d4,0x3c6063bd62311df4aa1084a6943884c0874d179a06ca43621644be3c16230a5707b9842709a78e26367a68bc96c6216443c51d57791d88c074467127c55e518ded44c9ef114512ef7d345e0d496c0cf8a3aaef23b119c49f130bca31bda8993de228a25defa68bc96c0b7c73cc46c1a2108463347bc4bbdf4d1792d80ff3422c9f3da210b0406bedcf34f780435e013156e8a5fd420f30406a60b22104d6eadd6e223e3072380576169f8091082640122104d5edcf51a0c8e1e33005ee681b200910828681b2009108382f35,0x178f86110838347434158f27c42099a17c79362f2cc249841e99486d020f0ca43618442099a7bcc36eb121980d01a0e9f009b008789f43c96080d40888412108383ab2108383abc02b981d108240240e884138f0188c295c1ee6109c269e3898a7e9a2f25b1885910f10846109428ef38a26bef23b1180e88cd051cabca31bda8993de228a2d7ab4df4d1783525b047e2108c212851de7144d7de476d4fb10993ceb4df4d179fa613f,0xc10c842ed710c845070721c60d446282f8bcb634f79484c5d9621910a42603441ee08150f480d10ae60144215cc5dae21b485a4e08441e18a130eb74540e20f14420884d10824037c2104cc20f4a1baf044c36eb06d9804f6,0x10a982e0220854c1701e0111998201334f78b65d4880d1086a219060219084326018cb421588d925f84bba390ba0fd5b6beea84bb84bcc021a8bb2c42a60fd4c557ee10c871945e5ee10c891345e5e21b308909fd5b19eb8864334f594172,0x1086ac22318058134f6269ef1084469ef10ae469ef10a0469efc0843334f7883c234f7886d2f6e78851c10099a7bc0a8857310d982e0234f7addc9223d90021af05c06010d782e0c017a01510ad82e03,0x754884bc110d2221a70402421b04421a88028859210d580542c474233c71086a3] 0x1a1a0a37883c77f387f1f8d6fd594c4fbd1ebf9df23b1b8202e7451b233e86828de20f0e0577484e17cae3dbf565313eecfaee7dc9ec6e0d146c8cff7d735dc6f4fc21d0cedf02829c25cbdff1eaca627dc8f67cff93d8d71a28d91bdf0e0a582672c071857f7d594c4fb21cfb2e85caec7c5146c836319dfe0cf5387f3a6281e66f8bea3f17b7e87caec7c5146c8bbc86ea588a16bd539cf130474601b28a9a038c8ccc2deecd43154337467e9ce2f82b87d574bc4146cc2dfabaa372f2a186728f7fcc9b30b6a96be64d9650d190cd7b17c47c26cc2d92a18668e81f865d4d985b25610cc7b17df19b33028f08008cd299a5082ad0b1c1aa12f974fcd10c680ac72e01b3cc070bab61839c77424f2f4b9d1b222ca8ba02679469ea47ead43e033c3f8eae9f9a22f8620280458e640a5ccd985b1dc4ddbcfb397cd8434a7995e4db448f137efb2a2cff373a10c62f2699251b0434291a026686fa0a8601ee07019d23dff3a708be0289fd79b9859636616c3b22e35bbe798ed513072db179fd898643785cb6bc9df777eda32ac0caa6a8107ff9f200cfedfade9d86d5f50e3ccdf206fa03311f7e1363d53110cd3cb34a81ce64a02f98efd074346aa055212cbc5001b30b60ca9ec063bca7e13d27fe1c3c3b4a7dba7d8d71a28d9542b11d288be0b2048148fb4d214cd1afd8eaab9e3f16c4a332486850133437d054331780cc0501f2bb5e6c0616517c8086947de6cc2d906d2a5e80e8241877f97e0eded0a7e1bc82280bf9fdaf364530b2c67ef1ac97019b3548097e2cd2a7e768620aa86c3073a019a95cdcb79c22f88fc68d985b22de3d1cefb7016f11c4fe22a6e91c061cd2a024be96cda1eee74d3ece5114ceaf574fc890c543900cc05110e6c0aa5bc5f7e71b30b65594fbc832c499aa3eaf7c5210cbcde12cbfd5430cfc8043ae1fac2ddb02963282672b4e7d887c7f5eaf63a28d98467134fb395819443e1fbf3784b29b6cd09492e608569088e1c0b3f8bb8defbd46fda5015950c33eacef17c43627ee6cc2d8fe60c9bce2b9aa18672525992e2f89d1ae26cc2ddaa398285cae644a86198bec1b30b64a861990e73b242d8382cf23622ca0386c8b425659d89aa8ae8b3219a472f26cc2dbb42ce023262ee6cf35e95966e3969aa8ae8b32198be6cc2db25ff87d4b62e3426686ea198bc067670738be21b30b78d095966626a8ccbcacaa1867da9e22fe801b30b7680e4a1425a19ade5e8bfd19b30b6ab5e9492ee5b366ce1c644c8a18662202ff36400c2ca6cc2dc247f57ab9a74517f831d4b42b9ab7e09b216926894e4187610fb251832d2c0b2c085993e1f5643421bf83d6807082bc3f1446c8efc5001b30aa866528be21b30b61da04902608c6aa8662f9b30b61d928ba0264b4f660d099a1b801fa463280bcdf12caa1867e2f52758be02900fc7cf00d985b22d133374f6850704dfbb4e98a03a2a7a2c80ac722cd9182caa1807ac61c19f9f0f8fd4c4406f8be05c6407f100d985b2ec9d91ab4fcd368413f8d7750c33d3c5ea4eb17c4807e7e7806cc2d84e3596e98b4f38d5a7e688622680bcdedecdaf2a1987067f0f8fd49d62f843001fcc036616c8352cd54d150132467d1a704c4c1a14f6845405e6c0b0595430cfc5ea4eb17c0b2203faf9e01b30b64780bcda0cd9861af8fd496e47f5f87ab365950cc50cc5f6c58136616c54fcd303d3d48f819f9be25954313c33f17a93ac5f03cf3c036616c6755c654180b4873821dbf4f336041c49a54074519c4d313d48c930179b66eac16550cc51660cfe103a53ac5f02e02ca3cf00d985b2df3d35405e6c85d54be4fcd10c443f8c6fce74e7ea483ac050036452fd066cc10d7e1f1cebe0a38c00d964a3419b30435f87c73ac400d937c1e97052c133958f36694fd0e44f3f8828d9b627c067781c87b6f38287af217c4c8bf33ae325988a50ad327a09fe225d222b3472daaaa8bf602b2daf6557f4bcd528427a229eccd197e7210aaf592c0219752fe5ed79d430230a570808f70965ea707b768a862aa6602c30623f4219a2534a3c061f148e3f2fc6f0aaaa02ac08afea7a86c0ac2736626660250511228c1833f75091c5f057e1a208297e288d985bb3e2dc16894415ca6cfad4061f5a0db571d88f35c7e7596e25bc6c993407f44ab50a048c389171cd5ef4e17d489f019de4f8de0721ed05723bceaf83879e836e58b705a2518e415caecfad4041f7a0db65efcc601bc44a8971fb25fdcc44ab50810230e2456623a24dc76c9ab687bc13946f44fc3113b5e7f85958600365009551bc3f425daf66d1933da5985bd59101550ce90cfc517fcf8d988157d21da51b5ba511e0d238f45cc90f427100684370660ed79d69c0616542ce5057c3eaf57e0e9035043c78d91fcd12753f20d3ac7623e31f9d625bc65b8bcd1cb6042c9a3c8226792d9530427e3f17828b56ab429fc0a24566d774c46da0042bf58ab7a7e22197958695894d4be0324a10e548109335a102052c13eee57d433943393783a4c317c843cab5e78d985b5af176bc48d6618ef2dbbed1aa679655851cc109f8f9fe6be2437859b1b7082fdc2b7a76221901e5695894d4bcd528439320424cd686052c13eeedf86e57ce50cd49e0e917d0d1e78d985b45fa766dafe8f175bd377152925dcd50c3317cd985b96853c7505745ee836e014cd1af052c1339449a5eaee0e901ca3678c001d55f22c33e545f1276942836616d121da51b56f0544a0db15456bd9be9d439292cc970cd1997936616dd31caf2447b5843317c4a003664053005d244c71ed610cc5f36616c52d5a728d8ea757367885334c1ac1da214cd106b1169c07452a48cd1af00df052c25ede5473046360314fc27196614ba0253b45fe1d036616c2be7052c255399525c5cc1a0db19c4f850cc50cc5f6c58136616c557c331cc5f80d985b114530cab22c7357c333945f10d985b41006dd3349956c2583a439a28d9c50ccb0cc5f6ad7f36616c550c332cc5f6bcd985b048b30c7357c3317cd985b14b95cc8950c3317cd985be10005148e0341bd4339c3347f83ac5f129bf029096500d916c411ac6713d819633096510492b4cf237571d4051175164526e5e6828d905c5a12925dcd50c3317cd930e16d1024c322444e648696f4de7164a4b325dcd50c3317cd985b18cab30c7357c3317cd985b0049554a50ccc17c3d10d985b24394c4e90bceb48d9b50cc383317c3b100975a36616c2bf481304635543317cd985b06c92eccb254c1fcd9c0a6174b13668cb2e0e5466cc10d6cc19533c393ac27a9c42616700d92354fc0419b8c11bc4b202f83633ac27a5280816700d92067d1c77610daea2595033648451fa5bd03230cd1ae020654310ec1501c2027b6b26c350244844d9e02a616540cd92083194314fe694155027bc26dc4876766e02896540cd98c1206720cd11a591fa5bd0323037d85a1525e42de4864694cd0dc57f07d0e486842de0e70bc44296f238a0036481ad21706b33669439f180b7839d0a5bc8e2800d923923d3f1e4198d449b1dea5d503205d4d2126ee2595033648259b3043538e19b304351accd9a50e540dda138c2de0e7e0eb128097100d919d9b4c408c10d4e3112fe0e7602fe0ebd2217100d9d4876946d5bc0736ce90be800d9145124c57435c17458c44812727e9698d701c46a55345ad4951a721de5d7842c9bba2c28a91aaaa87eeaa74ea6ce02aa60c8f,u 0x3609a877f [0x32c646262b630579822bd36160b631492904,0x6130f78a2c32704546538b89218c1411b8e321a40,0x11c604cbd9b11defc5f6b825b8a1af11173ec966500,0x1f5431349b005d99c9281658f1c8484080fbdc71c8,0x531c1d450d60f7310d06158ff7ca42a5ea8] [0xdb63884371e82a1f0869e2eeb9004265bab7426ff02cb45bb1f42197020140ac1c21a08266f021a20cd7c08842ae1740b2f00426bfb654215cd6eadd099bc00c50011056eed908fa35bbb6423eb03f54084615bab74266f021b44184d6e84cde0436912add61085a3,0x42d084358dfd09bf25bab7426fcc210f03472099b1085b138ab142a1f0ba080b8021b05d084120ba0c215f03473086f1] 0x8514f01decb8a8482eb86509e04ba7df467c505f751c0037dd46d84769d10077041e77783f4d6b461da9861b5e8573d591dff0cd41ef520c10c6ab0318be9615a89561d00f12b92005c79605b9f810775d750926de0d87a2d56d0ad73690f4d0224a0cc61af3c402eb17c79c96e125c444e611c02ed4d7b37d953041b5d3f6430d931c96002a77d170aa2d0906d031039ccb45714e846ecbedf24a371d110233deda0fddc4039cf88408ab860f5c014b8c5a2c62318e536cf0610809fce748e0,x 0x140570871 [0x873082198749a10bc3590ce03b0a2404104520c4,0x26ec1506b2a8e3d90ed0140a02c298a08e1051c8,0x326b681cc4589b5a190ca6046acf966988654] 0x1046400dc842208d81c42211d2a13a5583b22bca18bebc42060e9700a8b07eb1089826933a55948623a5580552 0x1194bdd3ede19c7e735245676b30329b623c0bc3e2ea0704c32f23981c13dbd0630601d66423439e71dbd1e4ac50e306800eb13301282a47ef2810716f06c60c8f00136a4bc9424c5281033ee1968e71632628364ca0919d5349c4cb9b69220f0d5b40,x 0x1406418f2 [0x624a30dd067e433810c241515862a2cec10412584,0x196760931840e004201f04314b19fb151c8016cc3746600,0x1b064242f96560b50a43f67a0ab3059071d8a28,0x86fd46cc] 0x14181081a31b417090c6fc206e0108c42c88847c20690859c17011418c0216705c28210c09c021244041 0x85b545218dbe23693178d0a42f4656db52f7c872ea25da81747f7b62ad9ebcea131aedd080a1fd7b80aef9752313aa520ded60e8608019f00be39a470acd83382e1ad3e04a4b34746151e8ba90823210f10c699a39b10528423b941db0d1450,x 0x1405c51f7 [0x35994e6feb14ada091c886021848bef75bf3606dcc12a04,0x3d6445d2286e654e10780908101f15b9162c41b0ca76a600,0x8c9802cbdd9b0f6087b50105460b54c4aaa421660a8] 0x4238885811337821b28335899b233498b51c068011088a669316a380d00221130080c27af07564216c4d6f080581 0x40cb5d2fd6d3a6a0c495bb952789a1055486042186f40db790af3ac22d9e2b888e903a1f8beee3e628446e2ba3a517c7e86d3c271d1fa1be767b8021f6daca439152450550,x 0xa03e2171 [0x931c65ef919239dc666d054e44c01303aa09012412104,0x740dbabaed4c9868d296005953b46ab290dd8d8a3508] 0x4230fd72100a83400a84211b072f80543 0x31b171e315f8ad586fb77d93673c906fb57e66341cef6f7a654e3743c57bbb4c1c4171073bdbde99538dd0f1bb5c585f462c5a0,x 0xc0321171 [0x956c14f5f264fd0620deb63cd069e44c0130240452184,0x13a4b6b1536c193474a1894bda6b6b54] 0x1a6406e2ce0154ae2e6054c8c1d08530c020914181 0x17d32a62877b99e5847df17512c7ce51cfb2ade6a2ba65eedb38dfdabc9a99a59ea2c3adf0896eb0b2654,x 0x80318071 [0x4f983a83903ef018fb41178fb21140f76a8241412104,0x16c418eb43189230cd434814] 0x180a1f300200dc40680372 0x4cd2c92eb7efdc4e76d6ba6b93b56d9e0f6e885b4dfe715d52ff3bae70b3887bd6bd5eccd0,x 0x1603028f2 [0x25869496586ac0e65ce64814566178a2a30a037b2604,0xb569a0216ccdad8c8b530638b94] 0x447c186ea30de049d4e379704fa64eb31bcb827d3c477827c239dd805f2081823bf04a43094881 0xf8d1279bc0c2a493c87a5567d935859fd62c9d5d2345216d2d951f64767d93593816,y 0xa01e15e2 0x3d8837d193aa69a584664511992c05997e0a32e037b2644 0x79388154740c3486dc1e43aa1 0x37745b676d945a9cff5c8b4ad37a414,y 0x20184371 0x464c8598e460a3ca23f67a5042109c84600d2104 0x5fe01 0x1bcaddb99da2b56b3f39b14,z 0x1f0070 0x1d11610c4d89b48184acf5b0b4a181e67ef5041c8 0x7ab49c73f34db7dd5d0,z 0x102070 0x1d1060a83481894b020c1c8 0x51d8e7810,z 0xc9572 0x2614d2aa84a328037b2644 0x7caf1c0,z 0x68070 0x50690301c8 0x2960]
def d11:List CD:=[v 0xa01ba15f7 [2441] [144] [] [0x55860824bd304125698a4b5304129c4,0xec16f60ba090104515658208ad8c1a584,0x310fc1245fa64a109c9a4136d0f6087320a00,0x4a08218dc98b11defbdffb81e783dcc126966240,0x164164161c020210203e27db4dc71c8,0xeaa286064b63626f6d81b6b04a8c017599ba724a,0x415401b20b212d9059055982cac68,0x959597b6f694b08f226e315029c636020b2cdea8,0x7a3eec58be8388a086324318a0a408401292,0x4118a1cc50f66ac9d9730862800c3417a61aa6,0x528125d0428da3263de4fde9c9e0021a614cd840b20cc8c,0x2678ec5ddc336750c99e3be07fcf81933c7620303a34a,0x149b8b2ebb0b2e9b8f20803860d7a7660,0x3d74fd01966f7e8062a186b4dc49b5c5c] [0x1200b04214301a0138c436e1120bdc9669e8878a0b60cc228ee0403127b87c5cf603570878cc1d2b7b87ccc843c66037c0747683a5c46802ebd4394442b60341fba8bb4c2ea910f1d83a75f6ed9a7a2880583abc0311fb94cd3d17b74cd3d1130ffc48bcb3089180582,0x1edcf50865f4c804c50755806220755811009a7ede7832383aac1e802d510db80622b00562334d8062210798441c031183abec0158c5d16216700ac669e854681f1e4f80d077cbee1f42a3245da66e2e50f1982508a4141d2e25401670191085806236da2e830f1d94d074f8062634f580572,0x57b73c0169addc026e406883d52a203442be0865042208847106a211c8068851c02598bcbc43510bcbc43610bcbc42817b73c06f04212085b100c42681f00c44681f10a3806233895804b2,0x10b1802f2022a1079bd901a08ada50d4f21a2f1f5083cc44bd901a08aebdbbe2163b5208bd3dbbe21630c0670fb711a180d01bb1402bb7b72c301900de08423880983ab254195fbc802c4022210c9c219096ee015c2210d21bb6b7570890c4176984510846b77009b9e08425,0x1ee484436081110ae421b300aa40eff00a84215b07544210841d308843c1d310b5dd42140c2ec351c42b634674f69005ee23430755802f311a18603c017988435138432108581] 0x700195f73b7ff07d1a8049349ecb6ffe0fa350083333f802d64a0672f1416a872cfb683ddaab7604b21e7c2b1a02b18fabcf44540d1f813743c737789ec6615fd7e714f65b7d88df79dbfcfa0813719887d2ec4da2b1478d70448999d462cd79a12d45f27bef712b9eab446b54042563c1f701cd443eb54935bf4cd1353d23d531f168a646a23109614f3085c197996cc9bc2311ed689f4ba356276c42562c2170c5efa136410d885808f1c92f93a8c69bc082d503008ff35b8e76e7b0bb446b3baaae27aac6020fb8117b97ba25e6251097a9f7025fe5943f37bbeef147e02b45628525c4c7f8742501eb6803cc060a0c08166c0568227d68ac0023f12988420dc9798ec822fd6a26040023e9db9ec2aaf2188c42c6e8127b01970b83e80d355988959b0c9ef71d8548bca084bd60011f7a7d01a6ab1166ff6296647b8ec2b11694425e30008f86322d007dcd1093ef1750a623ea2ea14479a0c5e3724fdb1547c8a3cce863449651f142cd12597d66ef13d8cec4d8fc2b1917020011f898d1259789ec660689b1f81c871464584808f1eda5f4594448c80710a4b1aa7caa444c0478a2203d4fd099e4cc42691ea80026e21f037318a12023d57b914d124f8bc14cb27a7f8a132339bc10ba478a5930a11798a4782df130a12ad47f1546a421644214f2584fd4e0144d5a023f54f914c56965133784bc40479ec4aab850a268fa6c9145d1f4ddc284c7080be2af712e237843d96df6e3ff06ca0478454c4270200b54bcda6ec27403e97467df9dce7208bc02a80aa1291c0800834096c4a8813991a1cb2651e4ef7429744b3b7fe0d922d08a821381000ff3540a3dc5f0dc92408fbbe826c811ba44ead0c822022693c1895ba2f103ed993ab43200a8284e0c4b4e50262044c50e0d4e5e2dc7d8c8d7d7f6285871b73e7e76eafd3ce7e66007505b8bd098b680e3e6912141952109bbfd4a5907f883cbcc79730c59dd201041eef1e61043174c5c5393ee035c0022cac277bf8208626aaaaaaa80b10491c0801b7999fcd600b609dd0b9409569bbdd0e40a4ca1c9673a7c0a8ec91010004040e48e040053cccfe6b005b04edca812a91312052250e4b39d3f51d980aa0008081c91c08009f6de14240a22667f005a42dc5ef712bfea1b29f42d1e1121000503922c177020021d3b8251e4e23ef403bdd0ac17687114015bdc080359d9425b7043c62f913a0b74bb02573909b20094fa5d2266c1d4016d39553c980aa0080206626422c31247020021c8999d4018ba504a810150f19c8fb07c08247020018e8f272ecedf6601dee85e1d0e802b7b81005b1f028dfbb812341148b644400899b408ae0390284002cbbcfa3575aed3b018248e0400acfe465bdee0401d0485306ed2be04018317ca544f0f918ce5203e4000a6c9a8337da6c4713d9198dcc08038bb810044fe4665330200e9ec8cb2260401d4192a18508bc091a08a169361662974a41,u 0x661062572 [0x4504559608a08ad0c10450452484,0x3da282a7249851e4ed90520020cc106724646244,0x210491523bd8bd8c962578a0953236f8c942540,0x2f1027282285b3449c209236d994a08,0x1d743d9bb761759d9428249686292f800fbdc8,0x16606f95665ec49a00a42084b406f7d8ebaeda68,0x66d2d5136a2b009b0828ca0ca02c18b54,0xc5d006e813646581bf52461302a62a7484382d8,0x5eccb8be4dcc] [0xe821998b288852c20d98038104fd8038204d780382108f803821801a8428ea04eaa216c7c48667c3080384fbadae111cd827f414035c5f1ec108cb0657107b821b31447bc4b345e5e210b0f7f6025eaa08425108d8397c02a1b31108d80543,0x3411801108e6004423e015cd02108a82c211a0ddfd04cca68231f858c02c0c9841f30c02c008847c133261cae0c8a984234194a42edc4026994dd34fadd652248b077ec5374d3e68235baca449130f1cd02108d2a8f1cc6016064c20f992a8f1cc6016064c20fb00a8e3c733ba300b002211d46016211f00ac7a07f108f83aa3,0x4ff8036283209fc84238d81de1a8e522700aa8300302aa443c772164a813f7527950788c1d3a9a08c42391a08c6016211ce220e2191988504ecbf02bd72de62debf3f117f30f79f91322f2f54fd1087bf9982abfa0a402a09ffdd6f7f3e3f0b50bc3d420fbb620efb027f42dfcb89917938844c09fb001108e5a697c0a3c441ef89879f87146006210f04eb4320b108f83be3dfc7894e8bc9c42c640a7181518,0x67bc104fe25223a0e043] 0x83b3736e5ec742caf271c4b92af7762862b7acca3aeb2ab0dc4a6e252dd4e9742caf78e7acc54dd222017ab3216fc783175f23079bba2d6401b128e3d0b7a01e081e3785a3b387609ff8a6bab3667ecddc1176323d234d47dcb473c41501575a33c9814d99c1d47782048c02eda6a032111637cb8d605787bde56aedd8c46796621e231ea3811d68991047064085bc280182b58d006c1efa8139fab0ec12eca476b10fa31d6fb577f06bdd4844065c88ac63779cd07d7c402ebfc967b7809af56c88cb9b9463172335e79116b236efa18213565eb6def581cf96bd3368eedfe009408e8c08eccf65d2db618c5d9a6bd1222d9c6feb030e6d4455dedda37f5783bb037f369d6fbb3db45c8cd7a64458dbcf961225ef6ff04ad8c5bac1a5754d1decf37bbc1770782f21cad8a4fc46fd489c0485ef5222d9c6faf05f170b18b6ebb52006ac6b02b5e9ead49cc00e641db779803ebe363c395b16f76f51c37286760b19d82d7970e95421c222d9c6fbf68e987625f3ad88cb6060df8d6057a74df890dfa744a3b263b71d8904756ae1d8893fafa72dd474fe0618c5fe68a5b17400b2264d6c3b1eebdbb07a4f54f42ef143a71d04ba520019cdadf8e9894e74306e213e1cefe3815b8767a88839d2b42ee992c542a7cf1e1c82001bdd70200cc4190a6dd2b9af7c7c38860d2d85c8c1e60a2183497fa9c6a167d1793458b67c3945dd839120f201f832980,u 0x500dc43ff [0x5718adac5156d9af4c95d66b5304d2904,0x8237e43182686b0484501d0416560c31ec824e244,0xa0f936200d95b9f66b329cda4c9d7b142d87b41200,0x9a5260eafb402503ebaa38e42420407c56ee08,0x1ab6069803bd642d1e507dc5f60830675aaa835e9b034a30,0x3daf60ac25aa0f20ea2d730f6087b10108598,0x728c7528c74b65eccad1c4253c3211c2a11e1b680b8c9932a6a5d0] [0x680d083fc165f01ae50bc9cc4c04226045ec173d94901a10aa810de2b756e84f59add5ba13d781d5a002c0add5ba13326342d826010d0be5b41150d20842360b2f80d720fd1fab74ce8fd099bc086dc685f072086a6071b801810ca6609804ba4652f04c03,0x20cdeb74266f021b4085bc01588c2842d909f14f15b97430d88e712153e26dfadd5bb8b583d41ed32135b7f4811004114f0bc9c00c02149126add6e252421a701a0402e281add6eadd6e21199816cb8592e52421a701bae40109a40838a1212f6b756eb7108ccc0b1580c842211bc108861842dd700210b1802ba85e4f4b0422252d1f41c5102f276602113022f5,0x41e0861083c2005710c5bca49830841e6042ac1650210b6219e1842c6081a6dc4a480d08554] 0xa9a1ec4eec6feee101168d5507c223973b2c2d9811b71f9791d7c2e39b57fd1410271107c60b661dd02bf989918d6ccc55e7af842d3bddcbe7a114173bf834636c34828ebe4604a03ddcf1e23a5003098990da003e706ca31f04a278ed5043706a38365a001ead2e74bdeb56f419a51634d6d5723d15dbc012156fac06c007de0d9695f80ec81f10548e8f2114cf6a0830c0084cbeb01be62c1b28e6c263373f085e89a71e8befe008002ac340b20d96972b56e32926b4cd8d4015662452ee435f406117f3bf34fcb36c8b516392f54c58783c8fe1b24080ab0d13b58000208651df3d44dedd8ec321c48fe1cb90ab0d600608656973ed2519d1d7c540e096c22fe09935b54bdc541be4a3724022ac378ed600008219793f5b3315954372de3f86c28c37b48bf6000082197dcd12f7154022d36c90202ac3580182195a5ce0f063975d1d622fd0f3e2d372d0ab0d656973b1933ad5b1f6fa65216764167044853e13d84408a15ea6c30445c624cf4ca8b9994024ccbab99416e54065d74762b994a41516332ac35953f0d345c39366505cbab05050200630e4d994178b9070b940,w 0x1e14a21f6 [1079,2439] [113] [] [0x41a800c2090524105659208ad0c134124c4,0x8b04a9a238c1486663b109c09829ce4195b0f6814720e00,0x428a77b4bec75d906c8a096b68929800f8299a42e888,0x8fbf7905204011a238f5a0652c39a16c1f38694,0x14c52368aa1ac90b6a2f914006442993dd236050,0x7c771eefb7fd5b3c1aad6ead2fc004347df577551f4b5236b0bdec244199acc40c,0x5550429428a282882146db73fd99eff57c7b1e,0x189ab0ad4daaece09b5b536ac2b1978ae0d836c0fb52,0x212719510401c55d9b1356159cb96704d9f60,0x619d76124596555d85976564c1c,0x1964e7e80e28386] 0x36a044238c841e91bcc4f03df05af22b70df84d128462ca2508c63402a9a3eec69f29abbaf106d10a6ea68fd027e2308bb0539246d7c41976b0e985ad1d14d78857c168273c030987e204c5029f11847cd0646d9e197646d462164842c6081484228fbdac42210846c02b9038cc03091a0a13415927e2f7b19a0a2341588462 0xaf4670f9ee9fe5fb33b0e87df181b42421ec8e0278d6ee68b1ea2ef80b1a6cf45c4a82b86027c05227314135e061e0801a599a006120037c000d22bdbe1ac2e4d0a39171a81043a056410828a19f400b9c20dad143e728f2f6c0dbdc01a180ab8634de009bf79ef48f8f002f5c2d3dbfa7b7d1037ed203a5933a722fe1b0d3cdb0238fd1abc23c04868f0c850f3d1473c0637706d61f29050e76e90c31572060028e80796346e3cf52861d46881586c9d9cca5e2f193215140c0f10c41c87b6304224be1404587b2291120d6568d159e826a48750004137807a517e819e5f82d6782ea5ec00104de01e317d802d205604da3807117d800de002f8549aab9cb306cea245,w 0x811420dd [1811,2435] [49] [] [0xc58530160a40134617a051fd206401450410412044,0xf588b391828608db7b94892c6c5068a18c2d82b86648,0x10b70f7e8208228a2088303728232d718435558,0x11f411ca48eb7435acb1362800c0f63efd8d90,0x17baa93e36edc14cb800869b6d5f6aa4f36eef2b90ed8dbe7b856d6ea6fcea6fbee51acecbcc,0x29428a682082146d2b7ef21f7a97d87bc78d2f7dce7eab6f4,0x1c402bd24cb182b8bdfded31f7b926d8c3d9b9f0238042a474a,0x175155a5195d159c49c49d409c,0x65839fa038a04186955a601c] 0x1cb0792c4124792f72d2 0xbc02fe8dde3b5e103048c7808438432c021841981f81d751411104837a0c41c1396605a017fc76bc20608193000011c21971e020811400c0fc1ebb821022061bd09350609cb3c102b00200bf000f4a1971eaa01d8fd051c75f2b10de4007a52672b69166636804e017f46ee0e6fbd0031cfc7e800638ebe55bd8600e0af968a23661b51493b540800122227be0c67d4084c4f681781004d13c76e71c10c460f9f3816154740f10144c01e88026f3df42b1977faaaa964952f,x 0x1e0800371 [0x15ec819a82a7f4134854001dca890114104d2004,0x3b75a145a4ee90c6286337d0753623945580,0x8c585353304a1823ad4060d1ab30163ac19aaca1a355ac,0x77bdf7d1b3a0ee838a0a1b506d66b2290593a06c554a98a32435a48c] 0x20081100805ec9733404555300aa4084840160994a1fbaf994a211bf5ccd0e37df00aabf753329583f43108985d07f3805e437ebc6d30eb83f8437ebc7130eb83f842b266871bef83f84fae799482 0x72b1409d16b7c0c833691634af1c752005830608c2c2f1bd9f29004f5180144c1ac855be16746911bfbed8b200c209085330c30b923d0efd285c1b6bf208616f0cfb5dc25ccebc80f41522ec756170c30b9d5989533af0e8dcd18628be08bb040008b1c2b0b877c35bb0a24f62b5cdda059410244c20cfe7612872eb4cab8e9a8b5d5a44c6614e0cfa5cf2d6ab400c3699ae6b129cd335b5cd442202c795d30742,x 0x120440561 [0x50504fa68431674041ebb16843f21d0004124d2004,0x16c55421abb4918f570bd894f9ca3b523512fb07dd228,0x1fefa3274] 0x68204ef039a414210e68b02510bb6961cd06e09d218da08ce5a5a057ee40031 0x8231f89d90d880b7baa8aec684e190c5d85177ae0d329f3b21e17175515d018be39d90f099baac2b204168edcc551779b21c65d62359cb6d1dbf8aa2eb56438cbafaca0b2c75a3f780d01548d590e0b62eb845cc76437db6c5345094,w 0x20c010bd [1554] [] [] [0x245206224628c4f40a787b20a000411410412044,0x2252f96f742c54625fe34a900a051e7287322608d448,0x199bb5162e33d1f7e87bc461efd44102a7c9037558,0x1ea6770b91eef73fd3b9fd1f6df2fc15cb47c67f70aa36855490362c64c,0x95b37dfb4c7ebec71f813c04f527a50248a6825467c7b1e,0x83140c37bc8030278823036c84b02737dcbcadf5e0] 0xe21 0x67b9f0210400e1855d8c283e410ebbe9f44543001d52800e2cb01892e7f3df9dcd21899070eb02000d08115db48569c1050278f14f1e469582eca2c50300300e2731bb455548a94e3,x 0xe03843f2 [0xa6c41bfecada091cbd908c0030c2425759ad6cd2504,0xd8a9914a6976dc20a3ca23f67a36ee08] 0x1dd02081473c5e081484f06081481c6e00b8ba19099a61 0xc2da517498d4c70f7af66b3be171c37eb9d1a45058dd16cb8590e8e56f77b552e66847de55c12551416bd71e8bd71e80,x 0xc03e11de [0x40e00420f62c7b16239462401455a648ad4c12604,0x186278642784627c3066ad24617bb361ec10f6a0212fb00e028] 0x3aa184010551850185418441 0xb5969334106d5954d07243d0dd612f7cdb8517984dd7764f8c717b84bcdb3c58c17d14aaa774985,x 0xa0388171 [0x124b3d0c60b0b1a63241e31741a0c802a09090412104,0x5a1b46c8b369458731435a58ca668fb12af49144bac] 0x885024ea84ca50f426137318ec22 0x111e54e0d243b719d714bbeb56ace996b84db719d714b56ace92696544768df3d8f6526c16,x 0x80240a61 [0x360c2f6d4b0a97b7794892c75f141eb14988461c00412184,0x2c64c] 0x10882c09d08840411cd160412 0x158b476f36b284da8f95babffddcf0c6667ed65a75a9376940,x 0x40249051 [0x3169030d5cac2b000d855199585b0458eb16209459002184,0x24facd64124b2] 0x168cbc1 0x1979796ea2989cbcadf734f5da95eace1c,y 0x20208249 0x54c55a40c66d466ec0f65ecbd8f30723798fb411800452104 0x2f61 0x575f63fb69431e98b3e6,z 0x1a0270 0x44911610c458ab48195ed2860bdea20c1c8 0x37371ea4e7cb9550,z 0xc9171 0x2c1b28a2c282452104 0x1b3d1c0,z 0x821f1 0x25e62e08466002244 0x59980,z 0x85171 0x26363d08465002244 0x59980]
def d12:List CD:=[u 0x8411661f3 [0x2d6cd5b66bd304d5b6482d4c134128c4,0x52a64f6361238349a28cb03760c698a340d00c604,0x1a22ca981ba4d15238dfa5ee145fca3b6c966540,0x1a5260eafb076524a0419ba878040420407c56ee08,0x1d51dbae87b016ea8286f6b6fbd920b532a70,0xcc8b28608c146541b604c5741d1608d1ab07dd4a8,0x813212f696a6af6bcd00615a4258204c55458494,0xc1b3a06c590b48a08200c19515cacf36a28c,0xe518ed528fea9853953446a0d4e6115f16ad34059522d6] [0xefcc02c90845a3f1ce58bcb52d218f1221623bc13e1830e10a18059517618867c01c1dbf6c4619db89c0c4423e0e3645a9bf08407065f108b838d319dbb843260341c6a838dc018162a7c7ec1a9c06e450525803978353803722755a3d108d827f42759a3d108d827f4275da3d108d827f4,0x42c60e3700b260b4428912d46a2caf10a3f6d005ed814f336780d10b18059510b1aa9071b8059410b180d4b20e3700b2b06a7f137f638955072211701bae413ae00eec6bd6211701a9541c7600ed85884f178382744a1b02971803b302163c6a7146adb10071707e75bab744d6e09f70070de16868dd23f1a3c9885028f5ba29371077f21a5a016620536b756e8985f90d2d00b2f9e5f23778d7adb082a55,0x8353add5baca4465609d5870c63e45b89886dc01c10ad33a3590ca68637708436e00c4842c6112300b26a346b2600c4c428e112300b262147c9a0a9300b298a9f83f389e68bc3d4210c980dc8b0051382c607c1acdae82a451fa360b086a706bb5bab759488cac13ab6212c70c162141,0x275d827d22230311ec623e08059108200e089d5610401c182a5c20803831af5b61054b803b439dd8888b9883cc02c90dddd9488cac208038527518273c02c98865c02c906110798059310b180592,0x27d12755827d2] 0x1158f86b3257138308006a2b1b15672f8b3f54adee3eb95c1840095158f8ab3c28d2e860c200228ac6c759e347974dc18400458504ce351f06100054ea47051ccafe0c20012c24719147c1840014bd83c296855e8adc00343835907f9b3da5867608c280360803ebcd2132c241eb50e57c10bd7d0aad3db80028d0ab20f03bf9ed2c33b04f401c410011f36791996124f0eaf2b61b197f4d72001a3c2ac83c1ef68b4b0cec13d006410010f5e7909b6121f0d381872b138742a9fb57738296843ac83c0f1e8b4a05867609e80320023ead12336c24bec7369830802a8585266507eeedd1295aa1638f04287681811808d268654bdae052849e3b3dbd569619d82711008d1aa467d87dc7c02ec1da70ac33e1808a9d5d1b0c3c25d9302ab07693344b0031b14202341e35d4ac22beb4b3e1d8673111834ebe958455529d7f044d95ac873cee6c1891c0191600edc00f7b654ec2339ca994fcdab47643ed0b1a4b59b144f853c0a44fabadad831e00f802f8f6f53c309000b8deab61c184017c7446d48715d5b0e0c200ae5616ea53b80899e9beb1ad5ad8609f89eadf56f0c24002f4a9e053a3bc43ba0ed9ab6d835d7f2b26cf1bce042193c103cdcfad0004008061209b5be9d08da6ae5616411841dd5f356eb0ebb3461063a07968dbbcacfcd9603b88b8fe42193fddd3af02018620bbe0cba99589efdca785bce8c20cd474c00072b002e5e565ebcb01dc4547f210c9fcf4ac408061882bd72bba9a5e89e41fd66a95af4b944b23b80803a37b8bfd7806f011737f8418d633f12e643100d8138439f6ec36b1b7e8830f117e26cad6c13bad7313c309005086a230c40b3a67c159b192d76090873298bb576c24cc1210c48061205ef91f8ae4128580a61076b426f4903ad7cd7d3cfa7380c7b7ae43ca193fd7d6bd000400806120b339530095b2864fc3ddd7bd806161880a5a2bb5de39abde0e9c43d68166021c1840177ec3c528216e3852572a358c767abc8100132b04e43058414419d357702f8b8e9830802e1b0a1b77933290893c83fd5e09ead88e56ce1ac80b24f20ff537ee5ece1ac969ad9bb427907fe9f770d84170f553061005c361499941ecd449e41ff0eb7178075f98100132988dbf93a987030c2de3e84e83fe1cdd9b03464124f20ffc58e4f4f8e896ac663fb1000493a0ff874346f011468d9b0a70a646b32b20ccac9f32b5f34,v 0x3e17603fe [1079,2439] [113] [] [0x410410415a62820b530450412504,0x6b04d88662789bb6cdfa842f046d90d2002c832a24,0x35b0451494c207002100fb9b4db490e63edd88,0x3bed2a50cdc3763aeafb059043dbad0a0545b0,0x17b10904095252a2a94b04a5aa306904218834a58,0xa00312d4de83e83c83c83a8bec6b2490,0x374b7e9537e74b6d6c299b0915a2c82db2886324198cb06616d65844c,0x510428db41ffaf8efb0f78f77dbfe9d9fc6edcbdb7cbf0010d36ddfe6ddeda,0x1cb967fcc6594b7c650f15c4b0678150429428b346,0x319510401c95725d7a5994329716ce5cb3ef6d0d65e0,0x95d85196555d8519656597485c,0x7084f30c4f10c4f0c84f08c4f8065939fa038a04186] [0x40d1efbb3b7af683ab8ca56243b9ed14aea0a6372ef98107d82d03f111f81a3df75b6f5ed0757194ac48774122269298dcbbe0845c1681f887fbeeb62435ad5a4a6372893ce083dc1681f8e3eece83aba01123bd72ef864840160b40fc6c4bd752bd0bcbc2113040d63284f30389cf0f1217fe7449905de217a7d5004364f0670c086c47c3a9f0c01c5c18a1004cb542f2f0852c0fcd0216c5f76741d5c200b003745aa1797a821530409542a7c418dd842c20b50bcbf8108d980699e68176e008145349685e5fc0208107b0854f88302b0844477c1c2f2f06ca3,0xe44018042f2f0852c0fccc214f0526208e71042fc018082f2f0854c0681fae0082a5345a85e5e601a603f1c010205a85e5e10ab9806980fc7004087b73c2f2f278210703f167e38ca68604e1089980681fae00c101813801e7a0cc88eb5fa153e0cc98020a0423881108442] 0xcd237b62a4520add39138e22905667a4344499f5c26c7933fbb60de7e95a2e706656de7e2e2443ce7153685d9476412241d8391211207fb8a5ce27e2f1095f9eea39a58eb1e5fce797b89f8b9095ba7126743889ed3b312c774f68163055989c455d23a99b78abb4ec1c0f580857d8a1d17f8908695de7d69b43f9c54e2c2bc2ca182948873298a32830a1d148647515ce916fc0bf0679883b19f2da6f1975c0af8bfd43487aa7c820043aea043ba772479f85cf5d767d4f6cc841bd58a5c4e9081aac3c35e9b42ef1e8dc845e5eccc316fe02d2e5e8bcd6d49158206bb176b7501ed90c7014687100be2ef743bb33405ee0c4871822483b803621878de303a6060adcfc0100707f09614d57070cdc7504d9d8c9a9f9ec467508573775431935612b6fa124554377011c740444de14ff54e9de411935cfdcf04bd09e53456e26e44a7715bc859cc76433a41df042bed5f90ede37add5cf5edff76426186020d3c4c898a426389862c3888a0255909d600afac47b041dbe4aed427b1b017091cb034e87100be2f220e3ba3c3c1890e30c69077006f1f59d2db030d8a9688230c184a9f055445b338b86d520fe7aa1dae1fe7f1682f8ba9003a749ce30a23e8a25613a9c7e0c83f050a7e2e4257890991569773350ca41dd5c0d00f18020c2040c50ec0a5a02a068a3c86476331296a3d44275f917937bfb19c3706858d68cd,u 0x820a81572 [0x71908e04c1e0ba09010451561826b531492504,0x198c3006104024f5b049eb6c4c7049eb684c722600,0x334588ce53412f860129d71c00844fa18c81e21eda48,0x491868330a629600c95bd2c1bc8236f74ad0a5019aac,0x1defa327b26c680820a2083eaa2aa10c45b60c,0x78087dc604fab274] [0xcd170746fd188c3aecc46fd601594461d766237eb077ca758b1b7182423261b8dbe234098daac22f9d806c1a3e01dccd0564c308d0ae3c98842b00b9a044f72b9a06c793e1cb90eb1636e3005e7065704365066304364522360e0832a038e222,0x36ff103050633043650dd7068e436ab103050d6b068e598b701a36acc6df60158aba9bf4c6fd994d33418dbfc22fa4378c1a3912d8c6dfe086cc96d6086c8a42ec1c1061df846fd6248b072f8054430ebb311bf580564,0x1bf78922c1a3e01510dfae28ca230eb8ed7c1e939bf5cc3ae2b476be248b077d80547293b8e0e212458397c02a199a0c6dfe034a4834753ac599a0c6dfe0341d5299a6c1cb90dbec49160150ccd162b46dfe248b00a8b2f4cd162b46dfe6641a3b12d7c6dfe086cccd1637ef00ac652171c1f8347329118e0fc1a3999a2c068dabc0683be5,0x2166086c84216080c8194e00b8ac040892213345892221b7d8922233458ad1b7f8922433458ec22124580542124583bec02a1e051c6d516050c49160150c6fde248b00a86712f1145119a1c793e0f49c6fde248b077d80544,0xdaa1] 0x1e3ecdf99183b5c76ef35439a07a006d2bc0ca730e8188430eb208a99edc3b75edaa601d8d906dd7f490f85c7d46531b36be0c4e17b71d2004574dfc6bc97d4df9f6676174dd995f2189d76f72c3c4494c9afa1611ba028090babbea63def1d736f5d99f856f217376544a39d9cf02144c18e7bf8d79258e0c10c17ca48a3ea4b1c3e3c9b7b0f7610686b46187b1e914107af193439b899f051cf6f1ac3794c821f596887836e8e258f8c687cf95828e7b78d61bd043ddda1a14dc42933666fb40916b500dd6f43cb6887836e86158fa14c6961f4936f42c165df50ae26de35e44d78795e79ccb885d977df26dac4dde2b858245bd0d942bc5e7bf9563c38439d621dba98f7becf89b78d79129e2d02195434562549bd99f85916be37584d7fb45a2449bd99f85916b7952614102195836f84312783118bca54872e273e5edd8b2bc92d499005289489d374627476b11e68bc89d35feac6de754221a98f7be1015fd24cf0abf1fe9c82f2252831385c74ee3ded2d0252005535472783aba817518cae1d097e210508782017504084ce10457cb0420025da0823138411421f097482b856115fd25042bea3ded0bd9c4c1a689c8ae8f3842a65f519ca5dac9d071a4911fd8952c462d2e082f68b5d44f2006,u 0x420c28572 [0x1dcc1f660aa09050414561822b531492504,0x7db08bc114f5d030f608e315045e1efd0f6422812a64,0xc59f7d0661efd03636c517d0520fdd0362540,0x8cd9e97bf5d606ea8286a6292f860129c7002100fb908,0x5460ad1207cca70c359aa83b405405bdd4b47ec,0x9b491883106b432554c0d730465fa6ad1960d9554,0x28d5eda] [0x21ad09a901a20f0fee9fd4dfb0a798e7d6ee9910058fd8f20253ee591d200df859017178382d84108783472108d83472293983282b0a78bcbc4237ef7b08ed006ce904423600d8c9a16b757088fac329e0b8d96eae111f5b032666d4132e010a045bcf1d0c7061045d59f0ca478737178f82663174188572,0x211c4471e00d8bee9f7f9b04a639f274f80d38a2fd31005841bc01bde71f23e3409c218c7ce28bf4c021a7dd4cb7ae2268fae111f58653c20ec5852c63c62168c42ecbd6af2689a1dac20953a8254f223eb0ccf9b504cb803410f318f80412175cbc333600d10423600d885877f04d460ca06173e182306c87f74fea6fd853cc73eb774c8802c7ecc54fb964748037d01a20f304c380364,0x3f61] 0xad59003794051d08a947db91e1841fc886f2d03ebbda16b2fedd7c30221748b032c8af9194faef687b75d8d53f91609e308730782e66606f94e2d37d9bda7e897700073c280f371bd9a1c017b57cdaba5440932d706a45024d04695b786315032ed684405132d447d015c36767107c541bcb40d46b472f730c0e084d05cba19748b45ad39129c972dc9b75e861ec683d5c367107886f2d036b2f21374c4bda1d7c302025d1af1e8d02dd52e07f50cbd0137005035efd84801d58fc52cad64d3cd5cc1a9e3d91bd894d05b2fd0236348f5d2d7664bd0a2b5913512f404d0501cbf610f923cb617b50ec2952706a57c182050ec5445da8dc05f6b591128c0018bde004d011419160a4463ce03d8c7e0e64c469380e598cddb60b3f17fa3cb48018077597403730098db68616bd92d20063d7e6e0f99f840,u 0x3a0858272 [0xbcdf3047da08bc857001f76a824157db6b0412544,0x18710210fbd450d64e413892caa7d45071455c0,0x44140f6083caab6320ca286e6092b83adece094e38,0x2d8ab450c60acca6116b230286316728db4655554,0x3db44c] [0x108384d02bc4f9808d6e8995ca681b160125fe70e9f8366410a7833e21374378f7a222153a8a01357a889ba2ea353442b1de3de17be60371081d490098d0bdf5ba2747a03365bc51add132b94d0362b889b1c884602b1d7badd13a383415c44d8e942c44d8ebc2107f833e2,0x217b0de27cc04142f413018378a843930e4111c823980a2108582db205b7804c2bc55cbd1a7863a5310824602b10a783523] 0xdfcd42c6620cc8022aad0b480350669d5372401e57768480352df05c8760740a342b200e6fa9b569975dc2101b838ed830187561721ddfa4fd29b23199f5986721fdf7cf8b8c5b66dfe0bbb220e21f26e75b108406c8be0c0c306d66459c68013dcc1f49a7c01ce6943e1d7dab1cf2e05b60e1d9147c3b0bb69e25c0afbfeec7c3b1bbefaa18e1d91503bf3e10528513adff1eb8daa00615f7fd6034ce0c0bdda52aa0411189f98e1a0801e5f7e0f3381559a52bfa0810b1c13b384647c8038ddf3bbc9c8f90071b563af1f200e372c79d45143b034c3d4,w 0xa0ca01f5 [1591] [] [] [0x3621189e824f0060ea1ec8280010410410412084,0x96c0c9e6015ecb4bd4ef697d978a39b40190b1e63ccdc8,0x7907de7d052040859a897b2a609535798,0x90b628730f629222c29c206c61948cf415c10,0xa08af46da0ff0b4ff66ce7915b1e27de9c9edfafd7f6b47ac7b6a74b2d6,0x1e8130172fa04c29c2b6bdded737a4ef37de15b03ed4b695b46,0xe18a061bdf5f5c] 0x2908268184a41600b0bb2f549f0eaee9df108461085135a2de212a5eb5348f704fad65d4c615f28f5a2028db7ccc8651ca2826520fc3abbab8d07be225878ec9e3a85238 0x28e13da36aac80a07180dd367093e9a06eac80a07180d5567a48eb63c60816d44800e5299e6554026db50102f013ad131c4009a45d9082046aa1ce028030b4cf54d404050d7020304280a26edba4ed6436b0e7041b7a240172944752a60101d66e0205e8802f5a000188893ec10b34102341e70145516ac7a029a8080cbd0a0048fac8ed63cda5754e62d78e3459f3374f638e7d9aaaaac3a19,x 0x1c05825ff [0x1e2c9421390f2003b841212b6c1276dbf3606dcc12a04,0x12a626953054153860929d73c0484080f83ddc110cc7ef6ccc746600,0xa129e61e9e1d29f041be8ca5b8be8238c95010] 0x2c8842d884f50e25085020bb6c21b7005631485c27a8812c0211cc5217b7210d66290bdb5086c302bc084735bab7427af03ab45bab7427af03abc016146830603eb1a0c2 0x55a04ad6e92282281676b73f47c742ea4b4e67101490410908f43d73d9119991120858479dca7a10aa3af09e5909e94a9842c63dab756cd48309478d2174fa9b9e52273b28f32eae9b735689010309c799b1f66a816c2a3ca243101431014345a43f1fee212282ed3d0d12b810,x 0xc04f0271 [0x3de441873d44183908a87221400410410452044,0x16903299ad0c2431668ecc1a02a28563ac8a050061ef008,0x10541e26826b2002593a22c21b60c] 0xc021ef658c022180580552180782792b09385524978469c84802d67e1980832 0x166f8d58189afb742d714aa9d0bd8a8c294fe2f9b18d5b5e2681f53a37b151852c688fb6bc4d038a642046d56639b76d78915d02d4611444e8e25c66735661a9aff76d726a467c28bdb1b51698f1d647c,x 0x1203d2872 [0xb1821cc20817d65d78be86b455f90ae03a89181b732604,0x2835d190ca67a9894bdb3358d4892c8cd04c61038810a548] 0x9ac1f7ed89ac2f7ed89acc02618344100ac388eb0096588eb06884b744d6e09f4d6eae111c5827b4 0x4a2d18c0f45f4ae1b5c18c5915182d89a2f6c7a3c759445668bc7c69468195c9f7cd8c797d594623bc54941375ed96ef3ad9584f64df35a32,x 0xa0444171 [0xdb1585da06e9046083b68a47219000450412104,0x6b3361cc29a6cc5c674d5e606d8294a80a5363aa0a3d08,0x36ad4d64236b2] 0xaa24ea300aa421007a18083a01 0x4218b69921a0cdf55042da68d744d85e6be50dbe8992d9e866fab420d5d5c5c6f943c5b433550d5d5c555f2e5675a34ab9d2637841a,x 0x80392071 [0x72aa58a8a07d963027a83908c2f415f90ae03a89011412104,0x1c70da3a10e14669a31558d8a67c99b4414] 0x551290d8e072bc4b9b98ca331832a1 0x31ad057f7bdc90c59597f52ee739e3d538f0eefbacd31ca3f3fcdaf5d248e2b2b221df3c5f34afb68,x 0x604a835e [0x2d79ec5f435a08dd01908a02a090d5e62b532452504,0x1e7a0c61425ae9030ca28edc12987102100f975903e4d8861900,0x5b185eed587b5c90] 0x41e89000eb90422 0x1ad537252cf4459d5e8a4756886f3c6a7acd189a0556fb64693ae6520cb1aa38310d7a1a5726a0,x 0x60281859 [0x2f6d4b10c48a44960fb4d6104783421bfa43b010c240412184,0xa26c31b60c] 0x108827f02b863e32cd3 0x1348dbb7bb8949b57f319d6e984efab348ddb98deb24b6ab60,y 0x6020915e 0x138d98e30a08f2803e6a664c588611ba329c49a08c022d4d12504 0x216c40b84b1702e2 0xf8a5731b6b35357bbccf5569c7773f82f8a4a1a0,z 0x1e0170 0x1d036e95313622d2463a31a6b7307cc79e25ec648 0x4d4cf772acf3f3585d0,z 0x1a1070 0x7445843376903099d7b4a180f73ac104188 0x1f772567adb1c550,z 0xc25f2 0x25e62e086663a330037b2644 0x1aebf1c0,z 0x88371 0x18563908419002184 0x59980,z 0x602f0 0x306d830d88 0x2960]
def d13:List CD:=[u 0x700f20af2 [0x410413561820826b3b0410412544,0x49eb707e8388a83b7007e8243a80dec1776ea24,0x28a39450c629311bcc507bd82c42f14146180,0x2d8c50495c2071e808403e0e62f220f9d6248,0x186ec0592760b20f20f20b20b6284630,0x54e105d0410481f23ece1f531954841892c,0x83c564e81b54d2861ec55b1914a65e60fa36cd6a98,0x3ab734abf577ded36acdc1c1a54df8d32b5995a74568b2] [0x7beec42291c4ac02b17becd6eae111f09efaf0322104fdf5e0b3700ac70a173895805635b20b3082e8393c02619c4ac13360134c77462f24bdf5f0a17008670a170f4582cdc02b202cdc06804233895880259fc5ac1a2e0158c59887179383444,0x3ae5648670ccbca9bda038d8598ef7ea58a8fe0e8733c188337c0254f5c9c641600ccb827fc030b1c4aee0884038437c448f45e1ea10a4e4ea7006e591bfb13a9c60676b436be0101ce2565063bf2044421afbeae144e712b150e8712b30840317478846210c63c41fe00d903d160e9300866b757088f8c166a2dd5c223e3059b80425f7dd80572,0x20e5e4ea0bae561034a0e5e4ea3009a60cdb009a5d727275187ab3eb99840d2d417840c23894221647237f6275386d7c1776c0072e217ff8853c01b20859c02697beace2562f24ce2562100b0080d108183a54389580422,0x72b0804d183902395b009a44ea861bb0fc5c1839583c62] 0x55a7d1d6ff357f366c31b086c70d4c658f11d1d3d383eef8e33eae7d1f6ef55ab0c6c21b0c55319e3c474355520ebd64faad9f47e2ae7eac957b3abb5d483f2f7af7e4b6d2ad555bd07154c67933b8447435d560ebf65dab957cfa3aec8afaf5f6fab07e6effce5b6d29adab957d071d4c67973b844743655a0ec166e232a711d187450c2850c1f83cd64654e2359d0a69683e0d361b3d5ec91cb59cfd08fdbd7f0f9e41ab3555ecea69add1014c677b11a159437562d6a20ec58014c688e68a0ed9e2f4696b3a6b2a98bfba6a63311d0dfb1076388d3c4654e23dbd0a19683e1d7e3f77a75ec70a283f6e8e0c635414f076ef27ab432a711d1836e082941d96d75495881cb62078e706a4083018cf9c6e0d3c0cb7e8b35f3380150d3df43659b6302d6c703db5d9352c43eb10446b49cb1e06d4302819f0e0b990e5f1600bb7cf81d58e06b331befcbbd7cb572ea9e7359b52030f35ff2f2c5b495bdd9f66ffe3c1fa89f172d8e0d63a660ed1dc76233f8bfc32c45b31bd64254c55781ea4340db0e30b74afe0cab9ec40977b1d80077c111fc756fda9ced8621bc7eff2e33ea4063c5f32f5c5b495b9a766ffe9c1903c95ef62d63b83cc6fd10215b3caa45fc79f051ee7eee1b08ff0bb06812ef7c2a98f5c7af817ccc6deeeb006b331b10c58f5fc57fe6ba497dfb3d0c62ab9836c3b5e6bf8326e612028f19981d4fdcb103c231de6f4a1dc5c0617706adb048a1ea5b4cbc305b0c66d1029246258c2c8fdec5ee8408e4bc10243c808058cdb160de98cdb1638806706146623c12d23c8081705841917ec4802c80836ee8d0d8d2007c28200356c5933800659c7ad6376552c6007633411988cdec6007d9c15d2466232dc15d12020565e1863080081c7594438086b9a14adf6,u 0x5c0d90a72 [0x4114558608209ad0c10411452444,0x3018e305057e086be41215c005905b982ea246204,0x28eb240dc20939022fb582c2bf07127d45940,0x12383aeafb74e094ebaea8e204214e9803f6148,0x280a43767a0efd05199fb045141ad0c504524f0,0xad33d56532208c41b7b5a581262cc09893842186b58d4,0x27447cbdb6005ac29a080b74d0d74b34c] [0x6e8e216300aa6a10a585d04d286823052255fc3334f9417c7f1f4368e8a71c42c60b3644218c780384df038844c14898e92c41f92dd6e2238b0657804a54822110ac3172245696fbc043299a7ca0c63f8f4d29345e4e2161ebf86505f14e38858c166e010d8a43600442119486cc214cd6ebb911c983100aea1e33074b80413,0x26c98f1ac03a1a042992dd137782d007295c442990858c021168422e0150cc318f107e6610a980383f357c3c9c9b27834429e015196ebb911c9838f45ba278f071f8056410b18291210b18291c02b9d85fe448ad2df7846dc431402147b7fe8e878cc40e8f0070dbe0710b182913,0x2158474a6214c8c2148bdc06238896e89bbc3c598858100857226c98842b18858c02010858ca6827d334118ee9c42c1c286c01c10858c01c91363c40c211ba180745] 0x1663ecf71552161cc1aa71d0daf2666051bc7ca44cfaf8b81548803e31cc63bd8541c1a8dce459f5eaaef7359a216f41a8dd4bf86fd0ac8298459f5790aa42230e64a31a997b7e8580313e8cfd8cf552173058a9095197987c232e840a477a0ba0a02043dddbeb88fe3bb85e8db5105d05408fbfb78858a909459761a1d3dfa285682c011e4ac701585edd08e8807c594fc148228f7ca3fc59aae8dbc6c01712ae6a406cbcc342f35d0588228788d742c66a16f3e2dd7416208f1d6c9fb0030882e8ee3b78fb0e2ee6a47d58d4f9d0b0d20bf5a159d15532b4572c43415ef42b2268aa8ad68a33840b4e3d4c78b80f6ce4403273bb056e085a6fc2c750f79f8b8105982823e8cfe088b3eaf0154da8dee459f5eaa62ca0d08fdc8b3ebd544422e43285859434608a58c713dd4561572e750d21d059e00625e20c6c089d370bdb9763a101c2d6004401f532fb9c713dd45c28621660a213b5510c610e1831e7633968f04953355622cfab51c2c87254106a3311287847308acdab485552d02f4cf4ea8f9505820d4fa33fd9c284c58005e5426d550b36ad11c3867d643ccd1b5870b008b3d426c440e19f5921c22b348ab56e53b5531a1536c2cf4a455561029129f310ad87210b51982670f441601fc065e84a55d41601dca3496336bd55088c9b560f5473d40bb83610292d4d82f81be307327a02f4cfca95058205b50bcd422e00f2326a65807a57476661506970f10f16ad08b6182806ad08b61010028053e8cfd805c284c5558b2b51a35d46b2,v 0x241c002f5 [1555,1811,2435] [50] [] [0x6d200d9743d903204309010410410452044,0x130b6283a87357104239bf608db416786321a40,0x171813216b4d9e97b743db6280451b7aea26e148,0x46f98aac4208264c104a1d22ccd19534b949a6c,0x1041008490308248c18469903055742980b5b98,0x2b05d0866ec1183a8a0030214c62fdd450c10,0x7ba06b614cd8429a281b1439c20cc514d0b6eab8c,0x18f639b68fb6097e354fc00434db777d5c37cd487abf578c6db6b74b7e505ddf741dcdd2d6,0x10428db18ffba8cfcaeceea6f90538f1a5efb9cff4e4f2f7a865e6f4f4,0x3bd939f7f6dec09e016621523490a50208249a746,0x5bed9b8b62cce187b236a4ca187b36d5a7ea4d0420,0x1892aba2803860ea0f1ec60af7a6c9336602e2de0,0x945445255345065855959849dc,0x300d501960435fa058a041061819510419601c] [0x84bd99a22283180362a003622831805f2ec37c85c5cf33a3a5e49604eef2eb101556a92a7504a114b2a2d1286e894e10a250846b447d6e94d5daf884a1384d54fea67ff0882d3c6d880c9806feee0b49207e0c7c3a1b0d9d1ee3604da66b5c6000b513fb0df9364223b217173f6fdfa7ff33a3a5fe3492c09dde5d6205baa4a2b4f69ed01ac744a11aa1284ab447d6e94d5daf884a138565533ff845bc8553a7bc9c602f003d142af064855240f9618311097d6306c36935566433b6618a4512183a6d335ae30005aa7fc5ff813b880289daa4adc1f129c22ead11f1094270acaa67ff08b793ac79806ca43e584903f0d46c37da42026068c8fc5e5ffec3788a28b8b9e49604ee63bb175421184295a20e758f3017fdd33a481f2c3063e11b298676f5e9b469780803624fec378b8b9f03df31dd8baa108c214ad107300d99d240fc18f846ca619db368140e00d86bcce8e97bcbacc6b440d6e94d5dafa67fcd44d8eb01e70fbf2bcc09e4a970fdb955073da79005b209b8714d6307b07e785d006cb1d5333445efb3108982cd3,0x668871698062] 0xeb25e0db4d2014f24b80721e7bb78ae4bbcb424463f537791434ee35e9d7605a9f590cbddc9f2dccdbe001cf50b12468d65da690c0b705ad750beba182e6469d45e32451dbb467920be4742805cec617100c5e70618a6f07ef67120c25195901204805c653189358e563a6fa9cb68a172fbca00b391f32d4480901c3a8ac4e6ef450b405a7bb7945005a721f7d39d9509683d544fadcccf52c3cc426a29883596d5d4e9828d9e02046ac0eadbd37a05d1c8b670e76bc9947248588bb1d13fa05b026f2b624ad6fb8a8bb03eedc0171ad97c2685070036eb8bb1c30c307473829a3779fa605a3acb917d20001fab650e41960824076d3808c7490df1e2642eec4b4875eef4115957033543bd3c790fba9608220b448d69a43582adbe957c7055b3509f6bb44ce0a03aa470a738d84624157ad036a0366e3639dcbdcaa18fa43865d3a005adcc7b410d761478db0d4e8e41abfcb0016d5467f80003aea94b9cdd6899dd2afecf3d87619ef96fe573f88cf46cfe9d7f0dcedb02be3fc69d51d2bf614435064113d7667345038a06d59246dd8e3d6021db820820dce5d8aef679f8dbcfba05ad034242185ee82e9140223bf840924fd9499c4c7530d63c7af90c0c5f60d424b48379ca173f620408a0294106eca3db76b7331dc1,u 0x480d4077e [0xf06a8240410410571820b5b1410412504,0xb49047982822f0f76fa00c114845001ef6ea24,0x4fa18c50e620f91061ccd88a3616d879f7ef5421c0,0x75d50d02924a60ebaed4129d77d41c008403e,0x42401246a99b5b7eabec2a4aab7c145a6f7d80de28,0x6622c4589b49182fba8ba8bad03f7d1c90,0xdd09e5909e21c9e1d89f274beda151066ac4cc] [0x1d7336438d0a270136b41b0702cb70bcbc406009083dc0815d0667521d0bc1e410a0d01d9b057e1797840b2321c68513a8214302cb5005d0e10b26a0850c10cf0060401a4083c30c2dd810a3821ae00c0a179792884041e60812e84c3add09b9c048162ace9baaad420f30409508fac1027004231adc11adcc239886b7300382,0x1074312a6c3af711a6c82664c3b420270039b062ef298975e23728999c020d918fd05b60269c75cbc0a4b003930321078483a1b2908cac00e50008421140fd600724108d801c92dd5c211cd801ca059003920526c00e48239f00602003716ac5d90e36da85138decf06436a715210378165d0002902103006056ac5d90e36da85138543e1037d5902cb8,0x3910667c00e4b288429600c26408502] 0x304612a5528408ac081e8b916e9ec03a007df6d0a1e4bee00f9d568cf7f4b8c9fdda68aaca2e140eebe7a2e45badb00e801e113af237c00f5000abc931b61252daa71177ee67d3c4c521d576f56580dc961e46c0400007bc0114ec0e625da68ac8a2e12793f72704af2e5c64ff26f4b96359f4f118418e8327824f25e46c092a9354d031a1128418054a2e53e04e23118695f0333215f0338c614393e8b9a58dae04d848d0acf61a5057c3c4b75b11a3962333823e6109dba00a98028404f1fefe9719aedad36807120d1cc02af9850c7340ad6142a257c1ced46b04ad0bb4d156741d576f45d0691941ac8708ad98500119f3d04248b7a1d4402c680145767d68b23b5129329c7f106b44729629c7eb4dc5cc46f014454c8142634b09a92822a2109f4fe07383acd850af29d858dd352c612f229eab4bd00224d3c4e23a3c614054357331235850ea08c0ce35848c8850,u 0x3207c6172 [0x8247216400772a7aa0901256d82482d4c12412504,0x36303749be8290d2c734adf26ce303634d141500,0x5de28da80ec1a0508c60eafb402503b51c7a02100fae08,0x1b88aeacb944da20c2970b3006cc1d6b5594] [0x5d1e216c84445f5085342eb068f4622222f8d5a62755a8429989981e3c989982e3c589982e3c19948c4cc1994cc4cc14b110b6510a70222114e214e6853108a6216f00bc578c723718998c2cbe06b96f18e4eb313318597c0d72c1161,0x42d0883f12230220ff00c250458488ce2006e6445b00c2429807fa88522] 0x892cc0c276805216c0869598a1d8f5b8668b8892cd5676148db4b6e0be9dde635721dd101c07085d4b5bc2fb09e0eea540817c996bcec01b2842fa5990e38584f04389401430e0955b3046c1c5c294122d2df0ba7ea80ae8e372a078a2e339506007a44033a36f3a1d87664467964408810d1691eb6a03698f6609ef61ab76d4dec04c02e779a9ad880dc05241a00778cac2782800c002f195880dd90680053f5b410e16e4102d6efe368a3b33480f40e78cac2782800c0029fada0870b720816b77f188a35ce54d203d0063f1cd8c27120a14004a7d1072c0190caa21c2ed8be03d2289c287ca16e901e9146a5402e37a7eea00450,u 0x2408c437e [0x1f0db982a8240450579820b530450412504,0x5af1367181b1b602c14117a369ba82422813064,0x4a60edc12bd61c408403e2b69ccd0b64ea50477b66500,0x7dab2e2b0f7ef221210b304ed1e51daf6eaa682670,0xd660c458634c9894a6] [0x10a022b4068536e1078814db8820f0c317f704286040a88d42f07304286042aa108c380845c0e3f005440a5dcc1079810aa0645f40847c0179008e8507575baca42329107575baca4232b026156ab017bbbcce7b58eb74455c6aa0eae329b89d6e2b4ee9827d700370ff083cf94801c184236005c4b74266f02423,0x8521083e1] 0x1bc056eb8e4d687779ad482222639644872f5b77c0eb6162285b86f9ad5dc0806342d4cd09e038d8e26deafdeb314a800557e3e72219e8a2044d7be3a571e38b2350b611ce2d8237a8313850d5bdc499d3128b43a7d518df76332e918cd3bd086fb540d408dee8fbd281608e14117fdf47de9d70c30c50462046b10c32602e477a584e8c73d076df2230d08610e38b006b873daa01a1ac4057cb46cfdde881631c7d0b5d6691a77cb7749099d4be232328bf1a206277ca282253c7fa5160,u 0x2a08c07f2 [0xbb3706e82404505698a08ad4c50452504,0x4966538fb611b824fbfac7da08dc41fa16c1211c0,0x96ac0631437b25f0c0253ae38010809a73e4319a1ccd88,0xbda734466cd296119416a63cc29b03451e511992c,0x9909e1d06f0398837d193aa6] [0x10a3f1900586210c4707e0130816f72008460d13009a5e6a8442ce01509c0134a12f6b75b888ccc162afb73c2ec25dc4233397a05750829005f417612ee232a215ba1a9f40282039469820f30084bedcf005a40d1841d50827e1,0x108438efc402b0804d101bb4506883c4] 0x1992d8fa7193239e3b66ebd53032b63d8ca4c8698ec8bec30a60759578110d98ce47391cb249b9b58e817ba9d59c9c7629120645a10c188ae5486b21a64936b1d02b1481291d325a93eb8eb7b0c29468816b2b0cd000167351b64938ef7bf520d32e8de088cac31400f0854de049664fce3aeaa7d564bcdd590a24211a24b62438c927658ef7a9e6c212da48822214e4d884ce64eb0c9c778c2a41f5864e3bc63520f17d37cf4088,w 0x20de00f4 [1810] [] [] [0x1a3cc398a0ea885b344480064803a7d20640,0x112a60a24aca983b2572abb2e748a8c15316d88,0x88731414435a4b2511719efa1efd04109198,0x10b25d7f6b8d53f2f60ae5a6a33fb855395419b4409164e81b1439a3eb94c,0x54a04105504a8db3e7bd498f19bee73e4f4ecf337c6c5e6a5f4,0xab24776ccdd5324754cd1e7bef6725ca9ba3fa648c1ca0,0x10628186e405fbc80bf415ba00c29c3470ee36a0] 0x776c1 0x1bf072e0ef021c4b296420c4064290410820010870c4011014561504030c70000354b92532cca1d6953ba7c428018f44f43a0011874eec9e05ec8300400000f80871008bb8880ce404854ab5522d519807cef,x 0x1c05841f2 [0x12b682474e6413000c2890905719ad4c12412504,0xb362ed285219b01da86801f7a36c3997b046884310bcd46500,0x6b6ded4a11e5ef41b546906b06b546b43041ba36a988654] 0x10d8c196c10d95e30c029331c42c606d5444d0f006e77f8b04d0578bf27298a75d46db10070ca18b188543372278484228e046110b630fc07a19099a61 0xe09060bbaf3824162f89841b5d3894f49ece491f145573896a0044467a0b8f66d80c8fe6c4eac660a6b8abcb8241631a19f95904109d8cd0a1fd2ca0e1adb05b260810b5cbdbdd2c58568a7174b1619ba58b1cdd2c580,x 0xe0469577 [0x432ffb192cca725194e38c141180e16f4d91b531492904,0x6a286b50d0955407034153860929cf01210203e0c720c588,0x7dce36610] 0xc460c3e086ca1a860d1c842388843c1a39086bc0319085b1 0x7e35d4e38528963826caef7129a6655698a5b466554f862ecd38080aa231a45e5b8d7a6a66505546db7bea4d9c940,x 0x604e875a [0x63240586305046e0912a0032a24241606d4d12504,0xaef9aa64a40a24165c68267001f7a74c118f34520946500,0x165a2cc0f6f4a64459794] 0x211c611f3f7202e1 0x4a3c6f746c7eeb0815aa458db58d743acf0f045159742992cb14babc3108016973b216abc755c50450,x 0x803a515e [0x114d018410ca4f3a768c29a0d3c864001157d8ad4d12504,0x7169730bdceb1f7aac3d8c282e36a58bcd04ce003e] 0x5e280b8171001847285b1 0x5f17c3df333899cfe696cb4c7551743f57deaadfd59755141a16d955b38dd8584d40,x 0x603605de [0x94b00e028c0253ae38010b6080495a6292d4c12604,0x5084f30e4f0e84f820df460be8238c95010] 0x10ae2204b28441 0xddf3e3522a20bb7db4fe3e3f4e654eb9b08bdab17268f555a9e985,x 0x203608b1 [0x25141a14c019f3e445873282107800104104520c4,0x1d0366ac5997b371894c81abcc3d0a5228] 0x4b1 0x36bdef7cef8db4d064efad9953cb3fbcda9ee296,y 0x201a03f1 0x16d71ab8c4a58f0696a8eda28552012412104 0x7b741 0x34e77597bb07b73cac73e74,y 0x20120729 0x1373329adec4b4a4b5636284520d2144 0x371 0x14e31aa93e6,z 0xe2871 0x11b31ea62245224b0a08461c02204 0x129bfd9e0,z 0xc51f2 0x2654d2aa86a328037b2644 0x7caf1c0,z 0x60870 0x106fa30208 0x2960]
def d20:List CD:=[v 0xd63a203fe [2377,2441,2442,1883,1885,2444,2381] [144,1681,673,689,705,145] [135512077] [0x4105658208208ad2c104104524c4,0xb2083b5660b20bf305b982a62404161c4,0x168209b69b48ba8a0906a03a0f32664,0x2f26fb683a8a0a06bc5b41d4521d80,0x16524909628b1ac516d04116541e40,0x52d6282c1af245945075149a41459c0,0x2d8a1ac1362052d64cdb00628631371ef962180,0xf5471e808403eb7d242d8a08a40f115d08,0x1049696082082292783aeafbf4c095038,0xa5672d830d90f60b3083304599fb00678a0960f0,0x13304632ca98a4b26f2809aa8fb04098db7bec,0x1c8c026da54c90690f6cea0ba24e56914,0x1a0d3c85b04634cda46983082cae13958,0x720803e41e41f751430439405d2434e58958,0x140061ca981e41e40183eea0f22c6b2490,0x992083b7490864a216c124d1499844c,0x1176f4152b2245096292284b1414410870b3cc,0x13597da6e7b26b75fcae3575c42db852a70010d30fb5e74dfdf253dc849d884adadd2df4bcdb5b0b9ec2,0xf2757e7c7ba791db254388098f6d4fa9ce32112ef64fbd393ea75f4,0x10a50208208a0820920851a3df7bd2b51e,0xd47d836c04da486b06aea408208268294a,0x109a230751f610d098a326e19931060ebc0c2b20,0xcda9b0750f630ccd9331c60aab33688c1d52760,0x490401ca42bca8ccd933e439aab33668c9d5eae0,0x4497412511413412415412419c,0x34115534d14134134d14124d9c,0x34174d24104144d4450451595c,0x9fbf47dfa038a049a4d161810414655c,0x58c7e1d89e14c8e0d48f1d5e37406c81041041cb0bc9b838a,0x16527c] [0x601362107780cea2dd6e2116c603420e896eb7108b6c00e11074b5badc422d9107535badc422d91003420e8d07575badc422db025f501a1075801b9add77211718161a21586b75dc845c60586a33478783eb7624845e28cd1e1e0fc02115203e73060961088833498783eb7624845e28e25e534668f00574,0x20fb0022201ae113add6eae108e6c09ad44e5f085b20ba2ccc842c98427084276007246084ec066cc213b028720a71c213b61000d946e7f084ec0a1cc1e85cff20844c068542aef0847c0fb8ec109c5804e4841de036e8a084e2,0x2109a1ff0bcbc0ef999e9b1bf6c0134c08882108d94a890859c0e4d10c4301b4083ac0cb5452171031083a47d5ec521b0042ba0ca4e10b640642103032dc01290dc08453d22a24211703a541bf6c012c8668b052107463345829083ac0b0d02ab73042060340e45700a59083f3,0x178f80508423e04229041de069d8025185e3e015c1074810a9825e108215096eb2908f6c012d16eae108f634289d6eae108f645bab8423db02f345bab8423db004345bab8423db02cbc010d50c57527d0bc7c410a8c601aa083b4b082e8ac2d2842108421091d6701aa12264e7955884134c210846141a4a75109668844f4423277cb457268bc7c831bf6c2f17004332f1091f7f3caac463e27c4c27094a31bde88464ef8844f4422ef3c9a2f12d61cf,0x170847c12e108f8c0b84c2150421504010a64059b802110008841f18ca4e276fc8823e30409c0185c506f5bab8528e0211b026b76042a100d7081010a87c0845200a10844014210880488210b03314,0x7fa4d102fc921218810ad81d39042b600ae410b22024210c8681b0843202210884201210867805708421e068a8228a277b5e6a88d0c713a4228f1c9a4f29a3345884d970f27c210305ed14f185ad6e84d49b346e340d8bd262909a45bea18f58394e06b5219178150840c01812ae882158c681baba10b06208402,0xca50802b88423e00ac4272c245041f180250add5c211cd8135a0423e00944107580251042b0bfd168817e49090c4] 0x106c1a8a66c32fe9b60ec21e8ec83e1ca8f97d8c1ae98086a41b06a295ec583b08763b20f87267e576706ba60216b226b83e1cbe72d5833c419a3d9f97410814dd848360d452be177f41d742e288a0fbb90e40333f3bb5835d3a439095cb3dc1776fe55d907c09f321580643b9c3cfc1a02a26ec107242b16a381ee6e0372d3b45cd72bc1f76f0cbda1cfe9f73069bac6ba59128fcbc0e9de4ed779bc6ef2c56e8503bdf1aac0463b79d61d06cc9eb395ab5f02cae000adfac9a3e5fa177d54b06c002002b862c2ab35bb6d9ab9aa9f9dd08dc8907f6861d37454b517c1d80d5f3fc95822bf6d3acd09ce45a1371daf64505a53323d81140913f4bd988d058a02ac1c09d588be03c180106cd860d23823dcd7201994fd6f451d3fe8b09bcc3f7282fb2abda9a9ba2a7996af36156c57145c09fbbee61980dbb60cd7201913f6bd3a22181ed5939c1b4ed1778f0cb0605fc74205c1c76bd9522080cd707c09fa6e840e11de0d924e880808b3ccbf1fdb9a98fee29d610f86a8ce04ade798275843a1aa33ade79a00b726595231b1607fcdc8c6441019ae0fff37b3207f82263f57aff1e84c2350185423a5299371ecfc9d6e9e6133c46308e316b085eabcb9148b531364556cd5744f0087e5fb5e9645b080cd70dc1f23ec87203bf77aa00100dee9a62899d6207e4715ae98ce4454345a199e0b3acaafac0dd5e4c8e7b3b1a4c086273ccb6c516c06e491831a6b89a11a1f2e99c1fb9cb64d673740f1385dc6820d945ac04c5ecbc78a5ed41b797f555133950e007b3f3df36a43c1338359fa0dd085408e13026b09f45793d4e1865f306c45ac4f64cd7084077c28392c8e14b6a1190e73aa40c02dc8ff0a881fa19326b58c61f8420389f4e4527f28678310eea9d2261455baa32e1010c98e4db8c1fd30efc7aa01b308a10b0c50fbe921ce91943b8346f41d230fe669d26090e32d81ce0fd6000940fa10203e40b103b918300d911c2160843f8bd73f7130fea88a200a2eb9abbbe1864921e03195bd074437af40296a22748cabab3e02fdb439b0efb3835cd545013740401900c841fa91c79201ef00f60f99ea0da5a889aeb1f66f7bb6a8a32808a0c8077db60e014405fba400d59f3d1a0840a809ba109083f711d080a39084274d1da434c224eb19c3de28893ac676ec3d2013000909cf68d076c10bf2fb55f517c1bda743a55a55a5494b48446035c75c373d571bad69b230c2810020176486548584dd1740b3e6011fdbc8701a6f8a5ed71db35fce506632a9e203fc51084056009f3ebb89c44e748b426c00d5adf802738fa56b69d534f5210668dd61f5f4e025e09c60acf847fafa70384742183593594804c46de084dd285cfd11301e3035145973cdd6744bd8c8744c9184e38cc747034ca71f44c38ca7744481f4e31858dd01316400df693100c00d3f31a22629365dde7450281337b808c76bfa0d993d72dba6cfa5e7d41be16dbf59430c96c00b7ec9c1061800881f064d7357584e485076e2808b3761c0f5351c3e0971d8f5b54145c81d96778640bbbead013144cf90840792d6f1b22bf6d3acd09cd06c59147d01028004f08f0f6f0234160002ac1c09d608e6c20300041800001b360d6148e80d720005667e240e2c0a1f8a1062bb230a455dde7fe4775af67dca5092e51e1862062c722aba57d53d264d0a9855b9103d05707f3cc6305607d38c6159d950179f16435a3ca1308d954d3d46583174473ef484db56850b08dd7038474ff374930860d22018d5939c1b815af4dd153c42522080ced35c1f8095306dd53628400464934082201fc25864f705e0dd1ec59e28e31b54dd153c440ed0e28db516d08654d94116234efd51120059135c1f0afafa16c3942cdfd7054a9b325c53a20830b37f5c1104500fbf1dcc6ccdf811235fd1adb9b027a380cd707c2bebd2943c4835bda185374210c45500fbf294776cd5137df1865cb097c900f7808b6bc5108d01837e197b5b3094c3de8006863bd44df60d0d91975c5070e79940465ea60335d43f4456dbd6261972c25b3b36b403dcdb600f0c831dcdf14c01ef429c11036d8503c776ccdfc001608ef55ea6036f52b35fc865fd6955f3b42588dff4fd1b40ef36c9fa01102c6a4670878474d904d87bddb49c4d08e080cd707c09110727cdb6240f3f45341b3434dfd1f18642530f7004023c8d49f60ff49c02003dc01634249570d8622dbf60c014241078b16fc690060e5275b70040502de1e4e515c018245adb0db94c6b49190db8c0a40b056b4c5245c36e338cf6b46d66b4cf2dd8db245ad118074ca011b4db1258379c80cd707e0ac46b4db346f3a4412e0b926acd12ee1352937454233213431d32345ab1c5a49a136bde21b17af9aa679842876aaa777d,x 0x100762161 [0x95079fa824aeb201c07f6ea240411410492004,0x14ed11422483b03660f51c620c0d81901ec41cfb421c0,0x1bb3719caa6f2e0f0b5814918346cbd9caa13376ac,0x376de9a9106d6ea45ac89ed644aa0add0870bc4c] 0x74c23a7c0444842c74e405514e5605524e56663c0aa7947ddf7a72b1fbe05e5edbf947e92fc21707605f6 0x7e37cbebc3a541681017485626529438cdf0ed8cbebc3da588da20867edf470b60020aaab122210d6ac0c72702086018ecc2bd520e2a31245b12cab5db306d899c05b036912faf0f516f40189d265245b62e80000b61af400cdda90ac60,x 0x100469472 [0x44f69b0edc11489ed3e50670095e60b631412584,0x1999530c6c328eece094eb0e004201f0e3053d823951c8,0x2961fc755897d4] 0x2608854110b6203442013f54d6eae1112180e95e7883064f5bab844697dc40173430a1 0x1556c3517ab2891ce99611d9a50a36a30104b0d0f32ad6c37a7aa2c505e2f75cf6b4a0c1e43ada6a27189c4edcfb2115d23c707c951d212624f1c1d2546c24352b9f5596e546426c0,x 0xa04e2459 [0xe30064e41a18f499220d051e43a80ea240411492084,0x5b193230a2c6dfae8d45535dfa50a054263ec175a48,0x1888305d8471aecc] 0x99c4060412c40dc610b0372 0xeaa8316d7028a8a5a65f4e2eb156eeaf712b606044b6818589fde355d80d2b6e4588f41615b648b51ddf65102c959868f297c90,x 0x1203828f2 [0x3d8f3106f0400317f1b0f1c5461406060b6b04125c4,0x26e61936c6b7302ae58694961ab283400fbdc8] 0x268c3761108c3f64f88f19948c13ea194ac4239623bc13e17d74c3fae09f4e19d0fc5a1 0x16d2ae6eca5dedc0deb1946141a652ef6e0ddda0ce1151b693dada55cdd5e3e371f758b69573765bcb145ae744cada4f6b693d9f266,x 0xa06250de [0x7b0e6814f220800f704241451565b2cec11452504,0x292d840e004201f05b5651e66cd488ef6cc4f17146240,0x5ee45e4cc3d87bf410421f611192c2d95521fb0ddc0684630,0x464c] 0x84016c819fc15bb3fa4b767f740d3 0x3e8e2df122f9a54bd7f304288e0e09ccb121c674cb721dcdf74a0265a9cc11c632ccc6765f268210412a629a02350484705f60,x 0x60514266 [0x6b459786b1f62a007c45906c002c62455698adac524c4,0x7966fa8ebb604a076a38810893a602c319246406b60d40,0x36d58667b2167ef118fb0090] 0x109c2b753465a501 0x278359cbd6692ba3c2b0e9b56aae08a451acfe28814563916fa6ed08a41410efac35b3e4472b660f6312,x 0x804619f2 [0x1a48e785fbca0f1c3590f204b99015f60b6b04125c4,0x246c1a491aaf4284ae2fb303440e004201f1f3165c8,0x187278981fc9954] 0x2750619e08359c02b1085b1 0x30672777169acf2d7e2552185a8ee3f862ce16c62e8eb794ba546ccf1c1c82f95bb75c9859cd40,x 0x803e0c71 [0x157286b076eb490dedfda10fc86700104104d2044,0x3a77340b628730f68aa14d68603b5b9888d490500af848] 0x6320441f09c4b1cb799c4b2 0x2f345b1b69b216552c1917e96b85706f44d7c514175195faf6dc93e7ffbdb76d636c78,x 0x80461c5e [0x1ad3d8afec35a0d3c4590ce04c19011515960b632644,0xd4059eb8578fb3f60a20d6da96007cfadd07692477b665c0,0x39be8ca150] 0x4eb0db185925bb3ae4b7675f3473 0x2d35464cf62d0d0789bd15319cb1e5e8b3839b56ac2994119eb8f71221adf60,x 0xc0321cf2 [0xe43d873f47db4900f7b665fea8c4f41e005f60b732644,0xfa30bdc4ac020cc8a0332d803e] 0x3d0609488186f020d1c44eb0add13af83473 0x3cbde30ccaa88b58a1e75c6fe675acaba78cea6977ad4efb2a91ae910827aed60,x 0x603420d9 [0x5435aaca45036c799b2a42331d087e443810e240411412104,0xb6aec41a48c056aad6e60d5d535a14] 0x846104a13301 0x1cde16e4733472eeb36ceeaa3dcff57c4d05ba2cb5bea8fe276,x 0x40300ae1 [0xb42948a03d8f3126ec42331c7590b003b0a240410412144,0x151ad8c2f6d53060c95b735a54] 0x108c33aa1 0x3688cd3f977148ac95dd73471f6eb0d7edea78,y 0x202040b1 0x26e604335589a79d0a1d5652280b63cd5a32119800134120c4 0x5f1 0xb87adcce38311ee9dd61bad35e54,z 0x200170 0x6b0e628c419ab371836dad9535b58057280b0e61ec608 0xb7559c19f27ab28e10,z 0x1c00f0 0xb63ad09a68c047aae504e3606d87324698c5c8 0x4f63ae1b73f31590,z 0x188070 0x1cb0761ccdd9b8cdf6d4ce46019261ac148 0x1f5c36e4dd9510,z 0xc29f2 0x2c46a44b6210e037b2604 0x7caf1c0,z 0x818f1 0x25463a08466002244 0x59980,z 0x82c71 0x3e8c83d8421c02204 0x59980,z 0x90371 0x14561cc8414c02144 0x59980,z 0x602f0 0x706b631548 0x2960,z 0x78171 0x391444dc020c4 0x2960]
def d21:List CD:=[v 0xba1e40bff [1590] [] [] [0x92f2c10410455a6082d8c10412984,0x63120a0822acb14515a9820822ad38a04,0x20e0005977d5760b20f2aec56417e6c664,0x1c5195059e28b8fa0da29b487320e40,0x220f39fbc8ac3b711604c6dc8bd4126941e00,0x243980b1712435aa91dee287f043ff7917569a00,0xa01281641e7d33c03c820210203ee7a08,0xb4c135e5aab4db9820825360cbaebb424a,0x82aba082a82b0cf5820a228145c4f0,0x1ca3e994c113c5d0411462f2eca908d8edca8,0x47b1376920da685b343040d5f22aca9b7b3bd8,0x5041580b06629bb371938a627de752715510,0x14416a33e068f756e765c6e20eda6a541b5bad1e3a116b227b590a16c1dc0cc,0x25067efbc803f650560ce44b05718dd1db8e340d4a,0x1eb9763973f54bb1c3da7623993a39870f87b1303f2443cdc3ad1e30628186,0x3db981fc] [0x8209d0a2f5bab7570847b30a081f428bd6eadd5c211ece28207c48513add5bab8423da208274286d6eadd5c211ecc10b382f11288685e4e2005910421600b3213cd82f114249f0233add5bab84243b036e70ba3c216c8088421e0bc46176f842d12dd5ba13cf82f1600b2aff4fa208eb756e84f3e079f802b3bfc4eb756eb7108f85433bd6eadd09d5c013950cef5bab742757036c5,0x32108657f6da842b9c0587c01a108180d8a8190856c0db0d6eadd09e7c016502edb0843c0130f268421e009860375684f3185d17c085935bb69421b4dfe9f5bab74279f005755bab742757004c45bab7427570359c013146827002108a638958a13e11ee70413a145eb756eae108f66,0x1949c21bc865230cb5c0680803421039aa00af23291d004e202103019d840b3d6eae122210c780ceb05f5f0d68022a0108b80ceca0586b756eae108b8c0675acc085bc0fbd068235bab7570847c6059b88010e16eae13e210d281642113004c34fa178f80102a1088a277abc4c3c39e446213a2f4769bf4fa34f3cc5b7113fce2194dc3aa3a93944dec0c10ade95474400863bec01a107f8135e006ca277abc4c3c39e446213a2f4769bf4fa34f3cc5b7113fce2194dc3aa3fc34e00069820efd2a7ac8400863fe18dbf02167004240c1dc216700563,0x742d0bc9c410d981d5b06726200a2085558421be580d00210858133b4350bc9c507124109d81cfc9842350810aae329188400468f41db8e771079adb11081083bc0eaf0059a71cec521bf00930420e074aee39d8a437794068420e200577381dcd3eb2685c068010842c099de10870466012034210702cd7370c108381d2a85d0e0342114d5285e4e60854c0165680200d0840c12f301b171949c33bfb7210d980d03ab6,0x84510b5bc218f033bc00910313f0ba10778011205d084320857101210ae4169f882154c06842192ddac26086ac068199b00910421185e4e0578108a8b84d480d0853c099d4068150841385a1793a8219b0ba0746d124e0841de0340e2f00246128cbd5ba052e250ab756eae108bccd4e25b4a2002510f,0x4d1e9217ff80d085340bffc068429e006c8108181e91121092a083ac0e2d42107004d2085a10b6515ba153a410d621f420ec82a77086b208451] 0x67d87cbaced1bb59e0383b9a0418ac9f5722540c681144dbe42f75d6099bf567f8c6dcf340029acf0c8126e381153a4f408314424dadab911b735a696b0d9bda7b5e95dacf802a40deb103a0418a8502119fd967eb20383bd7ec0800c110a28d5d60abbabbbbf45b1b2fd3c07037e3f10c34595c55fb2f6e57794c0831442015787051071db36c8344c43ef369706286e881840813cd7c4dd6bbed15673f80fa2c7c1de26992873f9f218d2082981dd5028e10b02379000a6812f63a2cea5bf37c36d58b5ee208600a7d276ccc69e9a1ee89de0409e6ba4ad57f227eb391d3e3de2692ad1e7b42471a7120a607f540a3842c085ec0a8812f2182752db9ee2f6bc5ef710430053e93b658b1d53dd0f695df87008dbec15722028b33ebf858223ceedd0c214d225aefead9edbb7fb329bb2e1f12d70fa9c78601268b6046cc3ff811c0d5efe05bf1a4482fd358217f6d871e0418a021fd3bf904514f148d66723f8c564620280acee357fdd17f3df6c6f2bcec17adb9c1a04014535de5193d102b918c0e7d3c945c8620a2bbe815e0c9363d7c791c0aa00e3b544406301cf82418a24ebd15d0aa2752ea01dfcdb745d96af767dee0ecbf6bae071f5726b17c0dd881ac45ed38fb97c430418e04e3bc56651160680a2ad5163902c084f8fb785fe0008010a3c9e0ad5606265a1eff6974d002c678be23a1a092a0d67087bfda7d5400ac122322dbdef6167eb31a864c62a7d8311928aefa056a0152d164702feaf0fa37fa10a3b55818a049ae4d700deea2fc43dfed2ec815bbc688d447088f069a2e9ee518e0d77d4081063d33f59a77a359fa4447c5363ec116ab4445de2b21c001319344d0eac8ecf4a850642f75ad50800441411719eace0328d5f342088a08c9f0858e4ecf458c432efea5b6c5610e5f31d703b590e307040100014d225ac1e11b5cf06b806fd98bf90abd3794f8a7d707337789cc73ca200ac748bab6d74b042fd55a21ed4d9697c42f1b8b43e5811a14f0abdb7fb1e0c52bfa42f7c28658a911051ee158a3363d2ce7ef58583d165f2588f8f14d96ab3f598d47e20b4ce316e650dc08e87cadc4fcfd732e0410d8089e498b015590abd37b3d21d49ad8ecd16b6489f0b65ef7db01f564adcb796c96c835bff8b5ed006387dd634245b74276b1126eb5a38a2eeb3408a03890c8dc67301838b516607ff721c9f3b1c8b014773449ccaec71be1d43449ccae37dbe87564210696ce831375a9c5022238a220a08b8cf5663520997024c4adccf8eebe002a7c253b0c79df781debb05eb926389f3bcdb2c408a1e2d9d682babb900639a87bfda5f781ac3f46c30e8e6b0cf03e9b4bb5762901a163281adb05e9b2abac38004cbdec72dfda609c4aa06b6c17adc06c8a0a42a4a1ed2bb726ce14c4f4b660a40d6d83eb1043881c1d6dad2bb4bde51315b6953a1e183df8ab3fdf5bc106b85fd783015a29084b54d80a459f0498908fb39b56a2528ece7f6e5bed014dae9ec90f91a4b5b21732bf042c54ff76dac189e26446396cc6c8554b5d3e34eb45759062a7359e270db43856ff5a69f22031d2b681c1d7e2b6c1c12b0a1aa9edad302bd2e252aed2bb60,u 0x2c0c40375 [0x1dafb747d9fb75fdb189010410410492004,0xb405f282c7d41c4dd4da405ea3ec1201c0,0x16c50c628731720912788731f6c0c1d4142180,0xbed20503dfafedd405006c61926ca18d5c5d88,0x7d825edbd87b185003604c219531c684ebd85ac04b7014,0x281b15508622c4585b1b789d30b1860a6f416050,0xcdcc] [0xe4011103506a0014c423609af006c7201a008ccc0f650cf84237eb1088a229838e16c5dfa085f6620f8c42fb3108c6210844b8448660cc4c0680412328f8efbdb8890ec1fbe0179a6c887ec19ae01293e6cfafc77e138731c1fb60015a36981bc50c191b57805f6f65dc16bcd027084702620eb0653804a8,0x25088f6c196905d00464211057088f8c170980411] 0x14ebe771d3d94d6806a10c781b808427663a623121d4e724284178f6fe3390f6301082147cdd0c34667b7a1210e1034eb90101dcb776fc4c10c5fb527621a72ce608180347bde8d13d59eb4da1914fb7070e73d403da493bf722fc1aeed2770cfdb812aaa2c0cbab81d8be006faf880f51ee42170a17637f4d05a748abbc07de2b62d0ac1ba4034ee817f49ebaede1822dcc28140e744526d253f1e710dd5ca799b6d90e78a3876151e0099dec61af401d0ea8545b38b10e6d2c228ff640c5b9efd0b30bfa6d389eba6156f0d8c0,u 0x2609e0e76 [0x320ba89011415c60820b5b0410412544,0x18216c105057e04c1d7504858001db7b676ec64,0x37115d886a1f80305875e1ac124d0a75ef142240,0x68d6dadcc02eca8ed5931a097c30094eb8e204201f1eb169c8,0x6b0e622c018035b19c87bf6b988bd7d15108958] [0x4286c16590853c01b108e2c1339004d11085804d283e78a73c048267410a5804d230852c02698858c02690846c026922c211f009a82b17108f80907f29ded78513941bc020a3f70d6e895b35ba275706db804c406d980562,0x4ce2214c40482cb2] 0x384f420d9a324a286e7624b603f7e18ae6563ec44e34f5180314bcd118029163ef58033471d9c4410200053545ec01517bc81ac6b673e5014e2e06ca68b000b8800039c0d51bdbe1b8835be6ce5dfa6b2eab1deaa4cdaf121205c3121470b23df1eb85037ddeaf39d9212ae81bafc4d28076acbaef5d7816adecbb27456fae4230e63f120eb5b367f7dbb0b6bd027d366d994f03313cf9d758860afa0cffd57cc603a9dba5926397bb15587fe61608a0,x 0x1a07429ff [0x420f912e04ba917d820b735f60bf3057982dcc129c4,0x1e42420407dca03136e64410fda87fcb0f1d3dcfb421c0,0xbd86087633b98160f5211b01055a151dedbd951803038,0x1b2d6da6568b591362ca6e607b2f722c099e34d10] 0x110843508437084220842b0882108821686fe84ea9407c616ca410b221747842d900108452004e1 0x33b6ca0bcbe014cff1470100446116a2768b17e2d164b232f0ce8bb04236ff2c320480e1b3d8bf247a1a74d62fc91e664b232f0cc18884e4953821c6255162fd403522ab624f0e682329143360020d21ba4f62fc542c000410d5400077d3a00015542,x 0xe0564261 [0x11ac5f485a0a9cbd908c0430ec6240450410452044,0x2f6aa29ed02802614c058033d602e91752823945580,0x7415a250c91166ecdc642ac39b6554] 0x1b8a11050898b3480822c1fc0825401b1651f15a0233 0x5e04f02f818d1fa1d5c0f0ec35b2338a9c08f7a0071430976c06d4705c442456ecaa8934b5d370eb02dc0012cc01df2c340dd49a1e10692d803c4ec8622b360a6329606938ecd07802ba0,x 0x60568366 [0x20cfc110602c8630017e60b1890d156d82dcc12584,0x9418396c829804a71c408404ed017a9b91cb0cfc39d8341d80,0xbac019bb37185ec3dcab04398035850] 0x137c2b7537e5a5a1 0x2d9bb489919790d6090f80848008463c1501cc7f5199b37580698954f97905a2d1bf555c00a620d4f10f589f07cc141c0,x 0x605b035e [0x206bc51b620c8360017e60b1890105818adac524c4,0x379475db02528e2042c490b62aa90d1af60d7ea8b2f414c0,0x2873116d833df759823ec3986483a337d4] 0xa6a15bb3464b7668f25f3 0x17cdda44cb6465d098e51f8a4340484006704c20e70d9bac033c4aa7cba1714e1d43404840029148393b51213c0fb6d2,x 0xa04e03d9 [0x2a908cc724c1a06bc54966906a07b263a9890514520c4,0x70677300ca54c95f030366ca92d585ccd17125cc8,0x14a99260cdd9b8c7518] 0x4b127e183a183ac978a0eb0372 0x36b3de36d4f39c3355623e0ce1141a687778e0200738412685b835961079f5cf2438ce2c7321460af053808c512c72247c90,x 0x6055095e [0x8b414f85b348630201b189010415d66b5b14524c4,0x68837b57982768ed81530094eb8e2042f456620adcfb421c0,0x398a36a98ebbebbeee31910] 0x2608662c2012dd9832 0x1a360e14244182b3c95157d52ee33c8bcd0dd654a2528d14241045486f1477f171e321aa628318e0b08712f2d2,x 0x803c09f6 [0xe6434f1d878e0a7b9f7ca0f1d39907004b99155b6dcc125c4,0x2c6fa337189b2b6686081dcc40e204201f7280e5c8] 0x215856e89e72881d8aaf21747885b2 0x3bb5f879d936f8c393ad711699573cbf6b4ed6104445dcd18ffa9573cbf6b4ed6105bcd5a740,x 0x60486061 [0x1a0a40db1f71cd01a071d7d903204c09012410412084,0x6ecdc642ac03385b9d0a03385ac585128ab1d7e95bf4608,0x852b3590482c81dc40c] 0x4458405823f81 0x39a61f73df2cd440f29747065e96d5c1a65562fb8b4706948af6c5348cd2008c2ba1241,x 0xe04c10f1 [0xd7d968ba973992005ef32469a0d3c9225000452184,0x6919cb7b1a6d4b00aa66d7d8ad6a80abc92387ec,0xdb5359080ac951465bbcc] 0x2a097a3e0c8d93c4876034199b735af4c871b3832d88d2c1039e5c7c19917373c2f7103aa1 0x7ef538915943e5f0c82be6adaf4d10a3ce88286d389ea4a0ee88c69412a378d339d294545a,x 0xa03f285e [0x2a477b6617e28bc712681af2c641c00ea2404d5a64b632604,0x3adda67a497bd161ed3440c9fab391881c408418de08] 0x9ac1341f102b0add9ad27e01 0x9cb71a91d33f0adf24395410aaf869dd10d5d7184d04414166e365a3745079b7252,x 0x204c095d [0x294e61244fb421f8fbf4fd900e03a89011411492004,0x7a1efd3f6b8c7dfa1ec7d808805ac0fb7f65cd4153008,0x3587314634cad9b8c] 0x83e1 0x2c8c5644d46c872a6584b1c1933d0b279d2439742aaaab487,x 0xa0274071 [0xe0d12a6a7a89ec2987b0821183fea0a6031890504520c4,0x4876ad0c] 0x4d104cd209344c7b311344c7b4143941 0xaac6cc3cecc5bbdec1e5e766a4b333cb99b525c75e76aa16,y 0x402006f1 0xd8327dadec7b34dae5269b0499311e4d095e434812a242412144 0x208fdd61 0x199b5d7fb54c771b99b7afedfcb385ae54,u 0x220870 [0x51b60ec399bb37192ace9b4b3918006bafd34612c248,0x4dcc] [] 0x7fbcde91e6b16d6d71650,z 0x1e2070 0x6dd1564cce59b0c607d6ebd85ac3b2ec9b4248 0xbb8fdb24b777569d0,z 0x1a1070 0x363ac11adb36184cfa59dcc127af904208 0x1951bb2d3f6c7950,y 0x201242f1 0x8c989edaa60988421b910c04309052184 0x7bec1 0x146ddb52a2d3e6,z 0x824f1 0x25e63208466002244 0x59980,z 0x88671 0x1ca61d8841d8021c4 0x59980,z 0x94271 0xca6154840d4020c4 0x59980,z 0x70971 0x391444dc020c4 0x2960]
def d22:List CD:=[v 0x5012e19ff [1597] [] [] [0x14565828bc3141356182dcc10412984,0x20e000439abb1060b7305c84829a0acb051c484,0x3110640f9907caa70c5409f9a12c9369219c0,0x463ed488ef713c781e3f22f39ef9e17ef2c3c746600,0x1b9925360804a05d71c7208084080fb505650e648,0x2a7cdd063d1b610c31ea08dca5359ba5aa181c2364b0,0x13e803b49046d9b692f8c4dda5ecd0810,0xa20b519f06c7bab73c86bf65d6d352a0da10634c54e66e33d9d50,0x10c34befbe82b97d0060ac19c97de8fbc737836c1b4a,0x39763a97639261e6e2607f21bf5a18a] [0x159406842b9882a84221dfdb6a10af8026a0806842b1add5ba13ce6b756e84f3e07768341985bb92dd5ba13cf802ca2dd5ba13cf802ca3fd3eb756e84f3e0776ab756e84fee00c690b6badd5ba13fb8210ae015d210878026a0801086625aa25bab65748421baddc02ba4210f03335,0x171b842d905d084420aa5c21130ba2b40681cee0034e8027805104212090117129b685defa086080aa5ec107180d039d501b40842e24800c2a009e71610c821330ba07db809dc09ddef107d102d11ffae17421130019b29a18df9826842260084c1742113004c30ba20842c0159110330bc9c2e88210942e8f0062280fbc522f5bab7427554522f5bab74275703315,0x84d10854108441086f130435105c5ea24216cc21b0421b303bf2] 0x2b9ab7f4f831fc6191116003002d543855f29633244f672f3e1ed4860fc3d8408637fa98141138801064a101420ada1328741648dceff3e410a10218220b36851f45d32b6e157e56147f8efb6b346b08ef876784292bb45cc66445a2d53a8e2301ddd49281b950c6887a330a3a1b31389a6bdb910a0b4a02e6b9618b058ce73c4b0d998113bf42961707bc5e077e77acabcee0856e86878fbf353df7f2c455129f406a8ee7400240d720737e10203bf4bde54c7aeec8a0a03470b71ef1de0ed0b3e88c2197e077ebf255ef616cf4aff43d55ccf57da10d02087145f50c553cc721d7fc7c55b371376af9d4573c1ab522f03b77c92ba517002d654d1f7227b22dcf400cdadd8c1dad1e1b9b3ae962ebdcf45bc54b5b2a4394640be94fae8bf8c2c6312a12a0bd8afae8b79892a1260bc84c6804337e1c5121959eaac611a46800ff799524c4630955e4bfb23a1c9b77ac59de80ef710de0bcb1b5601ce777138603ac9e9046800ee60000a884c7c585121b58ea6cd3d581121c5aebad125b16a3568ae3b1222a8927aadeab435c4b99f252e80,u 0x320ac42f6 [0x4504105698a0820b4b0450412504,0xebaf60f208630f62a08dc7580b211806f60b30a64,0x201281da8e204201f05b2441ea80c399b117ed998ec34746180,0x15560904d706caa88c2d63beafb68d0492b83b604a,0x4b44d27622cb19e4c2f768fd2f7a2fdf7d0c10,0x1952397b0a64790a566b2090594dcc] [0x42960158ac211f00ac623e300ac423e3012010cc47cfc6402b1c1d5c9d6e376b006e8200a2107045a8200a4107d822d5108d85d07578056411f3901e32015912a8853c80f1900aca00b87fa5623e0bfa5623e300866b75b888f8c1dca1417c0480433,0x108a2044422908411282f884121747885b2a922160aa49042a988020900561] 0x5b6f4e45a73cec8c1cdd961032e6c67ef41a122a9d653f6c0473d3b9c19236cfd01f455ac9c9680a31daa0525eff8938806ce1dcd69b3086157025b050cef5685a1288c6aa0936f7ea5754e037119f02597540bd837cf90d8f56067db0186153a0fcdb1a48c780a4040cfde5d4d5b1abc1cf2e80cfa77e6dc9199011af09396ce8611192d4ca2b2ebc0d3ba073aac0826e4918802040f67ec28eeb005138ff8d6bac046399569168b074af9f076aab037dc01ac0c336449339181fd8404106d78a8e2ae7fc4499d640103f2200e200474e29bc7dd3c053456c01c022039e23847374f1151bd0600574d06ad9c0ef4936275a7bfb0808d505f6a038c937df9efec00408758649bb080388ebcec6002ab5c76700511479698cf01151db59b1b91b7eff58080642,w 0x1410c02f5 [2326] [] [] [0x89f35ec01a10bd75902e04289010410410452044,0x1b147b6822883a490061cc50c62873f4988,0x1c3381884d58350cada48a426aea5ac163a1ed3dbc28,0xf43dceb1161ec3d8608204a925b7cd3ca8bd415518,0xe709a08c31a34a206c21d2292b1b18baa65c90,0x3b9cf93d3b3f8e1bb1e9f1bb3e20eda6b66d5f192e6d2d981ac832d642eb6c6cc,0x4b16654dcd983476e5cc4de06a50a492746db73ec31c7bbadf4,0x6a08fd0278833860e4985b0962cca9b9b306eedd74e0,0xc18a061805ea08d99c] 0x1c4b138979a06227518dda229098c002006e20b7f006e4712b008242113006e4309b006e5f6133733add2e8792a55 0x936f0f9f79390d976109860842e0274ab917123d5701821093f550da1108373e408800102102290c9b3a1c0f8a30030e159c94860821023658028309313eb060d38140080c01bb1f0003081411391f1228b74256040415d8218005320d00382d8569cd5400d9faec860f88737e22d0031388300fdd55436425d088424749463a1c0c969400f933da234805e20d0dd436425d8218819c0e21d74842e5e04d1903a7df51cae0d027389379c0946b513d056921225e80b12f69f80e60d94e24de497d972b4319143c4e24c941a65b44330204f1f9097608600169ec3f8932518e6e0ad998a92,u 0x2c09414f6 [0x391486701ddbb090104d5960826b430452584,0x1ca328a18fdf6248ed62b32dc5c7fd80b419c0,0x3a2cdd386ebe286d64c60edc129d7587002100fbdc8,0x1750165ee89fa5ed2040d19532e60b52c4d2a4d366068,0xc313c3b13e2a0833143988b6c1938a6] [0x5e5e215301a0fd51448793285758dfbc4231a890f2782e335121e4f00866668f5121e4cccd1e211b07567e6af3349da519018846c4b54165c1a79c5d162110c6fd60104bcd5e1e9b1004b434f18f12233478f13c42360ead0cd263c4f5ba27af0756a2f2f50840c2e80d07ead0ae780ac1b71add138780437,0x12844230c365c54ce21081832d5179a9cc06e52270096a2f2f108c42f2ff08463] 0xb25ad0d372578d5c01281d81750a6206240056018d06e44c22171076dda62072071b722213305a7954b720fcd8d96245943d50bd00bc33ad80f61becb558e47d60f2a200815c052878b7917747069010106b990d926bb27ad3dcb02fc80082059135e8676d5fb6de01c87c748c16e71ac0570d0028eec00278c87cbe9fd44875ea45844ac95efa2e41a9800450be250ed5d007b1bbf1e17e4507500388c5172560aab9419159431fdbd5388ca481296ed971e2dd3cf9c07b1439a2d77121c292ba49f3b760,u 0x2a08e1cff [0x433810c245e60b6b157582fac1157582dcc129c4,0x1a803d07af8be5878e0ea20f41ea0a0f1f121a40,0x2eb4a3006071c8484080fb914b187b8923bdf7b86240,0x6a02ef98030e60df3137e8c0817b779405f342f389f0,0x79b97638f352ec7820c89b1cc] [0x33af086cc0158c21184410b04108b802b15b1085ac013cc0c842192dd5ba13ce686edb210a9dc0a84222a1bc61348108890927db1085ac0d6d001605103b5bab74279d16eadd09fd3835cd6eadd09fd44486d6eadd09fd44488d6eadd09fd4,0x15842107005720ba1083802b9842d881908442] 0x19724b807f06105569f3cba281ee7025808f5800236c84b1bda72e0f5d380774f150d56712870e15dafd7347bac095823de062b6c84d19f9e5a369435faddd3c7fac0948f20617c89bc6b6c9b69267fa4cf9831cd2202a239dcb478399e3fde4f73d84780ded9bdf6314c0a1d459078139471c602e0ee454c15180a251f761805cb3cf929d39e79ee53038ef9d2cd92bd70992246d53402e7caf65a91861a057fd6be9c18c01408c000db59e3df55b2694e0286d17ddbb7804160,x 0x1e0910a7e [0x7417e6c6640410455b62b6304104524c4,0x4f117b58222d035e2e208a14c110641b010a64,0x3aeb0e204236d0178823d7d0e64c434cbc1615c0,0x60bf4bd864843fce4603597b086f0cdf50e4b103412783b704a,0x2873c411b60cf7d9a50] 0x21586468391104210839160674410a428085225042910a0be173d842a9add6e211c58195a21a26b75b8847160656b7a5410a46b75dc84726071e8b75dc8472600ae90847add77211c981d1aadd09a92 0x2ef5b1759811afe98fe302cc88062218c8a4b0c0d6ffc7944b1ed8e4cfade36f12042e72292011cdba3f940b3318e796c1aad0e9608630ad3a06c8a66efb362003865b0eab43ac1b1ef3cbee9d8c45cb385f7e72b5150de0513cb80be252c506f06e21c75276da0d7112c35262860d62631083040dc44f4dfd67890eddd3b45f1eb592,x 0xc0540a5d [0x144180b432045d7b10683afe486700104104520c4,0x11acbd87b0d1095768ce461a451a4b1d74ddbe282f642e148,0x12c51b608c459bb37181ef55910] 0x18383839820960e6096583bc20102a88850232 0x6b660e7a4b05ab61b721f1e03aba2b96527dcb47114427118571d880439ba4af6589bad6cb81c2b7caec969260f1e4909dd345018de08151d5fa44e25a764c87a6f55ca31cfb874d16a18d4377c730,x 0xc0601175 [0xfd8281c72f60923200c017726240410490452004,0x1d2ebd85cc1d0a2228067eaa18c9b5129630410b44dc0,0x74ee68280b143988b50709b8cf4bdc6bc3da7b005087d8] 0x2f0883ac02f117bac41d17b2fce25e505b05a3805551081805f2f65d87732 0x1590570ae921e52c0b12e7053bf00046084723c918df4225f0d708e77adf26bcc71c0cd08a263c616abd824683c688d8db621434a4138a86d533f33d54c1df28a8410,x 0x8054295e [0x602c31a0b1d39907004c1eea243455a608ad8c125c4,0x4edbdadac2b3765481c408403e4061cf905a0865e398344dc0,0xb1bdb37185ee51fbb8cbd87b0d10] 0x85a19e615bb3ce4b7679f3bb3 0x1b44db84f22fd0b159560e39c385d60098da78ea2b1cc3c276eba531cc265abc85aba12be1750a01a832cb24e243a4860118718c10,x 0xc0430b62 [0x15bd361ad035e42b800ba890115758a2b5b14524c4,0xa98fc9a8fe3e8c306b6dbdd26ca8804a75c710210fb0d658c608,0x2870fc] 0x10ae2853142c88cec539434881 0x71cce34a38283336c947073beb3c1c590738c9cf21468b690ddf5f554d0dba51ec7592377d7d533496e7ef39416777cb16292,x 0x605c24f6 [0x3331f937eda0340a0014504559608ad6c525c4,0x2a35bd886944866edb140ad6c99c007c36c15c24cdc886a600,0x110b64a7b4b9804f11278921ee899fb4810] 0x42b88846187f588462 0x2f4b786832019d93e5a0212d5a00e78c9175ae001570c709c4781a5191551292dd0c518f330e8ee5133e3f62960,x 0xc0309071 [0x38c12163acfde212427baf683b00c62414114120c4,0xc5bb33319accee62bda3ca3e28] 0x10742012c42e8023205c5802d282b422fabb805f3 0x3cf12c76f74595d54e50b3cefadf448e0a35d21fdb67874ada9f5bef9ccd64d3b7ad5bcddff8b6b2658,x 0xa03a18fe [0x264866278b8883df683c721e407870c241579b730452584,0x46ccf74189bb56441ea61e5b48a00fb917988] 0x9ea1e0423902108402085b1849a1 0x1d7d71c3ae36f3161669b65253e631c1317637c5f169475c4f168d6d5cef8c7e9cb475f5eb1ec0,x 0x80482c5e [0x1887e1cf818f34163913004c19010455c608ad8c125c4,0x1e6aa20ded6e61a1422b840e204201f1fb1e7c829cc2486a1c0,0x137303de8b6510] 0x1988c2288118452a9c1 0xae1eecfd6cb4d4b6f0779e344d85bdb5d023ca6c550244cfb2bddb416ea3394f2510,x 0x6041817e [0xb90d39f2b762f537d414c0806c624057992d6c52544,0x6a995cc1dfaa8a1ab7b57d87814c02538e2042f71e55c8] 0x8401889e108421 0x5cf271051945666338cb56b59fb59d315970d1db579d6195be477b6eb8b694,x 0x603f2962 [0x1ab29056e7d80b1161ad035e41c00ea645d66b5b14524c4,0xfa3215a6082d2d1845365436ec98d1038810a8c8] 0x25f8404834881 0x255cf4e1a2fadf15537b9d9acef9d2e56da5f46bd91c11796c916232,x 0x4033835a [0x71c40841cc419b11a8f3af60ea83380c624606dcc12584,0x84b9820cfb37d476ec4851804a] 0x85418421 0xb52caf79b55cd2354b7866d69ddccd9fc57edf54,y 0x20200e71 0x137304da5b5b9899143f61ac3d87b4921197e83a80ea241452144 0x662a1 0x23873766957736387b9fc7b74e8,x 0x20240b49 [0x7ae530ed28ed585cc498f32621178e090ea03aea240412144,0x360c87d8] 0x27a1 0x157fafc4696bb309d6ad9476e56,z 0x1e4070 0x1accd8833566e30a9adb2b6b6f0b58761da212c248 0x36e3fead257ef3569d0,y 0x20181931 0x25e677b3b987b543f632474b41e790f204b890521c4 0x5e1 0x12dbb6737554d14,z 0xc0370 0x1b99bb371928303ad148 0xb5b1c0,z 0xc2cf2 0x2c46a44b6210e037b2604 0x7caf1c0,z 0x850f1 0x26363208466002244 0x59980,z 0x92171 0x14561cc8414c02144 0x59980,z 0x60a70 0x306d831e08 0x2960,z 0x78271 0x57d4455802144 0x2960]
def d23:List CD:=[v 0x301ce21fe [1353,2441,2445] [1680,145] [] [0x4114104158608228ad2c104d24c4,0x41a3e85340a3f228c258241c009ec10e60c18ea664,0x42289b0791b61ec5c869e3803e512b73ecd420c0,0x6b60824be0efa9ec1d941281dfa638810807c1ef208,0x44186b7454040988b0d6e8d80ec1d83b506c8a0145f0,0x1ec3dfa102080ba48159a8aab66677305ec10618694,0x624ca08c9106fec500181ecbdd231f7ecfb2450,0x457b1780086919106d5ef97ca5bfc2b4796345ac89c3a0655905ba415ba0bc4c,0x208209a682146a339e6def95fbe4a8700131eead9fbd4be96e74,0x363152193346da7728c1720d9a90a09a68214a,0xb362edb18a72fbd93323726e518a90c99a366cc060,0x226834aa09a68200e36314e5933e632a0,0x44544d34116564d44d26124b5c,0x7b3f65cfd01c50200c18674d341b4975d5c,0xc991c2991c2191e43fe81032da58a] [0xa242168972842192e50843c06d4c1c841d1621b0427607de800962a743885ce64b544a04227b942ed990022c1a6fc2f271042c6077f801133eb0ebca58d540a9c0681d5e0046e10b7802f109d4e1739842998d37e004840340eaf00603004c186c0c013082437004c2,0x3581085910859c0d1096e84ea92dd09d5c0d14c243455a8427903f76200233] 0xc296e580c2531f8ce06e1355ad914d9f815c3a83813dce240632a9146b413871459ad1427348cc48b4cac42d1da0ca845414364382b1c314f41885613123e9246f005c17eb1b94e2ef6340672fcd50e24f1d864168f1d101b0c5d8030a4ca502619b8aa83f0263f5c234d6609dd01f1947a0323bba73b479f5e9d68d8fe2e7c09d7287d32c53f746ea2f5454a9229619aa8ae2a5f90a3499de82ea137402e0aabc2c9ac295b830c487a18629f4096edd737026db080371532a90dae8efb659fc00ce4ef7aa0eb80c580e10e11e81410a34c03da03c4038e7f24d11989e4741ac8a28c024693b600823e84885a4cf5c80b24315065f08e5004381046daecfe52c02d9c405feb8b3956051e7a9145b9f7152bcdc0a0dfc57130ee59c7f475147d066ff49620168bc4472ba2b8a00268f58218ee499d8c4fb18c42d267e4e8560ec4ec555e5b9e001540055185212075,v 0x2a1120b76 [1590] [] [] [0x4114957608208ad2c104104524c4,0x3694060900c03fb6f60b208bb5660b189016204,0x50f61ce39803006080b1a640d007e686307121a00,0xc304719a2d229216c555205ed62f7b61d80,0x61b7429994c17b0421eab36946693437b263081c408403e,0x10843376b6c0467bc8034e60ae31f7e87b0d108958,0x1a8da81a3c0f2cb8fc41db47212b69b280d6740d8a1cc53425b68c,0x1282b067235ff7bef6acffbdc7b1c7e0cf033d49e940a2f46,0x306281869419fbef200cd9c] [0x651f15a008cc420088561022210480a8840c01118c1cc42b100d1084507c35bab84471200d108580563334da07856b744f3a85221150f8842c0211add5c223db05bf804255bab8447b60b2d21446b757088f6406d980562,0x40110a008c94e29f108461084a55a27e2108c2108c9fe73777de9517b7c6ed8cf8834110a980542] 0x15f82349b2e46536edac6cad03b7397090155062600a89561c781ecf6819e3d0ac90e31e0a36385596ebebf2c4eeb9fb376d637e1b79f7f2b176fce810604fe7ad223dc56cf42e2280808220030647049220222a71d404048550040104214cd0df4009bb65873f54056796451f04b6f07356c41c764c5d1c1084c3aac14efbc2366dcb7c1fa14f841c670377686072ae2b77a22f27f01934310d40a4dcb7aa99c401153be8390e127069372329ad6365a86001c3990b12e2b7ee202a8ef1304512afa620f50f722dd783d8200d59828c1cc36830125822e63d871000150154c7ce262028c1c419cee0037713095735f98bf61c4762f634b54498617f24402fd8711d8bc0d19600656715db11200793e3f429e4cc2f80006c485d458537111162c4861655b37d810a0,u 0x420aa0eff [0x2ec24257982dac55d60beb0455d6dcc529c4,0x6a04f7983a8baa0d1fdc45219c06f60830c24,0x725cc5206ec477bef70cbfd401e83d7c5f2c3c746600,0x1e97b7794a4d00f7370653e0804a05d71c721210203e,0x1d88f041be8c0f77cc458b6824ddb137e8c081236a98,0x3e6e5d8e1ec79a9763c] [0x7fa4c2abf084235bb7b4216ccfa85100821054028110843c013110ddb0bc7f841042b35b1085a20845c015890def5bab7427570331500581084615bab7427f7006348492d0ddfbfa13ae8b756e84ebe06b688913add5ba13fb8206aadd5ba13af8027a4249e86f1add09d74,0x21544048421104340e0216c82b13036e20ba10824134c1082628207c48513add5bab8423db0040912144eb756eae108f6c0b2dc0c882108c2a882104c682b085a24289c6823147fcc0082a176d842c10559e108a434119ed105d08415,0x85b1] 0xb78673a23ea236c6525cd6f5919800a8e9aeee7a6e78a6e8ec63408516114d428dd56c8c7dbc077be63408d1c05f5814242beabda4db8572a53c3c051a08318e4234c695f29d1735da102a3b6bf121cc9605583063386fd81a9656bfa6400c77a3c2977ea2de37077ab5543d77c0f243710930d6860cd9c3091a3838d1227e62ba2456df95b64f80009355f825ba721e797a36b1e4e02fd70032f3e2b5a89ce17aadc926ace1a79e7cde39676cbb293e40ed96ad0db9b82c59b697127fd6d5d50e56390b64cdd7be967d0a1d50670347016a01c7cd3c4f5d35e020e0a7b502e7ee834b02f28192a2ef68a60b8c114455372c63151d2066aad9296a8b426b9a910fd5a8f310ef17068ab8145b409e63fa8eaef5a7b7bfd912b6cdaec9efa0,u 0x280a40afe [0x2c830a240410415c6282d6c11412544,0x5522fdb331c0586b0175efd07141e3fbcf242c012c64,0x2496c1d5f6804a77d51c408403ee40986b0063edd88,0x282040ca9adec173666d2285cd99b4963a0bacd06845b0,0x157ea6d52a6dac8ad165480310789335b182fbeebee9b1c10,0x1952387523c] [0xd084421a6fd4107c610b5802b12206610b5802b1beeae329b8800dd0210b03bbc0158c682310020985d1e10b64f0378d047534410ab8196e0080e1bb58800dcd70a3d085835c28f42160c2163004228311c6329380903ab58225d6eae108f8c0b8546527085b2,0x42a0842208422605be4608402] 0x10807b981a1b6857ea82156c9f9005bbad58c00a214efd28f415b802ea5a07ac03a5294326469b1250205bcb630237be006ee3b00e3063616a35d4ed1fdc6ea29349208d35a3e043b405f42c50318c74aedf918efa8fee39b8212388d7ba8245363aee928eb7cceae63d144f0429bb22c00c38b1dc3dd002df31f6404d6422b107434dcb0070b6efc1231d83c4001cf7d86b7f0caaedfc3048c76c400358e0a49a914991bb2581975e866430af7bf41097b7c3504a7bdad4fa1611c6df81dd992416fe2a5ac2f35a42,u 0x3009b297f [0x8380179820ba89095d6ded85be36066b5304d28c4,0x5ee819a74c960d7a256e7d80b0c624d035fa86b215c0,0x71c030216a18c098e33823bdc507e083e6d28efb660c0,0x5133c61a202f2ed2908d942a1b995183730500940b2e78,0x506bf2e7479a8137d18497b9c6eba28c95450] [0x153b8421e06b26290d85120421600acb0c97c212e87978bd3ba2f4268f00578bfb234213cc82879083b386c3c68375bab74279d468375bab74279f03a7583dfc522f5bbda4cc8422b2dded26642117038b55bab8422f301a148a3dd6eadd098345bb9441f8301ea45bb9441f8301a03aca8193add5c21179b0075982ddf08592086d1,0x210c421a8421104288422e00ac6674288422e07a28184c107c6034215c82a7708432] 0x63454636c0cfab0bb8a2d0cbb485033477eeaf17e30411b342a4fdc02f43ba16758aba7e0779da1c6cd92033d59065599ad05721d79ce81e0981df540b75d0695b460791dd04d0ef41be04ad2968c6ca5863cb16a6868885ddf583465ac41bf80aceefac4a9279d6d086eb0d6e282ef8d8269cdb01d6ba29c6a9439d441d0846d83eecec3b81e8a877890fdd59b38d17a0700348800adfc4f810e7c4c4b10dc58b3152fcc4c8296ea2571439667e55178eb195cad5b4,w 0xa0e801e5 [2441] [] [] [0x87304398a2904804389010410410412084,0x73887b007c8b9000cfdcfb3651576a08ff921e00,0x9e6011071cc69a4aa08b7becd7688a06d90327df5d08,0x7befbefa102006c959a5cc459ab086a85b3b98,0x16c58415c210c9096c8220d24607bf7d5050,0x4ed4aa9408a0cd189e9d9f35b5d6aa74da177d4887a357f8c8836a1522d644e0b2,0x602c01f200f9f429cef7def16cde58d27794d41b552,0x4862a186c635c] 0x6d450882844c68a404b1a4ce04b2 0x857cdabdbc4e0ee47c2e133c1f9acbeaa3c1890ce801554011208446dd66b16e401ac42af1faf1ce00c06b802109f1301d584d41c0ac00a00ad5005fc4b21277bc0530c069d10865b028f3e9a5a2466d1c10c501a2826f07608b1007c02b5b3f602928cc8f5e2560026a1914a3fdfd88562d709997524f6020aa33d0ed0,x 0x1006f087d [0x13418fe204d299010003bd76c6240410450452004,0x3066ebe93280b243de3e931026c758e344200,0x6c3151b53147e8a880b33a75ec9e60d9f9336d497680a3dc8,0x50e68803e441ad0c] 0x8d008c62e00824108180111450d6108180111b8e76107c400a822140088820d300542 0x2745d5245578d2043a206301b879903d3b7e0822c866250e210cd0ae81150f00d7846bd683580ed6044f662302f215d8163041297161c27879c98200ce6cb0086f45d10de50cb55a8221068a2b780044da0,x 0x100400cf2 [0xef6ccc7075616fef941e00756182dac10552444,0xa607e6448f041be8c30618c35bd0a0a68247001f73e8b376a48] 0x1c9883d21106d83d22108c3100700ae4522062070c4861 0x3bd2dae48700c4f08e8874b28af513c239379a4216c6983c7139e58acaba4a46a9f73cb149b395f4cb1446e8ae746e6564719c9a97d612c5a7676f7ac7c0,x 0xa04d0171 [0x1152200ddfb0a608d023e2906c01909050450452004,0x3a9838c9e6093954396c67680a0c9e3a80bf71258c8,0x143988b2441ad0c] 0x43121066b8041201a01048a43088381 0x60bcfa66ef5a4721593078fd2b654358dd551a420b691c122b2d8b2c5b7e723af291d7ae456e6db4d5b52f653341a58458,x 0x804e8161 [0xb45c82b75ac0587b2f6803f21e400410410452004,0x75584c616dd151d1b24142b0fa04cbd8b8ea1ecdc8,0x2a96c398a6ac25950c] 0x2f8a0e0507c32061 0x39ae7b1b414695f1603ab3a215258f26b5b930df2de558c5258f27b7b92edb4716ad985b5fa1983356dbca174da,x 0xa04e5071 [0x69f2a81918cc5da073d259241b01263b1890114920c4,0x21fe773022ec1cab0409996a197607ba45098c8982375248,0x5b49db85419b8c97d8] 0x8845def7183b8041492222fb07de6017c5ac805f2 0x577c6dd586642d804757d91ddb8b28e0bcc2c7049ac5ea437a651c19d33d9d5fbc928649b717c16e028dc35ecf7321c0,x 0x604f2166 [0xb45cf86b40d78db215c05f60ba89016162b5b14524c4,0x3ec51416451d76c0940ed47102108bd4f1922a406b60d40,0x7441b6b3a19e9934d90] 0x213c40703a3c1 0x2e9dc4f0387db570ac1759aac00a792e44672754d158d371151548fac75b6dc9b21959707072f2,x 0x604a915e [0x1a67ec33f4e760f94f60a00dc1590c60318909596dcc12584,0x1a80a0eab09ac163d4c02538e204201f04b5525f260c588,0x37189eec981b5850] 0xa9915bb3a24b767473553 0x387934573963a66c0738c3a5d1a0188299611473aad6d702ca6504445db23121f91560,x 0x6046865e [0x30edcc1e7be5067e20c87503ddba990d5d60b730412544,0x1ef958d05b9805d9530094e38810807c80c718a1ec9c869d80,0x26e617b9610] 0x10a820982b766ff2f33 0x5b73dc9d3341b66c09898a98c7c5546fb174002ca435f0ae575fb29109172191960,x 0x40408261 [0x2d0266c4721eebd8fb411b912c031890504104120c4,0x18b2667eccc63a37558c9660a8cdd9a8730445fa1add88] 0x107433aa1 0x31750ddf2c55cfe6d950d6924391ae7ec1f7dd6324391ae7ed5351cef65a16c76,x 0x802c08f1 [0x411c1ea0208e0fb39f479d49000fcda107c8830012204,0x2da230d999d8c7a98] 0x437611bcb88bc2272d8de5c45e1fbf61 0x1aa6965fe7b346bb57bd5d534b6a9979f5a35bff64de57ccf0cea967e216,x 0x602d2061 [0x65468505ee91f69ac1c8f5175e81a80ea240451492004,0x2799b0c4466ebb3654] 0xd040e81b8d01681b8d0604b3 0x3768fb7ddced14b06977acff82c8795fb9bbd2a56,x 0x402804f1 [0xb7692a86ee5140db0435c3b11235462400412492044,0x65bc4c7a588b94] 0xd030fb901 0x36b3fb1cae378596b7bccb3aaaceed62294,x 0xc02260f2 [0xee6035c20a06b842c1b61cea48441660fa20a306037b2604,0x8b98] 0x3eaf0c4841890c3066060cb0840c1 0x2eaae6738f6fa95b56924f2691cbb949c16,z 0x200470 0x1ad508628c4188b49187ec6d94b5b989a6296b04208 0xe1bb5262fdb7aa10,z 0x1c14f1 0x464caf6d4b12fa92873f5fd84918a313c8290152084 0xfd9f4b862d5d90,z 0xd6071 0x8b79bcc362824520c4 0x1b3d1c0,z 0x809f1 0x3e8c8158421c02204 0x59980,z 0x82971 0x3e8c8158421c02204 0x59980,z 0x89171 0x185615c8419c02184 0x59980,z 0x601f0 0x41be8c7518 0x2960,z 0x61170 0xb066e31a48 0x2960,z 0x50870 0x1c19b0c 0xd40]
def d24:List CD:=[v 0x3613611fe [2438] [] [] [0x318901041141056582092d2c10412584,0x1342582082423001ed3d82c82dcc10f6e424,0x18eb1681934fa087b411f81b94114d21c80,0x1a7d1471a23af92f608b11deffdb0f3f146240,0x3b7441c02815b182092f860129d71c008403eb7a08,0x37b08620cef61104142668ca9ad34954992c0f60d428,0x11e410a66e03f43dfa182052e944958237518,0x74ecf64d6d33549d885eda1439c210cd5a48cf47dfb3ecd6050,0x60ac19c6cde93bc737836c0db52da502492d466dfbd886c7ba7734,0xc393c3b13e30628186f7d007c81bb4f5c] [0xf6e3a0c9e1b29e122fe1b628040e2f0054a1042114040ef725b9b0e862b8a44e20a93c4109f820e6040b607ef8026105d07c0845c01352b088215302df40d95c211301203429944213b04033085b11a06c0684206009a8862380d0840c01350c10a8460854c1160e02f75baca423db034155ba13fa4b7427f704213,0xba2153345ebca39b91041de0b3bc7529b464012ac2108421605fe8b440fc279cc215c4410ae406421008215f004b279a7d78ef1421e1086d4610b1e0177006769ee1f002a741e3303a55] 0x11e05c83c398e2b5b44deac746c6e50255dd1c5d05baae837b8b4b379c02fe34598c3fbf90a715418d1a489d047c132cbc1475b98634729c0a2edc4057596831637a1e1d57c1d57022eae891797591001bf81af80521da334a5ad9400bb22203110dfa0838fad8213edc1020f7c8dde9db48f290c5c959e8c667ddd1c038e00f78f043821630439081bb9e9090b9756de35e46ec8919018c813f4fdfb7fbd81912004e5463d283c10f47df8791be6d6e5561e270430767368cede33c012ad67680027c3d9be84b3c0a245e7a246dc80521e235abe02ec75ab19053a5c0b58315a1135984e8c957ba83c10f0458788f3f54e05178a0f0f161ff32b26a5cc5564d44d8682d5bd035979a8e62c58de33f78911c7720324d5791bd19823dbc0d958b054a9637c7b1021c1ece7a192e2aab909119e0f0f17e0ab65e90a3a98446e70c113966234fe6b7e28bd9f8280a14f5122dd6582998bad13d667ecba890d2db6160,u 0x480f10b7f [0x35b1455b628af4c15e608a2b5b14528c4,0x3af2088320d806f6082fcd8cc80af3045c544,0xadd8be163ec35b06bf5c441cfb01618d10d681af220c0,0x2c82c82c82a38060422178a21ad54888dc0,0xcb6a8ed62b6b14a5c01759057982cba624a,0x192042c13416262ba354d951d75d0499b8a8,0x733717499bedd77d7712739ebe87b0d10,0xf5c2afdb2cffd50abf0e62f0cb3f8ebfa] [0x5e3e230433205e3e230433606d8a00406842118670e40a2108580262fcd0ba107e6009c2b756e84c1985d0e10b24176b84369002ec70869395a034214ce1685e3e60866c068195b2dd5bab84238b01a0076d03ffadd5bab84238b027b60026183dcd6eadd09cb4,0x98210cf80261043660098419c3843660098610d981b31404f618f384291a82198846086630842103210844243c9d6eadd77211c981c7b85d084225bab7570845e60342a152f98219b004d441f5c238b01a00728174210b004c3,0x83f10856101a10ac4608662] 0x182b8951e5d5ac680cf85c583be9de94fc707d2572bfc96ef608000ac12722cfdd5470e2f63581fc08f2ddbf90c7258dfbd8e20b52719d02ff1c1f1917b92c461822c176855ecdfb48136f1a0bdca2a23a6b585a40225fe212f3ad4c49a56bc9f2e594bebfc64a8ea204db4d9e1419bdbc9732e04a5d2430e7e7e1fc4f5caa045037f7d2dd3a6d6240ed95a2837c302eb8387f1b9fa4483db2b450ce9a5f868dd6c7a48c3956ba28568956ba2045c7d0dc381ed81d10ccd5045f52d8c30e57ee664a6b8c718246f683f80a1ace9f96219fde4679113387d551d9ce595d95153447fc0b487ab0c20c56af2051f5c56755059a40624c40337220ad4c51e1e202c669ee76ba41087ff265e7437772697eb862661814fa6d75e45af715ae76bed21fdc9979014250efd8c6e048080217f454db87d4e1fd22ddd10efd8c8617f454c8056baa416949d7adc4c5bc73d661c1113602007974a6d4,v 0x22120195e [775] [] [] [0x7ae0240510455860920b4304104924c4,0x9a12c93650479fae8331480701d0f72664,0x1755425aac64346fd897e12d52b7ac2bb7541e40,0xb281a0d6a68927860129d71c408403e745278c8,0x722cea9c200ee1816c08b0431b3a0ce953d19d365268,0xbed8dfa1ed3dae327d0c648e3f43d808819b8958,0xcbadc97434d4a877df4f7212f0d32b69b2ded60362873076ed2a0d6d808c,0x29376dea4e31a139c6a4cdb6070a9052815428cf8023d4ae1e435f4,0x1418fe3862a186e40182b9790060afdf401c527d8e1c20] [0x10b582a142d60444814306830ac30ada0592a18562542046104d4c8a158ea778432542e84e3f42312dd5c321d999a3a1189d08d8db9add9cb2,0x85b1] 0x55cbd51f74c9b056174e1dfcf80c68e27eb22618e28e0c7ab900004a06411e7abae871ef589901831098208062e00020089000860b12fc21ca41e9600c30aa200989d895dc16b9b63370f63b0000020e6aa5f803d1c1028016d8391b0178f1854c4cd3810f02ca7f0700eea86459aee08b0b076c0b80bceef014ec8005e5540048f9dda103ce0eb03af5c2970c41bf5709834c4dbf390962ccab21dd645e8c3a034871a48d56337c7b359465bc49a48e57ccbafa08774b17a30d7e80d8c6923950ee574089b6337cd020cbc65bc3f2c0ab62081cd84ba30d7c6c0649a48c734fe2c44230d31a4151b33d6b143861018c69053ec4ec8404469e53a94960,u 0x3c0d206fe [0x4104104958608209acec10412584,0x2e2087b0411d640c00cec1641e57d82ec24,0x6627b0d3c1d4018baa03817693a88b1c680cf221c0,0xeb8e004201f5ac843043591344e5821cc1c86a240,0x1ab845e3692a9125830d90439ca686e60824be1804a,0x180c058630705fbefa3ec1040118cb04a5a1b46d8,0xa049f050e708436c181efd94d0] [0x206b74257d6e84dce05b0aff4badd652121981d3a8010845c0e98c215b0ba005a7944215303f538207d0a275bab8423d950a275bab8423db02cb50df0c40082610b62f723a9950a2078cc0e9d837c302210826b7427f496e84fe92dd09fdc1084f00a91084134286f00a9108414,0x423884200842a8802588cd1e108443347842a10801049ee4b19a3219a3c2140821104681b004b20856130420100108452] 0x146cf029b009ec6c027a6ec8651b373a40a4065ce7a20cd11321b4267d6cc766b5c4740cb419c095019339c344cb3478077340c1373813c263e863aae1474488c72195803197775915d9351d13370a96f60066bf84077340c4208941c06c488c7219467a58bb077b7f1153679ab6341341a6a977a1e00d8023536809a3430bafe4db52c1f3c0008a30a07b19cd7fe0440035630af47cd39bb077b7f11d92724cf8a510550836fa2ac0ec0d98a8b36cdc474b65001ad16dd95956d4fda3c76d7075031665d06fc9ab0330358a8b36cdc615dc380be1ad4ef448496b3d6c7654791f4ab2c7651923728425fc56d12187155d94ef4f5ac401cbd490160,u 0x2808b837f [0x71906c03fb058c480b13dc64bdb057982dcc12984,0x9b11139fb481b46dd867fa8eb06bdf26fa829f21d40,0x6fb29f005d6e6724a059058700c08589216d5c8,0xcc2e8f3c07e8a2813dcc13794786c863d9e6888f0,0x4ec1f989216b32d8593e0c8e10] [0xb756ebb908b84d28213cc06842092dda1210ac6b76608434181129a0fb87802a5341f7101dc8421085a283b9100220842be060c4b756e84c19c51e77f4260cd6eadd09d1c013d202f34317d6eadd09d15,0x218c421384215442eff08552] 0x27f6ca2b6cdb7e2d8227c08f843861d132cf1c83fca2fc46a9deb4ccaa0b3c2851c35204185b30bb9d33723134872e5ad763f7983442fe74d89aa2bcfc5076102e27a91cf875353836c5608816be28200273f0f7a99aa5be88a278775f0adbc50774a62313453a03bb186391b3bd88df7c31c8f48d6b2537a240e3cd972a2d24f06a54f8f504ca600371800083de031e7045b145115cfb88c638e83d0233ad605d145dc0ab3829ddc4a61ba295149a,x 0x160740671 [0x82c71b7e82090ae003bef6ea240410413412004,0x1660b21ecde5117628b89c1024ef18fb41640,0x2c650b296aad0c4db346682b1a8b258cec1dfac8a3d48,0x153b5a0a12c54425c210c45ad8c] 0x13a81067c22110614309418c42210846111cd83f32180388442006e32006e4766f340bc211ba180555 0x12dbd75dfa922cab448f2b3709004b757c0d3dad9e32d7c1db502f45dd085f0169101615b16486389002f40019d28091e0190ab41dc3344800150b93204470f8e0d0c0eceb4481e331785337257901d0a30aba41c0f70405d1e2d129d05f05850574af374610a969b3b0870d0,x 0x140520bf2 [0x17541a390ec0030c2404d5a60824b530412584,0x7428804a71c7a02100fb940620c3582ae4310fc81cfb421c0,0xa5c8e1cc8f041be8ceb6773054e57794] 0xf41c20e4c442160e4ca144eb757088f6c165ac3b5c0211009108842e8f10b646828454e6013481088402 0x60854590905cda58720bdd627cd16305e7b31d09bc3085f839d0886275a40a178c418962a8fb745dcecb737cb0db90c36b91e120ab211ac4438cfb0840ad12d9017a4f443dcd171d5ac8244c37345f1f0e452b95b9334d0,x 0xa064187d [0x15036e4fbc97320a007f70c3b189010412412084,0x19e314103612c503650fd09231007bcc942180,0x390c608d95988c3f75ec018fbf52440c0602d89b6014692c,0xdc6cc] 0x10440154420eb005520844c0178a16c308442 0x2542af390f2450685e1d9efb473a46105392de85f20001ba327d81bc84bdf7fc56397000d2a8b42d0d0b06694632fac06c8523ae000ad5345a36d873cb8ab40df71112fb5e144b80,x 0xc0522871 [0xe61246f304634c7da051d69903004c09012490412004,0x2030082383d4741892ca4500ae506608530c604d948,0x3a06c75933376b6c0461937a98] 0x8bc1240d88bc21068221187dfb083441 0x21adb638d41b51c13f10fae53f4c1d41b810c2c9c0f880332c11ce05ebe19d9869cfb34a1de586164e07c0e658233bf82d6ebc326c36483145208c98,x 0xa0438061 [0x85f20829024f75a0cbf50485601bdb2890104520c4,0x41ad0c9495a2d4ce460d9923555e5164b101416305948,0x3b4c] 0x258a0f84483e29a268e0247160412 0x27073c315e3148bc85d647a19c14336c502b49f95955cd8dd91f52c092314464dc2fad3904241bd11798b693eb843d4c6c50,x 0xc0380eda [0x7dc8034e6f0430f1c1ff7ca0f1c876018182dcc125c4,0x52e478fa3225603186b841779477ec402538e0042] 0x2114610c616c56ecf391c960ae4b7679f3933 0x1bdec613f5a315c375bdd65317d6e14f1ebd947574115f252b9d72ec693c5075b470ee61ae72efa45075b572556cd60,x 0xc04d0271 [0x318a1cc1c8ed6088b40d78242b80ea240451492004,0x2a9a2b1b090d12560509582c68504d3ef220d548,0x642582bb56d9b0c] 0x2c350c286100a821c48612a094181 0x701ae92c344d0389dd88a388e5e6ea6451bdb2c715726ecaa7c0310548f036cfe364d2c3145cb3bd76967c58,x 0xc0402cff [0xe4b9d4911cc78663f7b662783aa312037b5f700d79b732a44,0x278e8b6538e083342a3bda5182012a171c721210203e] 0x215842b104211856eadd09fdc018d20d775bab7427f704215849cd6eadd09eb4 0x1f3c5a6da5a2ba1dc059d402312c7501073218be374b815dc47952879371b1215f4d675940,x 0x4043825e [0x8e4739ec10163ad03501fdb1990d5c60b7304524c4,0xf5597b4c90755856a59aaa3b704a758710217220d548,0x3b4c] 0x4200add9a92 0x153cbc41d53637967cd1eb99ae738c5f655d10ed99bba6324455b1c3bdcddebe74,x 0x40488459 [0x4902ad25cfb0f65ed007e42b80ea241410412412004,0xd35518eab0ead4151c7b07140e3642da139415ba0ec448,0x2463b590122c909b90c] 0x3c60fb00f2 0x42281675ccc2c0de37cdd1da31b49141a4c7129b45ad54653f200882f9cbe,x 0xa0321471 [0xfb0f6c94b0823dff65ed029e44481302404104d2084,0x1688b6c18883b307decad52888] 0x5c58110882ca449161034ca0c094861 0x148733d7b77999492c2adf3678e0d6195fdba795beb664f99b44ad2a96,x 0x602d607e [0x2d3047a8a901ad835e34fd186b40d406262b5324524c4,0x42c41a6c829ea40e2042] 0x25108591863e1 0x18e6d6ce1c55a94572e35dee6b6b4d777ba9b1b2,x 0x602411f1 [0x45dab20570bc4c3bd805727a932d85ce648f066a126049891520c4,0x6217b69b7cad6] 0x4a704c050fdc21 0x2b14b3ccbf2ebbe3dac52fdf2285bd9b68,x 0x20270a29 [0xa83036de59b2a22282f7e88b232045a06a03a890104520c4,0x16d9b0c7418] 0x231 0x6eef2becd56115b1fd7dd7f37468,z 0x200270 0xd8eb04622ce59b0c2a64cfa99dac0131076803f4a08 0x3abaad067c9b74e10,z 0x1d0070 0x1cf104626cdd9b0c786cd718d8d48da4b04188 0x1fb6af1dd975590,y 0x201221f1 0x32de260537a98421f910e043890121c4 0x7bf61 0x251edd4a8b7f66,z 0x81c71 0x25463dc8465c02244 0x59980,z 0x88371 0x185615c8419c02184 0x59980,z 0x92871 0x15461e08416002144 0x59980,z 0x61870 0x306d830188 0x2960]
def d30:List CD:=[v 0x1103aa13ff [2376,2441] [640,145,1681,193,1473] [] [0xbcb0412569820920b4b04124128c4,0x82282b4c10456c608a0acb04189c4,0x2086b0414d62aa0f20b730416f6c824,0x5411f9b6822d209b892085304121180,0xd0a606d864e6832a0b8f66da4da00c941900,0x68348030d6a85b0f6ae477bd5612e079fe6c1664c0,0x1d576824a05905907943c020210203e17908,0x115b182c2ded82bec96a60951802c83704a,0x7b1060aa0822cc12d60b2082b0a09e0f0,0x29f2b47d4041241046befa99cb6020aa0e068,0x1847dd209a09bec0209208208139414,0x1004f4021240c348fb04d0651a60c34ccb4ad8,0x122ea08214cd0751639fa1ec3d8828425292,0xa487313626c5267c8a003112a6baa62416050,0x55a2ed593208369aa8a1cd90412560ae8c,0x904c1c709382dc25e1b6b6b6b83fe583fe183fe0fe1850b4f1e2ad976f6202b2,0xa54e0021a6ea7feb157ea457ce97fb9093b6457d2c4256d03ac65e0973067854d6,0x6738f7ec8671c0e12312f087fd3b3f925fb84b76497e3f93c66eb8a2b2dc41db4,0x482146c3f3ecce7abd7e74dfa41d376c960f1a53a0a8e00263d92112,0x104904904294082082082082b46,0x22ccd9b311666ccdaa3117e80b11666c006089a90374a,0x15599b45604f9f4100622ccd8bb1d622fd049e20,0x10999b1763acc58233366ccfdfa90d5188b33666d4060,0x514d00701049806bc1cc81fa089b3368ae2ea0,0x34904514514d34114d3590425c,0x14104d34d14104d34d14124d9c,0x14504d04d0410410410412585c,0xc18604124114d44115134905f1c,0x3d74fd0208208196f7df4018fbf479fa038a,0x14253e718845f874a3864a7c] [0x3fab600604121f81d004a3180fc3b0f5bab7570848760667802543dd5e34f58a43e0e400c1469eb1821c3b08c243f02a0098633bf8a43e20620060a61487d81c11842360666c610a42e1c1f842360666c10d9801810d3d6293b87071a1a6e0653881880182a1a6e119f80181a073e34f580db1a071634f441079e91004e3,0x39e2e29138852e5b88562e194210b982024013f1063bd4200c46e7858a44ee95a1456e8562e1085995a1a009f623135119a2070ee9ec00ad22109a20703bef400a8f434018890393a1a00c4681c5d0d00623072fc0498012d10633d4200c4600ba1c2164d41917842b6034102f00626003017e25cd08423183900302302900303,0xcd25a165e3045af980a19ed8026b94d6692c758f1489ca8a8d2921b57003401388111f01a009c634f787616a0850c0189421ab03322810ac01888698b0da9c4009a824329d6ed495043260652e55598b312194ea3541c118428600c52cd25a8d50704610a181aae00c4ec807a0c0e0d83816c6005ea34f7870762086ac0189469eb51a1c1c634f780d0857e60803128a45e1c1fcc100624,0x880b8557e18441084a066420667803110ceff084383b06f1043467b72c4ef6f88682f147bc0855d0b2f0333c0188c42780dc2f1f06dac010180ccf02a00987021f826112165e19e98199e04401355060bd4200c4600bb5c2160c2ed7a042ce00c4810d5811004d342cbc31b70ba10828024215f00623,0x4687da400b8cd0842bfda400b90aa8090857fb48017285e0e06682109414841e600986b7724ad90845c015943c9bde36a40a842b600b2c6642167ed2005c80a701087810ca07936074d88015d02e8302210af810ca0cefe6004b3412107b80171a0c761337810d9842d8a0c677f4266f021b4,0x2f2f086a2418cd6eae108d044329c30a820f3032954315c41829842020903975c2117c90f42f27104356079ea271d1c16c802a3b9e21226ae7955882289d1165108b28840f4e4d718a601a034d21094642a2f34d29a534cb7729bcb4422d15d44d1783512d8c2f17342185bedfd059dc0d07052005e73e0b64212848ef388489ab9e5562303512a2131d108e55717a2328d200a230b88c45e932529a534cb7729bcb4422d15d44d1783512d8c2f17002f33f109e76f0bbfc1cdb004a64790e42884a347fcbbd7268bc836f12d8c00bec0e8852109424779c4244d5cf2ab108e8c71084611a4014461730494d29a534c9e7108b45751345e41b78d55e178a53e1c0c2074429084a123bce21226ae79558842308c22704c6d3279c422d15d44d1783120bec6aaf0bc520f4329d6ebb929210d78194b04367da400b8c2e8b08442,0xc07e1b578436e00948830382d085131043590423885e5e10a241797829085130bcbc06d882f2f05210a3802ba0a4261c1185e5e10d88831fadd5c211a0817978421e00ae610882179781d08503c0422105e5e10ac4024211302193,0x1c1e210ac210ad802690a42610ad80269b410e10ad81d56009a8a085020aa9c219096e852ee6083cc08a542abf086a20856f7a802698025884368802708150857208be140e61,0xd0388d046045243411879360452610a2214bf841e1042188d05e03420f4dedcb1a08c3c9b086a4] 0x172dcce96eb47c36005d4c10ddefa1031eae9eb8093fc5e2fb5f0bc3118e042a903faf2ae972b49824aac65e88e79d3dd547a1e2beac1c01bfdf83ea063cf52370125f9fc576fe2f86231e154828fb9abe5eac65c9d2ddd47a3e2beac1c01bbe183ea063d7b3d5823701244fe6f1fdbb8de188c7855209b58c956ebc2ce8163f056d3a7bbc0aec943c760e00dff09eb8092fd7e3f8da063d37e188c78552097d1d6d0efd6d973ec26dab428eaf67b5b55e21158c844cff0cdebf5ba3e8544bf832f62ff02e702600a9fa67a22521d56e5472f4670e7e9d189cc710b6f30ab09d2598da2586ea3e361b0cca4520c9a02468b20a89ee7c4f0c463810aa42ceb190899fe36b3af27cfb8b31c5b10d11ddcb685173c4c70f41707470edddbb1b2e7d84db56851d7edb6fa3ab81001c545c1c422e4d50c28e42267f97e33b01988f5db4c1450c41c0173c04c74014426410e7cdbcc2a0aa9ca5e8db06ef15c6f639948a4193406812ff2bbdf2318f0ab410b5b369ba3a7497e46389237c998f0b4bc973c8574bd0e651c439f51b419920fa66c835782342d208d3dfb9500c71fd81ac4f7c2ed4af93f0e0aea7a017a17832e3964204322b1906a8045a3c1722018e2e90e4bae2ae97a17832a106ac45631e44031c5da56d76ea0720396aea3a79805c85e0c98c32ab1a9641aa4523c3f2e018e3785af65831b43767459014f8663d808acbc563c6512e0bd20469667e288384297e37b37f4de38a7daac9b1cdf7f61ccc8c23b9674d9f701a23593f57fc7daec9187b891055183193e1b37b9a818ea1dfbb60fbc96efb66a946cf92c46dc38236382022e30942698c5071d7357d3f474f32e5baaf24ab72f4419a60cdb2cc37c3e9e0e5c05404031eba982468b2011f1d8f2e018e442a90db98207cb72d6331f0bd0383d781b445b1d8c8f45cf60063d6d0fd8d3e4d0018fe8e3336eec5be180012f499204cff7e57b8ecc058d173c41751e9b9e4326b6d06987f27cb743051463d03f93afacc7631ca91540181b58015cc80bab9f73d9d2e781ec5f0fcc79f40063da5e80849da17bb76756d2fc3f13e7d0018ee9a61efd773cd50fe828a31c2157c98001bffdd21c0cd1fc4fe710010031e758063a1a95e418d61d986189a24a8d3ee53b055f990c8d9f67deb9eb69c63287ec31f41b219f003f57a6018e45a8e9891a5bba91e51f2460267433066a00febf4cc7c7d8f097b5eea9fd1d1ecb9f6d5020029fd6e8c4e63a2884db701510df015c7923c2b2dc6ba178845c958caf837dda70902e7a3e3361cb61973fc971007baf060cbeffa67895cf6e70574bd0e7fa8da91ee732c4444031e19a007f7faa63a9e2b86efd55909d1f23e68caf0cc0f1eb98ee8ca6c8e6d1b1e60f9f5c031c9e12f25cb90087143d02c7b263a3e6c000df48703347f42488008018f3acc931f6fd900c7f5ccc908100c7bdb31c5364911942ffc260b8609346c79d664beffb6018f4a434cdbdda2df81dda179228b0198875992fc5f2d0ca474cdbdf31f2b86e56340af0f4d548ceb80bd43f09ae4a8ca1ad06c90e430031ff7c031c771944b39c6dfaf431e6aff57c2018e21aa38ccd8bbc3002fd12bc522cbb1e4c78245801d1d9066ff183c1cebcaf035dce7949121e0355cfa26f3afd1180184dc760d374c19661bede466b87d2760c98b203ff77cbee78bc15842c98c785533ebb9d783ca5062375361ccec1a6c892ccdbf35c3e599a3fcba6e0ac2164d5639aae95a5c739edf9ae1f49cd1fe7e0729c1708e59e4683a42e369fe0b86a7a460daec5f03a6653600654c7d385dae4572e18f6e0b4e9c8d0772f8cb0032afaf3f95e8f551f4b118c218474f32fc6f14dfb8da22832fd68a0c93afa91242f42419312cc7da638ce48cd1feda000c704852fe41bc5335473419b8d98347de018f0ac6422648cd19fe6c87a0108507ef00c7a292df81dc43d42f7b7832229fdb3648427ee018f45a43aba83ff7e9c9188677f8d0018e24b3d292232892f2cc93ad231b602a063ff29df018f8066851e97e4d90a37b37fcc8e2fc9b21541bd9b14dfa9aa2a3a7997e378a620da22832a51419275f52178ca84800c7c1fd4c719d6321153e43d502de73cbf41ddcb685173c43d05c480c7a0d85dcb58d891a83247f196c0063ec00c70a41574c728d0c506d01b314956214bf1bd9b305108f83df66495090007421f6bdde262d4384058d4d25dcf5b495574c2f42f065fb9affdd47357c7def95f56299b2cc37fcbe2c1ed5a6246d0abfd7863cf1e4093eec64f0c2063b52bac32edc436e7adad7ae8b3cf0f470b3be8779dbbb3d22e2b3de9621f35eaeeadf07e98618d95dbec55b4bc4adc95e1cf13baebb9c818fdff33bfeb8a969a92e39883f0ed384cd2b68d25e85e0cff7b4dfb61cb611fc0d7b359b0e8951d21354c1908c3d7df737bedf50202a0201001830ddf4f8b07a6246d0aa879c31e7dcb4a8f267bfb8e0ec0c64f0c20f78ff42d8e320031fc3002bf55952d7609a1db7ef44a3cfa9821be1ebc1f314cdd0aa03e963c5931e08d1e7fafbfdff0c204b942c4f0c012fcfdf50c1d26cd9f57754cc30c72fb5685a236e4af0e789ba70a8e8d99e2f72505ac7310769cef099a56d1a648456348c197e5872d45c0d73373d6f0a7e8bc14749cd530467230f5f7da313bf698e884df5a0080a80a2983554b30ddf6f8b07a6246c2ab1e78f2e41efc64f0c20cb92bc308446ca3b6d5a3ff5ba7346c78ca25d9841193c30852215e34ceaa8e7ada1fa8e42466bbeac54cc9b25986f85f7f8b07b569891b42af0c79e3cc1e7bf193c30816e62836888767b98615f70339f1c1d933ae8378d77949121e033ed9fa9a0b798615ddf6cd56c1f6578db86f7b1c0463ac5a354c1243aadc85f84fdf7f028d5f3be309889a508a6159cd96b514b90fc17b069bc14721230383070bd5cd70f7d4080a8880060cd92cc37beff169383d31236855e18f3f05b8c79b3dfdbd7f8c9e0021077ecf9f78bda753832fc2489a6298565b46f0fd29444830ecf730c2bdfee9b540800e2a2e8af071d7960fb25439dcf5ba313bf698e884e6de55500bff583caf855f3dcb30479410f5e02a8099150f861051de79fb755db3070f5e0b147199b138600e514b51efdf67d438029c5b0280080008575487d36299be012858907529e180244f7e99b50d50de85524fdfe1840521c541f4b118c47830c3b216d33c3f4a5800d3024f554349ddb02a20063cb121c6acc9e18407f30c3b016d33c3f48d800d301c23cf4847974c8a618f5d4c141043d776e62064cc9e1840974ecbd476c848e0a66c2504c1c3d721d59a9ed26cd9f57754cc3da485b64cbf09ba70e30a8d0a16696288e8070c1b91a500c789ce667845c558e48473dcf5bc29fa2d872f051d82dc67b0f5f7da313bf698e884e86a698355508d92cc37c3c54c5193fcd323615c3d63cf1e7480a809938c9a3861066c8dee7cf1e6ce18401c1cb58cc3070f5da963c54c48d1e7c21847c7b16f8610e4a3e184203be0fd30c05b44a057655d2f439206d334dd0c525a0d180a219551fcf1e5cb92fe07b16f861027d4f4e4a511f37457fe184095f54d4dd8a92ee32e12fe18409b84bc9de1843ae12f22f8610e28cc111cb58f86100495e18422835d127e11931fe863c6d10f8600501ce1899564378578c515780b1474c48de18024091d364c7f1958f33862b58f194472d63e18814f43f755a935cc51d313648d02083ab675438c9e1822e43da16f8610e27dc5e07b858c45e78e07ba71cf5b4b90fcd7366c50e3278610e5d56a501785b610a0f68431f59158e1772f86244af0f685b1ec48c5141785b27dcb8c5e58d494cf827c7d3183564378551e5c0751fe18026c74e22863c6512f8621eddb6ad0b11f46310b7e18812dc3da10f862049d2ec450f8610e0de85522d43e184051b443e1802aa7aec7a7687cf711be662a225542c20daa77688aa6b48b]
def d31:List CD:=[v 0x1083e423ff [2441,2422,2103,2375] [1680,353,114,627,144] [] [0xbcb0412569820920b4b04124128c4,0x8a082b4c12416a608a082b4c189c4,0xd414e60820ac10550416660ba0e8624e244,0x2d2690490431920dbc9070003c832a64,0x2514098256e3d9b6920d23ec102681a722540,0x29b48fb9f600cde741da4832b0f3cd46500,0x8084080f81f410b646ced87b172001c4f1c982100,0x951802cbaeba9ed04940b20f3e99e2042,0x222804905a9824adb04905e582bec149f0,0x43d4cd6b1d076082a820aae8436760ac28,0x68a4ceb3866826aa8881304110608e1846c,0x1ea26adb2a7e8d33bd80961cc1a7d34183d4,0x6b1790751430411241046dcb08ab7ad8,0xe41a4d1439d28832ab1cf90791c90,0x1a16cd13628030062cb0f22800c7f61aa66590,0x31561f0aa7f06acc268e4b234d64018836410490564b54c,0xacc71097e14a9c14cb8008680cef47cea47c64afbef6bb64adb5b356f9553f92b0f16f1aa6c2,0x415b8ed0e201f8a001e3d22fc98f848c483d87bef97fd5b3fde486ec9add7b2b4,0x2146077d943f559223e8197b2f7cb911f29fb65671e,0x10410a502082082082082082546,0x22c45a2312666c0990300181e6a428228208294a,0x13374622c09f22ec506d50626c0990326644c65e0,0x8b53624c9188b1164cc71ab333688c1180330622d08e0,0x40628c45a5bb48999311640c5d8a1ee912648dd520,0x28aa8208208a09200e2b2a2f5e2675a0,0x1411450412415450493492459c,0x24114114104554104d14534f1c,0x1411450451415450410451585c,0xc41161814451450490493452601c,0x40cb07bf435803d7d017ef22ea28062a386,0x6e81f52ec750e274ea1f326c714661c4e5d03e2607e2117e1d29f0984fd0208596,0x395a3b8713c] [0x1a09d6eadd652121981e732dd5baca4243303bbc016182437d00251848660663802c1a1a9e12198198e00b08869d8198e00b06a7dc1c008cc365704c0e96881002751a3cc482f0d95c30d2d005861205c365704c0f488013a80d038bc0098c2343ce200b068319e7100583ce217400c0f3885d1001720210f200583,0x1038b5bab8422fb01a350ba3c216c869bf0bc9dc10c8810de234df85e4ee083c47bd7d6eadd5c211a18102b0468600604f7b1add5bab84234302056005811a0c180f8c0160a4009c501ed802c10a42e0981802698210e00b0501ddd3100583,0x1a9b31a6ff5085e4e004410b0ebca5a3d5e79bd9d13e23eaef44734dab944d4d3471a0ac484308bcd6dc843664a7ec9006d063df7076205d1eaf3cdef52c6d8da4952ab9409440944a9a4de34158bd2f41205dde8450bc9c00da1e8397e083239e8f5782d3cc2c421635146511a56987289c2324d1384603a21025118369bc69178856add1145136d114511794e210842108421085e11460e4d0f8f6563415ba4240d801ba1786fe0af2963415e510846c068d469bf0bc9dc10a0834df85e4f20862c0ecd51dcfc6263b03cd2ffa23084210a65684234a7c5194451445f67e89a171eb2c69bf908eb0ff8d37e1793a8219b03b7575ccc3c9b0847c012d1a9b31a6fc1085d870a48213a00175f84339aa50bc9dc10a181c6abdebebca58d056253d85d0844c068dd039f5ba130f80901a35,0x138f2e25eadc486a388603710adaf047a696d5baff61e80d1e2100427ee3cb897ab7121a8e2180dc42b6bc11e9a5b56ebfd87a0347884016004427ef8bba1a8fec46037129fc3b0307ae71a0ac215882e8f083bc0184e07f75bab757084676009ac341585e4e10d463415882108d6eadd5c212198198a98419038436e00aca610640e108b802b2a1a96b756eae1090c51a0ad4c842b1802588436e0096490421b3004b3,0x2081b6ad3c419df8510847601a0142d9752a10ad94d039370bc8c2433005635bab757084866009eb01f7a1a6f5740d6116eadd5c2121981a2aadd5bab842433004d51a0911a0ac2f2496eae108bec4004aa2810dd6eae108bec06dd8682b0bc9c218cc682b0bc9c211cdf1774351fd88c06e253f8760616b780d084fc0f4b0022b75cacc00466bd5ba1a8e34df8c06e2b6bc11e8a291aff60cc1c408580ff,0x2f230ca10846179187d083c30bc8c08842b9add0a9dc410848179180d1042b205e4740321084821ba3742d6f0863c0d3f006175bb51421af004d48081dcf171486d6ed45086b60bc8c410d4703ff82916005e62032840842c0681c6c08248423e1340ead6820005204216005ce830985e0e2032840842801a0a420f702054,0x14225ac02fa05ae7985882681551c36e608aa21a23255128c22baad0ac2347bc463cb88a288bca7118561384e113fce055c032848170bf6c068429e03417df700de8ac00253df002000a108e814c3b820f302054751c10a280a498800bcc02819084235bab84b08432a0051042b98821ac840242160c4034215cefedd99042760340e2d82f2042f23086a20bc8c21b09efef08cf2,0x3fd20842d8843588110856200a10b24210988b70bc7c09e9a045f40e7c60370dabd6e84c3e0e5d8027c00500a108e62942f071041e603407fd845d5c8ff13039e209a094470db982e915349168946115d5685611a3de231e5c451445e5389c2709c227f9c620b02ae04848170eacc3ec922858fe6c1040444107580dc9a08a782d013be400b10be449a3f63f0f8902e1d59f81687002783cc2ca8985a12842108d1ef118f2e228a22f29c9a1c4fc2eff20894408410758013d20586177f911441820eb0027913956e70e18c4161796a27249ce1bb1882c2f2f00226,0x210c4521b084320ac31086c1] 0x224550fd9fa0dfc6e27ff039812ee5af56f832c69732f6b56032675b01a88cfd06f82e318d224fb93ffb88126efe7f32d580c99d635b01ae0cfd06f9960bf252b6e3c8126e9d61fb3f41be339adcc094b3f07686a93b826fd0f336a0d9b233e32eb290fc02afbfe980687db0ce31f5b2d6a720daca839b3e84dffdaf44ef15c4a1f29d210cad9e7beead97a5d7f3ccb718b4b66b4af1ce2f44d76fa8b02ffb96d142b590b86a2d0e819681592c8c0b899a1bd14ce6eba3059cd71d45b0ec4796dbdb1b5301e95ee853cd528461094cc8d0bb6d321090a9955e8411934ca3207dfb8b88ea7d0e4262c6509bddf4286082264f001610c419fe3f7513a003642b5087db14bf6afa7e8dffa779dab771a7c14331a0200237c4e876861d88ec99a4b84a65d3638e3d56866b79e150b12b1a32019f78878d6e341043576974218da137811580411113ba001420cab1020b0a869393a398620cbf57c2475d68f93cd706914352c8ade83b070e00da0450fa42162c3f851e00d74690f31aa5e0f0abf2cceb7946358458350631a8c1ce6b00237c4e8768a1da8cdd090bc050346e6436369b35c5690e10156cce497659bd80db69e70610818c18a6d57166689e0e1c4931aa5e130acab15e316a4e0b09ca715e77f03b8d3cf10215bf57828cd6808008df13a1fa5876a899bde7b4f53cf6edb4d8a6e6b764024ccd5c4854d3b45c838100bd849493fa7e5dab99196d3fc1911e6b8b020655750c4c7d6898ca158168813e3ccda8366c9be768ce1ad97ad13d575eb2833ec453a695754375dab933ac19f67543f7084d684af265f68e60fe0002aa9ec65c4ac1f4d913fd4f2842fe11134de9b2abaa5e6e94613ded5c164cf9067841f8a3673b0199366ffb7c23a43f8c059f2242d7ce2b8810f0002aa9e99712a805ef75914dc1b41cd9faaba9be0a88f15d0b56032676f016a1fcd1b0cc831a44b415c3dd1eaac281087c612db8f20d9b26f9dacfd087bf519cd14fecfb7c16540c1523fb85761fd555d48736857509e4723015d5574850bfefe5d0d374731142bb10bdd9d64389ecb80b0c81a810d1e0dffcd6540fd4240cf4059f58489e00f7e3f6c5504736dd3906d07364df117fabdd65c058483a787e62bd2e657f00cb110d1a449fc3e6d6d3fdcfb6e04ff5377eebc53ac55085ca2040064c05851d90321c2f411725607c6c883a090ad7996f689435b5ebd8430d095e4c883988a06a160eff84d963c410e1065c0587fb8b3eb42baa196428d6198850aaf1a7e75c1c1653f4c4cc87146933e05ed5d407d0be6ab9aae7d753fc4742438a23988aa1470eef95b703e910e1065d65b16149e8165026fd49a627a542d8401f07e3fad6957579341be2882ba8730a2f2e96b4e4ff420a56dc79024dd195e89d6600a449acf97244f0c00a24041fa4b77c17b4a7ebe1df8600533e6e59f58451df860056ecb311b967d6126c7d4679dbb7df02c87b7ef58783f447eaf793f65bf2085d439117f9863f6d352d42d0652b36580cea087e6efdc181001931cfecb4e688904fb4e3fb5fb44b95a3c6d74bade7f71d570ebb7070b9a9b12637f97a379cb6d9a5e9a627028766069d8100cd1ed8d36bd2f159b61f77d9538c39c8e6f3c4d7603b7eff7cf5a17c3163eca07796a4085a0ca5641b2c067411fd504384197016154d4d3fdf76463344fc2f3b027abed43037cb553f2ad362ea1c88bfdc317cef6d452742d067046d80cc87ee8372cfaca81568781fd497345e76049503eb161402f6555335169212d10216139275bd6441b82064d0736615c4cd1195979d714f633625500bc933de76040f1298f5ed3124c4416d3fcd30e5de88e04986e8ca004ea407df40ceba80fef441032602c247aaa6686f0b63f81f8d915b4013499687efbdabdab639f36e3c8366c9be7686a97b72cf8ce689020695b72cfac22a825599ea703ed25a8786ac969fa0cb0eedcb3eb0987c3000239d01cb42ba84e03e90d41940c574473117fb90fa4fd1f41933f7c1ec0cb18910f380ddab7a836f8a8e839b250826c1aa0af8fad0f3b500b67b57bb5f151d0706e300d1e77431d087d7cead2a29fa4e833c7f183d81963e1f239be21e7c1af1648feae7de3adbbe7fe0e88ce3fc868542f943913fd477c7c02d443b394cdfef7bdbe070854ec8a3efdff5f67c58106ce030c2194e22c0134d11c16430eea0bcab61ed72b292e04bf1cddefa1995c5173442ffea7adab49d074863030fbfa1d8f0d4288100193a837d834cc4c00dc6f3b1ea18adf36249d201b53d2f41cd92d5c182064d6518d810f5e987622014b866f00c819ce3eecb32aaf0822e805e4405c6cd716c1b3e6c8a9e824e0dbdd7060819341cd960b7f040e969e6042b7828cd60200237c4e87e2ebea048c0022cd608a57ecf6a06fa000801aac1061ec6005ba85774fce6e0b56032602c273b0e1a16afdfedb82d5b266cf68d8b2ec9ab56c9b7573ef1d6b177cff47075119c7f90d0bd9e036ad26f7f990363030db7d0e2a7916882064c8b4d5c166d807b5c53fcc9431336ad936a0e544ccbd71a44284d509e02c40cebd1f2b82d5b26b2ca569a223122481b289ab62cbb1b2209b6c98b62cbb152bac6416ecb90fc31611a453ae245a0fbdab64d65fb67b57b01fab76a2d01670c11e94eb891687ded5b26b2fdaf6af607f56ed45a024e18239e182ce8f3860804776e59f7bd6180f055e108054776e59f7bd61a4e1801782f44808fb38608b5ed6ed0bf6f7e52778608e7b670b1e18238776e59f7be19f80b922603da1578608e30c4e18228ab33c41f78608e25685523f8608057122edd968e33860805d92ef8608a765a340fe8491a78600104a9356307be182010e684f237860804d5304a9e07b13f860089354c12a781ec4fe180225bd40bf2778608eaaa9fbb6e08291db68e30b018aaa5d8f48a85e62a80a71c9f,x 0x602e1c5e [0xa4d04c6003e3d702c1c8ef6ccbf0d7c2d087001606dac12604,0x3e8cde61cd75404597b8194] 0x34719d61a9e1 0x13bdb6bf33da5cec856ff2aa656fb379d2ae940,u 0x221070 [0xec21c29cc559b0c43736c919dcc4a7ec5585b24108,0x4bcc] [] 0x7b79bc7662b2d5b3f1e50,y 0x401c09f6 0x837d18c0f1c10706ae434f1d878fca0f0002dcc125c4 0x3fd28804d1 0x19b8c3175d7731cbd4ebabe0,z 0x100470 0x21c29cd24677b491824108 0x7e8ed810,z 0xe6071 0x113312a62155215b0208461002204 0x129bfd9e0,z 0xc08f5 0x11b307041ea611c841e0021c4 0x252e7c0,z 0xc52f2 0x12aa92b586a328037b2644 0x14bf1c0,z 0x80cf1 0x223529c8421c02204 0x59980,z 0x89471 0x264531c8465c02244 0x59980,z 0x68371 0x751441d0021c4 0x2960]
def d32:List CD:=[v 0x80310237e [2103,2422,1792,2432] [353,1539] [] [0x141049566082482d2c10490492404,0x200c07401af3041982c820cc14e60ba09016204,0x14906504d0c6483483a8240c920100,0x1365149b47da349a81a704514922400,0x508b7bd9bbeed61e3e3c9a16f904018f344200,0x3e36d049f6167d0768a4b07d045c8,0x2c8834450682d2c10492530c0253ae38f4042,0x391960ae69a2082856c3588b0c75cc1446c176ec868,0x2f702c10b98449984b3445a208c90073ac14454,0xe8a34c1d55a4d0419f289bec3b4a58,0x175323ed228e9469246dcfd0f61ec7d8048202692,0x5ccd01602c8d92682482e8a0ac1c61a32a6,0x14cd13672000b27450401bacc30c3e82eb60c,0x1d2071017f0d20f04aab68d1dee97ca54782c551e9511fdec32ddc0b22d6c558309a39764d8b2,0x17b2b8b5871596fd2c41db8299716600e1a5ef43cee4b8a39d207901777dcd735b222da,0xd903ca7ed951f20adc349702331e602e4c7122e7dce3cbdf4c87e97c90dd935b4,0x450a502082082082482082146922f1e,0x10ec69963236aae3b569ca300781570a90a482d4a,0x7a5adc59a56cb5bab0b72aa98c2da530b6b8cc8e0,0x1509652d52d696ed236abc34666b4b1a694dab20,0x49269249a0b269208a00e020957a75a0,0x4904925504155d04504d54b1c,0x24125505904d249545041258dc,0x89f23efd0d60816285e450618104d364dc,0x3740fa740faa5d03e21c9f01032d878a] [0x71d9e4a8549e10b181a26009adc0842c00b0e03e74351c522751210b380d038dc2e8016485d1e10b641553b820f301a071aa871b8553f2083ac0e2d5c767f6b76421130344c013582a87f041a6075b802a284866072780261c07ce86a38a44eb757084863407ceb757084866068aa25b5802b10d03f2004c31a07c1acb9002620d03e0d6581dd1835002e2,0x10433add5c211a180d021961a08c4b630858c08610682312d8c2163d8200aea612f44e8161dad5bab8422d33920333426bfdd4651f75fa7da210842118529a20e231a44d4b83cae000a31ef35189c8cf138419444de96a0bcc2142bca1abf467deba6d47ac548ae982884aa4d108c610a27781eb9468f7ca4015ca2685d3e8f0163283f0510aaceea6023a987aa68b422bab296d2eab8448851120c09504e242e3d00aa7492bb1694588a12401513fc467da1c4d0ffde16da2bca5744f554627a25fa264a211842307510946b094075c2108468f38a3288a288becf1094654a212842b1bab133cea3477fb1941c5cb714fce023a9ea179a158b8ad4a32e7c297590a903bee400a8a1e1b0c21bfc21b2021b5c230f7896b61740e4d10e5f5bb0042343038d54397c2aa77041e6071aab86fc830060240e4d45ee7085b2,0x142110a19774397c2aa77041e2db11042b18557e2084235baca42433005740ed2c048421fcd4086540e083bfc0ef9004a68117dcf0b6a01d602747a85db8a65f456109e152b1558add98041de081423e3410225b1821083d31a08c2160868230858c0864c68230a9dc410848b757084866009a83411896c610b06044210f02193,0x1c6140b2100251084f1085a1085711204c0694848130856c0694c01304015042117005420845c0cd70054371e1da8271395de6e49652ab7b8e5103f9c06dee8108b802a1896be0a420f4c215b00542] 0x2e7828cdb2dc1edfd524f94ce132c02eebfe89a95754b63561a34fb5f023f0d7b1c8b0ebea0b5e7300423a859ef75c6d9a362d6e4890803fbdd45132f502ae9f29b564737c0ede867697918d9f640005047066815d91446f6c1e5f4b427696e3b2034516cd9f60932411729f5d95e52d125c83fc144eab284a78d9c766805ed80d1762c29accafeaf9a74890175b563566820f0d8b42c40c4ae393a1f47b8081b35dd14783f53adcada847d29b5bcef07b8a19ea638e9fa4000506d99e057b811446f9fa7d3d09ea5f20642071d864d91a93f32b3877dfd75512885f8ec591ddd6b4a60c3c82f4df40ffa1bdc917876329d9544e3e6b74bb07904355f13234a7d6b3fc3ae6a19163b7e800504716790017f4795447f9baad4d19ee5f6064217198b4dd1b026f5c9ac327ca948fc353e276fd77035152bea39eca68fb1729a2057f20a478ec732ee7f0cdf221734bb00dab48774ec09b7ceb7cbd21817f72848f609201cb688060d82d1e459066e82c8b2e82642f51d0e41fcce1af48605f2a1a3c9205ca69d8227af20e488ee05dfcc69b2ffc5b0dd9a0c4caeae02160067c5e1f732be82bb76d4f07000419a44c12a17796d9cab20cccf1a8bdfb5c268c0d6e55bc5eb129c913e94fa5e2c05dc857721c0583a6d320030cabfbbb335a831a851a0d99d8391759b264d22c194ee5affc9909608041feaa1739ba659d64bfc26e7a083daa4987c6ae88458b35348f7db3fc326da0eb2550762d2611424c2d0955568581d643ae1f6ac5e1f71b159e4f8e42fe396e7d328fc4777b965d4bcbeff264326317c1d2f27a496506b5914cf37bdebfa5a198e4b060247073dae66946edb63c7a9b85e043a03ac031c2203886d5621412ff4d004a867e22794b4e3af4bec2285c36eff87810a1c769d4661b4140c906e210489401bb66c883fee051311800f28a93a85bcde5804c601ff51be5ef02350f5df7098835151a7c9571583449f10ae578ec0786f5ac4438aa2e137ddda8c336a9827e807189f1e2e5984ff7b16b50f912d975485cc17a70b0ca0de135e287114b6fd31e12b522192feafc54e50fb97996e1b110f0281001f18001f25ad013306b3dca7006c0a7bcfd600befa2243808cd87af117c40bf41204e1befa028d3984441af3ca4f9a02093067f680a036361f1bbce46274ff2db276ff3a8244a408ac2e630b6b72c6ede1de1d1b8f818dcc0d1d2fc648364d64dc28ef5afe8d0435d5473dc9d1700f92388ff32ec02a2248377aa41a211786a48e46e055d4cf17e2d951d04301898e2c1abdd685840b4b4f60247c843016083bedd5087d631bfd207fc4869f63cc408fd36ec5ae41efb98675eec800040ef3b8de3376cf37b2d6d5b42af9eaafc62f665b6724002d550d67c36a48dae0665737750bcd6ed8b5351dbf4421a1239fe1d0ee5694f43bbfe7b99e47739aea98bfe9b664742c6affaba8f98a23010769bf419602be000d7200f83d570643ab638817d635f61153c78b1d6e7f1ec0bdbb7b6b1edf93ccade06aec39604c2aee2adaadf53c5ede4777cff1bb9ed3aae5740430e7f82c20c2006fb86ba9da52062a01d66cd8ec1a7061e9c22698e95189a6e38323e6f870743c2a7f7d9dead0ed0ebd1d8f1b2ab698e0202cd124d82ecda7275c06a996a3c0ae0b74793e257f55e927210fbdd82531dd500f9f8fddf5f6d684f171b1d3e73d12d030b3f6cf5584d4fcddbd5f2b52ce2a525b1c54a4b18c1fc7a2246194191547959da61cf2fa10f33d5609fd5f7c44799afc2b02f0caa4b20340d0609fdf15385628a1e8b29b1051987a2ca7006c0ac68211405fa12c6286d519145b01921a6a906a128309a98d9ceb1450229439aadc2ab0461dd1f588908fc7cbad8ca09518b0001cab499ccaa20d50881721c284688c11d9fa4688ec08b29895880054b6a791777c1018b7b61632355ab45a062caf9,u 0x26077297f [0x20c189115b66b5b5e60bf3057982dcc129c4,0x10210f35f608b91143fe7bdf03621fa254e819a841f220c0,0x16610f97054846c1f72c628c5fb732a30412502cb9e2242,0x3835f973a3c106fa30d1d13a4bda6c804b7ad8] [0x4350bc9d810c690d42f276011084e51a08c0134821b3036dc0130c338710a107580262042208021af004c31066fe10af80262407c610884009c2b756e84f39add5ba13cf81dda002c0c07c600b0434cd802c101acf2004e3,0xd040802b885e4e10d585d03a74] 0xa2021c2ef043500000bed751d8954badd073b247bc80476118e664b2dae7288e27ab5d25d2f44a96d8e4f87724c6f73065718fee0d96e92d0af21d2f482e468028abae0f4491619cb5ea5d2a517903ea6b3065722e2910c0c196f104638ea1136040d6720f604400030bf3bb1218e756c5e8da3ae974c62004aa9400036d866801128496d4a0001ed2a12a005d3f4,w 0xa0c0625e [2103] [] [] [0x4e648c80402bdc01901245141576682d4cd2504,0x26c31b4b569f42082b786cadfa685b36d40200,0x6da6b7b20909791a76c14c180a2c28453081c408403e,0xfb9a6d09101ace85b9066da2980c2f67ed819fbf4d4c90,0xcf6923cdc7afb19181c6a434a1455410a317bee71ee0c44434,0x1c3140c36ba81bf750160cd907602e67bcf6f63d9c60] 0x108a24845285a102e10561 0x16a15775072facce46e2010a6980408d322820304f42d0026d9571488d850241cc080880259000028a18020302b420ea470c55407104c4cd474b600e208332b6244a3517a6abd147200d2b200d0848eb48890,x 0x1007824f6 [0x799030043890104504958608a6b3b04125c4,0x2100f81027286b17692c9c8ef6cc4f07561688bf21e00,0x4105f7ed2b491888d47bec0f62ed41b2286b60824be1038,0x837414e692337187b22638e558fb1010] 0x42c8c3d0e7240644211085b1290b89fc217981c5063725a98dbec39260cf6002b0add13fb840d3 0x8c7a0bc00ec455245020031561b2c47b151999d0b6c001f950341c405f825c63aee77b846593a1dd912c3100c50d700b7141f81834c704b8f6848c6017a7a652bb9f042281f633b5905cf810b0a0f4be2a5772c42dd0462c5742560,x 0xc04a967f [0x349014e379fd8d997e4a329d074017d8afad7d8adac529c4,0x949934c558e3515004195540656b01b4d054e0080fb1c8,0x4b15fa6d5dacca4bb089594c8c] 0x2252c4211c56e854fe068e613ac3008472435c1 0x8a1fdaca94609184ec454010bcca3744de79352f0aad5a3801613be7c4d24613be4dd9dada668e1a1dd12c50559c4,x 0xe03c13f2 [0x17384142410472859e0d897fe0d097e449800c989165b7b2644,0xc4306d02dc256b32ede8bb5645edf464ea9b519e0c1208239414] 0x73c51e784379484a4e89486c7079149dc707108be1 0x522dde5651871676cf76916b87169140de35cd871676d3646fa458c8706914d87ac6d48552dacdf81a,x 0xa03e927e [0xd2477b66539d3c4654d039e68c834003dc999053579b532644,0x62dd9998c12648e3c554c907598305401f627ade48] 0x44a5884cd0b0211cb8108e4b74266f021b3 0x26776589c94378e6914feeb8c7bd50d78062c6d7c1c53b61890711b3349071b95960,x 0x202c02e5 [0x4736d29612f512fb2f145a6db9042331d0490010492104,0x36dde67a28fb5010] 0x1a091 0x5c5b4ba707329afb336c3a55e90effb35367a,x 0x802a2361 [0xeab1c8db03606dc05011722d41e3f2690e8043890121c4,0x1d706923017a58] 0x12874123a06c09648451 0x1f32bab4be5755a50f479d5250ffe82ac50e1ab3f3810,y 0x401a2962 0xe405be8c296f4a82e432f1f81a10e002dcc125c4 0x3416204d1 0x15acdea1172d5dde51e6c73babe0,y 0x2021815e 0x78993cf85384111530094e38810891421a73e8b9f411f9068036325c4 0x8431 0x17d4ce17d495b5c67fede156b14,y 0x401a2c62 0x20df4614b7a546f610432f1f81a10e002dcc125c4 0xae34871 0x27bb8b63f299da5aa2fe0,z 0x1200f0 0x28bb4e69232d5a46c38325108 0x36e7b33d450,z 0xe8171 0xf1312561d551d5b05c845d0021c4 0x129bfd9e0,z 0xc40f5 0x1193040412a61108412002104 0x252e7c0,z 0x80870 0x8d98f4b0dec208 0x15180,z 0x81170 0x979877305ed648 0x15180,z 0x818f1 0x26953608466002244 0x59980,z 0x96071 0x210528c8460c02204 0x59980]
def d33:List CD:=[v 0xb22fa22fe [1043,2103] [113] [] [0x4557608228208acec10490452444,0x539820cc1641f55982e83a089010456144,0x2a7c8a34053ea48349a56c3d92090280032a24,0x2b29ad6c4d819120c3db2f1cda452e748ed421c0,0x28680569826b5304d253081c008403e07dc71c8,0x420835ec69cb0820a0b603bf601b20aa28,0x919b4a7a8a2082e820ce5041d4d846c,0x1ed8c6c023643dca083a8228d113718c14a14,0x1d0411f74b93041056884b05d0414158,0x82009a8820ba0833a41c413418418,0xd14358b2fa68a12cd15f5fa28fb1010,0x209a84dd00608d299a0ca2800c065301b6090,0x2355fcf548d6db78467f835661163456dd079f21ceb200749aebb8be8c,0x5d9d43f841064b0be0ad5c105f79fdf52cda941067546d6,0xacc70010d365ec1ac15d21cf750bf57b5ef7b7c106cd0bf5367522da,0xe5839a001e3d217c2c62428fbef87e28a5efaa5ff24b79adbe5ed8e4f4,0x28a082092282146d0b3ecd0ff65187f7d91e11e,0x1a32e8585b77e58a10f00ab0c42a428a69214a,0x4cc2d9a284b95c9b2334def60ec58f65aca6e0,0x1459af1ab076b4da19b4ecd34e58bdac5b59ee0,0xf6dd816cb22b2ca431462c288b08c15e,0x564965544585124134900726dc9b5e,0x54584945d74134554575d8501c,0x6448f213f4c06a80cb1830e7e80e2810618d165dc] [0x109c52f058040bc0c00b08a0204cf3f004c2045411372ae1793827420486f6004a330998771623e36add5c2121981ace00954279a9c2f27072cc01215ef6840e87002e232a56249a1bba2004aebbf385e5e034462b4009091d230e89281fdc1853004c3,0xa689c5ff5df9cd42b2687c2f2f0020871e5ce1b30bcbc00810a3404a3385c8ff35b2c7e2f0453471dbcd6c31f8bc163700205138ece0b3980102032de04e5801098d04628d243411881002f3002410bc810bb9e42c9000b14324701b8b409af003850bcbc19eb006130bcac09af00363,0x141d099e70bca3e273c3dc5df6d8fc41745e34051184217a68838fc5e80718c086457c113849d03071f20524173c3d697f1bd3e4481d0e0018cf7b18d05138bbe26d8dc5e10a0288421085e9a20e3f1621e26d8dc5e10a0288421085e9a20e0b121fee79b830010d05600944f28bb2dee341598520d4d8ab0061213ca2e0e306535c6075df9cd42b2687c2f2f00207,0x11a6aaf8f8361d588794dacd34403085b1268810049105b0e74802b18a23e0980437a78a23e098065078250502525826b39802590d046290b83961f69181f200101045a1,0x1c9963410472698d0411a9761da647245896c100250842c6009443e0d801110dfb60c2f8011185d1610b2428d1811790f8361d5982f99b6b1e723d8dfb18529ea0836c07dd1b5bf39e6c2f0f04c343557c7c1b0eac33aec1,0x1628422f04e7a8442d4420db043721f0612736c1c7c8d61b1f0623536c7c1b19e93] 0x160922b696687f06a3a7bb1aa3cbf1786ab9b91fe96ee0818f03474e7233c48a6929885c7419fe175b50e4d50b1dc2c80239cbd02a7a5c79405f88209c3d93be557bdad64f7f484090000346a59bd84bcc3a476dacf0f61747cf565d47021992389c157013723bd7031ddc1c780a4e7292a037898b0d653003bcfb0eaee879aa123e86900573d7a5493246cf284bf603104bb7778ae33fbfade4d81c84090000b46931c5850e5b1a49b28f8364cd33c650d1a80c209f6cf17c5ad48edd9c58e6c5255732dc8e65c035886a198620825ddbc4aff8e46899bf698e6c0c7c4e97c273909d65161d5b89d1b593545452b43626104ded1cf919ca527aa06b82c839dc6758ef3a6d9e56ec8e38fcee000ba4b9a84716fca6d1ac3a3b18ee1f809e260953478c74027dd3cdb165f83494060d94de6fbbca39c7bf2b66729f5754923319245e0977ef3ec725a10b5792dc8be04c746ee865b741814f7cfa7a38fe0c8d950d4739b34712291d9f0e0039b618dd654b033d9214003bebb1cff363bb57e3acd3ad5041f774db3c75840d73ec1979c1504f937c17afa4b3d8d222bb8fdc6ed6f50d1ac0b2ee093f57d93fa908d9a237d1dfa8305e25fceafbb0df9dfa76a90d16e8f7bdd87f4b8279d7e3bfee838adba266fd72ca176d7247eff88dde60cee478020c71dbe568adbe5de35bd1bbba22eeb1ffbce35e63cc1a397a1a5a7d9e2c70dc9c35dfb5cd1fbd8e71eb3cd9e5b7f7db1c772022770ca4f1c88c9a35eccdb1ee4734fda02e2376c1c729344646f936df9b7ebb7ddd1719a1d008d268dcc9fe83ed6b86a51f5463c5bd4dd11bdc9e8397d25874e3adc8b0fb9f7fd163e9b58e3bda2394c1a48312a1defb32446488944b64da356e6b326fbee8e6780dbe468fec71dfd1738cf5fd2bbfa32f2b2e806c93129346a651a6bee759d2d39c4505b8d02d67f218f25033e4e1b0c873ed785c1cae83a6a329ebfa577d466f97d78f0745ba4c537cb2448370ceb228a79d1bb4df0595c86133249d605253cd1e46ff40fad11d2a25268d69135f7ba8a05ca0d8f3507396c733f1795c5cbe83b6a71df03adcd34025f379707fcca7e4cd429648b406de9eb54940def5b6f6c0696002b3f13f56655750c46cdedeac932256a48b63268d7e174eb8e26365d6e0a34d707a646154c40c3432f6b0d01a7c00127362e4483b006170dae817683f8c863cfdcd093fce7b27f379dc76e7a9cc68aedaa5ab42f76089bb545d9c25f5cf75df1d9b56eef851227429d009f5f0b42fb7a9d1e4de26fee81182a0683b0c4bf54d0871afa66a878853e66787dafede0be6a777ad4e2a23f6bc2c0efba2899f369d61e6e98685f7ca7402713fd4ade3fd1be59784074f393eed5c3fe23418a85f852129e526ba0f9fa77d96e69a10a5812d4a493e6000f3cfeae2e4707ae214a74025e5465e975cff14a63502fcb65feff4e334204bceeca027296bccdb7677faca73c5c25cb25d1aa00015ebc6d83dc507b7dbc760c0ccfcb94cd42a3f73bd77efae8abbba4d6e8fd7eee0a68c7deefa43020f68b46dbadb0766aea7775972242f8fbf90c1839a7d1f6fb6c0dadd28bdf69be6f0a46849e35f836b9865512800c9f31366c3797e543d01a1095f1b94aa90dae650f1a9a85dab420a9746b0017f104feb92a26f7fdfd7b086b27b98a81d87a63a0167fd9bd7a77e0a7318c8761e98e805dfe67b639db877e88f2b37f99ed7e770017cb07b35256baec445256b83ed7e96c9d50bb0015efc9e9af1ad1f41a8889e7430489e1e96f15fb60810fca1b0f5fc733c64e52122687e50c942188913aacce29594e5116cc0862095c849e26e1a94e804a738bdf222b6f7444b0d4ba423f00df9d9fafae8c6434102a9d008e6385ea174f7294649c1d7a8238734215a4a7af198a4187b1163a4e12e8900182586a65800c62c9eed144a4e65b1e8085ce66e81f8564dc96823a94ff5662f71014b224dd1,u 0x220772075 [0x5288db346df2404004ed5db989012411412004,0x7b9051892bce1469f410722b9a248c3411c0,0xfb6c644a00fa305bd8c6c020d7307609d0a38565428,0x19505ace88b355984b36183ef098fb5190] [0x10862008842e80222f7218e8ac41d6012904216015081d309a6dc02590834c02a17bf3cb9fe1cb70096820eb07178054317bf3cd041d867e2880d066dd003db78fbdf9de1c43001e9200964210bb620088ec24e157e2c211a798469c84802d8,0x7b931] 0x410d1b706e6f780e45d644aec02ce831d60868dbf00fcd087715775d7bb56c967418f3df355d806972802e74018bf15075100265edae231679698ea000a81b094ed5e2008138dfc043158d389139d410e471959901a5062405434afd375f80031414462acae6f3228da6b93f6e001b8182c0a9d012c5963269516a8c700fc714d5da4da496b3e31420053164960,u 0x240732872 [0x1038fe95b20dc005b982e62404d5b66b5304d24c4,0x8108d0a6befd04d0323bd97bef6c1c7e4bdd23420c0,0x741805628c109729b8ec116660a854deab01ac51038,0x7063f5063f820f18581b269a0c] [0x10882213857088bcc0d09add89222f0c42c888bcc012103b2c012111a0123418dfc2234183a62d01991a021bf98a9dc25fe784026a83a7c0261680ae171e52271bf884687b5a353b073c99f8b23438d4e3,0x2c360804d1] 0x1b48962d8c735aa45be58bc735aa250006a5e08a22d0b1cd601d81bdb327b02ec6412c50de42dc0385c942ed43b0a5b9fb19990684ea01f108039e4a5b90071ad1764a77bc410b06d8c5608f9c12b88ebed6c31171137559900d0ae253c475f6b6188b88b33753228746e153f8c33ce0ad72948aac669713c48f26a3f2,x 0x1204c2cdf [0x385eacc4f075f1684380ded7dbf35f60b7304129c4,0x1c1088d4896c6685477b4a30402542e38e42420407c5aea48,0x29763c839800f7187b5d90] 0x35910631421c18c816440cc2b142d60b2576dc369739b5a20cb08582cb2dda9fe10f3474 0xc80ce85e949141640218e54cdaa35beb08868f73edd5347b35c9b63c45612c8960639b2ce618a26e370aac45319008008eb4ecde8a35000b4a7635c180,x 0xc0585071 [0x5a6821094cd8b67cd049e7cc849003dca090134120c4,0x19b02609aaa4a1c09826ad8a0a00dfa094b0f62ac8c8,0x683b7069231078496db2a610cd5601d98383d4] 0x223100bc3cf30442360150b3c805f2bbd183962 0x253c5400a0f82cc80106280176940eb436a83cc0b10928d1377921f5d1d307350d6bb54a0f5029318e22aa533cc67a162828610f7323c837b3e463f0dc10,x 0x1405828f6 [0x20bb0b5c8b0723914f9d23420f91060028b4b05124c4,0x2d58e081f30f6f5b12832d307f369494196983ec,0x11a65e3a2f6b10b41e2b20d7a82b76989ee3587b5d90] 0x29c884201c4103881871020827c100982012841a2080601 0x59482f0859a9215ac245005051191785288e0d41c1fc69a82f9bc2ba42021d80832a6d04a8b962b54040554cc999,x 0x604a26da [0x390068bc72d642b800ca89011415a68b5304125c4,0x1b3d66982346949aac07741a098c10094eb8e0042036fac1c8,0x5084f832de260039654] 0x85714211ac41 0x3aa0dc16d0ae30d0ee6c2b9f4d5868782985dd47531443bdd36b450d964e8d5f6649c9151,x 0xa040945e [0x4a6003e1d63ed458390ccbf2429a2f3d0470115c6dad12504,0x12c166b209259183789934c498fb5150041d646e83280cab62a68] 0x2d121a134719d61a9e1 0x2f94f7570c0008c6b3752b635eb84db45a7c79c12f9a5b545377ceb6695d253d2,x 0x602b0855 [0x89187a547a6c3a660fd340c8307ded037e0906e039890d20c4,0x31859d9b0c4d10] 0x1286f108231 0xcd3bdde21ecd75071beb618997b731ff3bbc4d0,x 0x40292161 [0x2e7acc13a141c69ec8c845cfa007ce9907004189013492004,0x870bc4c8414] 0x30f238091 0xdb98f5cc4bead95c2f7e66b712fb0cd66,u 0x248275 [0x66313ddab2f61920eb3060a98c6b2921194e83a720d0014d20c4,0xc5bb4c] [] 0x1ecc279facd8726abc690,x 0x40232962 [0x455843e5c1505c845173e441800c18916982dcc125c4,0x46cc] 0x983a091 0x1552cd1287132df74e3fc50,z 0x102070 0x1d116a0d20657b4a58041c8 0x1a8e7810,z 0xe8471 0xf1312561d551d5b01c845d0021c4 0x129bfd9e0,z 0xd2070 0x3adc19b0c7a58f4208 0xb5b1c0,z 0x84070 0x899894b01ec208 0x15180,z 0x81870 0x8d98f4b0dec208 0x15180,z 0x81c71 0x1ee5264845e4021c4 0x59980,z 0x862f2 0x428a2108037b2604 0x15180]
def d34:List CD:=[u 0x7015216f7 [0x1156d824bd3041256d824b5304d2904,0x1211c00760b7b05d048082292b0c1249c444,0x4b329d878e0934f8b26d1e62a08fc9b4d21d00,0x130821ac52d622d1c8ef65eebdc313e049e6f5b66600,0x4a8c016e6824a05905c7008084080f85b7608,0x59076e9030f680d9d8c2825a582c2dedb0349f0,0x14750595bbea020a3ccab6020ea0de68,0x1d62a20846b3ffdc253e009490206c81a248c11cdb4a589ad4,0x5450e62b2f1303d87bad64e248ba8635150,0x11c6ae9babe4bebe086da9accc47b101e8c47a101590a0820b28c90c,0x138c422fc3a51e7ae9fac4aaf82b4b6ab857e38d6d6] [0x831d8846c10d9e421c068ba0f2686c7c16f312abf9c8bcb3f6e98858c0311fb74c4367a8403127b73c01690842d1cbd802b30842d1cb83d2ec0159fdba6a243c9e086d042260188a200e681f108d83abc02cac401cd03e211b07578802bb6053c5e5e0868c018083f1c01812dd5ba27f7089380625,0x2f2f0d22108c5e5e214085e5e2190803108ba0c068857c02521a7bc03117b77c0311662fc5e5e0d18e0c66211b04366a290b804b3f6ef83abc0311a01d360188c436e01888d3de21ab00c4669ef10ad8447c031273c1ccbde508784237db174188577,0x10b0221630756421630434402442c173c5e1ade0d43009e8210ac4044068843387ef805525ba297f108460a441e919d05220f4c0168980259084711797886a21797886c2,0x3c90c181c3c6103abc02a103a618303886d2f6e7c182c3c61b843210b27c1488503] 0x29a91a49993531b18c52902ea5f213d80ad412675b08f8083b7228402fa5eee35d3111f8b0a3cba1563ac91e81dd847218673468006544b60ba994752e7bb080f369e4cf2811c9913f93cc4477b011405a3cce085596b649d84a52205eccbad4bddc7fe6c38ef28402ee6c7367f3a984c445ebd143424214672eb049d572b631084c994c50ab3a2466204ee63317ba74ae23a74ba14692fca7e80169af9ce58e040d47fefebf9abc8400358bb365e6e6503b9b80cfb4b141981d8e14bd51a010fb800012ad002b5d84876ba6d0bb81cf62833039229c021e000016ad428011b4c639a74cecfb49801eee8b1419b8a612021a00001adcaa0056db18e76781801825408fbacc5cdb6e0e55fa7cd385bb6a699db40ec0eeaa6811af900238d26962080becdbd009b497fa138989c9f95869addc8bc886683b302e769b4ae37110023a827f406dcc061150dba00575b5b2a742007e14172c294e64dd7076e0bf38e1f95ba783a72fbea845fe0293802f26fe2dbc899ef2f4b9e3d89ded2a44bde4d3c93a001f44dcfa92b3357a0c63965d8cda7d13cbd1b939e5f44cff99a176e7dcf51aefc6523f802e0cbd0f6b2072407920a446cfa037a1834028080a97720401dd7f62aea3356ef6f181b22387a3afbf8bb046083ac8b0e99170e8d2b8c4cfa5ce04027e8d2a2ad836e6931bff3c85a80e25f9fc49171d5e8f11429efb38cf8d61401cc0ef8810bbb555b1b2821f769ae522f663f3210aa1c0d614b56fa7408d52641aaf9d3dcbd98818f53e2429deb44554c5aa1c024d4f4c987031d6d3dc87a3e9768762fd9c792c8d3775e9bd7d20a40d0bfa0472bc88088a64c0b11100287006fd4917458d9b943804afc9ce47b7c3bf23dec1ab42c22839b05b595018444053d3dde38143803ffadbfc50b9a55a1d94d06bd911543806c0a0b2250f8b31103106e51adbae6250400f33f752e820071c284034d00ef4,u 0x2e0d8137e [0xf60c989010411415b608a0b4b14d24c4,0x1893e087b19602e3d9b69274d140d384b47d21900,0x30094eb8e004201f0be8348032372fa82c5c866500,0x659aca4aaadefe09ab63a7ec1664341ad2c525f0,0x50fd94d2b7a8c1a793558051f4b98837bd4,0x15a2280b57626cdc6120da4fa18c09c832450,0x2e84f10e4f0ec4f8ea5fee424ec4306d56e97b7097a6d95ac8bb564acbcc] [0x4b5f0bcbc215b08aad01fbbb9e1661139662cc69e717a4c3a6b0333913bdae273cdc42ab388a28bf2c3575005451e80d29300d14c180392bd021918f13bdae2f378848e774010d94c1dd302d9a58a1797a34c083cc1015d98b31a79c2108c9685e5e0148108581fcb042388423e00444108f8025939e06108f83019b9e078083ac01290213b00612002108e410b6234f3e5108563,0x103945038060428422fc5e5d373c3d98b31a79c0068ac1797842c61740681fcaabf3e08abe4da0b1002f6] 0xa13f42b200706a185314f14ac801c1a86149c12b2007068e153d831140991771821c574bd8ad95614b424c903ed8042fe03862260a8b38f490f5986c9be003d327d340add0e155255740e8f202029564636f23d7f4b51171bc81fcd313550b4581ec4175d21ad547811500418780372aa5e1e564cc7fb9a6448d1bb9b6d72ad2fb7e174378d988a95947540966245244c102a35ce5549165c003522201c8234c14502d97831741d40290fb5654909c1e4dc1c09c418a8956345006f4d97831741d4029ad5043119480991370794e18a8d1401bc46d48c240674b8d500d700a545021314f27012ba385471d15beaf630295c650655c7c96a9cc52,u 0x2e0be937f [0xf60c999155b6482d6d7d92f4d55b64b532a44,0x69db611f9274c05c7b34398e3411f9a12cd1903200c0,0x3699b09642cdc8ef7defc1c127c3d8d3a1649d365240,0x305499ac0f688a379f636d654e00e0128171c721210203e,0x91c66c2a9037e63920eb3028235060ce6187343d4,0x29713974a78945fcd61376df373e13359a76f65f5d873aca915593992ca66610] [0x1010858202185e0ec821410798018bdfd0847c0d1cc21ac62533099b2099bc086c8c86ab80269e99042820f33da0347010778233f14401f90216c4d08593e10858101a2dda8a10d78194a70216c9061f98210b5810da2e129a10b580d1a2e129a10b5db900245,0x9820a443129631297801890421604064b742af704053099b1] 0x4d2a005dc20c3a28e02085b51f770f40cb6e4e80303ca205502481a60b6a200c4022f1eb7a66840ae40162f81471db57f4ddcff25c160294a05531bb2b03076826fc35887c426e08bd2d6f4a64210b7c0b3b6a287e31401cb8409a6ee5044c6b38307f140d3afcb41e70954b62473608ff1e0ffc496c52c54157548e08c4ede3d17741754fd5c65a0d3f74b2000235eca3978dd997c5f1c03a9c3e08d9d2c998400c63c46b04441be8e254208cb1dd456a1de3ab8212cda460253f9053dba8c2f4f4e268d63e7d082753caf76,w 0xe0e40375 [1792] [] [] [0x1e9ae803d4839039dba09010410410492004,0x4580b1a61cc458b9020cadcfb24e9a281a726921e40,0x8b09740cb5f26b29f0f935ac775da228f6d77008,0x1ec7d8fb0090e4098232412f668d5d92cf230a58,0x3955e2568e1a156d465b9ad281bc405833327a89b3719e97b5050,0x22a514a0590428c3a2780018f7bcb03c1dafb1510d24acbe0acbdb22ada,0x1c803f41dbbc843641d80b9131d4239cc75f6331c0620,0x628186] 0x8c79e00f3c9c8d5912d8125b1805e225b180232e785883c2 0x7d096420030c43e405d324f686067a0200b9cf49f8124400118570f19a05172812f0401010c38a210208213e6082f02c06c0477d80121ab01c4c5a958db0150b37620880926f695474360ce6536fc9d8074fa59b94919b09d9581608311f46683a12553411b6e3b065dfada7f3823a05381d8d2153230628e181683c1383a50049b7006fa086c0189934022d54031272e863c4a146e4ac066ee821880,x 0x1e08429e7 [0x4b99155a609ad4c15e60bf3057982dcc129c4,0x1c8484080f87d91b8323969e3b10fc14f73ed087e44b812ea4,0x111a80f20b342a3bdb7b2a300500940b20b8e2242,0xd4a836845ab8bdb37190ca64f71ac11d25eed597b0c107418,0xa5d8f2435f4] 0x4318a1b87a8fd90ae684e14ea8a1a84486a25dbe86f2032856250a9ea2c020650846b756ea754c0b02e98c0b0404e1 0x2ea0030cfe3199b23ad820b99039e7808768310d7110aa00004c73d061136da9e410a30c549b68018e7b18439830562c0d006b2682118987010e5ea1949241313b65929f640cb843b4ae0714ccd5047046abb3efc4036b11ccb323bc1781a588e0adc12df863ad28880172dd6d5002c439a5400078695e8000510,x 0xc06018f6 [0xef6ccc7e5189e83c7056431812e6414d0565828b432644,0x106695019aac27630e31436b267001f4aaf2d6d1c8,0x1c911d4b91cc911e01b1062d2ed313dcf3f513f6902105f3918] 0x110086201601288a11620e0842b088461880988462 0x1826ae019c581dc93a190063323c1c5045d3c119c82128f75b625184f051c0ef510943df687627a5c09882471a28231db80db151c468a09aadc63c1c3eddb46225c77be560,x 0xc060185d [0x281bf0e660c11f640380ec7b6f6e6240413492004,0x9dbdaa462877d0c729fb2060f209a0646f342600,0x3608ed7d66c31fdafb4f69a2036c9584bd709d7b0b98] 0xa8307582510ad023283acc9f04a33961846ce5f0543 0x31250484cf25453760dc217b086f3fad08176621a1984c839b861e660b4b4f8f221e18d17fc5fc7392bb420a962d238003bd2d21b447a0,x 0x60380671 [0x5c28f71056e8bb076d242329c8890010450492044,0x16c50e6aed2461f32a68aab5bd87b547bec] 0x668c402a0f3c31 0x76bdb33ae679741914c585ddcfb95d5beba0d8f79cb29f4cddb053561cd3ea8b79d634f717f3696,x 0xa03e935a [0x6921994e74e858931c6823f34893003d8326245579b532644,0x1283f92831aaad4e55c22a46a4cbd25b114c007c80e0c8] 0x6a0205c34c4268c2b7666f21b3 0x6335513754c7078b4d9d9a5f068af06fa53b7165f054899474845893fbad7941b745d8db60,x 0x80322475 [0x54f5da00a3730f60839083c7e47d82423810e240492104,0x1d116b4d0c60fb25434017a58] 0x19e9c4d040804b1340d804b2 0x4cb2ef7d73886d266d7563ca72dd4e979b6aaef30a2bf79ddffddbd1dd140,x 0x602d095e [0x895881c40851ec5c82b73ed087e441810664456d9ad6cd24c4,0x7867133d9e7d132050] 0x83b1859104c1 0x31bf9dca8b3982fed96a438cadfdd5a9942fbaa9e0772,x 0x402c1435 [0x7a3ed4543d5a00a403041c845e797b212400f728240492104,0x21c2b4d0c617b90d0] 0x160d41 0x19e3eb6ad2ce166a4ad7b11beab754d,u 0x284275 [0x10b73b980510502d8336f6e949080eb9afb405000592044,0x4bcca5fafb0490] [] 0xe56dffdb353e82d8f4edf10,z 0x190070 0x21c29cc559b0c42738d2361bd85b24108 0x3f6ad27773b9510,y 0x20141341 0x25e61dec0327a928590641126049891520c4 0x1b71 0x3568f9157afb66,z 0xe0c71 0xfa322561e951e9b01c845e0021c4 0x129bfd9e0,z 0xe9171 0xf1312561d551d5b05c845d0021c4 0x129bfd9e0,z 0xc2cf2 0x2c46a44b6210e037b2604 0x7caf1c0,z 0x809f1 0x22352dc8421c02204 0x59980,z 0x89271 0x12e51a48452402104 0x59980,z 0x66271 0x8514421002204 0x2960]
def d35:List CD:=[v 0x2e1b02275 [2103] [] [] [0x3a40400eec1dba0ed3dba09010450411412004,0x4053922ca8da6853140dd21cc104920500,0x3efa083901ec2dd7be51b491d2486340600,0x1b7652282484c09f490616615411768ccc48,0x529612c558e30655d248d7d8206c555171d7b406c,0x104158206e984185608bb0d624d818a30a98,0x3d97b0f7eb9bf43d87b0f609200823343586b8158,0xa0ce1145b413d602c058aaaa52c25830c,0x6c807043483c0054da7c9770d37702cd358e9a2b6e80039000591aeeaac6cc,0x51a40447bbdf75bf2f7ef4c07067c8e1c69c38acc71076d2f737e7481df735db202da,0x2f37616f6ded90869ec01e07a50a282082d46,0x42dec999c365a1b336705adbf85bdc7b866b0c99e0,0x6ea08030616710062aa00e5efdb7e0c57a2620,0x38628186d6d47d059dc] [0x3478c422e0010dc41661db00446211300585062b11a04682060c666820beebfc4abc9a229380774e830cfad7dbdfd1f51532c9bfee21194d1ef109f6ca54d139e00e509808ccc9471c8cff27436b1d34bd178fcbd3f37e56e91d5925141a261c402f17ffd5bf4fdf61a77915b8b1c728942109a83e24d0fda13d8997a4c9bbf154c2a58e9a5e8bc7c38c65546883bec446007f21fd3f7bc8adc55e3944a108426a0ba687cbd277449bbf064683e11cb011627ee2ab407bc191a178472ec01fdc41d60e98802509878c42110834c1d310842c016100031,0xa7e88004124a0014801109879130ed9076268f188452] 0x596a2d3b4e066b8006df7bbf96f182007048b8b04501898030628e2916086960b0b55119006001e357d93c0b38703dc087ebddb66a74244815ded6810490fa1eeedc8807f813f0205cf0d10305d9ce8a031000430c30031ec1041473121cca015c8c0c0008f0e0afac9d66e27a4212f76fcb5d3b1898f204040457d0409b012d803e8fbfb53a9302fe5f81473fb0440034040bbedaf4eb47e2869b1e4290073adbec508315054d089c06a46039dbab54799eb64413fc1817f1c32df5284062408f66f27e9030e5dae9404ad81e4c743811b21cdca5068200730bdb072a1020041bd56e7cbf39710eee2eba472761cfb7d3a64f759a2c007472c833583c7d5e3e25026b052ebef81b9212358338d7e9f10c3489246c41f6d624b1b2a93b1bdbda84080102ff5aa1af95a0df4697e8e4ec01e55caa73289bd91e003a19b411bc0e56bb250a6b053eb7080bb4ad216e26128d430d21cb1b117d36a96c72e8bb74ee3a26df0707776bb8eae50b07376ff599d97eb64e87914ab873ad8ea6470d11076f4d81c9070b55130230d434d24b233277eba97dbfe302e1df342080619246c6049b1ede9b1b9b3e4d31dbc704761204e5dee46fa51a2b000fb4c8378180104413e824200091f775b004d561059b00256c18073000fe3c61af4ec140bcefdfa077a49ae640bbd5c4ab1369819f35d0d8208ae2bd7aac7ddda17bf8d7fa3bedbc439e7e450751a2c0c11e7420c1976111b382c9daeae47a1000048d1dfc34ea35024146835dafc6f65181f5234223256a95f2b075ec656e74b000622c78e740c6d177e2c243f1fcebef54b83a980b0c7c55a023cda5387ca8552b14514a500d4895792649b0cd80a30095d24cf270418c101b91abd244a262c114978039fcea1b69c0ae934855ade,u 0x400b219ff [0x656582682d2c1356dbeb5f6082dac12a04,0x1af45fbab0f3c113656e7d9b4a0f1c3590f20032e64,0xf91944186b316ae477bef7dee097e0fbae8366600,0xcb514db976143f64343eb606deca8c0181c720808423e,0x9ee3d9369b6a256c09d031c1082d8a4cd81b72d4,0xf5cbb1fd52ec71303f1043f806c41be8c] [0x54e61542110c0138417bb004e2849c15bb80421a8e162b5bb80421a93810b6410de200c4213d7803112202600c4520058280f8d0d4f5bab7427554068027101a3e0340138e127300622,0x4d10c7a1005610857c01589100b0856c0158c2acc510130ab3209ea10058102a1088405421130332302a1089802b188210b005634404c410846154211096eadd09d53] 0x422cfa3988981af520e140ba3a48e00b2783718e59b165d973793c084333c2817475db30165f081af2c66e620931286d04852c7818e4603110a7824202e8ede0eed634327437d58aed3dc895ba5e9e486c6956840183bc12f94843600c3a71122bc776220bf442172df2202808187d2460826c3a9186dae0ca9a6c3982036a8a9d853cbb6866c849a0f11bb6686b787ceb240b13630a20813800488d000d81882dc0739d00058201040511a000a76ca97944479c40dd1c2599c5e6a3c4f3f9ec2498ae2d7363345007c6088a6458e53d6f6c610069c4014788a903103b738cd522270a20813aba1028982025eba102850,w 0x1213210f5 [530] [] [] [0x995519642c817001dca09010411410412044,0x7aaea5ef9c49c51a43d9a064728c4f221c0,0x18d88e7aecbd946a45fce3b3db45041e0081304187208,0x268fb441037cc63548dd2083b4413158,0x218bb1319ea234d1f43da2080204d104d9198,0x78ea6d3efab9632f94f8dad281b1439c26a531415da69a8c,0x4a8fca5ac7bbf5ff563fe383f9e65d3d87baf53f5587c3da7a970a74d351dff478bcf1deda,0x3fd9b9f253e06f01a475234e9409a08a282546d8af1e,0xf45d4df40dc37ad9bd6cdfb66edb3574e0,0x10628186f7d007c823051dc] 0x3cba8f974c19317de6c3c617de6c2f51034412e7c20154441e088421 0xaf8e605f0004c5123984504940af6282b9b9a4001ab51239895b3c7770610000986db14715b04eac1b80001413ae800888628610a22826dc405760e486a1043ded70221042e6a7e8a38208211f002804093f0e200853dcc031a9c844ab55238021523b7400100000041c00833c8820a52206805d022180301daaa7acc0006005c010113a44810471c22c1001403860d5812790c71004276824b667f349daf8002055c49141e91cc5a4b6303f9fa15ed64ece92002a881c4c526352da675aeb66f6820106918221c24dbb5aaa8da0d,w 0x140f41175 [2085] [] [] [0x3d440187b200c00f6ec989010411410452004,0x8c4584b04914203d95b9372aa52d5410f84b21e40,0xa5b7b0454396c743dca28e4195d8590660ae0c8,0x7b0f600a009f326796e51366030af4bf4298033514,0xb1590067ac4db218c9467a3efd937e87b1850,0x51bb9d7f46876464aa1a2ee478ee45b52550ea465e73e56b20e7591be8aac4cc,0x23007251dd3805fc8ee9bfbef66ebc01605a50288ab46,0x143140c34a0ee1e415fa02c95c] 0xbc2261f0346422fc4d488442117f85d005a622ff00be5e5d3b8559206c7d7616871726ae2012e6f12ee259b8595edc802d603b79377df3c2170d78c00982cee6700999a22401107fc2ea1 0x3215c476a61d0f8ce885128a2d4f2363f407e26a5c5060814ca0d014842d1d821a2d0ea64d0414083cc74e54a02642c862d0ea64d04160f10de9c9208cb000b4c8adc097754580239d082ee2276693d039716559c081faebe670608208478bc2c4613be18f9760185c0a33622b68aa986f41a2005838e02f6a722b877010375ce86556d0114941c46144a434c8061702640a7b60dc6bb195676351b6507452501c2c0e45e8706b4184862d0ea64d0414bc1ab2,x 0x18064197e [0x21acc1907003a0cb89014569826b4b04125c4,0x391061acbd983045c8136cb9f0d6a95b8e600f541e40,0x3b6366e3009da60d344131bdcc02b843996a4c6881c408403e,0x1418fe4bcc] 0x10b220098210b1802613c9004c2090e1d22121c5a44243b03f735c2ade48026184230add5c2121c7093421740cc700563 0x2d9d544ef8a3cee7a6420001a6d816a59b94a8b5282f3ac134f9d121765c10517c6c66581095bcbd23a92e02f46041b50cd120265baaf05e3dc809045ca42080f5a648419a1244e6cd1759882d59ca5c583e482c0b5e24c4d7c978c0df9533210f13e5f2e60,x 0x1206450f6 [0x3331cda5189e824715641181286444105659ad4d12504,0x7fb47d48bec0f60ee41a8286a64ce003e0b6c6fd0163cc0c8,0xa4c8e6488f2318bb3518bee4597b47df5204391b532bd89a54,0x39423a9423c] 0x1788847113d5802d213d580d003263e406883bc0caa40423977b4e093781442c243fac4f512dd13d783ab3 0x32f7d76f8141ec29b1f0ed2952036c72d9915f7410e183452009860098e0fc10e6dc9a0e8e848c500a4d9f3be094106c7810400ab4916cfa9a132d95b8c7d9dce97317cdf0552c0171c67d2986ef140233b386d3c795bb01d60,x 0x1004c1cff [0x1d7c5f283c000b6b5f60bf35f60b7304129c4,0x9914c15054e10780908101f723cea48ef7dee189fdec1665c0,0xa1e9f001f6bf515c10] 0x2de842ac8427a86da843615fdaca034215d00ea84016060d7300582 0x8f07da5a8b6d2d21da0babad57888c3144b1599046add4473445345b1d677a797ca7922b1dfa791b70434781aa4d1ec0,x 0xa03601e5 [0x8c5046c6d92a844fb2f6823f2e60908e043890124120c4,0x287385398a9030bdf83101044184414] 0x25c8812c50898128a90d8ca702a9a113198e04a3 0x23f5bb7cf174cf835d2cdbcfb362beedaca6327b55db93cdb1ddf2d5edaa3a7b46f45ccf3525a0,x 0xa03e527e [0x6923bdb329ce9ab5cce9a073c889005dc999016360b4b2644,0x97994bf24b18134c90d665ecef61105110b114c007c16f208] 0x11052213342c08472002108e4b74266f021b3 0x265763894902c8a956fc611d316d9d70e008b57c1c51f7389070fb7349071b8d960,x 0x60378061 [0x118a014f7ce248206420e7c7dda41b80e62424120c4,0xd4c626cd865032f6723132c158db38d4] 0xb0404437431 0xdb28db5d33aa76faddf5d138c5ef143cb9636ffbca74eb88797d90,u 0x3204f5 [0x132a928a009c21cc5d94b472354627a033c8940012492044,0x5176f130bdc87d104131da34918] [] 0x154ee3b58f2faccff32689c32e9bc4670,x 0x602b605e [0x1015207102137ba4608ef6cc1f2f7d4fd40e005f60b532604,0x44cc2f7e4fd4d90] 0x84515bb30a4b766171b53 0x1f5d1a7ed9561c9f6e730b2bcfdfe23bbd992,x 0x6022865e [0x156b921322803ec6359491ded994e49d3c4683a01bec525c4,0x90d0] 0x21b199a1a621 0xbc7b67dd6c1ab4e97edce272540,y 0x601e0cde 0x6f3136b82003ee479d491ded997faa313d0780181b732644 0x35b1a9e19d61 0x1bbab3f6b6b952671a7b988410,z 0x100170 0x21c29cd24677b491824508 0x7e8ed810,z 0xe2871 0x11b31ea62245224b0208461c02204 0x129bfd9e0,z 0xe9672 0x32aa92b58d242328037b2644 0x1fb6eb1e0,z 0x88070 0x789892301ec1c8 0x15180,z 0x82170 0x8d98f4b0bec608 0x15180,z 0x824f1 0x22e52a48462402204 0x59980,z 0x60370 0x4e69232dc8 0x2960,z 0x68671 0x751441d0021c4 0x2960]
def d36:List CD:=[v 0x4221221f6 [2441] [1680,144] [] [0x4114104158608228ad2c104d24c4,0x3692441820d3a83e9050027b041dbb0624,0x30c523676c3d922843331c52e600e3dfa5ef540e40,0x98c1d75d4f60eca0940efd31c7a02100fb107908,0x26944499c2092b7bac0f60b3e88390500b6b2670,0x220ca6ac5584325584499c208204c45d7b4b94,0x20c3983c83efa10200ca88ab2666ba35958,0x190c698c9b450018083a9811d23ed1a7d4990,0x722a369774ad6daa9b0899405ea0a38ba084324a9a68c,0x1ef72543a0a5e3b4380098f048c4bbad7f56cfd454eddabd9657af6572f6a929c00434,0x504d04904294082082682482146,0x1332460c131778ec9982310704d11ab33360030032952,0x8262ecd1860ef5dc5b26626e107704d11833052520,0xb0aa0a26803950578d065b862ecda632a0,0x6554184d26124115104d3471c,0x86181b4906d2498415510493575c,0xa64790ffa040cb07bf5bdfa018a] [0x174788462108b83382dda1d0b06678150094a2d4138bc9c20620842c1a2e0158c6c208eb0117981c45145ccb725a9c2d1b67add5c36d481c8712019c08f8bec2e2f1f0fe48211706885c78710b7859ec0dba5a5b08453bab0843961c04229004c134df804c2,0x851c02591c100b9bc08883a500b9bc4299f335f440f794b34df9785c96a620ef03f71a207bca583abc4008d4d37e20f0802b888451a084525c2211300ae6521b139b805730688269bf154f883a31553b841e60e853ee8b9c8e280af972dc8d7e074211af190908600d009c3005a23e2e8f109d83ef3,0x4b1] 0x3ae81fc01b7ae8e47f0d51008595e80596b14481df179cea597dade3d824446b06d16a9414c4fc31834d76a51f85e400083bacab412e1b83a961ec35b3f09cc4fb78a1560de9f4becb31f5b808b0a88c60d3a002cac53a816581d12517adf659a0d46f0d5655a5fe5428fd489c0dd539389abeaf1fee81e7e1b5b0d156aa12f8dc80990efe5702a34393c72c7dee5819b82db48e7fd82ed0617c3f5f5fc7020ec352c89fb77afb41ae590abdba5e1f77addb42932f8980820000d1539fc3a0276e760fe1d02a857a6d02478abedbebfe0b350072343890432200dc1dca578589130306989483a2b3eaf1b5c1d8ea2b24bef2f9b04b67eaed42e63427e8eb6decf318ac173c3bf63337ba6d0011957b1820781ab9731a2afb01b7c166a00e0561c500e982718fd243b68524022838140008530c753abec75483f042915f385bacb64a24961dfc4fe211681834c92588d0859f0535dd104ba40a4d60713a33a3d75583e9f7eff538266effa71135dbd6efb6bef6e15cebb314470d769f30fd645820001877fd94c5004ebb04c6404de94393c2f9b996a32b8c44f87a245dea0ec352c89600fdc0e7bedbe590aa0c92277c40020c8915a507d6b076c0adca14997c4c001001068a9cfe5b0e80f3a6c8ec110ad4ca00041dd6a71f895800541de883c5066b35db3152690b63aa52a7f2d81c1f6599f082980bb0bc049604f641dcac354891381baa70e818a24925774e0953f874015122dc1a67f0e81d114a8fe26a712b00512243b094770375881d8c6f2765f4ecc0426302243513ce5,v 0x3018e2676 [1792,2369] [529] [] [0x3a0901045049055d8249accc10492504,0x136a369a36c11e640c000ec15e60ec10f70024,0x1deebdb113c9f46df260d7d81ba411f63cc140600,0xb0a1a98a4be1038010807c4fb8b24ed39821ec208,0xc3680b1e8d304b5843976a8bb7f63828d2c79b8165e68,0x2f6b8c0dda68db1f66fadeed34724049a3b7a58,0x255e4ac18416dd086c8ba8a7ccdd8a6ac0460fb94d0,0x248214600031e063df78870790796038acc70a54d232dfc32ded6,0xe4adf7ba3609d3ef648c042004904294283146,0x166d97471d9b65d1c724c15a748f92b738ce620,0x23e9aca3e9202e0295e046dd5b641e62060,0x628106189b4dc49c49959a413511c,0x5084f3084f10e4f8065bd1f6238a] [0x83198844210b383a7255ff1dd1d3f7935aa2aa9ee880e8941b442108423348fca6c6d5e6789372ea1f1b85f1f2c92d000a43e2aa77083cc2e838d530ed8859c1d398f26c42be0184f9e0e3c9b10af8061410a02b75948922c1fca0abdc01610abdf90802c3157b885925ba27d4842d8884215b01a5541c9b2dd13eb84053,0x42b8802c1d4102211040308885917474fde4d621084211843244d1231145146512f31d33de69fc5bc550fe106983ad4] 0x91a7df4a1cee6d001738c8085c6b24100d9c4fd27be10aaa0cd6e937d858020212dd3c0b39fd8fc081006d3cf65dc3e65ac713527c3bcf62f14c7a0af56106732d8556e7e9e8c4d690ad019f5011402bec20008880430aa5b9175ad81088004031535e0a02b7eb5800aa00098000011bc500615f608a082f15b08030ea8041105144148115f58b1815739e01c0c790417c0e517f7131a3e0ddc98045fce65b700620b56d4e9aa0b644ad732ea7908b7f4ba186293f0111382b7b0baa009f478410900801c6821021b90104ea4d0a00410b1a48cf8d9f64e3da181f97778695320508338d5d8dc1d8a6ddaba28489fce64106315300b075d4ce369752855ebdb6c5a3c361058b1050c5c2141186d752462cf25f1acbfc60470b2058e83b819aa6cbe3646662b81ae6c4b99c0994647cc454ce223ec2c228334b195151f351945dfcc7022728734928149cb7933b6554ca240694eb5f07380a80c60345f4daae1b6b35449ee50b08dd6f01125217f2aa41c47511d9cdc168209f9759545ad3f15cf6df572745,w 0x1a14a62e7 [2103,2375] [625,112] [] [0x80a72150034d5c60b535f66bd3057d9ad6cd2904,0x54610388108101f083016decc48df6cca761239b4fa342100,0x1410425397ded06601dc2ea03b85ec841d685477b4a30,0x1a26c53562800c2f760cfdfa1ee0d8fb17d1010,0xed0e1a0780078f038c483df7cbf0a54e0021a3ef69b53aeff0a976b3290590b365a9a38c,0x90429428a28248214604b9827cc172211e,0xef774e75a0b9d682fbd99b59682ccdd5b33600300ab4a,0xda6b289b0926803864eb19938c6a4dd520,0x36514126524905944905944d1c,0x1efd207e8062810618d34164d34145edc,0x295a3b7b32347808196] 0xa6310178a0f0508b80bc9c8502428e0f401e7076109c9a47f084534378890301712f2040b020301 0x3d0990037a6082573fbd4101c1298440c26a4b9a28ab1a2012223c0c26bd45c7cc4b27100210a5d354108526061678ace0f7a0874f00006265041a600044db376a03cd6bf1e0ece6e8cc4516f564cc768a9823c3354057a08213eada01625eda205da104080c2281c20126014420056dd1c96a020298b0a80e5ebea80806255022f73cf427c01ac037eb12c9ea063c01371b3965122160614dc2183a3fa2d67e1002ce10000e0d84a5000049837b4746aa262428a9d65,u 0x2409c23f2 [0x4209010450415a608a082d2c10492504,0x78b35883f4f8b36941e3920f238c8470010670864,0x16411f680a116960931840e004201f0030c646e0c8,0x16612c134124740d53866d282cc11a28c2165c68,0x420fe427ebab674dd6d36861c2e930bd8f305608e158cb4018] [0x42260864bb2802f2d723967de10995108566b0845c02619f1108842e8f108c50d3f5bab8448621bf710cc980562c4118056228e18056237ed80562c08f8bc9c10c19bf6c198e0158e1a760cc700ac60cc79004c3,0x486088451] 0x41baa38c35f32dcf6ccf3ee3033c599e6bf926c025940cfdf0227af60650e7e0ac6106d471410b6ddf96952e31cf025cf3dd2b430c00114493038825d8d663ab004d0cec619ee4e87110422c0568e103a1f1ee928f61afe3929fb8b76780289e7ea2b3e1e9ef33235fbf037b8e00e59d5de945f80019dfb9efbb7133235f037ac019fd7dcc800c4cc8d7b3c3a4e777f0480067bcac7d688034990006b6f0a31e66646be1c64001a6646d60030840883882810,x 0x18068917e [0x834001067286414905658a482d2c524124c4,0x3d92284348fc85b08fd104ad931ec2990b411f86b21e40,0x5b2370a7082937b9807768cad9a8a3ab600f87d80bd5248,0xe58d9b8c6610] 0x9030842b0e91090e2004c18588c01308009056eb71090ec0fdd000b8401804068026101a8e005c407ef80d004c3 0x60449e3393800410d27c5aa7e892a50a705185f248a3676df9ac004109c88906f43095e08cf02102dc2291a4ef08ea38038b73fad454662202e246267d4a02f616d99d241c36aebb23eb9d42ec422e6f862020037ce21e3b3c41aed80841ccc3c7373f974bab0c08228361410,x 0x120629071 [0x12bb5037e14c95da41b800efddb989050450492004,0x1400bc4198331f61ec513769389a06467b42500,0x2966a830f66c3124601d81b927cea5ecc152d5a1f63e28,0x4bcc] 0x68c20c9c402588023115dc3c5e0e0661002f0ae111a5f29005880340251371121d83f73 0x158acecd061941c3d6be4cee0c7193182041a4d8b50a666dba2f3026f40759816db6be111d240c36d80237505a8380ac46678adecbe6168ab4196818dff32b1dc44624d3fa5760,x 0x120681676 [0x16fa6cc1db490cca72494647a0f3c89801798adac525c4,0x920ebcbb37014049075e647b303440e0042,0x4617869230bdd6b27124718fb251241a981b7558,0x9b56e4b876b2a34048b2] 0x2c100a62248b072f80523e78620d185fb7e003ca0c66086c842c0804c1 0x1891471711d4de8408385683234df14ccfc4e39dfb824060063040b46897500cf545b3c4a2ee55244ae91a282d55115555bd85c7ad,x 0xe04814e6 [0x1ac1af60e403affb41e400415c62b6b04125c4,0xf79afd47d58102460bd2c4d4a028ce53412f840e0042,0x14393c3b13c3393e46cc] 0x1086204110260a160740e205508448441 0xdcba518f0ba56cde1d3c56d50309d3f911c16bdb34cae97b5dc664d12b3ec9131148d34aab5849145,x 0xc04a06f6 [0xb060e4024d28c4f412790f2002092d4c10492504,0x7a28fb50107e736d29601d656501d41956cb7608,0x4620df4617b90d0] 0x10d8fb721e780200b84026080561 0x452ce984b8dbe452c8044ebdbcd7dbb0e30e115b2ef12af1829920b225cca9a2b555dcf1c1,x 0x4038835e [0x71c408403e407064263b2638d047e68c834016d92d8c92504,0x6e3119c36acbd86485ae530f728f7584be1804a] 0x856104c1 0x579ae9e1b1a7bdcdb5a5f3e78d27def9bca5ab5bb6f8d650fbdcc9a7890,x 0x402242de [0x14bf3162021edb9043509cdff656d04801819ad6cd2504,0x464c] 0x5719e01 0x13eda7a934d76b956feea8d631e6ddc8490,x 0x20262631 [0x15ed29601297f4d235269b2a1437b10610418b211c004d2104,0x7445bc4c] 0x551 0x1bbdba5e1e68c6d4e1aee7d62e5a56,u 0x270175 [0x248cf47dc93cbd882877b4454045c845cf97b210c00492104,0x870bc4c] [] 0x3ff7689431ef5a35d556d0,y 0x201e03f1 0x5b8d9830c019dec446a5c28237064210fc88700134120c4 0x7b731 0x2b72e47dcddc72d1f7be54,y 0x201221b1 0x65bc4c7a9888d4421f910e043890121c4 0x4a1 0x26a6d28d7ee6,z 0xe1971 0xfa322561e951e9b05c845e0021c4 0x129bfd9e0,z 0xc1cf2 0x264539c8665fa32e037b2644 0x1aebf1c0,z 0x801f0 0x7d191230decdc8 0x15180,z 0x82270 0x899894b09eca08 0x15180,z 0x850f1 0x26953208466002244 0x59980,z 0x70870 0xed30e4605c8 0x2960,z 0x70971 0x741445cc021c4 0x2960]
def d37:List CD:=[v 0x441c411f6 [2085] [80] [] [0x41045041596082282d2c104d24c4,0x4825ed043f6ea3ec1146411800edd0539830e24,0x5a1ec90c6886b1421989e8ca0aca58b1ecd424c0,0x4125f0c0253ae38010807c6ca6820ca00edc8,0x210c418738439a72d9e83b176eb0317688a0144f0,0x246a81b04d4601440d97b2073efde469a1b2454,0xfcfd0f61ec3d8428202692076aaa20d104794d54a58,0x90c63ec1d8a0030354c6da8fa14d1a514c10,0x6da9ac12d073ac89a551439c28ae115107689b8c,0x2a2c380058f028c4bbdd7f562fa585e4babc0043482b7f620af5d4ff522ab6977d5d48cbce7cad6,0x268229a08519753ff56a3f0539839cc152211e,0x45363636ffdefbc36f6d51c53375ef4dcd800c068214a,0x10ab2aa0d268349b0928803978d7a5d60,0x658bdfa018a0619595926d04da412575c,0x1872787627c] [0x5f7376f3c91bd03d8a085e607f11275c1a758bdb4e2eff0f0c9100b13d783ab3d03f8847c1d51fdc2dc211f00969e5f733bbc191c0b95d0e49833dc400b672888502101180562f34fde4fcd03f085c1c93c0206d232888562036c200904d3c09a78c45f9085b134f3804c2,0x2150442b8802210096237f07ee16083c842208844c01110844c2e80223109c2211b00444130856e89d5c1a21fdc2dc154543790afa9178307baedd96b79dceeb4ede421284d5442548471449e8f3d19d112dd1e71b12176044d71b2b446dfe354400e2a42d463d72a801b2dfef6f9a0bc06833dc02aa885793f179381b45,0x2a082e21] 0x2ac870716c203c35f5f45b6407738219e8c66033a702fc0496ea0f7071738641cc0f19c00769d4be1b3777632282282323610000089c914118f000029de1ecb77d3e4efb5d7d9013d8c0015bea3001255ae07d0e908500166ebf31a880206844304d75ddf1db4b21752082bfc8e7fd11c414614216038008a1b23a36cd0e2abcde3207f38b9fc5c86000062069a07001ebe9d0d621e6965c991719ac459a01973b4d61f6c12af9a7000bad748099040106858a2a30496081b450a38c0fa4f0e900777135b99c354a17c0db5091e142158e08a1b008e8ed60c6d579b90045602b13f81e4e2c86800a008229aa812fe0030e51b003981e33012f88f1245e17ecb1d5a4beaaf416075d8a1a5b0380a40e5c5b6bd2f9246a406dce8c640e6229103ce13fe027e0ac251bc1340fc32e07eef30f1606a2102c466bc5940010b49a60018610c0d00414f93c270549870059102045b5831b55c898c6486008860861972c4836d57c589b1e15a974220eb729f165ac3e5da5509e4b34e9fc8853a1c7ac536a8427020d81785c463ab54a05a0b01ca1b03004d53fd174821d825985afe0633945304b78a660028c64f56810339d62b867abc0e9b3f90602dd338a918c91e7089d00083174d8dc48cb2c8e5e97c2b1984a471c43e81f388ac673ae081c1d9f0b54f8a373d49,u 0x5011e26ff [0x95768bd3041555d82692cec10492904,0x282b0416f6e824049256182492cec5a5c4,0xc320704ed1f609134053ebaa238c7990300032a64,0x7a4ca1aea48ef70c4f1f73ec4defb62139b482345d00,0x75d75d3f6824a059041983b13c020210203e,0x190416615051bededb1b259d8254600b3724a,0x27d822ab000c69d27ce6982942935582ec1661daea8,0x7a28cb24919706fd147d8eb14104015cd34a98,0xe1d1f2ed4253cc3d3c3a53e427e841ba90d949185ee7181360d0] [0x8353dcf1ff42301f897deb756eae1090cf5a8026d8110b8dc2110c0285db6108b80d01a0340865dcf070bb4c2e8421a2dd5ba13fb8206a0d04e1642114c0ad2ac108b8105baa1a85e4e2086ac5681c9b9fd0f0d42085d4620b240842c17cb01b6b4082f0fe870ba8c217f05f2c082d4fe870aa4c0212042160be580db5a041767f45901ea88108582f96041707f4385d4617420dd150d42f27704326071ac273c5c68231097ce06aec17978804c0214300636,0x108d8206e00626a7bd7d061f3190e85e0e27042853debe20cbdec8b821932001743debe20cbdec8b82193f52006303411d09f220086bf8c801738a0b6773c0c425f3c210dbad6e88df2210d9f19002ed012108c468502ed929210d6a6842c9f3da10848164211882a84236005e6e783ed9292174210d5cf07f723013892ae1dad85fbea56821468682357a0242edb0858c0681c6b85e4ee0864c0681c6aabd0bc9dc10a180d038d6,0x435880d08512086c1086cc01288215842160421184211b040d2] 0x74ccd6a184bfcea1060422af018e0d360a1148aaa817eefa6c1400271565fc9fcbd3deac44eda0c31d424643a9be56adbd7f2f354940a762dd4288e3e848c8d7b2a18f4bae5a8e1e0c0847d2cf821e0c08ed1fc5b34715760beda08fad502eb7b1c17d6aa7343003010f7475efac311564e039eb7bbb6548fb8140ca0ed3852276bef0d057c0041ab2ed05555ad443b06dda0ababd9f17b8b82c9d8f80a9b77a3c710a63d57fc164ec7c051da7dd1592213b90714766e68aa90710540d283ccc85401d8a1aa8ee1088aaa9dd017d161868fb88d585401db2931b2c899c1540f46a4c66f59fba473e8c558f1fd9586fbe1a19bf505d2a811bd4db2cf2185b2d9e5cbcf00748b3492106793bae3d5571350fec7f03acdf524174a8e793c6527ec2a00fdf22c4017862f0c936071f4e2864e0cee767bac0803b8d49155d7d5136283f11feb37d49a1aa4e766526733b5b70132d0a71dcc5af1e430e7e9636eabd88e3a2e9eb9b2636b2ea3dbb3997f271308b9d9f90788f4f83ca00a058f0220389a34e2bef00bbc7b16cc97999b9d9067db53f083b644140140b18adefc1b25e6a92d13174f64a4025f0c9e6601862018d97b2589881178793b046adec2444536045e1e4ccecab116dafa0696d0f63b18e4f7f0a408ba99310c7ac10,u 0x280ae03f6 [0x539c39901049056d920b4b04124124c4,0x6e4520acadc9bb493a68a069edd511b6424012e64,0x1ad2c525f06f6804a75c7002100fad46900646e0c8,0x29677b006c12e7087e4d651b9edbe4d6b1d406cc868,0x3db64ce67a28fbd458e7e97b1050506a81b7558,0x61c9e1d09f2f7a0da39f2b59073ac82dc6cc] [0x20c5e20f70436669e70094469e7067850108d8022386a3db110856c198a9a79c42be0128c9cae30a7022210bc0210358614e004041085840d6272b859ec03099a79c2cfe0128fee1669e717978857dc0ca79004a834f3e5110ac70397b083ac0d1a1a79c42711a79c0261085b1,0x10ac442788847134f3859f2] 0x1265d663355f7e89fcb53d1a8d4838d7708e5b7b15b54667391067c107991c38a833a7761d0cd016ac8d4626ae3a025c69035c5a0e645c2339cdfcce24d6efd81a9e8aa36d1b376621a721042f3a6518d350ed816cf444992a1a5dceb5cb4de91871acfb90c02cefe8370e6fc590879359516c9131c49893dbf048f0e6ba2c8f7224947673dab8f28b608f3dd27cd971c44305141bca6891828a83845d27371935777409419d8d5626e40b508edd3228e53dde861ac7a0ec358eac0e0b6be6f3e4a79cf8600c9a65242,w 0x160f220f5 [1043] [] [] [0x3efdf7d04817001dbb06240412410412044,0xc68c3eaab6d1a4d01728391ca313c922500,0x128246c194107665b056cbdd7b4b942b7175950a3948,0xf7df6558fbf7df41040177d50612e97158,0xf1dcd6740d8837411454d6e8531561ec4c607b5d90,0x49d19053f3a8fcc5bc78c193dce7fab67ea3a76ed7e5ed8e4f46217729e5b6b51dcd6,0x6f10670d5a5b837eb6fcd9fdfb06782259ed49e9429af46,0x30c5030d282bf6d03600cd9c] 0x1e46043920f97ef7d7e4964ff5770cb89c61295689fa687d021f064834eb607e6d58d819d8b78022100bc21c9300bc40ff87dfa65ee8bdfa61030841e088421 0x154863d4d835c005760cc8a4e221212225ad5cf4566d94fca6215c7037edc8875d134c0f002ab24842a7da5841e0650400b6e628a5400858154b45405b55d8331788c35e8209880a562103c7834d47968ad8d99f821831200e3600b5b08b492f881be060063522255e6c8d4653da4c144010c9c04292d61666d5e2681500e414865010c9c04295d299365338411494de2112d214e3d3c144010c9c04115b2993e104588060c120e1365cc5af99aaaaa6f625,x 0x180672166 [0x15307920e000f60c189012415a68b5304d24c4,0x44f0c0253ae3881081e4208ee6c1c72a60cfb3e681c7221c0,0x5c2a8c05aa7433d1f7e4fda465ec4140bd982a2228,0x2e81f8ec4cc] 0x12c747a3a3dd0785a3dd0b05a3dd49b812cf47ba1089743a16496ec4945e1add8928bcc73e802507840561d1e60562 0x19216b3930bf0a9009bc312018df964916276038db976210e01c4f4d1638e502bcb8066364c2180869219f1e60308401c669159a91b215716a1ab520c2bbf098c511283b21ac5b2a1b5f8c483fbcbb6b4105658f9864edc831109149418619ee9c2822a92,x 0x1c08012f6 [0x1049e1ac8190900032e24256982092d4c10492504,0x4d841956c81c008569b6e4100934f0b425c0,0x454040959cb9b694b00a209b082caddf5019a6c,0x28427c4dcb73e1270db53599da089e439d642aaac6cc2712455c10] 0x1710804b100583f1401611a09113c020d6f00945200964243f0094410d700a8400b87410e0ea88026080561 0x307a7608b295fa015405aafbe0eda53157d550168aea45833870960d05aa42903cc1cf60f4ed757012718210255b575c3c234837e13d210980c09788ab7802a80ac927156c21a9320fa005b08284308508d00180aa000aaabacd0225,x 0x1004252df [0x35994e6ffb2b68240009af4d7d826b5304d2904,0x24c652fc92c68a8084aaa4ad6153841e02420407c16f2086a500,0x284a7c] 0x62275636f42b76acf3ab39ea1c0b0b05283d20581 0x98aa78e0e4b0a658ac71e9cd31a736967e36d9c9598ab5be9345557e6a9345e765673a4d141071994cb148e57449910,x 0xe05460ce [0x6f64643091f9441460f9070002682d2c134124c4,0xe57e860817bd4695b009a0c20a02683085854ea48,0x42a5bb2a45ac26d0362c8d8d66e33c19fb5190] 0x1c9108c42c109046018b042e1 0x617d7844200007c9410b04ea15f6e0b677904eab22482cdd93c78415a365cd551155ccd155,x 0x80441265 [0x1ee3e9eb6921149fe97b20e40743dc9890124120c4,0x73c5298db33184e248e3f494c902f7aae93918,0xdc6cc] 0xd0388150409420221 0x4207599bca8c985b000c27640d28cd4cd1d912c563c905b99d0d5a2aaa95d9,x 0x802e2165 [0x8a8287fb40140790823bda10fcb982423810e240492104,0x3ac80b8551a30c6050] 0x290a284415c290cc662604b1 0x1344adba614b2aa377cde546f6f7fcf677359bd42b655abbccd0,x 0x802c19e2 [0x7aac0d662d5c865e7f0be5078e43c800cb8918182dcc125c4,0x20df461233457a14] 0xd058813056eb71487640b4487e04c2 0xbf954f55de6dcee8b2eb73e5092aaf9be132ca1a0,x 0x20280270 [0xa2c6daba0de98c6c03b7bb820a1216cd1a4b548c822600,0x246aec559b0c] 0x5a671 0x2428dbd3388bacd4e3eeedaf79595d,x 0xe02416f2 [0x22460904199142410664b320805997e0a32e037b2644,0x3e8c9918] 0x1e6ac41cd0c3fa1290a2522041d50872e1 0xb23ee876a2cb7895d5eb99a6f1dd51f7a414,z 0x174075 0x1c1a48c2f724a0dec2984105ed14300d2104 0x9f30cb52cd0,y 0x201211a9 0x12f30ef624f520c8424f9126049891520c4 0x231 0x1da51a7da7f66,z 0xe0971 0xfa322561e951e9b05c845e0021c4 0x129bfd9e0,z 0xe22f1 0xe0d3464d2a502804d2104 0x175fdae0,z 0xc29f2 0x2c46a44b6210e037b2604 0x7caf1c0,z 0x82470 0x8d98f4b0dec208 0x15180,z 0x85271 0x12e51a48452402104 0x59980,z 0x642f1 0x8514421002204 0x2960,z 0x78171 0x741445cc021c4 0x2960]
theorem b00:Q G0 d00:=by decide +kernel
theorem b01:Q G0 d01:=by decide +kernel
theorem b02:Q G0 d02:=by decide +kernel
theorem b03:Q G0 d03:=by decide +kernel
theorem b04:Q G0 d04:=by decide +kernel
theorem b10:Q G1 d10:=by decide +kernel
theorem b11:Q G1 d11:=by decide +kernel
theorem b12:Q G1 d12:=by decide +kernel
theorem b13:Q G1 d13:=by decide +kernel
theorem b20:Q G2 d20:=by decide +kernel
theorem b21:Q G2 d21:=by decide +kernel
theorem b22:Q G2 d22:=by decide +kernel
theorem b23:Q G2 d23:=by decide +kernel
theorem b24:Q G2 d24:=by decide +kernel
theorem b30:Q G3 d30:=by decide +kernel
theorem b31:Q G3 d31:=by decide +kernel
theorem b32:Q G3 d32:=by decide +kernel
theorem b33:Q G3 d33:=by decide +kernel
theorem b34:Q G3 d34:=by decide +kernel
theorem b35:Q G3 d35:=by decide +kernel
theorem b36:Q G3 d36:=by decide +kernel
theorem b37:Q G3 d37:=by decide +kernel
theorem c0_ok:coverOk G0 ((d00++d01++d02++d03++d04).map cdKey)=true:=by decide +kernel
theorem c1_ok:coverOk G1 ((d10++d11++d12++d13).map cdKey)=true:=by decide +kernel
theorem c2_ok:coverOk G2 ((d20++d21++d22++d23++d24).map cdKey)=true:=by decide +kernel
theorem c3_ok:coverOk G3 ((d30++d31++d32++d33++d34++d35++d36++d37).map cdKey)=true:=by decide +kernel
lemma g0_ok:TLB G0:=main_of_coverOk G0 _ c0_ok fun e he=>by simp only[List.map_append,List.mem_append] at he;rcases he with ((((h|h)|h)|h)|h);{exact chkL_sound b00 e h};{exact chkL_sound b01 e h};{exact chkL_sound b02 e h};{exact chkL_sound b03 e h};{exact chkL_sound b04 e h}
lemma g1_ok:TLB G1:=main_of_coverOk G1 _ c1_ok fun e he=>by simp only[List.map_append,List.mem_append] at he;rcases he with (((h|h)|h)|h);{exact chkL_sound b10 e h};{exact chkL_sound b11 e h};{exact chkL_sound b12 e h};{exact chkL_sound b13 e h}
lemma g2_ok:TLB G2:=main_of_coverOk G2 _ c2_ok fun e he=>by simp only[List.map_append,List.mem_append] at he;rcases he with ((((h|h)|h)|h)|h);{exact chkL_sound b20 e h};{exact chkL_sound b21 e h};{exact chkL_sound b22 e h};{exact chkL_sound b23 e h};{exact chkL_sound b24 e h}
lemma g3_ok:TLB G3:=main_of_coverOk G3 _ c3_ok fun e he=>by simp only[List.map_append,List.mem_append] at he;rcases he with (((((((h|h)|h)|h)|h)|h)|h)|h);{exact chkL_sound b30 e h};{exact chkL_sound b31 e h};{exact chkL_sound b32 e h};{exact chkL_sound b33 e h};{exact chkL_sound b34 e h};{exact chkL_sound b35 e h};{exact chkL_sound b36 e h};{exact chkL_sound b37 e h}
end DS
lemma all4_lb:∀(v:Fin 11)(C:Circuit),v.val<4->Monotone2 C->C.size<=18->∃x:Fin 10->Bool,C.eval (List.ofFn x)≠graphFun (edgeGraph 11 g11Edges) ∅ (v.insertNth Bool.false x):=g11_lb_of_all4 fun gi=>by fin_cases gi;{exact DS.g0_ok};{exact DS.g1_ok};{exact DS.g2_ok};{exact DS.g3_ok}
end DataSec
namespace W
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
def wC:List Nat:=[9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97]
def wV (y:Fin 11->Bool):Bool:=wC.any λ t=>y (Fin.ofNat 11 (t/11))&&y (Fin.ofNat 11 (t % 11))
def wP:List (Fin 11×Fin 11):=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
lemma wAj:∀a b:Fin 11,(edgeGraph 11 g11Edges).Adj a b↔(a,b)∈wP\/(b,a)∈wP:=by decide +kernel
lemma wF (y:Fin 11->Bool):graphFun (edgeGraph 11 g11Edges) ∅ y=wV y:=by
  have h:graphFun (edgeGraph 11 g11Edges) ∅ y=wP.any (λ e=>y e.1&&y e.2):=by
    apply Bool.eq_iff_iff.mpr;delta graphFun
    simp only[Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
    constructor
    · rintro⟨a,b,hab,ha,hb⟩;rcases (wAj a b).mp hab with h|h;{exact⟨(a,b),h,ha,hb⟩};{exact⟨(b,a),h,hb,ha⟩}
    · rintro⟨⟨a,b⟩,h,ha,hb⟩;exact⟨a,b,(wAj a b).mpr (Or.inl h),ha,hb⟩
  exact h.trans rfl
end W

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PreparedCircuit.Reindex

def wire {n m : ℕ} (σ : Fin n → Fin m) (i : ℕ) : ℕ :=
  if hi : i < n then (σ ⟨i, hi⟩).val else m + (i - n)

def gate {n m : ℕ} (σ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire σ)⟩

def circuit {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate σ), wire σ C.output⟩

theorem size_eq {n m} (σ : Fin n → Fin m) (C : Circuit) : (circuit σ C).size = C.size := by
  simp [circuit, Circuit.size]

theorem readWire {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gates : List Bool) (i : ℕ) :
    (List.ofFn x ++ gates).getD (wire σ i) false =
      (List.ofFn (fun j => x (σ j)) ++ gates).getD i false := by
  by_cases hi : i < n
  · let j := σ ⟨i, hi⟩
    have left : j.val < (List.ofFn x).length := by simp
    have right : i < (List.ofFn (fun k => x (σ k))).length := by simpa using hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append _ _ _ _ left, List.getD_append _ _ _ _ right]
    simp [List.getD_eq_getElem?_getD, hi, j]
  · have left : (List.ofFn x).length ≤ m + (i - n) := by simp
    have right : (List.ofFn (fun k => x (σ k))).length ≤ i := by simpa using Nat.le_of_not_gt hi
    simp only [wire, hi, ↓reduceDIte]
    rw [List.getD_append_right _ _ _ _ left, List.getD_append_right _ _ _ _ right]
    simp

private def appendValue (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldGates {n m} (σ : Fin n → Fin m) (x : Fin m → Bool) (gs : List Gate)
    (priorValues : List Bool) : ∃ suffix : List Bool,
      (gs.map (gate σ)).foldl appendValue (List.ofFn x ++ priorValues) = List.ofFn x ++ suffix ∧
      gs.foldl appendValue (List.ofFn (fun j => x (σ j)) ++ priorValues) = List.ofFn (fun j => x (σ j)) ++ suffix := by
  induction gs generalizing priorValues with
  | nil => exact ⟨priorValues, rfl, rfl⟩
  | cons g gs ih =>
    let w := List.ofFn (fun j => x (σ j)) ++ priorValues
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have inputs : (gate σ g).inputs.map (fun i => (List.ofFn x ++ priorValues).getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      simp only [gate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact readWire σ x priorValues i
    have left : appendValue (List.ofFn x ++ priorValues) (gate σ g) = List.ofFn x ++ (priorValues ++ [v]) := by
      unfold appendValue
      rw [inputs]
      exact List.append_assoc _ _ _
    have right : appendValue w g = List.ofFn (fun j => x (σ j)) ++ (priorValues ++ [v]) :=
      List.append_assoc _ _ _
    obtain ⟨suffix, hl, hr⟩ := ih (priorValues ++ [v])
    refine ⟨suffix, ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons, left]
      exact hl
    · change gs.foldl appendValue (appendValue w g) = _
      rw [right]
      exact hr

theorem reindexed_wires {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    ∃ tail, (circuit σ C).wires (List.ofFn x) = List.ofFn x ++ tail ∧
      C.wires (List.ofFn fun j => x (σ j)) = (List.ofFn fun j => x (σ j)) ++ tail := by
  obtain ⟨tail, left, right⟩ := foldGates σ x C.gates []
  refine ⟨tail, ?_, ?_⟩
  · change (C.gates.map (gate σ)).foldl appendValue (List.ofFn x) = _
    simpa only [List.append_nil] using left
  · change C.gates.foldl appendValue (List.ofFn fun j => x (σ j)) = _
    simpa only [List.append_nil] using right

theorem eval_with_tail {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) (tail : List Bool) :
    (circuit σ C).eval (List.ofFn x ++ tail) = C.eval ((List.ofFn fun j => x (σ j)) ++ tail) := by
  obtain ⟨suffix, left, right⟩ := foldGates σ x C.gates tail
  change ((C.gates.map (gate σ)).foldl appendValue (List.ofFn x ++ tail)).getD (wire σ C.output) false =
    (C.gates.foldl appendValue ((List.ofFn fun j => x (σ j)) ++ tail)).getD C.output false
  rw [left, right]
  exact readWire σ x suffix C.output

end PreparedCircuit.Reindex

namespace PriorG11.Join

def append (P T : Circuit) : Circuit := ⟨P.gates ++ T.gates, T.output⟩

theorem append_size (P T : Circuit) : (append P T).size = P.size + T.size := by
  simp [append, Circuit.size]

theorem append_eval (P T : Circuit) (x : List Bool) :
    (append P T).eval x = T.eval (P.wires x) := by
  simp [append, Circuit.eval, Circuit.wires, List.foldl_append]

end PriorG11.Join

namespace PriorG11.Splice
open PEqualNP.TopForm PreparedCircuit.Reindex

def op (conj : Bool) : GateOp := if conj then .and else .or

def combine (conj left right : Bool) : Bool :=
  if conj then left && right else left || right

theorem op_eval (conj a b : Bool) : (op conj).eval [a,b] = combine conj a b := by
  cases conj <;> simp [op, combine, GateOp.eval]

def root (size : ℕ) (conj : Bool) (a b : ℕ) : Circuit := ⟨[⟨op conj,[a,b]⟩],size⟩

theorem append_wires (P T : Circuit) (w : List Bool) :
    (Join.append P T).wires w = T.wires (P.wires w) := by
  simp only [Join.append, Circuit.wires, List.foldl_append]

def assembled {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) : Circuit :=
  let lifted := circuit p.succAbove P
  let test := root (n+1+P.size) conj p.val (wire p.succAbove P.output)
  Join.append (Join.append lifted test) (circuit p.succAbove T)

theorem assembled_size {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) :
    (assembled p P T conj).size = P.size + 1 + T.size := by
  simp only [assembled, Join.append_size, size_eq]
  rfl

theorem assembled_eval {n : ℕ} (p : Fin (n+1)) (P T : Circuit) (conj : Bool) (y : Fin (n+1) → Bool) :
    (assembled p P T conj).eval (List.ofFn y) =
      T.eval (P.wires (List.ofFn fun j => y (p.succAbove j)) ++
        [combine conj (y p) (P.eval (List.ofFn fun j => y (p.succAbove j)))]) := by
  let x := fun j => y (p.succAbove j)
  obtain ⟨tail,large,small⟩ := reindexed_wires p.succAbove P y
  have left : (List.ofFn y ++ tail).getD p.val false = y p := by
    rw [List.getD_append _ _ _ _ (by simpa using p.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt, ↓reduceDIte, Option.getD_some]
  have right : (List.ofFn y ++ tail).getD (wire p.succAbove P.output) false = P.eval (List.ofFn x) := by
    change _ = (P.wires (List.ofFn x)).getD P.output false
    rw [small]
    exact readWire p.succAbove y tail P.output
  let value := combine conj (y p) (P.eval (List.ofFn x))
  have test : (root (n+1+P.size) conj p.val (wire p.succAbove P.output)).wires (List.ofFn y ++ tail) =
      (List.ofFn y ++ tail) ++ [value] := by
    change (List.ofFn y ++ tail) ++ [(op conj).eval [(List.ofFn y ++ tail).getD p.val false,
      (List.ofFn y ++ tail).getD (wire p.succAbove P.output) false]] = _
    rw [left, right, op_eval]
  rw [assembled, Join.append_eval, append_wires, large, test, List.append_assoc,
      eval_with_tail, ← List.append_assoc, ← small]

theorem monoMap {n m N} (σ : Fin n → Fin m) {C : Circuit} (ok : IsAO2 N C) :
    Monotone2 (circuit σ C) := by
  intro g hg
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
  constructor
  · simpa [gate] using ok.1 k hk
  · simp [gate,ok.2.2 k hk]

theorem mono {n} (p : Fin (n+1)) {P T : Circuit} (hp : IsAO2 n P) (ht : IsAO2 (n+1+P.size) T) :
    Monotone2 (assembled p P T false) := by
  intro g hg
  simp only [assembled,Join.append,root,List.mem_append,List.mem_singleton] at hg
  rcases hg with (h|rfl)|h
  · exact monoMap _ hp _ h
  · simp [op]
  · exact monoMap _ ht _ h
end PriorG11.Splice
end PEqualNP.Outside.L_meta_18015_aux
open PEqualNP.Outside.L_meta_18015_aux PEqualNP.Outside.L_meta_18015_aux.PriorG11.Splice in
theorem PEqualNP.Outside.L_meta_18015 : (∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →       PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →         x3.size + x4.size ≤ (17 : ℕ) →           (9 : ℕ) ≤ x3.output →             x3.output < (9 : ℕ) + x3.size →               have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>                 have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));               (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) → ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13)) := by
  intro v p P T hv hp ht room _ _ target _
  by_contra! agrees
  let C := assembled p P T false
  have hs : C.size ≤ 18 := by change (assembled p P T false).size ≤ 18; rw [assembled_size]; omega
  obtain ⟨y,hy⟩ := all4_lb v C hv (mono p hp ht) hs
  apply hy
  rw [W.wF,show C = assembled p P T false from rfl,assembled_eval]
  have recover : p.insertNth (y p) (fun j => y (p.succAbove j)) = y := Fin.insertNth_eq_iff.mpr ⟨rfl,rfl⟩
  simpa only [recover,target,W.wV,W.wC,combine,Bool.false_eq_true,ite_false] using agrees (fun j => y (p.succAbove j)) (y p)
