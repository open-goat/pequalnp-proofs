import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39695_aux

abbrev M := BitVec 55
abbrev Wire := M × M
namespace Wire
def zero : Wire := ⟨0,0⟩
def flip (u : Wire) : Wire := ⟨~~~u.1, ~~~u.2⟩
def meet (u v : Wire) : Wire := ⟨u.1 &&& v.1,u.2 &&& v.2⟩
def join (u v : Wire) : Wire := ⟨u.1 ||| v.1,u.2 ||| v.2⟩
def diff (u v : Wire) : Wire := meet u (flip v)
def ops (u v : Wire) := [meet u v,join u v,diff u v,diff v u]
def sig (u : Wire) := u.1 ^^^ u.2
def hit (u : Wire) := u.sig = (BitVec.allOnes 55)
def separates (u : Wire) (i : Fin 55) := u.1[i.val] ≠ u.2[i.val]
end Wire
open Wire

def allSig : List Wire → M
  | [] => 0
  | w::ws => w.sig ||| allSig ws

theorem allSig_bit (ws : List Wire) (i : Fin 55) :
    (allSig ws)[i.val] = true ↔ ∃ w ∈ ws, separates w i := by
  induction ws with
  | nil => simp [allSig]
  | cons u us ih =>
    simp [allSig, sig, separates] at ih ⊢
    exact or_congr_right ih

theorem hit_iff (u : Wire) : hit u ↔ ∀i : Fin 55, separates u i := by
  change u.sig = (BitVec.allOnes 55) ↔ _
  constructor
  · intro h i
    have hb : u.sig[i.val] = true := by rw [h]; exact BitVec.getElem_allOnes i.val i.isLt
    simpa [Wire.sig,Wire.separates] using hb
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hx := h ⟨i,hi⟩
    rw [BitVec.getElem_allOnes]
    simpa [Wire.sig,Wire.separates] using hx

theorem adequate (ws : List Wire) (h : ∀i : Fin 55, ∃ w ∈ws, separates w i) :
    allSig ws = (BitVec.allOnes 55) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_allOnes]
  exact (allSig_bit ws ⟨i,hi⟩).mpr (h _)

theorem sep_parent {a b c : Wire} (op : c∈ops a b) {i : Fin 55} (hs : separates c i) :
    separates a i ∨ separates b i := by
  by_contra! h
  simp [ops] at op
  rcases op with rfl|rfl|rfl|rfl <;>
    simp_all [separates,meet,join,diff,Wire.flip]

def Plan : ℕ → Finset Wire → Prop
  | 0, S => ∃ t : Wire, hit t ∧ S={t}
  | k+1, S => ∃ T a b c, Plan k T ∧ c∈T ∧ c∈ops a b ∧ c≠a ∧ c≠b ∧ c≠zero ∧ S=insert a (insert b (T.erase c))

theorem Plan.endAt (t : Wire) (yes : hit t) : Plan 0 {t} := ⟨t,yes,rfl⟩
theorem Plan.add {k T} (p : Plan k T) {a b c} (used : c∈T) (op : c∈ops a b) (fa : c≠a) (fb : c≠b) (nz : c≠zero) :
    Plan (k+1) (insert a (insert b (T.erase c))) := ⟨T,a,b,c,p,used,op,fa,fb,nz,rfl⟩

theorem Plan.byGates {C : (k : ℕ) → (S : Finset Wire) → Plan k S → Prop}
    (endAt : ∀(t : Wire) (h : hit t), C 0 {t} (Plan.endAt t h))
    (add : ∀{k T} (q : Plan k T) {a b c} (hu : c∈T) (ho : c∈ops a b) (fa : c≠a) (fb : c≠b) (nz : c≠zero),
      C k T q → C (k+1) (insert a (insert b (T.erase c))) (Plan.add q hu ho fa fb nz))
    {k S} (p : Plan k S) : C k S p := by
  induction k generalizing S with
  | zero => obtain ⟨t,h,rfl⟩ := p; exact endAt t h
  | succ k ih =>
    obtain ⟨T,a,b,c,q,h,op,fa,fb,nz,rfl⟩ := p
    exact add q h op fa fb nz (ih q)

theorem Plan.cardBound {k S} (p : Plan k S) : S.card ≤ k+1 := by
  induction p using Plan.byGates with
  | endAt => simp
  | @add k T _ a b c used op _ _ _ ih =>
    have h1 := Finset.card_insert_le a (insert b (T.erase c))
    have h2 := Finset.card_insert_le b (T.erase c)
    rw [Finset.card_erase_of_mem used] at h2
    have := Finset.card_pos.mpr ⟨c,used⟩
    omega

theorem Plan.cover {k S} (p : Plan k S) (i : Fin 55) : ∃ w∈S, separates w i := by
  induction p using Plan.byGates with
  | endAt t h => exact ⟨t,by simp,(hit_iff _).mp h i⟩
  | @add k T _ a b c used op _ _ _ ih =>
    obtain ⟨w,hw,sep⟩ := ih
    by_cases eq : w=c
    · subst w
      rcases sep_parent op sep with hs|hs
      · exact ⟨a,by simp,hs⟩
      · exact ⟨b,by simp,hs⟩
    · exact ⟨w,by simp [Finset.mem_erase,hw,eq],sep⟩

open Wire

def pairs : List Wire → List (Wire × Wire)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ pairs xs

def drops (xs : List Wire) (a b : Wire) : List (List Wire) :=
  [xs,xs.filter (· != a),xs.filter (· != b),xs.filter (fun w=>w != a && w != b)]

def seek : ℕ → List Wire → Bool
  | 0, xs => xs.any (fun w => w.sig == (BitVec.allOnes 55))
  | k+1, xs =>
    xs.length ≤ k+2 && allSig xs == (BitVec.allOnes 55) &&
    (xs.any (fun w => w.sig == (BitVec.allOnes 55)) ||
      (pairs xs).any fun (a,b) => (ops a b).any fun c =>
        c != zero && !xs.contains c &&
        (drops xs a b).any fun keep => seek k (c::keep))
def pins : List Wire := [⟨0x7ffbc7fd007fff#55,0x4000000000003a#55⟩,⟨0x3ffdf8e2ff8e07#55,0x38000001f8e04#55⟩,⟨0xedb276bb248#55,0x2c90000361b240#55⟩,⟨0x400f6d4bb6d490#55,0x75200003a65480#55⟩,⟨0xfb693dd6920#55,0x3a400003d86900#55⟩,⟨0x7fffffffffffff#55,0x3fffffffffffff#55⟩]

def probes : List (Nat × Nat) := [(35, 32), (35, 33), (35, 34), (37, 33), (41, 33), (49, 33), (37, 36), (41, 40), (49, 48), (39, 38), (43, 42), (51, 50), (45, 44), (53, 52), (57, 56), (46, 38), (54, 38), (46, 42), (58, 42), (54, 50), (58, 50), (46, 44), (54, 52), (58, 56), (61, 60), (62, 60), (37, 32), (41, 32), (49, 32), (39, 32), (43, 32), (51, 32), (45, 32), (53, 32), (57, 32), (46, 32), (54, 32), (58, 32), (47, 32), (55, 32), (59, 32), (61, 32), (62, 32), (63, 32), (35, 36), (35, 40), (35, 48), (35, 38), (35, 42), (35, 50), (35, 44), (35, 52), (35, 56), (35, 60), (41, 9)]

def row (k : ℕ) (i : Fin 6) : Bool := k.testBit i.val

def probeP (j : Fin 55) : Fin 6 → Bool := row (probes.getD j.val (0,0)).1
def probeN (j : Fin 55) : Fin 6 → Bool := row (probes.getD j.val (0,0)).2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372904 * 2^32 + 3941132456) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)

def monoEleven : Circuit :=
  ⟨[⟨.or,[2,5]⟩,⟨.and,[3,4]⟩,⟨.or,[2,7]⟩,⟨.and,[1,8]⟩,⟨.or,[0,9]⟩,⟨.and,[6,10]⟩,⟨.or,[3,4]⟩,⟨.or,[1,8]⟩,⟨.and,[0,13]⟩,⟨.and,[11,12]⟩,⟨.or,[14,15]⟩],16⟩

theorem elevenMono : Monotone2 monoEleven := by
  intro g hg
  simp [monoEleven] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem elevenSize : monoEleven.size = 11 := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem elevenEval : ∀ x : Fin 6 → Bool, monoEleven.eval (List.ofFn x) = target x := by decide +kernel
open Wire

def phase (w a : Wire) := w=a ∨ w=a.flip
def known (pool : Finset Wire) (w : Wire) := phase w zero ∨ ∃a∈pool, phase w a
def hasPlan (pool : Finset Wire) (bound : ℕ) := ∃k ≤ bound, ∃S⊆pool, Plan k S

@[simp] theorem flipFlip (a : Wire) : a.flip.flip = a := by cases a; simp [Wire.flip]
theorem known_flip {S a} (h : known S a) : known S a.flip := by
  have sw {u v : Wire} (h : phase u v) : phase u.flip v := by
    rcases h with rfl|rfl
    · exact Or.inr rfl
    · exact Or.inl (flipFlip _)
  exact h.elim (fun c=>Or.inl (sw c)) (fun ⟨u,hu,ph⟩=> Or.inr ⟨u,hu,sw ph⟩)
theorem known_mono {S T : Finset Wire} (sub : S⊆T) {a} (h : known S a) : known T a :=
  h.elim Or.inl (fun ⟨v,hv,hh⟩=>Or.inr ⟨v,sub hv,hh⟩)
theorem zeroKnown {S} : known S zero := Or.inl (Or.inl rfl)

theorem meet_zero (u : Wire) : meet zero u = zero := by cases u; simp [meet,zero]
theorem meet_top (u : Wire) : meet zero.flip u = u := by cases u; unfold meet zero Wire.flip; congr 1 <;> exact BitVec.allOnes_and
theorem meet_comm (u v : Wire) : meet u v = meet v u := by simp [meet,BitVec.and_comm]
theorem join_flips (u v : Wire) : join u v = (meet u.flip v.flip).flip := by
  cases u; cases v; simp [meet,join,Wire.flip,BitVec.not_and]

def newGate (pool : Finset Wire) (z : Wire) :=
  ∃ a∈pool, ∃ b∈pool, ∃ c∈ops a b, phase z c

theorem meet_options {pool : Finset Wire} {u v : Wire} (hu : known pool u) (hv : known pool v) :
    known pool (meet u v) ∨ newGate pool (meet u v) := by
  rcases hu with (rfl|rfl)|⟨a,ha,hpa⟩
  · rw [meet_zero]; exact Or.inl zeroKnown
  · rw [meet_top]; exact Or.inl hv
  rcases hv with (rfl|rfl)|⟨b,hb,hpb⟩
  · rw [meet_comm,meet_zero]; exact Or.inl zeroKnown
  · rw [meet_comm,meet_top]; exact Or.inl (Or.inr ⟨a,ha,hpa⟩)
  right; refine ⟨a,ha,b,hb,?_⟩
  rcases hpa with rfl|rfl <;> rcases hpb with rfl|rfl
  · exact ⟨meet _ _,by simp [ops],Or.inl rfl⟩
  · exact ⟨diff _ _,by simp [ops],Or.inl rfl⟩
  · exact ⟨diff _ _,by simp [ops],Or.inl (meet_comm _ _)⟩
  · refine ⟨join a b,by simp [ops],Or.inr ?_⟩
    rw [join_flips,flipFlip]

theorem join_options {pool : Finset Wire} {u v : Wire} (hu : known pool u) (hv : known pool v) :
    known pool (join u v) ∨ newGate pool (join u v) := by
  rw [join_flips]
  rcases meet_options (known_flip hu) (known_flip hv) with h|⟨a,ha,b,hb,c,hc,ph⟩
  · exact Or.inl (known_flip h)
  · right; refine ⟨a,ha,b,hb,c,hc,?_⟩
    rcases ph with h|h
    · exact Or.inr (congrArg Wire.flip h)
    · exact Or.inl (by rw [h,flipFlip])

theorem contract {pool : Finset Wire} {k : ℕ} {z : Wire} (hz : ¬known pool z)
    {a b c : Wire} (ha : a ∈pool) (hb : b ∈pool) (op : c∈ops a b) (ph : phase z c)
    (later : hasPlan (insert c pool) k) : hasPlan pool (k+1) := by
  have nc : c∉pool := fun h=>hz (Or.inr ⟨c,h,ph⟩)
  have nz : c ≠ zero := by rintro rfl; exact hz (Or.inl ph)
  obtain ⟨m,mb,S,sub,p⟩ := later
  by_cases mem : c∈S
  · refine ⟨m+1,by omega,_,?_,Plan.add p mem op (by rintro rfl; exact nc ha)
      (by rintro rfl; exact nc hb) nz⟩
    intro x h
    simp only [Finset.mem_insert,Finset.mem_erase] at h
    rcases h with rfl|rfl|⟨ne,hx⟩
    · exact ha
    · exact hb
    · exact (Finset.mem_insert.mp (sub hx)).resolve_left ne
  · exact ⟨m,by omega,S,fun x hx=>(Finset.mem_insert.mp (sub hx)).resolve_left (by rintro rfl; exact mem hx),p⟩
open Wire PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def legal (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2
def cost (g : Gate) : ℕ := match g.op with | .and | .or => 1 | _ => 0
def count (gs : List Gate) := (gs.map cost).sum

def wordGate (gs : List Wire) (g : Gate) : Wire :=
  match g.inputs,g.op with
  | [],.or => zero
  | [],_ => zero.flip
  | i::_,.not => (gs.getD i zero).flip
  | [i],_ => gs.getD i zero
  | i::j::_,.and => meet (gs.getD i zero) (gs.getD j zero)
  | i::j::_,_ => join (gs.getD i zero) (gs.getD j zero)

def wordRun (gs : List Gate) (ws : List Wire) :=
  gs.foldl (fun acc g=>acc++[wordGate acc g]) ws

def side (neg : Bool) (i : Fin 55) (w : Wire) : Bool :=
  if neg then w.2[i.val] else w.1[i.val]

theorem known_at {pool : Finset Wire} {ws : List Wire} (hk : ∀w∈ws,known pool w) (i : ℕ) :
    known pool (ws.getD i zero) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]; exact hk _ (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (by omega)]; exact zeroKnown

theorem gate_options {pool : Finset Wire} {ws : List Wire} (hk : ∀w∈ws,known pool w)
    {g : Gate} (hg : legal g) : known pool (wordGate ws g) ∨ (cost g = 1 ∧ newGate pool (wordGate ws g)) := by
  rcases g with ⟨o,ins⟩
  obtain ⟨ho,hlen⟩ := hg
  change o = .and ∨ o = .or ∨ o = .not at ho
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases ho with rfl|rfl|rfl <;> first | exact Or.inl (known_flip zeroKnown) | exact Or.inl zeroKnown
  | cons i tail =>
    cases tail with
    | nil =>
      rcases ho with rfl|rfl|rfl <;> first | exact Or.inl (known_at hk i) | exact Or.inl (known_flip (known_at hk i))
    | cons j tail =>
      rcases ho with rfl|rfl|rfl
      · exact (meet_options (known_at hk i) (known_at hk j)).imp_right (fun h=>⟨rfl,h⟩)
      · exact (join_options (known_at hk i) (known_at hk j)).imp_right (fun h=>⟨rfl,h⟩)
      · exact Or.inl (known_flip (known_at hk i))

theorem sideGate (n : Bool) (i : Fin 55) (ws : List Wire) {g : Gate} (hg : legal g) :
    side n i (wordGate ws g) = g.op.eval (g.inputs.map fun j=>(ws.map (side n i)).getD j false) := by
  have hzero : side n i zero = false := by cases n <;> simp [side,zero]
  have atI (j : ℕ) : (ws.map (side n i)).getD j false = side n i (ws.getD j zero) := by
    rw [←hzero]; exact List.getD_map _ _ _
  simp only [atI]
  rcases g with ⟨o,ins⟩
  obtain ⟨ho,hlen⟩ := hg
  change o = .and ∨ o = .or ∨ o = .not at ho
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,zero,Wire.flip,GateOp.eval] <;> exact BitVec.getElem_allOnes i.val i.isLt
  | cons a l =>
    cases l with
    | nil =>
      rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,Wire.flip,GateOp.eval]
    | cons b t =>
      have : t=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst t
      rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,Wire.flip,meet,join,GateOp.eval]

theorem sideRun (n : Bool) (i : Fin 55) (gs : List Gate) (ws : List Wire) (leg : ∀g∈gs,legal g) :
    (wordRun gs ws).map (side n i) =
    gs.foldl (fun v g=>v++[g.op.eval (g.inputs.map fun j=>v.getD j false)]) (ws.map (side n i)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (wordRun gs (ws++[wordGate ws g])).map _ = _
    rw [ih _ (fun h hh=>leg h (by simp [hh]))]
    simp [sideGate n i ws (leg g (by simp))]

theorem fromRun (gs : List Gate) (pool : Finset Wire) (ws : List Wire) (out : ℕ)
    (hk : ∀w∈ws,known pool w) (leg : ∀g∈gs,legal g)
    (hwin : hit ((wordRun gs ws).getD out zero)) : hasPlan pool (count gs) := by
  induction gs generalizing pool ws with
  | nil =>
    change hit (ws.getD out zero) at hwin
    have hsignal (u : Wire) : u.flip.sig = u.sig := by
      cases u; apply BitVec.eq_of_getElem_eq; intro i hi; simp [sig,Wire.flip]
    have t0 : ¬hit zero := by change ¬((0 : M) = BitVec.allOnes 55); decide
    rcases known_at hk out with (h|h)|⟨u,hu,ph⟩
    · exact (t0 (h ▸ hwin)).elim
    · rw [h] at hwin; exact (t0 (by simpa [hit,hsignal] using hwin)).elim
    · have uhit : hit u := by
        rcases ph with h|h
        · rwa [h] at hwin
        · rw [h] at hwin; simpa only [hit,hsignal] using hwin
      exact ⟨0,by decide,_,Finset.singleton_subset_iff.mpr hu,Plan.endAt u uhit⟩
  | cons g gs ih =>
    let z := wordGate ws g
    have tail := fun u (h:u∈gs) => leg u (by simp [h])
    change hit ((wordRun gs (ws++[z])).getD out zero) at hwin
    change hasPlan pool (cost g + count gs)
    by_cases already : known pool z
    · obtain ⟨k,h,S,hs,hp⟩ := ih pool (ws++[z]) (by intro w hw; rcases List.mem_append.mp hw with h|h; exact hk w h; simp only [List.mem_singleton] at h; exact h ▸ already) tail hwin
      exact ⟨k,by omega,S,hs,hp⟩
    · rcases gate_options hk (leg g (by simp)) with h|⟨cg,a,ha,b,hb,c,hc,ph⟩
      · exact (already h).elim
      have kn : known (insert c pool) z := Or.inr ⟨c,by simp,ph⟩
      have sub : pool ⊆ insert c pool := Finset.subset_insert _ _
      have base : ∀w∈ws,known (insert c pool) w := fun w hw => known_mono sub (hk w hw)
      have more := ih (insert c pool) (ws++[z]) (by intro w hw; rcases List.mem_append.mp hw with h|h; exact base w h; simp only [List.mem_singleton] at h; exact h ▸ kn) tail hwin
      simpa [cg,Nat.add_comm] using contract already ha hb hc ph more
open Wire

theorem pairs_mem {a b : Wire} {xs : List Wire} (ha : a ∈xs) (hb : b ∈xs) (ne : a≠b) :
    (a,b)∈pairs xs ∨ (b,a)∈pairs xs := by
  induction xs with
  | nil => simp at ha
  | cons u us ih =>
    by_cases e : a=u
    · subst u
      left
      simp [pairs, (List.mem_cons.mp hb).resolve_left (Ne.symm ne)]
    by_cases f : b=u
    · subst u
      right
      simp [pairs, (List.mem_cons.mp ha).resolve_left ne]
    rcases ih ((List.mem_cons.mp ha).resolve_left e) ((List.mem_cons.mp hb).resolve_left f) with l|r
    · exact Or.inl (List.mem_append_right _ l)
    · exact Or.inr (List.mem_append_right _ r)

theorem ops_swap (a b c : Wire) : c∈ops a b ↔ c∈ops b a := by
  have andComm : meet a b = meet b a := by simp [meet,BitVec.and_comm]
  have orComm : join a b = join b a := by simp [join,BitVec.or_comm]
  simp only [ops,List.mem_cons,andComm,orComm]
  tauto

theorem noLoop {a c : Wire} (h : c∈ops a a) (n : c≠zero) : c=a := by
  have x : meet a a = a := by cases a; simp [meet]
  have y : join a a = a := by cases a; simp [join]
  have z : diff a a = zero := by cases a; simp [diff,meet,Wire.flip,zero]
  simpa [ops,x,y,z,n] using h

theorem getDrops {xs : List Wire} {K : Finset Wire} {a b : Wire}
    (h : xs.toFinset = insert a (insert b K)) (nd : xs.Nodup) :
    ∃ ys∈drops xs a b, ys.toFinset=K ∧ ys.Nodup := by
  have spec (w : Wire) : w∈xs ↔ w=a ∨ w=b ∨ w∈K := by
    rw [←List.mem_toFinset,h]; simp
  by_cases ha : a∈K <;> by_cases hb : b∈K
  · exact ⟨xs,by simp [drops],by simpa [ha,hb] using h,nd⟩
  · refine ⟨xs.filter (· != b),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,bne_iff_ne,spec]
    grind
  · refine ⟨xs.filter (· != a),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,bne_iff_ne,spec]
    grind
  · refine ⟨xs.filter (fun w=>w != a && w != b),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,Bool.and_eq_true,bne_iff_ne,spec]
    grind

theorem Plan.found {m : ℕ} {S : Finset Wire} (p : Plan m S) {k : ℕ} (bound : m≤k)
    (xs : List Wire) (eq : xs.toFinset=S) (nd : xs.Nodup) : seek k xs = true := by
  have guardCard : xs.length ≤ k+1 := by
    have h := p.cardBound
    rw [←eq,List.toFinset_card_of_nodup nd] at h
    omega
  have guardMask : allSig xs = (BitVec.allOnes 55) := by
    apply adequate
    intro i
    obtain ⟨w,hw,s⟩ := p.cover i
    exact ⟨w, List.mem_toFinset.mp (eq.symm ▸ hw),s⟩
  induction p using Plan.byGates generalizing k xs with
  | endAt t ht =>
    have mem : t ∈ xs := by apply List.mem_toFinset.mp; rw [eq]; simp
    have hit' : xs.any (fun w=>w.sig == (BitVec.allOnes 55)) = true := List.any_eq_true.mpr ⟨t,mem,by simpa [hit] using ht⟩
    cases k with
    | zero => exact hit'
    | succ k => simp only [seek,decide_eq_true guardCard, guardMask, beq_self_eq_true, hit', Bool.true_or, Bool.true_and]
  | @add m T p a b c used op fa fb nz ih =>
    cases k with
    | zero => omega
    | succ k =>
      have bank (z : Wire) : z∈xs ↔ z=a ∨ z=b ∨ z∈T.erase c := by
        rw [←List.mem_toFinset,eq]; simp
      have nc : c ∉ xs := by simp [bank,fa,fb]
      have ne : a≠b := by rintro rfl; exact fa (noLoop op nz)
      have advance (a' b' : Wire) (heq : xs.toFinset=insert a' (insert b' (T.erase c)))
          (legal : c∈ops a' b') : ((ops a' b').any fun d =>
          d != zero && !xs.contains d && (drops xs a' b').any fun keep => seek k (d::keep)) = true := by
        obtain ⟨ys,hy,ey,dy⟩ := getDrops heq nd
        have cy : c∉ys := by intro h; have := List.mem_toFinset.mpr h; simp [ey] at this
        have en : (c::ys).toFinset = T := by simp [ey,Finset.insert_erase used]
        have dn : (c::ys).Nodup := List.nodup_cons.mpr ⟨cy,dy⟩
        have hn : seek k (c::ys) = true := ih (by omega) _ en dn (by
          rw [←List.toFinset_card_of_nodup dn,en]; have := p.cardBound; omega) (by
          apply adequate; intro i; obtain ⟨z,hz,sz⟩ := p.cover i
          exact ⟨z,List.mem_toFinset.mp (en.symm ▸ hz),sz⟩)
        apply List.any_eq_true.mpr
        refine ⟨c,legal,?_⟩
        simp [nz,nc,List.any_eq_true]
        exact ⟨ys,hy,hn⟩
      simp only [seek,decide_eq_true guardCard,guardMask,beq_self_eq_true,Bool.true_and,Bool.or_eq_true]
      right
      apply List.any_eq_true.mpr
      rcases pairs_mem ((bank a).2 (Or.inl rfl)) ((bank b).2 (Or.inr (Or.inl rfl))) ne with h|h
      · exact ⟨_,h,advance a b eq op⟩
      · exact ⟨_,h,advance b a (by rw [eq,Finset.insert_comm]) ((ops_swap ..).1 op)⟩

open Wire
def enough (k : ℕ) (xs : List Wire) : Bool :=
  decide (xs.length ≤ k+1) && (allSig xs == BitVec.allOnes 55)

def kids (k : ℕ) (xs : List Wire) : List (List Wire) :=
  (pairs xs).flatMap fun (a,b) => (ops a b).flatMap fun c =>
    if c ≠ zero ∧ c ∉ xs then
      ((drops xs a b).map (c::·)).filter (enough k)
    else []

open Wire

theorem mustCover {k} {xs : List Wire} (hk : 0<k) (found : seek k xs=true) : enough k xs = true := by
  cases k with
  | zero => contradiction
  | succ k =>
    simp only [seek,Bool.and_eq_true] at found
    exact Bool.and_eq_true_iff.mpr found.1

open Wire

def wireEq (a b : Wire) := a.1 == b.1 && a.2 == b.2

def quick : ℕ → List Wire → Bool
  | 0, xs => xs.any (fun w=>w.sig == BitVec.allOnes 55)
  | k+1,xs =>
    enough (k+1) xs && (xs.any (fun w=>w.sig == BitVec.allOnes 55) ||
      (pairs xs).any fun (a,b) =>
        let ds := (ops a b).filter (fun c=> !(wireEq c zero) && !(xs.any (wireEq c)))
        (drops xs a b).any fun keep =>
          (k==0 || decide (keep.length ≤ k)) &&
          let cover := allSig keep
          ds.any fun c =>
            (k==0 || ((c.sig ||| cover) == BitVec.allOnes 55)) && quick k (c::keep))
open Wire
theorem wireEq_true (a b : Wire) : wireEq a b=true ↔ a=b := by
  cases a; cases b; simp [wireEq]
theorem quickCovers (k : ℕ) (xs : List Wire) (h : seek k xs=true) : quick k xs=true := by
  induction k generalizing xs with
  | zero => exact h
  | succ k ih =>
    have ok := mustCover (Nat.zero_lt_succ k) h
    simp only [seek,Bool.and_eq_true,Bool.or_eq_true,List.any_eq_true] at h
    simp only [quick,ok,Bool.true_and,Bool.or_eq_true]
    rcases h.2 with hit|rest
    · exact Or.inl (List.any_eq_true.mpr hit)
    right
    obtain ⟨ab,hab,c,hc,⟨nz,nx⟩,keep,hkeep,yes⟩ := rest
    apply List.any_eq_true.mpr
    refine ⟨ab,hab,List.any_eq_true.mpr ⟨keep,hkeep,?_⟩⟩
    have cz : c≠zero := by simpa using nz
    have fresh : c∉xs := by simpa using nx
    have good : (!(wireEq c zero) && !(xs.any (wireEq c)))=true := by
      simp [←Bool.not_eq_true,wireEq_true,List.any_eq_true,cz,fresh]
    have legal : c ∈ (ops ab.1 ab.2).filter (fun w=> !(wireEq w zero) && !(xs.any (wireEq w))) := List.mem_filter.mpr ⟨hc,good⟩
    have room : k=0 ∨ (keep.length ≤ k ∧ c.sig ||| allSig keep = BitVec.allOnes 55) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k =>
        have yes' := mustCover (Nat.zero_lt_succ k) yes
        right
        simpa only [enough,List.length_cons,Nat.add_le_add_iff_right,allSig,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using yes'
    apply Bool.and_eq_true_iff.mpr
    constructor
    · rcases room with rfl|⟨len,_⟩ <;> simp [*]
    · apply List.any_eq_true.mpr
      refine ⟨c,legal,Bool.and_eq_true_iff.mpr ⟨?_,ih _ yes⟩⟩
      rcases room with rfl|⟨_,cov⟩ <;> simp [*]
theorem noSeekOfQuick {k xs} (h : quick k xs=false) : seek k xs=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  have contra := quickCovers _ _ yes
  rw [h] at contra; contradiction
theorem noPoolOfQuick {k} {pool : List Wire} (h : pool.sublists.any (quick k)=false) :
    pool.sublists.any (seek k)=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨xs,mem,win⟩ := List.any_eq_true.mp yes
  have t := List.any_eq_true.mpr (show ∃x∈pool.sublists,quick k x=true from ⟨xs,mem,quickCovers k xs win⟩)
  rw [h] at t; contradiction

open Wire

def fill (m : M) (j : Fin 55) (x : M) : M := if x[j.val] then x ||| ~~~m else x &&& m
def restrict (m : M) (j : Fin 55) (w : Wire) : Wire := ⟨fill m j w.1,fill m j w.2⟩

open Wire

abbrev constant (w : Wire) : Prop := w = zero ∨ w = zero.flip
theorem known_empty {w : Wire} : known ∅ w ↔ constant w := by simp [known,phase,constant]
theorem hit_not_const {w : Wire} (h : hit w) : ¬constant w := by
  rintro (rfl|rfl) <;> simp [hit,sig,zero,Wire.flip] at h

theorem op_known {S : Finset Wire} {a b c : Wire} (legal : c∈ops a b)
    (ka : known S a) (kb : known S b) : known S c ∨ newGate S c := by
  simp [ops] at legal
  rcases legal with rfl|rfl|rfl|rfl
  · exact meet_options ka kb
  · exact join_options ka kb
  · exact meet_options ka (known_flip kb)
  · exact meet_options kb (known_flip ka)

theorem meet_c_known {S : Finset Wire} {a b : Wire} (ca : constant a)
    (kb : known S b) : known S (meet a b) := by
  rcases ca with rfl|rfl
  · rw [meet_zero]; exact zeroKnown
  · rw [meet_top]; exact kb

theorem flip_c {a : Wire} (h : constant a) : constant a.flip := known_empty.1 (known_flip (known_empty.2 h))

theorem op_c_known {S : Finset Wire} {a b c : Wire} (h : c∈ops a b)
    (ka : known S a) (kb : known S b) (cp : constant a ∨ constant b) : known S c := by
  have mc {x y : Wire} (kx : known S x) (ky : known S y) (cc : constant x ∨ constant y) :
      known S (meet x y) := by
    rcases cc with z|z
    · exact meet_c_known z ky
    · rw [meet_comm]; exact meet_c_known z kx
  simp [ops] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact mc ka kb cp
  · rw [join_flips]; exact known_flip (mc (known_flip ka) (known_flip kb) (cp.imp flip_c flip_c))
  · exact mc ka (known_flip kb) (cp.imp_right flip_c)
  · exact mc kb (known_flip ka) (cp.symm.imp_right flip_c)

def fee (φ : Wire→Wire) (S : Finset Wire) : ℕ := ∑w∈S, if constant (φ w) then 1 else 0
theorem fee_ins (φ : Wire→Wire) (w : Wire) (S : Finset Wire) :
    fee φ (insert w S) ≤ fee φ S + (if constant (φ w) then 1 else 0) := by
  by_cases h : w∈S
  · simp [h]
  · unfold fee; rw [Finset.sum_insert h,Nat.add_comm]
theorem fee_erase {φ : Wire→Wire} {w : Wire} {S : Finset Wire} (h : w∈S) :
    fee φ (S.erase w) + (if constant (φ w) then 1 else 0) = fee φ S := by
  exact Finset.sum_erase_add _ _ h

theorem Plan.project {φ : Wire→Wire}
    (hits : ∀w,hit w → hit (φ w))
    (opsMap : ∀a b c,c∈ops a b → φ c∈ops (φ a) (φ b))
    {m S} (h : Plan m S) (pool : Finset Wire) (available : ∀w∈S,known pool (φ w)) :
    ∃k, k+fee φ S ≤ m ∧ hasPlan pool k := by
  induction h using Plan.byGates generalizing pool with
  | endAt t ht =>
    have good := hits t ht
    have nc := hit_not_const good
    rcases available t (by simp) with hc|⟨a,ha,ph⟩
    · exact (nc hc).elim
    have ga : hit a := by
      rcases ph with e|e
      · rwa [e] at good
      · rw [e] at good
        have hs : a.flip.sig=a.sig := by
          cases a; apply BitVec.eq_of_getElem_eq; intro i hi; simp [sig,Wire.flip]
        simpa only [hit,hs] using good
    exact ⟨0,by simp only [fee,Finset.sum_singleton,ite_eq_right nc,Nat.zero_add,Nat.le_refl],0,by decide,_,Finset.singleton_subset_iff.mpr ha,Plan.endAt a ga⟩
  | @add m T p a b c used op _ _ _ ih =>
    have ka := available a (by simp)
    have kb := available b (by simp)
    have oc := opsMap _ _ _ op
    have ca := fee_ins φ a (insert b (T.erase c))
    have cb := fee_ins φ b (T.erase c)
    have ce := fee_erase (φ:=φ) used
    have rest : ∀w∈T.erase c, known pool (φ w) := fun w hw => available w (by simp [hw])
    by_cases kc : known pool (φ c)
    · obtain ⟨k,low,plan⟩ := ih pool (fun w hw=>by
        by_cases e : w=c
        · simpa [e] using kc
        · exact rest _ (Finset.mem_erase.mpr ⟨e,hw⟩))
      refine ⟨k,?_,plan⟩
      have both (h : constant (φ a)) (j : constant (φ b)) : constant (φ c) :=
        known_empty.mp (op_c_known oc (known_empty.mpr h) (known_empty.mpr j) (Or.inl h))
      by_cases a0 : constant (φ a) <;> by_cases b0 : constant (φ b) <;> by_cases c0 : constant (φ c) <;>
        simp [a0,b0,c0] at ca cb ce <;> first | omega | exact (c0 (both a0 b0)).elim
    · obtain ⟨u,hu,v,hv,d,od,ph⟩ := (op_known oc ka kb).resolve_left kc
      have na : ¬constant (φ a) := fun e=>kc (op_c_known oc ka kb (Or.inl e))
      have nb : ¬constant (φ b) := fun e=>kc (op_c_known oc ka kb (Or.inr e))
      obtain ⟨k,low,plan⟩ := ih (insert d pool) (fun w hw=>by
        by_cases e : w=c
        · subst w; exact Or.inr ⟨d,by simp,ph⟩
        · exact known_mono (Finset.subset_insert ..) (rest _ (Finset.mem_erase.mpr ⟨e,hw⟩)))
      refine ⟨k+1,?_,contract kc hu hv od ph plan⟩
      simp only [ite_eq_right na,ite_eq_right nb,Nat.add_zero] at ca cb
      omega

theorem fill_bit (m x : M) (i j : Fin 55) :
    (fill m j x)[i.val] = if m[i.val] then x[i.val] else x[j.val] := by
  cases a : x[j.val] <;> cases b : m[i.val] <;> simp [fill,a,b]

theorem restrict_hits (m : M) (j : Fin 55) (w : Wire) (h : hit w) : hit (restrict m j w) := by
  apply (hit_iff _).2
  intro i
  change (fill m j w.1)[i.val] ≠ (fill m j w.2)[i.val]
  rw [fill_bit,fill_bit]
  split
  · exact (hit_iff _).1 h i
  · exact (hit_iff _).1 h j

theorem restrict_ops (m : M) (j : Fin 55) (a b c : Wire) (h : c∈ops a b) :
    restrict m j c ∈ ops (restrict m j a) (restrict m j b) := by
  have AND (x y : M) : fill m j (x &&& y) = fill m j x &&& fill m j y := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_and,eq]; split <;> rfl
  have OR (x y : M) : fill m j (x ||| y) = fill m j x ||| fill m j y := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_or,eq]; split <;> rfl
  have NOT (x : M) : fill m j (~~~x) = ~~~fill m j x := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_not,eq]; split <;> rfl
  simp [ops] at h ⊢
  rcases h with rfl|rfl|rfl|rfl <;> simp [restrict,meet,join,diff,Wire.flip,AND,OR,NOT]

open Wire
def NoPlan (k : ℕ) (xs : List Wire) : Prop := ∀m ≤ k, ¬Plan m xs.toFinset
def recognized (bank : List Wire) (w : Wire) : Bool :=
  w==zero || w==zero.flip || bank.any (fun a=>w==a || w==a.flip)
open Wire

theorem Plan.peel {m S} (p : Plan (m+1) S) {k : ℕ} (bound : m≤k)
    (xs : List Wire) (eq : xs.toFinset=S) (nd : xs.Nodup) :
    ∃ys∈kids k xs, ys.Nodup ∧ Plan m ys.toFinset := by
  obtain ⟨T,a,b,c,pt,used,op,fa,fb,nz,rfl⟩ := p
  have bank (z : Wire) : z∈xs ↔ z=a ∨ z=b ∨ z∈T.erase c := by
    rw [←List.mem_toFinset,eq]; simp
  have nc : c∉xs := by simp [bank,fa,fb]
  have ne : a≠b := by rintro rfl; exact fa (noLoop op nz)
  have makeChild (a' b' : Wire) (heq : xs.toFinset=insert a' (insert b' (T.erase c)))
      (leg : c∈ops a' b') (hm : (a',b') ∈ pairs xs) : ∃ys∈kids k xs, ys.Nodup ∧ Plan m ys.toFinset := by
    obtain ⟨ys,hy,ey,dy⟩ := getDrops heq nd
    have cy : c∉ys := by intro h; have := List.mem_toFinset.mpr h; simp [ey] at this
    have en : (c::ys).toFinset = T := by simp [ey,Finset.insert_erase used]
    have dn := List.nodup_cons.mpr ⟨cy,dy⟩
    have hc : (c::ys).length ≤ k+1 := by
      rw [←List.toFinset_card_of_nodup dn,en]; have := pt.cardBound; omega
    have hs : allSig (c::ys) = BitVec.allOnes 55 := by
      apply adequate; intro i; obtain ⟨w,hw,sep⟩ := pt.cover i
      exact ⟨w,List.mem_toFinset.mp (en.symm ▸ hw),sep⟩
    refine ⟨c::ys,?_,dn,en.symm ▸ pt⟩
    apply List.mem_flatMap.mpr; refine ⟨(a',b'),hm,?_⟩
    apply List.mem_flatMap.mpr; refine ⟨c,leg,?_⟩
    rw [ite_eq_left (And.intro nz nc)]
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,hy,rfl⟩,by simp only [enough,decide_eq_true hc,hs,beq_self_eq_true,Bool.true_and]⟩
  rcases pairs_mem ((bank a).2 (Or.inl rfl)) ((bank b).2 (Or.inr (Or.inl rfl))) ne with h|h
  · exact makeChild a b eq op h
  · exact makeChild b a (by rw [eq,Finset.insert_comm]) ((ops_swap ..).1 op) h

theorem hasPlanSearch {xs : List Wire} (nd : xs.Nodup) {k} (p : hasPlan xs.toFinset k) :
    xs.sublists.any (seek k) = true := by
  classical
  obtain ⟨m,mb,S,ss,pl⟩ := p
  let ys := xs.filter fun w=>w∈S
  have eq : ys.toFinset=S := by
    ext w
    simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨List.mem_toFinset.mp (ss h),h⟩⟩
  exact List.any_eq_true.mpr ⟨ys,List.mem_sublists.mpr (List.filter_sublist ..),pl.found mb ys eq (nd.filter _)⟩

theorem recognized_iff {xs : List Wire} {w : Wire} : recognized xs w = true ↔ known xs.toFinset w := by
  simp [recognized,known,phase]

theorem const_length (φ : Wire→Wire) (xs : List Wire) (nd : xs.Nodup) :
    (xs.filter (fun w => let t := φ w; t==zero || t==zero.flip)).length = fee φ xs.toFinset := by
  induction xs with
  | nil => simp [fee]
  | cons a xs ih =>
    obtain ⟨ne,dt⟩ := List.nodup_cons.mp nd
    have notin : a ∉xs.toFinset := by simpa using ne
    rw [List.toFinset_cons]
    unfold fee at *
    rw [Finset.sum_insert notin]
    by_cases h : constant (φ a)
    · have hb : (φ a==zero || φ a==zero.flip)=true := by simpa [constant] using h
      simp [hb,h,ih dt,Nat.add_comm]
    · have hb : (φ a==zero || φ a==zero.flip)=false := by simpa [constant,not_or] using h
      simp [hb,h,ih dt]

def applies (mask : M) (j : Fin 55) (bank : List Wire) (budget k : ℕ) (xs : List Wire) : Bool :=
  decide (k ≤ budget + (xs.filter (fun w => let t := restrict mask j w; t==zero || t==zero.flip)).length) &&
    xs.all (fun w=>recognized bank (restrict mask j w))

theorem banByRestriction {mask j bank budget k xs} (nodup : bank.Nodup) (ban : bank.sublists.any (quick budget)=false)
    (nd : xs.Nodup) (active : applies mask j bank budget k xs=true) : NoPlan k xs := by
  intro m upper pl
  simp only [applies,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at active
  have avail : ∀w∈xs.toFinset,known bank.toFinset (restrict mask j w) :=
    fun w hw=>recognized_iff.mp (active.2 w (List.mem_toFinset.mp hw))
  obtain ⟨q,low,has⟩ := pl.project (restrict_hits mask j) (restrict_ops mask j) bank.toFinset avail
  have qr : q≤budget := by have aux := active.1; rw [const_length _ _ nd] at aux; omega
  obtain ⟨n,nh,S,sub,plan⟩ := has
  have yes := hasPlanSearch nodup (k:=budget) ⟨n,by omega,S,sub,plan⟩
  rw [noPoolOfQuick ban] at yes; contradiction

theorem banBySearch {k xs} (nd : xs.Nodup) (h : quick k xs = false) : NoPlan k xs := by
  intro m hm p
  have t := quickCovers k xs (p.found hm xs rfl nd)
  rw [h] at t
  contradiction

theorem banBySplit {k xs} (nd : xs.Nodup) (miss : xs.any (fun w=>w.sig == BitVec.allOnes 55)=false)
    (h : ∀ys∈kids k xs, NoPlan k ys) : NoPlan (k+1) xs := by
  intro m hm p
  cases m with
  | zero =>
    obtain ⟨t,win,e⟩ := p
    have mem : t∈xs := by apply List.mem_toFinset.mp; rw [e]; simp
    have yes := List.any_eq_true.mpr (show ∃w∈xs,(w.sig == BitVec.allOnes 55)=true from ⟨_,mem,by simpa [hit] using win⟩)
    rw [miss] at yes; contradiction
  | succ m =>
    obtain ⟨ys,mem,_,py⟩ := p.peel (k:=k) (by omega) xs rfl nd
    exact h ys mem m (by omega) py

def base5 : List Wire := [⟨0x7ffbc7fd007fff#55,0x3a#55⟩,⟨0x7ffdf8e2ff8e07#55,0x38000001f8e04#55⟩,⟨0xedb276bb248#55,0x2c90000361b240#55⟩,⟨0xf6d4bb6d490#55,0x35200003a65480#55⟩,⟨0xfb693dd6920#55,0x3a400003d86900#55⟩]

theorem liftRoot (lower : NoPlan 8 base5) : NoPlan 9 pins := by
  intro m upper pl
  have active : applies 0x3fffffffffffff 0 base5 8 9 pins=true := by decide +kernel
  simp only [applies,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at active
  have avail : ∀w∈pins.toFinset,known base5.toFinset (restrict 0x3fffffffffffff 0 w) :=
    fun w hw=>recognized_iff.mp (active.2 w (List.mem_toFinset.mp hw))
  obtain ⟨q,low,has⟩ := pl.project (restrict_hits 0x3fffffffffffff 0) (restrict_ops 0x3fffffffffffff 0) base5.toFinset avail
  have nd : pins.Nodup := by decide +kernel
  have qr : q≤8 := by have aux := active.1; rw [const_length _ _ nd] at aux; omega
  obtain ⟨v,hv,S,sub,plan⟩ := has
  let xs := base5.filter fun w=>w∈S
  have eq : xs.toFinset=S := by
    ext w
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨List.mem_toFinset.mp (sub h),h⟩⟩
  have incl : xs∈base5.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have closed : base5.sublists.all (fun ys => ys==base5 || allSig ys != BitVec.allOnes 55) = true := by decide +kernel
  have all := List.all_eq_true.mp closed xs incl
  have covers : allSig xs=BitVec.allOnes 55 := by
    apply adequate; intro i; obtain ⟨w,hw,sep⟩ := plan.cover i
    exact ⟨w,List.mem_toFinset.mp (eq.symm ▸ hw),sep⟩
  have same : xs=base5 := by simpa only [covers,bne_self_eq_false,Bool.or_false,beq_iff_eq] using all
  have e : S=base5.toFinset := eq.symm.trans (congrArg List.toFinset same)
  exact lower v (by omega) (e ▸ plan)
open Wire

def shuffleBits (f : Fin 55 → Fin 55) (v : M) : M :=
  (BitVec.ofBoolListLE (List.ofFn fun i => v[(f i).val])).cast (by simp)

@[local simp] theorem shuffleBits_get (f : Fin 55 → Fin 55) (v : M) (i : Nat) (h : i < 55) :
    (shuffleBits f v)[i] = v[(f ⟨i,h⟩).val] := by
  simp only [shuffleBits,BitVec.getElem_cast]
  rw [←BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_ofFn, dif_pos h]; rfl

def shuffleWire (f : Fin 55 → Fin 55) (w : Wire) : Wire := ⟨shuffleBits f w.1,shuffleBits f w.2⟩

theorem shuffle_inj {f g : Fin 55 → Fin 55} (inv : ∀i, f (g i)=i) :
    Function.Injective (shuffleWire f) := by
  intro x y eq
  have injBits {x y : M} (hxy : shuffleBits f x=shuffleBits f y) : x=y := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    let j := g ⟨i,hi⟩
    have h := congrArg (fun z : M => z[j.val]) hxy
    simpa [j,inv] using h
  exact Prod.ext (injBits (congrArg Prod.fst eq)) (injBits (congrArg Prod.snd eq))

theorem shuffle_zero (f : Fin 55 → Fin 55) : shuffleWire f zero=zero := by
  apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp [shuffleWire, zero]

theorem shuffle_hit (f : Fin 55 → Fin 55) {w} (hw : hit w) : hit (shuffleWire f w) := by
  apply (hit_iff _).2
  intro i
  simpa [separates,shuffleWire] using (hit_iff _).1 hw (f i)

theorem shuffle_ops (f : Fin 55 → Fin 55) {a b c} (h : c∈ops a b) :
    shuffleWire f c∈ops (shuffleWire f a) (shuffleWire f b) := by
  have meetS (a b : Wire) : shuffleWire f (meet a b) = meet (shuffleWire f a) (shuffleWire f b) := by
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp [meet,shuffleWire]
  have joinS (a b : Wire) : shuffleWire f (join a b) = join (shuffleWire f a) (shuffleWire f b) := by
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp [join,shuffleWire]
  have flipS (a : Wire) : shuffleWire f a.flip = (shuffleWire f a).flip := by
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp [Wire.flip,shuffleWire]
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl|rfl|rfl|rfl <;> simp [diff,meetS,joinS,flipS]

theorem viaSymmetry {k xs ys} (f g : Fin 55 → Fin 55) (inv : ∀i, f (g i)=i)
    (low : NoPlan k ys) (he : xs.toFinset.image (shuffleWire f)=ys.toFinset) : NoPlan k xs := by
  intro m bound p
  apply low m bound
  rw [←he]
  have lift {m S} (p : Plan m S) : Plan m (S.image (shuffleWire f)) := by
    have inj := shuffle_inj inv
    induction p using Plan.byGates with
    | endAt t hit =>
      rw [Finset.image_singleton]
      exact Plan.endAt _ (shuffle_hit f hit)
    | @add k T _ a b c used op fa fb nz ih =>
      rw [Finset.image_insert,Finset.image_insert,Finset.image_erase inj]
      exact Plan.add ih (Finset.mem_image_of_mem _ used) (shuffle_ops f op)
        (fun h => fa (inj h)) (fun h => fb (inj h)) (fun h => nz (inj (h.trans (shuffle_zero f).symm)))
  exact lift p

def perm1 (j : Fin 55) : Fin 55 := (#v[0,1,2,3,5,4,6,8,7,9,11,10,13,12,14,16,15,19,20,17,18,22,21,23,24,25,26,28,27,29,31,30,33,32,34,36,35,37,39,38,40,41,42,43,44,46,45,47,49,48,51,50,52,53,54] : Vector (Fin 55) 55)[j.val]
def inv1 (j : Fin 55) : Fin 55 := (#v[0,1,2,3,5,4,6,8,7,9,11,10,13,12,14,16,15,19,20,17,18,22,21,23,24,25,26,28,27,29,31,30,33,32,34,36,35,37,39,38,40,41,42,43,44,46,45,47,49,48,51,50,52,53,54] : Vector (Fin 55) 55)[j.val]
theorem invId1 : ∀j, perm1 (inv1 j)=j := by decide +kernel
def perm2 (j : Fin 55) : Fin 55 := (#v[0,1,2,4,3,5,7,6,8,10,9,11,12,14,13,17,18,15,16,20,19,21,23,22,24,25,27,26,28,30,29,31,32,34,33,35,37,36,38,40,39,41,42,43,45,44,46,48,47,49,50,52,51,53,54] : Vector (Fin 55) 55)[j.val]
def inv2 (j : Fin 55) : Fin 55 := (#v[0,1,2,4,3,5,7,6,8,10,9,11,12,14,13,17,18,15,16,20,19,21,23,22,24,25,27,26,28,30,29,31,32,34,33,35,37,36,38,40,39,41,42,43,45,44,46,48,47,49,50,52,51,53,54] : Vector (Fin 55) 55)[j.val]
theorem invId2 : ∀j, perm2 (inv2 j)=j := by decide +kernel
def perm3 (j : Fin 55) : Fin 55 := (#v[0,1,2,4,5,3,7,8,6,10,11,9,14,12,13,18,17,20,19,15,16,23,21,22,24,25,27,28,26,30,31,29,34,32,33,37,35,36,40,38,39,41,42,43,45,46,44,48,49,47,52,50,51,53,54] : Vector (Fin 55) 55)[j.val]
def inv3 (j : Fin 55) : Fin 55 := (#v[0,1,2,5,3,4,8,6,7,11,9,10,13,14,12,19,20,16,15,18,17,22,23,21,24,25,28,26,27,31,29,30,33,34,32,36,37,35,39,40,38,41,42,43,46,44,45,49,47,48,51,52,50,53,54] : Vector (Fin 55) 55)[j.val]
theorem invId3 : ∀j, perm3 (inv3 j)=j := by decide +kernel
def perm4 (j : Fin 55) : Fin 55 := (#v[0,1,2,5,3,4,8,6,7,11,9,10,13,14,12,19,20,16,15,18,17,22,23,21,24,25,28,26,27,31,29,30,33,34,32,36,37,35,39,40,38,41,42,43,46,44,45,49,47,48,51,52,50,53,54] : Vector (Fin 55) 55)[j.val]
def inv4 (j : Fin 55) : Fin 55 := (#v[0,1,2,4,5,3,7,8,6,10,11,9,14,12,13,18,17,20,19,15,16,23,21,22,24,25,27,28,26,30,31,29,34,32,33,37,35,36,40,38,39,41,42,43,45,46,44,48,49,47,52,50,51,53,54] : Vector (Fin 55) 55)[j.val]
theorem invId4 : ∀j, perm4 (inv4 j)=j := by decide +kernel
def perm5 (j : Fin 55) : Fin 55 := (#v[0,1,2,5,4,3,8,7,6,11,10,9,14,13,12,20,19,18,17,16,15,23,22,21,24,25,28,27,26,31,30,29,34,33,32,37,36,35,40,39,38,41,42,43,46,45,44,49,48,47,52,51,50,53,54] : Vector (Fin 55) 55)[j.val]
def inv5 (j : Fin 55) : Fin 55 := (#v[0,1,2,5,4,3,8,7,6,11,10,9,14,13,12,20,19,18,17,16,15,23,22,21,24,25,28,27,26,31,30,29,34,33,32,37,36,35,40,39,38,41,42,43,46,45,44,49,48,47,52,51,50,53,54] : Vector (Fin 55) 55)[j.val]
theorem invId5 : ∀j, perm5 (inv5 j)=j := by decide +kernel
def v0 : Wire := ⟨0x7ffbc7fd007fff#55,0x3a#55⟩
def v1 : Wire := ⟨0x7ffdf8e2ff8e07#55,0x38000001f8e04#55⟩
def v2 : Wire := ⟨0xedb276bb248#55,0x2c90000361b240#55⟩
def v3 : Wire := ⟨0xf6d4bb6d490#55,0x35200003a65480#55⟩
def v4 : Wire := ⟨0xfb693dd6920#55,0x3a400003d86900#55⟩
def s0 : List Wire := [v0,v1,v2,v3,v4]
def v5 : Wire := ⟨0x7ff9c0e0000e07#55,0x0#55⟩
def s1 : List Wire := [v5,v0,v1,v2,v3,v4]
def v6 : Wire := ⟨0x43802ff8000#55,0x1f8000#55⟩
def v7 : Wire := ⟨0x7fffdbe76bbe4f#55,0x361b040#55⟩
def v8 : Wire := ⟨0x62d0bb6d090#55,0x3a65080#55⟩
def v9 : Wire := ⟨0x63613dd6120#55,0x3d86100#55⟩
def v10 : Wire := ⟨0x7ffbc7fd007fff#55,0x7ff9c0e0000e3f#55⟩
def s2 : List Wire := [v6,v7,v8,v9,v10]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p0 : s2.sublists.any (quick 6) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h1 : NoPlan 7 s1 := banByRestriction (mask:=0x63f1ffff1f8) (j:=3) (bank:=s2) (budget:=6) (by decide +kernel) p0 (by decide +kernel) (by decide +kernel)
def v11 : Wire := ⟨0x7fffffffffffff#55,0x38000001f8e3e#55⟩
def s3 : List Wire := [v11,v0,v1,v2,v3,v4]
def v12 : Wire := ⟨0x43802ff8000#55,0x38000001f8e04#55⟩
def s4 : List Wire := [v12,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h3 : NoPlan 6 s4 := banBySearch (by decide +kernel) (by decide +kernel)
def s5 : List Wire := [v12,v0,v1,v2,v3,v4]
def v13 : Wire := ⟨0x7ffffffff6ffff#55,0x60000#55⟩
def v14 : Wire := ⟨0x1d0000#55,0x180000#55⟩
def v15 : Wire := ⟨0x7fffffffebffff#55,0x7fffffffe1ffff#55⟩
def s6 : List Wire := [v13,v14,v15]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p1 : s6.sublists.any (quick 3) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h4 : NoPlan 6 s5 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s7 : List Wire := [v12,v11,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h5 : NoPlan 6 s7 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v16 : Wire := ⟨0x2071d0071f8#55,0x3a#55⟩
def s8 : List Wire := [v16,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h6 : NoPlan 6 s8 := banBySearch (by decide +kernel) (by decide +kernel)
def s9 : List Wire := [v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h7 : NoPlan 6 s9 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s10 : List Wire := [v16,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h8 : NoPlan 6 s10 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v17 : Wire := ⟨0xedb276bb248#55,0x800000018200#55⟩
def s11 : List Wire := [v17,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h9 : NoPlan 6 s11 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s12 : List Wire := [v17,v0,v1,v2,v3,v4]
def v18 : Wire := ⟨0x7fffdfff6bffff#55,0x32#55⟩
def v19 : Wire := ⟨0x7ffffbe7ffbe4f#55,0x3000000140c04#55⟩
def v20 : Wire := ⟨0x12448944490#55,0x11200000844480#55⟩
def v21 : Wire := ⟨0x12490944920#55,0x12400000904900#55⟩
def s13 : List Wire := [v18,v19,v20,v21]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p2 : s13.sublists.any (quick 4) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h10 : NoPlan 6 s12 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s14 : List Wire := [v17,v11,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h11 : NoPlan 6 s14 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s15 : List Wire := [v17,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h12 : NoPlan 6 s15 := banBySearch (by decide +kernel) (by decide +kernel)
def v22 : Wire := ⟨0x7fffffffffffff#55,0x2f9000037fbe7e#55⟩
def s16 : List Wire := [v22,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p3 : s6.sublists.any (quick 2) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h13 : NoPlan 6 s16 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s17 : List Wire := [v22,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h14 : NoPlan 6 s17 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v23 : Wire := ⟨0x7ff124d8944db7#55,0x30000001e0c3e#55⟩
def s18 : List Wire := [v23,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h15 : NoPlan 6 s18 := banBySearch (by decide +kernel) (by decide +kernel)
def s19 : List Wire := [v23,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h16 : NoPlan 6 s19 := banBySearch (by decide +kernel) (by decide +kernel)
def s20 : List Wire := [v23,v11,v0,v1,v3,v4]
def v24 : Wire := ⟨0x140000#55,0x1e0000#55⟩
def s21 : List Wire := [v13,v14,v24]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p4 : s21.sublists.any (quick 3) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h17 : NoPlan 6 s20 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s21) (budget:=3) (by decide +kernel) p4 (by decide +kernel) (by decide +kernel)
def s22 : List Wire := [v23,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h18 : NoPlan 6 s22 := banBySearch (by decide +kernel) (by decide +kernel)
def v25 : Wire := ⟨0x0#55,0x2c100003603040#55⟩
def s23 : List Wire := [v25,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h19 : NoPlan 6 s23 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s24 : List Wire := [v25,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h20 : NoPlan 6 s24 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v26 : Wire := ⟨0xf6d4bb6d490#55,0x1000000060400#55⟩
def s25 : List Wire := [v26,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h21 : NoPlan 6 s25 := viaSymmetry perm2 inv2 invId2 h9 (by decide +kernel)
def s26 : List Wire := [v26,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h22 : NoPlan 6 s26 := viaSymmetry perm2 inv2 invId2 h10 (by decide +kernel)
def s27 : List Wire := [v26,v11,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h23 : NoPlan 6 s27 := viaSymmetry perm2 inv2 invId2 h11 (by decide +kernel)
def s28 : List Wire := [v26,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h24 : NoPlan 6 s28 := viaSymmetry perm2 inv2 invId2 h12 (by decide +kernel)
def v27 : Wire := ⟨0x7fffffffffffff#55,0x37a00003bfdebe#55⟩
def s29 : List Wire := [v27,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h25 : NoPlan 6 s29 := viaSymmetry perm2 inv2 invId2 h13 (by decide +kernel)
def s30 : List Wire := [v27,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h26 : NoPlan 6 s30 := viaSymmetry perm2 inv2 invId2 h14 (by decide +kernel)
def v28 : Wire := ⟨0x7ff092b4492b6f#55,0x2800000198a3e#55⟩
def s31 : List Wire := [v28,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h27 : NoPlan 6 s31 := viaSymmetry perm2 inv2 invId2 h15 (by decide +kernel)
def s32 : List Wire := [v28,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h28 : NoPlan 6 s32 := viaSymmetry perm2 inv2 invId2 h16 (by decide +kernel)
def s33 : List Wire := [v28,v11,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h29 : NoPlan 6 s33 := viaSymmetry perm2 inv2 invId2 h17 (by decide +kernel)
def s34 : List Wire := [v28,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h30 : NoPlan 6 s34 := viaSymmetry perm2 inv2 invId2 h18 (by decide +kernel)
def v29 : Wire := ⟨0x0#55,0x34200003a05080#55⟩
def s35 : List Wire := [v29,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h31 : NoPlan 6 s35 := viaSymmetry perm2 inv2 invId2 h19 (by decide +kernel)
def s36 : List Wire := [v29,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h32 : NoPlan 6 s36 := viaSymmetry perm2 inv2 invId2 h20 (by decide +kernel)
def v30 : Wire := ⟨0xfb693dd6920#55,0x2000000180800#55⟩
def s37 : List Wire := [v30,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h33 : NoPlan 6 s37 := viaSymmetry perm4 inv4 invId4 h9 (by decide +kernel)
def s38 : List Wire := [v30,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h34 : NoPlan 6 s38 := viaSymmetry perm4 inv4 invId4 h10 (by decide +kernel)
def s39 : List Wire := [v30,v11,v0,v1,v2,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h35 : NoPlan 6 s39 := viaSymmetry perm4 inv4 invId4 h11 (by decide +kernel)
def s40 : List Wire := [v30,v0,v1,v2,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h36 : NoPlan 6 s40 := viaSymmetry perm4 inv4 invId4 h12 (by decide +kernel)
def v31 : Wire := ⟨0x7fffffffffffff#55,0x3bc00003dfef3e#55⟩
def s41 : List Wire := [v31,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h37 : NoPlan 6 s41 := viaSymmetry perm4 inv4 invId4 h13 (by decide +kernel)
def s42 : List Wire := [v31,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h38 : NoPlan 6 s42 := viaSymmetry perm4 inv4 invId4 h14 (by decide +kernel)
def v32 : Wire := ⟨0x7ff0496c2296df#55,0x180000007863e#55⟩
def s43 : List Wire := [v32,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h39 : NoPlan 6 s43 := viaSymmetry perm4 inv4 invId4 h15 (by decide +kernel)
def s44 : List Wire := [v32,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h40 : NoPlan 6 s44 := viaSymmetry perm4 inv4 invId4 h16 (by decide +kernel)
def s45 : List Wire := [v32,v11,v0,v1,v2,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h41 : NoPlan 6 s45 := viaSymmetry perm4 inv4 invId4 h17 (by decide +kernel)
def s46 : List Wire := [v32,v0,v1,v2,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h42 : NoPlan 6 s46 := viaSymmetry perm4 inv4 invId4 h18 (by decide +kernel)
def v33 : Wire := ⟨0x0#55,0x38400003c06100#55⟩
def s47 : List Wire := [v33,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h43 : NoPlan 6 s47 := viaSymmetry perm4 inv4 invId4 h19 (by decide +kernel)
def s48 : List Wire := [v33,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h44 : NoPlan 6 s48 := viaSymmetry perm4 inv4 invId4 h20 (by decide +kernel)
def s49 : List Wire := [v5,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h45 : NoPlan 6 s49 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s50 : List Wire := [v5,v11,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h46 : NoPlan 6 s50 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s51 : List Wire := [v5,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h47 : NoPlan 6 s51 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s52 : List Wire := [v5,v11,v2,v3,v4]
def v34 : Wire := ⟨0x7fffffeffffedf#55,0x0#55⟩
def v35 : Wire := ⟨0x7fffffffffffff#55,0x2000000000826#55⟩
def v36 : Wire := ⟨0x90000920#55,0x2400000000900#55⟩
def s53 : List Wire := [v34,v35,v36]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p5 : s53.sublists.any (quick 4) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h48 : NoPlan 6 s52 := banByRestriction (mask:=0x42400090000927) (j:=0) (bank:=s53) (budget:=4) (by decide +kernel) p5 (by decide +kernel) (by decide +kernel)
def v37 : Wire := ⟨0xac325003248#55,0x0#55⟩
def s54 : List Wire := [v37,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h49 : NoPlan 6 s54 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def v38 : Wire := ⟨0x7fffdfff6bffff#55,0x2c90000361b27a#55⟩
def s55 : List Wire := [v38,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h50 : NoPlan 6 s55 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v39 : Wire := ⟨0x7ff104d8004db7#55,0x3a#55⟩
def s56 : List Wire := [v39,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h51 : NoPlan 6 s56 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def v40 : Wire := ⟨0x418026b8000#55,0x2c90000361b240#55⟩
def s57 : List Wire := [v40,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h52 : NoPlan 6 s57 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v41 : Wire := ⟨0xb4549005490#55,0x0#55⟩
def s58 : List Wire := [v41,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h53 : NoPlan 6 s58 := viaSymmetry perm2 inv2 invId2 h49 (by decide +kernel)
def v42 : Wire := ⟨0x7fffefffb6ffff#55,0x35200003a654ba#55⟩
def s59 : List Wire := [v42,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h54 : NoPlan 6 s59 := viaSymmetry perm2 inv2 invId2 h50 (by decide +kernel)
def v43 : Wire := ⟨0x7ff082b4002b6f#55,0x3a#55⟩
def s60 : List Wire := [v43,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h55 : NoPlan 6 s60 := viaSymmetry perm2 inv2 invId2 h51 (by decide +kernel)
def v44 : Wire := ⟨0x42802b68000#55,0x35200003a65480#55⟩
def s61 : List Wire := [v44,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h56 : NoPlan 6 s61 := viaSymmetry perm2 inv2 invId2 h52 (by decide +kernel)
def v45 : Wire := ⟨0xb8691006920#55,0x0#55⟩
def s62 : List Wire := [v45,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h57 : NoPlan 6 s62 := viaSymmetry perm4 inv4 invId4 h49 (by decide +kernel)
def v46 : Wire := ⟨0x7ffff7ffdd7fff#55,0x3a400003d8693a#55⟩
def s63 : List Wire := [v46,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h58 : NoPlan 6 s63 := viaSymmetry perm4 inv4 invId4 h50 (by decide +kernel)
def v47 : Wire := ⟨0x7ff0416c0016df#55,0x3a#55⟩
def s64 : List Wire := [v47,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h59 : NoPlan 6 s64 := viaSymmetry perm4 inv4 invId4 h51 (by decide +kernel)
def v48 : Wire := ⟨0x43002dd0000#55,0x3a400003d86900#55⟩
def s65 : List Wire := [v48,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h60 : NoPlan 6 s65 := viaSymmetry perm4 inv4 invId4 h52 (by decide +kernel)
def v49 : Wire := ⟨0xcd8226b8200#55,0x800000018200#55⟩
def s66 : List Wire := [v49,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h61 : NoPlan 6 s66 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v50 : Wire := ⟨0x7ffffbe7ffbe4f#55,0x2f9000037fbe44#55⟩
def s67 : List Wire := [v50,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h62 : NoPlan 6 s67 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s68 : List Wire := [v50,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h63 : NoPlan 6 s68 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v51 : Wire := ⟨0x7ff120c0940c07#55,0x30000001e0c04#55⟩
def s69 : List Wire := [v51,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h64 : NoPlan 6 s69 := banBySearch (by decide +kernel) (by decide +kernel)
def s70 : List Wire := [v51,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h65 : NoPlan 6 s70 := banBySearch (by decide +kernel) (by decide +kernel)
def v52 : Wire := ⟨0x20305003048#55,0x2c100003603040#55⟩
def s71 : List Wire := [v52,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h66 : NoPlan 6 s71 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def v53 : Wire := ⟨0xd6842b68400#55,0x1000000060400#55⟩
def s72 : List Wire := [v53,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h67 : NoPlan 6 s72 := viaSymmetry perm2 inv2 invId2 h61 (by decide +kernel)
def v54 : Wire := ⟨0x7ffffdebffde97#55,0x37a00003bfde84#55⟩
def s73 : List Wire := [v54,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h68 : NoPlan 6 s73 := viaSymmetry perm2 inv2 invId2 h62 (by decide +kernel)
def s74 : List Wire := [v54,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h69 : NoPlan 6 s74 := viaSymmetry perm2 inv2 invId2 h63 (by decide +kernel)
def v55 : Wire := ⟨0x7ff090a0490a07#55,0x2800000198a04#55⟩
def s75 : List Wire := [v55,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h70 : NoPlan 6 s75 := viaSymmetry perm2 inv2 invId2 h64 (by decide +kernel)
def s76 : List Wire := [v55,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h71 : NoPlan 6 s76 := viaSymmetry perm2 inv2 invId2 h65 (by decide +kernel)
def v56 : Wire := ⟨0x20509005090#55,0x34200003a05080#55⟩
def s77 : List Wire := [v56,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h72 : NoPlan 6 s77 := viaSymmetry perm2 inv2 invId2 h66 (by decide +kernel)
def v57 : Wire := ⟨0xdb082dd0800#55,0x2000000180800#55⟩
def s78 : List Wire := [v57,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h73 : NoPlan 6 s78 := viaSymmetry perm4 inv4 invId4 h61 (by decide +kernel)
def v58 : Wire := ⟨0x7ffffef3ffef27#55,0x3bc00003dfef04#55⟩
def s79 : List Wire := [v58,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h74 : NoPlan 6 s79 := viaSymmetry perm4 inv4 invId4 h62 (by decide +kernel)
def s80 : List Wire := [v58,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h75 : NoPlan 6 s80 := viaSymmetry perm4 inv4 invId4 h63 (by decide +kernel)
def v59 : Wire := ⟨0x7ff04860228607#55,0x1800000078604#55⟩
def s81 : List Wire := [v59,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h76 : NoPlan 6 s81 := viaSymmetry perm4 inv4 invId4 h64 (by decide +kernel)
def s82 : List Wire := [v59,v11,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h77 : NoPlan 6 s82 := viaSymmetry perm4 inv4 invId4 h65 (by decide +kernel)
def v60 : Wire := ⟨0x20611006120#55,0x38400003c06100#55⟩
def s83 : List Wire := [v60,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h78 : NoPlan 6 s83 := viaSymmetry perm4 inv4 invId4 h66 (by decide +kernel)
def v61 : Wire := ⟨0xe4903229000#55,0x24000003201000#55⟩
def s84 : List Wire := [v61,v11,v0,v1,v2,v3,v4]
def v62 : Wire := ⟨0x90208#55,0x800000010200#55⟩
def v63 : Wire := ⟨0x90820#55,0x2000000080800#55⟩
def v64 : Wire := ⟨0x7fffffffffffd7#55,0x2800000090a04#55⟩
def v65 : Wire := ⟨0x7ffffffff6ffff#55,0x7d7ffffff6f5fb#55⟩
def s85 : List Wire := [v62,v63,v64,v65]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p6 : s85.sublists.any (quick 3) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h79 : NoPlan 6 s84 := banByRestriction (mask:=0x2800000090a2e) (j:=1) (bank:=s85) (budget:=3) (by decide +kernel) p6 (by decide +kernel) (by decide +kernel)
def v66 : Wire := ⟨0xfff6ffff6d8#55,0x3db00003e7f6c0#55⟩
def s86 : List Wire := [v66,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h80 : NoPlan 6 s86 := banBySearch (by decide +kernel) (by decide +kernel)
def v67 : Wire := ⟨0x9224492248#55,0x890000041a240#55⟩
def s87 : List Wire := [v67,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h81 : NoPlan 6 s87 := banBySearch (by decide +kernel) (by decide +kernel)
def v68 : Wire := ⟨0x12448944490#55,0x11200000864480#55⟩
def s88 : List Wire := [v68,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h82 : NoPlan 6 s88 := viaSymmetry perm2 inv2 invId2 h81 (by decide +kernel)
def v69 : Wire := ⟨0xe9203492000#55,0x28000003402000#55⟩
def s89 : List Wire := [v69,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h83 : NoPlan 6 s89 := viaSymmetry perm1 inv1 invId1 h79 (by decide +kernel)
def v70 : Wire := ⟨0xfffb7fffb68#55,0x3ed00003f9fb40#55⟩
def s90 : List Wire := [v70,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h84 : NoPlan 6 s90 := viaSymmetry perm1 inv1 invId1 h80 (by decide +kernel)
def v71 : Wire := ⟨0x4924229248#55,0x4900000219240#55⟩
def s91 : List Wire := [v71,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h85 : NoPlan 6 s91 := viaSymmetry perm1 inv1 invId1 h81 (by decide +kernel)
def v72 : Wire := ⟨0x12490944920#55,0x12400000984900#55⟩
def s92 : List Wire := [v72,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h86 : NoPlan 6 s92 := viaSymmetry perm4 inv4 invId4 h81 (by decide +kernel)
def v73 : Wire := ⟨0xf2403944000#55,0x30000003804000#55⟩
def s93 : List Wire := [v73,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h87 : NoPlan 6 s93 := viaSymmetry perm3 inv3 invId3 h79 (by decide +kernel)
def v74 : Wire := ⟨0xfffdbfffdb0#55,0x3f600003fe7d80#55⟩
def s94 : List Wire := [v74,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h88 : NoPlan 6 s94 := viaSymmetry perm3 inv3 invId3 h80 (by decide +kernel)
def v75 : Wire := ⟨0x4948229490#55,0x5200000261480#55⟩
def s95 : List Wire := [v75,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h89 : NoPlan 6 s95 := viaSymmetry perm3 inv3 invId3 h81 (by decide +kernel)
def v76 : Wire := ⟨0x9290492920#55,0xa400000582900#55⟩
def s96 : List Wire := [v76,v11,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h90 : NoPlan 6 s96 := viaSymmetry perm5 inv5 invId5 h81 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h2 : NoPlan 7 s3 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s3 = [s4,s5,s7,s8,s9,s10,s11,s12,s14,s15,s16,s17,s18,s19,s20,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50,s51,s52,s8,s10,s4,s7,s54,s55,s56,s57,s58,s59,s60,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71,s72,s73,s74,s75,s76,s77,s78,s79,s80,s81,s82,s83,s84,s86,s87,s88,s89,s90,s91,s92,s93,s94,s95,s96] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h6,h8,h3,h5,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76,h77,h78,h79,h80,h81,h82,h83,h84,h85,h86,h87,h88,h89,h90⟩
def s97 : List Wire := [v5,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h92 : NoPlan 6 s97 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h93 : NoPlan 6 s1 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s98 : List Wire := [v5,v16,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h94 : NoPlan 6 s98 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s99 : List Wire := [v11,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h95 : NoPlan 6 s99 := by unfold NoPlan at *; rw [show s99.toFinset=s8.toFinset by decide +kernel]; exact h6
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h96 : NoPlan 6 s3 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s100 : List Wire := [v11,v16,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h97 : NoPlan 6 s100 := by unfold NoPlan at *; rw [show s100.toFinset=s10.toFinset by decide +kernel]; exact h8
def v77 : Wire := ⟨0x20305003048#55,0x0#55⟩
def s101 : List Wire := [v77,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h98 : NoPlan 6 s101 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s102 : List Wire := [v77,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h99 : NoPlan 6 s102 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v78 : Wire := ⟨0xedf3f6bf3f8#55,0x2c90000361b27a#55⟩
def s103 : List Wire := [v78,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h100 : NoPlan 6 s103 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s104 : List Wire := [v78,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h101 : NoPlan 6 s104 := banBySearch (by decide +kernel) (by decide +kernel)
def v79 : Wire := ⟨0x4180041b0#55,0x3a#55⟩
def s105 : List Wire := [v79,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h102 : NoPlan 6 s105 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s106 : List Wire := [v79,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h103 : NoPlan 6 s106 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v80 : Wire := ⟨0xcd8226b8200#55,0x2c90000361b240#55⟩
def s107 : List Wire := [v80,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h104 : NoPlan 6 s107 := banBySearch (by decide +kernel) (by decide +kernel)
def s108 : List Wire := [v80,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h105 : NoPlan 6 s108 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def v81 : Wire := ⟨0x20509005090#55,0x0#55⟩
def s109 : List Wire := [v81,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h106 : NoPlan 6 s109 := viaSymmetry perm2 inv2 invId2 h98 (by decide +kernel)
def s110 : List Wire := [v81,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h107 : NoPlan 6 s110 := viaSymmetry perm2 inv2 invId2 h99 (by decide +kernel)
def v82 : Wire := ⟨0xf6f5fb6f5f8#55,0x35200003a654ba#55⟩
def s111 : List Wire := [v82,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h108 : NoPlan 6 s111 := viaSymmetry perm2 inv2 invId2 h100 (by decide +kernel)
def s112 : List Wire := [v82,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h109 : NoPlan 6 s112 := viaSymmetry perm2 inv2 invId2 h101 (by decide +kernel)
def v83 : Wire := ⟨0x214002168#55,0x3a#55⟩
def s113 : List Wire := [v83,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h110 : NoPlan 6 s113 := viaSymmetry perm2 inv2 invId2 h102 (by decide +kernel)
def s114 : List Wire := [v83,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h111 : NoPlan 6 s114 := viaSymmetry perm2 inv2 invId2 h103 (by decide +kernel)
def v84 : Wire := ⟨0xd6842b68400#55,0x35200003a65480#55⟩
def s115 : List Wire := [v84,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h112 : NoPlan 6 s115 := viaSymmetry perm2 inv2 invId2 h104 (by decide +kernel)
def s116 : List Wire := [v84,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h113 : NoPlan 6 s116 := viaSymmetry perm2 inv2 invId2 h105 (by decide +kernel)
def v85 : Wire := ⟨0x20611006120#55,0x0#55⟩
def s117 : List Wire := [v85,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h114 : NoPlan 6 s117 := viaSymmetry perm4 inv4 invId4 h98 (by decide +kernel)
def s118 : List Wire := [v85,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h115 : NoPlan 6 s118 := viaSymmetry perm4 inv4 invId4 h99 (by decide +kernel)
def v86 : Wire := ⟨0xfb79fdd79f8#55,0x3a400003d8693a#55⟩
def s119 : List Wire := [v86,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h116 : NoPlan 6 s119 := viaSymmetry perm4 inv4 invId4 h100 (by decide +kernel)
def s120 : List Wire := [v86,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h117 : NoPlan 6 s120 := viaSymmetry perm4 inv4 invId4 h101 (by decide +kernel)
def v87 : Wire := ⟨0x10c0010d8#55,0x3a#55⟩
def s121 : List Wire := [v87,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h118 : NoPlan 6 s121 := viaSymmetry perm4 inv4 invId4 h102 (by decide +kernel)
def s122 : List Wire := [v87,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h119 : NoPlan 6 s122 := viaSymmetry perm4 inv4 invId4 h103 (by decide +kernel)
def v88 : Wire := ⟨0xdb082dd0800#55,0x3a400003d86900#55⟩
def s123 : List Wire := [v88,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h120 : NoPlan 6 s123 := viaSymmetry perm4 inv4 invId4 h104 (by decide +kernel)
def s124 : List Wire := [v88,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h121 : NoPlan 6 s124 := viaSymmetry perm4 inv4 invId4 h105 (by decide +kernel)
def s125 : List Wire := [v12,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h122 : NoPlan 6 s125 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s126 : List Wire := [v12,v16,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h123 : NoPlan 6 s126 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s127 : List Wire := [v12,v16,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h124 : NoPlan 6 s127 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s128 : List Wire := [v37,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h125 : NoPlan 6 s128 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s129 : List Wire := [v38,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h126 : NoPlan 6 s129 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s130 : List Wire := [v39,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h127 : NoPlan 6 s130 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s131 : List Wire := [v40,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h128 : NoPlan 6 s131 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s132 : List Wire := [v41,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h129 : NoPlan 6 s132 := viaSymmetry perm2 inv2 invId2 h125 (by decide +kernel)
def s133 : List Wire := [v42,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h130 : NoPlan 6 s133 := viaSymmetry perm2 inv2 invId2 h126 (by decide +kernel)
def s134 : List Wire := [v43,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h131 : NoPlan 6 s134 := viaSymmetry perm2 inv2 invId2 h127 (by decide +kernel)
def s135 : List Wire := [v44,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h132 : NoPlan 6 s135 := viaSymmetry perm2 inv2 invId2 h128 (by decide +kernel)
def s136 : List Wire := [v45,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h133 : NoPlan 6 s136 := viaSymmetry perm4 inv4 invId4 h125 (by decide +kernel)
def s137 : List Wire := [v46,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h134 : NoPlan 6 s137 := viaSymmetry perm4 inv4 invId4 h126 (by decide +kernel)
def s138 : List Wire := [v47,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h135 : NoPlan 6 s138 := viaSymmetry perm4 inv4 invId4 h127 (by decide +kernel)
def s139 : List Wire := [v48,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h136 : NoPlan 6 s139 := viaSymmetry perm4 inv4 invId4 h128 (by decide +kernel)
def s140 : List Wire := [v49,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h137 : NoPlan 6 s140 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s141 : List Wire := [v50,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h138 : NoPlan 6 s141 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s142 : List Wire := [v51,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h139 : NoPlan 6 s142 := banBySearch (by decide +kernel) (by decide +kernel)
def s143 : List Wire := [v52,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h140 : NoPlan 6 s143 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s144 : List Wire := [v53,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h141 : NoPlan 6 s144 := viaSymmetry perm2 inv2 invId2 h137 (by decide +kernel)
def s145 : List Wire := [v54,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h142 : NoPlan 6 s145 := viaSymmetry perm2 inv2 invId2 h138 (by decide +kernel)
def s146 : List Wire := [v55,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h143 : NoPlan 6 s146 := viaSymmetry perm2 inv2 invId2 h139 (by decide +kernel)
def s147 : List Wire := [v56,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h144 : NoPlan 6 s147 := viaSymmetry perm2 inv2 invId2 h140 (by decide +kernel)
def s148 : List Wire := [v57,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h145 : NoPlan 6 s148 := viaSymmetry perm4 inv4 invId4 h137 (by decide +kernel)
def s149 : List Wire := [v58,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h146 : NoPlan 6 s149 := viaSymmetry perm4 inv4 invId4 h138 (by decide +kernel)
def s150 : List Wire := [v59,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h147 : NoPlan 6 s150 := viaSymmetry perm4 inv4 invId4 h139 (by decide +kernel)
def s151 : List Wire := [v60,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h148 : NoPlan 6 s151 := viaSymmetry perm4 inv4 invId4 h140 (by decide +kernel)
def s152 : List Wire := [v61,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h149 : NoPlan 6 s152 := banBySearch (by decide +kernel) (by decide +kernel)
def s153 : List Wire := [v66,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h150 : NoPlan 6 s153 := banBySearch (by decide +kernel) (by decide +kernel)
def s154 : List Wire := [v67,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h151 : NoPlan 6 s154 := banBySearch (by decide +kernel) (by decide +kernel)
def s155 : List Wire := [v68,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h152 : NoPlan 6 s155 := viaSymmetry perm2 inv2 invId2 h151 (by decide +kernel)
def s156 : List Wire := [v69,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h153 : NoPlan 6 s156 := viaSymmetry perm1 inv1 invId1 h149 (by decide +kernel)
def s157 : List Wire := [v70,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h154 : NoPlan 6 s157 := viaSymmetry perm1 inv1 invId1 h150 (by decide +kernel)
def s158 : List Wire := [v71,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h155 : NoPlan 6 s158 := viaSymmetry perm1 inv1 invId1 h151 (by decide +kernel)
def s159 : List Wire := [v72,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h156 : NoPlan 6 s159 := viaSymmetry perm4 inv4 invId4 h151 (by decide +kernel)
def s160 : List Wire := [v73,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h157 : NoPlan 6 s160 := viaSymmetry perm3 inv3 invId3 h149 (by decide +kernel)
def s161 : List Wire := [v74,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h158 : NoPlan 6 s161 := viaSymmetry perm3 inv3 invId3 h150 (by decide +kernel)
def s162 : List Wire := [v75,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h159 : NoPlan 6 s162 := viaSymmetry perm3 inv3 invId3 h151 (by decide +kernel)
def s163 : List Wire := [v76,v16,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h160 : NoPlan 6 s163 := viaSymmetry perm5 inv5 invId5 h151 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h91 : NoPlan 7 s9 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s9 = [s97,s1,s98,s99,s3,s100,s101,s102,s103,s104,s105,s106,s107,s108,s109,s110,s111,s112,s113,s114,s115,s116,s117,s118,s119,s120,s121,s122,s123,s124,s97,s98,s99,s100,s125,s126,s127,s128,s129,s130,s131,s132,s133,s134,s135,s136,s137,s138,s139,s140,s141,s142,s143,s144,s145,s146,s147,s148,s149,s150,s151,s152,s153,s154,s155,s156,s157,s158,s159,s160,s161,s162,s163] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h92,h93,h94,h95,h96,h97,h98,h99,h100,h101,h102,h103,h104,h105,h106,h107,h108,h109,h110,h111,h112,h113,h114,h115,h116,h117,h118,h119,h120,h121,h92,h94,h95,h97,h122,h123,h124,h125,h126,h127,h128,h129,h130,h131,h132,h133,h134,h135,h136,h137,h138,h139,h140,h141,h142,h143,h144,h145,h146,h147,h148,h149,h150,h151,h152,h153,h154,h155,h156,h157,h158,h159,h160⟩
def s164 : List Wire := [v11,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h162 : NoPlan 6 s164 := by unfold NoPlan at *; rw [show s164.toFinset=s4.toFinset by decide +kernel]; exact h3
def s165 : List Wire := [v11,v12,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h163 : NoPlan 6 s165 := by unfold NoPlan at *; rw [show s165.toFinset=s7.toFinset by decide +kernel]; exact h5
def s166 : List Wire := [v5,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h164 : NoPlan 6 s166 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s167 : List Wire := [v5,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h165 : NoPlan 6 s167 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v89 : Wire := ⟨0x418026b8000#55,0x800000018200#55⟩
def s168 : List Wire := [v89,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h166 : NoPlan 6 s168 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s169 : List Wire := [v89,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h167 : NoPlan 6 s169 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def v90 : Wire := ⟨0xefb27ffb248#55,0x2f9000037fbe44#55⟩
def s170 : List Wire := [v90,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h168 : NoPlan 6 s170 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s171 : List Wire := [v90,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h169 : NoPlan 6 s171 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v91 : Wire := ⟨0x2000940000#55,0x30000001e0c04#55⟩
def s172 : List Wire := [v91,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h170 : NoPlan 6 s172 := banBySearch (by decide +kernel) (by decide +kernel)
def s173 : List Wire := [v91,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h171 : NoPlan 6 s173 := banBySearch (by decide +kernel) (by decide +kernel)
def v92 : Wire := ⟨0xac325003248#55,0x2c100003603040#55⟩
def s174 : List Wire := [v92,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h172 : NoPlan 6 s174 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s175 : List Wire := [v92,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h173 : NoPlan 6 s175 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v93 : Wire := ⟨0x42802b68000#55,0x1000000060400#55⟩
def s176 : List Wire := [v93,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h174 : NoPlan 6 s176 := viaSymmetry perm2 inv2 invId2 h166 (by decide +kernel)
def s177 : List Wire := [v93,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h175 : NoPlan 6 s177 := viaSymmetry perm2 inv2 invId2 h167 (by decide +kernel)
def v94 : Wire := ⟨0xf7d4bffd490#55,0x37a00003bfde84#55⟩
def s178 : List Wire := [v94,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h176 : NoPlan 6 s178 := viaSymmetry perm2 inv2 invId2 h168 (by decide +kernel)
def s179 : List Wire := [v94,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h177 : NoPlan 6 s179 := viaSymmetry perm2 inv2 invId2 h169 (by decide +kernel)
def v95 : Wire := ⟨0x1000490000#55,0x2800000198a04#55⟩
def s180 : List Wire := [v95,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h178 : NoPlan 6 s180 := viaSymmetry perm2 inv2 invId2 h170 (by decide +kernel)
def s181 : List Wire := [v95,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h179 : NoPlan 6 s181 := viaSymmetry perm2 inv2 invId2 h171 (by decide +kernel)
def v96 : Wire := ⟨0xb4549005490#55,0x34200003a05080#55⟩
def s182 : List Wire := [v96,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h180 : NoPlan 6 s182 := viaSymmetry perm2 inv2 invId2 h172 (by decide +kernel)
def s183 : List Wire := [v96,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h181 : NoPlan 6 s183 := viaSymmetry perm2 inv2 invId2 h173 (by decide +kernel)
def v97 : Wire := ⟨0x43002dd0000#55,0x2000000180800#55⟩
def s184 : List Wire := [v97,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h182 : NoPlan 6 s184 := viaSymmetry perm4 inv4 invId4 h166 (by decide +kernel)
def s185 : List Wire := [v97,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h183 : NoPlan 6 s185 := viaSymmetry perm4 inv4 invId4 h167 (by decide +kernel)
def v98 : Wire := ⟨0xfbe93ffe920#55,0x3bc00003dfef04#55⟩
def s186 : List Wire := [v98,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h184 : NoPlan 6 s186 := viaSymmetry perm4 inv4 invId4 h168 (by decide +kernel)
def s187 : List Wire := [v98,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h185 : NoPlan 6 s187 := viaSymmetry perm4 inv4 invId4 h169 (by decide +kernel)
def v99 : Wire := ⟨0x800228000#55,0x1800000078604#55⟩
def s188 : List Wire := [v99,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h186 : NoPlan 6 s188 := viaSymmetry perm4 inv4 invId4 h170 (by decide +kernel)
def s189 : List Wire := [v99,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h187 : NoPlan 6 s189 := viaSymmetry perm4 inv4 invId4 h171 (by decide +kernel)
def v100 : Wire := ⟨0xb8691006920#55,0x38400003c06100#55⟩
def s190 : List Wire := [v100,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h188 : NoPlan 6 s190 := viaSymmetry perm4 inv4 invId4 h172 (by decide +kernel)
def s191 : List Wire := [v100,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h189 : NoPlan 6 s191 := viaSymmetry perm4 inv4 invId4 h173 (by decide +kernel)
def s192 : List Wire := [v16,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h190 : NoPlan 6 s192 := by unfold NoPlan at *; rw [show s192.toFinset=s125.toFinset by decide +kernel]; exact h122
def s193 : List Wire := [v16,v12,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h191 : NoPlan 6 s193 := by unfold NoPlan at *; rw [show s193.toFinset=s126.toFinset by decide +kernel]; exact h123
def s194 : List Wire := [v16,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h192 : NoPlan 6 s194 := by unfold NoPlan at *; rw [show s194.toFinset=s127.toFinset by decide +kernel]; exact h124
def s195 : List Wire := [v37,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h193 : NoPlan 6 s195 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s196 : List Wire := [v38,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h194 : NoPlan 6 s196 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s197 : List Wire := [v39,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h195 : NoPlan 6 s197 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s198 : List Wire := [v40,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h196 : NoPlan 6 s198 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s199 : List Wire := [v41,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h197 : NoPlan 6 s199 := viaSymmetry perm2 inv2 invId2 h193 (by decide +kernel)
def s200 : List Wire := [v42,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h198 : NoPlan 6 s200 := viaSymmetry perm2 inv2 invId2 h194 (by decide +kernel)
def s201 : List Wire := [v43,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h199 : NoPlan 6 s201 := viaSymmetry perm2 inv2 invId2 h195 (by decide +kernel)
def s202 : List Wire := [v44,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h200 : NoPlan 6 s202 := viaSymmetry perm2 inv2 invId2 h196 (by decide +kernel)
def s203 : List Wire := [v45,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h201 : NoPlan 6 s203 := viaSymmetry perm4 inv4 invId4 h193 (by decide +kernel)
def s204 : List Wire := [v46,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h202 : NoPlan 6 s204 := viaSymmetry perm4 inv4 invId4 h194 (by decide +kernel)
def s205 : List Wire := [v47,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h203 : NoPlan 6 s205 := viaSymmetry perm4 inv4 invId4 h195 (by decide +kernel)
def s206 : List Wire := [v48,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h204 : NoPlan 6 s206 := viaSymmetry perm4 inv4 invId4 h196 (by decide +kernel)
def s207 : List Wire := [v49,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h205 : NoPlan 6 s207 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s208 : List Wire := [v50,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h206 : NoPlan 6 s208 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s209 : List Wire := [v50,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h207 : NoPlan 6 s209 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s210 : List Wire := [v51,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h208 : NoPlan 6 s210 := banBySearch (by decide +kernel) (by decide +kernel)
def s211 : List Wire := [v51,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h209 : NoPlan 6 s211 := banBySearch (by decide +kernel) (by decide +kernel)
def s212 : List Wire := [v52,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h210 : NoPlan 6 s212 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s213 : List Wire := [v53,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h211 : NoPlan 6 s213 := viaSymmetry perm2 inv2 invId2 h205 (by decide +kernel)
def s214 : List Wire := [v54,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h212 : NoPlan 6 s214 := viaSymmetry perm2 inv2 invId2 h206 (by decide +kernel)
def s215 : List Wire := [v54,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h213 : NoPlan 6 s215 := viaSymmetry perm2 inv2 invId2 h207 (by decide +kernel)
def s216 : List Wire := [v55,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h214 : NoPlan 6 s216 := viaSymmetry perm2 inv2 invId2 h208 (by decide +kernel)
def s217 : List Wire := [v55,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h215 : NoPlan 6 s217 := viaSymmetry perm2 inv2 invId2 h209 (by decide +kernel)
def s218 : List Wire := [v56,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h216 : NoPlan 6 s218 := viaSymmetry perm2 inv2 invId2 h210 (by decide +kernel)
def s219 : List Wire := [v57,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h217 : NoPlan 6 s219 := viaSymmetry perm4 inv4 invId4 h205 (by decide +kernel)
def s220 : List Wire := [v58,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h218 : NoPlan 6 s220 := viaSymmetry perm4 inv4 invId4 h206 (by decide +kernel)
def s221 : List Wire := [v58,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h219 : NoPlan 6 s221 := viaSymmetry perm4 inv4 invId4 h207 (by decide +kernel)
def s222 : List Wire := [v59,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h220 : NoPlan 6 s222 := viaSymmetry perm4 inv4 invId4 h208 (by decide +kernel)
def s223 : List Wire := [v59,v12,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h221 : NoPlan 6 s223 := viaSymmetry perm4 inv4 invId4 h209 (by decide +kernel)
def s224 : List Wire := [v60,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h222 : NoPlan 6 s224 := viaSymmetry perm4 inv4 invId4 h210 (by decide +kernel)
def s225 : List Wire := [v61,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h223 : NoPlan 6 s225 := banBySearch (by decide +kernel) (by decide +kernel)
def s226 : List Wire := [v66,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h224 : NoPlan 6 s226 := banBySearch (by decide +kernel) (by decide +kernel)
def s227 : List Wire := [v67,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h225 : NoPlan 6 s227 := banBySearch (by decide +kernel) (by decide +kernel)
def s228 : List Wire := [v68,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h226 : NoPlan 6 s228 := viaSymmetry perm2 inv2 invId2 h225 (by decide +kernel)
def s229 : List Wire := [v69,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h227 : NoPlan 6 s229 := viaSymmetry perm1 inv1 invId1 h223 (by decide +kernel)
def s230 : List Wire := [v70,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h228 : NoPlan 6 s230 := viaSymmetry perm1 inv1 invId1 h224 (by decide +kernel)
def s231 : List Wire := [v71,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h229 : NoPlan 6 s231 := viaSymmetry perm1 inv1 invId1 h225 (by decide +kernel)
def s232 : List Wire := [v72,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h230 : NoPlan 6 s232 := viaSymmetry perm4 inv4 invId4 h225 (by decide +kernel)
def s233 : List Wire := [v73,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h231 : NoPlan 6 s233 := viaSymmetry perm3 inv3 invId3 h223 (by decide +kernel)
def s234 : List Wire := [v74,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h232 : NoPlan 6 s234 := viaSymmetry perm3 inv3 invId3 h224 (by decide +kernel)
def s235 : List Wire := [v75,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h233 : NoPlan 6 s235 := viaSymmetry perm3 inv3 invId3 h225 (by decide +kernel)
def s236 : List Wire := [v76,v12,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h234 : NoPlan 6 s236 := viaSymmetry perm5 inv5 invId5 h225 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h161 : NoPlan 7 s5 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s5 = [s164,s3,s165,s166,s1,s167,s168,s169,s170,s171,s172,s173,s174,s175,s176,s177,s178,s179,s180,s181,s182,s183,s184,s185,s186,s187,s188,s189,s190,s191,s166,s167,s164,s165,s192,s193,s194,s195,s196,s197,s198,s199,s200,s201,s202,s203,s204,s205,s206,s207,s208,s209,s210,s211,s212,s213,s214,s215,s216,s217,s218,s219,s220,s221,s222,s223,s224,s225,s226,s227,s228,s229,s230,s231,s232,s233,s234,s235,s236] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h162,h96,h163,h164,h93,h165,h166,h167,h168,h169,h170,h171,h172,h173,h174,h175,h176,h177,h178,h179,h180,h181,h182,h183,h184,h185,h186,h187,h188,h189,h164,h165,h162,h163,h190,h191,h192,h193,h194,h195,h196,h197,h198,h199,h200,h201,h202,h203,h204,h205,h206,h207,h208,h209,h210,h211,h212,h213,h214,h215,h216,h217,h218,h219,h220,h221,h222,h223,h224,h225,h226,h227,h228,h229,h230,h231,h232,h233,h234⟩
def s237 : List Wire := [v37,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p7 : s13.sublists.any (quick 5) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h235 : NoPlan 7 s237 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s238 : List Wire := [v38,v0,v1,v2,v3,v4]
def s239 : List Wire := [v40,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h237 : NoPlan 6 s239 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s240 : List Wire := [v40,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h238 : NoPlan 6 s240 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s241 : List Wire := [v40,v38,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h239 : NoPlan 6 s241 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def v101 : Wire := ⟨0x7ffdd8e26b8e07#55,0x800000018200#55⟩
def s242 : List Wire := [v101,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h240 : NoPlan 6 s242 := banBySearch (by decide +kernel) (by decide +kernel)
def s243 : List Wire := [v101,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h241 : NoPlan 6 s243 := banBySearch (by decide +kernel) (by decide +kernel)
def s244 : List Wire := [v22,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h242 : NoPlan 6 s244 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v102 : Wire := ⟨0x2071d0071f8#55,0x2c10000360307a#55⟩
def s245 : List Wire := [v102,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h243 : NoPlan 6 s245 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s246 : List Wire := [v102,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h244 : NoPlan 6 s246 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s247 : List Wire := [v91,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h245 : NoPlan 6 s247 := banBySearch (by decide +kernel) (by decide +kernel)
def s248 : List Wire := [v39,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h246 : NoPlan 6 s248 := banBySearch (by decide +kernel) (by decide +kernel)
def s249 : List Wire := [v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h247 : NoPlan 6 s249 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s250 : List Wire := [v39,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h248 : NoPlan 6 s250 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v103 : Wire := ⟨0xf4d4b22d490#55,0x24000003201000#55⟩
def s251 : List Wire := [v103,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h249 : NoPlan 6 s251 := banBySearch (by decide +kernel) (by decide +kernel)
def s252 : List Wire := [v103,v0,v1,v2,v3,v4]
def v104 : Wire := ⟨0x7fffefffb6ffff#55,0x2a#55⟩
def v105 : Wire := ⟨0x7ffffdebffde97#55,0x2800000090a04#55⟩
def v106 : Wire := ⟨0x9224492248#55,0x8900000412240#55⟩
def v107 : Wire := ⟨0x9290492920#55,0xa400000482900#55⟩
def s253 : List Wire := [v104,v105,v106,v107]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p8 : s253.sublists.any (quick 4) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h250 : NoPlan 6 s252 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v108 : Wire := ⟨0x7fffffffffffff#55,0x3db00003e7f6fa#55⟩
def s254 : List Wire := [v108,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h251 : NoPlan 6 s254 := banBySearch (by decide +kernel) (by decide +kernel)
def s255 : List Wire := [v108,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h252 : NoPlan 6 s255 := banBySearch (by decide +kernel) (by decide +kernel)
def v109 : Wire := ⟨0x7ff092b4492b6f#55,0x890000041a27a#55⟩
def s256 : List Wire := [v109,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h253 : NoPlan 6 s256 := banBySearch (by decide +kernel) (by decide +kernel)
def s257 : List Wire := [v109,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h254 : NoPlan 6 s257 := banBySearch (by decide +kernel) (by decide +kernel)
def v110 : Wire := ⟨0x2000940000#55,0x11200000864480#55⟩
def s258 : List Wire := [v110,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h255 : NoPlan 6 s258 := banBySearch (by decide +kernel) (by decide +kernel)
def s259 : List Wire := [v110,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h256 : NoPlan 6 s259 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v111 : Wire := ⟨0xf9693496920#55,0x28000003402000#55⟩
def s260 : List Wire := [v111,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h257 : NoPlan 6 s260 := viaSymmetry perm1 inv1 invId1 h249 (by decide +kernel)
def s261 : List Wire := [v111,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h258 : NoPlan 6 s261 := viaSymmetry perm1 inv1 invId1 h250 (by decide +kernel)
def v112 : Wire := ⟨0x7fffffffffffff#55,0x3ed00003f9fb7a#55⟩
def s262 : List Wire := [v112,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h259 : NoPlan 6 s262 := viaSymmetry perm1 inv1 invId1 h251 (by decide +kernel)
def s263 : List Wire := [v112,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h260 : NoPlan 6 s263 := viaSymmetry perm1 inv1 invId1 h252 (by decide +kernel)
def v113 : Wire := ⟨0x7ff0496c2296df#55,0x490000021927a#55⟩
def s264 : List Wire := [v113,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h261 : NoPlan 6 s264 := viaSymmetry perm1 inv1 invId1 h253 (by decide +kernel)
def s265 : List Wire := [v113,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h262 : NoPlan 6 s265 := viaSymmetry perm1 inv1 invId1 h254 (by decide +kernel)
def v114 : Wire := ⟨0x2000940000#55,0x12400000984900#55⟩
def s266 : List Wire := [v114,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h263 : NoPlan 6 s266 := viaSymmetry perm1 inv1 invId1 h255 (by decide +kernel)
def s267 : List Wire := [v114,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h264 : NoPlan 6 s267 := viaSymmetry perm1 inv1 invId1 h256 (by decide +kernel)
def s268 : List Wire := [v5,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h265 : NoPlan 6 s268 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s269 : List Wire := [v11,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h266 : NoPlan 6 s269 := by unfold NoPlan at *; rw [show s269.toFinset=s55.toFinset by decide +kernel]; exact h50
def s270 : List Wire := [v16,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h267 : NoPlan 6 s270 := by unfold NoPlan at *; rw [show s270.toFinset=s129.toFinset by decide +kernel]; exact h126
def s271 : List Wire := [v12,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h268 : NoPlan 6 s271 := by unfold NoPlan at *; rw [show s271.toFinset=s196.toFinset by decide +kernel]; exact h194
def s272 : List Wire := [v37,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h269 : NoPlan 6 s272 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s273 : List Wire := [v37,v38,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h270 : NoPlan 6 s273 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s274 : List Wire := [v37,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h271 : NoPlan 6 s274 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s275 : List Wire := [v41,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h272 : NoPlan 6 s275 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s276 : List Wire := [v42,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h273 : NoPlan 6 s276 := banBySearch (by decide +kernel) (by decide +kernel)
def s277 : List Wire := [v43,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h274 : NoPlan 6 s277 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s278 : List Wire := [v44,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h275 : NoPlan 6 s278 := banBySearch (by decide +kernel) (by decide +kernel)
def s279 : List Wire := [v45,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h276 : NoPlan 6 s279 := viaSymmetry perm1 inv1 invId1 h272 (by decide +kernel)
def s280 : List Wire := [v46,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h277 : NoPlan 6 s280 := viaSymmetry perm1 inv1 invId1 h273 (by decide +kernel)
def s281 : List Wire := [v47,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h278 : NoPlan 6 s281 := viaSymmetry perm1 inv1 invId1 h274 (by decide +kernel)
def s282 : List Wire := [v48,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h279 : NoPlan 6 s282 := viaSymmetry perm1 inv1 invId1 h275 (by decide +kernel)
def s283 : List Wire := [v49,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h280 : NoPlan 6 s283 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s284 : List Wire := [v50,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h281 : NoPlan 6 s284 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s285 : List Wire := [v50,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h282 : NoPlan 6 s285 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s286 : List Wire := [v51,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h283 : NoPlan 6 s286 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s287 : List Wire := [v52,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h284 : NoPlan 6 s287 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s288 : List Wire := [v52,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h285 : NoPlan 6 s288 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s289 : List Wire := [v53,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h286 : NoPlan 6 s289 := banBySearch (by decide +kernel) (by decide +kernel)
def s290 : List Wire := [v54,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h287 : NoPlan 6 s290 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s291 : List Wire := [v55,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h288 : NoPlan 6 s291 := banBySearch (by decide +kernel) (by decide +kernel)
def s292 : List Wire := [v56,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h289 : NoPlan 6 s292 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s293 : List Wire := [v57,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h290 : NoPlan 6 s293 := viaSymmetry perm1 inv1 invId1 h286 (by decide +kernel)
def s294 : List Wire := [v58,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h291 : NoPlan 6 s294 := viaSymmetry perm1 inv1 invId1 h287 (by decide +kernel)
def s295 : List Wire := [v59,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h292 : NoPlan 6 s295 := viaSymmetry perm1 inv1 invId1 h288 (by decide +kernel)
def s296 : List Wire := [v60,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h293 : NoPlan 6 s296 := viaSymmetry perm1 inv1 invId1 h289 (by decide +kernel)
def s297 : List Wire := [v61,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h294 : NoPlan 6 s297 := banBySearch (by decide +kernel) (by decide +kernel)
def s298 : List Wire := [v66,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h295 : NoPlan 6 s298 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s299 : List Wire := [v66,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h296 : NoPlan 6 s299 := banBySearch (by decide +kernel) (by decide +kernel)
def s300 : List Wire := [v67,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h297 : NoPlan 6 s300 := banBySearch (by decide +kernel) (by decide +kernel)
def s301 : List Wire := [v67,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h298 : NoPlan 6 s301 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s302 : List Wire := [v68,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h299 : NoPlan 6 s302 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s303 : List Wire := [v69,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h300 : NoPlan 6 s303 := viaSymmetry perm1 inv1 invId1 h294 (by decide +kernel)
def s304 : List Wire := [v70,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h301 : NoPlan 6 s304 := viaSymmetry perm1 inv1 invId1 h295 (by decide +kernel)
def s305 : List Wire := [v70,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h302 : NoPlan 6 s305 := viaSymmetry perm1 inv1 invId1 h296 (by decide +kernel)
def s306 : List Wire := [v71,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h303 : NoPlan 6 s306 := viaSymmetry perm1 inv1 invId1 h297 (by decide +kernel)
def s307 : List Wire := [v71,v38,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h304 : NoPlan 6 s307 := viaSymmetry perm1 inv1 invId1 h298 (by decide +kernel)
def s308 : List Wire := [v72,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h305 : NoPlan 6 s308 := viaSymmetry perm1 inv1 invId1 h299 (by decide +kernel)
def s309 : List Wire := [v73,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h306 : NoPlan 6 s309 := banBySearch (by decide +kernel) (by decide +kernel)
def s310 : List Wire := [v74,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h307 : NoPlan 6 s310 := banBySearch (by decide +kernel) (by decide +kernel)
def s311 : List Wire := [v75,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h308 : NoPlan 6 s311 := banBySearch (by decide +kernel) (by decide +kernel)
def s312 : List Wire := [v76,v38,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h309 : NoPlan 6 s312 := viaSymmetry perm1 inv1 invId1 h308 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h236 : NoPlan 7 s238 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s238 = [s239,s240,s241,s242,s243,s244,s17,s245,s246,s247,s173,s248,s249,s250,s251,s252,s254,s255,s256,s257,s258,s259,s260,s261,s262,s263,s264,s265,s266,s267,s268,s269,s270,s271,s272,s273,s274,s248,s250,s239,s241,s275,s276,s277,s278,s279,s280,s281,s282,s283,s284,s285,s286,s287,s288,s289,s290,s291,s292,s293,s294,s295,s296,s297,s298,s299,s300,s301,s302,s303,s304,s305,s306,s307,s308,s309,s310,s311,s312] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h237,h238,h239,h240,h241,h242,h14,h243,h244,h245,h171,h246,h247,h248,h249,h250,h251,h252,h253,h254,h255,h256,h257,h258,h259,h260,h261,h262,h263,h264,h265,h266,h267,h268,h269,h270,h271,h246,h248,h237,h239,h272,h273,h274,h275,h276,h277,h278,h279,h280,h281,h282,h283,h284,h285,h286,h287,h288,h289,h290,h291,h292,h293,h294,h295,h296,h297,h298,h299,h300,h301,h302,h303,h304,h305,h306,h307,h308,h309⟩
def s313 : List Wire := [v37,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h311 : NoPlan 6 s313 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h312 : NoPlan 6 s237 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s314 : List Wire := [v37,v39,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h313 : NoPlan 6 s314 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v115 : Wire := ⟨0x7ff100c0000c07#55,0x0#55⟩
def s315 : List Wire := [v115,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h314 : NoPlan 6 s315 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s316 : List Wire := [v115,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h315 : NoPlan 6 s316 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v116 : Wire := ⟨0x7ffdfcfaffcfb7#55,0x38000001f8e3e#55⟩
def s317 : List Wire := [v116,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h316 : NoPlan 6 s317 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s318 : List Wire := [v116,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h317 : NoPlan 6 s318 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s319 : List Wire := [v79,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h318 : NoPlan 6 s319 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def v117 : Wire := ⟨0xcf822ff8200#55,0x38000001f8e04#55⟩
def s320 : List Wire := [v117,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h319 : NoPlan 6 s320 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s321 : List Wire := [v117,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h320 : NoPlan 6 s321 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s322 : List Wire := [v38,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h321 : NoPlan 6 s322 := by unfold NoPlan at *; rw [show s322.toFinset=s248.toFinset by decide +kernel]; exact h246
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h322 : NoPlan 6 s238 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s323 : List Wire := [v38,v39,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h323 : NoPlan 6 s323 := by unfold NoPlan at *; rw [show s323.toFinset=s250.toFinset by decide +kernel]; exact h248
def v118 : Wire := ⟨0x10448004490#55,0x0#55⟩
def s324 : List Wire := [v118,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h324 : NoPlan 6 s324 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s325 : List Wire := [v118,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h325 : NoPlan 6 s325 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v119 : Wire := ⟨0x7fff6ddbb6ddb7#55,0x35200003a654ba#55⟩
def s326 : List Wire := [v119,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h326 : NoPlan 6 s326 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s327 : List Wire := [v119,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h327 : NoPlan 6 s327 := banBySearch (by decide +kernel) (by decide +kernel)
def v120 : Wire := ⟨0x7ff00090000927#55,0x3a#55⟩
def s328 : List Wire := [v120,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h328 : NoPlan 6 s328 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s329 : List Wire := [v120,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h329 : NoPlan 6 s329 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v121 : Wire := ⟨0xe6903b69000#55,0x35200003a65480#55⟩
def s330 : List Wire := [v121,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h330 : NoPlan 6 s330 := banBySearch (by decide +kernel) (by decide +kernel)
def s331 : List Wire := [v121,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h331 : NoPlan 6 s331 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v122 : Wire := ⟨0x10490004920#55,0x0#55⟩
def s332 : List Wire := [v122,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h332 : NoPlan 6 s332 := viaSymmetry perm1 inv1 invId1 h324 (by decide +kernel)
def s333 : List Wire := [v122,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h333 : NoPlan 6 s333 := viaSymmetry perm1 inv1 invId1 h325 (by decide +kernel)
def v123 : Wire := ⟨0x7fffb6dbdd6db7#55,0x3a400003d8693a#55⟩
def s334 : List Wire := [v123,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h334 : NoPlan 6 s334 := viaSymmetry perm1 inv1 invId1 h326 (by decide +kernel)
def s335 : List Wire := [v123,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h335 : NoPlan 6 s335 := viaSymmetry perm1 inv1 invId1 h327 (by decide +kernel)
def v124 : Wire := ⟨0x7ff00048000497#55,0x3a#55⟩
def s336 : List Wire := [v124,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h336 : NoPlan 6 s336 := viaSymmetry perm1 inv1 invId1 h328 (by decide +kernel)
def s337 : List Wire := [v124,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h337 : NoPlan 6 s337 := viaSymmetry perm1 inv1 invId1 h329 (by decide +kernel)
def v125 : Wire := ⟨0xeb203dd2000#55,0x3a400003d86900#55⟩
def s338 : List Wire := [v125,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h338 : NoPlan 6 s338 := viaSymmetry perm1 inv1 invId1 h330 (by decide +kernel)
def s339 : List Wire := [v125,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h339 : NoPlan 6 s339 := viaSymmetry perm1 inv1 invId1 h331 (by decide +kernel)
def s340 : List Wire := [v5,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h340 : NoPlan 6 s340 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s341 : List Wire := [v11,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h341 : NoPlan 6 s341 := by unfold NoPlan at *; rw [show s341.toFinset=s56.toFinset by decide +kernel]; exact h51
def s342 : List Wire := [v16,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h342 : NoPlan 6 s342 := by unfold NoPlan at *; rw [show s342.toFinset=s130.toFinset by decide +kernel]; exact h127
def s343 : List Wire := [v12,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h343 : NoPlan 6 s343 := by unfold NoPlan at *; rw [show s343.toFinset=s197.toFinset by decide +kernel]; exact h195
def s344 : List Wire := [v40,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h344 : NoPlan 6 s344 := banBySearch (by decide +kernel) (by decide +kernel)
def s345 : List Wire := [v40,v39,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h345 : NoPlan 6 s345 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s346 : List Wire := [v40,v39,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h346 : NoPlan 6 s346 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s347 : List Wire := [v41,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h347 : NoPlan 6 s347 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s348 : List Wire := [v42,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h348 : NoPlan 6 s348 := viaSymmetry perm2 inv2 invId2 h274 (by decide +kernel)
def s349 : List Wire := [v43,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h349 : NoPlan 6 s349 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s350 : List Wire := [v44,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h350 : NoPlan 6 s350 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s351 : List Wire := [v45,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h351 : NoPlan 6 s351 := viaSymmetry perm1 inv1 invId1 h347 (by decide +kernel)
def s352 : List Wire := [v46,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h352 : NoPlan 6 s352 := viaSymmetry perm4 inv4 invId4 h274 (by decide +kernel)
def s353 : List Wire := [v47,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h353 : NoPlan 6 s353 := viaSymmetry perm1 inv1 invId1 h349 (by decide +kernel)
def s354 : List Wire := [v48,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h354 : NoPlan 6 s354 := viaSymmetry perm1 inv1 invId1 h350 (by decide +kernel)
def s355 : List Wire := [v49,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h355 : NoPlan 6 s355 := banBySearch (by decide +kernel) (by decide +kernel)
def s356 : List Wire := [v49,v39,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h356 : NoPlan 6 s356 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s357 : List Wire := [v50,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h357 : NoPlan 6 s357 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s358 : List Wire := [v51,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h358 : NoPlan 6 s358 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s359 : List Wire := [v51,v39,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h359 : NoPlan 6 s359 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s21) (budget:=3) (by decide +kernel) p4 (by decide +kernel) (by decide +kernel)
def s360 : List Wire := [v52,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h360 : NoPlan 6 s360 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s361 : List Wire := [v53,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h361 : NoPlan 6 s361 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s362 : List Wire := [v54,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h362 : NoPlan 6 s362 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s363 : List Wire := [v55,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h363 : NoPlan 6 s363 := banBySearch (by decide +kernel) (by decide +kernel)
def s364 : List Wire := [v56,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h364 : NoPlan 6 s364 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s365 : List Wire := [v57,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h365 : NoPlan 6 s365 := viaSymmetry perm1 inv1 invId1 h361 (by decide +kernel)
def s366 : List Wire := [v58,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h366 : NoPlan 6 s366 := viaSymmetry perm1 inv1 invId1 h362 (by decide +kernel)
def s367 : List Wire := [v59,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h367 : NoPlan 6 s367 := viaSymmetry perm1 inv1 invId1 h363 (by decide +kernel)
def s368 : List Wire := [v60,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h368 : NoPlan 6 s368 := viaSymmetry perm1 inv1 invId1 h364 (by decide +kernel)
def s369 : List Wire := [v61,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h369 : NoPlan 6 s369 := banBySearch (by decide +kernel) (by decide +kernel)
def s370 : List Wire := [v66,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h370 : NoPlan 6 s370 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s371 : List Wire := [v67,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h371 : NoPlan 6 s371 := banBySearch (by decide +kernel) (by decide +kernel)
def s372 : List Wire := [v68,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h372 : NoPlan 6 s372 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s373 : List Wire := [v69,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h373 : NoPlan 6 s373 := viaSymmetry perm1 inv1 invId1 h369 (by decide +kernel)
def s374 : List Wire := [v70,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h374 : NoPlan 6 s374 := viaSymmetry perm1 inv1 invId1 h370 (by decide +kernel)
def s375 : List Wire := [v71,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h375 : NoPlan 6 s375 := viaSymmetry perm1 inv1 invId1 h371 (by decide +kernel)
def s376 : List Wire := [v72,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h376 : NoPlan 6 s376 := viaSymmetry perm1 inv1 invId1 h372 (by decide +kernel)
def s377 : List Wire := [v73,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h377 : NoPlan 6 s377 := banBySearch (by decide +kernel) (by decide +kernel)
def s378 : List Wire := [v74,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h378 : NoPlan 6 s378 := banBySearch (by decide +kernel) (by decide +kernel)
def s379 : List Wire := [v75,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h379 : NoPlan 6 s379 := banBySearch (by decide +kernel) (by decide +kernel)
def s380 : List Wire := [v76,v39,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h380 : NoPlan 6 s380 := viaSymmetry perm1 inv1 invId1 h379 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h310 : NoPlan 7 s249 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s249 = [s313,s237,s314,s315,s316,s317,s318,s319,s106,s320,s321,s322,s238,s323,s324,s325,s326,s327,s328,s329,s330,s331,s332,s333,s334,s335,s336,s337,s338,s339,s340,s341,s342,s343,s313,s314,s322,s323,s344,s345,s346,s347,s348,s349,s350,s351,s352,s353,s354,s355,s356,s357,s358,s359,s360,s361,s362,s363,s364,s365,s366,s367,s368,s369,s370,s371,s372,s373,s374,s375,s376,s377,s378,s379,s380] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h311,h312,h313,h314,h315,h316,h317,h318,h103,h319,h320,h321,h322,h323,h324,h325,h326,h327,h328,h329,h330,h331,h332,h333,h334,h335,h336,h337,h338,h339,h340,h341,h342,h343,h311,h313,h321,h323,h344,h345,h346,h347,h348,h349,h350,h351,h352,h353,h354,h355,h356,h357,h358,h359,h360,h361,h362,h363,h364,h365,h366,h367,h368,h369,h370,h371,h372,h373,h374,h375,h376,h377,h378,h379,h380⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h381 : NoPlan 7 s240 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s381 : List Wire := [v41,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h382 : NoPlan 7 s381 := viaSymmetry perm2 inv2 invId2 h235 (by decide +kernel)
def s382 : List Wire := [v42,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h383 : NoPlan 7 s382 := viaSymmetry perm2 inv2 invId2 h236 (by decide +kernel)
def s383 : List Wire := [v43,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h384 : NoPlan 7 s383 := viaSymmetry perm2 inv2 invId2 h310 (by decide +kernel)
def s384 : List Wire := [v44,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h385 : NoPlan 7 s384 := viaSymmetry perm2 inv2 invId2 h381 (by decide +kernel)
def s385 : List Wire := [v45,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h386 : NoPlan 7 s385 := viaSymmetry perm4 inv4 invId4 h235 (by decide +kernel)
def s386 : List Wire := [v46,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h387 : NoPlan 7 s386 := viaSymmetry perm4 inv4 invId4 h236 (by decide +kernel)
def s387 : List Wire := [v47,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h388 : NoPlan 7 s387 := viaSymmetry perm4 inv4 invId4 h310 (by decide +kernel)
def s388 : List Wire := [v48,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h389 : NoPlan 7 s388 := viaSymmetry perm4 inv4 invId4 h381 (by decide +kernel)
def s389 : List Wire := [v49,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h390 : NoPlan 7 s389 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s390 : List Wire := [v50,v0,v1,v2,v3,v4]
def v126 : Wire := ⟨0x7ffbc3e5003e4f#55,0x0#55⟩
def s391 : List Wire := [v126,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h392 : NoPlan 6 s391 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s392 : List Wire := [v126,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h393 : NoPlan 6 s392 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s393 : List Wire := [v22,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h394 : NoPlan 6 s393 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def v127 : Wire := ⟨0x43802ff8000#55,0x2f9000037fbe44#55⟩
def s394 : List Wire := [v127,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h395 : NoPlan 6 s394 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s395 : List Wire := [v127,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h396 : NoPlan 6 s395 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s396 : List Wire := [v79,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h397 : NoPlan 6 s396 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s397 : List Wire := [v52,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h398 : NoPlan 6 s397 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s398 : List Wire := [v52,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h399 : NoPlan 6 s398 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s399 : List Wire := [v52,v50,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h400 : NoPlan 6 s399 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s400 : List Wire := [v51,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h401 : NoPlan 6 s400 := banBySearch (by decide +kernel) (by decide +kernel)
def s401 : List Wire := [v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h402 : NoPlan 6 s401 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s402 : List Wire := [v51,v50,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h403 : NoPlan 6 s402 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s21) (budget:=3) (by decide +kernel) p4 (by decide +kernel) (by decide +kernel)
def v128 : Wire := ⟨0xf6943b69400#55,0x25000003261400#55⟩
def s403 : List Wire := [v128,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h404 : NoPlan 6 s403 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s404 : List Wire := [v128,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h405 : NoPlan 6 s404 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v129 : Wire := ⟨0x7fffffeffffedf#55,0x3fb00003fffec4#55⟩
def s405 : List Wire := [v129,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h406 : NoPlan 6 s405 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s406 : List Wire := [v129,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h407 : NoPlan 6 s406 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v130 : Wire := ⟨0x7ff092a4492a4f#55,0xa90000059aa44#55⟩
def s407 : List Wire := [v130,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h408 : NoPlan 6 s407 := banBySearch (by decide +kernel) (by decide +kernel)
def s408 : List Wire := [v130,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h409 : NoPlan 6 s408 := banBySearch (by decide +kernel) (by decide +kernel)
def v131 : Wire := ⟨0x408004090#55,0x10200000804080#55⟩
def s409 : List Wire := [v131,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h410 : NoPlan 6 s409 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s410 : List Wire := [v131,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h411 : NoPlan 6 s410 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v132 : Wire := ⟨0xfb283dd2800#55,0x2a000003582800#55⟩
def s411 : List Wire := [v132,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h412 : NoPlan 6 s411 := viaSymmetry perm1 inv1 invId1 h404 (by decide +kernel)
def s412 : List Wire := [v132,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h413 : NoPlan 6 s412 := viaSymmetry perm1 inv1 invId1 h405 (by decide +kernel)
def v133 : Wire := ⟨0x7ffffff7ffff6f#55,0x3fd00003ffff44#55⟩
def s413 : List Wire := [v133,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h414 : NoPlan 6 s413 := viaSymmetry perm1 inv1 invId1 h406 (by decide +kernel)
def s414 : List Wire := [v133,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h415 : NoPlan 6 s414 := viaSymmetry perm1 inv1 invId1 h407 (by decide +kernel)
def v134 : Wire := ⟨0x7ff0496422964f#55,0x5900000279644#55⟩
def s415 : List Wire := [v134,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h416 : NoPlan 6 s415 := viaSymmetry perm1 inv1 invId1 h408 (by decide +kernel)
def s416 : List Wire := [v134,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h417 : NoPlan 6 s416 := viaSymmetry perm1 inv1 invId1 h409 (by decide +kernel)
def v135 : Wire := ⟨0x410004120#55,0x10400000804100#55⟩
def s417 : List Wire := [v135,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h418 : NoPlan 6 s417 := viaSymmetry perm1 inv1 invId1 h410 (by decide +kernel)
def s418 : List Wire := [v135,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h419 : NoPlan 6 s418 := viaSymmetry perm1 inv1 invId1 h411 (by decide +kernel)
def s419 : List Wire := [v5,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h420 : NoPlan 6 s419 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s420 : List Wire := [v11,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h421 : NoPlan 6 s420 := by unfold NoPlan at *; rw [show s420.toFinset=s67.toFinset by decide +kernel]; exact h62
def s421 : List Wire := [v11,v50,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h422 : NoPlan 6 s421 := by unfold NoPlan at *; rw [show s421.toFinset=s68.toFinset by decide +kernel]; exact h63
def s422 : List Wire := [v16,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h423 : NoPlan 6 s422 := by unfold NoPlan at *; rw [show s422.toFinset=s141.toFinset by decide +kernel]; exact h138
def s423 : List Wire := [v12,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h424 : NoPlan 6 s423 := by unfold NoPlan at *; rw [show s423.toFinset=s208.toFinset by decide +kernel]; exact h206
def s424 : List Wire := [v12,v50,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h425 : NoPlan 6 s424 := by unfold NoPlan at *; rw [show s424.toFinset=s209.toFinset by decide +kernel]; exact h207
def s425 : List Wire := [v37,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h426 : NoPlan 6 s425 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s426 : List Wire := [v38,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h427 : NoPlan 6 s426 := by unfold NoPlan at *; rw [show s426.toFinset=s284.toFinset by decide +kernel]; exact h281
def s427 : List Wire := [v38,v50,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h428 : NoPlan 6 s427 := by unfold NoPlan at *; rw [show s427.toFinset=s285.toFinset by decide +kernel]; exact h282
def s428 : List Wire := [v39,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h429 : NoPlan 6 s428 := by unfold NoPlan at *; rw [show s428.toFinset=s357.toFinset by decide +kernel]; exact h357
def s429 : List Wire := [v40,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h430 : NoPlan 6 s429 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s430 : List Wire := [v40,v50,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h431 : NoPlan 6 s430 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s431 : List Wire := [v41,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h432 : NoPlan 6 s431 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s432 : List Wire := [v42,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h433 : NoPlan 6 s432 := viaSymmetry perm2 inv2 invId2 h287 (by decide +kernel)
def s433 : List Wire := [v43,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h434 : NoPlan 6 s433 := viaSymmetry perm2 inv2 invId2 h362 (by decide +kernel)
def s434 : List Wire := [v44,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h435 : NoPlan 6 s434 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s435 : List Wire := [v45,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h436 : NoPlan 6 s435 := viaSymmetry perm1 inv1 invId1 h432 (by decide +kernel)
def s436 : List Wire := [v46,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h437 : NoPlan 6 s436 := viaSymmetry perm4 inv4 invId4 h287 (by decide +kernel)
def s437 : List Wire := [v47,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h438 : NoPlan 6 s437 := viaSymmetry perm4 inv4 invId4 h362 (by decide +kernel)
def s438 : List Wire := [v48,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h439 : NoPlan 6 s438 := viaSymmetry perm1 inv1 invId1 h435 (by decide +kernel)
def s439 : List Wire := [v49,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h440 : NoPlan 6 s439 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s440 : List Wire := [v49,v50,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h441 : NoPlan 6 s440 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s441 : List Wire := [v49,v50,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h442 : NoPlan 6 s441 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s442 : List Wire := [v49,v50,v0,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h443 : NoPlan 6 s442 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s443 : List Wire := [v53,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h444 : NoPlan 6 s443 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s444 : List Wire := [v54,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h445 : NoPlan 6 s444 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s445 : List Wire := [v55,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h446 : NoPlan 6 s445 := banBySearch (by decide +kernel) (by decide +kernel)
def s446 : List Wire := [v56,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h447 : NoPlan 6 s446 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=2) (by decide +kernel) p3 (by decide +kernel) (by decide +kernel)
def s447 : List Wire := [v57,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h448 : NoPlan 6 s447 := viaSymmetry perm1 inv1 invId1 h444 (by decide +kernel)
def s448 : List Wire := [v58,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h449 : NoPlan 6 s448 := viaSymmetry perm1 inv1 invId1 h445 (by decide +kernel)
def s449 : List Wire := [v59,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h450 : NoPlan 6 s449 := viaSymmetry perm1 inv1 invId1 h446 (by decide +kernel)
def s450 : List Wire := [v60,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h451 : NoPlan 6 s450 := viaSymmetry perm1 inv1 invId1 h447 (by decide +kernel)
def s451 : List Wire := [v61,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h452 : NoPlan 6 s451 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s452 : List Wire := [v66,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h453 : NoPlan 6 s452 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s453 : List Wire := [v67,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h454 : NoPlan 6 s453 := banBySearch (by decide +kernel) (by decide +kernel)
def s454 : List Wire := [v68,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h455 : NoPlan 6 s454 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s455 : List Wire := [v69,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h456 : NoPlan 6 s455 := viaSymmetry perm1 inv1 invId1 h452 (by decide +kernel)
def s456 : List Wire := [v70,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h457 : NoPlan 6 s456 := viaSymmetry perm1 inv1 invId1 h453 (by decide +kernel)
def s457 : List Wire := [v71,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h458 : NoPlan 6 s457 := viaSymmetry perm1 inv1 invId1 h454 (by decide +kernel)
def s458 : List Wire := [v72,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h459 : NoPlan 6 s458 := viaSymmetry perm1 inv1 invId1 h455 (by decide +kernel)
def s459 : List Wire := [v73,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h460 : NoPlan 6 s459 := banBySearch (by decide +kernel) (by decide +kernel)
def s460 : List Wire := [v74,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h461 : NoPlan 6 s460 := banBySearch (by decide +kernel) (by decide +kernel)
def s461 : List Wire := [v75,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h462 : NoPlan 6 s461 := banBySearch (by decide +kernel) (by decide +kernel)
def s462 : List Wire := [v76,v50,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h463 : NoPlan 6 s462 := viaSymmetry perm1 inv1 invId1 h462 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h391 : NoPlan 7 s390 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s390 = [s391,s392,s393,s17,s394,s395,s396,s106,s397,s398,s399,s400,s401,s402,s403,s404,s405,s406,s407,s408,s409,s410,s411,s412,s413,s414,s415,s416,s417,s418,s419,s420,s421,s422,s423,s424,s425,s426,s427,s428,s429,s430,s431,s432,s433,s434,s435,s436,s437,s438,s439,s440,s441,s442,s400,s402,s397,s399,s443,s444,s445,s446,s447,s448,s449,s450,s451,s452,s453,s454,s455,s456,s457,s458,s459,s460,s461,s462] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h392,h393,h394,h14,h395,h396,h397,h103,h398,h399,h400,h401,h402,h403,h404,h405,h406,h407,h408,h409,h410,h411,h412,h413,h414,h415,h416,h417,h418,h419,h420,h421,h422,h423,h424,h425,h426,h427,h428,h429,h430,h431,h432,h433,h434,h435,h436,h437,h438,h439,h440,h441,h442,h443,h401,h403,h398,h400,h444,h445,h446,h447,h448,h449,h450,h451,h452,h453,h454,h455,h456,h457,h458,h459,h460,h461,h462,h463⟩
def s463 : List Wire := [v115,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h465 : NoPlan 6 s463 := banBySearch (by decide +kernel) (by decide +kernel)
def v136 : Wire := ⟨0x7ffbe7fd947fff#55,0x30000001e0c3e#55⟩
def s464 : List Wire := [v136,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h466 : NoPlan 6 s464 := banBySearch (by decide +kernel) (by decide +kernel)
def s465 : List Wire := [v136,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h467 : NoPlan 6 s465 := banBySearch (by decide +kernel) (by decide +kernel)
def s466 : List Wire := [v91,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h468 : NoPlan 6 s466 := banBySearch (by decide +kernel) (by decide +kernel)
def v137 : Wire := ⟨0xac73d0073f8#55,0x3a#55⟩
def s467 : List Wire := [v137,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h469 : NoPlan 6 s467 := banBySearch (by decide +kernel) (by decide +kernel)
def s468 : List Wire := [v137,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h470 : NoPlan 6 s468 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s469 : List Wire := [v49,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h471 : NoPlan 6 s469 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h472 : NoPlan 6 s389 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s470 : List Wire := [v49,v51,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h473 : NoPlan 6 s470 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s471 : List Wire := [v50,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h474 : NoPlan 6 s471 := by unfold NoPlan at *; rw [show s471.toFinset=s400.toFinset by decide +kernel]; exact h401
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h475 : NoPlan 6 s390 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s472 : List Wire := [v50,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h476 : NoPlan 6 s472 := by unfold NoPlan at *; rw [show s472.toFinset=s402.toFinset by decide +kernel]; exact h403
def v138 : Wire := ⟨0x12040940400#55,0x1000000060400#55⟩
def s473 : List Wire := [v138,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h477 : NoPlan 6 s473 := banBySearch (by decide +kernel) (by decide +kernel)
def s474 : List Wire := [v138,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h478 : NoPlan 6 s474 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v139 : Wire := ⟨0x7fff6dcbb6dc97#55,0x37200003be5c84#55⟩
def s475 : List Wire := [v139,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h479 : NoPlan 6 s475 := banBySearch (by decide +kernel) (by decide +kernel)
def s476 : List Wire := [v139,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h480 : NoPlan 6 s476 := banBySearch (by decide +kernel) (by decide +kernel)
def v140 : Wire := ⟨0x7ff00080000807#55,0x2000000180804#55⟩
def s477 : List Wire := [v140,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h481 : NoPlan 6 s477 := banBySearch (by decide +kernel) (by decide +kernel)
def s478 : List Wire := [v140,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h482 : NoPlan 6 s478 := banBySearch (by decide +kernel) (by decide +kernel)
def v141 : Wire := ⟨0xe4d0b22d090#55,0x34200003a05080#55⟩
def s479 : List Wire := [v141,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h483 : NoPlan 6 s479 := banBySearch (by decide +kernel) (by decide +kernel)
def s480 : List Wire := [v141,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h484 : NoPlan 6 s480 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v142 : Wire := ⟨0x12080940800#55,0x2000000180800#55⟩
def s481 : List Wire := [v142,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h485 : NoPlan 6 s481 := viaSymmetry perm1 inv1 invId1 h477 (by decide +kernel)
def s482 : List Wire := [v142,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h486 : NoPlan 6 s482 := viaSymmetry perm1 inv1 invId1 h478 (by decide +kernel)
def v143 : Wire := ⟨0x7fffb6d3dd6d27#55,0x3b400003de6d04#55⟩
def s483 : List Wire := [v143,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h487 : NoPlan 6 s483 := viaSymmetry perm1 inv1 invId1 h479 (by decide +kernel)
def s484 : List Wire := [v143,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h488 : NoPlan 6 s484 := viaSymmetry perm1 inv1 invId1 h480 (by decide +kernel)
def v144 : Wire := ⟨0x7ff00040000407#55,0x1000000060404#55⟩
def s485 : List Wire := [v144,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h489 : NoPlan 6 s485 := viaSymmetry perm1 inv1 invId1 h481 (by decide +kernel)
def s486 : List Wire := [v144,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h490 : NoPlan 6 s486 := viaSymmetry perm1 inv1 invId1 h482 (by decide +kernel)
def v145 : Wire := ⟨0xe9613496120#55,0x38400003c06100#55⟩
def s487 : List Wire := [v145,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h491 : NoPlan 6 s487 := viaSymmetry perm1 inv1 invId1 h483 (by decide +kernel)
def s488 : List Wire := [v145,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h492 : NoPlan 6 s488 := viaSymmetry perm1 inv1 invId1 h484 (by decide +kernel)
def s489 : List Wire := [v5,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h493 : NoPlan 6 s489 := banBySearch (by decide +kernel) (by decide +kernel)
def s490 : List Wire := [v11,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h494 : NoPlan 6 s490 := by unfold NoPlan at *; rw [show s490.toFinset=s69.toFinset by decide +kernel]; exact h64
def s491 : List Wire := [v11,v51,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h495 : NoPlan 6 s491 := by unfold NoPlan at *; rw [show s491.toFinset=s70.toFinset by decide +kernel]; exact h65
def s492 : List Wire := [v16,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h496 : NoPlan 6 s492 := by unfold NoPlan at *; rw [show s492.toFinset=s142.toFinset by decide +kernel]; exact h139
def s493 : List Wire := [v12,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h497 : NoPlan 6 s493 := by unfold NoPlan at *; rw [show s493.toFinset=s210.toFinset by decide +kernel]; exact h208
def s494 : List Wire := [v12,v51,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h498 : NoPlan 6 s494 := by unfold NoPlan at *; rw [show s494.toFinset=s211.toFinset by decide +kernel]; exact h209
def s495 : List Wire := [v37,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h499 : NoPlan 6 s495 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s496 : List Wire := [v37,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h500 : NoPlan 6 s496 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s21) (budget:=3) (by decide +kernel) p4 (by decide +kernel) (by decide +kernel)
def s497 : List Wire := [v38,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h501 : NoPlan 6 s497 := by unfold NoPlan at *; rw [show s497.toFinset=s286.toFinset by decide +kernel]; exact h283
def s498 : List Wire := [v39,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h502 : NoPlan 6 s498 := by unfold NoPlan at *; rw [show s498.toFinset=s358.toFinset by decide +kernel]; exact h358
def s499 : List Wire := [v39,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h503 : NoPlan 6 s499 := by unfold NoPlan at *; rw [show s499.toFinset=s359.toFinset by decide +kernel]; exact h359
def s500 : List Wire := [v40,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h504 : NoPlan 6 s500 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s501 : List Wire := [v41,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h505 : NoPlan 6 s501 := banBySearch (by decide +kernel) (by decide +kernel)
def s502 : List Wire := [v42,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h506 : NoPlan 6 s502 := viaSymmetry perm2 inv2 invId2 h288 (by decide +kernel)
def s503 : List Wire := [v43,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h507 : NoPlan 6 s503 := viaSymmetry perm2 inv2 invId2 h363 (by decide +kernel)
def s504 : List Wire := [v44,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h508 : NoPlan 6 s504 := banBySearch (by decide +kernel) (by decide +kernel)
def s505 : List Wire := [v45,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h509 : NoPlan 6 s505 := viaSymmetry perm1 inv1 invId1 h505 (by decide +kernel)
def s506 : List Wire := [v46,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h510 : NoPlan 6 s506 := viaSymmetry perm4 inv4 invId4 h288 (by decide +kernel)
def s507 : List Wire := [v47,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h511 : NoPlan 6 s507 := viaSymmetry perm4 inv4 invId4 h363 (by decide +kernel)
def s508 : List Wire := [v48,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h512 : NoPlan 6 s508 := viaSymmetry perm1 inv1 invId1 h508 (by decide +kernel)
def s509 : List Wire := [v52,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h513 : NoPlan 6 s509 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s510 : List Wire := [v52,v51,v0,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h514 : NoPlan 6 s510 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s511 : List Wire := [v52,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h515 : NoPlan 6 s511 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s21) (budget:=3) (by decide +kernel) p4 (by decide +kernel) (by decide +kernel)
def s512 : List Wire := [v52,v51,v0,v3,v4]
def v146 : Wire := ⟨0x7fffffdbfffdb7#55,0x4#55⟩
def v147 : Wire := ⟨0x7fffffffffffff#55,0xa#55⟩
def v148 : Wire := ⟨0x4000048#55,0x100000000040#55⟩
def s513 : List Wire := [v146,v147,v148]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p9 : s513.sublists.any (quick 4) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h516 : NoPlan 6 s512 := banByRestriction (mask:=0x4090002400024f) (j:=0) (bank:=s513) (budget:=4) (by decide +kernel) p9 (by decide +kernel) (by decide +kernel)
def s514 : List Wire := [v53,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h517 : NoPlan 6 s514 := banBySearch (by decide +kernel) (by decide +kernel)
def s515 : List Wire := [v54,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h518 : NoPlan 6 s515 := viaSymmetry perm2 inv2 invId2 h446 (by decide +kernel)
def s516 : List Wire := [v55,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h519 : NoPlan 6 s516 := banBySearch (by decide +kernel) (by decide +kernel)
def s517 : List Wire := [v56,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h520 : NoPlan 6 s517 := banBySearch (by decide +kernel) (by decide +kernel)
def s518 : List Wire := [v57,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h521 : NoPlan 6 s518 := viaSymmetry perm1 inv1 invId1 h517 (by decide +kernel)
def s519 : List Wire := [v58,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h522 : NoPlan 6 s519 := viaSymmetry perm4 inv4 invId4 h446 (by decide +kernel)
def s520 : List Wire := [v59,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h523 : NoPlan 6 s520 := viaSymmetry perm1 inv1 invId1 h519 (by decide +kernel)
def s521 : List Wire := [v60,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h524 : NoPlan 6 s521 := viaSymmetry perm1 inv1 invId1 h520 (by decide +kernel)
def s522 : List Wire := [v61,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h525 : NoPlan 6 s522 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s523 : List Wire := [v66,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h526 : NoPlan 6 s523 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s524 : List Wire := [v66,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h527 : NoPlan 6 s524 := banBySearch (by decide +kernel) (by decide +kernel)
def s525 : List Wire := [v67,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h528 : NoPlan 6 s525 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s526 : List Wire := [v67,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h529 : NoPlan 6 s526 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s527 : List Wire := [v68,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h530 : NoPlan 6 s527 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s528 : List Wire := [v69,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h531 : NoPlan 6 s528 := viaSymmetry perm1 inv1 invId1 h525 (by decide +kernel)
def s529 : List Wire := [v70,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h532 : NoPlan 6 s529 := viaSymmetry perm1 inv1 invId1 h526 (by decide +kernel)
def s530 : List Wire := [v70,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h533 : NoPlan 6 s530 := viaSymmetry perm1 inv1 invId1 h527 (by decide +kernel)
def s531 : List Wire := [v71,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h534 : NoPlan 6 s531 := viaSymmetry perm1 inv1 invId1 h528 (by decide +kernel)
def s532 : List Wire := [v71,v51,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h535 : NoPlan 6 s532 := viaSymmetry perm1 inv1 invId1 h529 (by decide +kernel)
def s533 : List Wire := [v72,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h536 : NoPlan 6 s533 := viaSymmetry perm1 inv1 invId1 h530 (by decide +kernel)
def s534 : List Wire := [v73,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h537 : NoPlan 6 s534 := banBySearch (by decide +kernel) (by decide +kernel)
def s535 : List Wire := [v74,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h538 : NoPlan 6 s535 := banBySearch (by decide +kernel) (by decide +kernel)
def s536 : List Wire := [v75,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h539 : NoPlan 6 s536 := banBySearch (by decide +kernel) (by decide +kernel)
def s537 : List Wire := [v76,v51,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h540 : NoPlan 6 s537 := viaSymmetry perm1 inv1 invId1 h539 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h464 : NoPlan 7 s401 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s401 = [s463,s316,s464,s465,s466,s173,s467,s468,s469,s389,s470,s471,s390,s472,s473,s474,s475,s476,s477,s478,s479,s480,s481,s482,s483,s484,s485,s486,s487,s488,s489,s490,s491,s492,s493,s494,s495,s496,s497,s498,s499,s500,s501,s502,s503,s504,s505,s506,s507,s508,s469,s470,s471,s472,s509,s510,s511,s512,s514,s515,s516,s517,s518,s519,s520,s521,s522,s523,s524,s525,s526,s527,s528,s529,s530,s531,s532,s533,s534,s535,s536,s537] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h465,h315,h466,h467,h468,h171,h469,h470,h471,h472,h473,h474,h475,h476,h477,h478,h479,h480,h481,h482,h483,h484,h485,h486,h487,h488,h489,h490,h491,h492,h493,h494,h495,h496,h497,h498,h499,h500,h501,h502,h503,h504,h505,h506,h507,h508,h509,h510,h511,h512,h471,h473,h474,h476,h513,h514,h515,h516,h517,h518,h519,h520,h521,h522,h523,h524,h525,h526,h527,h528,h529,h530,h531,h532,h533,h534,h535,h536,h537,h538,h539,h540⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h541 : NoPlan 7 s398 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s538 : List Wire := [v53,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h542 : NoPlan 7 s538 := viaSymmetry perm2 inv2 invId2 h390 (by decide +kernel)
def s539 : List Wire := [v54,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h543 : NoPlan 7 s539 := viaSymmetry perm2 inv2 invId2 h391 (by decide +kernel)
def s540 : List Wire := [v55,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h544 : NoPlan 7 s540 := viaSymmetry perm2 inv2 invId2 h464 (by decide +kernel)
def s541 : List Wire := [v56,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h545 : NoPlan 7 s541 := viaSymmetry perm2 inv2 invId2 h541 (by decide +kernel)
def s542 : List Wire := [v57,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h546 : NoPlan 7 s542 := viaSymmetry perm4 inv4 invId4 h390 (by decide +kernel)
def s543 : List Wire := [v58,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h547 : NoPlan 7 s543 := viaSymmetry perm4 inv4 invId4 h391 (by decide +kernel)
def s544 : List Wire := [v59,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h548 : NoPlan 7 s544 := viaSymmetry perm4 inv4 invId4 h464 (by decide +kernel)
def s545 : List Wire := [v60,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h549 : NoPlan 7 s545 := viaSymmetry perm4 inv4 invId4 h541 (by decide +kernel)
def s546 : List Wire := [v61,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h550 : NoPlan 7 s546 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s547 : List Wire := [v66,v0,v1,v2,v3,v4]
def v149 : Wire := ⟨0xbc76d0076d8#55,0x0#55⟩
def s548 : List Wire := [v149,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h552 : NoPlan 6 s548 := banBySearch (by decide +kernel) (by decide +kernel)
def s549 : List Wire := [v149,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h553 : NoPlan 6 s549 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s550 : List Wire := [v108,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h554 : NoPlan 6 s550 := banBySearch (by decide +kernel) (by decide +kernel)
def v150 : Wire := ⟨0x43802ff8000#55,0x3db00003e7f6c0#55⟩
def s551 : List Wire := [v150,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h555 : NoPlan 6 s551 := banBySearch (by decide +kernel) (by decide +kernel)
def s552 : List Wire := [v150,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h556 : NoPlan 6 s552 := banBySearch (by decide +kernel) (by decide +kernel)
def s553 : List Wire := [v120,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h557 : NoPlan 6 s553 := banBySearch (by decide +kernel) (by decide +kernel)
def v151 : Wire := ⟨0xdf862ff8600#55,0x1800000078600#55⟩
def s554 : List Wire := [v151,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h558 : NoPlan 6 s554 := banBySearch (by decide +kernel) (by decide +kernel)
def s555 : List Wire := [v151,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h559 : NoPlan 6 s555 := banBySearch (by decide +kernel) (by decide +kernel)
def s556 : List Wire := [v129,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h560 : NoPlan 6 s556 := banBySearch (by decide +kernel) (by decide +kernel)
def v152 : Wire := ⟨0x2070d0070d8#55,0x3c300003e070c0#55⟩
def s557 : List Wire := [v152,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h561 : NoPlan 6 s557 := banBySearch (by decide +kernel) (by decide +kernel)
def s558 : List Wire := [v152,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h562 : NoPlan 6 s558 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def s559 : List Wire := [v140,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h563 : NoPlan 6 s559 := banBySearch (by decide +kernel) (by decide +kernel)
def s560 : List Wire := [v68,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h564 : NoPlan 6 s560 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s561 : List Wire := [v68,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h565 : NoPlan 6 s561 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s562 : List Wire := [v68,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h566 : NoPlan 6 s562 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def s563 : List Wire := [v67,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h567 : NoPlan 6 s563 := viaSymmetry perm2 inv2 invId2 h564 (by decide +kernel)
def s564 : List Wire := [v67,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h568 : NoPlan 6 s564 := viaSymmetry perm2 inv2 invId2 h565 (by decide +kernel)
def s565 : List Wire := [v67,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h569 : NoPlan 6 s565 := viaSymmetry perm2 inv2 invId2 h566 (by decide +kernel)
def v153 : Wire := ⟨0xfb603dd6000#55,0x38000003c06000#55⟩
def s566 : List Wire := [v153,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h570 : NoPlan 6 s566 := banBySearch (by decide +kernel) (by decide +kernel)
def s567 : List Wire := [v153,v0,v1,v2,v3,v4]
def v154 : Wire := ⟨0x7ffff7ffdd7fff#55,0x1a#55⟩
def v155 : Wire := ⟨0x7ffffef3ffef27#55,0x1800000028604#55⟩
def v156 : Wire := ⟨0x4924229248#55,0x4900000209240#55⟩
def v157 : Wire := ⟨0x4948229490#55,0x5200000221480#55⟩
def s568 : List Wire := [v154,v155,v156,v157]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem p10 : s568.sublists.any (quick 4) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h571 : NoPlan 6 s567 := banByRestriction (mask:=0x45b0496c2296df) (j:=0) (bank:=s568) (budget:=4) (by decide +kernel) p10 (by decide +kernel) (by decide +kernel)
def v158 : Wire := ⟨0xffffffffff8#55,0x3ff00003ffffc0#55⟩
def s569 : List Wire := [v158,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h572 : NoPlan 6 s569 := banBySearch (by decide +kernel) (by decide +kernel)
def s570 : List Wire := [v158,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h573 : NoPlan 6 s570 := banByRestriction (mask:=0x1f8000) (j:=15) (bank:=s6) (budget:=3) (by decide +kernel) p1 (by decide +kernel) (by decide +kernel)
def v159 : Wire := ⟨0x496c2296d8#55,0x5b000002796c0#55⟩
def s571 : List Wire := [v159,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h574 : NoPlan 6 s571 := banBySearch (by decide +kernel) (by decide +kernel)
def s572 : List Wire := [v159,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h575 : NoPlan 6 s572 := banBySearch (by decide +kernel) (by decide +kernel)
def v160 : Wire := ⟨0x90000920#55,0x2400000180900#55⟩
def s573 : List Wire := [v160,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h576 : NoPlan 6 s573 := banBySearch (by decide +kernel) (by decide +kernel)
def s574 : List Wire := [v160,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h577 : NoPlan 6 s574 := banByRestriction (mask:=0x45b0496c2296df) (j:=0) (bank:=s568) (budget:=4) (by decide +kernel) p10 (by decide +kernel) (by decide +kernel)
def s575 : List Wire := [v5,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h578 : NoPlan 6 s575 := banBySearch (by decide +kernel) (by decide +kernel)
def s576 : List Wire := [v11,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h579 : NoPlan 6 s576 := by unfold NoPlan at *; rw [show s576.toFinset=s86.toFinset by decide +kernel]; exact h80
def s577 : List Wire := [v16,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h580 : NoPlan 6 s577 := by unfold NoPlan at *; rw [show s577.toFinset=s153.toFinset by decide +kernel]; exact h150
def s578 : List Wire := [v12,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h581 : NoPlan 6 s578 := by unfold NoPlan at *; rw [show s578.toFinset=s226.toFinset by decide +kernel]; exact h224
def s579 : List Wire := [v37,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h582 : NoPlan 6 s579 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s580 : List Wire := [v38,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h583 : NoPlan 6 s580 := by unfold NoPlan at *; rw [show s580.toFinset=s298.toFinset by decide +kernel]; exact h295
def s581 : List Wire := [v38,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h584 : NoPlan 6 s581 := by unfold NoPlan at *; rw [show s581.toFinset=s299.toFinset by decide +kernel]; exact h296
def s582 : List Wire := [v39,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h585 : NoPlan 6 s582 := by unfold NoPlan at *; rw [show s582.toFinset=s370.toFinset by decide +kernel]; exact h370
def s583 : List Wire := [v40,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h586 : NoPlan 6 s583 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s584 : List Wire := [v40,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h587 : NoPlan 6 s584 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s585 : List Wire := [v41,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h588 : NoPlan 6 s585 := viaSymmetry perm2 inv2 invId2 h582 (by decide +kernel)
def s586 : List Wire := [v42,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h589 : NoPlan 6 s586 := viaSymmetry perm2 inv2 invId2 h295 (by decide +kernel)
def s587 : List Wire := [v42,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h590 : NoPlan 6 s587 := viaSymmetry perm2 inv2 invId2 h296 (by decide +kernel)
def s588 : List Wire := [v43,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h591 : NoPlan 6 s588 := viaSymmetry perm2 inv2 invId2 h370 (by decide +kernel)
def s589 : List Wire := [v44,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h592 : NoPlan 6 s589 := viaSymmetry perm2 inv2 invId2 h586 (by decide +kernel)
def s590 : List Wire := [v44,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h593 : NoPlan 6 s590 := viaSymmetry perm2 inv2 invId2 h587 (by decide +kernel)
def s591 : List Wire := [v45,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h594 : NoPlan 6 s591 := banBySearch (by decide +kernel) (by decide +kernel)
def s592 : List Wire := [v46,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h595 : NoPlan 6 s592 := viaSymmetry perm4 inv4 invId4 h307 (by decide +kernel)
def s593 : List Wire := [v47,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h596 : NoPlan 6 s593 := viaSymmetry perm4 inv4 invId4 h378 (by decide +kernel)
def s594 : List Wire := [v48,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h597 : NoPlan 6 s594 := banBySearch (by decide +kernel) (by decide +kernel)
def s595 : List Wire := [v49,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h598 : NoPlan 6 s595 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s596 : List Wire := [v49,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h599 : NoPlan 6 s596 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s597 : List Wire := [v50,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h600 : NoPlan 6 s597 := by unfold NoPlan at *; rw [show s597.toFinset=s452.toFinset by decide +kernel]; exact h453
def s598 : List Wire := [v51,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h601 : NoPlan 6 s598 := by unfold NoPlan at *; rw [show s598.toFinset=s523.toFinset by decide +kernel]; exact h526
def s599 : List Wire := [v51,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h602 : NoPlan 6 s599 := by unfold NoPlan at *; rw [show s599.toFinset=s524.toFinset by decide +kernel]; exact h527
def s600 : List Wire := [v52,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h603 : NoPlan 6 s600 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s601 : List Wire := [v53,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h604 : NoPlan 6 s601 := viaSymmetry perm2 inv2 invId2 h598 (by decide +kernel)
def s602 : List Wire := [v53,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h605 : NoPlan 6 s602 := viaSymmetry perm2 inv2 invId2 h599 (by decide +kernel)
def s603 : List Wire := [v54,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h606 : NoPlan 6 s603 := viaSymmetry perm2 inv2 invId2 h453 (by decide +kernel)
def s604 : List Wire := [v55,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h607 : NoPlan 6 s604 := viaSymmetry perm2 inv2 invId2 h526 (by decide +kernel)
def s605 : List Wire := [v55,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h608 : NoPlan 6 s605 := viaSymmetry perm2 inv2 invId2 h527 (by decide +kernel)
def s606 : List Wire := [v56,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h609 : NoPlan 6 s606 := viaSymmetry perm2 inv2 invId2 h603 (by decide +kernel)
def s607 : List Wire := [v57,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h610 : NoPlan 6 s607 := banBySearch (by decide +kernel) (by decide +kernel)
def s608 : List Wire := [v58,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h611 : NoPlan 6 s608 := viaSymmetry perm4 inv4 invId4 h461 (by decide +kernel)
def s609 : List Wire := [v59,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h612 : NoPlan 6 s609 := viaSymmetry perm4 inv4 invId4 h538 (by decide +kernel)
def s610 : List Wire := [v60,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h613 : NoPlan 6 s610 := banBySearch (by decide +kernel) (by decide +kernel)
def s611 : List Wire := [v61,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h614 : NoPlan 6 s611 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s612 : List Wire := [v61,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h615 : NoPlan 6 s612 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s613 : List Wire := [v61,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h616 : NoPlan 6 s613 := viaSymmetry perm2 inv2 invId2 h615 (by decide +kernel)
def s614 : List Wire := [v61,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h617 : NoPlan 6 s614 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s615 : List Wire := [v69,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h618 : NoPlan 6 s615 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
def s616 : List Wire := [v70,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h619 : NoPlan 6 s616 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s617 : List Wire := [v70,v66,v0,v1,v3,v4]
def v161 : Wire := ⟨0xfff27fff248#55,0x3c900003e1f240#55⟩
def s618 : List Wire := [v161,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h621 : NoPlan 5 s618 := banBySearch (by decide +kernel) (by decide +kernel)
def s619 : List Wire := [v161,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h622 : NoPlan 5 s619 := viaSymmetry perm1 inv1 invId1 h621 (by decide +kernel)
def s620 : List Wire := [v161,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h623 : NoPlan 5 s620 := banBySearch (by decide +kernel) (by decide +kernel)
def s621 : List Wire := [v160,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h624 : NoPlan 5 s621 := banBySearch (by decide +kernel) (by decide +kernel)
def v162 : Wire := ⟨0x48000490#55,0x1200000060480#55⟩
def s622 : List Wire := [v162,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h625 : NoPlan 5 s622 := viaSymmetry perm1 inv1 invId1 h624 (by decide +kernel)
def s623 : List Wire := [v112,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h626 : NoPlan 5 s623 := banBySearch (by decide +kernel) (by decide +kernel)
def v163 : Wire := ⟨0x43802ff8000#55,0x3ed00003f9fb40#55⟩
def s624 : List Wire := [v163,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h627 : NoPlan 5 s624 := banBySearch (by decide +kernel) (by decide +kernel)
def v164 : Wire := ⟨0xdf8a2ff8a00#55,0x2800000198a00#55⟩
def s625 : List Wire := [v164,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h628 : NoPlan 5 s625 := banBySearch (by decide +kernel) (by decide +kernel)
def s626 : List Wire := [v144,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h629 : NoPlan 5 s626 := banBySearch (by decide +kernel) (by decide +kernel)
def v165 : Wire := ⟨0xf6d03b6d000#55,0x34000003a05000#55⟩
def s627 : List Wire := [v165,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h630 : NoPlan 5 s627 := banBySearch (by decide +kernel) (by decide +kernel)
def s628 : List Wire := [v165,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h631 : NoPlan 5 s628 := banBySearch (by decide +kernel) (by decide +kernel)
def s629 : List Wire := [v165,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h632 : NoPlan 5 s629 := banByRestriction (mask:=0x4ad092b4492b6f) (j:=0) (bank:=s253) (budget:=4) (by decide +kernel) p8 (by decide +kernel) (by decide +kernel)
def v166 : Wire := ⟨0x92b4492b68#55,0xad0000059ab40#55⟩
def s630 : List Wire := [v166,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h633 : NoPlan 5 s630 := banBySearch (by decide +kernel) (by decide +kernel)
def s631 : List Wire := [v71,v66,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h634 : NoPlan 5 s631 := banBySearch (by decide +kernel) (by decide +kernel)
def s632 : List Wire := [v71,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h635 : NoPlan 5 s632 := banBySearch (by decide +kernel) (by decide +kernel)
def s633 : List Wire := [v108,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h636 : NoPlan 5 s633 := viaSymmetry perm1 inv1 invId1 h626 (by decide +kernel)
def s634 : List Wire := [v150,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h637 : NoPlan 5 s634 := viaSymmetry perm1 inv1 invId1 h627 (by decide +kernel)
def s635 : List Wire := [v151,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h638 : NoPlan 5 s635 := viaSymmetry perm1 inv1 invId1 h628 (by decide +kernel)
def s636 : List Wire := [v140,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h639 : NoPlan 5 s636 := viaSymmetry perm1 inv1 invId1 h629 (by decide +kernel)
def s637 : List Wire := [v67,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h640 : NoPlan 5 s637 := viaSymmetry perm1 inv1 invId1 h634 (by decide +kernel)
def s638 : List Wire := [v67,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h641 : NoPlan 5 s638 := viaSymmetry perm1 inv1 invId1 h635 (by decide +kernel)
def s639 : List Wire := [v153,v70,v0,v1,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h642 : NoPlan 5 s639 := viaSymmetry perm1 inv1 invId1 h630 (by decide +kernel)
def s640 : List Wire := [v153,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h643 : NoPlan 5 s640 := viaSymmetry perm1 inv1 invId1 h631 (by decide +kernel)
def s641 : List Wire := [v153,v70,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h644 : NoPlan 5 s641 := viaSymmetry perm1 inv1 invId1 h632 (by decide +kernel)
def s642 : List Wire := [v159,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h645 : NoPlan 5 s642 := viaSymmetry perm1 inv1 invId1 h633 (by decide +kernel)
def s643 : List Wire := [v42,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h646 : NoPlan 5 s643 := banBySearch (by decide +kernel) (by decide +kernel)
def s644 : List Wire := [v44,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h647 : NoPlan 5 s644 := banBySearch (by decide +kernel) (by decide +kernel)
def s645 : List Wire := [v46,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h648 : NoPlan 5 s645 := viaSymmetry perm1 inv1 invId1 h646 (by decide +kernel)
def s646 : List Wire := [v48,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h649 : NoPlan 5 s646 := viaSymmetry perm1 inv1 invId1 h647 (by decide +kernel)
def s647 : List Wire := [v53,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h650 : NoPlan 5 s647 := banBySearch (by decide +kernel) (by decide +kernel)
def s648 : List Wire := [v55,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h651 : NoPlan 5 s648 := banBySearch (by decide +kernel) (by decide +kernel)
def s649 : List Wire := [v57,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h652 : NoPlan 5 s649 := viaSymmetry perm1 inv1 invId1 h650 (by decide +kernel)
def s650 : List Wire := [v59,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h653 : NoPlan 5 s650 := viaSymmetry perm1 inv1 invId1 h651 (by decide +kernel)
def s651 : List Wire := [v74,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h654 : NoPlan 5 s651 := banBySearch (by decide +kernel) (by decide +kernel)
def s652 : List Wire := [v74,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h655 : NoPlan 5 s652 := viaSymmetry perm1 inv1 invId1 h654 (by decide +kernel)
def s653 : List Wire := [v74,v70,v66,v0,v1]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h656 : NoPlan 5 s653 := banBySearch (by decide +kernel) (by decide +kernel)
def s654 : List Wire := [v75,v70,v66,v0,v1,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h657 : NoPlan 5 s654 := banBySearch (by decide +kernel) (by decide +kernel)
def s655 : List Wire := [v76,v70,v66,v0,v1,v3]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h658 : NoPlan 5 s655 := viaSymmetry perm1 inv1 invId1 h657 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h620 : NoPlan 6 s617 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 5 s617 = [s618,s619,s620,s621,s622,s623,s624,s625,s626,s627,s628,s629,s630,s622,s631,s632,s633,s634,s635,s636,s637,s638,s639,s640,s641,s642,s621,s643,s644,s645,s646,s647,s648,s649,s650,s651,s652,s653,s654,s655] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h621,h622,h623,h624,h625,h626,h627,h628,h629,h630,h631,h632,h633,h625,h634,h635,h636,h637,h638,h639,h640,h641,h642,h643,h644,h645,h624,h646,h647,h648,h649,h650,h651,h652,h653,h654,h655,h656,h657,h658⟩
def s656 : List Wire := [v71,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h659 : NoPlan 6 s656 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=4) (by decide +kernel) p2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h660 : NoPlan 6 s631 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s657 : List Wire := [v72,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h661 : NoPlan 6 s657 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
def s658 : List Wire := [v73,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h662 : NoPlan 6 s658 := viaSymmetry perm2 inv2 invId2 h618 (by decide +kernel)
def s659 : List Wire := [v74,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h663 : NoPlan 6 s659 := viaSymmetry perm2 inv2 invId2 h619 (by decide +kernel)
def s660 : List Wire := [v74,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h664 : NoPlan 6 s660 := viaSymmetry perm2 inv2 invId2 h620 (by decide +kernel)
def s661 : List Wire := [v75,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h665 : NoPlan 6 s661 := viaSymmetry perm2 inv2 invId2 h659 (by decide +kernel)
def s662 : List Wire := [v75,v66,v0,v1,v2,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h666 : NoPlan 6 s662 := viaSymmetry perm2 inv2 invId2 h660 (by decide +kernel)
def s663 : List Wire := [v76,v66,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h667 : NoPlan 6 s663 := viaSymmetry perm2 inv2 invId2 h661 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h551 : NoPlan 7 s547 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 6 s547 = [s548,s549,s550,s255,s551,s552,s553,s329,s554,s555,s556,s406,s557,s558,s559,s478,s560,s561,s562,s563,s564,s565,s566,s567,s569,s570,s571,s572,s573,s574,s575,s576,s577,s578,s579,s580,s581,s582,s583,s584,s585,s586,s587,s588,s589,s590,s591,s592,s593,s594,s595,s596,s597,s598,s599,s600,s601,s602,s603,s604,s605,s606,s607,s608,s609,s610,s611,s612,s613,s614,s563,s565,s560,s562,s615,s616,s617,s656,s631,s657,s658,s659,s660,s661,s662,s663] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h552,h553,h554,h252,h555,h556,h557,h329,h558,h559,h560,h407,h561,h562,h563,h482,h564,h565,h566,h567,h568,h569,h570,h571,h572,h573,h574,h575,h576,h577,h578,h579,h580,h581,h582,h583,h584,h585,h586,h587,h588,h589,h590,h591,h592,h593,h594,h595,h596,h597,h598,h599,h600,h601,h602,h603,h604,h605,h606,h607,h608,h609,h610,h611,h612,h613,h614,h615,h616,h617,h567,h569,h564,h566,h618,h619,h620,h659,h660,h661,h662,h663,h664,h665,h666,h667⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h668 : NoPlan 7 s564 := banByRestriction (mask:=0x536124d8944db7) (j:=0) (bank:=s13) (budget:=5) (by decide +kernel) p7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h669 : NoPlan 7 s561 := viaSymmetry perm2 inv2 invId2 h668 (by decide +kernel)
def s664 : List Wire := [v69,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h670 : NoPlan 7 s664 := viaSymmetry perm1 inv1 invId1 h550 (by decide +kernel)
def s665 : List Wire := [v70,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h671 : NoPlan 7 s665 := viaSymmetry perm1 inv1 invId1 h551 (by decide +kernel)
def s666 : List Wire := [v71,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h672 : NoPlan 7 s666 := viaSymmetry perm1 inv1 invId1 h668 (by decide +kernel)
def s667 : List Wire := [v72,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h673 : NoPlan 7 s667 := viaSymmetry perm4 inv4 invId4 h668 (by decide +kernel)
def s668 : List Wire := [v73,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h674 : NoPlan 7 s668 := viaSymmetry perm3 inv3 invId3 h550 (by decide +kernel)
def s669 : List Wire := [v74,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h675 : NoPlan 7 s669 := viaSymmetry perm3 inv3 invId3 h551 (by decide +kernel)
def s670 : List Wire := [v75,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h676 : NoPlan 7 s670 := viaSymmetry perm3 inv3 invId3 h668 (by decide +kernel)
def s671 : List Wire := [v76,v0,v1,v2,v3,v4]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h677 : NoPlan 7 s671 := viaSymmetry perm5 inv5 invId5 h668 (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem h0 : NoPlan 8 s0 := by
  apply banBySplit (by decide +kernel) (by decide +kernel)
  rw [show kids 7 s0 = [s1,s3,s9,s5,s237,s238,s249,s240,s381,s382,s383,s384,s385,s386,s387,s388,s389,s390,s401,s398,s538,s539,s540,s541,s542,s543,s544,s545,s546,s547,s564,s561,s664,s665,s666,s667,s668,s669,s670,s671] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨h1,h2,h91,h161,h235,h236,h310,h381,h382,h383,h384,h385,h386,h387,h388,h389,h390,h391,h464,h541,h542,h543,h544,h545,h546,h547,h548,h549,h550,h551,h668,h669,h670,h671,h672,h673,h674,h675,h676,h677⟩
theorem cert : NoPlan 8 base5 := h0
theorem probe_pos : ∀ i : Fin 55, target (probeP i) = true := by decide +kernel
theorem probe_neg : ∀ i : Fin 55, target (probeN i) = false := by decide +kernel
theorem pinsP : ∀ i : Fin 55, pins.map (side false i) = List.ofFn (probeP i) := by decide +kernel
theorem pinsN : ∀ i : Fin 55, pins.map (side true i) = List.ofFn (probeN i) := by decide +kernel
theorem pinsNodup : pins.Nodup := by decide

theorem circuitHit (C : Circuit) (leg : ∀g∈C.gates,legal g)
    (correct : ∀x,C.eval (List.ofFn x) = target x) : hit ((wordRun C.gates pins).getD C.output zero) := by
  apply (hit_iff _).2
  intro i
  have output (n : Bool) : side n i ((wordRun C.gates pins).getD C.output zero) =
      C.eval (pins.map (side n i)) := by
    have hzero : side n i zero=false := by cases n <;> simp [side,zero]
    rw [←List.getD_map (wordRun C.gates pins) zero (n:=C.output) (side n i),hzero,sideRun n i C.gates pins leg]; rfl
  have m := output false
  have n := output true
  rw [pinsP,correct,probe_pos] at m
  rw [pinsN,correct,probe_neg] at n
  intro eq
  change ((wordRun C.gates pins).getD C.output zero).1[i.val] = true at m
  change ((wordRun C.gates pins).getD C.output zero).2[i.val] = false at n
  rw [eq,n] at m
  contradiction

theorem noSmall (root : NoPlan 9 pins) (C : Circuit) (leg : ∀g∈C.gates,legal g) (small : count C.gates≤9)
    (correct : ∀x,C.eval (List.ofFn x)=target x) : False := by
  obtain ⟨m,mb,S,sub,pl⟩ := fromRun C.gates pins.toFinset pins C.output
    (fun w hw=>Or.inr ⟨w,List.mem_toFinset.mpr hw,Or.inl rfl⟩) leg (circuitHit C leg correct)
  let xs := pins.filter fun w=>w∈S
  have eq : xs.toFinset=S := by
    ext w
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨List.mem_toFinset.mp (sub h),h⟩⟩
  have incl : xs∈pins.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have closed : pins.sublists.all (fun ys => ys==pins || allSig ys != BitVec.allOnes 55) = true := by decide +kernel
  have all := List.all_eq_true.mp closed xs incl
  have mask : allSig xs=BitVec.allOnes 55 := by
    apply adequate; intro i; obtain ⟨w,hw,sep⟩ := pl.cover i
    exact ⟨w,List.mem_toFinset.mp (eq.symm ▸ hw),sep⟩
  have same : xs=pins := by simpa only [mask,bne_self_eq_false,Bool.or_false,beq_iff_eq] using all
  have e : S=pins.toFinset := eq.symm.trans (congrArg List.toFinset same)
  exact root m (by omega) (e ▸ pl)

theorem count_le (gs : List Gate) : count gs ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have one : cost g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [cost]
    change cost g + count gs ≤ gs.length + 1
    omega

theorem full_cost (gs : List Gate) (leg : ∀g∈gs,legal g) (h : count gs=gs.length) :
    ∀g∈gs, (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    change cost g + count gs = gs.length+1 at h
    have co : cost g≤1 := by cases g with | mk op ins=> cases op <;> simp [cost]
    have b := count_le gs
    have cg : cost g=1 := by omega
    have tl : count gs=gs.length := by omega
    have og := (leg g (by simp)).1
    have op : g.op=.and ∨ g.op=.or := by
      rcases og with oa|oo|on
      · exact Or.inl oa
      · exact Or.inr oo
      · simp [cost,on] at cg
    intro u hu
    rcases List.mem_cons.mp hu with rfl|mem
    · exact op
    · exact ih (fun z hz=>leg z (by simp [hz])) tl u mem

theorem positiveFromRoot (root : NoPlan 9 pins) : ∀s : ℕ, HasCircuitSize 6 target s → ∃C : Circuit,
    Monotone2 C ∧ C.size ≤ s ∧ ∀x, C.eval (List.ofFn x) = target x := by
  intro s hs
  by_cases hs9 : 11 ≤ s
  · exact ⟨monoEleven,elevenMono,elevenSize.le.trans hs9,elevenEval⟩
  obtain ⟨C,fan,sz,correct⟩ := hs
  have leg : ∀g∈C.gates,legal g := fun g h=>fan g h
  by_cases full : count C.gates=C.gates.length
  · exact ⟨C,fun g hg=>⟨full_cost _ leg full g hg,(leg g hg).2⟩,sz,correct⟩
  have cnt := count_le C.gates
  change C.gates.length ≤ s at sz
  exact (noSmall root C leg (by omega) correct).elim

end PEqualNP.Outside.L_meta_39695_aux

theorem PEqualNP.Outside.L_meta_39695 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3941132456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :=
  PEqualNP.Outside.L_meta_39695_aux.positiveFromRoot (PEqualNP.Outside.L_meta_39695_aux.liftRoot PEqualNP.Outside.L_meta_39695_aux.cert)
