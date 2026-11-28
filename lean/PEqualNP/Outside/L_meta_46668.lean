import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46668
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 128
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.and, [11, 16]⟩,
    ⟨.or, [13, 17]⟩], 18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 13 := rfl

def decNat (b : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | f+1, n, acc => bif Nat.beq n 0 then acc.reverse else decNat b f (n / b) ((n % b - 1) :: acc)
def dL (n : Nat) : List Nat := decNat 4096 200 n []
def dS (n : Nat) : List Nat := decNat 256 200 n []
def decH : Nat → Nat → List Nat → List (List Nat) → List (List Nat)
  | 0, _, cur, acc => (cur.reverse :: acc).reverse
  | f+1, n, cur, acc =>
    bif Nat.beq n 0 then (cur.reverse :: acc).reverse
    else bif Nat.beq (n % 256) 255 then decH f (n / 256) [] (cur.reverse :: acc)
    else decH f (n / 256) ((n % 256 - 1) :: cur) acc
def dH (n : Nat) : List (List Nat) := decH 4096 n [] []
def trip : List Nat → List (Nat × Nat × Nat)
  | a :: b :: c :: r => (a, b, c) :: trip r
  | _ => []
def aH (nc ns : Nat) : List (List Nat) := List.replicate 64 ((List.range ns).map (· + 100) ++ List.range nc)
def pH (n nc ns : Nat) : List (List Nat) := (decNat 16 64 n []).map (fun c => (List.range ns).map (· + 100) ++ c :: List.range nc)
def dC (n : Nat) : Nat × List (Nat × Nat × Nat) :=
  match decNat 256 200 n [] with
  | s :: ds => (s, trip ds)
  | [] => (0, [])
def dw (n : Nat) : Nat := n * 18446744073709551617
def w0 : Nat := dw 0xf0f0f0f0f0f0f0f0
def w1 : Nat := dw 0xaaaaaaaaaaaaaaaa
def w2 : Nat := dw 0xcccccccccccccccc
def w3 : Nat := dw 0xff00ff00ff00ff00
def w4 : Nat := dw 0xffff0000ffff0000
def w5 : Nat := dw 0xffffffff00000000
def w6 : Nat := dw 0xeeeeeeeeeeeeeeee
def w7 : Nat := dw 0xf0f00000f0f00000
def w8 : Nat := dw 0xffccffccffccffcc
def w9 : Nat := dw 0xffaaffaaffaaffaa
def w10 : Nat := dw 0x4444444444444444
def w11 : Nat := dw 0xfafaaaaafafaaaaa
def w12 : Nat := dw 0xc0c0c0c0c0c0c0c0
def w13 : Nat := dw 0xffffccccffffcccc
def w14 : Nat := dw 0xf000f000f000f000
def w15 : Nat := dw 0xffffaaaaffffaaaa
def w16 : Nat := dw 0xcc00cc00cc00cc00
def w17 : Nat := dw 0x3030303030303030
def w18 : Nat := dw 0x5050505050505050
def w19 : Nat := dw 0xcccc0000cccc0000
def w20 : Nat := dw 0xfcfcfcfcfcfcfcfc
def w21 : Nat := dw 0xeaeaeaeaeaeaeaea
def w22 : Nat := dw 0x2222222222222222
def w23 : Nat := dw 0xff000000ff000000
def w24 : Nat := dw 0xfafafafafafafafa
def w25 : Nat := dw 0xee00ee00ee00ee
def w26 : Nat := dw 0xffff00000000
def w27 : Nat := dw 0xcc00cc00cc00cc
def w28 : Nat := dw 0x8888888888888888
def w29 : Nat := dw 0xffffffffffff0000
def w30 : Nat := dw 0xeeee0000eeee0000
def w31 : Nat := dw 0xff88ff88ff88ff88
def w32 : Nat := dw 0xe0e0e0e0e0e0e0e0
def w33 : Nat := dw 0xeeeeaaaaeeeeaaaa
def w34 : Nat := dw 0xfaaafaaafaaafaaa
def w35 : Nat := dw 0xffaaaaaaffaaaaaa
def w36 : Nat := dw 0x3322332233223322
def w37 : Nat := dw 0x3300330033003300
def w38 : Nat := dw 0xffff8888ffff8888
def w39 : Nat := dw 0x5555000055550000
def w40 : Nat := dw 0xe0e0e0e0e0e0e0e
def w41 : Nat := dw 0x5500550055005500
def w42 : Nat := dw 0xfff0fff0fff0fff0
def w43 : Nat := dw 0xc0ccccc0c0ccccc
def w44 : Nat := dw 0xf00ff000f00ff00
def w45 : Nat := dw 0xf000f000f000f0
def w46 : Nat := dw 0xfcccfcccfcccfccc
def w47 : Nat := dw 0xeeee0000eeee
def w48 : Nat := dw 0x5555555500000000
def w49 : Nat := dw 0xfffff0f0fffff0f0
def w50 : Nat := dw 0xc0c0c0c0c0c0c0c
def w51 : Nat := dw 0xfff00000fff00000
def w52 : Nat := dw 0xcccc0000cccc
def w53 : Nat := dw 0xa0a0a0a0a0a0a0a0
def w54 : Nat := dw 0xa0a0a0a0a0a0a0a
def w55 : Nat := dw 0xffaa0000ffaa0000
def w56 : Nat := dw 0xee00ee00ee00ee00
def w57 : Nat := dw 0xeeaaeeaaeeaaeeaa
def w58 : Nat := dw 0xf0f00000f0f0
def w59 : Nat := dw 0xffffeeeeffffeeee
def w60 : Nat := dw 0xfcfcccccfcfccccc
def w61 : Nat := dw 0xcc88cc88cc88cc88
def w62 : Nat := dw 0xfff0ff00fff0ff00
def w63 : Nat := dw 0xeeeeeeeecccccccc
def w64 : Nat := dw 0x3333333300000000
def w65 : Nat := dw 0x5544554455445544
def w66 : Nat := dw 0x3333000033330000
def w67 : Nat := dw 0xf0a0f0a0f0a0f0a0
def w68 : Nat := dw 0xf8f8f8f8f8f8f8f8
def w69 : Nat := dw 0xf0f0f0f000000000
def w70 : Nat := dw 0x7777000077770000
def w71 : Nat := dw 0xff000000ff0000
def w72 : Nat := dw 0xf0c0f0c0f0c0f0c0
def w73 : Nat := dw 0x33cc33cc33cc33cc
def w74 : Nat := dw 0xaa00aa00aa00aa
def w75 : Nat := dw 0xecececececececec
def w76 : Nat := dw 0xf0f0f0f00000000
def w77 : Nat := dw 0xaaaa0000aaaa
def w78 : Nat := dw 0xccc0ccc0ccc0ccc
def w79 : Nat := dw 0x5555444455554444
def w80 : Nat := dw 0xffffffffcccccccc
def w81 : Nat := dw 0xffffffffaaaaaaaa
def w82 : Nat := dw 0x3f003f003f003f00
def w83 : Nat := dw 0xbabababababababa
def w84 : Nat := dw 0xfff00000fff0000
def w85 : Nat := dw 0xfcf0cc00fcf0cc00
def w86 : Nat := dw 0x3333222233332222
def w87 : Nat := dw 0xffffeeee00000000
def w88 : Nat := dw 0xaaaaaaaa00000000
def w89 : Nat := dw 0x7070707070707070
def w90 : Nat := dw 0xdcdcdcdcdcdcdcdc
def w91 : Nat := dw 0x3300ff003300ff00
def w92 : Nat := dw 0xcccccc00cccccc
def w93 : Nat := dw 0xe0eeeee0e0eeeee
def w94 : Nat := dw 0xfaaaaaaafaaaaaaa
def w95 : Nat := dw 0xeaeaaaaaeaeaaaaa
def w96 : Nat := dw 0xf0affaa0f0affaa
def w97 : Nat := dw 0xffff3333ffff0000
def w98 : Nat := dw 0xeeeeeeee
def w99 : Nat := dw 0xe0e0e0eeeeeeeee
def w100 : Nat := dw 0xcccccccc00000000
def w101 : Nat := dw 0xaa00aa00aa00aa00
def w102 : Nat := dw 0xffeeffeeffeeffee
def w103 : Nat := dw 0xffcc0000ffcc0000
def w104 : Nat := dw 0xf0cffcc0f0cffcc
def w105 : Nat := dw 0xf000f000f000f00
def w106 : Nat := dw 0xf0f0f0f0
def w107 : Nat := dw 0xeeeeeeeeeeee0000
def w108 : Nat := dw 0xcccceeeecccceeee
def w109 : Nat := dw 0x3232323232323232
def w110 : Nat := dw 0x5454545454545454
def w111 : Nat := dw 0x5050000050500000
def w112 : Nat := dw 0xafaf0000afaf0000
def w113 : Nat := dw 0xa0a0f0f0a0a0f0f0
def w114 : Nat := dw 0xffc0ffc0ffc0ffc0
def w115 : Nat := dw 0xffccff00ffccff00
def w116 : Nat := dw 0xcececececececece
def w117 : Nat := dw 0xfffffffff0f0f0f0
def w118 : Nat := dw 0x5555555555550000
def w119 : Nat := dw 0xeeeeeeee00000000
def w120 : Nat := dw 0xfcfcfcfccccccccc
def w121 : Nat := dw 0xffffaaaaffff0000
def w122 : Nat := dw 0xffffff88ff00ff00
def w123 : Nat := dw 0x1e1e1e1e1e1e1e1e
def w124 : Nat := dw 0x7700770077007700
def w125 : Nat := dw 0x3330333033303330
def w126 : Nat := dw 0xff44ff44ff44ff44
def w127 : Nat := dw 0xffccccccffcccccc
def w128 : Nat := dw 0xee00aa00ee00aa
def w129 : Nat := dw 0xfffff0f0ffff0000
def w130 : Nat := dw 0xcccccccc
def w131 : Nat := dw 0xf0f0a0a0f0f0a0a0
def w132 : Nat := dw 0xaaaaaaaa
def w133 : Nat := dw 0xfcfcfcfcfcfc0000
def w134 : Nat := dw 0xfefefefefefefefe
def w135 : Nat := dw 0xaaeeaaeeaaeeaaee
def w136 : Nat := dw 0xff330000ff330000
def w137 : Nat := dw 0xbbbbaaaabbbbaaaa
def w138 : Nat := dw 0xf0fc00ccf0fc00cc
def w139 : Nat := dw 0x3222322232223222
def w140 : Nat := dw 0xeee0eee0eee0eee
def w141 : Nat := dw 0x3232222232322222
def w142 : Nat := dw 0x3322222233222222
def w143 : Nat := dw 0xf3f03300f3f03300
def w144 : Nat := dw 0xea00ea00ea00ea
def w145 : Nat := dw 0xfa00aa00fa00aa
def w146 : Nat := dw 0xddddddddcccccccc
def w147 : Nat := dw 0xfcfc0000fcfc
def w148 : Nat := dw 0xaaaa8888aaaa8888
def w149 : Nat := dw 0xfafafafaaaaaaaaa
def w150 : Nat := dw 0xeeeeeeeeaaaaaaaa
def w151 : Nat := dw 0xeeee0000cccc
def w152 : Nat := dw 0x11111111eeeeeeee
def w153 : Nat := dw 0xe000e00ee00ee
def w154 : Nat := dw 0xfe00fe00fe00fe
def w155 : Nat := dw 0x1010101010101010
def w156 : Nat := dw 0xff50ff50ff50ff50
def w157 : Nat := dw 0xddddccccddddcccc
def w158 : Nat := dw 0xc0c00000c0c00000
def w159 : Nat := dw 0x3f3f00003f3f0000
def w160 : Nat := dw 0x3030f0f03030f0f0
def w161 : Nat := dw 0xf0000000f0000000
def w162 : Nat := dw 0xaafaaafaaafaaafa
def w163 : Nat := dw 0xf0f0f000f0f0f0
def w164 : Nat := dw 0xaaffaaaaaaffaaaa
def w165 : Nat := dw 0xc888c888c888c888
def w166 : Nat := dw 0xc8c88888c8c88888
def w167 : Nat := dw 0xeeeeee00eeeeee
def w168 : Nat := dw 0xcc888888cc888888
def w169 : Nat := dw 0xea00ea00ea00ea00
def w170 : Nat := dw 0x3f2a3f2a3f2a3f2a
def w171 : Nat := dw 0xee00aa00ee00aa00
def w172 : Nat := dw 0x3322ffaa3322ffaa
def w173 : Nat := dw 0xfa00aa00fa00aa00
def w174 : Nat := dw 0xfac8aa88fac8aa88
def w175 : Nat := dw 0xaeaeeeeeaeaeeeee
def w176 : Nat := dw 0xafaaffaaafaaffaa
def w177 : Nat := dw 0xfeeefeeefeeefeee
def w178 : Nat := dw 0xfefeeeeefefeeeee
def w179 : Nat := dw 0xfffaffaafffaffaa
def w180 : Nat := dw 0xf5f50000f5f50000
def w181 : Nat := dw 0xfcfc0000fcfc0000
def w182 : Nat := dw 0xaeaeaeaeaeaeaeae
def w183 : Nat := dw 0xffff3030ffff3030
def w184 : Nat := dw 0xffffeeee
def w185 : Nat := dw 0xffff2222ffff2222
def w186 : Nat := dw 0xfafa0000fafa
def w187 : Nat := dw 0xccccfcfcccccfcfc
def w188 : Nat := dw 0x3333333333330000
def w189 : Nat := dw 0xffff5555ffff0000
def w190 : Nat := dw 0xf0f0a0a0f0f0a0a
def w191 : Nat := dw 0x30f030f030f030f0
def w192 : Nat := dw 0xaaaa0000aaaa0000
def w193 : Nat := dw 0x44004400440044
def w194 : Nat := dw 0xddccddccddccddcc
def w195 : Nat := dw 0xff55ff00ff55ff00
def w196 : Nat := dw 0xff30ff30ff30ff30
def w197 : Nat := dw 0xcfcf0000cfcf0000
def w198 : Nat := dw 0xbbaabbaabbaabbaa
def w199 : Nat := dw 0xc0c0f0f0c0c0f0f0
def w200 : Nat := dw 0xff0f0000ff0f0000
def w201 : Nat := dw 0xf000f0f0f000f0f0
def w202 : Nat := dw 0x1100ff001100ff00
def w203 : Nat := dw 0xfe00ee00fe00ee
def w204 : Nat := dw 0x3332332233323322
def w205 : Nat := dw 0xbfaabfaabfaabfaa
def w206 : Nat := dw 0xffeaffeaffeaffea
def w207 : Nat := dw 0xbbaaffaabbaaffaa
def w208 : Nat := dw 0xffeeffaaffeeffaa
def w209 : Nat := dw 0x5444544454445444
def w210 : Nat := dw 0xaeeeaeeeaeeeaeee
def w211 : Nat := dw 0xfeee0000feee0000
def w212 : Nat := dw 0xffc8ff88ffc8ff88
def w213 : Nat := dw 0xfecceeccfecceecc
def w214 : Nat := dw 0xaaeeeeeeaaeeeeee
def w215 : Nat := dw 0xffeeeeeeffeeeeee
def w216 : Nat := dw 0xcceecceecceeccee
def w217 : Nat := dw 0x7777777700000000
def w218 : Nat := dw 0x3333333322222222
def w219 : Nat := dw 0x5555555544444444
def w220 : Nat := dw 0xbbbbbbbbaaaaaaaa
def w221 : Nat := dw 0x1111111100000000
def w222 : Nat := dw 0xffffffffeeeeeeee
def w223 : Nat := dw 0xffff0f0fffff0000
def w224 : Nat := dw 0xffffa0a0ffffa0a0
def w225 : Nat := dw 0xfafafafafafa0000
def w226 : Nat := dw 0x3333303033333030
def w227 : Nat := dw 0xffffc0c0ffffc0c0
def w228 : Nat := dw 0xffffaaaa00000000
def w229 : Nat := dw 0xffff0c0cffff0c0c
def w230 : Nat := dw 0xcccc8888cccc8888
def w231 : Nat := dw 0x444400004444
def w232 : Nat := dw 0xffffccccffff0000
def w233 : Nat := dw 0x33332222ffffaaaa
def w234 : Nat := dw 0xf0f0a0affffaaaa
def w235 : Nat := dw 0xe0e0e0e0c0c0c0c0
def w236 : Nat := dw 0xe0e0e0e0c0c0c0c
def w237 : Nat := dw 0xff0eff0effeeffee
def w238 : Nat := dw 0xc000c000c000c000
def w239 : Nat := dw 0x22aa22aa22aa22aa
def w240 : Nat := dw 0xaaa0aaa0aaa0aaa
def w241 : Nat := dw 0x4444cccc4444cccc
def w242 : Nat := dw 0x2222aaaa2222aaaa
def w243 : Nat := dw 0xf0e0f0e0f0e0f0e
def w244 : Nat := dw 0x3332333233323332
def w245 : Nat := dw 0x5554555455545554
def w246 : Nat := dw 0xfffafffafffafffa
def w247 : Nat := dw 0xfa00fa00fa00fa
def w248 : Nat := dw 0xf0a0f0a0f0a0f0a
def w249 : Nat := dw 0xfffcfffcfffcfffc
def w250 : Nat := dw 0xfc00fc00fc00fc
def w251 : Nat := dw 0xf0c0f0c0f0c0f0c
def w252 : Nat := dw 0x5550555055505550
def w253 : Nat := dw 0x4400440044004400
def w254 : Nat := dw 0x8c8c8c8c8c8c8c8c
def w255 : Nat := dw 0xaaff0000aaff0000
def w256 : Nat := dw 0x8888cccc8888cccc
def w257 : Nat := dw 0x30003000300030
def w258 : Nat := dw 0x33ff000033ff0000
def w259 : Nat := dw 0xff33ff00ff33ff00
def w260 : Nat := dw 0xccffccccccffcccc
def w261 : Nat := dw 0xcc00cccccc00cccc
def w262 : Nat := dw 0x1f001f001f001f00
def w263 : Nat := dw 0xf0effee0f0effee
def w264 : Nat := dw 0xdc50cc00dc50cc00
def w265 : Nat := dw 0xc4c0c4c0c4c0c4c
def w266 : Nat := dw 0x44cccc0044cccc
def w267 : Nat := dw 0x5540554055405540
def w268 : Nat := dw 0xffea0000ffea0000
def w269 : Nat := dw 0x1500150015001500
def w270 : Nat := dw 0x1515000015150000
def w271 : Nat := dw 0xffeaeaeaffeaeaea
def w272 : Nat := dw 0xffc0c0c0ffc0c0c0
def w273 : Nat := dw 0x5540404055404040
def w274 : Nat := dw 0xe0a0e0a0e0a0e0a0
def w275 : Nat := dw 0x1050105010501050
def w276 : Nat := dw 0xeeaa0000eeaa0000
def w277 : Nat := dw 0x1155000011550000
def w278 : Nat := dw 0xfefaeeaafefaeeaa
def w279 : Nat := dw 0xe0aeeaa0e0aeeaa
def w280 : Nat := dw 0xf0c00000f0c00000
def w281 : Nat := dw 0xf3f00000f3f0000
def w282 : Nat := dw 0x30f0f00030f0f0
def w283 : Nat := dw 0x5450440054504400
def w284 : Nat := dw 0xfaeaaaaafaeaaaaa
def w285 : Nat := dw 0x5554554455545544
def w286 : Nat := dw 0x5544550055445500
def w287 : Nat := dw 0x1010505010105050
def w288 : Nat := dw 0xf0e0f0a0f0e0f0a0
def w289 : Nat := dw 0x1100550011005500
def w290 : Nat := dw 0xfeeefaaafeeefaaa
def w291 : Nat := dw 0x5444500054445000
def w292 : Nat := dw 0xfcccf000fcccf000
def w293 : Nat := dw 0x444044404440444
def w294 : Nat := dw 0x555000005550000
def w295 : Nat := dw 0x5454444454544444
def w296 : Nat := dw 0x5550550055505500
def w297 : Nat := dw 0xfe00ee00fe00ee00
def w298 : Nat := dw 0x404444404044444
def w299 : Nat := dw 0xccc8cc88ccc8cc88
def w300 : Nat := dw 0x500550005005500
def w301 : Nat := dw 0xfc00cc00fc00cc
def w302 : Nat := dw 0xff0cffccff0cffcc
def w303 : Nat := dw 0x3330330033303300
def w304 : Nat := dw 0xcfccffcccfccffcc
def w305 : Nat := dw 0x50505000505050
def w306 : Nat := dw 0x5544444455444444
def w307 : Nat := dw 0xf0e0e0e0f0e0e0e0
def w308 : Nat := dw 0x44444400444444
def w309 : Nat := dw 0x1010f0f01010f0f0
def w310 : Nat := dw 0xf444f444f444f444
def w311 : Nat := dw 0xeaaaeaaaeaaaeaaa
def w312 : Nat := dw 0xeeaaaaaaeeaaaaaa
def w313 : Nat := dw 0xffa0ffa0ffa0ffa0
def w314 : Nat := dw 0xaa88aa88aa88aa88
def w315 : Nat := dw 0x22002200220022
def w316 : Nat := dw 0x6666666666666666
def w317 : Nat := dw 0xaaa0aaa0aaa0aaa0
def w318 : Nat := dw 0xccc0ccc0ccc0ccc0
def w319 : Nat := dw 0xfefe0000fefe
def w320 : Nat := dw 0xf0f0e0e0f0f0e0e0
def w321 : Nat := dw 0xf0f0e0e0f0f0e0e
def w322 : Nat := dw 0xffffeeeeffff0000
def w323 : Nat := dw 0xffff0000eeee
def w324 : Nat := dw 0xeeeee0e0eeeee0e0
def w325 : Nat := dw 0xeeee0e0eeeee0e0e
def w326 : Nat := dw 0xeeeeeeeee0e0e0e0
def w327 : Nat := dw 0xeeeeeeee0e0e0e0e
def w328 : Nat := dw 0xe0e0e0e0eeeeeeee
def w329 : Nat := dw 0xffff4444ffff4444
def w330 : Nat := dw 0xecec0000ecec
def w331 : Nat := dw 0xffff0a0affff0a0a
def w332 : Nat := dw 0xffff5050ffff5050
def w333 : Nat := dw 0xfffffafafffffafa
def w334 : Nat := dw 0x505000005050
def w335 : Nat := dw 0xcfcfcfcfcccccccc
def w336 : Nat := dw 0xeaeaeaeac0c0c0c0
def w337 : Nat := dw 0xffaaff88ffaaff88
def w338 : Nat := dw 0x222200002222
def w339 : Nat := dw 0xf0f0c0c0f0f0c0c0
def w340 : Nat := dw 0xfffffcfcfffffcfc
def w341 : Nat := dw 0x303000003030
def w342 : Nat := dw 0xf0f0c0c0f0f0c0c
def w343 : Nat := dw 0xfcfc0000cccc
def w344 : Nat := dw 0xecececececec0000
def w345 : Nat := dw 0xc0c0e0ecccceeee
def w346 : Nat := dw 0x7f007f007f007f00
def w347 : Nat := dw 0x70f070f070f070f0
def w348 : Nat := dw 0x4ccc4ccc4ccc4ccc
def w349 : Nat := dw 0x2aaa2aaa2aaa2aaa
def w350 : Nat := dw 0x8080808080808080
def w351 : Nat := dw 0x8800880088008800
def w352 : Nat := dw 0x4c4c4c4c4c4c4c4c
def w353 : Nat := dw 0xa000a000a000a000
def w354 : Nat := dw 0x5f005f005f005f00
def w355 : Nat := dw 0x44cc44cc44cc44cc
def w356 : Nat := dw 0x50f050f050f050f0
def w357 : Nat := dw 0x2a2a2a2a2a2a2a2a
def w358 : Nat := dw 0xf8f8f0f0f8f8f0f0
def w359 : Nat := dw 0xff88ff00ff88ff00
def w360 : Nat := dw 0x8888000088880000
def w361 : Nat := dw 0x1100110011001100
def w362 : Nat := dw 0x1111000011110000
def w363 : Nat := dw 0x4040404040404040
def w364 : Nat := dw 0xb0b0b0b0b0b0b0b0
def w365 : Nat := dw 0xbb00bb00bb00bb00
def w366 : Nat := dw 0x4444000044440000
def w367 : Nat := dw 0xbbbb0000bbbb0000
def w368 : Nat := dw 0x5000500050005000
def w369 : Nat := dw 0x50005000500050
def w370 : Nat := dw 0xaf00af00af00af00
def w371 : Nat := dw 0x55000000550000
def w372 : Nat := dw 0x88cc88cc88cc88cc
def w373 : Nat := dw 0xa0f0a0f0a0f0a0f0
def w374 : Nat := dw 0x5500000055000000
def w375 : Nat := dw 0xaa00ff00aa00ff00
def w376 : Nat := dw 0xc000c000c000c0
def w377 : Nat := dw 0x3000300030003000
def w378 : Nat := dw 0xcf00cf00cf00cf00
def w379 : Nat := dw 0x3030000030300000
def w380 : Nat := dw 0xcc000000cc000000
def w381 : Nat := dw 0x33000000330000
def w382 : Nat := dw 0xf030f030f030f030
def w383 : Nat := dw 0xcc000000cc0000
def w384 : Nat := dw 0xc0f0c0f0c0f0c0f0
def w385 : Nat := dw 0x3300000033000000
def w386 : Nat := dw 0xccff0000ccff0000
def w387 : Nat := dw 0xcc00ff00cc00ff00
def w388 : Nat := dw 0xccfcccfcccfcccfc
def w389 : Nat := dw 0xcc0ccc0ccc0ccc0c
def w390 : Nat := dw 0xf0000000f00000
def w391 : Nat := dw 0x1fff00001fff0000
def w392 : Nat := dw 0x1f00ff001f00ff00
def w393 : Nat := dw 0x10f0f0f010f0f0f0
def w394 : Nat := dw 0xf0fe00eef0fe00ee
def w395 : Nat := dw 0xeeeeeee0eeeeeee
def w396 : Nat := dw 0xe0ee00eee0ee00ee
def w397 : Nat := dw 0xf04ff440f04ff44
def w398 : Nat := dw 0xdcdcdc00dcdcdc
def w399 : Nat := dw 0x3310ff503310ff50
def w400 : Nat := dw 0xaf8cffccaf8cffcc
def w401 : Nat := dw 0x50dc00cc50dc00cc
def w402 : Nat := dw 0x7350330073503300
def w403 : Nat := dw 0x3f7f00003f7f0000
def w404 : Nat := dw 0x3f2affaa3f2affaa
def w405 : Nat := dw 0x3070f0f03070f0f0
def w406 : Nat := dw 0xf3f23322f3f23322
def w407 : Nat := dw 0xc4ccccc0c4ccccc
def w408 : Nat := dw 0xf3a23322f3a23322
def w409 : Nat := dw 0xd0cddcc0d0cddcc
def w410 : Nat := dw 0xddd0ccc0ddd0ccc
def w411 : Nat := dw 0x3f153f003f153f00
def w412 : Nat := dw 0x15ff000015ff0000
def w413 : Nat := dw 0xeaeaea00eaeaea
def w414 : Nat := dw 0xea00aa00ea00aa00
def w415 : Nat := dw 0xffeaffaaffeaffaa
def w416 : Nat := dw 0xea00aa00ea00aa
def w417 : Nat := dw 0x1500550015005500
def w418 : Nat := dw 0x3f2a2a2a3f2a2a2a
def w419 : Nat := dw 0xbbeebbeebbeebbee
def w420 : Nat := dw 0x1144114411441144
def w421 : Nat := dw 0x30c030c030c030c0
def w422 : Nat := dw 0xc030c030c030c030
def w423 : Nat := dw 0x33cc000033cc0000
def w424 : Nat := dw 0xcc330000cc330000
def w425 : Nat := dw 0x32fa22aa32fa22aa
def w426 : Nat := dw 0x504554405045544
def w427 : Nat := dw 0xf3c03300f3c03300
def w428 : Nat := dw 0xf0cc00ccf0cc00cc
def w429 : Nat := dw 0xafaeffeeafaeffee
def w430 : Nat := dw 0xfafeaaeefafeaaee
def w431 : Nat := dw 0x5054004450540044
def w432 : Nat := dw 0xfa32aa22fa32aa22
def w433 : Nat := dw 0xfbfabbaafbfabbaa
def w434 : Nat := dw 0x5150110051501100
def w435 : Nat := dw 0xc8fa88aac8fa88aa
def w436 : Nat := dw 0x10f050f010f050f0
def w437 : Nat := dw 0xeee0aaa0eee0aaa
def w438 : Nat := dw 0x3222faaa3222faaa
def w439 : Nat := dw 0x3777000037770000
def w440 : Nat := dw 0xc8888888c8888888
def w441 : Nat := dw 0xfeeeeeeefeeeeeee
def w442 : Nat := dw 0x444444404444444
def w443 : Nat := dw 0x3222222232222222
def w444 : Nat := dw 0x3700770037007700
def w445 : Nat := dw 0x4cc44cc04cc44cc
def w446 : Nat := dw 0x3070707030707070
def w447 : Nat := dw 0xe000e000e000e000
def w448 : Nat := dw 0xe0e00000e0e00000
def w449 : Nat := dw 0x1f1f00001f1f0000
def w450 : Nat := dw 0x10f010f010f010f0
def w451 : Nat := dw 0xee000000ee000000
def w452 : Nat := dw 0x11ff000011ff0000
def w453 : Nat := dw 0xf0e0f0e0f0e0f0e0
def w454 : Nat := dw 0xffee0000ffee0000
def w455 : Nat := dw 0xf010f010f010f010
def w456 : Nat := dw 0xff110000ff110000
def w457 : Nat := dw 0xee0eee0eee0eee0e
def w458 : Nat := dw 0xee00eeeeee00eeee
def w459 : Nat := dw 0xf4f44444f4f44444
def w460 : Nat := dw 0xff444444ff444444
def w461 : Nat := dw 0xc080c080c080c080
def w462 : Nat := dw 0xcf8acf8acf8acf8a
def w463 : Nat := dw 0x3070307030703070
def w464 : Nat := dw 0xcc880000cc880000
def w465 : Nat := dw 0x3377000033770000
def w466 : Nat := dw 0xc0d0c0d0c0d0c0d0
def w467 : Nat := dw 0xccdd0000ccdd0000
def w468 : Nat := dw 0xcc88ffaacc88ffaa
def w469 : Nat := dw 0xf0a00000f0a00000
def w470 : Nat := dw 0xf5f00000f5f0000
def w471 : Nat := dw 0x50f0f00050f0f0
def w472 : Nat := dw 0xd5c0d5c0d5c0d5c0
def w473 : Nat := dw 0xddcc5500ddcc5500
def w474 : Nat := dw 0xf5f05500f5f05500
def w475 : Nat := dw 0xeaea0000eaea0000
def w476 : Nat := dw 0x3fff00003fff0000
def w477 : Nat := dw 0xffc0ff00ffc0ff00
def w478 : Nat := dw 0x3f00ff003f00ff00
def w479 : Nat := dw 0xefaaefaaefaaefaa
def w480 : Nat := dw 0x30f0f0f030f0f0f0
def w481 : Nat := dw 0xfaeafaeafaeafaea
def w482 : Nat := dw 0xfffcffccfffcffcc
def w483 : Nat := dw 0xffeeaaaaffeeaaaa
def w484 : Nat := dw 0xe0e0a0a0e0e0a0a0
def w485 : Nat := dw 0xeeaaffaaeeaaffaa
def w486 : Nat := dw 0xfaaa0000faaa0000
def w487 : Nat := dw 0xfcccccccfccccccc
def w488 : Nat := dw 0xccccccc0ccccccc
def w489 : Nat := dw 0xeeaeeeaeeeaeeeae
def w490 : Nat := dw 0xf0a0a0a0f0a0a0a0
def w491 : Nat := dw 0xeeaaeeeeeeaaeeee
def w492 : Nat := dw 0xf3e23322f3e23322
def w493 : Nat := dw 0xf0ee00eef0ee00ee
def w494 : Nat := dw 0x15ea15ea15ea15ea
def w495 : Nat := dw 0xf3fc33ccf3fc33cc
def w496 : Nat := dw 0x30c33cc030c33cc
def w497 : Nat := dw 0xfcc0cc00fcc0cc00
def w498 : Nat := dw 0x11ee55aa11ee55aa
def w499 : Nat := dw 0x3666366636663666
def w500 : Nat := dw 0x3636666636366666
def w501 : Nat := dw 0x5fa55aa05fa55aa
def w502 : Nat := dw 0x3366666633666666
def w503 : Nat := dw 0xfec8ee88fec8ee88
def w504 : Nat := dw 0xfafa0000fafa0000
def w505 : Nat := dw 0xeecceecceecceecc
def w506 : Nat := dw 0xf3f30000f3f30000
def w507 : Nat := dw 0xfcf0fcf0fcf0fcf0
def w508 : Nat := dw 0xcfcccfcccfcccfcc
def w509 : Nat := dw 0xf7f00000f7f0000
def w510 : Nat := dw 0xfff80000fff80000
def w511 : Nat := dw 0xfff88888fff88888
def w512 : Nat := dw 0xf0e0f000f0e0f000
def w513 : Nat := dw 0xf0e0f000f0e0f00
def w514 : Nat := dw 0xfeeef000feeef000
def w515 : Nat := dw 0x1110fff01110fff0
def w516 : Nat := dw 0xeeeee000eeeee
def w517 : Nat := dw 0x5777000057770000
def w518 : Nat := dw 0xaaa88888aaa88888
def w519 : Nat := dw 0x5554444455544444
def w520 : Nat := dw 0xf080f080f080f080
def w521 : Nat := dw 0xfff8fff8fff8fff8
def w522 : Nat := dw 0x70007000700070
def w523 : Nat := dw 0xf080f080f080f08
def w524 : Nat := dw 0xf888f888f888f888
def w525 : Nat := dw 0x7770777077707770
def w526 : Nat := dw 0x8f888f888f888f88
def w527 : Nat := dw 0xfefef0f0fefef0f0
def w528 : Nat := dw 0xffeeff00ffeeff00
def w529 : Nat := dw 0xeee0eee0eee0eee0
def w530 : Nat := dw 0xe0eee0eee0eee0ee
def w531 : Nat := dw 0xbbb0bbb0bbb0bbb0
def w532 : Nat := dw 0x4f444f444f444f44
def w533 : Nat := dw 0xffecffecffecffec
def w534 : Nat := dw 0xec00ec00ec00ec
def w535 : Nat := dw 0x3320332033203320
def w536 : Nat := dw 0x5f4c5f4c5f4c5f4c
def w537 : Nat := dw 0x30ba30ba30ba30ba
def w538 : Nat := dw 0xa888a888a888a888
def w539 : Nat := dw 0x222022202220222
def w540 : Nat := dw 0xfffaaaaafffaaaaa
def w541 : Nat := dw 0xaaaaa000aaaaa
def w542 : Nat := dw 0xfffcccccfffccccc
def w543 : Nat := dw 0xccccc000ccccc
def w544 : Nat := dw 0xff08ff08ff08ff08
def w545 : Nat := dw 0xf0f8f0f8f0f8f0f8
def w546 : Nat := dw 0xffc8ffc8ffc8ffc8
def w547 : Nat := dw 0xccc8ccc8ccc8ccc8
def w548 : Nat := dw 0xc0e0c0e0c0e0c0e
def w549 : Nat := dw 0xe0e0c0c0e0e0c0c
def w550 : Nat := dw 0xff88ffccff88ffcc
def w551 : Nat := dw 0xaaa8aaa8aaa8aaa8
def w552 : Nat := dw 0xae00ae00ae00ae
def w553 : Nat := dw 0xfaf8faf8faf8faf8
def w554 : Nat := dw 0xf8f8fafaf8f8fafa
def w555 : Nat := dw 0x808080808080808
def w556 : Nat := dw 0x88008800880088
def w557 : Nat := dw 0xf2f2f2f2f2f2f2f2
def w558 : Nat := dw 0x202020202020202
def w559 : Nat := dw 0xff22ff22ff22ff22
def w560 : Nat := dw 0xf4f4f4f4f4f4f4f4
def w561 : Nat := dw 0x404040404040404
def w562 : Nat := dw 0xc8c8c8c8c8c8c8c8
def w563 : Nat := dw 0xc4c4c4c4c4c4c4c4
def w564 : Nat := dw 0xff0aff0aff0aff0a
def w565 : Nat := dw 0xa000a000a000a
def w566 : Nat := dw 0xcc44cc44cc44cc44
def w567 : Nat := dw 0xf0faf0faf0faf0fa
def w568 : Nat := dw 0xeeeecccceeeecccc
def w569 : Nat := dw 0xa8a8a8a8a8a8a8a8
def w570 : Nat := dw 0xa2a2a2a2a2a2a2a2
def w571 : Nat := dw 0xff0cff0cff0cff0c
def w572 : Nat := dw 0xc000c000c000c
def w573 : Nat := dw 0xaa22aa22aa22aa22
def w574 : Nat := dw 0xf0fcf0fcf0fcf0fc
def w575 : Nat := dw 0x8888aaaa8888aaaa
def w576 : Nat := dw 0xf0f08080f0f08080
def w577 : Nat := dw 0xfffff8f8fffff8f8
def w578 : Nat := dw 0x707000007070
def w579 : Nat := dw 0xf0f08080f0f0808
def w580 : Nat := dw 0xffff888800000000
def w581 : Nat := dw 0xffffffffffff8888
def w582 : Nat := dw 0xffff8888
def w583 : Nat := dw 0x777700000000
def w584 : Nat := dw 0x7777707077777070
def w585 : Nat := dw 0x8888f8f88888f8f8
def w586 : Nat := dw 0xf8f8f8f888888888
def w587 : Nat := dw 0x7777777770707070
def w588 : Nat := dw 0x88888888f8f8f8f8
def w589 : Nat := dw 0x8f8f8f8f88888888
def w590 : Nat := dw 0x7777777777770000
def w591 : Nat := dw 0xeeee2222eeee2222
def w592 : Nat := dw 0xffffe0e0ffffe0e0
def w593 : Nat := dw 0xfefefefe00000000
def w594 : Nat := dw 0xfefefefe
def w595 : Nat := dw 0xffff0e0effff0e0e
def w596 : Nat := dw 0x1111101011111010
def w597 : Nat := dw 0xeeeefefeeeeefefe
def w598 : Nat := dw 0xfefefefeeeeeeeee
def w599 : Nat := dw 0x1111111110101010
def w600 : Nat := dw 0xeeeeeeeefefefefe
def w601 : Nat := dw 0xefefefefeeeeeeee
def w602 : Nat := dw 0x1111111111110000
def w603 : Nat := dw 0xddddd0d0ddddd0d0
def w604 : Nat := dw 0x2222f2f22222f2f2
def w605 : Nat := dw 0xf2f2f2f222222222
def w606 : Nat := dw 0xddddddddd0d0d0d0
def w607 : Nat := dw 0x22222222f2f2f2f2
def w608 : Nat := dw 0x2f2f2f2f22222222
def w609 : Nat := dw 0xdddddddddddd0000
def w610 : Nat := dw 0xbbbbb0b0bbbbb0b0
def w611 : Nat := dw 0x4444f4f44444f4f4
def w612 : Nat := dw 0xf4f4f4f444444444
def w613 : Nat := dw 0xbbbbbbbbb0b0b0b0
def w614 : Nat := dw 0x44444444f4f4f4f4
def w615 : Nat := dw 0x4f4f4f4f44444444
def w616 : Nat := dw 0xbbbbbbbbbbbb0000
def w617 : Nat := dw 0xffffececffffecec
def w618 : Nat := dw 0xecececec00000000
def w619 : Nat := dw 0xecececec
def w620 : Nat := dw 0x3333202033332020
def w621 : Nat := dw 0x5f5f4c4c5f5f4c4c
def w622 : Nat := dw 0xa0a0ececa0a0ecec
def w623 : Nat := dw 0xececececa0a0a0a0
def w624 : Nat := dw 0x5f5f5f5f4c4c4c4c
def w625 : Nat := dw 0xa0a0a0a0ecececec
def w626 : Nat := dw 0xb3b3b3b3a0a0a0a0
def w627 : Nat := dw 0x5f5f5f5f5f5f0000
def w628 : Nat := dw 0xffff3232ffff3232
def w629 : Nat := dw 0x323200003232
def w630 : Nat := dw 0xfafac8c8fafac8c8
def w631 : Nat := dw 0xfafa3232fafa3232
def w632 : Nat := dw 0x32323232fafafafa
def w633 : Nat := dw 0xfafafafac8c8c8c8
def w634 : Nat := dw 0xfafafafa32323232
def w635 : Nat := dw 0xc8c8c8c8fafafafa
def w636 : Nat := dw 0xccccfefeccccfefe
def w637 : Nat := dw 0xffffceceffffcece
def w638 : Nat := dw 0xcece0000cece
def w639 : Nat := dw 0x3333020233330202
def w640 : Nat := dw 0xf5f5c4c4f5f5c4c4
def w641 : Nat := dw 0xa0acece0a0acece
def w642 : Nat := dw 0xcececece0a0a0a0a
def w643 : Nat := dw 0xf5f5f5f5c4c4c4c4
def w644 : Nat := dw 0xa0a0a0acececece
def w645 : Nat := dw 0x3b3b3b3b0a0a0a0a
def w646 : Nat := dw 0xf5f5f5f5f5f50000
def w647 : Nat := dw 0xffffdcdcffffdcdc
def w648 : Nat := dw 0xdcdc0000dcdc
def w649 : Nat := dw 0x3333101033331010
def w650 : Nat := dw 0xafaf8c8cafaf8c8c
def w651 : Nat := dw 0x5050dcdc5050dcdc
def w652 : Nat := dw 0xdcdcdcdc50505050
def w653 : Nat := dw 0xafafafaf8c8c8c8c
def w654 : Nat := dw 0x50505050dcdcdcdc
def w655 : Nat := dw 0x7373737350505050
def w656 : Nat := dw 0xafafafafafaf0000
def w657 : Nat := dw 0xffffeaeaffffeaea
def w658 : Nat := dw 0x3f3f2a2a3f3f2a2a
def w659 : Nat := dw 0xfcfca8a8fcfca8a8
def w660 : Nat := dw 0x545400005454
def w661 : Nat := dw 0xffffaeaeffffaeae
def w662 : Nat := dw 0xf3f3a2a2f3f3a2a2
def w663 : Nat := dw 0xffffbabaffffbaba
def w664 : Nat := dw 0xcfcf8a8acfcf8a8a
def w665 : Nat := dw 0xffffeeeeffffaaaa
def w666 : Nat := dw 0xffffbbbbffffaaaa
def w667 : Nat := dw 0xcccc8888ffffaaaa
def w668 : Nat := dw 0xfcfcececfcfcecec
def w669 : Nat := dw 0xfffffafa00000000
def w670 : Nat := dw 0xcfcfcececfcfcece
def w671 : Nat := dw 0xfffffafaffffaaaa
def w672 : Nat := dw 0xffffafafffffaaaa
def w673 : Nat := dw 0xf0f0a0a0ffffaaaa
def w674 : Nat := dw 0xffffeeeecccccccc
def w675 : Nat := dw 0xc0c0e0e0c0c0e0e0
def w676 : Nat := dw 0xc0c0e0e0c0c0e0e
def w677 : Nat := dw 0xcccceeee00000000
def w678 : Nat := dw 0xc0c0eaeac0c0eaea
def w679 : Nat := dw 0xfcfc5454fcfc5454
def w680 : Nat := dw 0xc0caeae0c0caeae
def w681 : Nat := dw 0x3030baba3030baba
def w682 : Nat := dw 0xcccceeee0000aaaa
def w683 : Nat := dw 0x3333bbbb0000aaaa
def w684 : Nat := dw 0xf0f0fafa0000aaaa
def w685 : Nat := dw 0xf0fafaf0000aaaa
def w686 : Nat := dw 0xffffeeeeffffcccc
def w687 : Nat := dw 0x3333222233330000
def w688 : Nat := dw 0x54545454fcfcfcfc
def w689 : Nat := dw 0xaeaeaeae0c0c0c0c
def w690 : Nat := dw 0xbabababa30303030
def w691 : Nat := dw 0x55554444ffffcccc
def w692 : Nat := dw 0xaaaaeeee0000cccc
def w693 : Nat := dw 0x55555050fffff0f0
def w694 : Nat := dw 0xaaaafafa0000f0f0
def w695 : Nat := dw 0x3f3f3f3f2a2a2a2a
def w696 : Nat := dw 0xfcfcfcfca8a8a8a8
def w697 : Nat := dw 0xf3f3f3f3a2a2a2a2
def w698 : Nat := dw 0xcfcfcfcf8a8a8a8a
def w699 : Nat := dw 0xc0c0c0c0eaeaeaea
def w700 : Nat := dw 0xfcfcfcfc54545454
def w701 : Nat := dw 0xc0c0c0caeaeaeae
def w702 : Nat := dw 0x30303030babababa
def w703 : Nat := dw 0xffffddddffffcccc
def w704 : Nat := dw 0xdddd0000cccc
def w705 : Nat := dw 0x3333111133330000
def w706 : Nat := dw 0xd5d5d5d5c0c0c0c0
def w707 : Nat := dw 0xa8a8a8a8fcfcfcfc
def w708 : Nat := dw 0x5d5d5d5d0c0c0c0c
def w709 : Nat := dw 0x7575757530303030
def w710 : Nat := dw 0xaaaa8888ffffcccc
def w711 : Nat := dw 0x5555dddd0000cccc
def w712 : Nat := dw 0xaaaaa0a0fffff0f0
def w713 : Nat := dw 0x5555f5f50000f0f0
def w714 : Nat := dw 0xeaea0000eaea
def w715 : Nat := dw 0xeaeaeaea00000000
def w716 : Nat := dw 0xeaeaeaea
def w717 : Nat := dw 0x5555404055554040
def w718 : Nat := dw 0x3f3f3f3f3f3f0000
def w719 : Nat := dw 0xffff5454ffff5454
def w720 : Nat := dw 0xaaaafefeaaaafefe
def w721 : Nat := dw 0xaeae0000aeae
def w722 : Nat := dw 0x5555040455550404
def w723 : Nat := dw 0xf3f3f3f3f3f30000
def w724 : Nat := dw 0xbaba0000baba
def w725 : Nat := dw 0x5555101055551010
def w726 : Nat := dw 0xcfcfcfcfcfcf0000
def w727 : Nat := dw 0xfafaf8f8fafaf8f8
def w728 : Nat := dw 0x5050707050507070
def w729 : Nat := dw 0x5555777700000000
def w730 : Nat := dw 0xfffffcfcffffcccc
def w731 : Nat := dw 0xf0f0c0cffffcccc
def w732 : Nat := dw 0xffffcfcfffffcccc
def w733 : Nat := dw 0xf0f0c0c0ffffcccc
def w734 : Nat := dw 0xf0f0fcfc0000cccc
def w735 : Nat := dw 0xf0fcfcf0000cccc
def w736 : Nat := dw 0xeeee0000aaaa
def w737 : Nat := dw 0x5555444455550000
def w738 : Nat := dw 0x33333030fffff0f0
def w739 : Nat := dw 0xccccfcfc0000f0f0
def w740 : Nat := dw 0xbbbb0000aaaa
def w741 : Nat := dw 0x5555111155550000
def w742 : Nat := dw 0xf0f03030f0f00000
def w743 : Nat := dw 0xf0f03030f0f0000
def w744 : Nat := dw 0xccccc0c0fffff0f0
def w745 : Nat := dw 0x3333f3f30000f0f0
def w746 : Nat := dw 0xdddddcdcdddddcdc
def w747 : Nat := dw 0xbbbbbababbbbbaba
def w748 : Nat := dw 0x2222323222223232
def w749 : Nat := dw 0x4444545444445454
def w750 : Nat := dw 0xccccfcfc00000000
def w751 : Nat := dw 0x3232323222222222
def w752 : Nat := dw 0xfafa0000aaaa
def w753 : Nat := dw 0x5454545444444444
def w754 : Nat := dw 0x5555505055550000
def w755 : Nat := dw 0x3333303033330000
def w756 : Nat := dw 0xdddddddddcdcdcdc
def w757 : Nat := dw 0xbbbbbbbbbabababa
def w758 : Nat := dw 0x2222222232323232
def w759 : Nat := dw 0x4444444454545454
def w760 : Nat := dw 0x2323232322222222
def w761 : Nat := dw 0xafaf0000aaaa
def w762 : Nat := dw 0x4545454544444444
def w763 : Nat := dw 0xcfcf0000cccc
def w764 : Nat := dw 0x5555050555550000
def w765 : Nat := dw 0x3333030333330000
def w766 : Nat := dw 0xddddddddddddcccc
def w767 : Nat := dw 0xbbbbbbbbbbbbaaaa
def w768 : Nat := dw 0xffffffff88888888
def w769 : Nat := dw 0x555500000000
def w770 : Nat := dw 0xcccccccceeeeeeee
def w771 : Nat := dw 0xffffcccc00000000
def w772 : Nat := dw 0x333300000000
def w773 : Nat := dw 0xaaaaeeeeaaaaeeee
def w774 : Nat := dw 0xaaaaaaaaeeeeeeee
def w775 : Nat := dw 0x5555505055555050
def w776 : Nat := dw 0xaaaafafaaaaafafa
def w777 : Nat := dw 0x5555555550505050
def w778 : Nat := dw 0x3333333330303030
def w779 : Nat := dw 0xaaaaaaaafafafafa
def w780 : Nat := dw 0xccccccccfcfcfcfc
def w781 : Nat := dw 0xafafafafaaaaaaaa
def w782 : Nat := dw 0xf1f1f1f1e0e0e0e0
def w783 : Nat := dw 0x1f1f1f1f1f1f0000
def w784 : Nat := dw 0xfefefefe10101010
def w785 : Nat := dw 0xf1f1f1f1f1f10000
def w786 : Nat := dw 0xfefe0000eeee
def w787 : Nat := dw 0xeeeee0e0eeee0000
def w788 : Nat := dw 0xeeee0e0eeeee0000
def w789 : Nat := dw 0xfefefefefefef0f0
def w790 : Nat := dw 0x101010101010f0f0
def w791 : Nat := dw 0xfafa3232fafa0000
def w792 : Nat := dw 0xfefefefefefecccc
def w793 : Nat := dw 0x5454fcfcfcfc
def w794 : Nat := dw 0xffffbaba30303030
def w795 : Nat := dw 0x3333666633336666
def w796 : Nat := dw 0xf0f0e4e4f0f0e4e4
def w797 : Nat := dw 0xf0f5a5a0f0f5a5a
def w798 : Nat := dw 0xc0c0e0e0cccceeee
def w799 : Nat := dw 0xeeeee0e0ccccc0c0
def w800 : Nat := dw 0xeeee0e0ecccc0c0c
def w801 : Nat := dw 0xffffeaeaffffc0c0
def w802 : Nat := dw 0xeaeaeaeaeaea0000
def w803 : Nat := dw 0xfefefefefefeaaaa
def w804 : Nat := dw 0x20202020202aaaa
def w805 : Nat := dw 0x5555666655556666
def w806 : Nat := dw 0xf0f3c3c0f0f3c3c
def w807 : Nat := dw 0xfff0fffcff00ffcc
def w808 : Nat := dw 0xfcfcfcccfcccfccc
def w809 : Nat := dw 0x3333333033303330
def w810 : Nat := dw 0xffe1ffe1ff00ff00
def w811 : Nat := dw 0xffffe1e1ffff0000
def w812 : Nat := dw 0xf0f0f080f000f000
def w813 : Nat := dw 0xfffffff8fff0fff0
def w814 : Nat := dw 0x7000f000f0
def w815 : Nat := dw 0xf0f0f080f000f00
def w816 : Nat := dw 0x1e1e1e1e00000000
def w817 : Nat := dw 0xffffffff1e1e1e1e
def w818 : Nat := dw 0x1e1e1e1e
def w819 : Nat := dw 0xe1e1e1e100000000
def w820 : Nat := dw 0x10101010e0e0e0e0
def w821 : Nat := dw 0xf1f1f1f1fefefefe
def w822 : Nat := dw 0x10101010e0e0e0e
def w823 : Nat := dw 0xe0e0e0e010101010
def w824 : Nat := dw 0xfefe0000aaaa
def p4_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := []
theorem p4_Y : ∀ s ∈ p4_Z, SliceN p4_R p4_T s := by intro s h; cases h
noncomputable def p4_C : List (Nat × List (Nat × Nat × Nat)) := []
def p4_P : List (Nat × Nat) := [(4,6),(4,5),(1,3),(2,3),(2,6),(1,5)]
noncomputable def p4_K : List CutV := p4_C.map (mkCut p4_Z)
theorem p4_W : ∀ c ∈ p4_K, CutP p4_R p4_T c := cutsGood p4_Y (by decide +kernel)
theorem p4_Q : p4_P.all (sepOK p4_T) = true := by decide +kernel
def p4_D2 : List StD := []
theorem p4_I2 : LevelN p4_R p4_T 2 p4_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p4_D3 : List StD := [
([w1,w2,w0],dL 0x0,dS 0x60504030201,pH 0x111 0 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p4_C3x0 : levelOK p4_T p4_K p4_P 2 (p4_D2.map Prod.fst) ((p4_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p4_I3 : LevelN p4_R p4_T 3 p4_D3 := levelStep p4_B p4_W p4_Q p4_I2 (chunks 64 p4_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C3x0
  ))
theorem p4_L : LowN p4_R p4_T 4 := lowSearch p4_B p4_I3 (by decide +kernel)
def p3_T : Nat := 0xe880e880e880e880e880e880e880e880
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
theorem p3_S0 : SliceN p3_R p3_T (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]) := mkSlice (w:=2) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S1 : SliceN p3_R p3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S2 : SliceN p3_R p3_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S3 : SliceN p3_R p3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p3_B p4_B p4_L (by decide +kernel)
def p3_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨p3_S0,p3_S1,p3_S2,p3_S3,by simp⟩
noncomputable def p3_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x2010104,dC 0x4,dC 0x2010103,dC 0x2010101,dC 0x2010102,dC 0x3010101,dC 0x3010102,dC 0x3010103,dC 0x3010104,dC 0x3020102,dC 0x3020103,dC 0x3020104,dC 0x3020101]
def p3_P : List (Nat × Nat) := [(9,13),(6,7),(5,7),(3,7),(3,11),(2,11),(1,11),(12,13),(10,11),(6,14),(10,14),(5,13),(9,11),(12,14)]
noncomputable def p3_K : List CutV := p3_C.map (mkCut p3_Z)
theorem p3_W : ∀ c ∈ p3_K, CutP p3_R p3_T c := cutsGood p3_Y (by decide +kernel)
theorem p3_Q : p3_P.all (sepOK p3_T) = true := by decide +kernel
def p3_D2 : List StD := []
theorem p3_I2 : LevelN p3_R p3_T 2 p3_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
([w346,w1,w2,w0],dL 0x0,dS 0x90807030604010502,pH 0x111111 0 9),
([w347,w1,w2,w3],dL 0x0,dS 0xd030804010209,pH 0x111111 0 7),
([w28,w53,w12,w3],dL 0x8007,dS 0xc0305010a,pH 0x111111 2 5),
([w28,w101,w16,w0],dL 0xa009,dS 0xb08040a0102,pH 0x111121 2 6),
([w348,w1,w0,w3],dL 0x0,dS 0x90d0304010208,pH 0x111111 0 7),
([w53,w101,w2,w14],dL 0xd00c,dS 0xe0105030d02,pH 0x111211 2 6),
([w349,w2,w0,w3],dL 0x0,dS 0xd030904010208,pH 0x111111 0 7),
([w1,w12,w16,w14],dL 0x1000f,dS 0x10509030208,pH 0x121111 2 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK p3_T p3_K p3_P 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I3 : LevelN p3_R p3_T 3 p3_D3 := levelStep p3_B p3_W p3_Q p3_I2 (chunks 64 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([w350,w1,w2,w0,w3],dL 0x3,dS 0xc0b010403020a090805,pH 0x1111111111 1 10),
([w89,w1,w2,w0,w3],dL 0x0,dS 0xc0103020e0d0a080905,pH 0x1111111111 0 10),
([w351,w1,w2,w0,w3],dL 0x5,dS 0x40e03050d090b020801,pH 0x1111111111 1 10),
([w124,w1,w2,w0,w3],dL 0x0,dS 0xb0a0e0301080204,pH 0x1111111111 0 8),
([w28,w53,w2,w0,w3],dL 0x4007,dS 0x1030c050a0908,pH 0x2111111111 2 7),
([w28,w101,w2,w0,w3],dL 0x6009,dS 0x50308040102,pH 0x2111112111 2 6),
([w28,w1,w12,w0,w3],dL 0x4008,dS 0x40e0302050a0d,pH 0x2111111211 2 7),
([w28,w1,w16,w0,w3],dL 0x600a,dS 0x50e0d020b040103,pH 0x2111112111 2 8),
([w352,w1,w2,w0,w3],dL 0x0,dS 0xa0d020b010509080c,pH 0x1111111111 0 9),
([w353,w1,w2,w0,w3],dL 0x1,dS 0xb040d0c010802090e03,pH 0x1111111111 1 10),
([w354,w1,w2,w0,w3],dL 0x0,dS 0xe05010b040d090203,pH 0x1111111111 0 9),
([w53,w101,w2,w0,w3],dL 0xb00c,dS 0x5090108030d02,pH 0x1211112111 2 7),
([w53,w1,w12,w2,w3],dL 0x7008,dS 0x30b04020a0c0501,pH 0x2111111211 2 8),
([w53,w1,w2,w14,w3],dL 0xb00d,dS 0xa0b01020e04030d,pH 0x1211112111 2 8),
([w355,w1,w2,w0,w3],dL 0x0,dS 0xb05030a0c04020801,pH 0x1111111111 0 9),
([w356,w1,w2,w0,w3],dL 0x0,dS 0xe04080a050302090d,pH 0x1111111111 0 9),
([w101,w1,w16,w2,w0],dL 0x900a,dS 0xd080b01040c0a,pH 0x2111111111 2 7),
([w101,w1,w2,w14,w0],dL 0xc00d,dS 0x1060e0a050d03,pH 0x1211112111 2 7),
([w357,w1,w2,w0,w3],dL 0x0,dS 0xc040308010b050d0e0a,pH 0x1111111111 0 10),
([w1,w238,w2,w0,w3],dL 0x2,dS 0xd030a0b0e0904010802,pH 0x1111111111 1 10),
([w82,w1,w2,w0,w3],dL 0x0,dS 0x90501040d030802,pH 0x1111111111 0 8),
([w1,w12,w16,w0,w3],dL 0xe00f,dS 0x5040d03090208,pH 0x1112111111 2 7),
([w1,w12,w2,w14,w3],dL 0xe010,dS 0xa0403010208,pH 0x1111111111 2 6),
([w239,w1,w2,w0,w3],dL 0x0,dS 0x4050d020c0a01030e0b,pH 0x1111111111 0 10),
([w191,w1,w2,w0,w3],dL 0x0,dS 0x8010c05030d0209,pH 0x1111111111 0 8),
([w1,w16,w2,w14,w0],dL 0xf010,dS 0x10c0a0705080902,pH 0x1112111111 2 8),
([w240,w1,w2,w0,w3],dL 0x0,dS 0xd0102050a040b030e,pH 0x1111111111 0 9),
([w78,w1,w2,w0,w3],dL 0x0,dS 0x90a03050c04010208,pH 0x1111111111 0 9)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK p3_T p3_K p3_P 3 (p3_D3.map Prod.fst) ((p3_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I4 : LevelN p3_R p3_T 4 p3_D4 := levelStep p3_B p3_W p3_Q p3_I3 (chunks 64 p3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D5 : List StD := [
([w28,w1,w2,w0,w3],dL 0x4006002001,dS 0xc0b0504010a,pH 0x3112213421 4 6),
([w53,w1,w2,w0,w3],dL 0x700b002005,dS 0xa0e0c030d05,pH 0x1312143241 4 6),
([w101,w1,w2,w0,w3],dL 0x900200c003,dS 0xb0e010d0304,pH 0x1121243241 4 6),
([w1,w12,w2,w0,w3],dL 0xe005001008,dS 0xc09050a0208,pH 0x3224231111 4 6),
([w1,w16,w2,w0,w3],dL 0xf00300100a,dS 0x408010b0902,pH 0x3222431111 4 6),
([w1,w2,w14,w0,w3],dL 0x1000d003005,dS 0xd090e020308,pH 0x1122143331 4 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK p3_T p3_K p3_P 4 (p3_D4.map Prod.fst) ((p3_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I5 : LevelN p3_R p3_T 5 p3_D5 := levelStep p3_B p3_W p3_Q p3_I4 (chunks 64 p3_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D6 : List StD := [
([w1,w2,w0,w3],dL 0x3005001002,dS 0x405030c0d010a090b02080e,pH 0x322111 4 12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C6x0 : levelOK p3_T p3_K p3_P 5 (p3_D5.map Prod.fst) ((p3_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I6 : LevelN p3_R p3_T 6 p3_D6 := levelStep p3_B p3_W p3_Q p3_I5 (chunks 64 p3_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C6x0
  ))
theorem p3_L : LowN p3_R p3_T 7 := lowSearch p3_B p3_I6 (by decide +kernel)
def p2_T : Nat := 0xeee8e8e0eee8e8e0eee8e8e0eee8e8e0
def p2_R : List Nat := [0, 1, 2, 3, 4]
def p2_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,3,11),(4,3,19)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_S0 : SliceN p2_R p2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) p2_B p3_B p3_L (by decide +kernel)
def p2_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨p2_S0,by simp⟩
noncomputable def p2_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p2_P : List (Nat × Nat) := []
noncomputable def p2_K : List CutV := p2_C.map (mkCut p2_Z)
theorem p2_W : ∀ c ∈ p2_K, CutP p2_R p2_T c := cutsGood p2_Y (by decide +kernel)
theorem p2_Q : p2_P.all (sepOK p2_T) = true := by decide +kernel
def p2_D6 : List StD := []
theorem p2_I6 : LevelN p2_R p2_T 6 p2_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p2_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1,dS 0x0,pH 0x1111111111 1 0)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C7x0 : levelOK p2_T p2_K p2_P 6 (p2_D6.map Prod.fst) ((p2_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p2_I7 : LevelN p2_R p2_T 7 p2_D7 := levelStep p2_B p2_W p2_Q p2_I6 (chunks 64 p2_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C7x0
  ))
theorem p2_L : LowN p2_R p2_T 8 := lowSearch p2_B p2_I7 (by decide +kernel)
def p6_T : Nat := 0xfeecfeecfeecfeecfeecfeecfeecfeec
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,4,5),(1,0,2),(2,1,5),(3,1,9)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_S0 : SliceN p6_R p6_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) p6_B p4_B p4_L (by decide +kernel)
def p6_Z : List SliceD := [(0x33333333333333333333333333333333,4,[0, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_S0,by simp⟩
noncomputable def p6_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p6_P : List (Nat × Nat) := [(0,2),(4,5),(1,3)]
noncomputable def p6_K : List CutV := p6_C.map (mkCut p6_Z)
theorem p6_W : ∀ c ∈ p6_K, CutP p6_R p6_T c := cutsGood p6_Y (by decide +kernel)
theorem p6_Q : p6_P.all (sepOK p6_T) = true := by decide +kernel
def p6_D3 : List StD := []
theorem p6_I3 : LevelN p6_R p6_T 3 p6_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x30201,pH 0x111111 1 3)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK p6_T p6_K p6_P 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p6_I4 : LevelN p6_R p6_T 4 p6_D4 := levelStep p6_B p6_W p6_Q p6_I3 (chunks 64 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
theorem p6_L : LowN p6_R p6_T 5 := lowSearch p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfef8fef8fef8fef8fef8fef8fef8fef8
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,0,4),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
theorem p7_S0 : SliceN p7_R p7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel)
def p7_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨p7_S0,by simp⟩
noncomputable def p7_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p7_P : List (Nat × Nat) := [(8,10),(8,9),(1,3),(2,3),(0,4),(1,5)]
noncomputable def p7_K : List CutV := p7_C.map (mkCut p7_Z)
theorem p7_W : ∀ c ∈ p7_K, CutP p7_R p7_T c := cutsGood p7_Y (by decide +kernel)
theorem p7_Q : p7_P.all (sepOK p7_T) = true := by decide +kernel
def p7_D3 : List StD := []
theorem p7_I3 : LevelN p7_R p7_T 3 p7_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x60504030102,pH 0x111111 1 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p7_I4 : LevelN p7_R p7_T 4 p7_D4 := levelStep p7_B p7_W p7_Q p7_I3 (chunks 64 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
theorem p7_L : LowN p7_R p7_T 5 := lowSearch p7_B p7_I4 (by decide +kernel)
def p8_T : Nat := 0xe8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,4,5),(1,9,11),(2,1,5),(3,3,11)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_S0 : SliceN p8_R p8_T (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]) := mkSlice (w:=2) p8_B p4_B p4_L (by decide +kernel)
def p8_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨p8_S0,by simp⟩
noncomputable def p8_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p8_P : List (Nat × Nat) := [(12,14),(4,5),(9,11),(6,7),(10,14),(10,11),(1,5),(6,14),(3,11)]
noncomputable def p8_K : List CutV := p8_C.map (mkCut p8_Z)
theorem p8_W : ∀ c ∈ p8_K, CutP p8_R p8_T c := cutsGood p8_Y (by decide +kernel)
theorem p8_Q : p8_P.all (sepOK p8_T) = true := by decide +kernel
def p8_D3 : List StD := []
theorem p8_I3 : LevelN p8_R p8_T 3 p8_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x90804070605030102,pH 0x111111 1 9)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK p8_T p8_K p8_P 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p8_I4 : LevelN p8_R p8_T 4 p8_D4 := levelStep p8_B p8_W p8_Q p8_I3 (chunks 64 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := 0xe8c0e8c0e8c0e8c0e8c0e8c0e8c0e8c0
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,10,11),(1,4,6),(2,2,6),(3,3,11)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_S0 : SliceN p9_R p9_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) p9_B p4_B p4_L (by decide +kernel)
def p9_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨p9_S0,by simp⟩
noncomputable def p9_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p9_P : List (Nat × Nat) := [(4,6),(12,13),(5,7),(10,11),(2,6),(3,7)]
noncomputable def p9_K : List CutV := p9_C.map (mkCut p9_Z)
theorem p9_W : ∀ c ∈ p9_K, CutP p9_R p9_T c := cutsGood p9_Y (by decide +kernel)
theorem p9_Q : p9_P.all (sepOK p9_T) = true := by decide +kernel
def p9_D3 : List StD := []
theorem p9_I3 : LevelN p9_R p9_T 3 p9_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x60503010402,pH 0x111111 1 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK p9_T p9_K p9_P 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p9_I4 : LevelN p9_R p9_T 4 p9_D4 := levelStep p9_B p9_W p9_Q p9_I3 (chunks 64 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)
def p10_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p10_R : List Nat := [0, 1, 2, 3]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_S0 : SliceN p10_R p10_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p10_B p4_B p4_L (by decide +kernel)
def p10_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨p10_S0,by simp⟩
noncomputable def p10_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p10_P : List (Nat × Nat) := [(4,6),(4,5),(1,3),(2,3),(2,6),(1,5),(2,10),(1,9),(8,9),(8,10)]
noncomputable def p10_K : List CutV := p10_C.map (mkCut p10_Z)
theorem p10_W : ∀ c ∈ p10_K, CutP p10_R p10_T c := cutsGood p10_Y (by decide +kernel)
theorem p10_Q : p10_P.all (sepOK p10_T) = true := by decide +kernel
def p10_D3 : List StD := []
theorem p10_I3 : LevelN p10_R p10_T 3 p10_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p10_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0xa090806040307050201,pH 0x111111 1 10)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p10_I4 : LevelN p10_R p10_T 4 p10_D4 := levelStep p10_B p10_W p10_Q p10_I3 (chunks 64 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p5_T : Nat := 0xeee8eac0eee8eac0eee8eac0eee8eac0
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,3,19)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_S0 : SliceN p5_R p5_T (0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]) := mkSlice (w:=2) p5_B p6_B p6_L (by decide +kernel)
theorem p5_S1 : SliceN p5_R p5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) p5_B p7_B p7_L (by decide +kernel)
theorem p5_S2 : SliceN p5_R p5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p5_B p8_B p8_L (by decide +kernel)
theorem p5_S3 : SliceN p5_R p5_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,4,[0, 3, 4]) := mkSlice (w:=2) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S4 : SliceN p5_R p5_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p5_B p9_B p9_L (by decide +kernel)
theorem p5_S5 : SliceN p5_R p5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]) := mkSlice (w:=1) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S6 : SliceN p5_R p5_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p5_B p10_B p10_L (by decide +kernel)
theorem p5_S7 : SliceN p5_R p5_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S8 : SliceN p5_R p5_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p5_B p4_B p4_L (by decide +kernel)
def p5_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,4,[0, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_S0,p5_S1,p5_S2,p5_S3,p5_S4,p5_S5,p5_S6,p5_S7,p5_S8,by simp⟩
noncomputable def p5_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x2010103,dC 0x4,dC 0x2010105,dC 0x6,dC 0x3010104,dC 0x3010106,dC 0x2010107,dC 0x3,dC 0x3010305,dC 0x8,dC 0x5,dC 0x7,dC 0x4010101,dC 0x4010103,dC 0x4010105,dC 0x4010102,dC 0x3020303,dC 0x9,dC 0x4020103,dC 0x4020105,dC 0x3020202,dC 0x4030207]
def p5_P : List (Nat × Nat) := [(2,6),(3,7),(1,9),(3,11),(5,21),(18,19),(17,19),(4,6),(5,6),(4,7),(20,21),(0,9),(8,9),(17,21),(6,20),(5,9),(9,17),(3,19),(20,22),(17,25),(5,13),(4,13),(12,13),(18,26),(10,11),(10,26),(6,18),(12,14),(5,7),(18,22),(10,14)]
noncomputable def p5_K : List CutV := p5_C.map (mkCut p5_Z)
theorem p5_W : ∀ c ∈ p5_K, CutP p5_R p5_T c := cutsGood p5_Y (by decide +kernel)
theorem p5_Q : p5_P.all (sepOK p5_T) = true := by decide +kernel
def p5_D3 : List StD := []
theorem p5_I3 : LevelN p5_R p5_T 3 p5_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([w1,w2,w358,w3,w4],dL 0x0,dS 0x11100f040d0c020a09050e0b080301,pH 0x1111111111 0 15),
([w1,w2,w0,w359,w4],dL 0x0,dS 0x11100f03020a09050e0d0b040801,pH 0x1111111111 0 14)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I4 : LevelN p5_R p5_T 4 p5_D4 := levelStep p5_B p5_W p5_Q p5_I3 (chunks 64 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([w360,w1,w2,w0,w3,w4],dL 0x8007,dS 0x11100e0c120706050b080103,pH 0x211111111212111 2 12),
([w70,w1,w2,w0,w3,w4],dL 0x0,dS 0x10040905070614130e0301080b0d,pH 0x111111111111111 0 14),
([w241,w1,w2,w0,w3,w4],dL 0x0,dS 0x10120806041a0501030e190b,pH 0x111111111111111 0 12),
([w192,w1,w19,w2,w0,w3],dL 0xf012,dS 0x101b0708111206181a0e030105,pH 0x122111111111211 2 13),
([w242,w1,w2,w0,w3,w4],dL 0x0,dS 0x1012070b0e021d051a03081801,pH 0x111111111111111 0 13)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK p5_T p5_K p5_P 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I5 : LevelN p5_R p5_T 5 p5_D5 := levelStep p5_B p5_W p5_Q p5_I4 (chunks 64 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([w28,w1,w2,w0,w3,w4],dL 0x5003009006004002001,dS 0x1110080d0c1204020e0b050301,pH 0x433111222157621 7 13),
([w54,w1,w2,w0,w3,w4],dL 0xb00c00600200400a,dS 0x17160b120307051508,pH 0x411221331256321 6 9),
([w192,w1,w2,w0,w3,w4],dL 0x1101000f00c00e006,dS 0x100d1407180e080301,pH 0x223213213416542 6 9),
([w27,w1,w2,w0,w3,w4],dL 0x13014004006,dS 0x1a1012060d050e010b,pH 0x121212111132411 4 9),
([w1,w19,w2,w0,w3,w4],dL 0x1601501400e012004,dS 0x100e1e080d180306010b,pH 0x331311165322222 6 10),
([w1,w2,w0,w3,w42,w4],dL 0xc01801700600400a00d,dS 0x121a05150d1f06070b08,pH 0x712211331244551 7 10)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK p5_T p5_K p5_P 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I6 : LevelN p5_R p5_T 6 p5_D6 := levelStep p5_B p5_W p5_Q p5_I5 (chunks 64 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1400c00400600e00d00a001002,dS 0x1f151c0e05030d18061a010b08,pH 0x4332221111 9 13)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C7x0 : levelOK p5_T p5_K p5_P 6 (p5_D6.map Prod.fst) ((p5_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I7 : LevelN p5_R p5_T 7 p5_D7 := levelStep p5_B p5_W p5_Q p5_I6 (chunks 64 p5_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C7x0
  ))
theorem p5_L : LowN p5_R p5_T 8 := lowSearch p5_B p5_I7 (by decide +kernel)
def p12_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_S0 : SliceN p12_R p12_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S1 : SliceN p12_R p12_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S2 : SliceN p12_R p12_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S3 : SliceN p12_R p12_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
def p12_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨p12_S0,p12_S1,p12_S2,p12_S3,by simp⟩
noncomputable def p12_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x2010202,dC 0x2010201,dC 0x2010203,dC 0x3010202,dC 0x3010201,dC 0x2010204,dC 0x4,dC 0x3,dC 0x3010203,dC 0x3020201,dC 0x3010204,dC 0x3020203,dC 0x3020202,dC 0x3020204]
def p12_P : List (Nat × Nat) := [(4,5),(4,6),(1,3),(2,3),(1,9),(4,11),(2,10),(1,5),(4,12),(2,6),(3,8),(7,8),(8,9),(8,12),(8,10)]
noncomputable def p12_K : List CutV := p12_C.map (mkCut p12_Z)
theorem p12_W : ∀ c ∈ p12_K, CutP p12_R p12_T c := cutsGood p12_Y (by decide +kernel)
theorem p12_Q : p12_P.all (sepOK p12_T) = true := by decide +kernel
def p12_D2 : List StD := []
theorem p12_I2 : LevelN p12_R p12_T 2 p12_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
([w6,w24,w20,w3],dL 0x4003,dS 0x60107030405,pH 0x111121 2 6),
([w6,w0,w9,w8],dL 0x7006,dS 0x402010c0b0a08,pH 0x111211 2 7),
([w154,w1,w2,w0],dL 0x0,dS 0x2030904010507,pH 0x111111 0 7),
([w243,w1,w2,w3],dL 0x0,dS 0xf0d0e0803020401,pH 0x111111 0 8),
([w2,w24,w9,w42],dL 0xc00b,dS 0x5010c0d0302,pH 0x121111 2 6),
([w244,w1,w0,w3],dL 0x0,dS 0x9050d010f040302,pH 0x111111 0 8),
([w1,w20,w8,w42],dL 0xf00e,dS 0x70204010d,pH 0x121111 2 5),
([w245,w2,w0,w3],dL 0x0,dS 0x9050f020d030401,pH 0x111111 0 8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK p12_T p12_K p12_P 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I3 : LevelN p12_R p12_T 3 p12_D3 := levelStep p12_B p12_W p12_Q p12_I2 (chunks 64 p12_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([w2,w6,w0,w24,w3],dL 0x5003,dS 0xa08020104030907,pH 0x1211111111 2 8),
([w2,w6,w0,w3,w9],dL 0x6008,dS 0x70405020e0d080a03,pH 0x1112112111 2 9),
([w1,w6,w0,w20,w3],dL 0x5004,dS 0x80a010203040905,pH 0x1211111111 2 8),
([w1,w6,w0,w3,w8],dL 0x8007,dS 0x50f0307010e0a0804,pH 0x1121111111 2 9),
([w1,w2,w0,w134,w3],dL 0x9,dS 0x90e0f02030d07040105,pH 0x1111111111 1 10),
([w40,w1,w2,w0,w3],dL 0x0,dS 0x708030502040901,pH 0x1111111111 0 8),
([w1,w2,w0,w3,w102],dL 0xa,dS 0x90e020f03010a040d08,pH 0x1111111111 1 10),
([w25,w1,w2,w0,w3],dL 0x0,dS 0xa0503080f040e0d,pH 0x1111111111 0 8),
([w2,w0,w24,w3,w9],dL 0xd00b,dS 0x701050a080f0d0203,pH 0x1121111111 2 9),
([w1,w2,w24,w20,w3],dL 0x3004,dS 0x304020a08010705,pH 0x1112111111 2 8),
([w109,w1,w2,w0,w3],dL 0x0,dS 0x90208050a010704,pH 0x1111111111 0 8),
([w1,w2,w24,w3,w42],dL 0xd00c,dS 0x50809040f0e020103,pH 0x1121111111 2 9),
([w1,w2,w0,w3,w246],dL 0x2,dS 0x70a09050f040d020103,pH 0x1111111111 1 10),
([w247,w1,w2,w0,w3],dL 0x0,dS 0x305080e02010f0d,pH 0x1111111111 0 8),
([w1,w2,w0,w9,w8],dL 0x6007,dS 0x20705010b0d0a08,pH 0x1111111111 2 8),
([w36,w1,w2,w0,w3],dL 0x0,dS 0xe030507080d0a04,pH 0x1111111111 0 8),
([w1,w2,w0,w9,w42],dL 0xb00c,dS 0x80905010e0d0302,pH 0x1111111111 2 8),
([w248,w1,w2,w0,w3],dL 0x0,dS 0xf080509030d0201,pH 0x1111111111 0 8),
([w110,w1,w2,w0,w3],dL 0x0,dS 0x9010a0708020503,pH 0x1111111111 0 8),
([w1,w0,w20,w3,w8],dL 0x1000e,dS 0x50f0207080a0d0104,pH 0x1111111111 2 9),
([w1,w2,w20,w3,w42],dL 0x1000f,dS 0x50e0a0903020d0401,pH 0x1111111111 2 9),
([w1,w2,w0,w3,w249],dL 0x1,dS 0x508030f020d0a0e0401,pH 0x1111111111 1 10),
([w250,w1,w2,w0,w3],dL 0x0,dS 0x4070a0e020f010d,pH 0x1111111111 0 8),
([w65,w1,w2,w0,w3],dL 0x0,dS 0xe0407050a0f0803,pH 0x1111111111 0 8),
([w1,w2,w0,w8,w42],dL 0xe00f,dS 0x80907020e0f0401,pH 0x1111111111 2 8),
([w251,w1,w2,w0,w3],dL 0x0,dS 0xd0a07090f020401,pH 0x1111111111 0 8),
([w252,w1,w2,w0,w3],dL 0x0,dS 0xf0109050e080203,pH 0x1111111111 0 8),
([w125,w1,w2,w0,w3],dL 0x0,dS 0xd0209070e0a0104,pH 0x1111111111 0 8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK p12_T p12_K p12_P 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I4 : LevelN p12_R p12_T 4 p12_D4 := levelStep p12_B p12_W p12_Q p12_I3 (chunks 64 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([w1,w2,w6,w0,w3],dL 0x8005002001,dS 0x70a090e03040508,pH 0x1432211121 4 8),
([w1,w2,w0,w24,w3],dL 0xd00300a001,dS 0x903070f08010502,pH 0x4211321211 4 8),
([w1,w2,w0,w3,w9],dL 0xb006009001,dS 0xe0f050a0d080302,pH 0x1423212111 4 8),
([w1,w2,w0,w20,w3],dL 0x1000400a002,dS 0x907050d0a040201,pH 0x4211213321 4 8),
([w1,w2,w0,w3,w8],dL 0xe007009002,dS 0xe0d07080f0a0401,pH 0x1422113211 4 8),
([w1,w2,w0,w3,w42],dL 0xf00c00900a,dS 0xf0d090e03040201,pH 0x1214213211 4 8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK p12_T p12_K p12_P 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I5 : LevelN p12_R p12_T 5 p12_D5 := levelStep p12_B p12_W p12_Q p12_I4 (chunks 64 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D6 : List StD := [
([w1,w2,w0,w3],dL 0x900a002001,dS 0xe090f07020a0d0508040301,pH 0x322111 4 12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C6x0 : levelOK p12_T p12_K p12_P 5 (p12_D5.map Prod.fst) ((p12_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I6 : LevelN p12_R p12_T 6 p12_D6 := levelStep p12_B p12_W p12_Q p12_I5 (chunks 64 p12_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C6x0
  ))
theorem p12_L : LowN p12_R p12_T 7 := lowSearch p12_B p12_I6 (by decide +kernel)
def p11_T : Nat := 0xfffefef8fffefef8fffefef8fffefef8
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,0,4),(3,1,9),(4,1,17)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_S0 : SliceN p11_R p11_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p11_B p6_B p6_L (by decide +kernel)
theorem p11_S1 : SliceN p11_R p11_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) p11_B p12_B p12_L (by decide +kernel)
def p11_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨p11_S0,p11_S1,by simp⟩
noncomputable def p11_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2]
def p11_P : List (Nat × Nat) := [(8,9)]
noncomputable def p11_K : List CutV := p11_C.map (mkCut p11_Z)
theorem p11_W : ∀ c ∈ p11_K, CutP p11_R p11_T c := cutsGood p11_Y (by decide +kernel)
theorem p11_Q : p11_P.all (sepOK p11_T) = true := by decide +kernel
def p11_D6 : List StD := []
theorem p11_I6 : LevelN p11_R p11_T 6 p11_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p11_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1002,dS 0x1,pH 0x1111111112 2 1)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p11_C7x0 : levelOK p11_T p11_K p11_P 6 (p11_D6.map Prod.fst) ((p11_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p11_I7 : LevelN p11_R p11_T 7 p11_D7 := levelStep p11_B p11_W p11_Q p11_I6 (chunks 64 p11_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C7x0
  ))
theorem p11_L : LowN p11_R p11_T 8 := lowSearch p11_B p11_I7 (by decide +kernel)
def p14_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
theorem p14_S0 : SliceN p14_R p14_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p14_B p4_B p4_L (by decide +kernel)
def p14_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨p14_S0,by simp⟩
noncomputable def p14_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p14_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p14_K : List CutV := p14_C.map (mkCut p14_Z)
theorem p14_W : ∀ c ∈ p14_K, CutP p14_R p14_T c := cutsGood p14_Y (by decide +kernel)
theorem p14_Q : p14_P.all (sepOK p14_T) = true := by decide +kernel
def p14_D3 : List StD := []
theorem p14_I3 : LevelN p14_R p14_T 3 p14_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x201,pH 0x111111 1 2)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p14_I4 : LevelN p14_R p14_T 4 p14_D4 := levelStep p14_B p14_W p14_Q p14_I3 (chunks 64 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
theorem p14_L : LowN p14_R p14_T 5 := lowSearch p14_B p14_I4 (by decide +kernel)
def p15_T : Nat := 0xe888e888e888e888e888e888e888e888
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_S0 : SliceN p15_R p15_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p15_B p4_B p4_L (by decide +kernel)
def p15_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨p15_S0,by simp⟩
noncomputable def p15_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p15_P : List (Nat × Nat) := [(12,14),(12,13),(1,3),(2,3),(10,14),(9,13),(6,14),(5,13)]
noncomputable def p15_K : List CutV := p15_C.map (mkCut p15_Z)
theorem p15_W : ∀ c ∈ p15_K, CutP p15_R p15_T c := cutsGood p15_Y (by decide +kernel)
theorem p15_Q : p15_P.all (sepOK p15_T) = true := by decide +kernel
def p15_D3 : List StD := []
theorem p15_I3 : LevelN p15_R p15_T 3 p15_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x807060504030201,pH 0x111111 1 8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK p15_T p15_K p15_P 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p15_I4 : LevelN p15_R p15_T 4 p15_D4 := levelStep p15_B p15_W p15_Q p15_I3 (chunks 64 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
theorem p15_L : LowN p15_R p15_T 5 := lowSearch p15_B p15_I4 (by decide +kernel)
def p16_T : Nat := 0xea88ea88ea88ea88ea88ea88ea88ea88
def p16_R : List Nat := [0, 1, 2, 3]
def p16_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,10,14),(3,1,9)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
theorem p16_S0 : SliceN p16_R p16_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel)
def p16_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨p16_S0,by simp⟩
noncomputable def p16_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p16_P : List (Nat × Nat) := [(12,14),(8,9),(1,3),(2,3),(10,14)]
noncomputable def p16_K : List CutV := p16_C.map (mkCut p16_Z)
theorem p16_W : ∀ c ∈ p16_K, CutP p16_R p16_T c := cutsGood p16_Y (by decide +kernel)
theorem p16_Q : p16_P.all (sepOK p16_T) = true := by decide +kernel
def p16_D3 : List StD := []
theorem p16_I3 : LevelN p16_R p16_T 3 p16_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x504030102,pH 0x111111 1 5)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK p16_T p16_K p16_P 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p16_I4 : LevelN p16_R p16_T 4 p16_D4 := levelStep p16_B p16_W p16_Q p16_I3 (chunks 64 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
theorem p16_L : LowN p16_R p16_T 5 := lowSearch p16_B p16_I4 (by decide +kernel)
def p17_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def p17_R : List Nat := [0, 1, 2, 3]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
theorem p17_S0 : SliceN p17_R p17_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p17_B p4_B p4_L (by decide +kernel)
def p17_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨p17_S0,by simp⟩
noncomputable def p17_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p17_P : List (Nat × Nat) := [(12,14),(4,5),(1,3),(2,3),(10,14),(1,5),(6,14)]
noncomputable def p17_K : List CutV := p17_C.map (mkCut p17_Z)
theorem p17_W : ∀ c ∈ p17_K, CutP p17_R p17_T c := cutsGood p17_Y (by decide +kernel)
theorem p17_Q : p17_P.all (sepOK p17_T) = true := by decide +kernel
def p17_D3 : List StD := []
theorem p17_I3 : LevelN p17_R p17_T 3 p17_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p17_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x7060503010402,pH 0x111111 1 7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C4x0 : levelOK p17_T p17_K p17_P 3 (p17_D3.map Prod.fst) ((p17_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p17_I4 : LevelN p17_R p17_T 4 p17_D4 := levelStep p17_B p17_W p17_Q p17_I3 (chunks 64 p17_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C4x0
  ))
theorem p17_L : LowN p17_R p17_T 5 := lowSearch p17_B p17_I4 (by decide +kernel)
def p13_T : Nat := 0xfee8ea88fee8ea88fee8ea88fee8ea88
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,10,14),(3,1,9),(4,5,21)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_S0 : SliceN p13_R p13_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) p13_B p3_B p3_L (by decide +kernel)
theorem p13_S1 : SliceN p13_R p13_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S2 : SliceN p13_R p13_T (0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]) := mkSlice (w:=2) p13_B p14_B p14_L (by decide +kernel)
theorem p13_S3 : SliceN p13_R p13_T (0x30303030303030303030303030303030,4,[0, 3, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S4 : SliceN p13_R p13_T (0x33330000333300003333000033330000,4,[0, 2, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S5 : SliceN p13_R p13_T (0x50505050505050505050505050505050,4,[1, 3, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S6 : SliceN p13_R p13_T (0x55005500550055005500550055005500,4,[1, 2, 4]) := mkSlice (w:=8) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S7 : SliceN p13_R p13_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p13_B p15_B p15_L (by decide +kernel)
theorem p13_S8 : SliceN p13_R p13_T (0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]) := mkSlice (w:=16) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S9 : SliceN p13_R p13_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S10 : SliceN p13_R p13_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) p13_B p14_B p14_L (by decide +kernel)
theorem p13_S11 : SliceN p13_R p13_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[0, 1, 3, 4]) := mkSlice (w:=4) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S12 : SliceN p13_R p13_T (0x44444444444444444444444444444444,4,[2, 3, 4]) := mkSlice (w:=2) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S13 : SliceN p13_R p13_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S14 : SliceN p13_R p13_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S15 : SliceN p13_R p13_T (0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]) := mkSlice (w:=0) p13_B p16_B p16_L (by decide +kernel)
theorem p13_S16 : SliceN p13_R p13_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p13_B p17_B p17_L (by decide +kernel)
theorem p13_S17 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S18 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
def p13_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]),(0x30303030303030303030303030303030,4,[0, 3, 4]),(0x33330000333300003333000033330000,4,[0, 2, 3]),(0x50505050505050505050505050505050,4,[1, 3, 4]),(0x55005500550055005500550055005500,4,[1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[0, 1, 3, 4]),(0x44444444444444444444444444444444,4,[2, 3, 4]),(0x55550000555500005555000055550000,4,[1, 2, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xf0f00000f0f00000f0f00000f0f0,4,[0, 1, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨p13_S0,p13_S1,p13_S2,p13_S3,p13_S4,p13_S5,p13_S6,p13_S7,p13_S8,p13_S9,p13_S10,p13_S11,p13_S12,p13_S13,p13_S14,p13_S15,p13_S16,p13_S17,p13_S18,by simp⟩
noncomputable def p13_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x4,dC 0x5,dC 0x2010101,dC 0x6,dC 0x7,dC 0x3020403,dC 0x2010208,dC 0x5010303020401,dC 0x2010203020109,dC 0xa,dC 0x3010302,dC 0x302010b,dC 0x201020c,dC 0x3010101,dC 0x201020302010c,dC 0x2010204020109,dC 0x3010201,dC 0x3010203010101,dC 0x8,dC 0x3010204020101,dC 0x4020103,dC 0x3020107,dC 0x301010d,dC 0x302020201020c,dC 0x4020202010209,dC 0x3010301,dC 0x201020302030c,dC 0x2010204020309,dC 0x3010102010101,dC 0x4010103010101,dC 0x4010101,dC 0xe,dC 0x201020402010c,dC 0x4030303,dC 0x5010304030301,dC 0xf,dC 0x402010b,dC 0x2010209,dC 0x5030102010101,dC 0x5010303020101,dC 0x503030201020c,dC 0x5040102010101,dC 0x5010304020101,dC 0x5030102010209,dC 0x504030201020c,dC 0x4020403,dC 0x2010210,dC 0x503010201020c,dC 0x2010107,dC 0x201020a,dC 0x11,dC 0x3020103,dC 0x503040201020c,dC 0x504010201020c,dC 0x2010212,dC 0x2010213,dC 0x5030103010202010209,dC 0xb,dC 0x13,dC 0x2010401,dC 0x5030302010209,dC 0x2010211,dC 0x3020303,dC 0x5040103010101,dC 0x5010304030101,dC 0x5040102010209,dC 0x4030403,dC 0x3010107,dC 0x10,dC 0x201020f,dC 0x4030103,dC 0x503010301020201020c,dC 0x201020b,dC 0x5040104010202010209,dC 0x5020103010201,dC 0x503020201020c,dC 0xc,dC 0x403010b,dC 0x5040202010209,dC 0x5040103010201,dC 0x9,dC 0x2010304,dC 0x5020303010301,dC 0x5040402010209,dC 0x3010305,dC 0x5040303010301,dC 0x3020103010301,dC 0x4020103010301,dC 0x4030103010301,dC 0x3010401,dC 0x5040302010209,dC 0x4020303,dC 0x504010401020201020c,dC 0x12,dC 0x4010401,dC 0x3020101,dC 0x2010204,dC 0x5010103020101,dC 0x301020201020c,dC 0x5010202010204030109,dC 0x5010203020101,dC 0x2010205020304030109,dC 0x4030102010209,dC 0x501020201020403010c,dC 0x5040103020101,dC 0x403010201020c,dC 0x201020403040c,dC 0x4030110,dC 0x3020301,dC 0x2010204030309,dC 0x4020101,dC 0x402020401020201020c,dC 0x401020201020c,dC 0x3010204,dC 0x3010202010209,dC 0x5010204020101,dC 0x402020201020c,dC 0x201020402030c,dC 0x504020201020c,dC 0x5030202010209,dC 0x3010304,dC 0x504040201020c,dC 0x5030402010209,dC 0x201020403030c,dC 0x2010204030409,dC 0x4030111,dC 0x4030101,dC 0x3010205,dC 0x5010104030101,dC 0x4010202010209,dC 0x5010204030101,dC 0x201020502030403010c,dC 0x4030401,dC 0x5030102010409,dC 0x201040c,dC 0xd,dC 0x503010201040c,dC 0x5040102010409,dC 0x503020201040c,dC 0x5040202010409,dC 0x503040201040c,dC 0x5040402010409,dC 0x503030201040c,dC 0x5040302010409,dC 0x504010201040c,dC 0x2010409,dC 0x504030201040c,dC 0x302020201040c,dC 0x2010408,dC 0x4020202010409,dC 0x3020102,dC 0x2010411,dC 0x4030102010409,dC 0x3020104,dC 0x2010410,dC 0x2010413,dC 0x3020302,dC 0x201030d,dC 0x2010404030309,dC 0x4020102,dC 0x504020201040c,dC 0x402020201040c,dC 0x3020304,dC 0x403010201040c,dC 0x4030102,dC 0x201040a,dC 0x201040b,dC 0x4030402,dC 0x302040d,dC 0x201040403040c,dC 0x2010412,dC 0x2010201,dC 0x201030c,dC 0x5020203010409,dC 0x201030a,dC 0x2010207,dC 0x2010312,dC 0x2010301,dC 0x201010c,dC 0x5020303010409,dC 0x5040103010409,dC 0x3020201,dC 0x301030c,dC 0x301030402010c,dC 0x5040203010409,dC 0x201020d,dC 0x402040b,dC 0x3010312,dC 0x5040403010409,dC 0x3020401,dC 0x301010c,dC 0x5040303010409,dC 0x3020111,dC 0x3010404,dC 0x3020211,dC 0x3020311,dC 0x401040302030c,dC 0x3010404020309,dC 0x4020310,dC 0x3020411,dC 0x401040302040c,dC 0x3010404020409,dC 0x4020410,dC 0x301040a,dC 0x3010409,dC 0x4020401,dC 0x4020110,dC 0x3020113,dC 0x3010204020401,dC 0x4020210,dC 0x301040d,dC 0x3020213,dC 0x3020313,dC 0x401010302030c,dC 0x3020413,dC 0x401010302040c,dC 0x302010c,dC 0x2010402,dC 0x2010106,dC 0x3010408,dC 0x4020103010409,dC 0x302020302010c,dC 0x4020204020103010409,dC 0x3010204020103010101,dC 0x4020205030203010404020109,dC 0x4020103010101,dC 0x5030203010404020109,dC 0x504020302010c,dC 0x302020c,dC 0x2010206,dC 0x4020203010409,dC 0x501040302020c,dC 0x2010403,dC 0x301040b,dC 0x3010410,dC 0x2010306,dC 0x2010406,dC 0x302040c,dC 0x402010c,dC 0x4020111,dC 0x3010106,dC 0x4020104010101,dC 0x4020102010402,dC 0x4020411,dC 0x3010406,dC 0x402040c,dC 0x4030104020101,dC 0x4030103010408,dC 0x403010c,dC 0x4030411,dC 0x3020406,dC 0x403040c,dC 0x3010202,dC 0x3010211,dC 0x602010301020201020c,dC 0x4010205010203020109,dC 0x5030202010101,dC 0x5030302010101,dC 0x4010209,dC 0x2010103010401,dC 0x502040301020c,dC 0x301020501020402010c,dC 0x4010210,dC 0x301020402010c,dC 0x4010203020109,dC 0x3010213,dC 0x301020402040c,dC 0x502010301020c,dC 0x301020c,dC 0x3020110,dC 0x302040b,dC 0x3010203,dC 0x4010203020409,dC 0x301020302010c,dC 0x4010204020109,dC 0x302020301020c,dC 0x4020204010209,dC 0x301020302040c,dC 0x4010204020409,dC 0x3020103010101,dC 0x4030103010101,dC 0x5030304010101,dC 0x5020104010209,dC 0x6020104010202010209,dC 0x201010d,dC 0x302010d,dC 0x5020303010401,dC 0x5020404010209,dC 0x201030f,dC 0x5040303010401,dC 0x4010103010401,dC 0x5030302010301,dC 0x2010308,dC 0x4020103010401,dC 0x5030304010301,dC 0x5030104010101,dC 0x3010212,dC 0x5030204010101,dC 0x301020503030402010c,dC 0x302030b,dC 0x301020302030c,dC 0x4010204030109,dC 0x502030301020c,dC 0x5030304020101,dC 0x5030104010209,dC 0x504030301020c,dC 0x403040b,dC 0x6030104010203010209,dC 0x504010301020c,dC 0x403020301020401020c,dC 0x301020401020c,dC 0x301020a,dC 0x604010301020401020c,dC 0x4010203010209,dC 0x301020402030c,dC 0x4010203020309,dC 0x5030204020101,dC 0x403020301020c,dC 0x301020403030c,dC 0x504020301020c,dC 0x5040203010209,dC 0x504040301020c,dC 0x301030a,dC 0x5030404010209,dC 0x402030b,dC 0x301020403010c,dC 0x5020304010209,dC 0x502020301040c,dC 0x5020204010409,dC 0x502030301040c,dC 0x5020304010409,dC 0x301040c,dC 0x504010301040c,dC 0x4010409,dC 0x3020108,dC 0x3010402,dC 0x3020104010409,dC 0x302010a,dC 0x4010410,dC 0x3010405,dC 0x3010411,dC 0x3010403,dC 0x3020408,dC 0x2010407,dC 0x4010403020409,dC 0x3010413,dC 0x302020301040c,dC 0x4020204010409,dC 0x4020108,dC 0x402010301040c,dC 0x2010404,dC 0x4020408,dC 0x3010407,dC 0x301040402040c,dC 0x3010412,dC 0x4030108,dC 0x504020301040c,dC 0x302030a,dC 0x403020301040c,dC 0x4010201,dC 0x502020401040c,dC 0x2010309,dC 0x2010313,dC 0x3010207,dC 0x4010301,dC 0x502030401040c,dC 0x2010109,dC 0x401040c,dC 0x4020301,dC 0x3020112,dC 0x301030d,dC 0x3020212,dC 0x3010204020301,dC 0x3020312,dC 0x3010104020309,dC 0x3020412,dC 0x3010104020409,dC 0x4030201,dC 0x503020401040c,dC 0x302020d,dC 0x3010313,dC 0x4010309,dC 0x4030301,dC 0x503030401040c,dC 0x4010109,dC 0x3020109,dC 0x4010402,dC 0x201010e,dC 0x4020102010101,dC 0x4010411,dC 0x4020104010402,dC 0x4010403,dC 0x3020410,dC 0x201040e,dC 0x3020409,dC 0x4020109,dC 0x301010e,dC 0x302010401040c,dC 0x4010408,dC 0x4020204020109,dC 0x302020302010401040c,dC 0x302020504020401040302010c,dC 0x504020401040302010c,dC 0x5030204020109,dC 0x4020209,dC 0x302020401040c,dC 0x301020e,dC 0x5010404020209,dC 0x401040b,dC 0x301030e,dC 0x301040e,dC 0x4020409,dC 0x4030109,dC 0x4020103020101,dC 0x4030104010408,dC 0x4030310,dC 0x302030e,dC 0x4030309,dC 0x5010203020109,dC 0x5030402010101,dC 0x4030102010101,dC 0x2010104030401,dC 0x2010102010401,dC 0x5040103020109,dC 0x5040203020109,dC 0x5040403020109,dC 0x501020302040c,dC 0x5040303020109,dC 0x201040d,dC 0x3010102,dC 0x3010111,dC 0x4010110,dC 0x603020501020402010c,dC 0x6040205010203020109,dC 0x5040302010101,dC 0x3010202010101,dC 0x4020203020109,dC 0x3020104020409,dC 0x5010202010104020101,dC 0x3020203020109,dC 0x4030104020102,dC 0x3020104030108,dC 0x4030103020108,dC 0x501020403010c,dC 0x502020403010c,dC 0x302010f,dC 0x4030102010401,dC 0x5010203020409,dC 0x3020404,dC 0x5030102010401,dC 0x5040103020409,dC 0x5030202010401,dC 0x302030c,dC 0x5040203020409,dC 0x5030402010401,dC 0x5040403020409,dC 0x5030302010401,dC 0x501020302010c,dC 0x5040303020409,dC 0x5040102010401,dC 0x5040302010401,dC 0x302040f,dC 0x2010404030401,dC 0x5010204020109,dC 0x302020501020302010c,dC 0x4020205010204020109,dC 0x2010205,dC 0x3010103010301,dC 0x4020309,dC 0x5020303010101,dC 0x5030304020109,dC 0x3010103010401,dC 0x504010302010c,dC 0x5040303010101,dC 0x504030302010c,dC 0x6050403010203010101,dC 0x6050303010103010201,dC 0x605040302020302010c,dC 0x6050404020204020109,dC 0x6030104020204020109,dC 0x7030104020205030204020109,dC 0x4020205030204020109,dC 0x302020504020302010c,dC 0x704010302020504020302010c,dC 0x604010302020302010c,dC 0x3010203010301,dC 0x3010203010401,dC 0x3010204010101,dC 0x302020402010c,dC 0x4020204030109,dC 0x302020403030c,dC 0x504040302020c,dC 0x5030104020209,dC 0x504030302020c,dC 0x504010302020c,dC 0x2010203,dC 0x301020b,dC 0x403020302020402020c,dC 0x302020402020c,dC 0x3020204,dC 0x403020302020c,dC 0x504020302020c,dC 0x302020403010c,dC 0x4010203,dC 0x401020b,dC 0x5040303010201,dC 0x501020302030c,dC 0x5010204020309,dC 0x5030304020309,dC 0x5040103010301,dC 0x504010302030c,dC 0x504030302030c,dC 0x302040302030c,dC 0x4020404020309,dC 0x4030104020309,dC 0x504020302030c,dC 0x5030204020309,dC 0x302020a,dC 0x401020302030c,dC 0x3010204020309,dC 0x402020302030c,dC 0x403010302030c,dC 0x5010204020409,dC 0x5030304020409,dC 0x5040103010401,dC 0x504010302040c,dC 0x504030302040c,dC 0x402010302040c,dC 0x504020302040c,dC 0x5030204020409,dC 0x401020302040c,dC 0x3010204020409,dC 0x403020302040c,dC 0x501020402010c,dC 0x5030404010101,dC 0x3020104010101,dC 0x4010103020301,dC 0x5020304010101,dC 0x201040f,dC 0x503020402010c,dC 0x503030402010c,dC 0x302030d,dC 0x4010104010401,dC 0x5010204030109,dC 0x5020204030109,dC 0x3020104020102,dC 0x4030104020108,dC 0x4020103020102,dC 0x5010204010104020101,dC 0x402020402010c,dC 0x501020402040c,dC 0x3020104010401,dC 0x3020105,dC 0x3020305,dC 0x5020304010401,dC 0x5030204010401,dC 0x503020402040c,dC 0x5030304010401,dC 0x503030402040c,dC 0x302040a,dC 0x4010403020301,dC 0x5010403020101,dC 0x2010311,dC 0x502020301020c,dC 0x3020104020101,dC 0x5020304030109,dC 0x2010307,dC 0x3020103020301,dC 0x602010501020403010c,dC 0x2010111,dC 0x2010108,dC 0x2010110,dC 0x602020501020403010c,dC 0x6020205010204030109,dC 0x5040303020101,dC 0x5030203020104020101,dC 0x4030204030109,dC 0x5010204030309,dC 0x5010203020301,dC 0x5020204030309,dC 0x5010303020301,dC 0x5020304030309,dC 0x5040103020301,dC 0x5040303020301,dC 0x402020401020c,dC 0x401020c,dC 0x5010404020101,dC 0x2010310,dC 0x502040401020c,dC 0x3010209,dC 0x403020401020c,dC 0x5030404020101,dC 0x3010311,dC 0x4010310,dC 0x503040401020c,dC 0x5010104020101,dC 0x401020402040c,dC 0x5020203010209,dC 0x502020401020c,dC 0x5030104020101,dC 0x401020403040c,dC 0x503020401020c,dC 0x402020c,dC 0x501040402020c,dC 0x3020209,dC 0x403020402020c,dC 0x503040402020c,dC 0x501020402030c,dC 0x5010203020309,dC 0x402030c,dC 0x503020402030c,dC 0x3020309,dC 0x403020c,dC 0x501040403020c,dC 0x4030209,dC 0x502040403020c,dC 0x5030204030104020101,dC 0x403020403010c,dC 0x501020403030c,dC 0x5010204030409,dC 0x502020403030c,dC 0x4030409,dC 0x403030c,dC 0x5010404030101,dC 0x5020204010209,dC 0x502030403010c,dC 0x3010307,dC 0x5020304030101,dC 0x4030104030401,dC 0x501020403040c,dC 0x5010204030401,dC 0x502020403040c,dC 0x5010304030401,dC 0x502030403040c,dC 0x5020304030401]
def p13_P : List (Nat × Nat) := [(8,9),(6,7),(2,3),(10,11),(18,19),(5,7),(1,3),(12,13),(20,21),(17,21),(10,14),(5,21),(10,26),(6,14),(20,22),(24,28),(1,9),(4,14),(12,14),(16,26),(12,28),(6,22),(20,28),(3,5),(24,26),(18,26),(1,19),(18,22),(17,19),(5,13),(17,25),(3,17),(9,10),(17,28),(18,28),(5,9),(9,12),(10,28),(5,28),(6,28),(9,17),(24,25),(1,21),(9,24),(11,12),(7,12),(19,20),(7,20),(13,24),(19,24),(11,24),(0,3),(1,25),(8,14),(2,14),(20,29),(18,23),(3,10),(6,13),(6,11),(3,6),(17,22),(5,22),(3,18),(18,25),(11,18),(5,15),(20,25),(13,20),(4,22),(2,26),(4,21),(6,23),(5,14),(20,30),(20,26),(14,20),(0,9)]
noncomputable def p13_K : List CutV := p13_C.map (mkCut p13_Z)
theorem p13_W : ∀ c ∈ p13_K, CutP p13_R p13_T c := cutsGood p13_Y (by decide +kernel)
theorem p13_Q : p13_P.all (sepOK p13_T) = true := by decide +kernel
def p13_D2 : List StD := []
theorem p13_I2 : LevelN p13_R p13_T 2 p13_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p13_D3 : List StD := [
([w1,w0,w503,w4],dL 0x0,dS 0xf0a0b06070904,pH 0x111111 0 7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x0 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I3 : LevelN p13_R p13_T 3 p13_D3 := levelStep p13_B p13_W p13_Q p13_I2 (chunks 64 p13_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D4 : List StD := [
([w6,w0,w174,w3,w4],dL 0x0,dS 0xd0c05040313010b0a090219,pH 0x1111111111 0 12),
([w2,w32,w30,w11,w3],dL 0x0,dS 0x1a050a0b1d06110e020107,pH 0x1111111111 0 11),
([w1,w0,w492,w3,w4],dL 0x0,dS 0xd0c0f1306050b0a070201,pH 0x1111111111 0 11),
([w1,w2,w493,w0,w4],dL 0x0,dS 0xa0b17140605070e110201,pH 0x1111111111 0 11),
([w263,w1,w2,w3,w49],dL 0x0,dS 0xe110713022b1016060b0a0109,pH 0x1111111111 0 13),
([w25,w2,w0,w94,w4],dL 0x0,dS 0x50a0b14061a0201070e11,pH 0x1111111111 0 11),
([w93,w2,w34,w3,w4],dL 0x0,dS 0xf0602111a091c08,pH 0x1111111111 0 8),
([w6,w0,w11,w212,w4],dL 0x0,dS 0x2130d0c0e0b0a040919,pH 0x1111111111 0 10),
([w203,w1,w2,w7,w49],dL 0x0,dS 0x2b070f0917060e110201,pH 0x1111111111 0 10),
([w93,w2,w0,w3,w35],dL 0x0,dS 0x302062a0a0916110e070b0c,pH 0x1111111111 0 12),
([w1,w264,w0,w8,w4],dL 0x0,dS 0xd0c0502040b0a060f01,pH 0x1111111111 0 10),
([w18,w1,w85,w8,w4],dL 0xe4,dS 0x10b020f060a0e,pH 0x1111111111 1 7),
([w96,w2,w21,w3,w4],dL 0x0,dS 0x1711041019060201090a,pH 0x1111111111 0 10),
([w36,w95,w0,w3,w4],dL 0x0,dS 0xd0c051913060b0a070102,pH 0x1111111111 0 11),
([w2,w0,w174,w9,w4],dL 0x0,dS 0x1f021a080d0c040e0b0a0901,pH 0x1111111111 0 12),
([w96,w2,w33,w0,w3],dL 0x0,dS 0x171113060415070501090c,pH 0x1111111111 0 11),
([w2,w67,w11,w3,w55],dL 0x0,dS 0xd0c2a081913060b0a030107,pH 0x1111111111 0 12),
([w0,w11,w213,w9,w4],dL 0x0,dS 0xe010d0c13090b041a0a,pH 0x1111111111 0 10),
([w204,w1,w7,w3,w49],dL 0x0,dS 0xe112b100a0907130f060102,pH 0x1111111111 0 12),
([w39,w1,w0,w85,w8],dL 0x195,dS 0x719041505010d0b0f06,pH 0x1111111111 1 10),
([w494,w1,w2,w0,w4],dL 0x0,dS 0xc0d190738020a061703010e101211,pH 0x1111111111 0 15),
([w1,w2,w169,w0,w268],dL 0x0,dS 0xd1f0503010e0c02061119,pH 0x1111111111 0 11),
([w2,w21,w7,w3,w35],dL 0x35083,dS 0xd02100b0a061619,pH 0x1121211111 2 8),
([w1,w2,w7,w3,w271],dL 0x83,dS 0x1516012a1002060b0a19,pH 0x1111111111 1 10),
([w273,w1,w2,w7,w3],dL 0x0,dS 0x16020e1110190a06,pH 0x1111111111 0 8),
([w57,w0,w11,w8,w4],dL 0x0,dS 0x4a0e0d0c060b0a040919,pH 0x1111111111 0 10),
([w1,w0,w278,w8,w4],dL 0x0,dS 0xf0a0b06010e07190904,pH 0x1111111111 0 10),
([w279,w1,w0,w8,w4],dL 0x0,dS 0x100b07470c360a060f0409,pH 0x1111111111 0 11),
([w1,w0,w495,w8,w4],dL 0x0,dS 0x12150d04020f1009140b01,pH 0x1111111111 0 11),
([w496,w1,w0,w8,w4],dL 0x0,dS 0xd0c0206010b09190e0a04,pH 0x1111111111 0 11),
([w16,w0,w284,w8,w4],dL 0x0,dS 0x1204090d0c010b0a,pH 0x1111111111 0 8),
([w1,w0,w497,w8,w4],dL 0x0,dS 0xf04020d0c090b0a01,pH 0x1111111111 0 9),
([w1,w72,w85,w8,w4],dL 0x1e4,dS 0x70b0604020a090e01,pH 0x1111111111 1 9),
([w1,w16,w0,w174,w4],dL 0x0,dS 0xf07014a0c0d0a0e060b09,pH 0x1111111111 0 11),
([w283,w1,w0,w8,w4],dL 0x0,dS 0x40d0c0f060b0a,pH 0x1111111111 0 7),
([w1,w0,w85,w103,w8],dL 0x1e7,dS 0xf070d0b090504020c1901,pH 0x1111111111 1 11),
([w285,w2,w7,w3,w49],dL 0x0,dS 0xe112b100a07130f09060201,pH 0x1111111111 0 12),
([w498,w1,w2,w0,w4],dL 0x0,dS 0xa0b14070c380617020115050e1311,pH 0x1111111111 0 15),
([w1,w2,w171,w288,w4],dL 0x0,dS 0xb1e1d07050201061a0a031113,pH 0x1111111111 0 13),
([w2,w33,w7,w34,w3],dL 0x49064,dS 0x5151a0a060d1c08,pH 0x1212111111 2 8),
([w1,w2,w7,w290,w3],dL 0x64,dS 0x101a1c0115050b080a,pH 0x1111111111 1 9),
([w291,w1,w2,w7,w3],dL 0x0,dS 0x1c051a1115130a06,pH 0x1111111111 0 8),
([w499,w1,w0,w3,w4],dL 0x0,dS 0x80a0f13060102111c0d0c1207,pH 0x1111111111 0 13),
([w1,w165,w0,w211,w3],dL 0x0,dS 0x1e131d07110908020d1a0c0601,pH 0x1111111111 0 13),
([w1,w0,w178,w212,w4],dL 0x0,dS 0xf0a0b06011307190904,pH 0x1111111111 0 10),
([w500,w1,w0,w3,w4],dL 0x0,dS 0xd0c0f1306010221090a0b07,pH 0x1111111111 0 12),
([w1,w166,w0,w297,w4],dL 0x0,dS 0x140f07020e210a0b0609,pH 0x1111111111 0 10),
([w1,w0,w213,w179,w4],dL 0x0,dS 0xf0a0b06020e1a070904,pH 0x1111111111 0 10),
([w1,w299,w0,w173,w4],dL 0x0,dS 0xa0b0f060117073a1109,pH 0x1111111111 0 10),
([w501,w1,w2,w0,w4],dL 0x0,dS 0xa0b0f06170201070e3a0911,pH 0x1111111111 0 12),
([w502,w1,w0,w3,w4],dL 0x0,dS 0x140c16110f130601020e0a0b07,pH 0x1111111111 0 13),
([w1,w168,w307,w3,w4],dL 0x0,dS 0x1f0b072a080219110e0a0601,pH 0x1111111111 0 12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x0 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I4 : LevelN p13_R p13_T 4 p13_D4 := levelStep p13_B p13_W p13_Q p13_I3 (chunks 64 p13_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D5p0 : List StD := [
([w25,w82,w1,w2,w0,w4],dL 0x0,dS 0x7141306110a1012020c0d01,pH 0x111111111111111 0 12),
([w6,w0,w11,w3,w8,w4],dL 0x0,dS 0x11050402130d0c060b0a030919,pH 0x111111111111111 0 13),
([w93,w1,w0,w3,w8,w4],dL 0x16,dS 0x11070403190a0e1a060b0f13021009,pH 0x111111111111111 1 15),
([w44,w1,w6,w0,w8,w4],dL 0xa,dS 0xa0705010d1119060b04170213,pH 0x111111111111111 1 13),
([w104,w1,w6,w0,w3,w4],dL 0x1a,dS 0x17190c02040111070b0a0e13060f,pH 0x111111111111111 1 14),
([w1,w6,w0,w138,w3,w4],dL 0x0,dS 0x1d1c0b0613050201041711070f1903,pH 0x111111111111111 0 15),
([w27,w6,w0,w11,w3,w4],dL 0x0,dS 0xd0c05131d0e060f0b0a0902071904,pH 0x111111111111111 0 15),
([w27,w93,w1,w0,w3,w4],dL 0x0,dS 0x30d150c0a0e070b0210061117090f,pH 0x111111111111111 0 15),
([w25,w91,w1,w2,w0,w4],dL 0x0,dS 0x140e060c15130a0b0201,pH 0x111111111111111 0 10),
([w391,w1,w2,w6,w0,w3],dL 0x0,dS 0x1710110f0401210e0a0c1d050b150602,pH 0x111111111111111 0 16),
([w25,w262,w1,w2,w0,w4],dL 0x0,dS 0x6110a19100c0d120201,pH 0x111111111111111 0 10),
([w392,w1,w2,w6,w0,w4],dL 0x0,dS 0xb0c150a1d070f050121101711040e0602,pH 0x111111111111111 0 17),
([w1,w2,w32,w56,w14,w4],dL 0x37,dS 0x150c241d230705220403210d0a111a100602,pH 0x111111111111111 1 18),
([w25,w1,w2,w32,w14,w4],dL 0x37,dS 0x150d061c05250e240a1a0c11021001,pH 0x111111111111111 1 15),
([w1,w2,w32,w30,w7,w3],dL 0x18039,dS 0x171a0b261d06050d11020e071001,pH 0x111121111111111 2 14),
([w2,w32,w6,w34,w3,w4],dL 0x0,dS 0x15220c1e081d1906250d111a070210,pH 0x111111111111111 0 15),
([w2,w32,w6,w11,w3,w4],dL 0x3c,dS 0xc170a0b091d1906110e100702,pH 0x111111111111111 1 13),
([w393,w1,w2,w6,w3,w4],dL 0x0,dS 0xc151d110f050401210b0602170a0e100703,pH 0x111111111111111 0 18),
([w1,w2,w56,w30,w0,w23],dL 0x4a,dS 0x100a29282705210b0c1d11040e150602,pH 0x111111111111111 1 16),
([w2,w56,w6,w0,w34,w4],dL 0x4b,dS 0xd030c150a221e081d070f0217111a06,pH 0x111111111111111 1 16),
([w2,w56,w6,w0,w35,w4],dL 0x4d,dS 0xb030c270a101f2a1d070f0217110e06,pH 0x111111111111111 1 16),
([w2,w0,w11,w3,w102,w4],dL 0x48036,dS 0xd0c1705190f13060b090a020107,pH 0x211111111111111 2 14),
([w43,w1,w0,w3,w102,w4],dL 0x48036,dS 0xd0c1705091913060f0b0a070201,pH 0x211111111111111 2 14),
([w44,w1,w2,w0,w102,w4],dL 0x48036,dS 0xf091317060d0c0b010a02,pH 0x211111111111111 2 11),
([w263,w1,w2,w0,w3,w4],dL 0x18,dS 0xb0d11070c0a0e06170f0109,pH 0x111111111111111 1 12),
([w25,w202,w1,w2,w0,w4],dL 0x0,dS 0x140e060c15130a0b0201,pH 0x111111111111111 0 10),
([w25,w1,w2,w30,w0,w23],dL 0x4a,dS 0x100a0607162c051a290b0e1102150c01,pH 0x111111111111111 1 16),
([w25,w2,w6,w0,w34,w4],dL 0xa,dS 0xd03150a251d06131e0c0802071a1711,pH 0x111111111111111 1 16),
([w25,w2,w6,w0,w35,w4],dL 0xa,dS 0xb030c2a2c0a1d06121f1002070e1711,pH 0x111111111111111 1 16),
([w25,w1,w2,w161,w0,w4],dL 0x3,dS 0xa0b15101406051a07170e110201,pH 0x111111111111111 1 14),
([w25,w84,w1,w2,w0,w4],dL 0x0,dS 0xc110a0b1406051a010e,pH 0x111111111111111 0 10),
([w25,w1,w2,w14,w7,w4],dL 0x51,dS 0xc0b17141305080e061c1a02110a01,pH 0x111111111111111 1 15),
([w1,w2,w0,w394,w3,w4],dL 0x51,dS 0x170e0f06050c130a0b070201,pH 0x111111111111111 1 12),
([w25,w2,w0,w11,w3,w4],dL 0x0,dS 0x130e0f02060c0d01090a0b,pH 0x111111111111111 0 11),
([w25,w43,w1,w0,w3,w4],dL 0x0,dS 0xe01130c0d0a0b02060f,pH 0x111111111111111 0 10),
([w25,w1,w2,w7,w0,w23],dL 0x51,dS 0xd170a19062a1a07160e11020c01,pH 0x111111111111111 1 14),
([w25,w163,w1,w2,w0,w4],dL 0x0,dS 0xa1a0607020c0d010e11,pH 0x111111111111111 0 10),
([w2,w30,w6,w0,w11,w3],dL 0x60,dS 0x171a0509130a111d0b0e021506,pH 0x111111111111111 1 13),
([w2,w30,w6,w0,w3,w35],dL 0x0,dS 0x2c2710051f2a130a021d0b1511060e,pH 0x111111111111111 0 15),
([w6,w0,w34,w46,w3,w4],dL 0x41,dS 0x50421242e2d1a06150a020c1108,pH 0x111111111111111 1 14),
([w78,w6,w0,w34,w3,w4],dL 0xa041,dS 0x51e0a251d21060f15111a0c020807,pH 0x212111121111111 2 15),
([w165,w6,w0,w34,w3,w4],dL 0x65,dS 0x110f1d0206130c0d1e0a080719,pH 0x111111111111111 1 13),
([w139,w6,w0,w34,w3,w4],dL 0x0,dS 0x1e02191d21060c0d031a0711080f,pH 0x111111111111111 0 14),
([w2,w6,w7,w34,w3,w4],dL 0x8041049,dS 0xc1d210f020a111a1c0806,pH 0x111122112111111 3 11),
([w140,w1,w2,w7,w3,w4],dL 0x3b,dS 0xc1c0d0e1106100b13020a08,pH 0x111111111111111 1 12),
([w2,w6,w0,w94,w3,w4],dL 0x6703200a06b041,dS 0xc010a1d0221060f110e07,pH 0x343111431111111 5 11),
([w395,w1,w2,w0,w3,w4],dL 0x41,dS 0xd1121100a0f0106020c0e1517,pH 0x111111111111111 1 13),
([w93,w1,w2,w14,w3,w4],dL 0x3d,dS 0xe0f06040c1c1a0d1002110b0a09,pH 0x111111111111111 1 14),
([w6,w0,w11,w60,w3,w4],dL 0x73041,dS 0xc1121302f020d0b06170e09,pH 0x121211111111111 2 12),
([w43,w6,w0,w11,w3,w4],dL 0x32041,dS 0x51d2106130c171102090e07,pH 0x221111211111111 2 12),
([w166,w6,w0,w11,w3,w4],dL 0x0,dS 0x11131d02060f0c0d0a0b090e0719,pH 0x111111111111111 0 14),
([w141,w6,w0,w11,w3,w4],dL 0x0,dS 0x17050a0b02131d21070f03190e110609,pH 0x111111111111111 0 16),
([w203,w1,w2,w7,w0,w4],dL 0x0,dS 0xb0d0c0a070f09170e06021101,pH 0x111111111111111 0 13),
([w93,w1,w2,w0,w23,w3],dL 0x3d,dS 0x170604030a161107020e150d0b0c09,pH 0x111111111111111 1 15),
([w1,w2,w396,w0,w3,w4],dL 0xa,dS 0xc170e1907050d0a060b130201,pH 0x111111111111111 1 13),
([w2,w6,w7,w0,w3,w35],dL 0x8035,dS 0x30a310221070c0f0b110e162a06,pH 0x111211111111111 2 14),
([w167,w1,w2,w7,w0,w3],dL 0x35,dS 0xe110a1604030106020b150c190d,pH 0x111111111111111 1 14),
([w6,w0,w3,w35,w127,w4],dL 0xa,dS 0x160506212911040b0233320a030c0e1910,pH 0x111111111111111 1 17),
([w92,w6,w0,w3,w35,w4],dL 0xa,dS 0x51f0b032c0a1d21060f0c111910020e07,pH 0x111111111111111 1 17),
([w168,w6,w0,w3,w35,w4],dL 0x84,dS 0xc1f2a020619110b130a0f0710,pH 0x111111111111111 1 13),
([w142,w6,w0,w3,w35,w4],dL 0x0,dS 0x51f0a0b02131d2106030e07112a0f,pH 0x111111111111111 0 15),
([w44,w1,w2,w0,w126,w4],dL 0x0,dS 0x110d0c130b0a060109,pH 0x111111111111111 0 9),
([w397,w1,w2,w0,w3,w4],dL 0x0,dS 0x20d0c0e17130b0a060109,pH 0x111111111111111 0 11),
([w44,w10,w1,w0,w8,w4],dL 0x98,dS 0xf0211090c130d0a010b,pH 0x111111111111111 1 10)]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p1 : List StD := [
([w104,w10,w1,w0,w3,w4],dL 0x0,dS 0x17021d11070e0b0a0f01091306,pH 0x111111111111111 0 13),
([w10,w2,w0,w94,w3,w4],dL 0x9b,dS 0x3406020f010b0a0d0e110c,pH 0x111111111111111 1 11),
([w398,w1,w2,w0,w3,w4],dL 0x0,dS 0x1f0e11160c0b0a0f190201,pH 0x111111111111111 0 11),
([w399,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d02150c0e1a1306010b0a03,pH 0x111111111111111 0 12),
([w1,w2,w264,w0,w3,w4],dL 0x0,dS 0xd0c0705040b0a0f1702110601,pH 0x111111111111111 0 13),
([w111,w1,w16,w0,w8,w4],dL 0xc5,dS 0xd12051510090e0b0a040f06,pH 0x111111111111111 1 12),
([w1,w400,w2,w0,w3,w4],dL 0x0,dS 0xd0c020e17130f0b0a0109,pH 0x111111111111111 0 11),
([w111,w65,w2,w0,w3,w4],dL 0x1a,dS 0x1a0a06051538100c1107020e0901,pH 0x111111111111111 1 14),
([w401,w1,w2,w0,w3,w4],dL 0x0,dS 0xb0e160c1c17110f130a0201,pH 0x111111111111111 0 12),
([w402,w1,w2,w0,w3,w4],dL 0x0,dS 0xb07150c100f170e0a060102,pH 0x111111111111111 0 12),
([w1,w112,w16,w0,w8,w4],dL 0x0,dS 0x120c1d020406050a0b190e0f01,pH 0x111111111111111 0 13),
([w65,w112,w2,w0,w3,w4],dL 0x0,dS 0xc09020e1a0a0b19060501,pH 0x111111111111111 0 11),
([w18,w1,w16,w7,w8,w4],dL 0xe20e3,dS 0xc12010b02040f0e19060a,pH 0x211211111111111 2 11),
([w18,w1,w2,w85,w3,w4],dL 0xe70e6,dS 0x4100201170b0a0f1106,pH 0x111111111111111 2 10),
([w18,w65,w2,w7,w3,w4],dL 0x1901a,dS 0x1a0c1905390211030a09060b01,pH 0x212111111111111 2 13),
([w18,w1,w2,w138,w3,w4],dL 0x0,dS 0x160c0e1305020d11010b1c0a0f0319,pH 0x111111111111111 0 15),
([w18,w1,w2,w143,w3,w4],dL 0x0,dS 0xc0d17120502010e0b03100a0f1a06,pH 0x111111111111111 0 15),
([w2,w21,w0,w9,w114,w4],dL 0x100,dS 0x16103c2a3a083b18040c11190d0701020a,pH 0x111111111111111 1 17),
([w82,w2,w21,w0,w9,w4],dL 0x100,dS 0x160c3d2a081f171e3a0d0a0111021906,pH 0x111111111111111 1 16),
([w61,w21,w0,w3,w9,w4],dL 0x102,dS 0x160c173e10080206040a190d0f0701,pH 0x111111111111111 1 15),
([w36,w21,w0,w3,w9,w4],dL 0x100,dS 0x160e3d100806010c02190d0a0f0704,pH 0x111111111111111 1 15),
([w2,w169,w21,w0,w9,w4],dL 0x2a,dS 0x1a0a1f0e0119070c0d02111706,pH 0x111111111111111 1 13),
([w144,w2,w21,w0,w9,w4],dL 0x0,dS 0xc0d1a2a081f0e1e3a011719061102,pH 0x111111111111111 0 15),
([w2,w21,w67,w3,w9,w4],dL 0x0,dS 0x161a0210083e06040c0a3d190d1c0701,pH 0x111111111111111 0 16),
([w2,w21,w7,w3,w9,w4],dL 0x8b083,dS 0xe0c3a041110190a020601,pH 0x111111111211121 2 11),
([w403,w1,w2,w0,w3,w9],dL 0x0,dS 0xe1c1302113a160d2a0c0f0a06010b,pH 0x111111111111111 0 15),
([w170,w1,w2,w7,w3,w4],dL 0x83,dS 0xc100f11060d07010e1c0a0b02,pH 0x111111111111111 1 13),
([w2,w95,w0,w3,w9,w4],dL 0x10310a109101100,dS 0xc0e0a1e2a023a08130604110d0701,pH 0x411221111111111 5 15),
([w404,w1,w2,w0,w3,w4],dL 0x100,dS 0xd1311013a0e020b0c0a0f06161c,pH 0x111111111111111 1 14),
([w36,w1,w158,w0,w3,w4],dL 0x3d,dS 0xd0c161c051913060b0a0f070102,pH 0x111111111111111 1 14),
([w36,w159,w1,w0,w3,w4],dL 0x0,dS 0xc140e050a0b011906,pH 0x111111111111111 0 9),
([w1,w12,w61,w67,w3,w4],dL 0x10f00f,dS 0xd062a3a08043e0716110c0f01,pH 0x112112111211111 2 13),
([w36,w1,w12,w67,w3,w4],dL 0xf,dS 0x5023d18061619010c070f0a03,pH 0x111111111111111 1 13),
([w36,w1,w12,w7,w3,w4],dL 0x18,dS 0x140c0b0f0e051906100711010a02,pH 0x111111111111111 1 14),
([w96,w1,w12,w2,w3,w4],dL 0x3,dS 0x161106040c10190d1c01070b0a09,pH 0x111111111111111 1 14),
([w2,w0,w11,w9,w8,w4],dL 0x0,dS 0x111a06040d0c010e0b0a09,pH 0x111111111111111 0 11),
([w43,w1,w0,w9,w8,w4],dL 0x100,dS 0x2a020d06041a110f010e0b0a,pH 0x111111111111111 1 12),
([w96,w1,w2,w0,w8,w4],dL 0x2,dS 0x1c06041a0a131911170b0e0109,pH 0x111111111111111 1 13),
([w104,w1,w2,w0,w9,w4],dL 0x1a,dS 0x1a0204010e0c0a1711,pH 0x111111111111111 1 9),
([w1,w2,w0,w143,w9,w4],dL 0x0,dS 0x150d17062a02080e10041a0b0f0701,pH 0x111111111111111 0 15),
([w37,w2,w0,w11,w9,w4],dL 0x0,dS 0x2a1a0f061f171113010e0b1e09040a,pH 0x111111111111111 0 15),
([w96,w37,w1,w2,w0,w4],dL 0x0,dS 0x1c070908131a0a020b060f0117110e,pH 0x111111111111111 0 15),
([w405,w1,w2,w3,w9,w4],dL 0x0,dS 0xc161f0e132a023a041c06080f110b0a0107,pH 0x111111111111111 0 18),
([w61,w33,w0,w3,w9,w4],dL 0x11f,dS 0x3f15171c081d051306040c0b0a0f0701,pH 0x111111111111111 1 16),
([w1,w61,w19,w0,w3,w55],dL 0x28,dS 0x20062a3a083f041c0c0a07110f01,pH 0x111111111111111 1 14),
([w36,w33,w0,w3,w9,w4],dL 0x100,dS 0x40150e1c081d1306010c050b0a0f0704,pH 0x111111111111111 1 16),
([w36,w1,w19,w0,w3,w55],dL 0x28,dS 0x540201306191c0a0c07010f02,pH 0x111111111111111 1 13),
([w265,w36,w1,w0,w3,w4],dL 0x0,dS 0x101306140e071c030a0d0c01,pH 0x111111111111111 0 12),
([w266,w36,w1,w0,w3,w4],dL 0x0,dS 0x1406110f160c0e0b0a0201,pH 0x111111111111111 0 11),
([w160,w36,w1,w0,w3,w4],dL 0x0,dS 0xa0f06110e02070c0d01,pH 0x111111111111111 0 10),
([w36,w1,w19,w7,w0,w3],dL 0x18,dS 0xe0a0507190d0f150611010c02,pH 0x111111111111111 1 13),
([w78,w36,w1,w0,w3,w4],dL 0x0,dS 0x140e0611121c0a020d0c01,pH 0x111111111111111 0 11),
([w1,w2,w0,w406,w3,w4],dL 0x18,dS 0x170e06050c0f110b0a0201,pH 0x111111111111111 1 11),
([w36,w2,w0,w11,w3,w4],dL 0x0,dS 0x60e0911010c0d020a0b,pH 0x111111111111111 0 10),
([w44,w36,w1,w2,w0,w4],dL 0x0,dS 0x61a0c0d0a0b0102110e,pH 0x111111111111111 0 10),
([w92,w36,w1,w0,w3,w4],dL 0x0,dS 0x1406110f160c0e0b0a0201,pH 0x111111111111111 0 11),
([w2,w33,w0,w9,w115,w4],dL 0x100,dS 0x15420b0d3a0820134106041c110a0c070105,pH 0x111111111111111 1 18),
([w91,w2,w33,w0,w9,w4],dL 0x100,dS 0xc400b1c2a081d071f0e1e3a0a1301110506,pH 0x111111111111111 1 18),
([w2,w171,w33,w0,w9,w4],dL 0x12b,dS 0xe0c1a1e011d070a0b05111706,pH 0x111111111111111 1 13),
([w128,w2,w33,w0,w9,w4],dL 0x0,dS 0xa0b2a081d17071f1e3a01130506110e,pH 0x111111111111111 0 16),
([w2,w33,w7,w0,w3,w9],dL 0x8b064,dS 0xe0a3a13070411150c050601,pH 0x111111111211121 2 12),
([w2,w33,w0,w3,w55,w9],dL 0x0,dS 0x50e150c1c2a083f1d1306040b16400a0701,pH 0x111111111111111 0 18),
([w172,w1,w2,w7,w0,w3],dL 0x64,dS 0x150a070b061a0f01160c0d05,pH 0x111111111111111 1 12),
([w96,w1,w19,w2,w0,w3],dL 0x3,dS 0x171113070f04150a0b1601060d0c09,pH 0x111111111111111 1 15)]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p2 : List StD := [
([w407,w1,w0,w3,w9,w4],dL 0x0,dS 0xc161f0e0b0a1e2a023a081306041c0f110701,pH 0x111111111111111 0 19),
([w2,w67,w11,w3,w9,w4],dL 0x137,dS 0xd1a09081304060c0b0a0f1c0107,pH 0x111111111111111 1 14),
([w1,w2,w67,w7,w3,w55],dL 0x138051,dS 0x1a0d0e19130f062a081103071601,pH 0x111111111111111 2 14),
([w2,w0,w11,w9,w62,w4],dL 0x101139,dS 0xc453a0a44080406110d0b0f010907,pH 0x112112111111111 2 15),
([w44,w2,w0,w11,w9,w4],dL 0x10a101,dS 0x2a1f0e3a0f011113090b0a06,pH 0x211111111111111 2 12),
([w2,w0,w173,w11,w9,w4],dL 0x0,dS 0xc0d1f17011a1e0f13060a0b0e110907,pH 0x111111111111111 0 16),
([w145,w2,w0,w11,w9,w4],dL 0x0,dS 0x2a0a0b1a080f071f3a1e01130906110e,pH 0x111111111111111 0 16),
([w2,w0,w11,w3,w55,w9],dL 0x13c,dS 0x90e0c080f191304060d160b0a0107,pH 0x111111111111111 1 15),
([w1,w2,w0,w408,w3,w4],dL 0x100,dS 0x6050c0f0d0e0b0a0201,pH 0x111111111111111 1 10),
([w204,w1,w7,w0,w3,w4],dL 0x0,dS 0xb0d110c0a130717090f0e010602,pH 0x111111111111111 0 14),
([w43,w1,w194,w0,w3,w4],dL 0x0,dS 0x60d0c0e0211090b0a,pH 0x111111111111111 0 9),
([w409,w1,w2,w0,w3,w4],dL 0x0,dS 0x10d0c0e11130f02090b0a,pH 0x111111111111111 0 11),
([w41,w2,w95,w0,w3,w4],dL 0x153,dS 0x38110e0113060c0d0a020b,pH 0x111111111111111 1 11),
([w43,w41,w1,w0,w8,w4],dL 0x153,dS 0x170106090c0e0d020a0b,pH 0x111111111111111 1 10),
([w104,w41,w1,w2,w0,w4],dL 0x0,dS 0xf011f1e06130209170b0a0e11,pH 0x111111111111111 0 13),
([w410,w1,w2,w0,w3,w4],dL 0x0,dS 0x1e0e1a1c0d0c110a0f130201,pH 0x111111111111111 0 12),
([w113,w1,w16,w0,w8,w4],dL 0x0,dS 0x12040a0f06020c0d0e190701,pH 0x111111111111111 0 12),
([w65,w113,w2,w0,w3,w4],dL 0x0,dS 0xa050906110c0d0e070201,pH 0x111111111111111 0 11),
([w411,w1,w2,w0,w3,w4],dL 0x0,dS 0x170e100a0d0c19060102,pH 0x111111111111111 0 10),
([w39,w1,w16,w7,w0,w8],dL 0x1940e3,dS 0x70a120105040f0d190e060c,pH 0x211121111111111 2 12),
([w39,w1,w2,w0,w85,w3],dL 0x197196,dS 0x7041505010d0b170f0611,pH 0x111111111111111 2 11),
([w65,w39,w2,w7,w0,w3],dL 0x1901a,dS 0xe0a07490511060c02090d01,pH 0x221111111111111 2 12),
([w39,w1,w2,w0,w138,w3],dL 0x0,dS 0x110e19050d160c1c0f01020b13,pH 0x111111111111111 0 13),
([w39,w1,w2,w0,w143,w3],dL 0x0,dS 0x1a0d05150c010217100f0b060e,pH 0x111111111111111 0 13),
([w267,w2,w21,w0,w3,w4],dL 0x104,dS 0x38030111100a020c0d1906,pH 0x111111111111111 1 11),
([w205,w2,w21,w0,w3,w4],dL 0x100,dS 0x103a0807063d160d0a040c020e,pH 0x111111111111111 1 13),
([w144,w82,w1,w2,w0,w4],dL 0x0,dS 0x6110a19100c0d120201,pH 0x111111111111111 0 10),
([w412,w1,w2,w21,w0,w3],dL 0x0,dS 0x170e01110a100619020d0c,pH 0x111111111111111 0 11),
([w1,w2,w169,w0,w206,w4],dL 0x0,dS 0x1a1f0f030a10010e0d170c02061119,pH 0x111111111111111 0 15),
([w1,w2,w21,w0,w3,w268],dL 0x34,dS 0xe0102100d110a0c0619,pH 0x111111111111111 1 10),
([w144,w269,w1,w2,w0,w4],dL 0x0,dS 0x11f100a0d0c1119060e,pH 0x111111111111111 0 10),
([w270,w1,w2,w21,w7,w3],dL 0x5,dS 0x160b1102170d0e0a10,pH 0x111111111111111 1 9),
([w1,w2,w21,w7,w23,w3],dL 0x35,dS 0x17160e11010b0d0a02100619,pH 0x111111111111111 1 12),
([w2,w21,w0,w3,w35,w4],dL 0x35083,dS 0x3d0c2c2a0e0a02100619,pH 0x111121111111111 2 10),
([w1,w2,w0,w3,w271,w4],dL 0x3a10d083,dS 0xe170b0f010c2a020a100619,pH 0x111121111111111 3 12),
([w413,w1,w2,w0,w3,w4],dL 0x0,dS 0xc0d0e170a100619022a,pH 0x111111111111111 0 10),
([w164,w2,w21,w0,w3,w4],dL 0x34,dS 0xe020d110a05190c06,pH 0x111111111111111 1 9),
([w2,w414,w95,w0,w3,w4],dL 0x2d1b31b21b1,dS 0xc053a1101070a0d0e0206,pH 0x322312414111114 4 11),
([w2,w95,w0,w3,w415,w4],dL 0x1b510a1b4101100,dS 0xc0e0a1e2a023a08130604110d0701,pH 0x411221111111111 5 15),
([w416,w2,w95,w0,w3,w4],dL 0x0,dS 0x38010e1102060c0d130a0b,pH 0x111111111111111 0 11),
([w417,w2,w95,w0,w3,w4],dL 0x0,dS 0x3811020e01130d0c060b0a,pH 0x111111111111111 0 11),
([w1,w12,w2,w7,w3,w35],dL 0x83,dS 0x6010d111019160e070b2a0a,pH 0x111111111111111 1 12),
([w1,w2,w7,w3,w272],dL 0x1bd1bc081,dS 0x16090b110e0a0207100119,pH 0x1112111111 3 11),
([w418,w1,w2,w0,w3,w4],dL 0x0,dS 0x1f0c1606110e0a0b070f2a02,pH 0x111111111111111 0 12),
([w273,w1,w2,w0,w3,w4],dL 0x0,dS 0x1f02160e0c11100a1906,pH 0x111111111111111 0 10),
([w83,w2,w0,w3,w35,w4],dL 0x121,dS 0x1f0c0f110e080a0b0619,pH 0x111111111111111 1 10),
([w1,w274,w57,w0,w8,w4],dL 0x1d4,dS 0x715190a010d0c060f04,pH 0x111111111111111 1 10),
([w275,w1,w57,w0,w8,w4],dL 0x4,dS 0xa0b07190410150c0f06,pH 0x111111111111111 1 10),
([w1,w276,w57,w0,w8,w4],dL 0x1d5,dS 0xe100c1d01060f0b0a04,pH 0x111111111111111 1 10),
([w277,w1,w57,w0,w8,w4],dL 0x5,dS 0xb0e04150f06100a,pH 0x111111111111111 1 8),
([w1,w57,w7,w0,w8,w4],dL 0x1d51d40e3,dS 0x70f19010e0604,pH 0x322213312111111 3 7),
([w2,w57,w0,w11,w3,w4],dL 0x48036,dS 0x3a0e21070d0c0f0b0a04110609,pH 0x111111211111111 2 13),
([w1,w2,w0,w278,w3,w4],dL 0x13b1d6075,dS 0xe110b0a1306010d070409,pH 0x313111111111111 3 11),
([w279,w1,w2,w0,w3,w4],dL 0x0,dS 0xd150c0a06110b100f170409,pH 0x111111111111111 0 12),
([w73,w1,w419,w16,w0,w4],dL 0x1e0,dS 0x41d070d430b0c060a,pH 0x111111111111111 1 9),
([w420,w73,w1,w16,w0,w4],dL 0x1e0,dS 0xd06010f0b4315100c0a,pH 0x111111111111111 1 10),
([w421,w73,w1,w0,w8,w4],dL 0x1e1,dS 0x190410020e0b0a09150c01,pH 0x111111111111111 1 11),
([w73,w1,w422,w0,w8,w4],dL 0x1e1,dS 0xd140a100e011909150c04,pH 0x111111111111111 1 11),
([w423,w73,w1,w0,w8,w4],dL 0x1e2,dS 0xd0c0b090e04150519100a01,pH 0x111111111111111 1 12),
([w73,w1,w424,w0,w8,w4],dL 0x1e2,dS 0x120b0c150e06190109100a04,pH 0x111111111111111 1 12),
([w73,w1,w7,w0,w8,w4],dL 0x1e1,dS 0xd140c0a060b014b19120e0904,pH 0x111111111111111 1 13),
([w1,w16,w280,w0,w8,w4],dL 0x9d01a,dS 0xc150f100d12040b0e090a01,pH 0x111111211211111 2 12),
([w281,w1,w16,w0,w8,w4],dL 0x0,dS 0x1209040c1d0605190e0a0b01,pH 0x111111111111111 0 12),
([w1,w16,w72,w7,w8,w4],dL 0x1e3018,dS 0x70c0b061402040e0a190901,pH 0x211111111111111 2 12)]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p3 : List StD := [
([w1,w16,w0,w11,w8,w4],dL 0x1a075,dS 0x120c010d0f0e06090a0b,pH 0x112111111111111 2 10),
([w1,w7,w0,w85,w8,w4],dL 0xa31e61e5,dS 0x70f060901,pH 0x111121213111111 3 5),
([w1,w0,w85,w8,w4],dL 0x1e51e6,dS 0x709040d0f0e060b01,pH 0x2111112111 2 9),
([w104,w1,w16,w0,w8,w4],dL 0xa6,dS 0xc4b04060e0d090b0a01,pH 0x111111111111111 1 10),
([w1,w16,w7,w0,w103,w8],dL 0x1e8018,dS 0xf070d0a120504190e0c0901,pH 0x121111111111111 2 12),
([w282,w1,w16,w0,w8,w4],dL 0x0,dS 0x12040a0906020c0d070e1901,pH 0x111111111111111 0 12),
([w425,w1,w2,w0,w3,w4],dL 0x0,dS 0x110e060c0d130a0b0904,pH 0x111111111111111 0 10),
([w283,w1,w2,w0,w3,w4],dL 0x0,dS 0x40d0c170f11060b0a,pH 0x111111111111111 0 9),
([w426,w1,w2,w0,w3,w4],dL 0x0,dS 0x10e11130d0c060b0a,pH 0x111111111111111 0 9),
([w43,w65,w1,w0,w3,w4],dL 0x0,dS 0x11907110f0d0c0e130b0a06,pH 0x111111111111111 0 12),
([w44,w65,w1,w2,w0,w4],dL 0x0,dS 0x11a130d0c060b0a0e11,pH 0x111111111111111 0 10),
([w2,w0,w284,w3,w8,w4],dL 0x0,dS 0xd0c1a111906090e1302010b0a,pH 0x111111111111111 0 13),
([w1,w2,w72,w7,w3,w103],dL 0x511f2018,dS 0x1a0d0e19050911130a020701,pH 0x313111111111111 3 12),
([w1,w2,w0,w174,w3,w4],dL 0x1903601a,dS 0x1511060d010c0e0a0b1309,pH 0x313112111111211 3 11),
([w1,w0,w60,w8,w62,w4],dL 0x1e60c61f5,dS 0x4d0e4c130d091a0b19020f01,pH 0x112132111111111 3 12),
([w44,w1,w0,w60,w8,w4],dL 0xd50a60c6,dS 0x161119090e0f131a0102,pH 0x311111111111211 3 10),
([w43,w1,w0,w8,w62,w4],dL 0xd50c61f7,dS 0xc0f0d0e060b10090201,pH 0x111111111111111 3 10),
([w43,w44,w1,w0,w8,w4],dL 0xa6,dS 0xc110106090e0d020b0a,pH 0x111111111111111 1 10),
([w1,w175,w0,w3,w8,w4],dL 0x16,dS 0xd0c110b1905040201130a060f1003,pH 0x111111111111111 1 15),
([w1,w0,w427,w3,w8,w4],dL 0x2,dS 0x1d061a190b130e0910020a01,pH 0x111111111111111 1 12),
([w1,w176,w2,w0,w8,w4],dL 0x2,dS 0xd0c061a102a0804020b0a0e111701,pH 0x111111111111111 1 15),
([w1,w2,w428,w0,w8,w4],dL 0x16,dS 0xd0c1a1019090b0e13020a01,pH 0x111111111111111 1 12),
([w285,w2,w7,w0,w3,w4],dL 0x0,dS 0xb0d110c0a1307170f090e020601,pH 0x111111111111111 0 14),
([w1,w429,w2,w0,w3,w4],dL 0x1a,dS 0x7151005090b0a0e0602170f01,pH 0x111111111111111 1 13),
([w135,w2,w0,w11,w3,w4],dL 0x19,dS 0x21913170e010f0c0b060a09,pH 0x111111111111111 1 12),
([w1,w2,w0,w430,w3,w4],dL 0x19,dS 0xc0e0f0601030a0b130217070911,pH 0x111111111111111 1 14),
([w431,w1,w2,w0,w3,w4],dL 0x0,dS 0xb130e02160c1c0f1711060a,pH 0x111111111111111 0 12),
([w1,w2,w0,w432,w3,w4],dL 0x75,dS 0xc1306030d0b0a0e021109,pH 0x111111111111111 1 11),
([w198,w2,w0,w11,w3,w4],dL 0x1a,dS 0x1a0e0c0f010b0611090a,pH 0x111111111111111 1 10),
([w1,w2,w0,w433,w3,w4],dL 0x1a,dS 0x170c0b130702080e0a090f110106,pH 0x111111111111111 1 14),
([w434,w1,w2,w0,w3,w4],dL 0x0,dS 0xb071101150c17100f0e0a06,pH 0x111111111111111 0 12),
([w1,w435,w2,w0,w3,w4],dL 0x13b,dS 0x110e0d130f060a0b0901,pH 0x111111111111111 1 10),
([w286,w2,w33,w0,w3,w4],dL 0x12d,dS 0x381d0e01150c051302060a0b,pH 0x111111111111111 1 12),
([w207,w2,w33,w0,w3,w4],dL 0x100,dS 0x3a08061d400e0b151a1c0c040a05,pH 0x111111111111111 1 14),
([w128,w91,w1,w2,w0,w4],dL 0x0,dS 0x14110c150613050a0b01,pH 0x111111111111111 0 10),
([w287,w1,w2,w33,w7,w3],dL 0x4,dS 0x1c0d05110b0e0a15,pH 0x111111111111111 1 8),
([w436,w1,w2,w33,w3,w4],dL 0x0,dS 0x1d010e0c15110613050b0a,pH 0x111111111111111 0 11),
([w1,w2,w171,w0,w208,w4],dL 0x0,dS 0x1e1d0c150201060e1a170b050a1113,pH 0x111111111111111 0 15),
([w1,w2,w33,w288,w3,w4],dL 0x47,dS 0x1d15010c1a1105060b130a,pH 0x111111111111111 1 11),
([w128,w289,w1,w2,w0,w4],dL 0x0,dS 0x14011e150c1306110b0a1a,pH 0x111111111111111 0 11),
([w2,w33,w0,w34,w3,w4],dL 0x49064,dS 0x11400a251d070f0c05081a06,pH 0x121111221111111 2 12),
([w1,w2,w0,w290,w3,w4],dL 0x12c03b064,dS 0xe0a1d1a0f0601070508,pH 0x221111111111111 3 10),
([w437,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d110c150e06130a0b0508,pH 0x111111111111111 0 11),
([w1,w2,w33,w14,w7,w3],dL 0x49,dS 0xe1c1a11010d0b0a05150613,pH 0x111111111111111 1 12),
([w162,w2,w33,w0,w3,w4],dL 0x47,dS 0x1d071a0e0b0c050206130a,pH 0x111111111111111 1 11),
([w438,w1,w2,w0,w3,w4],dL 0x0,dS 0x1e0c0d0a06111c0f1a0805,pH 0x111111111111111 0 11),
([w1,w19,w2,w7,w34,w3],dL 0x64,dS 0xf01130b1115061c0d1a080a,pH 0x111111111111111 1 12),
([w291,w1,w2,w0,w3,w4],dL 0x0,dS 0x1e1d05150c1a1c1311060a,pH 0x111111111111111 0 11),
([w1,w2,w7,w292,w3],dL 0x21f2250f3,dS 0x1c050b091a0206110a150113,pH 0x2111111111 3 12),
([w137,w2,w0,w34,w3,w4],dL 0x120,dS 0x1e09011c130d0a0611080c,pH 0x111111111111111 1 11),
([w209,w2,w0,w34,w3,w4],dL 0x68,dS 0x1e3408021a1c1301060c0d110a,pH 0x111111111111111 1 13),
([w210,w2,w0,w34,w3,w4],dL 0x2b00a,dS 0x111e1d132107250f0d02150c0a0608,pH 0x112112112111211 2 15),
([w78,w139,w1,w0,w3,w4],dL 0x0,dS 0x140e0611121c020a080d0c,pH 0x111111111111111 0 11),
([w439,w1,w2,w0,w34,w3],dL 0x0,dS 0x1e010f110a061a1c080d0c,pH 0x111111111111111 0 11),
([w1,w165,w0,w177,w3,w4],dL 0x0,dS 0x1e1d1307010a020f0d11190c1a1c0608,pH 0x111111111111111 0 16),
([w1,w2,w0,w34,w211,w3],dL 0x120,dS 0x1e01111a130a1c0d06080c,pH 0x111111111111111 1 11),
([w293,w139,w1,w0,w3,w4],dL 0x0,dS 0x140e02111206131c0a0d0c,pH 0x111111111111111 0 11),
([w294,w1,w2,w7,w34,w3],dL 0x3e,dS 0x150a1a111c0f06,pH 0x111111111111111 1 7),
([w440,w2,w0,w94,w3,w4],dL 0x6c23f23e23d23c,dS 0xd091121020a060f010c0e,pH 0x343111431155111 5 11),
([w2,w0,w94,w441,w3,w4],dL 0x24103200a240041,dS 0xc05010a031d0f2106110e0207,pH 0x343111111111111 5 13),
([w442,w2,w0,w94,w3,w4],dL 0x0,dS 0x340601020f0e0d0c110b0a,pH 0x111111111111111 0 11),
([w443,w2,w0,w94,w3,w4],dL 0x0,dS 0x34020f0106110c0d0e0a0b,pH 0x111111111111111 0 11),
([w295,w2,w0,w11,w3,w4],dL 0x77,dS 0x34020d0c090f1101060e0b0a,pH 0x111111111111111 1 12),
([w175,w2,w0,w11,w3,w4],dL 0x32041,dS 0x5210c020f170e0609,pH 0x221111211121111 2 9)]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p4 : List StD := [
([w43,w141,w1,w0,w3,w4],dL 0x0,dS 0x60d0c0e0211090b0a,pH 0x111111111111111 0 9),
([w296,w2,w0,w11,w3,w4],dL 0x140,dS 0x4e0e01130d0c0f020b060a,pH 0x111111111111111 1 11),
([w176,w2,w0,w11,w3,w4],dL 0x10a101,dS 0xd3a0813040e0c010f170609,pH 0x221111211121111 2 12),
([w145,w44,w1,w2,w0,w4],dL 0x0,dS 0x110c0d060a0b130901,pH 0x111111111111111 0 9),
([w1,w2,w0,w11,w212,w4],dL 0x75,dS 0x10c130e110d090a0b,pH 0x111111111111111 1 9),
([w444,w1,w2,w0,w11,w4],dL 0x0,dS 0x1301170c0d0f060a0b0e0911,pH 0x111111111111111 0 12),
([w1,w166,w0,w178,w3,w4],dL 0x0,dS 0x1713100f07010221190e0a06090b,pH 0x111111111111111 0 14),
([w1,w2,w0,w11,w297,w4],dL 0x1a,dS 0x20d0e0f0c110b06090a,pH 0x111111111111111 1 10),
([w203,w1,w2,w0,w11,w4],dL 0x0,dS 0x1201170c0d0f06090a0b110e,pH 0x111111111111111 0 12),
([w298,w141,w1,w0,w3,w4],dL 0x0,dS 0x60f020e0d0c110b0a,pH 0x111111111111111 0 9),
([w1,w0,w11,w213,w3,w4],dL 0x13b,dS 0xc02130e0f0d06090a0b,pH 0x111111111111111 1 10),
([w445,w1,w0,w11,w3,w4],dL 0x0,dS 0x1070e130f0c0d110a0b0906,pH 0x111111111111111 0 12),
([w1,w2,w0,w173,w179,w4],dL 0x0,dS 0xa0b0f0602011a170e3a071109,pH 0x111111111111111 0 13),
([w1,w299,w0,w11,w3,w4],dL 0x19,dS 0xd01130c170f1106090a0b,pH 0x111111111111111 1 11),
([w204,w1,w0,w11,w3,w4],dL 0x0,dS 0x1070e0913060c0d110a0b0f,pH 0x111111111111111 0 12),
([w145,w300,w1,w2,w0,w4],dL 0x0,dS 0x10d0c13110b0a0617,pH 0x111111111111111 0 9),
([w301,w44,w1,w2,w0,w4],dL 0x0,dS 0x19050e160d1c0b0f130201,pH 0x111111111111111 0 11),
([w44,w1,w2,w0,w302,w4],dL 0x0,dS 0x11090d0c130f010b0a02,pH 0x111111111111111 0 10),
([w43,w303,w1,w0,w3,w4],dL 0x0,dS 0x1a05150d1d12061317100b070e0201,pH 0x111111111111111 0 15),
([w43,w1,w304,w0,w3,w4],dL 0x0,dS 0x6090d0c0e17020b0a01,pH 0x111111111111111 0 10),
([w305,w1,w2,w7,w3,w35],dL 0xd,dS 0xd10132a0b160a0f06,pH 0x111111111111111 1 9),
([w306,w2,w0,w3,w35,w4],dL 0x86,dS 0x1f34160c020e01110b0a1906,pH 0x111111111111111 1 12),
([w214,w2,w0,w3,w35,w4],dL 0xa,dS 0x50e1f040b03212c0a0c022a100619,pH 0x111111111111111 1 15),
([w92,w142,w1,w0,w3,w4],dL 0x0,dS 0x140c1611060e130b0a0f2a02,pH 0x111111111111111 0 12),
([w446,w1,w2,w3,w35,w4],dL 0x0,dS 0x1f010c1611070e0f0a0b,pH 0x111111111111111 0 10),
([w1,w168,w0,w3,w215,w4],dL 0x0,dS 0x131f120c1601110f0e0a0b0619,pH 0x111111111111111 0 13),
([w1,w2,w307,w3,w35,w4],dL 0x121,dS 0x1f16010c110e0a0b0619,pH 0x111111111111111 1 10),
([w308,w142,w1,w0,w3,w4],dL 0x0,dS 0x140c1611020e130f06190b0a,pH 0x111111111111111 0 12)]
noncomputable def p13_D5 : List StD := p13_D5p0 ++ p13_D5p1 ++ p13_D5p2 ++ p13_D5p3 ++ p13_D5p4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x0 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x1 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x2 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x3 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x4 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (4*64)).take 64) = true := by decide +kernel
theorem p13_I5 : LevelN p13_R p13_T 5 p13_D5 := levelStep p13_B p13_W p13_Q p13_I4 (chunks 64 p13_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C5x0
  · exact p13_C5x1
  · exact p13_C5x2
  · exact p13_C5x3
  · exact p13_C5x4
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D6p0 : List StD := [
([w82,w1,w2,w6,w0,w3,w4],dL 0xb00a002009,dS 0xf050b0615100d0402,pH 0x313111111113121321111 4 9),
([w25,w1,w12,w2,w0,w3,w4],dL 0xb00f00e,dS 0xd180b06050e160a07010c02,pH 0x212111111112111212111 3 12),
([w1,w56,w0,w8,w4],dL 0xd003016015,dS 0xf0a0b061107190e090204,pH 0x3432221111 4 11),
([w1,w6,w7,w0,w3,w8,w4],dL 0x1b01900d018017,dS 0x1b110d070c0a050403011a190e130602,pH 0x211511124111312111111 5 16),
([w27,w1,w32,w6,w0,w3,w4],dL 0x20003,dS 0x15100a1305011d0e170c0d1e0611070204,pH 0x111111111111111111211 2 17),
([w27,w1,w30,w6,w0,w3,w4],dL 0x3021,dS 0x1517100c19010e1f05110a1d06020b04,pH 0x111211111111111111111 2 16),
([w27,w1,w6,w7,w0,w3,w4],dL 0x1e003019,dS 0xd0c0a05011d0e070f19130602111704,pH 0x131111111211111111111 3 16),
([w91,w1,w2,w6,w0,w3,w4],dL 0x2600a002025,dS 0xf050d0615100b0402,pH 0x313111111113121123111 4 9),
([w25,w1,w19,w2,w0,w3,w4],dL 0x2602800e,dS 0xb200d190e1c050c0a060102,pH 0x212111111112111212111 3 12),
([w1,w2,w447,w6,w0,w3,w4],dL 0x2902b00202a,dS 0xd15100a0e0b1d07030121171a020c0611,pH 0x111111411311112111121 4 17),
([w262,w1,w2,w6,w0,w3,w4],dL 0xa02c009,dS 0x151e070f012111100c04020d06,pH 0x323111112111211111111 3 13),
([w1,w2,w448,w6,w0,w3,w4],dL 0x802e00202d,dS 0xd150c0a1d070503012117100b0e060211,pH 0x111111141311112111121 4 17),
([w449,w1,w2,w6,w0,w3,w4],dL 0x2f032030031,dS 0x1110130401210d0e171d050206,pH 0x332111112111211112211 4 13),
([w1,w2,w32,w56,w0,w3,w4],dL 0x36008034020035033003,dS 0x190521100c170704030d0602,pH 0x322312161211141111111 7 12),
([w25,w1,w2,w32,w0,w3,w4],dL 0x36035034038,dS 0x170a0e1006020c0d1901,pH 0x211121111111111111111 4 10),
([w1,w2,w32,w30,w0,w3,w4],dL 0x3b03a02f039,dS 0xc1a0a110e1d0605020701,pH 0x211131111111111111111 4 11),
([w1,w2,w32,w6,w14,w3,w4],dL 0x10037,dS 0xa2419070504010321150d110c100602,pH 0x112111111211111111111 2 16),
([w1,w2,w32,w6,w7,w3,w4],dL 0x1002f018,dS 0xb0e1b190705040103211711100602,pH 0x231111111311111111111 3 15),
([w450,w1,w2,w6,w0,w3,w4],dL 0x42041033,dS 0x17110f050401210a060215030c07,pH 0x122332332111213231211 3 14),
([w1,w2,w451,w6,w0,w3,w4],dL 0x10044002043,dS 0xb15100d1a1d07030121170e0c0a020611,pH 0x111111114311112111121 4 17),
([w452,w1,w2,w6,w0,w3,w4],dL 0x46032045,dS 0x17110f0401210c100a1d050206,pH 0x221233231121113132211 3 13),
([w1,w2,w56,w30,w0,w3,w4],dL 0x8048047049021045003,dS 0x70f13210a170515040b0602,pH 0x224171211211133111111 7 12),
([w1,w2,w56,w6,w14,w0,w4],dL 0x33008037,dS 0xd0a24070f050921150c11041a170602,pH 0x312111111211111111111 3 16),
([w45,w1,w2,w56,w6,w0,w4],dL 0x4c042,dS 0x150b0f0904210a0e10111706020d030c07,pH 0x111112111111111111111 2 17),
([w1,w2,w56,w6,w0,w23,w4],dL 0x4500804a,dS 0xb0a29070f050921100c11040e170602,pH 0x231111111211111111111 3 16),
([w71,w1,w2,w56,w6,w0,w4],dL 0x4c046,dS 0x100d0f0904210c1a1511170a0b1d050206,pH 0x111112111111111111111 2 17),
([w1,w2,w453,w3,w4],dL 0x3d03600304e,dS 0x1a0e191306050a0b070102,pH 0x4332221111 4 11),
([w1,w2,w7,w0,w3,w102,w4],dL 0x5204804f036051018017,dS 0x1a170d0e0c0a190f07050902110601,pH 0x231523123121112111111 7 15),
([w1,w2,w0,w3,w454],dL 0x4803d003053,dS 0xd0e11191306050c070102,pH 0x3432221111 4 11),
([w1,w2,w6,w455,w0,w3,w4],dL 0x2b038055041056037,dS 0xb0703012115170c110206,pH 0x133341111412112222411 6 11),
([w1,w2,w6,w0,w3,w456,w4],dL 0x4405705805903204a,dS 0xd0a170e07040301210c100206,pH 0x124221141111313341111 6 13),
([w25,w1,w2,w30,w0,w3,w4],dL 0x48049047057,dS 0xc17150e060a0b130201,pH 0x112121111111111111111 4 10),
([w25,w1,w2,w6,w14,w0,w4],dL 0xa038037,dS 0xd0b13050121240e150c0a1a0217061104,pH 0x211111111111111111311 3 17),
([w25,w1,w2,w6,w0,w23,w4],dL 0xa05704a,dS 0xd0b0a0712050121291a100e0217060c1104,pH 0x121111111111111111311 3 18),
([w25,w1,w2,w14,w0,w4],dL 0x3804f03705a03d,dS 0xd15140705080a0c170611021a1301,pH 0x511333222111111 5 15),
([w25,w1,w2,w7,w0,w3,w4],dL 0x304803605b057038051,dS 0x17070e06130201,pH 0x121213312731241111111 7 7),
([w25,w1,w2,w0,w23,w4],dL 0x5704a05c05203d,dS 0x10070c192a061711020a0e0b1201,pH 0x151441331111111 5 14),
([w309,w1,w2,w6,w0,w3,w4],dL 0x3905f041,dS 0x1113050401210b060217150e0307,pH 0x111221221111112211111 3 14),
([w202,w1,w2,w6,w0,w3,w4],dL 0xa05e025,dS 0x101f0f01210e150a0b040602,pH 0x323111211121111111111 3 12),
([w1,w2,w30,w6,w7,w0,w3],dL 0x29039018,dS 0x1a13040121170d1d0511150602,pH 0x213111111311111111111 3 13),
([w1,w2,w30,w6,w0,w23,w3],dL 0x2904a,dS 0xc2913040121100a1d050b11150602,pH 0x211111111211111111111 2 15),
([w2,w6,w14,w0,w34,w3,w4],dL 0x800a041,dS 0x5241e1d21070f111a150c020806,pH 0x212111113312111111111 3 14),
([w2,w6,w0,w34,w3,w4],dL 0x1603600204100a067066008063064,dS 0x251d21061c15110a08021a070d,pH 0x652422568111112 10 13),
([w1,w6,w14,w0,w46,w3,w4],dL 0x400a041068,dS 0x1a240b110301060215130c,pH 0x313222244113121111111 4 11),
([w78,w1,w6,w14,w0,w3,w4],dL 0x3700a02b041,dS 0x24171003011d070f2111150c021306,pH 0x311111131122221141411 4 15),
([w78,w1,w6,w0,w3,w4],dL 0x6900a02a00504103702b002,dS 0xd0504031d070c11170a1015130602,pH 0x541333222111112 8 15),
([w1,w2,w14,w0,w177,w3,w4],dL 0x3b06105a02b04104f,dS 0xa0e0b1d0f0705010315130c020608,pH 0x151222113111111111111 6 15),
([w140,w1,w2,w6,w0,w3,w4],dL 0x4105502b,dS 0xd1d1a070b020c15170a101106,pH 0x111111111111121121311 3 13),
([w140,w1,w2,w14,w0,w3,w4],dL 0x37038041,dS 0x101d060c02151308,pH 0x111121111111111133311 3 8),
([w140,w1,w2,w0,w3,w4],dL 0x4804103b03703802b,dS 0x13070d110a020c15061008,pH 0x421333111163511 6 11),
([w1,w2,w6,w161,w0,w3,w4],dL 0x206a03200a00306d04106c,dS 0x1517100a1d0e070301210c110206,pH 0x522111652411141111111 8 14),
([w84,w1,w2,w6,w0,w3,w4],dL 0x4906e03203b,dS 0x110f0401210c1d050e0a0602,pH 0x221241211121111122211 4 12),
([w1,w2,w6,w14,w7,w3,w4],dL 0x806f005049041,dS 0xc0e1d0f05040121111c1a0a0b0602,pH 0x111313221111131111111 5 15),
([w1,w2,w457,w6,w0,w3,w4],dL 0x41,dS 0x150d0a1d0f050409210c110703170b101a0602,pH 0x111111111111111111111 1 19),
([w1,w2,w6,w0,w3,w200,w4],dL 0x803503203b,dS 0xb11070f040301211d05100e0602,pH 0x431221133111111111111 4 14),
([w2,w6,w7,w0,w11,w3,w4],dL 0x74072032041,dS 0xc0a1d21070f1102170e0906,pH 0x221111113121111111111 4 12),
([w2,w6,w0,w11,w3,w4],dL 0x48032002041036074076072075,dS 0xc04171d2106110b090d0e020a07,pH 0x321242815111112 9 14),
([w1,w6,w7,w0,w60,w3,w4],dL 0x78032004041077,dS 0x1c05030111060f0217,pH 0x431222323141121111111 5 9),
([w43,w1,w6,w7,w0,w3,w4],dL 0x7903201802e041,dS 0xc0a0503011b07132111170e0f0206,pH 0x411111411122221311311 5 15),
([w43,w1,w6,w0,w3,w4],dL 0x4c02d03204102e002,dS 0x504031d070c170a150f10060e02,pH 0x123413222111112 6 14),
([w1,w2,w7,w0,w178,w3,w4],dL 0xd02e07b04107a,dS 0xb0c170a1113070401030f020e0609,pH 0x315222114111111111111 5 15),
([w93,w1,w2,w6,w0,w3,w4],dL 0x4107c02e,dS 0x5030a11150d020e0b100617,pH 0x111111111111121211311 3 12),
([w93,w1,w2,w7,w0,w3,w4],dL 0x1807d041,dS 0x1004060e02170f09,pH 0x111211111111111313311 3 8),
([w93,w1,w2,w0,w3,w4],dL 0x7e03d01604101807d02e,dS 0x110f0403150b020e17061009,pH 0x712312111135411 7 12)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p1 : List StD := [
([w44,w1,w2,w6,w0,w3,w4],dL 0x4807f03600208000300a,dS 0xc070f0501210e17040d0b0602,pH 0x131715111111111111221 7 13),
([w1,w2,w6,w7,w0,w23,w3],dL 0x808103500406d032,dS 0x170a0b070f04030121110e160c0d0602,pH 0x123121415113111111111 6 16),
([w2,w6,w0,w23,w3,w35,w4],dL 0x808203200a,dS 0x291f030a1d21110e060f022a1007,pH 0x211431211121111111111 4 14),
([w2,w6,w0,w3,w35,w4],dL 0x3200200a01606b083085082008,dS 0x32c101d1621060e0c020b2a11070a,pH 0x212511967514112 9 15),
([w1,w6,w0,w23,w3,w127,w4],dL 0x503208600a,dS 0x1d290e0d1a0c061102010a190310,pH 0x311141311132121222211 4 14),
([w92,w1,w6,w0,w23,w3,w4],dL 0x3204404a00a,dS 0x2915170a0301070f210c1119021006,pH 0x111411411133311222111 4 15),
([w92,w1,w6,w0,w3,w4],dL 0x400a08704303204404a002,dS 0xb11050403070c150e0a1719100602,pH 0x141222333111113 8 15),
([w1,w2,w0,w23,w3,w215,w4],dL 0x3205c04403503e,dS 0x290d1a0b0f01020e102a0a030619,pH 0x121131111111111111111 5 14),
([w167,w1,w2,w6,w0,w3,w4],dL 0xa058044,dS 0xb1d07110d02150c170e0a1006,pH 0x111111111111121121311 3 13),
([w167,w1,w2,w0,w23,w3,w4],dL 0x4a03205700a,dS 0x150a061002192a,pH 0x212211211121111244111 4 7),
([w167,w1,w2,w0,w3,w4],dL 0x3603500a04a044057,dS 0xb1119070c0e0a15171006022a,pH 0x151313222214622 6 13),
([w163,w1,w2,w6,w0,w3,w4],dL 0x7103a041035,dS 0xc1d110f050401210a06020e0703,pH 0x122312112111211221211 4 14),
([w1,w2,w458,w6,w0,w3,w4],dL 0x4c,dS 0x100c0f0409210d150b11170a1d050e0602,pH 0x111111111111111111111 1 17),
([w1,w2,w6,w201,w0,w3,w4],dL 0x4900803a041,dS 0x1a1d110f05040121150e07030602,pH 0x211113241111111111111 4 14),
([w253,w1,w0,w8,w4],dL 0x408b002015,dS 0xf0a0b0705011204190e0602,pH 0x3431112221 4 12),
([w1,w2,w7,w0,w3,w126,w4],dL 0x8f04805103601a004,dS 0xd0a1307041a0e060901,pH 0x211111124121212111111 6 10),
([w10,w1,w7,w0,w3,w8,w4],dL 0x1900401a,dS 0x1b0d070a0f19021a060e130901,pH 0x112222213111111111111 3 13),
([w1,w2,w14,w0,w310,w3,w4],dL 0x9a,dS 0x1a0d241c0e0b1d07110a0915080c130601,pH 0x111111111111111111111 1 17),
([w10,w1,w14,w0,w46,w3,w4],dL 0x9a09b,dS 0xa2406150e0b010f02080d0c1a1113,pH 0x111111112111111111111 2 15),
([w10,w1,w2,w161,w0,w3,w4],dL 0x8b09b09d,dS 0x15171011340a0b0f020c060d0e,pH 0x122111112211221112211 3 13),
([w84,w10,w1,w2,w0,w3,w4],dL 0x9e09f,dS 0x34010f020c060b110e0a,pH 0x221211211121111122222 2 10),
([w10,w1,w2,w14,w7,w3,w4],dL 0x809c09b004,dS 0x1134060f0209080d1a1c0b,pH 0x312213112211221112211 4 11),
([w10,w1,w2,w0,w3,w200,w4],dL 0x9e09f,dS 0xd0834010b0f020611100e,pH 0x122221221122111221111 2 11),
([w1,w2,w7,w0,w459,w3,w4],dL 0xa409b0a3,dS 0xb161c0717110f0e090601,pH 0x111221111111111111111 3 11),
([w10,w1,w7,w0,w60,w3,w4],dL 0xa50a309e09b,dS 0x6161c0113021711090e0f,pH 0x231111113121111211111 4 11),
([w44,w10,w1,w2,w0,w3,w4],dL 0x8b0980a6,dS 0x934060f020e0a0d010b,pH 0x212121121112111112222 3 10),
([w10,w1,w2,w7,w0,w23,w3],dL 0x80a7005,dS 0x11092a0134060f02080e160b0c0d,pH 0x122321111111111111111 3 14),
([w1,w2,w0,w23,w3,w460,w4],dL 0xa8,dS 0x16290e0d1a0b09080c11102a0a190601,pH 0x111111111111111111111 1 16),
([w10,w1,w0,w23,w3,w127,w4],dL 0xa8098,dS 0x290d1a10010f020e2a160c190a0b,pH 0x111121111111111111111 2 14),
([w163,w10,w1,w2,w0,w3,w4],dL 0x9b0a9,dS 0x34060f020a01110c0d0e,pH 0x122112112111211221222 2 10),
([w10,w1,w2,w201,w0,w3,w4],dL 0x9b0ae,dS 0x1a0b093406010f020d0e1115,pH 0x122221112211221112211 2 12),
([w1,w2,w90,w0,w23,w3,w4],dL 0xb200403e04a,dS 0xd060c0f2a110b020a01,pH 0x212123111111111111111 4 10),
([w71,w1,w2,w90,w0,w3,w4],dL 0xb40270460b3,dS 0x350b060c17130f05010a,pH 0x111311112111111111111 4 10),
([w1,w19,w2,w0,w3,w156,w4],dL 0xd0550280bb03e,dS 0xc0b0d0f08060a0e0501,pH 0x311122134213321111111 5 10),
([w66,w1,w2,w0,w3,w156,w4],dL 0xbf0050be0bd,dS 0x111b060c0f0e0b2a0317010a,pH 0x311112111111111111111 4 12),
([w111,w1,w16,w2,w0,w3,w4],dL 0xc40c5,dS 0xc0e0a0b130502151009170d0f04,pH 0x122112112111211121221 2 14),
([w111,w1,w2,w0,w3,w8,w4],dL 0x170160020190c601a,dS 0x110a06151009010e13020c,pH 0x131212111216113113111 6 11),
([w27,w111,w1,w2,w0,w3,w4],dL 0x30c50ca0c90c80190c7,dS 0x12151710090e060102,pH 0x411421211211111211111 7 9),
([w37,w111,w1,w2,w0,w3,w4],dL 0x3d0cf0ce0cd0cc01a0cb,dS 0x1215100f0911130201,pH 0x411421221111111211111 7 9),
([w1,w112,w16,w2,w0,w3,w4],dL 0xd20d3,dS 0x6110e130c02040b050a01,pH 0x221211211112222111111 2 11),
([w1,w112,w2,w0,w3,w8,w4],dL 0xd60d40d50d7,dS 0x11060c1a19020e0a130501,pH 0x221241214112131331111 4 11),
([w27,w1,w112,w2,w0,w3,w4],dL 0xd90ca0d8,dS 0x1213110c0e060a0201,pH 0x221211122221111211121 3 9),
([w37,w1,w112,w2,w0,w3,w4],dL 0xdb0ce0da,dS 0x120e060c11130a0102,pH 0x221211122221111211121 3 9),
([w18,w1,w16,w0,w8,w4],dL 0xdd0e208b0150040e1,dS 0xd071215040c0f0e0619,pH 0x411221331254361 6 10),
([w18,w1,w16,w2,w7,w3,w4],dL 0xe00e50c4004,dS 0x110e1303020f0d170a040b,pH 0x412112112133211223221 4 11),
([w18,w65,w2,w0,w3,w4],dL 0xed0140ec08b0eb,dS 0x1a0d19050e150c13010a110609,pH 0x111221241315431 5 13),
([w18,w1,w2,w7,w3,w8,w4],dL 0xee01900701a0ea0c6017,dS 0x110c061a02010b0e1319030a,pH 0x331122314211111221111 7 12),
([w27,w18,w1,w2,w7,w3,w4],dL 0x8b0ee0070c90c7,dS 0x110c1239020d0e0617130a01030b,pH 0x211211211111211211133 5 14),
([w37,w18,w1,w2,w7,w3,w4],dL 0x80ee0070cd0cb,dS 0xc061239020d11130e0f0a03010b,pH 0x211211211111211211133 5 14),
([w18,w1,w19,w2,w7,w3],dL 0x8b01a00d0d00270070f60ee0f50f3,dS 0x15061a0d02010e130b050a,pH 0x141313212211111 10 11),
([w18,w1,w2,w7,w23,w3],dL 0xd00080190040fb0070050ee0fa081,dS 0x110d162a021901030e0f0b0a,pH 0x311131221211111 10 12),
([w12,w2,w21,w0,w3,w9,w4],dL 0x10108b006100,dS 0x1e3a19180601070d110216,pH 0x112441111211112111321 4 11),
([w2,w21,w0,w3,w9,w4],dL 0x10301603500210006608b,dS 0x161f3d2a3a040c100211060d0a0119,pH 0x711222145211121 7 15),
([w1,w12,w2,w0,w9,w114,w4],dL 0xd101100104,dS 0x1e19180b13020a110701160e0c,pH 0x111333222224111111111 4 13),
([w82,w1,w12,w2,w0,w9,w4],dL 0x10100f105100,dS 0x181c06021f173a0a01160c070e11,pH 0x144111111121222113331 4 14),
([w82,w1,w2,w0,w9,w4],dL 0x10102a02710000f105016,dS 0x160c072a08041f0e0f0a1c0d061101,pH 0x557442212211112 7 15),
([w1,w461,w2,w0,w3,w9,w4],dL 0x10610501602a,dS 0x161c10190b0603010d110f0a0c07,pH 0x111111111143211111112 4 14),
([w1,w12,w2,w0,w3,w206,w4],dL 0x8306110710504f101100,dS 0x1f17180b062a03070a160c0e110201,pH 0x611221111114111111111 7 15),
([w170,w1,w12,w2,w0,w3,w4],dL 0xf101108100,dS 0x1f1c0c01160e02,pH 0x122112111211211112441 4 7),
([w170,w1,w2,w0,w3,w9,w4],dL 0x1000b2105,dS 0x10190b010d0c110a1c160f07,pH 0x111111111112111131121 3 12),
([w170,w1,w2,w0,w3,w4],dL 0x4800f100083105108,dS 0xd110e0a070c161c0f0102,pH 0x315141222262142 6 11),
([w1,w158,w2,w0,w3,w9,w4],dL 0x10c10a01610b10103d10002d,dS 0xb1307161c0f02010d0c110a06,pH 0x711441222213311111111 8 13),
([w159,w1,w2,w0,w3,w9,w4],dL 0x10e10d10a083,dS 0xe023a0c1f2a110a0119060b,pH 0x221231211121111121111 4 12),
([w1,w12,w61,w0,w3,w9,w4],dL 0x8b10f00f,dS 0xb062a093a08040d07160c110f01,pH 0x113222131211112111111 3 14)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p2 : List StD := [
([w36,w1,w12,w0,w3,w9,w4],dL 0x10010800f,dS 0xe0d0b2a023a08180601160c11190a070f04,pH 0x111211111111111131111 3 18),
([w36,w1,w12,w0,w3,w4],dL 0x10800f04f107003,dS 0x1416050d0a0e0c110f07011902,pH 0x154141222211111 5 13),
([w1,w12,w2,w67,w3,w9,w4],dL 0x11000f,dS 0x1a18062a033a0804070a160c111c01,pH 0x111121111111111111111 2 15),
([w1,w12,w2,w7,w3,w9,w4],dL 0x11108308b02710110c,dS 0xe0c062a023a04071910110a0b01,pH 0x111122151212311111111 6 14),
([w1,w2,w462,w0,w3,w9,w4],dL 0x113,dS 0x16170a192a093a040d1e080c0b1c070f1101,pH 0x111111111111111111111 1 18),
([w1,w2,w197,w0,w3,w9,w4],dL 0x10a08b10d064,dS 0x1f0a023a08041c0b2a19110601,pH 0x223111311111111111111 4 13),
([w17,w1,w61,w0,w3,w9,w4],dL 0x113112,dS 0x16170b093a040a061c0711080f0d010c1e,pH 0x111111121111111111111 2 17),
([w1,w61,w0,w8,w4],dL 0x403d002015,dS 0xa0b0608010f11190e0904,pH 0x3432221111 4 11),
([w1,w2,w7,w0,w9,w8,w4],dL 0x11705100401a017,dS 0x1f0d1e0c0a062a0208041a0e19131101,pH 0x211523124111212111111 5 16),
([w37,w1,w2,w67,w0,w9,w4],dL 0x11b119,dS 0x161a0c0e0a2a031f130f06081e010d110704,pH 0x111111111111111121111 2 18),
([w37,w1,w2,w7,w0,w9,w4],dL 0x11903d01a,dS 0xd0c0a072a02081f171e131a010e0f110604,pH 0x131121111111111111111 3 18),
([w37,w1,w2,w0,w55,w9,w4],dL 0x3d11c,dS 0x160c1a1c0f02131d2a1f111001060b040a,pH 0x211111111111111111111 2 17),
([w463,w1,w2,w0,w3,w9,w4],dL 0x10f101,dS 0x161719033a1e0a06080d110c0f0107,pH 0x111111111111111111111 2 15),
([w1,w464,w2,w0,w3,w9,w4],dL 0x11d110016043,dS 0x161f1c13070d1902010b0f0c11060a,pH 0x111111111114231111112 4 15),
([w465,w1,w2,w0,w3,w9,w4],dL 0x11e0be10a,dS 0xe1c023a0c1f2a110b0f06010a,pH 0x111122122111211111111 3 13),
([w1,w61,w19,w0,w3,w9,w4],dL 0x11e08b028,dS 0xb20062a093a08041c0c0a07110f01,pH 0x112111211112111111111 3 15),
([w66,w1,w61,w0,w3,w9,w4],dL 0x1130be,dS 0x171c0d093a040c191606110f2a1f0b010a,pH 0x111111121111111111111 2 17),
([w1,w61,w2,w67,w0,w3,w4],dL 0x8b11b03603d06412010f,dS 0xf062a3a1c08040c0d1101,pH 0x411114331112111111111 7 11),
([w1,w61,w2,w0,w3,w55,w4],dL 0x8308b04812111c03d11e,dS 0xe063a080f162a040b0a1101,pH 0x213112162111311111111 7 12),
([w1,w466,w2,w0,w3,w9,w4],dL 0x1081050b210112200f,dS 0xb01160c0a110f07,pH 0x112311111334111242224 6 8),
([w1,w2,w467,w0,w3,w9,w4],dL 0x12311d12410a028125,dS 0xd1307041c010f0c11060a,pH 0x221322142111111141141 6 11),
([w36,w1,w19,w0,w3,w9,w4],dL 0x123100028,dS 0xe0b0d15023a0820130619011c110a0c070f04,pH 0x111111111111111121111 3 19),
([w36,w1,w2,w67,w0,w3,w4],dL 0x36064120108,dS 0xa0f061c111a010c0d03,pH 0x111111221211111111111 4 10),
([w36,w1,w2,w0,w3,w55,w4],dL 0x48083121123,dS 0xc0f1606110e0a010b02,pH 0x111111121111111111111 4 10),
([w36,w1,w19,w0,w3,w4],dL 0x123052028126003,dS 0xb1c070c1a05060e0a0f011302,pH 0x353131222211111 5 13),
([w36,w1,w2,w14,w0,w3,w4],dL 0x127128037,dS 0xd240e0b050806150a11020c01,pH 0x212211111112121111111 3 13),
([w36,w1,w2,w7,w0,w3,w4],dL 0x3d048036129123108018,dS 0xf06010211,pH 0x322273111134241111111 7 5),
([w36,w1,w2,w0,w23,w3,w4],dL 0x12a12804a,dS 0x290d1a10062a0c110a0b0201,pH 0x211122111112211111111 3 12),
([w19,w2,w33,w0,w3,w9,w4],dL 0x10a08b022100,dS 0x1f3a0820061d0b0113111c050a,pH 0x412111211111112311121 4 13),
([w2,w33,w0,w3,w9,w4],dL 0x10901604900210008508b,dS 0x401c1e3a081d07040c060511150b0a1301,pH 0x221271545111111 7 17),
([w160,w1,w2,w0,w3,w9,w4],dL 0x11412c101064,dS 0xc0e132a023a041e0a08060d110107,pH 0x311222111211121221111 4 15),
([w1,w19,w2,w0,w9,w115,w4],dL 0x10a02710012d,dS 0x1f0b20130d190c110206011a1c0a,pH 0x441111222213111111111 4 14),
([w91,w1,w19,w2,w0,w9,w4],dL 0x10a02810011d,dS 0xb20160f020e1e3a0c011a1c060a11,pH 0x411222121111111311331 4 15),
([w91,w1,w2,w0,w9,w4],dL 0x10a00d12e04310002811d016,dS 0xc1c062a08041e160f0b1a070a1101,pH 0x376241212211112 8 15),
([w1,w19,w2,w0,w3,w208,w4],dL 0x10a06412611d03e100,dS 0xe200d1902080b061c1a11050a01,pH 0x211121111113111111111 6 14),
([w172,w1,w19,w2,w0,w3,w4],dL 0x2810a123100,dS 0xb160e1a0a011c05,pH 0x221211111221111211441 4 8),
([w172,w1,w2,w0,w3,w9,w4],dL 0x10012411d,dS 0x1f130d010b160c110f0a1c06,pH 0x111111111112111131121 3 12),
([w172,w1,w2,w0,w3,w4],dL 0x3610006402811d123,dS 0x7060b111a0c160a1c0f0105,pH 0x313151222212652 6 12),
([w1,w19,w2,w7,w0,w3,w9],dL 0xf306408b00d10a10b,dS 0xe0a130f023a08041507110c0d01,pH 0x111221511223111111111 6 14),
([w1,w19,w2,w0,w3,w55,w9],dL 0x106028,dS 0xe200f022a3a08040c061c0a111601,pH 0x211111111111111111111 2 15),
([w1,w199,w2,w0,w3,w9,w4],dL 0x8b08310112c,dS 0x19131e0b062a023a041608071101,pH 0x114222131222111111111 4 14),
([w1,w468,w2,w0,w3,w9,w4],dL 0x113,dS 0x171c130c093a08040d161f01060b0f0a112a,pH 0x111111111111111111111 1 18),
([w78,w1,w2,w0,w3,w9,w4],dL 0x12713010012f,dS 0x160c17432a023a060a040d111c01,pH 0x111311211211132211111 4 14),
([w265,w1,w2,w0,w3,w9,w4],dL 0x10013212f,dS 0x161706033a07040c1c0a0d1101,pH 0x111211311111121111111 3 13),
([w1,w2,w469,w0,w3,w9,w4],dL 0x13308b01606c,dS 0xd161f1e0c0a13072a0208041c0b0f110106,pH 0x111111142111113111121 4 18),
([w470,w1,w2,w0,w3,w9,w4],dL 0x13410a135136,dS 0xe07023a0d0a1f0b2a111c0f0601,pH 0x111111111211121121111 4 14),
([w1,w2,w67,w7,w3,w9,w4],dL 0x110134051,dS 0x1a0b1e13062a033a08040f11071c01,pH 0x121311131111111111111 3 15),
([w1,w2,w67,w0,w3,w55,w4],dL 0x10d12c138134,dS 0xc1e0a131119062a08030701,pH 0x111222221111111111111 4 12),
([w2,w7,w0,w11,w3,w9,w4],dL 0x10a13a072101,dS 0x1f3a1e0c0a13040701110f0906,pH 0x412211111211121111111 4 13),
([w2,w0,w11,w3,w9,w4],dL 0x13d04810a07201613b10103613a,dS 0x1f2a3a1e0804060f130d0c0911010b070a,pH 0x716124131111111 9 17),
([w43,w1,w2,w0,w3,w9,w4],dL 0x13f04813e03601603d100,dS 0xc0e2a023a060f04110d010b0a,pH 0x611141111111111122111 7 13),
([w1,w2,w7,w0,w9,w62,w4],dL 0x10a14100d101140,dS 0x1e10072a02080411170f0601,pH 0x351222331111111111111 5 12),
([w44,w1,w2,w7,w0,w9,w4],dL 0x10a142101133051,dS 0xc0a072a02081f0e1e3a06170f110113,pH 0x533131111121221111111 5 16),
([w44,w1,w2,w0,w9,w4],dL 0x10a10106c113133016,dS 0x161c072a08041f1e0d0f0b0c170a111301,pH 0x615111212211112 6 17),
([w1,w2,w7,w0,w3,w179,w4],dL 0x144133143101004,dS 0xe0c0a130702040f1711090601,pH 0x311211141111111111111 5 13),
([w96,w1,w2,w7,w0,w3,w4],dL 0x51145101,dS 0x111c130e1706010f09,pH 0x111211111111111313311 3 9),
([w96,w1,w2,w0,w3,w9,w4],dL 0x101146133,dS 0x13072a080a160d11010b1c060f,pH 0x111111111112111231111 3 13),
([w96,w1,w2,w0,w3,w4],dL 0x3002051101147145133,dS 0x16131107040b060d1c0f0109,pH 0x312352111121461 7 12),
([w1,w2,w7,w0,w3,w55,w9],dL 0x106138051,dS 0xe1f0d1e0a191307022a3a08040f11061601,pH 0x311111111111111111111 3 18),
([w92,w1,w2,w0,w3,w9,w4],dL 0x12a100016148,dS 0xe1c2a0d110616040a010b,pH 0x111111311312113111111 4 11),
([w266,w1,w2,w0,w3,w9,w4],dL 0x10014a148,dS 0xe1c1d023a061604110b0a01,pH 0x121211211121111111111 3 12),
([w471,w1,w2,w0,w3,w9,w4],dL 0x101138,dS 0x160d1f0e132a023a041e0b06080f110107,pH 0x111222111211121221111 2 17),
([w1,w2,w194,w7,w0,w3,w4],dL 0x4800d01903614c14b018,dS 0x604031913110209,pH 0x522253111111111111111 7 8),
([w1,w12,w2,w472,w0,w3,w4],dL 0x152,dS 0x1018190b130d0a070916020c0e1103,pH 0x111111111111111111111 1 15)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p3 : List StD := [
([w41,w1,w12,w2,w0,w114,w4],dL 0x152153,dS 0x190718160b1303170102100a0c0e0d,pH 0x111111121111111111111 2 15),
([w41,w1,w158,w2,w0,w3,w4],dL 0x8155153,dS 0x161c0f0c3811020e01130d0a0b,pH 0x211111111112111211111 3 13),
([w159,w41,w1,w2,w0,w3,w4],dL 0x156157,dS 0x3811020e010c0a060b19,pH 0x221211211121111122222 2 10),
([w41,w1,w12,w2,w7,w3,w4],dL 0x8b15415800d,dS 0x38110e010907020d10190b,pH 0x112312223111212112121 4 11),
([w41,w1,w2,w197,w0,w3,w4],dL 0x15615d,dS 0xd38110e01020b131c06,pH 0x221122211221121211211 2 10),
([w41,w1,w2,w7,w0,w8,w4],dL 0x1a01900d,dS 0x1f0d0a03170e1a011911130902,pH 0x211121111321122112111 3 13),
([w1,w19,w2,w473,w0,w3,w4],dL 0x160,dS 0xb1e1520130d19090c061c0a051a1102,pH 0x111111111111111111111 1 16),
([w160,w41,w1,w2,w0,w3,w4],dL 0x158162,dS 0x3811020e010a0c130d06,pH 0x122112112111211221222 2 10),
([w41,w1,w19,w2,w0,w115,w4],dL 0x160153,dS 0x200d1c19020e011305150c0a1a0b,pH 0x111111121111111111111 2 14),
([w41,w1,w19,w2,w7,w0,w3],dL 0x8b027156155,dS 0x7381109060e01050b15130d,pH 0x323112221311212132121 4 12),
([w41,w1,w199,w2,w0,w3,w4],dL 0x158166,dS 0x190b053811020e010d130616,pH 0x122112221211212112121 2 12),
([w1,w2,w7,w0,w474,w3,w4],dL 0x168167158,dS 0xb15101307030f1102061709,pH 0x121112112111111111111 3 12),
([w43,w41,w1,w2,w0,w3,w4],dL 0x8169153,dS 0x538110e0106020a0d0b,pH 0x211111121121111211111 3 10),
([w41,w1,w2,w7,w0,w62,w4],dL 0x16a167156158,dS 0x1e1510020e010f17130906,pH 0x311131211121111211111 4 11),
([w1,w2,w157,w14,w0,w3,w4],dL 0x506116e037,dS 0xd0e0b060508110a0f0c0201,pH 0x212411111111111111111 4 12),
([w45,w1,w2,w157,w0,w3,w4],dL 0x16e00d04216f,dS 0xd0b37060e0a190f020c01,pH 0x111113211111111111111 4 11),
([w113,w1,w16,w2,w0,w3,w4],dL 0xc4175,dS 0x6110e1305040a0d02010c,pH 0x122112112111211221221 2 11),
([w113,w1,w2,w0,w3,w8,w4],dL 0x1781760c6177,dS 0x11060e0a131a19020c01,pH 0x311222113234321321111 4 10),
([w27,w113,w1,w2,w0,w3,w4],dL 0x17a0c7179,dS 0x1213110a0e060c0201,pH 0x122112112122121112112 3 9),
([w37,w113,w1,w2,w0,w3,w4],dL 0x17c0cb17b,dS 0x120e060a11130c0102,pH 0x122112112122121112112 3 9),
([w1,w12,w2,w0,w3,w195,w4],dL 0x2705806100f,dS 0xd19170b062a0a0c070201,pH 0x332111211241111111111 4 11),
([w17,w1,w2,w0,w3,w195,w4],dL 0x18000411217f,dS 0xe0d0b36070a061a080217010c,pH 0x121131111111111111111 4 13),
([w39,w1,w12,w2,w7,w3],dL 0x8b01a02717300d18a023189188111,dS 0x10070b050e0117190d020a,pH 0x111313212211111 10 11),
([w39,w1,w16,w0,w8,w4],dL 0x18619400519308b,dS 0xb071210040f0a190e06,pH 0x221233214311452 5 10),
([w39,w1,w16,w2,w7,w0,w3],dL 0x50d20c5,dS 0x110e1302480c050f0b17040d,pH 0x123132132111211221221 3 12),
([w65,w39,w2,w0,w3,w4],dL 0x18b19c19b08b,dS 0x1a10190e020b130c0a09110106,pH 0x223211131121142 4 13),
([w39,w1,w2,w7,w0,w3,w8],dL 0x18901902301a0d5199017,dS 0x110a060e051a191301020d0c,pH 0x122331142311111311111 7 12),
([w27,w39,w1,w2,w7,w0,w3],dL 0x8b1890230c80ca,dS 0x110a1248050e0b0617190c02010d,pH 0x211121121111211121133 5 14),
([w37,w39,w1,w2,w7,w0,w3],dL 0x81890230cc0ce,dS 0xa12074805110b131a0f0c02010d,pH 0x211121121111211121133 5 14),
([w39,w1,w2,w14,w7,w3],dL 0x80191730051a20230041891a106f,dS 0x111c0b08051301021a0f0d0a,pH 0x131113212211111 10 12),
([w1,w2,w21,w0,w3,w114,w4],dL 0xd034104,dS 0x1118010d0e02100a0c0719,pH 0x221122111111111111111 3 11),
([w82,w1,w2,w21,w0,w3,w4],dL 0x34035105,dS 0xe011110020c0d0a1906,pH 0x221121111111111113111 3 10),
([w144,w1,w12,w2,w0,w3,w4],dL 0xf1a700e,dS 0x18160b060e07010d0a0c02,pH 0x313111111122222112221 3 11),
([w1,w2,w169,w21,w0,w3,w4],dL 0x1a603603400203502a,dS 0x100e03170d0c0a021906,pH 0x221121611411113111131 6 10),
([w1,w2,w21,w0,w3,w206,w4],dL 0x1a603603510704f034,dS 0x170e0102100d0c110a0619,pH 0x111221141112111111111 6 11),
([w144,w1,w2,w21,w0,w3,w4],dL 0x3500e0341a7,dS 0x17070e19020d0c0a06,pH 0x212121111111131111411 4 9),
([w269,w1,w2,w21,w0,w3,w4],dL 0x34035,dS 0xe020317110c100a0d1906,pH 0x111111111111111112211 2 11),
([w1,w2,w475,w21,w0,w3,w4],dL 0x3a1a6,dS 0x150d170c1f1d0e01110a10020619,pH 0x111111111111111111111 2 14),
([w270,w1,w2,w21,w0,w3,w4],dL 0x3a005,dS 0xc02110d170e100a0619,pH 0x111111111111111111111 2 10),
([w1,w2,w21,w7,w3,w4],dL 0x16708b01a0a31a6036188,dS 0xc170d0b10190a021106,pH 0x322372452111141 7 10),
([w1,w2,w21,w0,w23,w3,w4],dL 0x3d03a0351a61a8,dS 0xd02010c11100a1906,pH 0x412311433111111111111 5 9),
([w71,w1,w2,w21,w0,w3,w4],dL 0x3a0271a60341a9,dS 0x1511010c170d1d020a06,pH 0x332421321111111112211 5 10),
([w1,w2,w311,w0,w3,w4],dL 0x501603600202a,dS 0x100d190a11060c0f,pH 0x433511222111121 5 8),
([w2,w311,w0,w3,w4],dL 0x5016036002,dS 0xd170a19070c11100f06,pH 0x3224321111 4 10),
([w476,w1,w2,w0,w3],dL 0x16036002048,dS 0x110a0f0e0b060d0c,pH 0x3224321111 4 8),
([w267,w1,w12,w2,w0,w3,w4],dL 0xa9104,dS 0x18160e0b0301100d19110a0c07,pH 0x111111111211111111111 2 13),
([w1,w205,w12,w2,w0,w3,w4],dL 0x1070341011ae100105,dS 0x1f1c0a07020e0c110116,pH 0x144224221311551111111 6 10),
([w1,w205,w2,w0,w3,w4],dL 0x1000271ae1b0016105,dS 0x101907060f2a08010d0c160a04,pH 0x242523513611111 6 13),
([w1,w2,w95,w0,w3,w4],dL 0x3d01604803600202d,dS 0xb0e0d0c11060a13,pH 0x433151222111121 6 8),
([w2,w95,w0,w3,w4],dL 0x48036002,dS 0x111020e19070d0c0b130a06,pH 0x3223121111 3 12),
([w1,w2,w0,w477,w4],dL 0x4803d036002,dS 0x110e0b130d0c0a06,pH 0x3221114321 4 8),
([w478,w1,w2,w0,w4],dL 0x48036002016,dS 0xd0c0b170a0f060e11,pH 0x3224321111 4 9),
([w1,w12,w60,w3,w4],dL 0x1bb1111ba03608b,dS 0xd16060510070f0b0201,pH 0x4112221113 5 10),
([w1,w12,w2,w7,w23,w3],dL 0x1851bc1be0fc111081,dS 0x2a16110d10070b0e19020a01,pH 0x211121111112111 6 12),
([w1,w12,w2,w0,w3,w35,w4],dL 0x10d0031bf0831a8,dS 0x180b0601160e0a2a0c1107,pH 0x121251122212111111111 5 11),
([w1,w2,w0,w3,w272,w4],dL 0xd0011c0005,dS 0x5110c0e160a1002071901,pH 0x111222121213111 4 11),
([w1,w164,w12,w2,w0,w3,w4],dL 0x610341a91c1,dS 0xd0b060a011107050c,pH 0x313134131122333222221 4 9),
([w1,w83,w2,w0,w23,w3,w4],dL 0x3e1c212109d,dS 0xe0d0109190a0b0608,pH 0x414111222122233333111 4 9),
([w71,w1,w83,w2,w0,w3,w4],dL 0x1c40ac,dS 0x350d0e010c1719060b09080a,pH 0x111111111111121112111 2 12),
([w1,w2,w479,w0,w3,w4],dL 0x271cc08b1cd016,dS 0xb0c0a1c072a041511060f01,pH 0x121532312344441 5 12),
([w17,w1,w2,w0,w3,w35,w4],dL 0x10d0041bf1211c2,dS 0x1c11010a060b070e2a1e0c,pH 0x151343222311111221111 5 11),
([w17,w1,w164,w2,w0,w3,w4],dL 0x15b1d10ac,dS 0xb3607010a061109050c,pH 0x322121112211131111111 3 10),
([w1,w16,w57,w0,w8,w4],dL 0x1d51d400500408b002015,dS 0x15100d430b0c06040a,pH 0x343514222111121 7 9),
([w1,w57,w0,w8,w4],dL 0x21d41d508b015,dS 0xb0d070e1519100c040a06,pH 0x2423141111 5 11)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p4 : List StD := [
([w1,w2,w274,w57,w0,w3,w4],dL 0x361cd,dS 0x151e0a07010d0c110406170f,pH 0x111111111111111111111 2 12),
([w275,w1,w2,w57,w0,w3,w4],dL 0x36004,dS 0xa0b070410150c1706110f,pH 0x111111111111111111111 2 11),
([w1,w2,w276,w57,w0,w3,w4],dL 0x481d3,dS 0x100c1f1d01110617040f0b0a,pH 0x111111111111111111111 2 12),
([w277,w1,w2,w57,w0,w3,w4],dL 0x48005,dS 0xb0704151711100a060f,pH 0x111111111111111111111 2 10),
([w1,w2,w57,w7,w0,w3,w4],dL 0x480361d31cd0e5,dS 0x1707010f040611,pH 0x322213312431211111111 5 7),
([w1,w16,w0,w8,w4],dL 0xe1003002015,dS 0xf0a0b0612020107190e0904,pH 0x3432221111 4 12),
([w1,w2,w312,w0,w3,w4],dL 0x48016004002043,dS 0x150b0e070c06110a0f,pH 0x433113222111121 5 9),
([w2,w312,w0,w3,w4],dL 0x48016004002,dS 0xc0e111307150a0b0f06,pH 0x3224321111 4 10),
([w480,w1,w2,w3,w4],dL 0x48016002036,dS 0xc11060d0e0f0b0a,pH 0x3224321111 4 8),
([w73,w1,w2,w0,w3,w4],dL 0x500400208b,dS 0xb0201150c100a04,pH 0x433111111141311 4 8),
([w73,w1,w2,w0,w4],dL 0x500400208b,dS 0xb150c100a120401,pH 0x3111114311 4 8),
([w73,w1,w0,w3,w4],dL 0x8b02700d008,dS 0xb150c100a0104,pH 0x1211113124 4 7),
([w73,w1,w16,w0,w8,w4],dL 0x1df00500408b,dS 0xd091510010b0c0a04,pH 0x121212111131214 4 9),
([w73,w1,w16,w0,w4],dL 0x31e0005004002,dS 0xd06010b43150c100a04,pH 0x2113243214 5 10),
([w73,w1,w0,w8,w4],dL 0x21df1e21e108b,dS 0x120b0d150e0c10190114090a04,pH 0x1211113124 5 13),
([w1,w16,w72,w0,w8,w4],dL 0x9a1e30040e108b,dS 0x70d1514040c09020e1901,pH 0x121421312511111 5 11),
([w1,w16,w7,w0,w8,w4],dL 0x180e3193004,dS 0x70f12190409060e01,pH 0x211142111133131 4 9),
([w1,w16,w0,w103,w8,w4],dL 0xa81e800519308b,dS 0x71012190902040b050a0e01,pH 0x112214215111111 5 12),
([w1,w16,w2,w0,w11,w3,w4],dL 0x3d00313b0750e5,dS 0xe130c01110d06090b0a,pH 0x313111222121211111111 5 10),
([w1,w2,w7,w0,w85,w3,w4],dL 0xa30e7197,dS 0x7170f0902110601,pH 0x111121213111111111111 3 8),
([w1,w2,w0,w85,w3,w4],dL 0x10a300d0041970e7,dS 0x70d0417020f0b061101,pH 0x234111235121611 6 10),
([w65,w1,w2,w7,w0,w3,w4],dL 0x1904803619b0eb01a,dS 0x70901131106,pH 0x322263312111111114411 6 6),
([w1,w2,w280,w0,w3,w8,w4],dL 0x1ef1ee00201a,dS 0xd111510060b0e090c13020a01,pH 0x111111142111111111111 4 13),
([w281,w1,w2,w0,w3,w8,w4],dL 0x1f00d51f1031,dS 0x1106090c1a0e0b1913050a01,pH 0x111111111211121121111 4 12),
([w1,w2,w72,w7,w3,w8,w4],dL 0x510e81f0018,dS 0x110b1a070e1309020a1901,pH 0x121314131111111111111 4 11),
([w1,w2,w72,w0,w3,w103,w4],dL 0xd71771f21f0,dS 0xd0e0b11190513020701,pH 0x111222221111111111111 4 10),
([w1,w2,w0,w481,w3,w4],dL 0x1f404f1f303e04e036,dS 0x1a11190a0d02060c0813,pH 0x335112324122121 6 10),
([w1,w2,w0,w11,w3,w8,w4],dL 0x1600201901701a,dS 0x1106010e0b130c090a,pH 0x131213111211111221111 5 9),
([w1,w7,w0,w60,w3,w8,w4],dL 0xd500d1f60040c6,dS 0x1a1c130f0e0901,pH 0x512214111121121111111 5 7),
([w43,w1,w7,w0,w3,w8,w4],dL 0xd50180c6004,dS 0x1a0a060f131902090e01,pH 0x411111121111111311331 4 10),
([w43,w1,w0,w3,w8,w4],dL 0xd50c6169002,dS 0x61a0919020f0c0d0a0b0e1301,pH 0x411131111211111 4 13),
([w1,w2,w7,w0,w8,w62,w4],dL 0xd51f800d0040c6,dS 0x100e06191709021301,pH 0x352121331112111111111 5 9),
([w44,w1,w2,w7,w0,w8,w4],dL 0xd50c605100d,dS 0xa111a17190e09130102,pH 0x411131111111111112211 4 10),
([w44,w1,w2,w0,w8,w4],dL 0xd50c60a6016,dS 0x1119091a17010c0d0a0b130e02,pH 0x413111112111111 4 13),
([w1,w2,w7,w0,w3,w482,w4],dL 0x721f90c61ef,dS 0x111a1510061917090e0f021301,pH 0x111211111111111141111 4 13),
([w104,w1,w2,w7,w0,w3,w4],dL 0x181ef0c6,dS 0xe0a02111713010f09,pH 0x111211111111111313311 3 9),
([w104,w1,w2,w0,w3,w8,w4],dL 0xc61ee002018,dS 0x1a170f0b0c0e13010a09,pH 0x111111111111111142121 4 10),
([w104,w1,w2,w0,w3,w4],dL 0x1690c60510a61ef01a,dS 0x20e13010c170f090b0a,pH 0x422112112116111 6 10),
([w1,w2,w7,w0,w3,w103,w8],dL 0x1981f2051018,dS 0x110d0a06050e1a130919020c01,pH 0x411112112111111111111 4 13),
([w282,w1,w2,w0,w3,w8,w4],dL 0x5f0c61f2,dS 0xc11060a090e1a13021901,pH 0x311222113213123321111 3 11),
([w1,w2,w0,w3,w483,w4],dL 0x1fc1fb053052061,dS 0xc1105060e2a130a0b,pH 0x112111123111111 5 9),
([w1,w135,w2,w7,w0,w3,w4],dL 0x8b0480360041ff1fe01905b,dS 0x170705030102061311,pH 0x433324423821221111111 8 9),
([w1,w2,w7,w0,w138,w3,w4],dL 0xa30c7207,dS 0xb161c191109170f021301,pH 0x132111113111111111111 3 11),
([w1,w2,w0,w138,w3,w4],dL 0xc7209019208004,dS 0x1c0d1719110b020f01,pH 0x313111111131311 5 9),
([w27,w1,w2,w0,w11,w3,w4],dL 0x1600304803607520a20b01905b,dS 0x120c010e06130b11090a,pH 0x312321328411111212411 9 10),
([w27,w1,w7,w0,w60,w3,w4],dL 0x20c0a30ca0c7,dS 0x1113161c0d0e06090f011702,pH 0x231111113121111211111 4 12),
([w27,w1,w0,w60,w3,w4],dL 0x2090ca0c700408b,dS 0x170d05061119161c0b020f01,pH 0x121221111121131 5 12),
([w1,w198,w2,w7,w0,w3,w4],dL 0x804800d03601a20e1ae129,dS 0x72a08020f060111,pH 0x322283342141441111111 8 8),
([w1,w2,w7,w0,w143,w3,w4],dL 0x180cb214,dS 0xb1510120709170e0f020601,pH 0x132111113111111111111 3 12),
([w1,w2,w0,w143,w3,w4],dL 0xcb1f721521400d01a,dS 0x171a12100e0f0b020601,pH 0x222333111311131 6 10),
([w37,w1,w2,w0,w11,w3,w4],dL 0x3d00204803613b21621701a129,dS 0x120c0111130e0b09060a,pH 0x319341322211111212411 9 10),
([w37,w1,w2,w7,w0,w62,w4],dL 0x2181670ce0cb,dS 0xe1510060d11130917010f02,pH 0x311131211121111211111 4 12),
([w37,w1,w2,w0,w62,w4],dL 0x1f70ce0cb00d008,dS 0x1a0f0d0e05110615100b170102,pH 0x221112111121311 5 13),
([w1,w2,w33,w0,w3,w115,w4],dL 0x2704712d,dS 0xe201a010b0506130c0a,pH 0x221122111111111111111 3 10),
([w91,w1,w2,w33,w0,w3,w4],dL 0x4704911d,dS 0x1a1d010e1513050c0a0b06,pH 0x122121111111111311111 3 11),
([w128,w1,w19,w2,w0,w3,w4],dL 0x2821a00e,dS 0x200d1c191106010c0b0a05,pH 0x313111111122222211221 3 11),
([w1,w2,w484,w33,w0,w3,w4],dL 0x3b219,dS 0x100b1e0a1d07010e0c1511050613,pH 0x211111111111111111111 2 14),
([w287,w1,w2,w33,w0,w3,w4],dL 0x3b004,dS 0xa1d07050b150c060e1113,pH 0x211111111111111111111 2 11),
([w1,w2,w171,w33,w0,w3,w4],dL 0x4821904700204912b,dS 0x150e111d07020b0c05060a13,pH 0x122121115411113111131 6 12),
([w1,w2,w33,w0,w3,w208,w4],dL 0x48219049126047052,dS 0xe151a010c1105060b0a13,pH 0x111122242111111111111 6 11),
([w128,w1,w2,w33,w0,w3,w4],dL 0x4900e04721a,dS 0xe1d1311050c0b060a,pH 0x212121111111131111411 4 9),
([w289,w1,w2,w33,w0,w3,w4],dL 0x47049,dS 0x1d1a05020e11150c0a13060b,pH 0x111111111111111211211 2 12),
([w1,w2,w33,w14,w0,w3,w4],dL 0x3d04921903b21b,dS 0x150b1d0701050c110a0613,pH 0x232131142211111111111 5 11),
([w45,w1,w2,w33,w0,w3,w4],dL 0x3b00d21904721c,dS 0x101d11010e0a060b050c07,pH 0x233124123111111211211 5 11)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p5 : List StD := [
([w1,w2,w33,w7,w0,w3],dL 0x16708b01a0a32190480f5,dS 0xa0e070d0b15130c060511,pH 0x322732542111141 7 11),
([w286,w1,w19,w2,w0,w3,w4],dL 0x21e12d,dS 0x200d1a1c020e011115130c0b060a,pH 0x111111111211111111111 2 14),
([w1,w207,w19,w2,w0,w3,w4],dL 0x12604710a20e10011d,dS 0xb160c1106021a011c0a,pH 0x441422122351151111111 6 10),
([w1,w207,w2,w0,w3,w4],dL 0x10020e00d22101611d,dS 0x11130f2a08010b0c0a1c0604,pH 0x242324314611111 6 12),
([w1,w19,w2,w0,w34,w3,w4],dL 0x322312c21b064,dS 0x200d0f011a1c0c1106080a,pH 0x332112111111111221222 5 11),
([w1,w2,w0,w292,w3,w4],dL 0x3e0f309a001004224,dS 0x7111a050c0a1c0206151301,pH 0x112112114111311 6 12),
([w1,w19,w2,w14,w7,w3],dL 0xf22272261a00f306f,dS 0x81c11150b060d1a13050a01,pH 0x121112111111211 6 12),
([w1,w162,w19,w2,w0,w3,w4],dL 0x3e04721c155,dS 0xb0d0f0c011106020a,pH 0x313431131132233222221 4 9),
([w1,w19,w0,w60,w3],dL 0x2290f322804808b,dS 0x130b1c061902070d0f0501,pH 0x1412221113 5 11),
([w1,w137,w2,w14,w0,w3,w4],dL 0x6122b12022c,dS 0xd0e0b0a13011106090c,pH 0x114111222232223333311 4 10),
([w45,w1,w137,w2,w0,w3,w4],dL 0x22d0a1,dS 0x370b11010e0a13060d092a0c,pH 0x111111111111121211111 2 12),
([w1,w2,w485,w0,w3,w4],dL 0xd23108b1d3016,dS 0xb0c160a0708041011060f01,pH 0x121235213344441 5 12),
([w66,w1,w2,w0,w34,w3,w4],dL 0x12c00522312022b,dS 0x161e010c0f0d061c080a1f,pH 0x341311322211111122111 5 11),
([w66,w1,w162,w2,w0,w3,w4],dL 0x2331640a1,dS 0xb1b06010c0f1109020a,pH 0x312131311311121111111 3 10),
([w1,w2,w0,w34,w46,w3,w4],dL 0x4120068,dS 0x240601130d1c0a08110c,pH 0x122111112122111111111 3 10),
([w78,w1,w2,w0,w34,w3,w4],dL 0x12006402b,dS 0x1301061c080c1a0d110a,pH 0x111221222111111131111 3 10),
([w139,w1,w2,w14,w0,w3,w4],dL 0x37235236,dS 0x24150e0b060a0d0802110c,pH 0x111111331122222122211 3 11),
([w1,w165,w2,w0,w34,w3,w4],dL 0x223119120036064065,dS 0x1c06011a0f0d0c110a08,pH 0x111221222161431111113 6 10),
([w1,w2,w0,w34,w177,w3,w4],dL 0x22305a064036237120,dS 0xf0211130d0c1a0a1c0608,pH 0x112114221111111111111 6 11),
([w293,w1,w2,w0,w34,w3,w4],dL 0x120064,dS 0x113080f060c1a111c0d0a,pH 0x112111111111111122111 2 11),
([w139,w1,w2,w0,w34,w3,w4],dL 0x236120064235,dS 0x1e0f1c0611080d0a0c,pH 0x111111333111411112111 4 9),
([w1,w2,w7,w34,w3,w4],dL 0x80a3019167223238036,dS 0xc131a0d0b1c06080f110a,pH 0x432111316122122 7 11),
([w1,w2,w0,w486,w34,w3,w4],dL 0x12c223,dS 0xc1f160d1e1d010f110a1a1c0608,pH 0x111111111111111111111 2 14),
([w294,w1,w2,w0,w34,w3,w4],dL 0x12c03e,dS 0xc1e080d0a0f1a111c06,pH 0x111111111111111111111 2 10),
([w209,w1,w2,w14,w0,w3,w4],dL 0x162068,dS 0x24150b01021a1c0d13110a0c06,pH 0x111121111111111111111 2 13),
([w1,w210,w2,w14,w0,w3,w4],dL 0x5a00a1201fe04102b,dS 0x101d1103010c02061513,pH 0x522231152214411111111 6 10),
([w1,w210,w2,w0,w3,w4],dL 0x12004123a00a0051fe00202b,dS 0x1a0711170a0504030d0c151002,pH 0x431222457111111 8 13),
([w1,w2,w0,w94,w3,w4],dL 0x300204801603606c,dS 0xe0d0b0c11060f0a,pH 0x311221435211211 6 8),
([w2,w0,w94,w3,w4],dL 0x48016036,dS 0x6020f010c110e0d0a0b,pH 0x2321113211 3 10),
([w1,w0,w487,w3,w4],dL 0x48016003036,dS 0xc0e060d110f0b0a,pH 0x3221114321 4 8),
([w488,w1,w0,w3,w4],dL 0x48016036002,dS 0xc0e1113070d0b0a0f06,pH 0x3224321111 4 10),
([w1,w2,w14,w62,w4],dL 0x6f243244036008,dS 0x110e0d151a0a1005080b0201,pH 0x1215121114 5 12),
([w1,w2,w489,w0,w3,w4],dL 0x4c0050081cd248002,dS 0xb15170a1005040c071a0f03,pH 0x433543111222212 6 12),
([w1,w2,w0,w11,w60,w3,w4],dL 0x24c00401a048077036,dS 0x170c0a0e0b110f09,pH 0x364212111134121222111 6 8),
([w43,w1,w2,w0,w11,w3,w4],dL 0x1a07502e,dS 0xf0106090d0c0e110b0a,pH 0x111111222111111311111 3 10),
([w141,w1,w2,w7,w0,w3,w4],dL 0x25001824f24e236,dS 0xc0a191306170e110209,pH 0x311111341122222212211 5 10),
([w1,w2,w0,w11,w3,w62,w4],dL 0x1900d252048140036,dS 0xc0a130b170f0609,pH 0x431222111131111221111 6 8),
([w44,w1,w2,w0,w11,w3,w4],dL 0x1913b133,dS 0x17010e090d0c130b060a,pH 0x212111111111111311111 3 10),
([w145,w1,w2,w7,w0,w3,w4],dL 0x256051255253254,dS 0x1a0e0c0a110f01061309,pH 0x311111311122222212211 5 10),
([w1,w166,w2,w0,w11,w3,w4],dL 0x25801a036075257,dS 0x6010d0e130c0b11090a,pH 0x111111222111431111113 5 10),
([w1,w2,w0,w11,w178,w3,w4],dL 0x7525a25901a,dS 0x130c0d020e0f110a0b0609,pH 0x221114212111111111111 4 11),
([w298,w1,w2,w0,w11,w3,w4],dL 0x1a075,dS 0x10f0913060c0d0e110b0a,pH 0x121111111111111212111 2 11),
([w141,w1,w2,w0,w11,w3,w4],dL 0x23601a07524e,dS 0x1713060c0b0e09110a,pH 0x111111333111411112111 4 9),
([w1,w2,w0,w173,w11,w3,w4],dL 0x25c01903613b25b,dS 0xd0e110c02130f0b0a0609,pH 0x212114111311111111311 5 11),
([w1,w2,w0,w11,w3,w179,w4],dL 0x13b01925d144,dS 0xe0c0d1701130f110a090b06,pH 0x111143111111111111111 4 12),
([w145,w1,w2,w0,w11,w3,w4],dL 0x1925413b253,dS 0xe0f07110b0c0906130a,pH 0x414111111111311112111 4 10),
([w300,w1,w2,w0,w11,w3,w4],dL 0x13b019,dS 0x1709020e110c0d13060b0a,pH 0x212111111111111111111 2 11),
([w295,w1,w2,w7,w0,w3,w4],dL 0xc509e25f07709b,dS 0xa2a0d0b02170e110f06,pH 0x411511411122222511211 5 10),
([w1,w2,w0,w60,w3,w62,w4],dL 0x3d00d048003261004036,dS 0x1615100b05170f0201,pH 0x351326111152111111111 7 9),
([w44,w1,w2,w0,w60,w3,w4],dL 0x209048003004036,dS 0xc0a050d0e0b161c170f0102,pH 0x455111411111111213231 5 12),
([w301,w1,w2,w7,w0,w3,w4],dL 0x2622070ca0510c7,dS 0x1f1e15100e0913010f02,pH 0x211111321132111411111 5 10),
([w1,w175,w2,w7,w0,w3,w4],dL 0x3201a26426304102e,dS 0xe050301170611020f,pH 0x622324612251511111111 6 9),
([w1,w2,w7,w0,w3,w302,w4],dL 0xd52661ef0c6051,dS 0x1a110c0a190e09020f1301,pH 0x111222111111111111111 5 11),
([w43,w1,w2,w0,w3,w62,w4],dL 0x4803d00d0361f7,dS 0xc0515060f0d0b10170201,pH 0x152111111111111344111 5 11),
([w43,w44,w1,w2,w0,w3,w4],dL 0x1ef0a6169,dS 0x50e0601020d0b0a,pH 0x111221111221121121122 3 8),
([w1,w175,w2,w0,w3,w4],dL 0x3203d01604126426300202e,dS 0x170504030c150e0a100702,pH 0x413222865111111 8 11),
([w296,w1,w2,w7,w0,w3,w4],dL 0xcf156269140158,dS 0xa1305110d0b01170f06,pH 0x411521411122222521211 5 10),
([w303,w1,w2,w7,w0,w3,w4],dL 0x26b2140ce0180cb,dS 0x15101b12110f0609170102,pH 0x311111222231112212211 5 11),
([w1,w2,w0,w23,w62],dL 0x16708126c04826d008,dS 0x1a110e0c0d150b2a100201,pH 0x1121651114 6 11),
([w1,w176,w2,w7,w0,w3,w4],dL 0x10a01926f26e133101,dS 0x1713062a080402110f01,pH 0x611314611152521222211 6 10),
([w1,w2,w304,w7,w0,w3,w4],dL 0x2700d51ef0180c6,dS 0xc0a06191309021701,pH 0x411111211212121111111 5 9),
([w1,w176,w2,w0,w3,w4],dL 0x10a10100300226f26e016133,dS 0x13060f2a08010c160a1c1104,pH 0x212423817511111 8 12),
([w1,w2,w7,w0,w3,w35],dL 0xa30080191671bf0fa048,dS 0xa130e070d0b16060c2a0f11,pH 0x233111713112222 7 12),
([w1,w2,w0,w3,w35,w127,w4],dL 0x5121086,dS 0x29060119110e0c0b2a0a,pH 0x211121121121111111111 3 10)]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p6 : List StD := [
([w92,w1,w2,w0,w3,w35,w4],dL 0x121083044,dS 0x190106160e2a0c110b0a,pH 0x121211121111111311111 3 10),
([w142,w1,w2,w0,w23,w3,w4],dL 0x4a273128,dS 0x290d1a100611020c0a0b2a,pH 0x111111311122222222111 3 11),
([w1,w168,w2,w0,w3,w35,w4],dL 0x481211bf016083084,dS 0x130e06010f0c110b2a0a,pH 0x121211121115341111113 6 10),
([w1,w2,w0,w3,w35,w215,w4],dL 0x4808305c1bf274121,dS 0xf16020c110e0a0b0619,pH 0x215221111111111111111 6 10),
([w308,w1,w2,w0,w3,w35,w4],dL 0x121083,dS 0x1060f190e160c110a0b,pH 0x112111111111111221111 2 10),
([w142,w1,w2,w0,w3,w35,w4],dL 0x121083128273,dS 0x1f0f0e062a0c110b0a,pH 0x111111441112111131111 4 9),
([w1,w2,w490,w0,w3,w35,w4],dL 0x10d1bf,dS 0x1c0b1e0a07010c16112a060e0f,pH 0x122111111111111111111 2 13),
([w305,w1,w2,w0,w3,w35,w4],dL 0x10d00d,dS 0x70a0b10160c110f060e,pH 0x112111111111111111111 2 10),
([w306,w1,w2,w0,w23,w3,w4],dL 0x157086,dS 0x290d1001160e020c110b0a1906,pH 0x112111111111111111111 2 13),
([w1,w214,w2,w0,w23,w3,w4],dL 0x5c1210321ff00a044,dS 0x150a0c11020103100619,pH 0x413422422155111111111 6 10),
([w1,w214,w2,w0,w3,w4],dL 0x12100a2761ff004002044,dS 0x6170504030b0c150e0a1002,pH 0x433222763111111 7 12),
([w1,w2,w491,w0,w3,w4],dL 0x4c0080041d327c002,dS 0xb0c15171004030a070e0f02,pH 0x334354111222212 6 12)]
noncomputable def p13_D6 : List StD := p13_D6p0 ++ p13_D6p1 ++ p13_D6p2 ++ p13_D6p3 ++ p13_D6p4 ++ p13_D6p5 ++ p13_D6p6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x1 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x2 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x3 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x4 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (4*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x5 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (5*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x6 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (6*64)).take 64) = true := by decide +kernel
theorem p13_I6 : LevelN p13_R p13_T 6 p13_D6 := levelStep p13_B p13_W p13_Q p13_I5 (chunks 64 p13_D6 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  · exact p13_C6x1
  · exact p13_C6x2
  · exact p13_C6x3
  · exact p13_C6x4
  · exact p13_C6x5
  · exact p13_C6x6
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D7p0 : List StD := [
([w10,w2,w6,w0,w3,w4],dL 0x5004001003002,dS 0xd0c0807060504030b0a090102,pH 0x544222111311133 5 13),
([w1,w12,w2,w6,w0,w3,w4],dL 0xd00c008007005006003002,dS 0xd0a111706050415100e031602,pH 0x441223111311211333133 8 13),
([w1,w16,w2,w6,w0,w3,w4],dL 0x13012008005004003011002,dS 0xc0a151710050d0b0204,pH 0x544324111211161222122 8 10),
([w1,w6,w0,w3,w8,w4],dL 0x1b01c008014003,dS 0xc110a0b0d07050403010e1a13190206,pH 0x133513121122222 5 16),
([w27,w1,w2,w6,w0,w3,w4],dL 0x1f01e01100800500401d003002,dS 0xb15171006161c0204,pH 0x544222111333313121113 9 9),
([w27,w1,w6,w0,w3,w4],dL 0x201101f01e00301d008,dS 0xb0d15051d0e071319100611170402,pH 0x141313222211112 7 15),
([w1,w19,w2,w6,w0,w3,w4],dL 0x27008024023004022003002,dS 0xe0c0b171a1d0415101c0205,pH 0x544322111321111333133 8 12),
([w1,w2,w32,w6,w0,w3,w4],dL 0x802f010006003,dS 0x1015170e1d0504010c030d110206,pH 0x433111451311222222222 5 14),
([w1,w2,w32,w0,w3,w4],dL 0x2f01603d03e004003010036006,dS 0xd0e050c19060102,pH 0x622224552111111 9 8),
([w155,w1,w2,w0,w3,w4],dL 0x4001603d03e03603f003,dS 0xc0a0b1917100f0806020115,pH 0x433111222211112 7 12),
([w1,w2,w56,w6,w0,w3,w4],dL 0x33045008011003,dS 0x15101d0705090a0d0c0b17020604,pH 0x441111415312122222222 5 14),
([w1,w2,w56,w0,w3,w4],dL 0x800302700d016011,dS 0x60c170a0d09040b02,pH 0x232252523111111 6 9),
([w1,w2,w0,w3,w102,w4],dL 0x5404805003604f05203d014003,dS 0xc170a0b0d0e190f1306050911070102,pH 0x133513111122222 9 16),
([w25,w1,w2,w6,w0,w3,w4],dL 0x1103805700801d003,dS 0xb0d15171007010a02040c06,pH 0x343111111222222313122 6 12),
([w25,w1,w2,w0,w3,w4],dL 0x4803601100303805701d03d,dS 0x170e0d0b07010c0a02,pH 0x141314222211122 8 9),
([w361,w1,w2,w0,w3,w4],dL 0x5e02c05d02700300d,dS 0xb110406171301031510,pH 0x111222444421224 6 10),
([w1,w2,w30,w6,w0,w3,w4],dL 0x8039029022003,dS 0x15101a0401170a0b1d02061105,pH 0x331111154321122222222 5 13),
([w1,w2,w30,w0,w3,w4],dL 0x1603d039061005003029048022,dS 0xb1a13060a07050102,pH 0x226422255111111 9 9),
([w362,w1,w2,w0,w3,w4],dL 0x1603d030062003061,dS 0xd0b0a1306050215170f090c0110,pH 0x111222333312223 6 14),
([w1,w2,w6,w14,w0,w3,w4],dL 0x6101600a04103600301006a008037063004,dS 0xd1d07050403110a0c151a0206,pH 0x564514341711312222212 12 13),
([w45,w1,w2,w6,w0,w3,w4],dL 0x6100300d004071010070042008,dS 0x150d0a06020b1003110c07,pH 0x141512212333363161113 9 11),
([w1,w2,w6,w7,w0,w3,w4],dL 0x804803200d041036003029010005018072004,dS 0x1d070504030d170b110e0206,pH 0x6551d43a1711312222212 13 12),
([w1,w2,w6,w0,w23,w3,w4],dL 0x4803203e01600a00302906d04a008082005,dS 0x1d07040310110c0e0b0206,pH 0x331535137a41112222212 12 11),
([w71,w1,w2,w6,w0,w3,w4],dL 0x3e00302706e005029088046008,dS 0x100c0d1d051502110a06,pH 0x141216212333353151113 9 10),
([w363,w1,w2,w0,w3,w4],dL 0x8901603d005036006002,dS 0xd0a10190e0b0f0206080316,pH 0x433111222211112 7 12),
([w1,w364,w2,w0,w3,w4],dL 0x3e00408a03f036,dS 0xd0c0a050619030108,pH 0x511441111222222 5 9),
([w253,w1,w2,w0,w3,w4],dL 0x8d08c005016004011002,dS 0xe130401020d0b,pH 0x433111222211112 7 7),
([w1,w2,w0,w3,w126,w4],dL 0x4803608f03d00208e08b014,dS 0xc0e0d19130608011a0b0a090704,pH 0x254333212411111 8 14),
([w193,w1,w2,w0,w3,w4],dL 0x9109000503d00401d002,dS 0xb06090e0f0204161c,pH 0x433111222211112 7 9),
([w1,w365,w2,w0,w3,w4],dL 0x9309202700d08b05d016,dS 0xb1211130515100201,pH 0x141313111222222 7 9),
([w366,w1,w2,w0,w3,w4],dL 0x1603d094048004022002,dS 0xc150b1d0613090d1a0f0501021c,pH 0x433111222211112 7 14),
([w1,w367,w2,w0,w3,w4],dL 0x61096005095062048,dS 0x130c02070b0a0109,pH 0x116145111222222 6 8),
([w10,w1,w0,w3,w8,w4],dL 0x309900200809701408b,dS 0xc0e0d130f071a0b1909010a,pH 0x145333222211152 7 12),
([w27,w10,w1,w0,w3,w4],dL 0x408b00801d002,dS 0xa0b0112021d0717110919081306,pH 0x353222111211122 5 14),
([w10,w1,w2,w14,w0,w3,w4],dL 0x6108b09b09c098008063004,dS 0x1115010209061c080a1a0d,pH 0x411513111122121111121 8 11),
([w45,w10,w1,w2,w0,w3,w4],dL 0x610a10a009b0a208b004008,dS 0x11020c0a060d0b10091a01,pH 0x121212111121211121115 8 11),
([w10,w1,w2,w7,w0,w3,w4],dL 0x800d08b09b072005004,dS 0x11170209060d0b010e,pH 0x211172111133131111131 7 9),
([w10,w1,w2,w0,w23,w3,w4],dL 0x3e08b0a7008098082005,dS 0x111007092a020a0616010c0b0e,pH 0x141145111112221111121 7 13),
([w71,w10,w1,w2,w0,w3,w4],dL 0x3e0ac0ab0aa0ad08b005008,dS 0x11070b020c0a060d15090e01,pH 0x121212111121211121115 8 12),
([w1,w2,w90,w0,w3,w4],dL 0x4803d0160360b10b00af003,dS 0xd06050b0c11130f0a0102,pH 0x433112111122222 8 11),
([w254,w1,w2,w0,w3,w4],dL 0xb701603d0050b60b5002,dS 0xc100a0f13361a06010d03,pH 0x433111222211212 7 11),
([w368,w1,w2,w0,w3,w4],dL 0xb800200303e016063036,dS 0x1e0d111a0a1c0e0b1308010215,pH 0x311431222211112 7 13),
([w1,w2,w0,w3,w156,w4],dL 0x480030020bc0360ba03d0b9,dS 0xd05080c060e170b0a0103,pH 0x224313522411111 8 11),
([w369,w1,w2,w0,w3,w4],dL 0xc000200303e03d070036,dS 0xc1a110b08010e1c0f020a0316,pH 0x311431222211112 7 13),
([w1,w370,w2,w0,w3,w4],dL 0xc30020030270c20c1016,dS 0x370c170e1c0a1119050d0201,pH 0x131413112122222 7 12),
([w111,w1,w2,w0,w3,w4],dL 0x1603d002003048072036,dS 0x130e051510090c0d0b01170f0a02,pH 0x311311222211112 7 14),
([w1,w112,w2,w0,w3,w4],dL 0x480d103e,dS 0x130e06110c020b0a0105,pH 0x331311332322222 3 10),
([w17,w18,w1,w2,w3,w4],dL 0x805008b03e03f036,dS 0xd1903013617071c0b0c0a,pH 0x334222111511122 6 11),
([w18,w1,w16,w2,w0,w3,w4],dL 0x6108b0070dd0360df0080de0c40e00110dc004,dS 0x7170d15040c060f11,pH 0x422112112733211553552 13 9),
([w18,w1,w2,w0,w3,w8,w4],dL 0x610070e90360c60ea0e800808b,dS 0x110d0615010e130c1a1903,pH 0x122333111311131512113 9 11),
([w27,w18,w1,w2,w0,w3,w4],dL 0x610dd0360070ef0c90c7004008,dS 0xd120e060c17160111191303,pH 0x121212111133132111118 9 12),
([w37,w18,w1,w2,w0,w3,w4],dL 0xf10df0610ec0360080040070f00cd0cb08b,dS 0xd12131a0f0a0c0e06031501,pH 0x327112111122126111119 12 12),
([w18,w1,w19,w2,w0,w3,w4],dL 0xd0080270070f40dd0f30220f200403e,dS 0xa060d1a010e0b15050c13,pH 0x133223223114322111253 11 11),
([w66,w18,w1,w2,w0,w3,w4],dL 0x2700d0080f80f70ec0f900703e08b,dS 0x60a020c031617010d2a13,pH 0x222111111122111111215 10 11),
([w45,w18,w1,w2,w3,w4],dL 0x8b05000803e070036,dS 0xd1a1137060103100b0c0a,pH 0x334222111511122 6 11),
([w18,w1,w2,w7,w3,w4],dL 0x808b0270050d0072036,dS 0xc1711020d13010a030e0f0b,pH 0x311311222211212 7 12),
([w18,w1,w2,w0,w23,w3,w4],dL 0x408b0070050820fc00d03e,dS 0xd0a11192a030b01160f060c0e,pH 0x111333122312231111113 8 13),
([w71,w18,w1,w2,w0,w3,w4],dL 0x500408b0fe0fd0ed0ff00700803e,dS 0x110a020c150f0d0e0501,pH 0x211121222212212212225 10 10),
([w41,w2,w0,w3,w9,w4],dL 0x102700d03d016,dS 0x30d0c090a2a3a0801020b04,pH 0x215331421311111 5 12),
([w1,w12,w2,w0,w3,w9,w4],dL 0x6103610111000203d10000f08b10c00d006,dS 0x1e19182a08040d0a16070c0111,pH 0x331325344267242121111 12 13),
([w17,w1,w2,w0,w3,w9,w4],dL 0x6103d00400d11411203f11008b,dS 0x160d0a080b1c01071e0c,pH 0x543222111236333111223 9 10),
([w1,w16,w2,w0,w3,w9,w4],dL 0x11611508b02700d03d011016,dS 0x161c0c0f0a2a080d010b04,pH 0x312431521416111212222 8 11),
([w1,w2,w0,w9,w8,w4],dL 0x11711808b01403d,dS 0xc0a0b0d1e062a0208010e1a13190411,pH 0x112511331322222 5 16),
([w37,w1,w2,w0,w3,w9,w4],dL 0x11a01111908b02700d05d03d016,dS 0x161c0f110b15100104,pH 0x213421521431333111113 9 9)]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p1 : List StD := [
([w37,w1,w2,w0,w9,w4],dL 0x1601111a11303d11905d08b,dS 0xe160b0d1c2a1f1a0f0a1104071001,pH 0x434113222211552 8 15),
([w1,w61,w2,w0,w3,w9,w4],dL 0x8b10f11e01103d,dS 0x161c2a09080f010d0b0a0c1104,pH 0x112311311435241222222 5 13),
([w1,w61,w2,w0,w3,w4],dL 0x3d11e08b10f005004011002,dS 0xc0a0f060809010d0b04,pH 0x433111121122222 8 10),
([w36,w1,w2,w0,w3,w9,w4],dL 0x1110812305d08b03d,dS 0x160d1c0f020b010a040c11,pH 0x113411211233333213213 6 11),
([w36,w1,w2,w0,w3,w4],dL 0x4801103603d10812305d003,dS 0xf060d0b11020c0a01,pH 0x344111222212112 8 9),
([w1,w19,w2,w0,w3,w9,w4],dL 0x4803e10000203d10608b10b028027022,dS 0x201308040b1c070c010a11,pH 0x331644283457242121111 11 11),
([w66,w1,w2,w0,w3,w9,w4],dL 0x3e03d0050270be10e06210608b,dS 0x1c070c2a160d0a01061f0b,pH 0x223244211136333211123 9 11),
([w1,w2,w14,w0,w3,w9,w4],dL 0x13100708b00402706303d016,dS 0x16151e070a132a040d0c1c0806010f,pH 0x213431111212111313331 8 15),
([w1,w2,w67,w0,w3,w9,w4],dL 0x8b13411006303d,dS 0x161c072a0304080d0c1106010f,pH 0x112312432111135222221 5 13),
([w1,w2,w67,w0,w3,w4],dL 0xd00200303d03e110036063,dS 0x1a111c06050d08010c03,pH 0x422215482211111 8 10),
([w1,w2,w7,w0,w3,w9,w4],dL 0x4802710100408b03603d11005110600d072,dS 0xd130b072a08040601110f,pH 0x321555262339158121111 12 11),
([w1,w2,w0,w23,w3,w9,w4],dL 0x2314908b00500d08203d016,dS 0x1f1c100c19070804162a060a0b010f,pH 0x313211421112111313311 8 15),
([w1,w2,w0,w3,w55,w9,w4],dL 0x8b13810608203d,dS 0x1c1e1619070208042a06110a0b010f,pH 0x113222314131511222211 5 15),
([w1,w2,w0,w3,w55,w4],dL 0x200302703d106082061,dS 0x16190e112a0a010b02,pH 0x412111115122222 7 9),
([w371,w1,w2,w0,w3,w4],dL 0x13500200308803d061,dS 0xe110a16170f050d01021c0c,pH 0x212121333312223 6 12),
([w1,w2,w194,w0,w3,w4],dL 0x4803601614c00814b014003,dS 0xb0d0604030c130a19091102,pH 0x433121111122222 8 12),
([w372,w1,w2,w0,w3,w4],dL 0x1614e08b14d00500401d002,dS 0xd1213060b161c0102,pH 0x433111222212112 8 9),
([w373,w1,w2,w0,w3,w4],dL 0x3e07003600d,dS 0x1e0d0c1a050e0a110102,pH 0x122412333323223 4 10),
([w374,w1,w2,w0,w3,w4],dL 0x15000200304800d082016,dS 0x1f0c16110e0b05020d17192a0110,pH 0x131413222211112 7 14),
([w1,w255,w2,w0,w3,w4],dL 0x61048088027,dS 0x1f110e0a0c17020b0105,pH 0x331314323322222 4 10),
([w41,w1,w12,w2,w0,w3,w4],dL 0x6100808b15415300600d,dS 0x1603010c110710020a190d,pH 0x111411415121122121111 7 11),
([w17,w41,w1,w2,w0,w3,w4],dL 0x6115b15a15915c00800d08b,dS 0x703010c0a110d0b1c020919,pH 0x222111111121211111215 8 12),
([w41,w1,w2,w0,w8,w4],dL 0x3d15f00815e01601408b,dS 0xc0d030e1711190b1a090a1302,pH 0x141131222255332 7 13),
([w37,w41,w1,w2,w0,w4],dL 0xd08b05d016,dS 0xa0b0f07050312011f1e13021a0e0611,pH 0x433222111211122 4 16),
([w41,w1,w19,w2,w0,w3,w4],dL 0x3e00816108b153022027,dS 0x71c0601110215050c130b,pH 0x111113415111222121111 7 11),
([w66,w41,w1,w2,w0,w3,w4],dL 0x3e16416315916500802708b,dS 0x703010c0a110b0d16020913,pH 0x222111111121211111215 8 12),
([w41,w1,w2,w7,w0,w3,w4],dL 0x8b00415800807202700d,dS 0x70f03011109020d0b13,pH 0x111112211731133131111 7 10),
([w1,w2,w157,w0,w3,w4],dL 0x3d01603604816c16d16b003,dS 0xb06050d110a0f0c190102,pH 0x334211111122222 8 11),
([w256,w1,w2,w0,w3,w4],dL 0x1603d171172004170002,dS 0x150c0a460f190e06010b02,pH 0x433111222221112 7 11),
([w113,w1,w2,w0,w3,w4],dL 0x174036061,dS 0x130e06110a0d01020c,pH 0x122112333332223 3 9),
([w1,w2,w0,w3,w195,w4],dL 0x3600300204817e18103d17d,dS 0xb2a0d1a17070a0c0102,pH 0x125342522411111 8 10),
([w375,w1,w2,w0,w3,w4],dL 0x18300200318400d182016,dS 0x47160c171a0a0e13020b01,pH 0x131413222221112 7 11),
([w39,w1,w12,w2,w0,w3,w4],dL 0x2700800d023187186111006185005061,dS 0xc070e0b010d1710020a19,pH 0x331322322134122111253 11 11),
([w17,w39,w1,w2,w0,w3,w4],dL 0x18e00d02700818d18c18b02306108b,dS 0x70c050a0217011c0b0819,pH 0x222111111112211111214 10 11),
([w39,w1,w16,w2,w0,w3,w4],dL 0x8b03e0231860481921911900d201100818f005,dS 0x7100b17040a060f11,pH 0x223211211328711355552 13 9),
([w39,w1,w2,w0,w3,w8,w4],dL 0x3e19a0d502304819919800808b,dS 0x110b06101a0a19010e1302,pH 0x332312311131111112413 9 11),
([w27,w39,w1,w2,w0,w3,w4],dL 0x3e1860480c802319d0ca005008,dS 0xb120a0e06171c1113190102,pH 0x121212111113332111118 9 12),
([w37,w39,w1,w2,w0,w3,w4],dL 0x19203e18b19f0cc04800502319e0080ce08b,dS 0xb1207131a0a0f0c0e10060201,pH 0x32311111111222611111a 12 13),
([w66,w39,w1,w2,w0,w3],dL 0x805408b061062048,dS 0x13020116461706100d0a0c,pH 0x343222111511122 6 11),
([w39,w1,w2,w14,w0,w3,w4],dL 0x508b1920230040630081a003e061,dS 0xc1113080a1c02011a0f06,pH 0x331314341235121411113 10 11),
([w45,w39,w1,w2,w0,w3,w4],dL 0x400508b1a41a31891a5023061008,dS 0x110c0f050a06101a0b0201,pH 0x121212111111221121115 10 11),
([w39,w1,w2,w7,w0,w3],dL 0x808b00d004173072048,dS 0x110a130e07050b020c01170f0d,pH 0x311131222211212 7 13),
([w71,w39,w1,w2,w0,w3],dL 0x8b054008061088048,dS 0xe110b470f0102150d0a0c,pH 0x343222111511122 6 11),
([w1,w12,w2,w21,w0,w3,w4],dL 0xd08b1a6005036006002,dS 0xa10170719180e060d16110c02,pH 0x433472111211321222122 7 13),
([w1,w2,w21,w0,w3,w4],dL 0x4803d01603601008b1a6002006,dS 0x101707190a0d0c110602,pH 0x335371221111121 9 10),
([w17,w1,w12,w2,w3,w4],dL 0x50041aa08b050002003,dS 0xd0c0510081c0b020a01,pH 0x711223441211315 7 10),
([w1,w238,w2,w0,w3,w4],dL 0x541ab00100501603602a002,dS 0x100e0b13050a190c11020601,pH 0x433111143122222 8 12),
([w1,w12,w2,w0,w3,w114,w4],dL 0x1ac00d005036104002,dS 0xd180e0b130503101907160a0c0201,pH 0x441333111115111222222 6 15),
([w1,w2,w0,w3,w114,w4],dL 0x4800500d1041ac0020e8008,dS 0xd05030e0b0a0c070201,pH 0x113211311311115 8 10),
([w376,w1,w2,w0,w3,w4],dL 0x1ad1a7005036002008,dS 0xa070b0e1c06011602,pH 0x131222111221225 6 9),
([w82,w1,w12,w2,w0,w3,w4],dL 0x1af0e810500500200d,dS 0x161c0c0e0701100a020d,pH 0x111211211134144121114 6 10),
([w82,w1,w2,w0,w3,w4],dL 0x1af0141050020270f1016,dS 0xe1c0a060c190201100d,pH 0x121312352514115 7 10),
([w1,w158,w2,w0,w3,w4],dL 0x1603d00104803602d002,dS 0xb13161c0f05110d0c0a020601,pH 0x433111413122222 7 13),
([w159,w1,w2,w0,w3,w4],dL 0xf91b6048005,dS 0xb11020c0a060119,pH 0x224211233122223 4 8),
([w1,w12,w2,w0,w3,w8,w4],dL 0x1b81b700d0050e800208b,dS 0xc100e130d0a16090201,pH 0x142313151125212111116 7 10),
([w37,w1,w12,w2,w0,w3,w4],dL 0x1b90cb1070e800d00500208b,dS 0xd0a160e0615100102,pH 0x334111221211111121116 8 9),
([w1,w12,w2,w7,w3,w4],dL 0x27185188036005,dS 0xd0c10190e0609110a0b070201,pH 0x122112222133333 5 13),
([w1,w12,w2,w0,w23,w3,w4],dL 0x1a800d005,dS 0xd160b2a10190e0c110a070201,pH 0x111122111111112333333 3 13),
([w71,w1,w12,w2,w0,w3,w4],dL 0xf0271a9005061,dS 0x150d0b11020c0e010a10051d,pH 0x111121121113133121113 5 12),
([w1,w83,w2,w0,w3,w4],dL 0x1c303600308b00403f,dS 0xd0e0c0b0906080a,pH 0x622333331111111 6 8),
([w377,w1,w2,w0,w3,w4],dL 0x1c61c503e01603608b003,dS 0xb1106171013081501,pH 0x433111222111116 7 9),
([w1,w2,w0,w3,w196,w4],dL 0x1c904808b0041c70031c8008,dS 0x161e0b19051c1710020701,pH 0x113222513311144 8 11),
([w257,w1,w2,w0,w3,w4],dL 0x1cb1ca03e03d03608b003,dS 0xe0710170a0609010c,pH 0x433111222111116 7 9),
([w1,w2,w378,w0,w3,w4],dL 0x1ce08b0030040271cc0dc016,dS 0x190713050c1e0d0a02060b01,pH 0x121161412133333 8 12)]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p2 : List StD := [
([w379,w1,w2,w0,w3,w4],dL 0x1603d1cf04803608b003,dS 0x160d0b19130c170a0f1c060109,pH 0x433111222111115 7 13),
([w1,w2,w197,w0,w3,w4],dL 0x408b0031d00f204803e,dS 0x13111c020601,pH 0x221522271224144 7 6),
([w17,w1,w2,w0,w23,w3,w4],dL 0x4a0041c20fc00d03e,dS 0xd1c0b2a02070a08190c16011e,pH 0x111111122114414111114 6 13),
([w71,w17,w1,w2,w0,w3,w4],dL 0xd0040461121d206103e,dS 0xe0a0c0d151e081d05,pH 0x111141131314121211524 7 9),
([w1,w16,w2,w57,w0,w3,w4],dL 0x8b0081d31cd005004016011002,dS 0x15100c0a0d0b04,pH 0x343524111213121222122 9 7),
([w1,w2,w57,w0,w3,w4],dL 0x4803600801608b1d31cd002011,dS 0xd100f07150b0c110a0406,pH 0x633413212111121 9 11),
([w27,w1,w16,w0,w3,w4],dL 0x40011d7016008002,dS 0xa0b1205040f071913020601,pH 0x363131232111114 6 12),
([w27,w1,w2,w0,w3,w4],dL 0x160031d81c801d002,dS 0xd1213060b161c0102,pH 0x433111222211112 6 9),
([w191,w1,w2,w0,w3,w4],dL 0x1da03e00d1d9036004,dS 0x19050c0a11020601,pH 0x422112332322223 6 8),
([w37,w1,w16,w2,w0,w4],dL 0x40011db08b002003,dS 0xa0b1205041a0e17011102,pH 0x611222331211114 6 11),
([w37,w1,w2,w0,w3,w4],dL 0x201619f0f105d003,dS 0xb12061302151001,pH 0x433111222211112 6 8),
([w1,w380,w2,w0,w3,w4],dL 0x501dc001048016004043002,dS 0x150f0e070d1a19050c110a060201,pH 0x433111541122222 8 14),
([w258,w1,w2,w0,w3,w4],dL 0x1de0611dd027048005,dS 0xe070a060c11020f01,pH 0x225211244122224 6 9),
([w1,w16,w2,w0,w3,w8,w4],dL 0x1930e101500500400208b,dS 0x6130c0a0d0902040b01,pH 0x142313111121122111115 7 10),
([w1,w16,w2,w0,w8,w4],dL 0x401500208b,dS 0xa0b06130217111a0e090401,pH 0x141212222211123 4 12),
([w1,w16,w0,w3,w8,w4],dL 0xd015016008,dS 0xf110a0b060e02040719130901,pH 0x121412222211213 4 13),
([w1,w16,w0,w8,w4],dL 0x500408b0030021930e1015,dS 0x70e121902040b090d0c060a01,pH 0x5224141111 8 13),
([w1,w16,w2,w7,w0,w3,w4],dL 0xc40dc03600d18f0e5004,dS 0x17070f0d0e0b130904061101,pH 0x311143111111111222222 7 12),
([w65,w1,w2,w0,w3,w4],dL 0x4803600800303d19b0eb08b014,dS 0xb0d07090c0a1106,pH 0x433222111121211 9 8),
([w27,w1,w2,w0,w8,w4],dL 0x40011e900208b,dS 0xa0b121711091a0e0201,pH 0x151212111222223 5 10),
([w37,w1,w0,w3,w8,w4],dL 0xd0011ea01608b003,dS 0xf120a0b06071a0e0919130102,pH 0x131613212211114 6 13),
([w1,w19,w2,w0,w3,w8,w4],dL 0xd51ec1eb02802700400208b,dS 0xe0b0a1909020c1a1c0501,pH 0x152313141114222111116 8 11),
([w1,w2,w14,w0,w3,w8,w4],dL 0x1ed0c6027037004016008,dS 0xc0d0815190a09021301,pH 0x113511233142142111111 7 10),
([w1,w2,w72,w0,w3,w8,w4],dL 0x1f00e803d08b003,dS 0x110d15070c0e091a19021301,pH 0x133413543111111212221 5 12),
([w1,w2,w72,w0,w3,w4],dL 0x41f000803d08b03e0e800304e036,dS 0x5110a15130c070201,pH 0x511113331322222 10 9),
([w1,w2,w7,w0,w3,w8,w4],dL 0x480270c603d00503600305100d0040170181980e8,dS 0x1a1909020e1301,pH 0x225111186226515444441 14 7),
([w1,w2,w0,w23,w3,w8,w4],dL 0xd51fa04a00d005016008,dS 0x10090c0b2a190a021301,pH 0x113133411252121111111 7 10),
([w1,w2,w0,w3,w103,w8,w4],dL 0x1f219803d08b003,dS 0x110b101a06090e05020a191301,pH 0x114333515311111212221 5 13),
([w1,w2,w0,w3,w103,w4],dL 0x81f208b00503d053003061,dS 0xb1013071a190511060c02010a,pH 0x211111222233333 8 13),
([w381,w1,w2,w0,w3,w4],dL 0x1f11fd03d08b003061,dS 0x160b15060c170f09010a,pH 0x111222333212225 6 10),
([w1,w135,w2,w0,w3,w4],dL 0x4803603d08b1ff1fe00200801d,dS 0xd190705030b0c0a021106,pH 0x242323212111111 9 11),
([w1,w16,w2,w0,w3,w4],dL 0x301618f0dc011002,dS 0x130502010d0b04,pH 0x433111111122222 6 7),
([w1,w2,w382,w0,w3,w4],dL 0x20000803e03d056036004,dS 0x50c1102130701,pH 0x411114111133133 7 7),
([w1,w2,w0,w3,w8,w4],dL 0x19803d0020e8016003014,dS 0xc0e0a0b1a1309190102,pH 0x235423232511111 7 10),
([w383,w1,w2,w0,w3,w4],dL 0x202201048004002008,dS 0xc0d06161a0f011c05,pH 0x131222111221225 6 9),
([w1,w2,w0,w3,w136,w4],dL 0x820305903d061005,dS 0xe070b19110a060201,pH 0x311112111111444 6 9),
([w27,w37,w1,w2,w0,w3,w4],dL 0x20520400500408b003002,dS 0xb13061510161c0102,pH 0x544111333121222121111 7 9),
([w27,w37,w1,w2,w0,w4],dL 0x408b003002,dS 0xa0b0513061117011a0e02,pH 0x411331222211111 4 11),
([w27,w37,w1,w0,w3,w4],dL 0xd00803d016,dS 0xa0b0502110e0719130f0106,pH 0x141313111122221 4 12),
([w27,w1,w2,w14,w0,w3,w4],dL 0x2060c705a0e8004027016008,dS 0xd150a1308161c0201,pH 0x131241314211111111116 8 9),
([w27,w1,w2,w7,w0,w3,w4],dL 0x270480e81c80360c705100d1d805b004,dS 0x171219090613021101,pH 0x311143111122222111112 11 9),
([w27,w1,w2,w0,w23,w3,w4],dL 0xca20d05c19800500d016008,dS 0xb100c190a2a161c0201,pH 0x114312412311111111116 8 10),
([w1,w198,w2,w0,w3,w4],dL 0x480360081ae00320e01608b05d,dS 0xb0e072a080d0a0c011106,pH 0x363222212111111 9 11),
([w1,w384,w2,w0,w3,w4],dL 0x20f08b03e00312203600d,dS 0x5020c060e1101,pH 0x122412224233233 7 7),
([w385,w1,w2,w0,w3,w4],dL 0x21121004808b00300d,dS 0xd0a0c151719112a1001,pH 0x111222333221225 6 10),
([w1,w2,w386,w0,w3,w4],dL 0x21208b061003125048027,dS 0x1307061a0a021101,pH 0x221422244223333 7 8),
([w37,w1,w19,w2,w0,w3,w4],dL 0xce21312619802700400208b,dS 0xc0b1a1c0f0515100102,pH 0x433111122211111121116 8 10),
([w37,w1,w2,w7,w0,w3,w4],dL 0x50480cb0360e800401819f12900d,dS 0x1a12070f0911060e0102,pH 0x111113311522222111112 10 10),
([w1,w19,w2,w33,w0,w3,w4],dL 0x2708b219004048022002,dS 0xc150e2006131a1d0b1c110a05,pH 0x334274111231121222122 7 13),
([w1,w2,w33,w0,w3,w4],dL 0x3d01603602904808b219002022,dS 0x150e1d13070c110b0a0506,pH 0x633183122111121 9 11),
([w160,w1,w2,w0,w3,w4],dL 0x18e21d036004,dS 0xd13110a0c020106,pH 0x422112332322223 4 8),
([w1,w19,w2,w0,w3,w115,w4],dL 0x21f02704800412d002,dS 0xb200d1a19151302061c0c0a0501,pH 0x441333111115111222222 6 14),
([w1,w2,w0,w3,w115,w4],dL 0x3600412d21f048027002008,dS 0x60b050a0d1a0c070201,pH 0x112311211211116 8 10),
([w91,w1,w19,w2,w0,w3,w4],dL 0x22003d11d004002027,dS 0x161a1c0a06050201150c130b,pH 0x111112112114324121114 6 12),
([w91,w1,w2,w0,w3,w4],dL 0x22001411d00219f00d016,dS 0x161a0c060a130201150b,pH 0x121312352514115 7 10),
([w66,w1,w19,w2,w0,w3],dL 0x22208b054004002003,dS 0xb160d1c05150a090c01,pH 0x311224531211416 6 10),
([w1,w19,w2,w14,w0,w3,w4],dL 0x2721b03e004,dS 0x150b130d0a1c081a0c11060501,pH 0x211212111111112331333 4 13),
([w45,w1,w19,w2,w0,w3,w4],dL 0x2800d21c00403e,dS 0x100b0d11050a1a010c150206,pH 0x111121121113133121113 5 12),
([w1,w19,w2,w7,w0,w3],dL 0xd0f20f5048004,dS 0xb150a13071a0f09110c060d0501,pH 0x122112222133333 5 14),
([w1,w137,w2,w0,w3,w4],dL 0x4822a00308b062005,dS 0xb110d0a2a06090c,pH 0x115333233222222 6 8),
([w1,w199,w2,w0,w3,w4],dL 0x408b00322e185036061,dS 0x131116020601,pH 0x122152225214244 7 6),
([w1,w2,w0,w3,w259,w4],dL 0x3608b00322f230005008,dS 0xb0d1c1f190705160a020601,pH 0x115333211211144 7 12),
([w1,w387,w2,w0,w3,w4],dL 0x23208b00300500d23118f016,dS 0xc1f0a0d13060b0102,pH 0x141214161133333 8 9),
([w66,w1,w2,w14,w0,w3,w4],dL 0x3700502722b1a003e061,dS 0x160d0b0802060c1c0a09131f01,pH 0x111112151214144111114 7 13)]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p3 : List StD := [
([w45,w66,w1,w2,w0,w3,w4],dL 0x2330f700522d0be04223406103e,dS 0x13010c0a0b10091f0602,pH 0x111141131322112121418 9 10),
([w1,w2,w14,w0,w34,w3,w4],dL 0x800422303e016063036,dS 0x24151e1a0a1c130d110f060c08,pH 0x342112132153611221222 7 13),
([w1,w2,w0,w34,w3,w4],dL 0x48003002016036008110223063,dS 0xf1c1a0a0d0c061108,pH 0x621211267511511 9 9),
([w1,w2,w14,w0,w46,w3,w4],dL 0x22403e016004068036,dS 0x24150b05080d1a1c110a130c0201,pH 0x453111133164111222221 6 14),
([w1,w2,w0,w46,w3,w4],dL 0x270480040680162240360e808b003,dS 0xd050b11020c130a01,pH 0x611331114122127 10 9),
([w78,w1,w2,w14,w0,w3,w4],dL 0x23900302b01603e036004,dS 0x15100c11080a1c060113021a0d,pH 0x411212111134155111115 7 13),
([w78,w1,w2,w0,w3,w4],dL 0x23901401602b0051c8002,dS 0x101213110a060c01021c0d,pH 0x322111342411114 7 11),
([w45,w1,w2,w14,w3,w4],dL 0x3e23b05000d008036,dS 0xd0c05081c100b020a01,pH 0x314631231514115 6 10),
([w1,w2,w161,w0,w3,w4],dL 0x200300104801606c036,dS 0x1517100e05060d0b0c110a0201,pH 0x311431431122222 7 13),
([w84,w1,w2,w0,w3,w4],dL 0x2724204803e,dS 0xe060c0b11020a01,pH 0x221241233322223 4 8),
([w1,w2,w14,w7,w3,w4],dL 0x51a01a1036027,dS 0xc0e0d1a1c1309080a02060b1101,pH 0x122212112233333 5 14),
([w1,w162,w2,w0,w3,w4],dL 0x24503d03600807000d,dS 0xd060c0b1109020a,pH 0x313631322322222 6 8),
([w1,w2,w388,w0,w3,w4],dL 0xd04800403d2470362460f108b003,dS 0xb1c0f0705151102100601,pH 0x633111111122244 10 11),
([w1,w389,w2,w0,w3,w4],dL 0x24900803d00d0052480dc002,dS 0x1a0e050c0a060d0b110301,pH 0x422111111633333 8 11),
([w390,w1,w2,w0,w3,w4],dL 0x200324a048036008,dS 0x1a150d110b020c170a0f0e100109,pH 0x122312112121224 6 14),
([w1,w2,w0,w3,w200,w4],dL 0xd00803d24b0fc04803e,dS 0xe0610110201,pH 0x513333117314444 7 6),
([w1,w2,w7,w0,w11,w3,w4],dL 0xd00425124d048072036,dS 0x170d0b060e1311090f,pH 0x327112412531611221222 7 9),
([w1,w2,w0,w11,w3,w4],dL 0x3d01600300204803625124d072,dS 0xd0e130b0c110a0609,pH 0x318121516411411 9 9),
([w1,w2,w7,w0,w60,w3,w4],dL 0xd00404807726025e036,dS 0x17090e11020f01,pH 0x327112216331111444141 7 7),
([w1,w2,w0,w60,w3,w4],dL 0x3d01604807703625e26008b003,dS 0xd161c050b11020f01,pH 0x311341115122126 9 9),
([w43,w1,w2,w7,w0,w3,w4],dL 0xd00326502e267048036004,dS 0x1711090d0b060f010e02,pH 0x311124111131155111115 8 10),
([w43,w1,w2,w0,w3,w4],dL 0x1603d02e267265002,dS 0xf11060d0c0a0e02010b,pH 0x322111442411114 6 10),
([w1,w2,w7,w0,w3,w62,w4],dL 0x400d04814026a268036,dS 0x13091706020f01,pH 0x231121261337111444141 7 7),
([w1,w2,w0,w3,w62,w4],dL 0x4800300214003626a268008,dS 0xd15171005060b0201,pH 0x114211811411115 8 9),
([w44,w1,w2,w7,w0,w3,w4],dL 0x404826827113303600d,dS 0xf090617130102,pH 0x111114411233131121113 7 7),
([w44,w1,w2,w0,w3,w4],dL 0x2003133271272016,dS 0x17060e0d0c0a1301020b,pH 0x121312442411114 6 10),
([w1,w2,w7,w0,w23,w3],dL 0x400d0fa0fc048,dS 0x170a0e190b07162a09060c020d1101,pH 0x421111412133333 5 15),
([w1,w2,w0,w23,w3,w35,w4],dL 0x80051bf00d048082016,dS 0x291f100c16110e1907060f0b0a2a,pH 0x212321341536115212222 7 14),
([w1,w2,w0,w3,w35,w4],dL 0x360030020481060080161bf082,dS 0x160f070e0c060b0a112a,pH 0x111223673213111 9 10),
([w1,w2,w0,w23,w3,w127,w4],dL 0x1c000d005086048016,dS 0x290d10160e112a0c02190a0b01,pH 0x211244251121116333311 6 13),
([w1,w2,w0,w3,w127,w4],dL 0x503600d0860480161981c008b003,dS 0xb050d1102190c0a01,pH 0x141313151121227 10 9),
([w92,w1,w2,w0,w23,w3,w4],dL 0x327504400d005,dS 0x151019112a06010a02160c0e0b,pH 0x111122111112323111113 5 13),
([w92,w1,w2,w0,w3,w4],dL 0x142750160441d8004002,dS 0x15190c11060a0e0102160b,pH 0x322111342411114 7 11),
([w163,w1,w2,w0,w3,w4],dL 0x1a527703600d,dS 0xd02060a0c11010e,pH 0x122412312322223 4 8),
([w71,w1,w2,w0,w23,w3],dL 0x27800805403d00d,dS 0xb2a16150d050c010a,pH 0x321211211532225 5 9),
([w1,w164,w2,w0,w3,w4],dL 0x27904803d008088027,dS 0xb070a0d1109050c,pH 0x313136223322222 6 8),
([w1,w2,w260,w0,w3,w4],dL 0x3600527b04803d27a02708b003,dS 0x160d0f0605100215111d01,pH 0x337111111122244 9 11),
([w1,w261,w2,w0,w3,w4],dL 0x827d03d02700427c18f002,dS 0xc0a1d0d0e0b110201,pH 0x244111111633333 8 9),
([w1,w2,w201,w0,w3,w4],dL 0xd00803d27e1a0036061,dS 0xe0615110201,pH 0x122225152214244 7 6)]
noncomputable def p13_D7 : List StD := p13_D7p0 ++ p13_D7p1 ++ p13_D7p2 ++ p13_D7p3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x1 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x2 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x3 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (3*64)).take 64) = true := by decide +kernel
theorem p13_I7 : LevelN p13_R p13_T 7 p13_D7 := levelStep p13_B p13_W p13_Q p13_I6 (chunks 64 p13_D7 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  · exact p13_C7x1
  · exact p13_C7x2
  · exact p13_C7x3
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
([w1,w2,w6,w0,w3,w4],dL 0x29010003001,dS 0xb0d171d0e070504030115100c02110a06,pH 0x433222222111111 4 17),
([w10,w1,w2,w0,w3,w4],dL 0x9508a08b002001,dS 0x702090e010c0b060d110a,pH 0x544222111122211 5 11),
([w18,w1,w2,w0,w3,w4],dL 0x70360d0050001,dS 0x13070f0d0a01150e03060c11,pH 0x322312111144141 5 12),
([w1,w2,w0,w3,w9,w4],dL 0x10611003d001,dS 0x161c0f132a0208010d0c0b04070a11,pH 0x221333422311111 4 15),
([w41,w1,w2,w0,w3,w4],dL 0x15114f008016001,dS 0x703010913020c06110d0b0a,pH 0x242524111121221 5 12),
([w39,w1,w2,w0,w3,w4],dL 0x23048173054001,dS 0x1113070f0c0b171001020e0a06,pH 0x223213111114441 5 13),
([w1,w12,w2,w0,w3,w4],dL 0x5185006050002,dS 0x10190b050d160e0a11020c0701,pH 0x422112112233333 5 13),
([w17,w1,w2,w0,w3,w4],dL 0x18e00403f05008b,dS 0x11170a080b1c19020e0c0d0701,pH 0x522112333311213 5 13),
([w1,w16,w2,w0,w3,w4],dL 0x2700d00500418f0160dc011002,dS 0x70e130502040d0b0c110a0601,pH 0x433111141122222 9 13),
([w1,w2,w0,w3,w8,w4],dL 0x808b19803d0e8014003,dS 0x1113060d1a0e0919020b0c0a01,pH 0x144313111122222 7 13),
([w27,w1,w2,w0,w3,w4],dL 0x50041d81c800201d008,dS 0x13120e060d0b191c16110c020a01,pH 0x141313222211132 7 14),
([w37,w1,w2,w0,w3,w4],dL 0x270f119f05d00d08b,dS 0xb1a120711130d100e15060c010a02,pH 0x252111333312113 6 15),
([w1,w19,w2,w0,w3,w4],dL 0x40f2022054002,dS 0x1513070d020b1a1c0c110a050601,pH 0x244211211233333 5 14),
([w66,w1,w2,w0,w3,w4],dL 0x50f906205408b,dS 0x161307020c170e0d110a0b090601,pH 0x224211333321113 5 14),
([w1,w2,w14,w0,w3,w4],dL 0x2703e0160361a0063050,dS 0x150b1a1c0508130a020d060c1101,pH 0x511411351422222 7 14),
([w45,w1,w2,w0,w3,w4],dL 0x1a500d070050008,dS 0xa061a0b100c0d07021101,pH 0x122512333312413 5 11),
([w1,w2,w7,w0,w3,w4],dL 0x36054050072,dS 0x17130e070f090d0b02061101,pH 0x322243312411111 4 12),
([w1,w2,w0,w23,w3,w4],dL 0xd0fc082054016,dS 0xd10160e072a190c060b02110a01,pH 0x222444211433333 5 14),
([w71,w1,w2,w0,w3,w4],dL 0xff027088054008,dS 0x70c0f0d150e060a0b051101,pH 0x221215333321113 5 12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK p13_T p13_K p13_P 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I8 : LevelN p13_R p13_T 8 p13_D8 := levelStep p13_B p13_W p13_Q p13_I7 (chunks 64 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D9 : List StD := [
([w1,w2,w0,w3,w4],dL 0x54050001,dS 0x130e07050d0b0c0206110a01,pH 0x3223121111 3 12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C9x0 : levelOK p13_T p13_K p13_P 8 (p13_D8.map Prod.fst) ((p13_D9.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I9 : LevelN p13_R p13_T 9 p13_D9 := levelStep p13_B p13_W p13_Q p13_I8 (chunks 64 p13_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C9x0
  ))
theorem p13_L : LowN p13_R p13_T 10 := lowSearch p13_B p13_I9 (by decide +kernel)
def p19_T : Nat := 0xe8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0
def p19_R : List Nat := [0, 1, 2, 3]
def p19_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,3,11)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
theorem p19_S0 : SliceN p19_R p19_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p19_B p4_B p4_L (by decide +kernel)
def p19_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨p19_S0,by simp⟩
noncomputable def p19_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p19_P : List (Nat × Nat) := [(4,6),(4,5),(9,11),(10,11),(2,6),(1,5)]
noncomputable def p19_K : List CutV := p19_C.map (mkCut p19_Z)
theorem p19_W : ∀ c ∈ p19_K, CutP p19_R p19_T c := cutsGood p19_Y (by decide +kernel)
theorem p19_Q : p19_P.all (sepOK p19_T) = true := by decide +kernel
def p19_D3 : List StD := []
theorem p19_I3 : LevelN p19_R p19_T 3 p19_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p19_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x60503010402,pH 0x111111 1 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C4x0 : levelOK p19_T p19_K p19_P 3 (p19_D3.map Prod.fst) ((p19_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p19_I4 : LevelN p19_R p19_T 4 p19_D4 := levelStep p19_B p19_W p19_Q p19_I3 (chunks 64 p19_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C4x0
  ))
theorem p19_L : LowN p19_R p19_T 5 := lowSearch p19_B p19_I4 (by decide +kernel)
def p20_T : Nat := 0xe8c8e8c8e8c8e8c8e8c8e8c8e8c8e8c8
def p20_R : List Nat := [0, 1, 2, 3]
def p20_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,5,13)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
theorem p20_S0 : SliceN p20_R p20_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p20_B p4_B p4_L (by decide +kernel)
def p20_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨p20_S0,by simp⟩
noncomputable def p20_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p20_P : List (Nat × Nat) := [(4,6),(12,13),(1,3),(2,3),(2,6),(9,13)]
noncomputable def p20_K : List CutV := p20_C.map (mkCut p20_Z)
theorem p20_W : ∀ c ∈ p20_K, CutP p20_R p20_T c := cutsGood p20_Y (by decide +kernel)
theorem p20_Q : p20_P.all (sepOK p20_T) = true := by decide +kernel
def p20_D3 : List StD := []
theorem p20_I3 : LevelN p20_R p20_T 3 p20_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p20_D4 : List StD := [
([w1,w2,w0,w3],dL 0x1,dS 0x60503010402,pH 0x111111 1 6)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C4x0 : levelOK p20_T p20_K p20_P 3 (p20_D3.map Prod.fst) ((p20_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p20_I4 : LevelN p20_R p20_T 4 p20_D4 := levelStep p20_B p20_W p20_Q p20_I3 (chunks 64 p20_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C4x0
  ))
theorem p20_L : LowN p20_R p20_T 5 := lowSearch p20_B p20_I4 (by decide +kernel)
def p21_T : Nat := 0xfc88fc88fc88fc88fc88fc88fc88fc88
def p21_R : List Nat := [0, 1, 2, 3]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := []
theorem p21_Y : ∀ s ∈ p21_Z, SliceN p21_R p21_T s := by intro s h; cases h
noncomputable def p21_C : List (Nat × List (Nat × Nat × Nat)) := []
def p21_P : List (Nat × Nat) := [(8,10),(1,3),(2,3),(3,6),(2,7),(5,12),(2,10),(3,5),(1,7),(6,10),(0,12)]
noncomputable def p21_K : List CutV := p21_C.map (mkCut p21_Z)
theorem p21_W : ∀ c ∈ p21_K, CutP p21_R p21_T c := cutsGood p21_Y (by decide +kernel)
theorem p21_Q : p21_P.all (sepOK p21_T) = true := by decide +kernel
def p21_D2 : List StD := []
theorem p21_I2 : LevelN p21_R p21_T 2 p21_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p21_D3 : List StD := [
([w1,w2,w0,w3],dL 0x0,dS 0xb0a090806050407030201,pH 0x111111 0 11)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p21_C3x0 : levelOK p21_T p21_K p21_P 2 (p21_D2.map Prod.fst) ((p21_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p21_I3 : LevelN p21_R p21_T 3 p21_D3 := levelStep p21_B p21_W p21_Q p21_I2 (chunks 64 p21_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C3x0
  ))
theorem p21_L : LowN p21_R p21_T 4 := lowSearch p21_B p21_I3 (by decide +kernel)
def p18_T : Nat := 0xfee8fc88fee8fc88fee8fc88fee8fc88
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,5,21)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
theorem p18_S0 : SliceN p18_R p18_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p18_B p19_B p19_L (by decide +kernel)
theorem p18_S1 : SliceN p18_R p18_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) p18_B p14_B p14_L (by decide +kernel)
theorem p18_S2 : SliceN p18_R p18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) p18_B p7_B p7_L (by decide +kernel)
theorem p18_S3 : SliceN p18_R p18_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p18_B p9_B p9_L (by decide +kernel)
theorem p18_S4 : SliceN p18_R p18_T (0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]) := mkSlice (w:=16) p18_B p12_B p12_L (by decide +kernel)
theorem p18_S5 : SliceN p18_R p18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p18_B p20_B p20_L (by decide +kernel)
theorem p18_S6 : SliceN p18_R p18_T (0x22222222222222222222222222222222,4,[2, 3, 4]) := mkSlice (w:=1) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S7 : SliceN p18_R p18_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S8 : SliceN p18_R p18_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel)
theorem p18_S9 : SliceN p18_R p18_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p18_B p21_B p21_L (by decide +kernel)
theorem p18_S10 : SliceN p18_R p18_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S11 : SliceN p18_R p18_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S12 : SliceN p18_R p18_T (0x33330000333300003333000033330000,4,[0, 2, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
def p18_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0x22222222222222222222222222222222,4,[2, 3, 4]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0x55550000555500005555000055550000,4,[1, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0x33330000333300003333000033330000,4,[0, 2, 3])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨p18_S0,p18_S1,p18_S2,p18_S3,p18_S4,p18_S5,p18_S6,p18_S7,p18_S8,p18_S9,p18_S10,p18_S11,p18_S12,by simp⟩
noncomputable def p18_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x4,dC 0x5030202010105,dC 0x6,dC 0x2010402,dC 0x5030302010105,dC 0x5040202010105,dC 0x2010107,dC 0x3020101,dC 0x5040204030102010105,dC 0x3020201,dC 0x2010207,dC 0x4030205040202010105,dC 0x3020301,dC 0x2010108,dC 0x6030105040202010105,dC 0x6030205040202010105,dC 0x9,dC 0x3010402,dC 0x5040302010105,dC 0x2010105,dC 0x4010402,dC 0xa,dC 0xb,dC 0x302010b,dC 0x302020b,dC 0x2010106,dC 0x4030102010105,dC 0x5020202010104030105,dC 0x201010c,dC 0x2010103,dC 0x4030202010105,dC 0x4030106,dC 0x2010104030305,dC 0x3020401,dC 0x2010109,dC 0x2010104030405,dC 0x3010304,dC 0x2010208,dC 0x2010204010305,dC 0x4010101,dC 0x4010103010304,dC 0x7,dC 0x3010301,dC 0x5040402010205,dC 0x3020102,dC 0x3020302,dC 0x2010205,dC 0x4010104,dC 0x4030302,dC 0x5040302010205,dC 0x3020402,dC 0x2010206,dC 0x5020202010204030105,dC 0x201020c,dC 0x4030102010205,dC 0x5,dC 0x3020202,dC 0x2010203,dC 0x4030202010205,dC 0x2010204030305,dC 0x2010204030405,dC 0x2010306,dC 0x4030102010305,dC 0x2010303,dC 0x4030202010305,dC 0x2010307,dC 0x2010407,dC 0x2010305,dC 0x5040202010405,dC 0x2010408,dC 0x2010405,dC 0x2010406,dC 0x3020104,dC 0x4030102010405,dC 0x2010403,dC 0x4030202010405,dC 0x3010201,dC 0x5020203010105,dC 0x3020206,dC 0x301020b,dC 0x8,dC 0x5040203010105,dC 0x3010105,dC 0x3010205,dC 0x4020101,dC 0x5020203010305,dC 0x3010305,dC 0x5040203010405,dC 0x3010405,dC 0x5020204010105,dC 0x4010105,dC 0x4010205,dC 0x5020204010305,dC 0x4010305,dC 0x2010401,dC 0x3010306,dC 0x4010405,dC 0x4030401,dC 0x5040203020105,dC 0x3020105,dC 0x3020205,dC 0x3020305,dC 0x4020406,dC 0xd,dC 0x5040203020405,dC 0x3020405,dC 0x3020203,dC 0x3020409,dC 0x4030203020405,dC 0x4030103020409,dC 0x5010204020105,dC 0x5010304020105,dC 0x5030204020105,dC 0x5030304020105,dC 0x4020105,dC 0x4020205,dC 0x4020305,dC 0x4020405,dC 0x5010204030105,dC 0x5010304030105,dC 0x4030105,dC 0x5020204030105,dC 0x6010105020204030105,dC 0x6010205020204030105,dC 0x5020304030105,dC 0xc,dC 0x4030205,dC 0x5020404030205,dC 0x4030109,dC 0x4020303,dC 0x5020304030205,dC 0x4030305,dC 0x5020204030405,dC 0x4030405]
def p18_P : List (Nat × Nat) := [(2,3),(3,6),(20,21),(24,25),(3,5),(8,10),(20,22),(17,21),(8,12),(5,21),(9,25),(9,11),(6,22),(6,10),(2,10),(4,12),(0,12),(17,25),(1,3),(9,10),(3,17),(6,7),(18,19),(18,22),(5,7),(17,19),(18,26),(5,13),(12,20),(1,13),(1,21),(10,18),(1,25),(9,13),(0,3),(4,7),(6,14),(3,9),(5,12),(2,7),(20,28),(2,11),(1,7),(24,28),(24,26),(0,10),(4,21),(10,24),(4,22)]
noncomputable def p18_K : List CutV := p18_C.map (mkCut p18_Z)
theorem p18_W : ∀ c ∈ p18_K, CutP p18_R p18_T c := cutsGood p18_Y (by decide +kernel)
theorem p18_Q : p18_P.all (sepOK p18_T) = true := by decide +kernel
def p18_D3 : List StD := []
theorem p18_I3 : LevelN p18_R p18_T 3 p18_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([w1,w0,w46,w31,w4],dL 0x0,dS 0xf0e080a060b03070d0c04,pH 0x1111111111 0 11),
([w84,w1,w2,w0,w31],dL 0x0,dS 0x4060b07030a0c08090d,pH 0x1111111111 0 10),
([w125,w1,w0,w31,w4],dL 0x0,dS 0x100e0a0c0b09030d040706,pH 0x1111111111 0 11),
([w1,w2,w0,w31,w51],dL 0x0,dS 0xb08100e0a060904070d0c03,pH 0x1111111111 0 12),
([w509,w1,w2,w0,w31],dL 0x0,dS 0x4060b07030a0c08090d,pH 0x1111111111 0 10),
([w1,w2,w0,w31,w510],dL 0x0,dS 0xb0809110e0a0604070d0c03,pH 0x1111111111 0 12),
([w70,w1,w0,w46,w3],dL 0x0,dS 0x6070e080905040d0f0a0b0301,pH 0x1111111111 0 13),
([w1,w2,w0,w3,w511],dL 0x0,dS 0xb0809110e011404070d0603,pH 0x1111111111 0 12),
([w25,w1,w0,w46,w4],dL 0x0,dS 0x1a0a0b181612070e060f010804,pH 0x1111111111 0 13),
([w1,w2,w30,w512,w3],dL 0x0,dS 0x181a170e120509010806,pH 0x1111111111 0 10),
([w513,w1,w2,w30,w3],dL 0x0,dS 0x1a1012080917060105,pH 0x1111111111 0 9),
([w1,w30,w0,w46,w3],dL 0x0,dS 0x80e191a0a0b0c16170f061201,pH 0x1111111111 0 13),
([w1,w2,w0,w514,w3],dL 0x0,dS 0x80e0a0b1a1917160c0f010612,pH 0x1111111111 0 13),
([w515,w1,w2,w0,w3],dL 0x0,dS 0x100c0b0719120908160d0601,pH 0x1111111111 0 12),
([w516,w1,w2,w0,w3],dL 0x0,dS 0x100e040a080b090c070103,pH 0x1111111111 0 11),
([w517,w1,w0,w46,w3],dL 0x0,dS 0x6070e080905040d0f0a0b0301,pH 0x1111111111 0 13),
([w1,w0,w46,w211,w3],dL 0x0,dS 0x1a250a0b19170c160f061201,pH 0x1111111111 0 12),
([w518,w2,w0,w3,w51],dL 0x0,dS 0xf1d0d2c09110e0407060103,pH 0x1111111111 0 12),
([w519,w2,w0,w3,w51],dL 0x0,dS 0xb0a2c09110e2b05040c070103,pH 0x1111111111 0 13)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK p18_T p18_K p18_P 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I4 : LevelN p18_R p18_T 4 p18_D4 := levelStep p18_B p18_W p18_Q p18_I3 (chunks 64 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([w1,w2,w14,w0,w31,w4],dL 0xc00b00a,dS 0x80f0e1009060b030a070c,pH 0x111311111111111 3 11),
([w1,w2,w0,w31,w42,w4],dL 0xf00d00e,dS 0xf080e060b1009040a07030c,pH 0x312111111122111 3 12),
([w45,w1,w2,w0,w31,w4],dL 0x10,dS 0x11090c10080a0f03040b0706,pH 0x111111111111111 1 12),
([w105,w1,w2,w0,w31,w4],dL 0x0,dS 0x1110080d0c0f090b040a060307,pH 0x111111111111111 0 13),
([w1,w2,w520,w0,w31,w4],dL 0x1200b00a,dS 0x80f0e1009060b030a070c,pH 0x111311111111111 3 11),
([w1,w2,w0,w31,w521,w4],dL 0x1300d00e,dS 0xf080e060b1009040a07030c,pH 0x311111111122111 3 12),
([w522,w1,w2,w0,w31,w4],dL 0x0,dS 0x11090f0d0c10080a030b070406,pH 0x111111111111111 0 13),
([w523,w1,w2,w0,w31,w4],dL 0x0,dS 0x1110080d0c0f090b040a060307,pH 0x111111111111111 0 13),
([w70,w1,w2,w14,w0,w3],dL 0x1901b00a,dS 0x80f0e10090b03010a0706,pH 0x111111222211211 3 11),
([w70,w1,w2,w0,w3,w42],dL 0x1901c,dS 0xf08100e13040b090a07060301,pH 0x111111111121111 2 13),
([w45,w70,w1,w2,w0,w3],dL 0x0,dS 0x11090f0410080a0706030b01,pH 0x111111111111111 0 12),
([w105,w70,w1,w2,w0,w3],dL 0x0,dS 0x111008030f090b0607040a01,pH 0x111111111111111 0 12),
([w1,w2,w0,w524,w3,w4],dL 0x1901b00b01d,dS 0xb10080e0c0a01140407060d03,pH 0x332111111111111 4 13),
([w28,w1,w0,w46,w3,w4],dL 0x1f01d011,dS 0xe0403140c010d060f080a,pH 0x111121111131111 3 11),
([w84,w28,w1,w2,w0,w3],dL 0x19011020,dS 0x403140f0c010b0608090d0a,pH 0x121211211111111 3 12),
([w525,w1,w2,w0,w3,w4],dL 0x1901c00d,dS 0xe07040f080c100906030a0113,pH 0x221211111131111 3 13),
([w125,w28,w1,w0,w3,w4],dL 0x21,dS 0xd1501140c0b04030a0f13090706,pH 0x111111111111111 1 14),
([w28,w1,w2,w0,w3,w51],dL 0x19023011021,dS 0xb0803140c010d040f060a09,pH 0x211121121142111 4 12),
([w526,w1,w2,w0,w3,w4],dL 0x25,dS 0x11100c0f0904030b080a0607,pH 0x111111111111111 1 12),
([w74,w2,w30,w0,w3],dL 0x202c02b,dS 0x101b191a16170a0409130f180106,pH 0x1112211111 3 14),
([w25,w1,w2,w14,w0,w4],dL 0x30,dS 0xb1d091a1916120e081c130a0f10010604,pH 0x111111111111111 1 17),
([w25,w45,w1,w2,w0,w4],dL 0x31,dS 0x1a040108121e070b0a190910060f,pH 0x111111111111111 1 14),
([w1,w2,w30,w0,w527,w3],dL 0x19,dS 0x100b0819160c1a170f010612,pH 0x111111111111111 1 12),
([w309,w1,w2,w30,w0,w3],dL 0x0,dS 0x1f080b1a17090a1210160f190106,pH 0x111111111111111 0 14),
([w1,w2,w30,w0,w3,w528],dL 0x0,dS 0xf0a0b201a160c08191b1709120106,pH 0x111111111111111 0 15),
([w202,w1,w2,w30,w0,w3],dL 0x35034,dS 0x210a0f0b191b08010906,pH 0x111112111111121 2 10),
([w1,w2,w30,w14,w0,w3],dL 0x1902b00a030,dS 0xe10091a16170c0b180a060f01,pH 0x111114222111111 4 13),
([w1,w2,w30,w0,w3,w42],dL 0x19,dS 0xf080e1910170c0b09160a1a1c0106,pH 0x111111111111111 1 15),
([w45,w1,w2,w30,w0,w3],dL 0x0,dS 0x11091a0f03100812160a0b190106,pH 0x111111111111111 0 14),
([w105,w1,w2,w30,w0,w3],dL 0x2b036,dS 0x1108191a16030f09100b0a061301,pH 0x111111111111111 2 14),
([w1,w6,w0,w46,w3,w4],dL 0x38037029,dS 0xe0a0617141603080f120c01,pH 0x131222312211111 3 12),
([w140,w1,w2,w0,w3,w4],dL 0x19039037,dS 0x19121406030c010f09080a10,pH 0x211211211131111 3 12),
([w84,w1,w2,w6,w0,w3],dL 0x19039,dS 0x1906030c140b0d17100f120809010a,pH 0x111111111111211 2 15),
([w1,w2,w529,w0,w3,w4],dL 0x3b019,dS 0xe221a1917140b1310160a091c0c01,pH 0x111111111111111 2 15),
([w1,w2,w6,w0,w3,w51],dL 0x19,dS 0xb0810221906160314090d0f0c010a1c,pH 0x111111111111111 1 16),
([w1,w2,w530,w0,w3,w4],dL 0x0,dS 0x1c0f1a19160a0b10130809060104,pH 0x111111111111111 0 14),
([w22,w1,w0,w46,w3,w4],dL 0x41,dS 0xe23010c030a06080d120f18,pH 0x111111111111111 1 12),
([w84,w22,w1,w2,w0,w3],dL 0x0,dS 0x182301060c030b120f0a08090d,pH 0x111111111111111 0 13),
([w22,w125,w1,w0,w3,w4],dL 0x43,dS 0xa1707241a030c0b0113090f1c06,pH 0x111111111111111 1 14),
([w22,w1,w2,w0,w3,w51],dL 0x0,dS 0xb080723010c0306220a1c090d0f,pH 0x111111111111111 0 14),
([w1,w2,w0,w310,w3,w4],dL 0x4b,dS 0x818060123121904250a0c0d03,pH 0x111111111111111 1 13),
([w10,w1,w0,w46,w3,w4],dL 0x0,dS 0xb0e230c0306010d180a0f0812,pH 0x111111111111111 0 13),
([w84,w10,w1,w2,w0,w3],dL 0x0,dS 0x12230c0306010b0f1810080d090a,pH 0x111111111111111 0 14),
([w1,w531,w2,w0,w3,w4],dL 0x0,dS 0x1b1006040a0d0f0c0918130301,pH 0x111111111111111 0 13),
([w10,w1,w2,w0,w3,w51],dL 0x2304e,dS 0xb08230601040c030d0f0a1009,pH 0x111111111111111 2 13),
([w532,w1,w2,w0,w3,w4],dL 0x0,dS 0x10d0f180b10080604030a13,pH 0x111111111111111 0 12),
([w1,w75,w0,w3,w8,w4],dL 0x50,dS 0x1005092608160f1806010b0a1904,pH 0x111111111111111 1 14),
([w1,w2,w0,w3,w533,w4],dL 0x53019052050,dS 0xb1008180e0a07190503160609010d04,pH 0x311221111111111 4 16),
([w534,w1,w2,w0,w3,w4],dL 0x0,dS 0xd160f0a0b180919060104,pH 0x111111111111111 0 11),
([w1,w2,w0,w313,w8,w4],dL 0x52,dS 0x72627020f06180a09010d1c04,pH 0x111111111111111 1 13),
([w535,w1,w2,w0,w3,w4],dL 0x0,dS 0x1b16060a0d1c0f09180401,pH 0x111111111111111 0 11),
([w536,w1,w2,w0,w3,w4],dL 0x0,dS 0xd0b0f0a1c090806190103,pH 0x111111111111111 0 11),
([w1,w216,w0,w3,w8,w4],dL 0x50,dS 0x1026160f0b0a060109081304,pH 0x111111111111111 1 12),
([w537,w1,w2,w0,w3,w4],dL 0x0,dS 0xd10080a0f181303040b06,pH 0x111111111111111 0 11),
([w1,w2,w0,w196,w8,w4],dL 0x52,dS 0x1326100f090a18060d0103,pH 0x111111111111111 1 11),
([w17,w1,w2,w3,w51],dL 0x3071023,dS 0x292d0e041c0c2c220a0d0610030901,pH 0x1121111111 3 15),
([w538,w1,w0,w46,w3,w4],dL 0x7e01d011,dS 0x250403140c08010d060f0a,pH 0x111121111131111 3 11),
([w1,w0,w46,w177,w3,w4],dL 0x7f037029,dS 0xa1a06250819170314160f120c01,pH 0x131111222111111 3 14),
([w539,w1,w0,w46,w3,w4],dL 0x0,dS 0xb0e2301060c030a080d12180f,pH 0x111111111111111 0 13),
([w209,w1,w0,w46,w3,w4],dL 0x0,dS 0xb0e230c0306010d180a0f0812,pH 0x111111111111111 0 13),
([w1,w2,w0,w3,w51,w540],dL 0x19,dS 0xd0f09110e292c0406070c03,pH 0x111111111111111 1 12),
([w541,w1,w2,w0,w3,w51],dL 0x0,dS 0x29182f030a01070d220c091c060f,pH 0x111111111111111 0 14),
([w1,w2,w0,w3,w51,w542],dL 0x0,dS 0xa2c180e063004292d100d07010903,pH 0x111111111111111 0 15),
([w543,w1,w2,w0,w3,w51],dL 0x86085,dS 0x310a07040d06092d0f0103,pH 0x211111111112111 2 11)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK p18_T p18_K p18_P 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I5 : LevelN p18_R p18_T 5 p18_D5 := levelStep p18_B p18_W p18_Q p18_I4 (chunks 64 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([w1,w2,w68,w3,w4],dL 0x5003004001,dS 0xb0a0709080604030502,pH 0x4332221111 4 10),
([w89,w1,w2,w3,w4],dL 0x8007006004001,dS 0xb0a04080906070103,pH 0x5221113341 5 9),
([w1,w2,w0,w3,w31,w4],dL 0x11006001009004,dS 0xc0b070804090a0306,pH 0x221241111133311 5 9),
([w1,w2,w0,w31,w4],dL 0x9004001,dS 0x910080f0b07040a030c,pH 0x3312221111 3 10),
([w124,w1,w2,w0,w4],dL 0x16015014004001,dS 0xa0b03120f1007060104,pH 0x5221113341 5 10),
([w70,w1,w2,w0,w3],dL 0x1901801a004001,dS 0x910080f040a0b06070103,pH 0x1221113541 5 11),
([w28,w1,w2,w14,w0,w3,w4],dL 0x1e00a01101d00b,dS 0xb080e100903140c0106,pH 0x322211532211111111111 5 10),
([w28,w1,w2,w0,w3,w42,w4],dL 0x601100e02200d021,dS 0xf080e03140c0104100609,pH 0x151311315121512215111 6 11),
([w45,w28,w1,w2,w0,w3,w4],dL 0x2401d010011,dS 0xb11091203140c011008060a,pH 0x113411222222211111122 4 12),
([w105,w28,w1,w2,w0,w3,w4],dL 0x6027026021025,dS 0x11140c010f090b0604,pH 0x322432111111111211211 5 9),
([w74,w2,w6,w0,w3,w4],dL 0x2902a028002001,dS 0x1a191716030b1009040f18130d010c,pH 0x441222333112111 5 15),
([w25,w1,w2,w0,w3,w4],dL 0x602802e02902f02d002,dS 0x101808130a0b09010406,pH 0x331222111131765 7 10),
([w1,w2,w30,w0,w3],dL 0x3201902d02b033002,dS 0x9101216170a080b190f0106,pH 0x1554231113 6 12),
([w1,w2,w6,w14,w0,w3,w4],dL 0x103a02900a037030,dS 0xe100906160314180d0c0f01,pH 0x422211111133331111111 6 12),
([w1,w2,w6,w0,w3,w42,w4],dL 0x3c03d03e,dS 0xf080e221a1306170314191016091c0c01,pH 0x211112331111111111111 3 17),
([w45,w1,w2,w6,w0,w3,w4],dL 0x3f031037029,dS 0x11090a060314100819160d0f0c01,pH 0x122332112133213211211 4 14),
([w105,w1,w2,w6,w0,w3,w4],dL 0x600104003d036,dS 0x11080603140f090d0c100b1301,pH 0x322112112111211211111 5 13),
([w22,w1,w2,w14,w0,w3,w4],dL 0x4200b00a,dS 0xf0e100923010c030b07180a06,pH 0x111311111122222222211 3 13),
([w22,w1,w2,w0,w3,w42,w4],dL 0x4404300d00e,dS 0xa0f080e23011c220c030b07100609,pH 0x311313131322222221111 4 15),
([w45,w22,w1,w2,w0,w3,w4],dL 0x10045,dS 0x11090f23010c0310080a0b0607,pH 0x111111222222211111122 2 13),
([w105,w22,w1,w2,w0,w3,w4],dL 0x25046,dS 0x11100823010c030f090b0a0706,pH 0x111111222222211111122 2 13),
([w1,w2,w0,w3,w126,w4],dL 0x49006048004002,dS 0xa250f0c0b090819040d0306,pH 0x331341222211111 5 12),
([w10,w1,w2,w14,w0,w3,w4],dL 0x104d04c04b030,dS 0xe100923060103180d0f,pH 0x422211332211211111111 5 10),
([w10,w1,w2,w0,w3,w42,w4],dL 0x4f00100603c04e,dS 0xf080e0a13230306010b0c250d1009,pH 0x111111111122222211111 5 15),
([w45,w10,w1,w2,w0,w3,w4],dL 0x3104b049,dS 0xb11090a2303060110080c0d0f,pH 0x112111331333311111113 3 13),
([w105,w10,w1,w2,w0,w3,w4],dL 0x3604e,dS 0x11102306010f09180c040d250b,pH 0x111111221222211111122 2 13),
([w1,w2,w75,w0,w3,w4],dL 0x2902d006051001,dS 0x160a0b0f191018090401,pH 0x233254443111111 5 10),
([w1,w2,w0,w3,w313,w4],dL 0x5500e001054006,dS 0xa18220c0d09071c010604,pH 0x521111442133311 5 11),
([w53,w1,w2,w0,w3,w8,w4],dL 0x5205005402d,dS 0xb250c030d0a0f06,pH 0x121221121111113332111 4 8),
([w1,w2,w0,w504,w3],dL 0x5802d002054,dS 0x1207090608010f03,pH 0x1111312224 4 8),
([w1,w2,w116,w0,w3,w4],dL 0x5905400302d001,dS 0xa1a130b0f100c0301,pH 0x433542222111111 5 9),
([w1,w2,w0,w3,w156,w4],dL 0x5b02d006002,dS 0x291013050c0b0a070809010604,pH 0x411222333211111 4 13),
([w1,w2,w505,w0,w3,w4],dL 0x5d054014001,dS 0x9270d0a180c08100f0301,pH 0x232423423111111 4 11),
([w1,w2,w216,w0,w3,w4],dL 0x2900606002d001,dS 0x1a191816090f100a0b13080401,pH 0x331324221111111 5 13),
([w74,w17,w1,w2,w0,w3,w4],dL 0x6302d054062,dS 0xb0d061201100a13,pH 0x244322121144321111111 4 8),
([w74,w1,w2,w0,w3,w8,w4],dL 0x5002d,dS 0xd07180c010f060a0b0809,pH 0x111111111111111111111 2 11),
([w1,w255,w2,w0,w3],dL 0x6501905402d014002,dS 0x912080b070a060f0301,pH 0x2232551116 6 10),
([w1,w2,w0,w3,w114,w4],dL 0x6600602d,dS 0x1a050c0b0a1304250108090603,pH 0x331222111111111 3 13),
([w1,w2,w0,w506,w3],dL 0x6b06a02d019003004,dS 0xb040607030d08090c,pH 0x3221114351 6 9),
([w1,w2,w0,w3,w196,w4],dL 0x6c00100e006054,dS 0xa291a1318041c220c090d10010603,pH 0x512222311234111 5 15),
([w17,w1,w2,w0,w3,w8,w4],dL 0x6e052054,dS 0x10250d0408060a0f0b0301,pH 0x111111111111111111131 3 11),
([w17,w1,w2,w3,w42,w4],dL 0x7006f00e003006,dS 0x290b1a130e041c0c2c0822180d0603091001,pH 0x211324321111111 5 18),
([w2,w57,w0,w3,w4],dL 0x72014004002,dS 0xa0b1204100c070103,pH 0x3431112221 4 9),
([w239,w2,w0,w3,w4],dL 0x73014004001,dS 0xa0b0f041006070301,pH 0x3432221111 4 9),
([w1,w2,w507,w3,w4],dL 0x74014003004,dS 0xa0d1208070e0913,pH 0x3221114321 4 8),
([w191,w1,w2,w3,w4],dL 0x75014004006,dS 0xa0d1206180f0c0908,pH 0x3224321111 4 9),
([w258,w1,w2,w0,w3],dL 0x1406b01902d,dS 0xf100406010b07030d,pH 0x4111113222 4 9),
([w314,w1,w2,w0,w3,w8,w4],dL 0x5002d,dS 0xd071809010c060b0a0f2208,pH 0x111111111111111111111 2 12),
([w315,w1,w2,w0,w3,w8,w4],dL 0x5002d,dS 0xd070f180301040a0b0809,pH 0x111111111111111111111 2 11),
([w1,w2,w72,w0,w3,w8,w4],dL 0x52054,dS 0xb12092d04160d0a0f25060103,pH 0x111111111111111111111 2 13),
([w257,w1,w2,w0,w3,w8,w4],dL 0x52054,dS 0x1218090e0d0408060a0b0301,pH 0x111111111111111111111 2 12),
([w2,w0,w34,w3,w4],dL 0x7a014002006,dS 0xe0d1203080a01180f,pH 0x3221114321 4 9),
([w240,w2,w0,w3,w4],dL 0x7b014006001,dS 0xd0818040a100f0301,pH 0x3224321111 4 9),
([w1,w2,w0,w46,w3,w4],dL 0x107d01400600a,dS 0xe12040a08180d0f0103,pH 0x341221112211511 5 10),
([w1,w0,w46,w3,w4],dL 0x7d014006,dS 0xe010c03060a1218080d0f,pH 0x2321113211 3 11),
([w78,w1,w0,w3,w4],dL 0x80014006004,dS 0xa0d1208060f09070c,pH 0x3224321111 4 9),
([w84,w1,w2,w0,w3],dL 0x19014081,dS 0x18010c03060b0f12080a090d,pH 0x1212111113 3 12),
([w125,w1,w2,w0,w3,w4],dL 0x6f00108305400e003,dS 0x9041310030a0d18010f,pH 0x311432422146215 6 10),
([w1,w2,w0,w3,w51],dL 0x84019023054003,dS 0x292c0722010c0a0d1c03060f09,pH 0x3114214531 5 13),
([w1,w2,w508,w0,w3,w4],dL 0x1088014003046,dS 0xb0a2d040c0d1801060f03,pH 0x322411111211151 5 11)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK p18_T p18_K p18_P 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I6 : LevelN p18_R p18_T 6 p18_D6 := levelStep p18_B p18_W p18_Q p18_I5 (chunks 64 p18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
([w28,w1,w2,w0,w3,w4],dL 0x14006003002004017001,dS 0x910080f14010b070403060a,pH 0x221233111111111 7 12),
([w1,w2,w6,w0,w3,w4],dL 0x1400300603202d004001002,dS 0x81a1716140a0b1009190f0c01,pH 0x551111443211232 8 13),
([w22,w1,w2,w0,w3,w4],dL 0x204700102d,dS 0x910080f2301030a0b0607,pH 0x331111222222222 4 11),
([w10,w1,w2,w0,w3,w4],dL 0x1400600300100404a002,dS 0x91023010b0c19040f18030d,pH 0x221233111111111 7 12),
([w53,w1,w2,w0,w3,w4],dL 0x605402d056001,dS 0xb090d0f021c0318060401190a,pH 0x225233111111311 5 13),
([w1,w2,w0,w24,w3,w4],dL 0x5700600102d054002,dS 0x22100702081606030f,pH 0x211224321211514 6 9),
([w54,w1,w2,w0,w3,w4],dL 0x2d05a054001,dS 0x100d0f18280316010c120b,pH 0x222324111111411 4 11),
([w18,w1,w2,w0,w3,w4],dL 0x105405c02d002,dS 0x22080f0428030b060110070d,pH 0x334222111111111 5 12),
([w101,w1,w2,w0,w3,w4],dL 0x2d05e054001,dS 0xd0f27030104180c0b22,pH 0x222342111114111 4 10),
([w1,w2,w0,w3,w9,w4],dL 0x600105f02d054002,dS 0x1c12270b070918040d06,pH 0x145412313312115 6 10),
([w74,w1,w2,w0,w3,w4],dL 0x602d061054001,dS 0x9100d06182a010b0f0408130a,pH 0x332344111114111 5 13),
([w41,w1,w2,w0,w3,w4],dL 0x6402d002054,dS 0xb08012a0f040906,pH 0x111333222221222 4 8),
([w1,w12,w2,w0,w3,w4],dL 0x5406700602d004,dS 0xb0809060518070125040d16,pH 0x433111111122211 5 12),
([w1,w2,w0,w20,w3,w4],dL 0x100606805402d004003,dS 0x12100503070b0d041819010f,pH 0x411112226233332 7 12),
([w50,w1,w2,w0,w3,w4],dL 0x6905400302d004,dS 0x90d2b1806010f,pH 0x433111222111111 5 7),
([w17,w1,w2,w0,w3,w4],dL 0x300105406d02d006,dS 0xb0f2b04010c0d061810030a,pH 0x311321321211211 6 12),
([w1,w16,w2,w0,w3,w4],dL 0x7602d054004,dS 0xb08260f060409130301,pH 0x222111121133311 4 10),
([w1,w2,w0,w3,w8,w4],dL 0x600107702d004054,dS 0xa082526040c0b18030f09060d01,pH 0x442411212233332 6 14),
([w27,w1,w2,w0,w3,w4],dL 0x607707805402d004,dS 0x910122e04070b060d1801,pH 0x443111222111111 6 11),
([w37,w1,w2,w0,w3,w4],dL 0x107707905402d014,dS 0x2e180113070d0f0b0409,pH 0x131413412212111 6 10),
([w1,w2,w14,w0,w3,w4],dL 0x400100207c014006,dS 0xe1009010c03060a1218080d0f,pH 0x211121321132111 6 13),
([w1,w2,w0,w3,w42,w4],dL 0x4002001014006054082003,dS 0xe13251c220c030a0d01061009,pH 0x134151213121541 8 13),
([w45,w1,w2,w0,w3,w4],dL 0x87006054,dS 0x1109010c030610080a0d120f,pH 0x122312312121222 3 12),
([w105,w1,w2,w0,w3,w4],dL 0x6004001002014089003,dS 0x112510010c090d1c081806040b,pH 0x211231231111111 7 13)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C7x0 : levelOK p18_T p18_K p18_P 6 (p18_D6.map Prod.fst) ((p18_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I7 : LevelN p18_R p18_T 7 p18_D7 := levelStep p18_B p18_W p18_Q p18_I6 (chunks 64 p18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C7x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D8 : List StD := [
([w1,w2,w0,w3,w4],dL 0x3b,dS 0x1018040c0b070a1208010f0903060d,pH 0x1111111111 1 15)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C8x0 : levelOK p18_T p18_K p18_P 7 (p18_D7.map Prod.fst) ((p18_D8.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I8 : LevelN p18_R p18_T 8 p18_D8 := levelStep p18_B p18_W p18_Q p18_I7 (chunks 64 p18_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C8x0
  ))
theorem p18_L : LowN p18_R p18_T 9 := lowSearch p18_B p18_I8 (by decide +kernel)
def p23_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def p23_R : List Nat := [0, 1, 2, 3]
def p23_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := []
theorem p23_Y : ∀ s ∈ p23_Z, SliceN p23_R p23_T s := by intro s h; cases h
noncomputable def p23_C : List (Nat × List (Nat × Nat × Nat)) := []
def p23_P : List (Nat × Nat) := [(4,6),(1,3),(2,3),(9,12),(2,6),(1,9),(0,9),(6,12),(5,9)]
noncomputable def p23_K : List CutV := p23_C.map (mkCut p23_Z)
theorem p23_W : ∀ c ∈ p23_K, CutP p23_R p23_T c := cutsGood p23_Y (by decide +kernel)
theorem p23_Q : p23_P.all (sepOK p23_T) = true := by decide +kernel
def p23_D2 : List StD := []
theorem p23_I2 : LevelN p23_R p23_T 2 p23_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p23_D3 : List StD := [
([w1,w2,w0,w3],dL 0x0,dS 0x90807040503020601,pH 0x111111 0 9)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p23_C3x0 : levelOK p23_T p23_K p23_P 2 (p23_D2.map Prod.fst) ((p23_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p23_I3 : LevelN p23_R p23_T 3 p23_D3 := levelStep p23_B p23_W p23_Q p23_I2 (chunks 64 p23_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C3x0
  ))
theorem p23_L : LowN p23_R p23_T 4 := lowSearch p23_B p23_I3 (by decide +kernel)
def p22_T : Nat := 0xfeeafc88feeafc88feeafc88feeafc88
def p22_R : List Nat := [0, 1, 2, 3, 4]
def p22_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
theorem p22_S0 : SliceN p22_R p22_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p22_B p19_B p19_L (by decide +kernel)
theorem p22_S1 : SliceN p22_R p22_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p22_B p16_B p16_L (by decide +kernel)
theorem p22_S2 : SliceN p22_R p22_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p22_B p14_B p14_L (by decide +kernel)
theorem p22_S3 : SliceN p22_R p22_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) p22_B p23_B p23_L (by decide +kernel)
theorem p22_S4 : SliceN p22_R p22_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) p22_B p7_B p7_L (by decide +kernel)
theorem p22_S5 : SliceN p22_R p22_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p22_B p4_B p4_L (by decide +kernel)
theorem p22_S6 : SliceN p22_R p22_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p22_B p21_B p21_L (by decide +kernel)
theorem p22_S7 : SliceN p22_R p22_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p22_B p4_B p4_L (by decide +kernel)
def p22_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0x55550000555500005555000055550000,4,[1, 2, 3])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨p22_S0,p22_S1,p22_S2,p22_S3,p22_S4,p22_S5,p22_S6,p22_S7,by simp⟩
noncomputable def p22_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2010202,dC 0x2010203,dC 0x4,dC 0x2010205,dC 0x2010206,dC 0x7,dC 0x3010208,dC 0x8,dC 0x4010101,dC 0x2010405,dC 0x2010402,dC 0x2010406,dC 0x5,dC 0x2010301,dC 0x2010308,dC 0x6,dC 0x3010403,dC 0x3010205,dC 0x2,dC 0x3010201,dC 0x2010102,dC 0x2010106,dC 0x3010101,dC 0x3010108,dC 0x3,dC 0x2010101,dC 0x2010108,dC 0x3020103,dC 0x2010401,dC 0x3020403,dC 0x3020205,dC 0x3020102,dC 0x4020203,dC 0x3010301,dC 0x3010308,dC 0x4020303,dC 0x4020105,dC 0x3020106,dC 0x4020102,dC 0x4010401,dC 0x4020405,dC 0x4020402,dC 0x4020101,dC 0x4020305,dC 0x4030401,dC 0x3020306,dC 0x4030405]
def p22_P : List (Nat × Nat) := [(16,17),(9,10),(2,3),(2,7),(3,6),(2,10),(4,12),(2,19),(1,17),(1,3),(3,5),(1,7),(6,22),(9,12),(8,12),(8,17),(9,17),(6,7),(8,10),(17,18),(8,13),(5,12),(24,25),(5,13),(18,22),(18,19),(5,7),(9,11),(20,22),(9,25),(9,13),(8,14),(6,12),(6,14),(20,21),(5,21),(24,26),(18,26),(24,28),(20,28),(4,22)]
noncomputable def p22_K : List CutV := p22_C.map (mkCut p22_Z)
theorem p22_W : ∀ c ∈ p22_K, CutP p22_R p22_T c := cutsGood p22_Y (by decide +kernel)
theorem p22_Q : p22_P.all (sepOK p22_T) = true := by decide +kernel
def p22_D3 : List StD := []
theorem p22_I3 : LevelN p22_R p22_T 3 p22_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p22_D4 : List StD := [
([w10,w2,w30,w0,w3],dL 0x0,dS 0x100c0b0a05040203070d0601,pH 0x1111111111 0 12),
([w2,w30,w0,w3,w9],dL 0x0,dS 0x617140a0c0b0e1903090d02,pH 0x1111111111 0 12),
([w1,w2,w72,w9,w4],dL 0x0,dS 0xf06210c01150e0a0219090d13,pH 0x1111111111 0 13),
([w27,w1,w2,w72,w4],dL 0x0,dS 0x190712220a06090d0301,pH 0x1111111111 0 10)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C4x0 : levelOK p22_T p22_K p22_P 3 (p22_D3.map Prod.fst) ((p22_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I4 : LevelN p22_R p22_T 4 p22_D4 := levelStep p22_B p22_W p22_Q p22_I3 (chunks 64 p22_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D5 : List StD := [
([w10,w2,w6,w0,w3,w4],dL 0x1,dS 0x110f0e0c0b0a08050402010d03070906,pH 0x111111111111111 1 16),
([w2,w6,w0,w3,w9,w4],dL 0x2,dS 0x11060416150e140a0c0b1318170f09030d02,pH 0x111111111111111 1 18),
([w1,w2,w0,w3,w102,w4],dL 0x8007004006,dS 0x11070f181d131b01120206090d170a03,pH 0x311121111111111 4 16),
([w25,w1,w2,w0,w3,w4],dL 0x0,dS 0xd1206090a1e190f130317,pH 0x111111111111111 0 11),
([w1,w2,w30,w6,w0,w3],dL 0x3,dS 0x7190f111b13121a02090d060a0318,pH 0x111111111111111 1 15),
([w1,w2,w30,w0,w3],dL 0x700a,dS 0x1e0d1b121a06190f0a09181303,pH 0x1221111111 2 13),
([w1,w2,w0,w3,w126,w4],dL 0x400d,dS 0x1e07060e0219171b090d0f1301,pH 0x111121111111111 2 13),
([w193,w1,w2,w0,w3,w4],dL 0x0,dS 0x1e0a07170e02061d0313010d09190f,pH 0x111111111111111 0 15),
([w1,w2,w90,w0,w3,w4],dL 0x0,dS 0x1118060a17120d090703191f01,pH 0x111111111111111 0 13),
([w254,w1,w2,w0,w3,w4],dL 0x701000f,dS 0xd201d181f190a030109060f07,pH 0x221211111121111 3 13),
([w1,w2,w0,w9,w8,w4],dL 0x15,dS 0xa062116010e0219090d1817130f,pH 0x111111111111111 1 14),
([w1,w61,w2,w0,w3,w4],dL 0x7018004017019016,dS 0x21190a170e1d140307090d010f,pH 0x121113213111111 6 13),
([w36,w1,w2,w0,w3,w4],dL 0x0,dS 0x11120a09180d060f191703,pH 0x111111111111111 0 11),
([w1,w2,w21,w0,w3,w4],dL 0x701c,dS 0x1b0501091f0d180f0a0613,pH 0x111211111111111 2 11),
([w1,w83,w2,w0,w3,w4],dL 0x0,dS 0x110e011809060a0d1f1913,pH 0x111111111111111 0 11),
([w65,w1,w2,w0,w3,w4],dL 0x0,dS 0x111b030f061f130d18090a,pH 0x111111111111111 0 11),
([w27,w1,w2,w0,w8,w4],dL 0x14,dS 0x7191222210f06090d0301,pH 0x111111111111111 1 11),
([w1,w2,w72,w3,w8,w4],dL 0x20,dS 0x250a211712091e0613190f0301,pH 0x111111111111111 1 13),
([w1,w2,w72,w3,w4],dL 0x4021,dS 0x26192517121f0a090d0306130f01,pH 0x1211111111 2 14),
([w1,w135,w2,w0,w3,w4],dL 0x7024,dS 0x91a1201071918030a0f13,pH 0x111111211111111 2 11),
([w1,w2,w0,w3,w115,w4],dL 0x4027,dS 0x6251b121e0f131703190a01,pH 0x111121111111111 2 12),
([w1,w2,w0,w3,w259,w4],dL 0x0,dS 0x6251b17121e0d130f19030a01,pH 0x111111111111111 0 13),
([w1,w2,w0,w60,w3,w4],dL 0x0,dS 0x260a17120d09060703190f01,pH 0x111111111111111 0 12),
([w43,w1,w2,w0,w3,w4],dL 0x2d004,dS 0x26291d170d190f0a0906070301,pH 0x111111111121111 2 13),
([w1,w2,w260,w0,w3,w4],dL 0x0,dS 0xa120617030d1e07190f01,pH 0x111111111111111 0 11),
([w1,w261,w2,w0,w3,w4],dL 0x402f,dS 0x1e291d090d0a17121907060f0301,pH 0x111111111111111 2 14)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C5x0 : levelOK p22_T p22_K p22_P 4 (p22_D4.map Prod.fst) ((p22_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I5 : LevelN p22_R p22_T 5 p22_D5 := levelStep p22_B p22_W p22_Q p22_I4 (chunks 64 p22_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D6 : List StD := [
([w1,w2,w6,w0,w3,w4],dL 0x2005004003009001,dS 0x1e071c1b1a03010d06190f1209180a,pH 0x221264311111111 6 15),
([w10,w1,w2,w0,w3,w4],dL 0xc00400b009001,dS 0x1e1c170e03010a0d0607190f09,pH 0x221213111125411 5 13),
([w18,w1,w2,w0,w3,w4],dL 0x12009001004011,dS 0x906171d1201030d07,pH 0x122412333322322 5 9),
([w1,w2,w0,w3,w9,w4],dL 0x13011009014001,dS 0x1d0a0d19180917131f,pH 0x321342312512111 5 9),
([w1,w12,w2,w0,w3,w4],dL 0x701d01100e01b004,dS 0x1e19171f0d22090a181201,pH 0x411541111122222 6 11),
([w17,w1,w2,w0,w3,w4],dL 0x701f01e01100e004,dS 0x1e0d06180f23030a240107,pH 0x311531431411114 6 11),
([w1,w2,w0,w3,w8,w4],dL 0x22007011020015014,dS 0x26072517121f1c0d19090603130f01,pH 0x511441111322111 6 15),
([w27,w1,w2,w0,w3,w4],dL 0x7023025011014,dS 0x1e071f0618011c0d0919030f,pH 0x121312342451214 5 12),
([w1,w19,w2,w0,w3,w4],dL 0x2800400a026007009,dS 0x130d17070a121a26190f01,pH 0x111113222111114 6 11),
([w66,w1,w2,w0,w3,w4],dL 0x2b00402902a007009,dS 0x13171f092706190a280f0103,pH 0x111113111122214 6 12),
([w1,w2,w7,w0,w3,w4],dL 0x1102c00700e004009,dS 0x280906071d1723030a1301,pH 0x112321112211151 6 11),
([w71,w1,w2,w0,w3,w4],dL 0x3002e007011009,dS 0x706161d0a0f190103,pH 0x112122111121334 5 9)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C6x0 : levelOK p22_T p22_K p22_P 5 (p22_D5.map Prod.fst) ((p22_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I6 : LevelN p22_R p22_T 6 p22_D6 := levelStep p22_B p22_W p22_Q p22_I5 (chunks 64 p22_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1100901a01400e001,dS 0x1e0d1317040619030a09181f01,pH 0x3224321111 6 13)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C7x0 : levelOK p22_T p22_K p22_P 6 (p22_D6.map Prod.fst) ((p22_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I7 : LevelN p22_R p22_T 7 p22_D7 := levelStep p22_B p22_W p22_Q p22_I6 (chunks 64 p22_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C7x0
  ))
theorem p22_L : LowN p22_R p22_T 8 := lowSearch p22_B p22_I7 (by decide +kernel)
def p24_T : Nat := 0xeee8eac8eee8eac8eee8eac8eee8eac8
def p24_R : List Nat := [0, 1, 2, 3, 4]
def p24_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,5,21)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
theorem p24_S0 : SliceN p24_R p24_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p24_B p17_B p17_L (by decide +kernel)
theorem p24_S1 : SliceN p24_R p24_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p24_B p20_B p20_L (by decide +kernel)
theorem p24_S2 : SliceN p24_R p24_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p24_B p4_B p4_L (by decide +kernel)
theorem p24_S3 : SliceN p24_R p24_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p24_B p23_B p23_L (by decide +kernel)
theorem p24_S4 : SliceN p24_R p24_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p24_B p4_B p4_L (by decide +kernel)
theorem p24_S5 : SliceN p24_R p24_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p24_B p10_B p10_L (by decide +kernel)
def p24_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨p24_S0,p24_S1,p24_S2,p24_S3,p24_S4,p24_S5,by simp⟩
noncomputable def p24_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2010101,dC 0x2,dC 0x2010103,dC 0x4,dC 0x2010102,dC 0x2010105,dC 0x2010106,dC 0x6,dC 0x2010201,dC 0x2010202,dC 0x2010203,dC 0x2010205,dC 0x2010206,dC 0x2010301,dC 0x2010303,dC 0x2010302,dC 0x2010305,dC 0x2010306,dC 0x2010401,dC 0x2010403,dC 0x2010402,dC 0x2010405,dC 0x2010406,dC 0x3010202,dC 0x3,dC 0x3010203,dC 0x3010302,dC 0x3010303,dC 0x3010306,dC 0x4010401,dC 0x3010201,dC 0x4010206,dC 0x5,dC 0x4010102,dC 0x3010301,dC 0x3020202,dC 0x3020203,dC 0x3020206,dC 0x4020101,dC 0x3020302,dC 0x3020303,dC 0x3020201,dC 0x3020301,dC 0x4020306,dC 0x4020402,dC 0x3010102,dC 0x3010401,dC 0x3020101,dC 0x3020402,dC 0x4030206,dC 0x4030101,dC 0x4030102]
def p24_P : List (Nat × Nat) := [(5,6),(2,6),(9,12),(8,9),(20,21),(0,3),(17,21),(3,4),(3,12),(1,9),(3,20),(4,19),(5,9),(9,17),(5,21),(2,3),(3,10),(3,18),(6,12),(4,6),(6,20),(1,3),(18,26),(10,26),(3,5),(3,17),(24,26),(5,13),(10,14),(9,10),(4,13),(12,13),(10,11),(18,19),(5,7),(8,14),(12,14),(17,19),(26,28),(6,10),(1,7),(2,7),(18,22),(24,25),(21,28),(17,25),(1,11),(2,11),(20,22)]
noncomputable def p24_K : List CutV := p24_C.map (mkCut p24_Z)
theorem p24_W : ∀ c ∈ p24_K, CutP p24_R p24_T c := cutsGood p24_Y (by decide +kernel)
theorem p24_Q : p24_P.all (sepOK p24_T) = true := by decide +kernel
def p24_D3 : List StD := []
theorem p24_I3 : LevelN p24_R p24_T 3 p24_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p24_D4 : List StD := [
([w22,w2,w68,w3,w4],dL 0x0,dS 0xf0e0d0c0b0903010807050a0402,pH 0x1111111111 0 14),
([w10,w1,w0,w31,w4],dL 0x0,dS 0xd01180f17020a07,pH 0x1111111111 0 8),
([w1,w2,w68,w31,w4],dL 0x0,dS 0xd180f09011704050a0702,pH 0x1111111111 0 11),
([w124,w1,w2,w68,w4],dL 0x0,dS 0x180f08010d0717020a0405,pH 0x1111111111 0 11),
([w1,w2,w68,w3,w38],dL 0x0,dS 0xd180f0b011704050a0702,pH 0x1111111111 0 11),
([w70,w1,w2,w68,w3],dL 0x0,dS 0xd170208010a07180f0504,pH 0x1111111111 0 11),
([w2,w6,w68,w3,w4],dL 0x0,dS 0xd030f1808040a0102051707,pH 0x1111111111 0 12),
([w1,w2,w68,w3,w4],dL 0x0,dS 0x1d180f0801170a04050702,pH 0x1111111111 0 11),
([w1,w2,w0,w544,w4],dL 0x0,dS 0x1d180f0401170a02070511,pH 0x1111111111 0 11),
([w89,w1,w2,w31,w4],dL 0x0,dS 0x180f04011d170a05110702,pH 0x1111111111 0 11),
([w89,w124,w1,w2,w4],dL 0x0,dS 0x180f101d170a04050702,pH 0x1111111111 0 10),
([w89,w70,w1,w2,w3],dL 0x0,dS 0x170a101d180f05040702,pH 0x1111111111 0 10),
([w1,w2,w0,w31,w38],dL 0x0,dS 0x170a1d011b0207050414,pH 0x1111111111 0 10),
([w70,w1,w2,w0,w31],dL 0x0,dS 0x1d170a021107180f0504,pH 0x1111111111 0 10),
([w1,w6,w0,w31,w4],dL 0x0,dS 0x1d1104180f0107141b02,pH 0x1111111111 0 10),
([w1,w2,w545,w3,w4],dL 0x0,dS 0x1d180f0801170a04050702,pH 0x1111111111 0 11),
([w1,w2,w0,w31,w4],dL 0x0,dS 0x1d180f0401170a02070511,pH 0x1111111111 0 11),
([w124,w70,w1,w2,w0],dL 0x0,dS 0x207101c180f0504170a,pH 0x1111111111 0 10),
([w316,w1,w0,w3,w4],dL 0x0,dS 0x1c14180f171b010a1606,pH 0x1111111111 0 10),
([w316,w2,w0,w3,w4],dL 0x0,dS 0x1c010f180a0510170604,pH 0x1111111111 0 10),
([w40,w1,w2,w3,w4],dL 0x0,dS 0x180f20011d170a05100702,pH 0x1111111111 0 11),
([w1,w2,w32,w56,w4],dL 0x0,dS 0x1d180f22210601170a100702,pH 0x1111111111 0 12),
([w25,w1,w2,w32,w4],dL 0x0,dS 0x180f221c171002070a03,pH 0x1111111111 0 10),
([w1,w2,w32,w30,w3],dL 0x0,dS 0x1d170a0601180f22030702,pH 0x1111111111 0 11),
([w154,w1,w2,w0,w4],dL 0x0,dS 0x180f101c0207170a0504,pH 0x1111111111 0 10),
([w40,w1,w2,w56,w4],dL 0x0,dS 0x180f21011d170a05100702,pH 0x1111111111 0 11),
([w25,w40,w1,w2,w4],dL 0x0,dS 0x2622010d16100717020a,pH 0x1111111111 0 10),
([w40,w1,w2,w30,w3],dL 0x0,dS 0x170a24262022011d16100702,pH 0x1111111111 0 12),
([w47,w40,w1,w2,w3],dL 0x0,dS 0x170a211d180f10050207,pH 0x1111111111 0 10),
([w25,w1,w2,w0,w4],dL 0x0,dS 0x180f221f1c020717100a04,pH 0x1111111111 0 11),
([w1,w2,w56,w30,w0],dL 0x0,dS 0x1d180f22210601170a021007,pH 0x1111111111 0 12),
([w243,w1,w2,w3,w4],dL 0x0,dS 0x180f05011d170a04100702,pH 0x1111111111 0 11),
([w25,w1,w2,w30,w0],dL 0x0,dS 0x2071f221c180f17100a04,pH 0x1111111111 0 11),
([w47,w25,w1,w2,w0],dL 0x0,dS 0x11c0e0207161017180a0f,pH 0x1111111111 0 11),
([w1,w2,w180,w24,w3],dL 0x0,dS 0x1d02040801141b05031807,pH 0x1111111111 0 11),
([w1,w2,w24,w181,w3],dL 0x0,dS 0x2427040801170a05031807,pH 0x1111111111 0 11),
([w1,w2,w0,w546,w4],dL 0x0,dS 0x180f11170a1d070504,pH 0x1111111111 0 9),
([w317,w2,w24,w3,w4],dL 0x0,dS 0x170d221d040102051b0308,pH 0x1111111111 0 11),
([w1,w2,w24,w3,w51],dL 0x0,dS 0x1d0408011807020305141b,pH 0x1111111111 0 11),
([w1,w547,w0,w3,w4],dL 0x0,dS 0xf0e1b13030601140a1d070405,pH 0x1111111111 0 13),
([w244,w1,w0,w3,w4],dL 0x0,dS 0x170a1d051b1404070206,pH 0x1111111111 0 10),
([w50,w1,w2,w180,w3],dL 0x0,dS 0x170a1d160302071810,pH 0x1111111111 0 9),
([w74,w1,w2,w0,w55],dL 0x0,dS 0x40e1c101707020f130a16,pH 0x1111111111 0 11),
([w1,w2,w0,w55,w8],dL 0x0,dS 0x142d2c2010170f02070a04,pH 0x1111111111 0 11),
([w548,w1,w2,w3,w4],dL 0x0,dS 0x180f05011d170d03100702,pH 0x1111111111 0 11),
([w74,w1,w2,w0,w136],dL 0x0,dS 0x1b2c042e1c050702130a16,pH 0x1111111111 0 11),
([w74,w1,w2,w0,w51],dL 0x0,dS 0x403021c05130a170f16,pH 0x1111111111 0 10),
([w549,w1,w2,w3,w4],dL 0x0,dS 0x180f05011d170a03100702,pH 0x1111111111 0 11),
([w1,w2,w0,w550,w4],dL 0x0,dS 0x180f10170a02070504,pH 0x1111111111 0 9),
([w50,w1,w2,w181,w3],dL 0x0,dS 0x170a051d2b161807030210,pH 0x1111111111 0 11),
([w551,w2,w0,w3,w4],dL 0x0,dS 0x180f2b1d132419030601141b050402,pH 0x1111111111 0 15),
([w245,w2,w0,w3,w4],dL 0x0,dS 0x170a071d14021b05100604,pH 0x1111111111 0 11),
([w552,w1,w2,w0,w4],dL 0x0,dS 0x180f221f1c1d0717100a04,pH 0x1111111111 0 11),
([w50,w1,w2,w3,w51],dL 0x0,dS 0x14130a1d160302071810,pH 0x1111111111 0 10),
([w1,w2,w553,w3,w4],dL 0x0,dS 0x180f08010305170d0702,pH 0x1111111111 0 10),
([w1,w2,w0,w136,w8],dL 0x0,dS 0x1410170f02070504,pH 0x1111111111 0 8),
([w1,w318,w0,w8,w4],dL 0x0,dS 0x1421180f1d070504,pH 0x1111111111 0 8),
([w1,w2,w0,w8,w51],dL 0x0,dS 0x1707021c14100f0a131b0504,pH 0x1111111111 0 12),
([w128,w1,w2,w0,w4],dL 0x0,dS 0x180f1f1c0207170a2204,pH 0x1111111111 0 10),
([w1,w2,w554,w3,w4],dL 0x0,dS 0x180f08010305170a0702,pH 0x1111111111 0 10)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C4x0 : levelOK p24_T p24_K p24_P 3 (p24_D3.map Prod.fst) ((p24_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I4 : LevelN p24_R p24_T 4 p24_D4 := levelStep p24_B p24_W p24_Q p24_I3 (chunks 64 p24_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D5p0 : List StD := [
([w22,w28,w2,w0,w3,w4],dL 0x1,dS 0xe0d151312110603011407050f10040a02,pH 0x111111111111111 1 17),
([w22,w1,w2,w0,w3,w4],dL 0x0,dS 0xd06101416040f180a071702,pH 0x111111111111111 0 12),
([w10,w28,w1,w0,w3,w4],dL 0x1,dS 0xd1a19060118160f17020a07,pH 0x111111111111111 1 12),
([w10,w1,w2,w0,w3,w4],dL 0x0,dS 0xd0616041410180f17020a07,pH 0x111111111111111 0 12),
([w28,w1,w2,w68,w3,w4],dL 0x2,dS 0xd011918170714050f040a,pH 0x111111111111111 1 11),
([w1,w2,w0,w68,w3,w4],dL 0x0,dS 0x219011c0f180a1b050414,pH 0x111111111111111 0 11),
([w1,w2,w68,w3,w4],dL 0x0,dS 0x1d1c191b0a05070f1817020414,pH 0x1111111111 0 13),
([w555,w1,w2,w0,w3,w4],dL 0x5003004,dS 0x7021c170116100504140f0a,pH 0x111111111112111 3 12),
([w89,w28,w1,w2,w3,w4],dL 0x4,dS 0x17050116101d140f040a0702,pH 0x111111111111111 1 12),
([w28,w1,w2,w0,w31,w4],dL 0x6,dS 0x181d01111b050704140f02,pH 0x111111111111111 1 11),
([w1,w2,w0,w3,w31,w4],dL 0x0,dS 0xa01180f1d021b07050414,pH 0x111111111111111 0 11),
([w1,w2,w0,w31,w4],dL 0x0,dS 0x1d1c111b0a05070f1817020414,pH 0x1111111111 0 13),
([w556,w1,w2,w0,w3,w4],dL 0x5001007,dS 0x181d1b0116100714040f02,pH 0x111111111111211 3 11),
([w124,w28,w1,w2,w0,w4],dL 0x7,dS 0x70116101c140f17020a0405,pH 0x111111111111111 1 12),
([w28,w1,w2,w0,w3,w38],dL 0x5007004,dS 0x1c1b05011a120a020414,pH 0x121121121132111 3 10),
([w70,w28,w1,w2,w0,w3],dL 0x8,dS 0x1d1b010a16101807140f050204,pH 0x111111111111111 1 13),
([w70,w1,w2,w0,w3],dL 0x0,dS 0x1d1c101617071b050a02140f1804,pH 0x1111111111 0 14),
([w28,w1,w6,w0,w3,w4],dL 0x0,dS 0x1d18041a19101701070f141b0a1602,pH 0x111111111111111 0 15),
([w28,w2,w6,w0,w3,w4],dL 0x0,dS 0x1d0318141211160417070f05100a02,pH 0x111111111111111 0 15),
([w22,w1,w6,w0,w3,w4],dL 0x1,dS 0x1d0601180f16141b170a0702,pH 0x111111111111111 1 12),
([w10,w2,w6,w0,w3,w4],dL 0x1,dS 0x1d03060104180f0517020a07,pH 0x111111111111111 1 12),
([w2,w6,w0,w24,w3,w4],dL 0xa,dS 0x1c02201f031e161418070f0a10051701,pH 0x111111111111111 1 16),
([w54,w2,w6,w0,w3,w4],dL 0xa,dS 0x1c201f18141207041016050f170a01,pH 0x111111111111111 1 15),
([w1,w6,w0,w3,w8,w4],dL 0xb,dS 0xf0a1d25132422011e0418171610071b02,pH 0x111111111111111 1 17),
([w27,w1,w6,w0,w3,w4],dL 0xb,dS 0x1d25241e041a1723140118020f1b071610,pH 0x111111111111111 1 17),
([w1,w2,w32,w6,w3,w4],dL 0xc,dS 0xf1d261b222103010a1702071610,pH 0x111111111111111 1 14),
([w1,w2,w0,w134,w3,w4],dL 0x500300c,dS 0x1d18171b2004010f020a070510,pH 0x132111111111111 3 13),
([w40,w1,w2,w6,w3,w4],dL 0xa,dS 0xf2614222105011d0a1716100702,pH 0x111111111111111 1 14),
([w40,w1,w2,w0,w3,w4],dL 0x0,dS 0x20a1617180f14101c05,pH 0x111111111111111 0 10),
([w40,w1,w2,w3,w4],dL 0x0,dS 0x2624201d0a16170710180f1c140205,pH 0x1111111111 0 15),
([w1,w2,w56,w6,w0,w4],dL 0xd,dS 0xf1d2613220521010a1702071610,pH 0x111111111111111 1 14),
([w1,w2,w0,w3,w102,w4],dL 0xd005001,dS 0x1d1814220520010f170a02040710,pH 0x211111111111111 3 14),
([w25,w1,w2,w6,w0,w4],dL 0xb,dS 0xf261b2204011c0216100a0717,pH 0x111111111111111 1 13),
([w25,w1,w2,w0,w3,w4],dL 0x0,dS 0x200a07020f1816101d1b04,pH 0x111111111111111 0 11),
([w25,w1,w2,w0,w4],dL 0x0,dS 0x23221f1c021007160a0f181d1b1704,pH 0x1111111111 0 15),
([w1,w2,w30,w6,w0,w3],dL 0xe,dS 0x1d1426210422010a1702161007,pH 0x111111111111111 1 13),
([w1,w2,w30,w0,w3],dL 0x0,dS 0x1d1c2526202210160a0717020f180414,pH 0x1111111111 0 16),
([w47,w1,w2,w6,w0,w3],dL 0xd00500c,dS 0x1c0a1b21050117020716100f18,pH 0x131111111111211 3 13),
([w28,w1,w2,w0,w3,w4],dL 0x5008006002,dS 0x1c1b05010216100a04140f,pH 0x211321321132111 4 11),
([w1,w2,w6,w0,w3,w4],dL 0x500e00b00a,dS 0x1c2614222104010f0a1702071610,pH 0x211421111111111 4 14),
([w1,w2,w0,w557,w3,w4],dL 0x0,dS 0xd0220030601170f18100a1b140705,pH 0x111111111111111 0 15),
([w558,w1,w2,w0,w3,w4],dL 0x5010,dS 0x18021c100107160414050f170a,pH 0x111111111111111 2 13),
([w1,w2,w0,w3,w559,w4],dL 0x12005,dS 0xe171d22200f0a141b02100704,pH 0x111111111111111 2 13),
([w315,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d141b130a160510040f180702,pH 0x111111111111111 0 13),
([w22,w10,w1,w0,w3,w4],dL 0x0,dS 0x1d102604180f16170a0702,pH 0x111111111111111 0 11),
([w22,w10,w2,w0,w3,w4],dL 0x0,dS 0x1d1416180f0405170a0702,pH 0x111111111111111 0 11),
([w22,w2,w0,w24,w3,w4],dL 0x0,dS 0x100d0208040301170f18200a14051b07,pH 0x111111111111111 0 16),
([w54,w22,w2,w0,w3,w4],dL 0xf,dS 0x170f01222107061c1b20101405,pH 0x111111111111111 1 13),
([w1,w2,w0,w560,w3,w4],dL 0x15005,dS 0x170a1d072625060118140f16040502,pH 0x111111111111111 2 15),
([w561,w1,w2,w0,w3,w4],dL 0x0,dS 0x1c1614070405030601021b10180f170a,pH 0x111111111111111 0 16),
([w1,w2,w0,w3,w126,w4],dL 0x0,dS 0xa1d1321180f161b02070504,pH 0x111111111111111 0 12),
([w193,w1,w2,w0,w3,w4],dL 0x5017,dS 0x181d161b21171410040f0702,pH 0x111111111111111 2 12),
([w10,w1,w0,w3,w8,w4],dL 0x0,dS 0xa1d1413100504171b180f0207,pH 0x111111111111111 0 13),
([w27,w10,w1,w0,w3,w4],dL 0x16,dS 0x1d1026172306140f1b1802070416,pH 0x111111111111111 1 14),
([w54,w1,w2,w24,w3,w4],dL 0x1,dS 0x50d0318141b170f070a16,pH 0x111111111111111 1 11),
([w1,w2,w24,w20,w3,w4],dL 0x0,dS 0xa0d1d1525162703040801182014050f0207,pH 0x111111111111111 0 18),
([w1,w562,w2,w0,w3,w4],dL 0x5003004002,dS 0x1c1817072702141e101b0f0a0504,pH 0x211211231111111 4 14),
([w109,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d140f18070a17020510,pH 0x111111111111111 0 10),
([w1,w2,w24,w3,w42,w4],dL 0x19,dS 0xa0d28160401180f051d1b070314,pH 0x111111111111111 1 14),
([w1,w2,w0,w3,w246,w4],dL 0x1b005,dS 0xe0a17021610010f1d1b07050414,pH 0x111111111111111 2 14),
([w247,w1,w2,w0,w3,w4],dL 0x0,dS 0x210a0f18071d141b0504,pH 0x111111111111111 0 10),
([w1,w2,w116,w0,w3,w4],dL 0x0,dS 0x726291420180f1c0a1617021005,pH 0x111111111111111 0 14),
([w1,w563,w2,w0,w3,w4],dL 0x14,dS 0x1c1406101807020f170a051604,pH 0x111111111111111 1 13),
([w1,w2,w0,w3,w564,w4],dL 0x0,dS 0x17011d1b16180f02050414,pH 0x111111111111111 0 11)]
set_option maxHeartbeats 0 in
noncomputable def p24_D5p1 : List StD := [
([w565,w1,w2,w0,w3,w4],dL 0x501d,dS 0x21c1b0a0710180405160f14,pH 0x111111111111111 2 12),
([w54,w1,w2,w0,w180,w3],dL 0x1e,dS 0x1c2a050418020f160a1714,pH 0x111111111111111 1 11),
([w1,w2,w0,w180,w3],dL 0x1f,dS 0x1d2b161b1805100a170f040214,pH 0x1111111111 1 13),
([w54,w50,w1,w2,w3,w4],dL 0x0,dS 0x232b1d162a0d29031805170f0a140702,pH 0x111111111111111 0 16),
([w74,w1,w2,w0,w9,w4],dL 0x3,dS 0x17040e1c111807020a0f1416,pH 0x111111111111111 1 12),
([w1,w2,w0,w9,w8,w4],dL 0x0,dS 0x14132c2d052011181b0f1702070a04,pH 0x111111111111111 0 15),
([w1,w61,w2,w0,w3,w4],dL 0x0,dS 0x14131716071d21180f0a050204,pH 0x111111111111111 0 13),
([w36,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d160f180a1704070210,pH 0x111111111111111 0 10),
([w248,w1,w2,w0,w3,w4],dL 0x0,dS 0x71b0a180f1c16041405,pH 0x111111111111111 0 10),
([w1,w2,w0,w3,w55,w9],dL 0x21,dS 0x2e1c102c112021141b02070a04,pH 0x111111111111111 1 13),
([w1,w2,w0,w3,w55],dL 0x23,dS 0x2e1c2c20100f1b1618070204140a,pH 0x1111111111 1 14),
([w1,w2,w216,w0,w3,w4],dL 0x500100d,dS 0x181d0a262f142220010f160207170410,pH 0x111312111111111 3 16),
([w1,w566,w2,w0,w3,w4],dL 0x0,dS 0x1d14180f21170a02050704,pH 0x111111111111111 0 11),
([w1,w2,w0,w567,w3,w4],dL 0x0,dS 0x216010f18171c1b07050414,pH 0x111111111111111 0 12),
([w74,w27,w1,w2,w0,w4],dL 0x0,dS 0x1e13302e1c2f05180f1b070204170a,pH 0x111111111111111 0 15),
([w74,w1,w2,w0,w42,w4],dL 0x24,dS 0x2300a0d1d05171f181c160f13,pH 0x111111111111111 1 13),
([w1,w2,w568,w0,w3,w4],dL 0x500c,dS 0x1c18261a02142220170a071004,pH 0x121111111111111 2 13),
([w241,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d14180f170a10020704,pH 0x111111111111111 0 10),
([w1,w2,w157,w0,w3,w4],dL 0x0,dS 0x1d142220180f170a02100704,pH 0x111111111111111 0 12),
([w256,w1,w2,w0,w3,w4],dL 0x5007,dS 0x171d1b0f0a1410020704,pH 0x211111111111111 2 10),
([w569,w1,w2,w0,w3,w4],dL 0x0,dS 0x19040307051c23170f180a0214,pH 0x111111111111111 0 13),
([w110,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d05180f0214170a0716,pH 0x111111111111111 0 10),
([w50,w1,w2,w20,w3,w4],dL 0x1,dS 0x718052b1d190f170a020410,pH 0x111111111111111 1 12),
([w1,w2,w0,w3,w249,w4],dL 0x26005,dS 0x180a2b071d16132419010f02141b050410,pH 0x111111111111111 2 17),
([w250,w1,w2,w0,w3,w4],dL 0x0,dS 0x1017020f181d141b0504,pH 0x111111111111111 0 10),
([w1,w2,w0,w181,w20,w3],dL 0x27,dS 0x1d2b2516311901170a0502140410,pH 0x111111111111111 1 14),
([w1,w2,w0,w181,w3],dL 0x28,dS 0x1d2b2531161805100a170f140204,pH 0x1111111111 1 14),
([w1,w182,w2,w0,w3,w4],dL 0x500300c,dS 0x181c250222212a040f0a07161014,pH 0x111111321111111 3 14),
([w570,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d04230f180a17071402,pH 0x111111111111111 0 10),
([w1,w2,w0,w3,w571,w4],dL 0x0,dS 0xa01180f041b14051d0710,pH 0x111111111111111 0 11),
([w572,w1,w2,w0,w3,w4],dL 0x502a,dS 0x1c1b051702161814100f04,pH 0x111111111111111 2 11),
([w50,w1,w2,w3,w42,w4],dL 0x29,dS 0xa2902280d1607240f1d101803,pH 0x111111111111111 1 13),
([w314,w1,w2,w0,w3,w4],dL 0x5001007006,dS 0x1d1b2d010a1604181707050f1402,pH 0x121211111121311 4 14),
([w65,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d04180f170a021b0716,pH 0x111111111111111 0 10),
([w27,w1,w2,w0,w8,w4],dL 0x3,dS 0x17131805100f020704,pH 0x111111111111111 1 9),
([w1,w2,w0,w8,w42,w4],dL 0x2b,dS 0x20d14181d1713100f1c1b0504,pH 0x111111111111111 1 13),
([w251,w1,w2,w0,w3,w4],dL 0x0,dS 0x1002180f171c1b140405,pH 0x111111111111111 0 10),
([w1,w135,w2,w0,w3,w4],dL 0x0,dS 0x17223001040f181d1b0a02100716,pH 0x111111111111111 0 14),
([w573,w1,w2,w0,w3,w4],dL 0x11,dS 0x1d061016040f170a14180702,pH 0x111111111111111 1 12),
([w1,w2,w0,w574,w3,w4],dL 0x0,dS 0x2b0719010f180a051c1b02041410,pH 0x111111111111111 0 14),
([w27,w1,w2,w0,w3,w136],dL 0x2d,dS 0x1d0f2f1b0514180a10020704,pH 0x111111111111111 1 12),
([w1,w2,w0,w3,w136],dL 0x2e,dS 0x2e1c101b0f0516141807020a04,pH 0x1111111111 1 13),
([w1,w2,w33,w0,w3,w4],dL 0x500d,dS 0x1d260f2212040a0702161714,pH 0x211111111111111 2 12),
([w242,w1,w2,w0,w3,w4],dL 0x0,dS 0x1d040f1807160a170214,pH 0x111111111111111 0 10),
([w1,w137,w2,w0,w3,w4],dL 0x0,dS 0x1d2c040a1707140f18020516,pH 0x111111111111111 0 12),
([w575,w1,w2,w0,w3,w4],dL 0x5004,dS 0x71c050f0204160a1714,pH 0x121111111111111 2 10),
([w317,w1,w2,w0,w3,w4],dL 0x2f,dS 0x16100a07042317020f1c1418,pH 0x111111111111111 1 12),
([w252,w1,w2,w0,w3,w4],dL 0x30,dS 0x301017041b180a1d07140f16,pH 0x111111111111111 1 12),
([w1,w318,w2,w0,w3,w4],dL 0x31,dS 0x16171421180a1d07050f04,pH 0x111111111111111 1 11),
([w125,w1,w2,w0,w3,w4],dL 0x32,dS 0x29160a071417050f1c02041810,pH 0x111111111111111 1 13),
([w1,w2,w0,w3,w51,w42],dL 0x33,dS 0xa020d10030601180f1c1d1b14041605,pH 0x111111111111111 1 16),
([w1,w2,w0,w3,w51],dL 0x35034,dS 0xd10161b0f180a05021404,pH 0x1111211211 2 11)]
noncomputable def p24_D5 : List StD := p24_D5p0 ++ p24_D5p1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C5x0 : levelOK p24_T p24_K p24_P 4 (p24_D4.map Prod.fst) ((p24_D5.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C5x1 : levelOK p24_T p24_K p24_P 4 (p24_D4.map Prod.fst) ((p24_D5.drop (1*64)).take 64) = true := by decide +kernel
theorem p24_I5 : LevelN p24_R p24_T 5 p24_D5 := levelStep p24_B p24_W p24_Q p24_I4 (chunks 64 p24_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C5x0
  · exact p24_C5x1
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D6 : List StD := [
([w28,w1,w2,w0,w3,w4],dL 0x9005003006001002008,dS 0x1d1c1b0116101705071804140f0a02,pH 0x111112111164211 7 15),
([w1,w2,w6,w0,w3,w4],dL 0x900500300b00100a00e,dS 0x1d1c26231422210401070a0f1716101802,pH 0x111642111111111 7 17),
([w22,w1,w2,w0,w3,w4],dL 0x501100f013,dS 0x1d1c1b210616040710140a170f1802,pH 0x111112111143211 4 15),
([w10,w1,w2,w0,w3,w4],dL 0x5016014018,dS 0x1d1c23061410051716040207180f0a,pH 0x111111111143211 4 15),
([w1,w2,w0,w24,w3,w4],dL 0x1901a001,dS 0x1c0216201b070a1718050f14,pH 0x223111111111111 3 12),
([w54,w1,w2,w0,w3,w4],dL 0x1c01a001,dS 0x1d1b2007021618050a17140f,pH 0x211211211123111 3 12),
([w1,w2,w0,w3,w9,w4],dL 0x22020003,dS 0x2e171c2c20211b0a0f161807020414,pH 0x311121111111111 3 15),
([w74,w1,w2,w0,w3,w4],dL 0x24022003,dS 0x1d1b1720210a04070216140f18,pH 0x121211211121311 3 13),
([w192,w1,w2,w0,w3,w4],dL 0x2201a009005,dS 0xd1004140f1702262e07,pH 0x113143143111111 4 10),
([w39,w1,w2,w0,w3,w4],dL 0x2201a009005,dS 0xd101604180a071b172b,pH 0x113143143111111 4 10),
([w1,w2,w0,w20,w3,w4],dL 0x2501a001,dS 0x2b1d07312523050f0a170210181404,pH 0x223111111111111 3 15),
([w50,w1,w2,w0,w3,w4],dL 0x2901a001,dS 0x1c250507230214170a1004180f,pH 0x211211211123111 3 13),
([w1,w2,w0,w3,w8,w4],dL 0x2b022003,dS 0xa1d251017050f07021b1804,pH 0x211131111111111 3 12),
([w27,w1,w2,w0,w3,w4],dL 0x2c022003,dS 0x1c2505170a101b0207180f04,pH 0x121211211121311 3 12),
([w1,w19,w2,w0,w3,w4],dL 0x2201a009005,dS 0xd182b0f0516140a0702041722,pH 0x113143111211111 4 13),
([w66,w1,w2,w0,w3,w4],dL 0x2201a009005,dS 0xd1016140f051702042e07,pH 0x113143143111111 4 11),
([w1,w2,w0,w3,w42,w4],dL 0x1a033003001,dS 0x1b0510160f1c1d181404,pH 0x421121112111211 4 10)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C6x0 : levelOK p24_T p24_K p24_P 5 (p24_D5.map Prod.fst) ((p24_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I6 : LevelN p24_R p24_T 6 p24_D6 := levelStep p24_B p24_W p24_Q p24_I5 (chunks 64 p24_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x2201a009003001,dS 0x1d1c1b0510160f180a1707041402,pH 0x2113213211 5 14)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C7x0 : levelOK p24_T p24_K p24_P 6 (p24_D6.map Prod.fst) ((p24_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I7 : LevelN p24_R p24_T 7 p24_D7 := levelStep p24_B p24_W p24_Q p24_I6 (chunks 64 p24_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C7x0
  ))
theorem p24_L : LowN p24_R p24_T 8 := lowSearch p24_B p24_I7 (by decide +kernel)
def p25_T : Nat := 0xfefefee8fefefee8fefefee8fefefee8
def p25_R : List Nat := [0, 1, 2, 3, 4]
def p25_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
theorem p25_S0 : SliceN p25_R p25_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p25_B p10_B p10_L (by decide +kernel)
theorem p25_S1 : SliceN p25_R p25_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) p25_B p12_B p12_L (by decide +kernel)
def p25_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨p25_S0,p25_S1,by simp⟩
noncomputable def p25_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2]
def p25_P : List (Nat × Nat) := [(4,5)]
noncomputable def p25_K : List CutV := p25_C.map (mkCut p25_Z)
theorem p25_W : ∀ c ∈ p25_K, CutP p25_R p25_T c := cutsGood p25_Y (by decide +kernel)
theorem p25_Q : p25_P.all (sepOK p25_T) = true := by decide +kernel
def p25_D6 : List StD := []
theorem p25_I6 : LevelN p25_R p25_T 6 p25_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p25_D7 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1002,dS 0x1,pH 0x1111111112 2 1)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p25_C7x0 : levelOK p25_T p25_K p25_P 6 (p25_D6.map Prod.fst) ((p25_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p25_I7 : LevelN p25_R p25_T 7 p25_D7 := levelStep p25_B p25_W p25_Q p25_I6 (chunks 64 p25_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C7x0
  ))
theorem p25_L : LowN p25_R p25_T 8 := lowSearch p25_B p25_I7 (by decide +kernel)
def p26_T : Nat := 0xfffeffeafffeffeafffeffeafffeffea
def p26_R : List Nat := [0, 1, 2, 3, 4]
def p26_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,0,8),(4,2,18)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
theorem p26_S0 : SliceN p26_R p26_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p26_B p7_B p7_L (by decide +kernel)
def p26_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨p26_S0,by simp⟩
noncomputable def p26_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p26_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p26_K : List CutV := p26_C.map (mkCut p26_Z)
theorem p26_W : ∀ c ∈ p26_K, CutP p26_R p26_T c := cutsGood p26_Y (by decide +kernel)
theorem p26_Q : p26_P.all (sepOK p26_T) = true := by decide +kernel
def p26_D4 : List StD := []
theorem p26_I4 : LevelN p26_R p26_T 4 p26_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p26_D5 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1,dS 0x201,pH 0x1111111111 1 2)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p26_C5x0 : levelOK p26_T p26_K p26_P 4 (p26_D4.map Prod.fst) ((p26_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p26_I5 : LevelN p26_R p26_T 5 p26_D5 := levelStep p26_B p26_W p26_Q p26_I4 (chunks 64 p26_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C5x0
  ))
theorem p26_L : LowN p26_R p26_T 6 := lowSearch p26_B p26_I5 (by decide +kernel)
def p27_T : Nat := 0xfefefeeafefefeeafefefeeafefefeea
def p27_R : List Nat := [0, 1, 2, 3, 4]
def p27_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
theorem p27_S0 : SliceN p27_R p27_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p27_B p10_B p10_L (by decide +kernel)
def p27_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p27_Y : ∀ s ∈ p27_Z, SliceN p27_R p27_T s := by
  unfold p27_Z
  simp only [List.forall_mem_cons]
  exact ⟨p27_S0,by simp⟩
noncomputable def p27_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p27_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p27_K : List CutV := p27_C.map (mkCut p27_Z)
theorem p27_W : ∀ c ∈ p27_K, CutP p27_R p27_T c := cutsGood p27_Y (by decide +kernel)
theorem p27_Q : p27_P.all (sepOK p27_T) = true := by decide +kernel
def p27_D4 : List StD := []
theorem p27_I4 : LevelN p27_R p27_T 4 p27_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p27_D5 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1,dS 0x201,pH 0x1111111111 1 2)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p27_C5x0 : levelOK p27_T p27_K p27_P 4 (p27_D4.map Prod.fst) ((p27_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p27_I5 : LevelN p27_R p27_T 5 p27_D5 := levelStep p27_B p27_W p27_Q p27_I4 (chunks 64 p27_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C5x0
  ))
theorem p27_L : LowN p27_R p27_T 6 := lowSearch p27_B p27_I5 (by decide +kernel)
def p28_T : Nat := 0xfffefefafffefefafffefefafffefefa
def p28_R : List Nat := [0, 1, 2, 3, 4]
def p28_E : List (Nat × Nat × Nat) := [(0,0,1),(1,8,10),(2,0,4),(3,2,10),(4,2,18)]
theorem p28_B : baseOK p28_T p28_R p28_E = true := by decide +kernel
theorem p28_S0 : SliceN p28_R p28_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p28_B p6_B p6_L (by decide +kernel)
def p28_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p28_Y : ∀ s ∈ p28_Z, SliceN p28_R p28_T s := by
  unfold p28_Z
  simp only [List.forall_mem_cons]
  exact ⟨p28_S0,by simp⟩
noncomputable def p28_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p28_P : List (Nat × Nat) := [(8,10),(0,1)]
noncomputable def p28_K : List CutV := p28_C.map (mkCut p28_Z)
theorem p28_W : ∀ c ∈ p28_K, CutP p28_R p28_T c := cutsGood p28_Y (by decide +kernel)
theorem p28_Q : p28_P.all (sepOK p28_T) = true := by decide +kernel
def p28_D4 : List StD := []
theorem p28_I4 : LevelN p28_R p28_T 4 p28_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p28_D5 : List StD := [
([w1,w2,w0,w3,w4],dL 0x1,dS 0x201,pH 0x1111111111 1 2)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p28_C5x0 : levelOK p28_T p28_K p28_P 4 (p28_D4.map Prod.fst) ((p28_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p28_I5 : LevelN p28_R p28_T 5 p28_D5 := levelStep p28_B p28_W p28_Q p28_I4 (chunks 64 p28_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C5x0
  ))
theorem p28_L : LowN p28_R p28_T 6 := lowSearch p28_B p28_I5 (by decide +kernel)
def ptopT : Nat := 0xfefefee8feeafc88fefefee8feeafc88
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,5,37)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0x55555555555555555555555555555555,8,[1, 2, 3, 4, 5]) := mkSlice (w:=0) ptopB p2_B p2_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0x33333333333333333333333333333333,8,[0, 2, 3, 4, 5]) := mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[0, 1, 3, 4, 5]) := mkSlice (w:=4) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) ptopB p13_B p13_L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff,9,[0, 1, 2, 3, 5]) := mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,8,[0, 1, 2, 3, 4]) := mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8,[0, 1, 3, 4, 5]) := mkSlice (w:=0) ptopB p24_B p24_L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0x550055005500550055005500550055,7,[1, 2, 4, 5]) := mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0x555500000000000055550000,4,[1, 2, 3]) := mkSlice (w:=16) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS9 : SliceN ptopR ptopT (0xffff000000000000ffff00000000,7,[0, 1, 2, 3]) := mkSlice (w:=32) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS10 : SliceN ptopR ptopT (0xffffffff00000000ffffffff00000000,8,[0, 1, 2, 3, 4]) := mkSlice (w:=32) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS11 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4, 5]) := mkSlice (w:=1) ptopB p26_B p26_L (by decide +kernel)
theorem ptopS12 : SliceN ptopR ptopT (0x22222222222222222222222222222222,5,[2, 3, 4, 5]) := mkSlice (w:=1) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS13 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3, 5]) := mkSlice (w:=16) ptopB p27_B p27_L (by decide +kernel)
theorem ptopS14 : SliceN ptopR ptopT (0xffff000000000000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS15 : SliceN ptopR ptopT (0x5555000055550000555500005555,5,[1, 2, 3, 5]) := mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS16 : SliceN ptopR ptopT (0x5555000000000000555500000000,4,[1, 2, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS17 : SliceN ptopR ptopT (0x2222000022220000222200002222,4,[2, 3, 5]) := mkSlice (w:=1) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS18 : SliceN ptopR ptopT (0x50505050505050505050505050505050,5,[1, 3, 4, 5]) := mkSlice (w:=4) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS19 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f,5,[0, 1, 3, 5]) := mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel)
theorem ptopS20 : SliceN ptopR ptopT (0x55550000555500005555000055550000,5,[1, 2, 3, 5]) := mkSlice (w:=16) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS21 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f0,5,[0, 1, 3, 5]) := mkSlice (w:=4) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS22 : SliceN ptopR ptopT (0x555555550000000055555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS23 : SliceN ptopR ptopT (0x55555555000000005555555500000000,5,[1, 2, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS24 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS25 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f00000000,5,[0, 1, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS26 : SliceN ptopR ptopT (0x44444444444444444444444444444444,5,[2, 3, 4, 5]) := mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS27 : SliceN ptopR ptopT (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4, 5]) := mkSlice (w:=2) ptopB p28_B p28_L (by decide +kernel)
theorem ptopS28 : SliceN ptopR ptopT (0xaaaa0000aaaa0000aaaa0000aaaa,5,[1, 2, 3, 5]) := mkSlice (w:=1) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS29 : SliceN ptopR ptopT (0x30303030303030303030303030303030,5,[0, 3, 4, 5]) := mkSlice (w:=4) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS30 : SliceN ptopR ptopT (0x3333000033330000333300003333,5,[0, 2, 3, 5]) := mkSlice (w:=0) ptopB p9_B p9_L (by decide +kernel)
theorem ptopS31 : SliceN ptopR ptopT (0x550000005500000055000000550000,4,[1, 2, 5]) := mkSlice (w:=16) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS32 : SliceN ptopR ptopT (0xcc00cc00cc00cc00cc00cc00cc00cc,5,[0, 2, 4, 5]) := mkSlice (w:=2) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS33 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) ptopB p23_B p23_L (by decide +kernel)
theorem ptopS34 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f0,7,[0, 1, 4, 5]) := mkSlice (w:=4) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS35 : SliceN ptopR ptopT (0xf0000000f0000000f0000000f0,4,[0, 1, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS36 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f,5,[0, 1, 4, 5]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS37 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00000000,7,[0, 1, 2, 4]) := mkSlice (w:=32) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS38 : SliceN ptopR ptopT (0xffff000000000000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS39 : SliceN ptopR ptopT (0x440044004400440044004400440044,4,[2, 4, 5]) := mkSlice (w:=2) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS40 : SliceN ptopR ptopT (0x33333333000000003333333300000000,5,[0, 2, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS41 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff0000,5,[0, 1, 2, 5]) := mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS42 : SliceN ptopR ptopT (0x500050005000500050005000500050,4,[1, 4, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS43 : SliceN ptopR ptopT (0x300030003000300030003000300030,4,[0, 4, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS44 : SliceN ptopR ptopT (0x330033000000000033003300000000,4,[0, 2, 4]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS45 : SliceN ptopR ptopT (0xf0f0000000000000f0f00000000,4,[0, 1, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS46 : SliceN ptopR ptopT (0x550055000000000055005500000000,4,[1, 2, 4]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS47 : SliceN ptopR ptopT (0x3333000000000000333300000000,4,[0, 2, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
def ptopZ : List SliceD := [(0x55555555555555555555555555555555,8,[1, 2, 3, 4, 5]),(0x33333333333333333333333333333333,8,[0, 2, 3, 4, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[0, 1, 3, 4, 5]),(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),(0xffff0000ffff0000ffff0000ffff,9,[0, 1, 2, 3, 5]),(0xffffffff00000000ffffffff,8,[0, 1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8,[0, 1, 3, 4, 5]),(0x550055005500550055005500550055,7,[1, 2, 4, 5]),(0x555500000000000055550000,4,[1, 2, 3]),(0xffff000000000000ffff00000000,7,[0, 1, 2, 3]),(0xffffffff00000000ffffffff00000000,8,[0, 1, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4, 5]),(0x22222222222222222222222222222222,5,[2, 3, 4, 5]),(0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3, 5]),(0xffff000000000000ffff0000,5,[0, 1, 2, 3]),(0x5555000055550000555500005555,5,[1, 2, 3, 5]),(0x5555000000000000555500000000,4,[1, 2, 3]),(0x2222000022220000222200002222,4,[2, 3, 5]),(0x50505050505050505050505050505050,5,[1, 3, 4, 5]),(0xf0f00000f0f00000f0f00000f0f,5,[0, 1, 3, 5]),(0x55550000555500005555000055550000,5,[1, 2, 3, 5]),(0xf0f00000f0f00000f0f00000f0f0,5,[0, 1, 3, 5]),(0x555555550000000055555555,5,[1, 2, 3, 4]),(0x55555555000000005555555500000000,5,[1, 2, 3, 4]),(0xf0f0f0f000000000f0f0f0f0,5,[0, 1, 3, 4]),(0xf0f0f0f000000000f0f0f0f00000000,5,[0, 1, 3, 4]),(0x44444444444444444444444444444444,5,[2, 3, 4, 5]),(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4, 5]),(0xaaaa0000aaaa0000aaaa0000aaaa,5,[1, 2, 3, 5]),(0x30303030303030303030303030303030,5,[0, 3, 4, 5]),(0x3333000033330000333300003333,5,[0, 2, 3, 5]),(0x550000005500000055000000550000,4,[1, 2, 5]),(0xcc00cc00cc00cc00cc00cc00cc00cc,5,[0, 2, 4, 5]),(0xf0f0f0f000000000f0f0f0f,4,[0, 1, 3, 4]),(0xf000f000f000f000f000f000f000f0,7,[0, 1, 4, 5]),(0xf0000000f0000000f0000000f0,4,[0, 1, 5]),(0xf000f000f000f000f000f000f000f,5,[0, 1, 4, 5]),(0xff00ff0000000000ff00ff00000000,7,[0, 1, 2, 4]),(0xffff000000000000ffff,4,[0, 1, 2, 3]),(0x440044004400440044004400440044,4,[2, 4, 5]),(0x33333333000000003333333300000000,5,[0, 2, 3, 4]),(0xff000000ff000000ff000000ff0000,5,[0, 1, 2, 5]),(0x500050005000500050005000500050,4,[1, 4, 5]),(0x300030003000300030003000300030,4,[0, 4, 5]),(0x330033000000000033003300000000,4,[0, 2, 4]),(0xf0f0000000000000f0f00000000,4,[0, 1, 3]),(0x550055000000000055005500000000,4,[1, 2, 4]),(0x3333000000000000333300000000,4,[0, 2, 3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,ptopS9,ptopS10,ptopS11,ptopS12,ptopS13,ptopS14,ptopS15,ptopS16,ptopS17,ptopS18,ptopS19,ptopS20,ptopS21,ptopS22,ptopS23,ptopS24,ptopS25,ptopS26,ptopS27,ptopS28,ptopS29,ptopS30,ptopS31,ptopS32,ptopS33,ptopS34,ptopS35,ptopS36,ptopS37,ptopS38,ptopS39,ptopS40,ptopS41,ptopS42,ptopS43,ptopS44,ptopS45,ptopS46,ptopS47,by simp⟩
noncomputable def ptopC : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x6030202010104,dC 0x6030202010105,dC 0x5040201,dC 0x5040202,dC 0x5040203,dC 0x5040206030202010104,dC 0x6030202010106,dC 0x5040401,dC 0x5040402,dC 0x5040403,dC 0x6030205040402010104,dC 0x7,dC 0x6030302010104,dC 0x6030302010105,dC 0x5040207,dC 0x5040206030302010104,dC 0x6030302010106,dC 0x5040407,dC 0x6030305040402010104,dC 0x2010104,dC 0x8,dC 0x6040202010105,dC 0x4020201,dC 0x4020202,dC 0x6030202010107,dC 0x6030202010103,dC 0x3020208,dC 0x9,dC 0x4020301,dC 0x4020302,dC 0x3020308,dC 0x504020201010a,dC 0x5020101,dC 0x5020102,dC 0x4020108,dC 0x5020201,dC 0x5020202,dC 0x6040202010106,dC 0x5030206040202010105,dC 0x4020208,dC 0x604020201010b,dC 0x5020301,dC 0x5020302,dC 0x4020308,dC 0x5020401,dC 0x5020402,dC 0x4020408,dC 0x301020c,dC 0x6010405040202,dC 0xd,dC 0x4030208,dC 0x6040205010402010105,dC 0x6040205010402010106,dC 0x4030408,dC 0x6040202010104,dC 0x2010105,dC 0x6040202010107,dC 0x6040202010103,dC 0xe,dC 0x4030206040202010104,dC 0xf,dC 0x6040204030302010104,dC 0x201010a,dC 0x10,dC 0x401020c,dC 0x6050205010402010106,dC 0x605020201010b,dC 0x5040206040202010104,dC 0x6050202010106,dC 0x6040205040402010104,dC 0x6,dC 0x4020101,dC 0x4020102,dC 0x7030106040202010104,dC 0x11,dC 0x7030206040202010104,dC 0x7030306040202010104,dC 0x4020401,dC 0x4020402,dC 0x7030406040202010104,dC 0x6040205030102010104,dC 0x5030206040202010104,dC 0x6040205030302010104,dC 0x6040205030402010104,dC 0x5040101,dC 0x5040102,dC 0x7050106040202010104,dC 0x6030205040101,dC 0x6030205040102,dC 0x2010112,dC 0x7020106030205040101,dC 0x8030107050106040202010104,dC 0x6050204030102010106,dC 0x7020206030205040102,dC 0x4030206050202010106,dC 0x3020211,dC 0x7050206040202010104,dC 0x5040301,dC 0x5040302,dC 0x7050406040202010104,dC 0x7050306040202010104,dC 0x5,dC 0xb,dC 0x6050202010104,dC 0x6050202010105,dC 0xa,dC 0x6050302010104,dC 0x6050302010105,dC 0x6050302010107,dC 0x6050302010103,dC 0x4030206050302010104,dC 0x5030206,dC 0x5030306,dC 0x6050304030302010104,dC 0x2010103,dC 0x4030202010104,dC 0x13,dC 0x6040302010107,dC 0x14,dC 0x2010107,dC 0x6040302010103,dC 0x15,dC 0x16,dC 0x2010104030304,dC 0x2010106,dC 0x17,dC 0x5030102010104,dC 0x5030105,dC 0x5030202010104,dC 0x18,dC 0x19,dC 0x2010105030304,dC 0x1a,dC 0x2010105030404,dC 0x5030405,dC 0x5040202010104,dC 0x201010b,dC 0x6050302010106,dC 0x2010106010405040204,dC 0x2010105010405,dC 0x2010105040404,dC 0xc,dC 0x2010202,dC 0x2010203,dC 0x1b,dC 0x2010401,dC 0x1c,dC 0x2010206020403010204,dC 0x2010206020403010205,dC 0x1d,dC 0x3010202010204,dC 0x3010206,dC 0x301020b,dC 0x2010206,dC 0x201020b,dC 0x2010201,dC 0x2010402,dC 0x2010207,dC 0x2010206020203010404,dC 0x2010206020203010405,dC 0x2010203010404,dC 0x3010406,dC 0x301040b,dC 0x2010204,dC 0x4010202,dC 0x2010205,dC 0x4010201,dC 0x4020204010202010204,dC 0x201020f,dC 0x201020a,dC 0x4010401,dC 0x2010202010305,dC 0x2010206020404010204,dC 0x4010207,dC 0x4010203,dC 0x4010202010204,dC 0x4010301,dC 0x4010204010302,dC 0x4010206040402010204,dC 0x6040402010207,dC 0x5010202,dC 0x5010401,dC 0x2010206020405010204,dC 0x2010206020405010205,dC 0x5010207,dC 0x5010203,dC 0x5010202010204,dC 0x5010201,dC 0x2010206020205010404,dC 0x2010206020205010405,dC 0x5010402,dC 0x2010205010404,dC 0x5010407,dC 0x5010403,dC 0x2010206010403020204,dC 0x2010206010403020205,dC 0x3020202010204,dC 0x3020202010205,dC 0x2010204010301,dC 0x4010302,dC 0x6040402010203,dC 0x302020e,dC 0x201021d,dC 0x12,dC 0x3020206040402010204,dC 0x3020206,dC 0x302020201020a,dC 0x302020f,dC 0x504041c,dC 0x3020206050402010206,dC 0x302020b,dC 0x6040402010201,dC 0x201020e,dC 0x4010101,dC 0x2010204020307,dC 0x2010206040403020204,dC 0x201020302020a,dC 0x2010203020205,dC 0x504021c,dC 0x5040202010203,dC 0x6010105040202,dC 0x6010105040201,dC 0x201021a,dC 0x6050102010206,dC 0x302020201020b,dC 0x2010215,dC 0x3020202010206,dC 0x2010205040403,dC 0x2010206010203020404,dC 0x2010206010203020405,dC 0x2010203020404,dC 0x6040202010401,dC 0x6040202010203020404,dC 0x3020402010205,dC 0x302040201020a,dC 0x2010203020405,dC 0x2010404010301,dC 0x201041d,dC 0x3020406040402010204,dC 0x3020406,dC 0x302040f,dC 0x302040b,dC 0x201020302040b,dC 0x1e,dC 0x5040202010207,dC 0x6050404020303,dC 0x201020302040a,dC 0x2010203020406,dC 0x2010205040407,dC 0x4020202010204,dC 0x2010206010404020204,dC 0x4010402,dC 0x2010202010405,dC 0x201020201040a,dC 0x4020207,dC 0x4020203,dC 0x4010204010301,dC 0x4020206040402010204,dC 0x7010104020202010204,dC 0x301021c,dC 0x3010208,dC 0x6040202010202010105,dC 0x1f,dC 0x401020201020f,dC 0x504020201020201010a,dC 0x2010202010105,dC 0x201020201010a,dC 0x7010404020202010204,dC 0x4010202010101,dC 0x2010102,dC 0x6030104020202010204,dC 0x4020202010207,dC 0x6030102010205,dC 0x503010201020a,dC 0x2010109,dC 0x4010202010301,dC 0x4020202010203,dC 0x6030404020202010204,dC 0x6030402010205,dC 0x503040201020a,dC 0x2010309,dC 0x2010302,dC 0x6040404020202010204,dC 0x7060402010204020304,dC 0x2010204020304,dC 0x2010104010301,dC 0x7030102010204020304,dC 0x2010304010301,dC 0x2010204020303,dC 0x7030402010204020304,dC 0x5020202010204,dC 0x2010206010405020204,dC 0x2010206010405020205,dC 0x5020207,dC 0x5020203,dC 0x5020202010205,dC 0x2010206010205020404,dC 0x2010206010205020405,dC 0x2010205020404,dC 0x6040205010401,dC 0x6040202010205020404,dC 0x6040205020407,dC 0x6040205020403,dC 0x5020402010205,dC 0x2010205020405,dC 0x5020407,dC 0x5020403,dC 0x2010101,dC 0x6030102010204,dC 0x6040202010101,dC 0x6040202010102,dC 0x402020c,dC 0x402021c,dC 0x5030202010108,dC 0x20,dC 0x2010202010101,dC 0x2010202010102,dC 0x21,dC 0x4020121,dC 0x402011d,dC 0x6030206030102010204,dC 0x6030206030102010205,dC 0x4010202010102,dC 0x6040202010207,dC 0x6040206030102010204,dC 0x6030102010206,dC 0x6050102010104010201,dC 0x6050102010104010202,dC 0x5040102010103010208,dC 0x6050106030102010205,dC 0x2010104010302,dC 0x6030106040402010204,dC 0x6030106050402010206,dC 0x6050102010207,dC 0x6050102010203,dC 0x603010201020b,dC 0x5010102010101,dC 0x5010102010102,dC 0x6050106030102010204,dC 0x2010115,dC 0x22,dC 0x6040302010203,dC 0x6050402010207,dC 0x6050402010203,dC 0x6050302010207,dC 0x6050202010203,dC 0x6030106050302010204,dC 0x7060302010205040203,dC 0x7060102010205040203,dC 0x6030202010204,dC 0x6030202010205,dC 0x2010205010301,dC 0x2010205010302,dC 0x603020201020b,dC 0x6030206050402010204,dC 0x6030405010302010201,dC 0x6030406050402010207,dC 0x503020201020a,dC 0x4010315,dC 0x6040405010302010202,dC 0x6040406050402010207,dC 0x5030404010302010208,dC 0x6030402010201,dC 0x6040402010202,dC 0x5030402010208,dC 0x6050102010201,dC 0x6050102010202,dC 0x5040102010208,dC 0x6050402010201,dC 0x6050402010202,dC 0x5040402010208,dC 0x2010301,dC 0x6030402010204,dC 0x6040202010301,dC 0x6040202010302,dC 0x402030c,dC 0x402031c,dC 0x5030202010308,dC 0x2010223,dC 0x6030306030402010204,dC 0x6030306030402010205,dC 0x4010202010302,dC 0x6040202010203,dC 0x6040206030402010204,dC 0x6030402010206,dC 0x603040201020b,dC 0x2010306050404010201,dC 0x2010306050404010202,dC 0x2010305040403010208,dC 0x6030406050402010205,dC 0x6030406040402010204,dC 0x6030406050402010206,dC 0x5010202010301,dC 0x5010202010302,dC 0x6050206030402010204,dC 0x2010315,dC 0x2010306040405010202,dC 0x2010305030404010208,dC 0x2010305010301,dC 0x2010305010302,dC 0x6030406050402010204,dC 0x3010112,dC 0x7060302010205040207,dC 0x7060102010205040207,dC 0x6030302010204,dC 0x6030302010206,dC 0x6050106030302010204,dC 0x6040202010204,dC 0x6040206040402010204,dC 0x6050104010304010201,dC 0x6050104010304010202,dC 0x5040103010303010208,dC 0x6050402010206,dC 0x6050104010201,dC 0x6050104010202,dC 0x6050102010205,dC 0x5040103010208,dC 0x6050404010201,dC 0x6050404010202,dC 0x6050402010205,dC 0x5040403010208,dC 0x6010404020204,dC 0x4010204010402,dC 0x7010406040202010204,dC 0x6050104010404010202,dC 0x6050102010402010205,dC 0x6010405020206,dC 0x6020404010204,dC 0x4010204010401,dC 0x7020406040202010204,dC 0x6020104010201,dC 0x6020104010202,dC 0x7030106040202010204,dC 0x6050106020104010201,dC 0x6050106020104010202,dC 0x5040105020103010208,dC 0x6020404010201,dC 0x6020404010202,dC 0x7030406040202010204,dC 0x6020406050404010201,dC 0x6020406050404010202,dC 0x5020405040403010208,dC 0x7050106040202010204,dC 0x6050202010206,dC 0x605020201020b,dC 0x7050406040202010204,dC 0x6040402010204,dC 0x7040402010204030304,dC 0x7040402010205040404,dC 0x4030306040402010204,dC 0x5040404010301,dC 0x5040404010302,dC 0x5040406040402010204,dC 0x5010101,dC 0x5010102,dC 0x6050102010204,dC 0x6040205010101,dC 0x6040205010102,dC 0x5030204010108,dC 0x5010205010101,dC 0x5010205010102,dC 0x6050206050102010204,dC 0x6050206050102010205,dC 0x502030c,dC 0x502031c,dC 0x7050102010205030304,dC 0x7050102010205030305,dC 0x5010105020301,dC 0x5010105020302,dC 0x6050202010204,dC 0x6050202010205,dC 0x6040405010201,dC 0x6040405010202,dC 0x5030404010208,dC 0x5010301,dC 0x5010302,dC 0x6050402010204,dC 0x6050306050402010204,dC 0x6050306050402010205,dC 0x5020105010301,dC 0x5020105010302,dC 0x502010c,dC 0x6050405030102010204,dC 0x502011c,dC 0x6050302010204,dC 0x4030202010204,dC 0x6010104020201,dC 0x6010104020202,dC 0x7060102010204030204,dC 0x6030302010205,dC 0x503030201020a,dC 0x6010204020301,dC 0x5010203020308,dC 0x6010304020301,dC 0x6010304020302,dC 0x7060402010204030304,dC 0x24,dC 0x2010204030304,dC 0x6010205020102,dC 0x6010202010205030104,dC 0x5030102010204,dC 0x6010205020101,dC 0x6020202010205030104,dC 0x5030102010205,dC 0x5010204020108,dC 0x6010305020102,dC 0x6010305020101,dC 0x7060402010205030104,dC 0x7060402010205030105,dC 0x5010304020108,dC 0x6030206030402010207,dC 0x6030202010207,dC 0x3010209,dC 0x6040202010206,dC 0x2010225,dC 0x6030402010207,dC 0x3010309,dC 0x6040402010206,dC 0x3020206030402010207,dC 0x3010202010207,dC 0x2010203010307,dC 0x6040205020101,dC 0x6040205020102,dC 0x6040202010205030104,dC 0x7060102010205030105,dC 0x5030202010204,dC 0x6010105020201,dC 0x6010105020202,dC 0x502020c,dC 0x7060102010205030204,dC 0x502021c,dC 0x5010104020208,dC 0x6010205020301,dC 0x5010204020308,dC 0x6030202010206,dC 0x6010305020301,dC 0x6010305020302,dC 0x7060402010205030304,dC 0x5010304020308,dC 0x2010226,dC 0x2010205030304,dC 0x6010205020401,dC 0x6050202010207,dC 0x5010204020408,dC 0x6010305020401,dC 0x6010305020402,dC 0x502040c,dC 0x7060402010205030404,dC 0x502041c,dC 0x7060402010205030405,dC 0x5010304020408,dC 0x2010205030404,dC 0x6040205020401,dC 0x6040205020402,dC 0x6040202010205030404,dC 0x5030402010205,dC 0x2010205030405,dC 0x5040202010204,dC 0x504020c,dC 0x7060102010205040204,dC 0x27,dC 0x6050302010205,dC 0x6050302010206,dC 0x2010205040404,dC 0x2010304,dC 0x6040202010303,dC 0x6040203020202010304,dC 0x2010303020205,dC 0x4020107,dC 0x201030302020a,dC 0x6040203020402010304,dC 0x2010303020405,dC 0x302040e,dC 0x4020103,dC 0x201030302040a,dC 0x6040202010307,dC 0x6040202010304,dC 0x2010305,dC 0x4020206040202010304,dC 0x201030a,dC 0x2010303,dC 0x3020202010304,dC 0x3020202010305,dC 0x6010402010303020204,dC 0x6010402010303020205,dC 0x2010306,dC 0x201030b,dC 0x5040202010303,dC 0x5040202010201,dC 0x2010307,dC 0x2010209,dC 0x302020201030b,dC 0x2010205040401,dC 0x302020201030a,dC 0x3020202010306,dC 0x2010305040403,dC 0x3020402010304,dC 0x3020402010305,dC 0x6010202010303020404,dC 0x6010202010303020405,dC 0x5040202010401,dC 0x302040201030b,dC 0x5040202010307,dC 0x2010405040401,dC 0x302040201030a,dC 0x3020402010306,dC 0x2010402010305,dC 0x6010402010304020204,dC 0x4020202010304,dC 0x5020202010304,dC 0x6010402010305020205,dC 0x6010402010305020204,dC 0x6020405010204,dC 0x5020402010304,dC 0x6010202010305020404,dC 0x6010202010305020405,dC 0x4030202010304,dC 0x6010404020202,dC 0x6030302010305,dC 0x6010204020302,dC 0x2010304030304,dC 0x5030102010304,dC 0x6010202010305030104,dC 0x6010202010305030105,dC 0x5030202010304,dC 0x6010405020202,dC 0x6030302010306,dC 0x6010205020302,dC 0x2010305030304,dC 0x6010205020402,dC 0x2010305030404,dC 0x5040202010304,dC 0x6050302010306,dC 0x2010305040404,dC 0x2010404,dC 0x4010206040202010404,dC 0x2010405,dC 0x6040202010404,dC 0x201040a,dC 0x2010403,dC 0x3010202010404,dC 0x2010402010307,dC 0x2010406020403010204,dC 0x2010406020403010205,dC 0x2010406,dC 0x201040b,dC 0x2010407,dC 0x3010402010404,dC 0x6020202010403010404,dC 0x6020202010403010405,dC 0x4010202010404,dC 0x4020204010202010404,dC 0x201040f,dC 0x2010406020404010204,dC 0x5010202010404,dC 0x2010406020405010204,dC 0x2010406020405010205,dC 0x2010402010306,dC 0x6010405020204,dC 0x5010402010404,dC 0x6020202010405010404,dC 0x6020202010405010405,dC 0x4020202010404,dC 0x4030202010404,dC 0x6010404020201,dC 0x6030302010405,dC 0x2010423,dC 0x28,dC 0x503020201040a,dC 0x2010404030304,dC 0x5030102010404,dC 0x5030102010405,dC 0x6020202010405030104,dC 0x6040202010405030104,dC 0x5030202010404,dC 0x6010405020201,dC 0x5010404020208,dC 0x6030302010406,dC 0x29,dC 0x2010426,dC 0x2010405030304,dC 0x2010405030404,dC 0x6040202010405030404,dC 0x2010405030405,dC 0x5040202010404,dC 0x6010405040201,dC 0x5010404030208,dC 0x6050302010405,dC 0x6010402010405040204,dC 0x5010402010405,dC 0x2010405040404,dC 0x6020203010104,dC 0x6020203010105,dC 0x4020206020203010104,dC 0x502020301010a,dC 0x4020307,dC 0x6020204020303010104,dC 0x6020203010106,dC 0x5020206020203010104,dC 0x602020301010b,dC 0x5020307,dC 0x6020205020303010104,dC 0x6040402010102,dC 0x7040406020203010104,dC 0x3010308,dC 0x6050102010102,dC 0x5020107,dC 0x7050106020203010104,dC 0x6050402010102,dC 0x7050406020203010104,dC 0x7050406020203010105,dC 0x5040206020203010104,dC 0x5040202010102,dC 0x6020105040207,dC 0x5010104030208,dC 0x2010105040402,dC 0x6020205040403010104,dC 0x3010104,dC 0x6040203010104,dC 0x3010105,dC 0x4020206040203010104,dC 0x301010a,dC 0x4020407,dC 0x3010408,dC 0x503010201030a,dC 0x5040206040203010104,dC 0x6050203010106,dC 0x605020301010b,dC 0x4020203010104,dC 0x6020303010105,dC 0x3010104020304,dC 0x3010106,dC 0x4010108,dC 0x5020103010104,dC 0x5020203010104,dC 0x6020303010106,dC 0x4010208,dC 0x4010308,dC 0x3010105020304,dC 0x602030301010b,dC 0x4010408,dC 0x301010b,dC 0x3010105020404,dC 0x5040203010104,dC 0x6050303010105,dC 0x6050303010106,dC 0x3010105040404,dC 0x3010204,dC 0x3010205,dC 0x4010203010204,dC 0x4010204010307,dC 0x4010206040403010204,dC 0x301020a,dC 0x5010203010204,dC 0x3010205010404,dC 0x6040203010203020404,dC 0x3020403010205,dC 0x301020e,dC 0x301020d,dC 0x4020303,dC 0x3010203020404,dC 0x3010203020405,dC 0x5040203010203020404,dC 0x301020302040b,dC 0x403020d,dC 0x5040202010202,dC 0x403021b,dC 0x6010105040207,dC 0x6050103020403010205,dC 0x4030223,dC 0x403040d,dC 0x403041b,dC 0x3010203020405040404,dC 0x3010203020406,dC 0x2010205040402,dC 0x6020403010204,dC 0x6020403010205,dC 0x5030202010408,dC 0x3020323,dC 0x6040402010401,dC 0x502040301020a,dC 0x5040206020403010204,dC 0x6020403010206,dC 0x602040301020b,dC 0x2010305040407,dC 0x6020405040403010204,dC 0x4020203010204,dC 0x6010104020207,dC 0x6020103010205,dC 0x5020103010208,dC 0x3020223,dC 0x502010301020a,dC 0x6020304010301,dC 0x3010204020304,dC 0x6040404020303010204,dC 0x6010205020107,dC 0x3010206010205020104,dC 0x6010205020103,dC 0x3010205020104,dC 0x5020103,dC 0x6020305010101,dC 0x6010305020107,dC 0x5020304010108,dC 0x4020123,dC 0x5020203010204,dC 0x6020105010201,dC 0x6010105020207,dC 0x5020104010208,dC 0x4020223,dC 0x5020303,dC 0x6020305010301,dC 0x6010305020307,dC 0x4020323,dC 0x3010205020304,dC 0x6020305010401,dC 0x6010305020407,dC 0x5020304010408,dC 0x4020423,dC 0x3010205020404,dC 0x6040203010205020404,dC 0x5020403010205,dC 0x301011b,dC 0x5030204020423,dC 0x6050103010206,dC 0x3010205020405,dC 0x201021c,dC 0x2010204020302,dC 0x3010206020204030304,dC 0x4020403,dC 0x3010203020205,dC 0x3010204030304,dC 0x4010307,dC 0x6040403010204,dC 0x6050403010206,dC 0x5040406040403010204,dC 0x5040203010204,dC 0x6020405040203,dC 0x3010206020405040204,dC 0x2010205040202,dC 0x6020105040201,dC 0x602020301020b,dC 0x6050103010205,dC 0x3010205040404,dC 0x6020203010304,dC 0x4020206020203010304,dC 0x6020203010305,dC 0x6020204020303010304,dC 0x6040402010302,dC 0x502020301030a,dC 0x5040206020203010304,dC 0x5040202010302,dC 0x6020203010306,dC 0x602020301030b,dC 0x403021e,dC 0x2010305040402,dC 0x6020205040403010304,dC 0x3010304,dC 0x6040203010304,dC 0x3010305,dC 0x4020206040203010304,dC 0x503040201030a,dC 0x301030a,dC 0x4020203010304,dC 0x6040302010302,dC 0x6020303010305,dC 0x3010304020304,dC 0x5020103010304,dC 0x6010203010305020104,dC 0x5020203010304,dC 0x6050302010302,dC 0x6020303010306,dC 0x3010305020304,dC 0x3010306,dC 0x602030301030b,dC 0x6010205020407,dC 0x5020403010304,dC 0x5040203010304,dC 0x301030b,dC 0x6010405040207,dC 0x6050303010306,dC 0x3010305040404,dC 0x6020203010404,dC 0x6020203010405,dC 0x6040202010201,dC 0x5030202010208,dC 0x2a,dC 0x502020301040a,dC 0x5040206020203010404,dC 0x5040202010402,dC 0x602020301040b,dC 0x6020203010406,dC 0x6020205040403010404,dC 0x3010404,dC 0x4010206040203010404,dC 0x3010405,dC 0x4010303,dC 0x6040203010404,dC 0x6040202010402,dC 0x301040a,dC 0x4010203010404,dC 0x5010203010404,dC 0x5010403010404,dC 0x3020203010404,dC 0x301030d,dC 0x3010406040403020204,dC 0x301040e,dC 0x3010403020205,dC 0x3020203010405,dC 0x5040203020203010404,dC 0x302020301040b,dC 0x3020203010405040404,dC 0x3020203010406,dC 0x2010405040402,dC 0x4020203010404,dC 0x2b,dC 0x502030301040a,dC 0x6020204010301,dC 0x6010304020303,dC 0x5020203010308,dC 0x3010404020304,dC 0x6020205010101,dC 0x6010305020103,dC 0x5020204010108,dC 0x5020103010404,dC 0x5020203010404,dC 0x6020405010201,dC 0x6010105020203,dC 0x5020404010208,dC 0x3010426,dC 0x6020205010301,dC 0x6010305020303,dC 0x5020204010308,dC 0x3010405020304,dC 0x6020205010401,dC 0x6010305020403,dC 0x6050202010402,dC 0x602030301040b,dC 0x5020204010408,dC 0x3010405020404,dC 0x6040203010405020404,dC 0x5020403010405,dC 0x3010405020405,dC 0x4030203010404,dC 0x201041c,dC 0x3010403020405,dC 0x3010406020404030204,dC 0x5040203010404,dC 0x6020405040201,dC 0x6010105040203,dC 0x5020404030208,dC 0x6050303010405,dC 0x6020405040207,dC 0x3010406020405040204,dC 0x2010405040202,dC 0x3010405040404,dC 0x4,dC 0x4010204,dC 0x4010206040205010404,dC 0x5010206,dC 0x5010405,dC 0x501020b,dC 0x4010205010404,dC 0x6010203020105,dC 0x4010206010203020104,dC 0x501020302010a,dC 0x3020105,dC 0x4010203020104,dC 0x6040204010203020104,dC 0x302010a,dC 0x6040302010101,dC 0x6010303020105,dC 0x5030302010108,dC 0x501030302010a,dC 0x3020106,dC 0x3020205,dC 0x4010203020204,dC 0x6040102010201,dC 0x5030102010208,dC 0x3010223,dC 0x501010302020a,dC 0x6040402010402,dC 0x501040302020a,dC 0x302020a,dC 0x6050104010203,dC 0x5010203020206,dC 0x706030501020302020b,dC 0x2010210,dC 0x4010203020304,dC 0x3020305,dC 0x4010206040203020304,dC 0x6010203020305,dC 0x6040302010301,dC 0x6010303020305,dC 0x5030302010308,dC 0x302030a,dC 0x3020306,dC 0x4010203020404,dC 0x3020405,dC 0x6040202010202,dC 0x6010203020405,dC 0x6040302010401,dC 0x6010303020405,dC 0x5030302010408,dC 0x2c,dC 0x501030302040a,dC 0x302040a,dC 0x6050104010207,dC 0x706020501020302040b,dC 0x5010203020406,dC 0x2010410,dC 0x4010204010102,dC 0x401021c,dC 0x7010104020204010204,dC 0x7010404020204010204,dC 0x4010204010101,dC 0x6020104020204010204,dC 0x6020404020204010204,dC 0x4020204010204,dC 0x4010204020101,dC 0x4020204010207,dC 0x6030104020204010204,dC 0x4010204020401,dC 0x301041b,dC 0x4020204010203,dC 0x6030404020204010204,dC 0x6020104010204,dC 0x6020206020104010204,dC 0x6020204010204,dC 0x6020206030104010204,dC 0x2010203010105,dC 0x201020301010a,dC 0x6050104020104010201,dC 0x5040103020103010208,dC 0x6030105010206,dC 0x6020206030404010204,dC 0x2010203010305,dC 0x5030202010223,dC 0x6040402010407,dC 0x201020301030a,dC 0x6020304010204,dC 0x2010302010405,dC 0x6020406020304010204,dC 0x6030106020304010204,dC 0x3010102010405,dC 0x301010201040a,dC 0x5020104010401,dC 0x5030102010305,dC 0x401010d,dC 0x6020404010207,dC 0x5030106020404010204,dC 0x6020405010206,dC 0x6020404010203,dC 0x401040d,dC 0x6020405030404010204,dC 0x6010205020105,dC 0x4010206010205020104,dC 0x5020105,dC 0x4010205020104,dC 0x6040204010205020104,dC 0x6040205020103,dC 0x6040305010101,dC 0x6010305020105,dC 0x5030304010108,dC 0x3020210,dC 0x201020d,dC 0x4030205010206,dC 0x5020404010226,dC 0x3020310,dC 0x201030d,dC 0x4010205020404,dC 0x5020405,dC 0x6050204010202,dC 0x5030204010408,dC 0x6040305010401,dC 0x6010305020405,dC 0x5030304010408,dC 0x2d,dC 0x201020c,dC 0x6010204020101,dC 0x5010203020108,dC 0x6030104010204,dC 0x4020204020101,dC 0x6030206030104010204,dC 0x3010203010105,dC 0x6030204010204,dC 0x6050104020201,dC 0x5040103020208,dC 0x6030304010204,dC 0x3010303010405,dC 0x6030406030304010204,dC 0x6010204020401,dC 0x201040c,dC 0x5010203020408,dC 0x6030404010204,dC 0x4010206010205030104,dC 0x6010205030105,dC 0x6020205030105,dC 0x4010206020205030104,dC 0x4010205030104,dC 0x6040204010205030104,dC 0x5030204020108,dC 0x6040305020101,dC 0x6010305030105,dC 0x5030304020108,dC 0x3010210,dC 0x402020f,dC 0x3020204010207,dC 0x5040403010223,dC 0x5030404010226,dC 0x402030f,dC 0x3010310,dC 0x6020205030405,dC 0x4010206020205030404,dC 0x4010205030404,dC 0x6050204010207,dC 0x6010205030405,dC 0x5030204020408,dC 0x6040305020401,dC 0x6050404010207,dC 0x5030304020408,dC 0x5010105,dC 0x6050104010204,dC 0x6010205040101,dC 0x6020205010105,dC 0x501020c,dC 0x5010204030108,dC 0x6050304010204,dC 0x6020104010302,dC 0x6020204010307,dC 0x6020204010303,dC 0x7030106020204010304,dC 0x6020205010306,dC 0x6020404010302,dC 0x7030406020204010304,dC 0x6020204010304,dC 0x6050104010302,dC 0x602020501030b,dC 0x7050106020204010304,dC 0x5020104010302,dC 0x5030106020204010304,dC 0x4010305020402,dC 0x6020205030404010304,dC 0x4010304,dC 0x2010108,dC 0x3020104010304,dC 0x6010204010303020104,dC 0x5010306,dC 0x6020304010302,dC 0x6020304010307,dC 0x2010208,dC 0x6010403020205,dC 0x3020204010304,dC 0x6040404010303020204,dC 0x2010308,dC 0x3020304010304,dC 0x6020304010303,dC 0x6020204010302,dC 0x2010408,dC 0x3020404010304,dC 0x6010204010305020104,dC 0x5020104010304,dC 0x602030501030b,dC 0x5020404010304,dC 0x5030104010304,dC 0x6010204010305030104,dC 0x5030404010304,dC 0x6020205010107,dC 0x3020206020205010104,dC 0x6020205010103,dC 0x6020203020305010104,dC 0x6020203020305010105,dC 0x6040405010102,dC 0x6020205010104,dC 0x4020206020205010104,dC 0x5020206,dC 0x6020204020305010104,dC 0x5020306,dC 0x6010304020401,dC 0x6020105010102,dC 0x7030106020205010105,dC 0x6020405010102,dC 0x6020204020305010103,dC 0x7030106020205010104,dC 0x7040406020205010103,dC 0x201022e,dC 0x7030406020205010104,dC 0x7030406020205010105,dC 0x7040406020205010107,dC 0x3010313,dC 0x7040406020205010104,dC 0x4030206020205010104,dC 0x4020205010102,dC 0x5010104020302,dC 0x6020204030305010104,dC 0x5010104,dC 0x6040205010107,dC 0x6040203020105010104,dC 0x5010103020105,dC 0x2010110,dC 0x6040203020205010104,dC 0x6040205010103,dC 0x5010103020205,dC 0x6040203020305010104,dC 0x5010103020305,dC 0x2010310,dC 0x6040203020405010104,dC 0x5010103020405,dC 0x6040205010104,dC 0x4020206040205010104,dC 0x6050102010305,dC 0x5020406,dC 0x4030206040205010104,dC 0x5010107,dC 0x401011f,dC 0x3020105010104,dC 0x3020105010105,dC 0x5010103,dC 0x6020305010107,dC 0x6020305010102,dC 0x3020205010104,dC 0x3020205010105,dC 0x501020302030a,dC 0x5010103020304,dC 0x6020305010103,dC 0x6020205010102,dC 0x5010103020404,dC 0x4020205010104,dC 0x6020305010105,dC 0x5010102010405,dC 0x5010106010404020204,dC 0x5010104020304,dC 0x4030205010104,dC 0x5010104030304,dC 0x5010204,dC 0x6010203020106,dC 0x5010206010203020104,dC 0x601020302010b,dC 0x5010203020104,dC 0x6050302010101,dC 0x6010303020106,dC 0x5040302010108,dC 0x3020126,dC 0x5010203020204,dC 0x5010203020205,dC 0x4010223,dC 0x5010203020304,dC 0x6050302010301,dC 0x6010303020306,dC 0x5040302010308,dC 0x5010203020404,dC 0x6050302010401,dC 0x6010303020406,dC 0x5040302010408,dC 0x3020426,dC 0x5010205020404,dC 0x6010205020404,dC 0x6020405010205,dC 0x6020205010304,dC 0x5010304,dC 0x5010307,dC 0x3020105010304,dC 0x6010205010303020104,dC 0x5010303,dC 0x6020305010302,dC 0x6020305010307,dC 0x3020205010304,dC 0x3020305010304,dC 0x6020305010303,dC 0x6020205010302,dC 0x6010203020406,dC 0x3020405010304,dC 0x6020205010404,dC 0x6020205010405,dC 0x6050204010201,dC 0x5040203010208,dC 0x4020205010201,dC 0x4020205010402,dC 0x6020205010407,dC 0x6020205010403,dC 0x4030206020205010404,dC 0x5010204020301,dC 0x6020204030305010404,dC 0x5010404,dC 0x501030b,dC 0x6040205010403,dC 0x6040205010407,dC 0x6040203020205010404,dC 0x6040203020405010404,dC 0x5010403020405,dC 0x6040205010404,dC 0x302010b,dC 0x6050202010101,dC 0x601030302010b,dC 0x5040202010108,dC 0x3020105010404,dC 0x601010302020b,dC 0x6020305010402,dC 0x6020305010407,dC 0x4010423,dC 0x3020205010404,dC 0x3020205010405,dC 0x5040205010403,dC 0x5040203020205010404,dC 0x5040205010407,dC 0x6050202010301,dC 0x601030302030b,dC 0x5040202010308,dC 0x5010403020304,dC 0x6050202010401,dC 0x601030302040b,dC 0x6020205010402,dC 0x6020305010403,dC 0x5040202010408,dC 0x2f,dC 0x5010403020404,dC 0x5040205010403020404,dC 0x502020b,dC 0x4020205010404,dC 0x6020305010405,dC 0x5010404010402,dC 0x5010406010404020204,dC 0x6050204010301,dC 0x601030502030b,dC 0x5040203010308,dC 0x5010404020304,dC 0x5020205010404,dC 0x5020205010405,dC 0x503020b,dC 0x4030205010404,dC 0x6050404020201,dC 0x601010503020b,dC 0x5040403020208,dC 0x6030305010405,dC 0x501041c,dC 0x6020405030206,dC 0x5010406020404030204,dC 0x6050204020301,dC 0x601030503030b,dC 0x5040203020308,dC 0x6020205030306,dC 0x602020503030b,dC 0x4020305010402,dC 0x6020205010404030304,dC 0x5010404030304,dC 0x503030b,dC 0x5040205010404,dC 0x5010406020405040204,dC 0x5010405020405,dC 0x6010203020104,dC 0x6040402010101,dC 0x5030402010108,dC 0x6050102010101,dC 0x7050106010203020104,dC 0x6050402010101,dC 0x7050406010203020104,dC 0x7050406010203020105,dC 0x5040206010203020104,dC 0x5040202010101,dC 0x5010203020126,dC 0x2010105040401,dC 0x504040c,dC 0x6010205040403020104,dC 0x3020104,dC 0x6040203020104,dC 0x4010407,dC 0x503010201040a,dC 0x5040206040203020104,dC 0x6050203020106,dC 0x605020302010b,dC 0x5040203020104,dC 0x5020404030223,dC 0x6050303020105,dC 0x3020105040404,dC 0x6010403020204,dC 0x3010323,dC 0x5040206010403020204,dC 0x601040302020b,dC 0x6010403020206,dC 0x6010405040403020204,dC 0x3020204,dC 0x4020203020204,dC 0x4020206040403020204,dC 0x5020203020204,dC 0x5020203020205,dC 0x3020205020404,dC 0x6040203020205020404,dC 0x5020403020205,dC 0x2e,dC 0x3020205020405,dC 0x4010403,dC 0x3010423,dC 0x6040403020204,dC 0x5040203020204,dC 0x6010405040203,dC 0x3020206010405040204,dC 0x6020105040202,dC 0x601020302020b,dC 0x6050103020205,dC 0x3020205040404,dC 0x6010203020304,dC 0x6040402010301,dC 0x5030402010308,dC 0x5040206010203020304,dC 0x5040202010301,dC 0x6010203020306,dC 0x601020302030b,dC 0x4030213,dC 0x2010305040401,dC 0x6010205040403020304,dC 0x3020304,dC 0x6040203020304,dC 0x6040205040403020304,dC 0x6050203020306,dC 0x5040203020304,dC 0x302030b,dC 0x6050303020305,dC 0x3020305040404,dC 0x6010203020404,dC 0x5030402010408,dC 0x5040206010203020404,dC 0x601020302040b,dC 0x501020302040a,dC 0x6010205040403020404,dC 0x3020404,dC 0x6040203020404,dC 0x4020206040203020404,dC 0x4020203020404,dC 0x5020203020404,dC 0x5020403020404,dC 0x5020403020405,dC 0x6040203020405020404,dC 0x5040203020404,dC 0x6020405040202,dC 0x5020104030223,dC 0x6050303020405,dC 0x6010403020405040204,dC 0x3020405040404,dC 0x4020204,dC 0x4010102,dC 0x6020204010102,dC 0x6020304010102,dC 0x6010104020204,dC 0x6030204010102,dC 0x401020f,dC 0x6050304010102,dC 0x6010206010104020204,dC 0x6050104010104010202,dC 0x6050102010102010205,dC 0x6010105020206,dC 0x6010204020204,dC 0x6010406010304020204,dC 0x6010304020204,dC 0x30,dC 0x4020206040205020404,dC 0x4020205020404,dC 0x6030104020204,dC 0x4020204020102,dC 0x6030206030104020204,dC 0x3020203020105,dC 0x6030204020204,dC 0x6030304020204,dC 0x3020303020405,dC 0x6030406030304020204,dC 0x6030404020204,dC 0x4020206020205030104,dC 0x4020205030104,dC 0x6040204020205030104,dC 0x4020205030404,dC 0x6050204020207,dC 0x6040305020402,dC 0x6050404020207,dC 0x6050104020204,dC 0x6050304020204,dC 0x6010204020304,dC 0x4020304,dC 0x6030205020102,dC 0x6030204020307,dC 0x5040203020323,dC 0x5030104020304,dC 0x6020204020305030104,dC 0x5030404020304,dC 0x6010205020104,dC 0x6050104010301,dC 0x5040103010308,dC 0x5020104,dC 0x5010406,dC 0x6040205020104,dC 0x6040205020107,dC 0x4030206040205020104,dC 0x4030205020104,dC 0x5030304020123,dC 0x5020104030304,dC 0x5020204,dC 0x5020205,dC 0x6010405020205,dC 0x6010205020304,dC 0x6010205020305,dC 0x5020304,dC 0x6010205020405,dC 0x6050304010201,dC 0x5040303010208,dC 0x5020404,dC 0x6040205020404,dC 0x7030106040205020404,dC 0x7030406040205020404,dC 0x4030205020404,dC 0x6030305020405,dC 0x5030304020423,dC 0x5020404030304,dC 0x4030204,dC 0x6020204010407,dC 0x6010404030204,dC 0x6010204020407,dC 0x5010403020208,dC 0x6020404030204,dC 0x6010204030304,dC 0x6020204030304,dC 0x7050106020204030304,dC 0x4030304,dC 0x6010205030104,dC 0x6050102010401,dC 0x5040102010408,dC 0x6050104020301,dC 0x5030104,dC 0x6020205030104,dC 0x7040406020205030104,dC 0x6050104020302,dC 0x6040205030104,dC 0x6050103020405,dC 0x5030204,dC 0x5030205,dC 0x6050202010201,dC 0x5040202010208,dC 0x6010405030204,dC 0x6010405030205,dC 0x6020405030204,dC 0x6020405030205,dC 0x6010205030304,dC 0x6050402010401,dC 0x5040402010408,dC 0x6010205030305,dC 0x6020205030304,dC 0x5030304,dC 0x6050302010201,dC 0x5040302010208,dC 0x6010205030404,dC 0x6050304020201,dC 0x6040405010207,dC 0x6020205030404,dC 0x6050304020202,dC 0x5030404,dC 0x6040205030404,dC 0x6050303020205,dC 0x5040204,dC 0x6010405040204,dC 0x6020405040204,dC 0x5040404]
def ptopP : List (Nat × Nat) := [(2,3),(1,3),(3,6),(16,17),(24,25),(36,37),(3,5),(8,10),(20,22),(36,38),(18,22),(8,12),(33,37),(18,26),(2,10),(33,41),(1,17),(18,50),(33,49),(3,9),(4,12),(40,41),(24,28),(48,52),(36,52),(5,21),(9,41),(5,37),(1,21),(36,44),(12,40),(40,44),(20,52),(20,21),(1,37),(40,42),(1,49),(18,19),(5,17),(17,33),(20,28),(24,26),(48,49),(48,50),(6,10),(0,12),(9,25),(3,34),(9,10),(6,7),(9,11),(9,13),(6,22),(33,35),(34,50),(5,7),(10,24),(4,22),(6,38),(34,35),(34,38),(1,7),(0,17),(5,13),(9,12),(8,44),(32,37),(32,38),(8,13),(16,22),(0,3),(17,48),(25,56),(26,56),(4,37),(4,38),(16,50),(5,12),(4,7),(16,19),(34,42),(2,35),(6,14),(3,18),(41,56),(2,22),(0,10),(2,19),(8,28)]
noncomputable def ptopK : List CutV := ptopC.map (mkCut ptopZ)
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
def ptopD4 : List StD := []
theorem ptopI4 : LevelN ptopR ptopT 4 ptopD4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def ptopD5 : List StD := [
([w1,w0,w808,w38,w122,w5],dL 0x0,dS 0x1028110f0a2d05261b0b0e0d09060804,pH 0x111111111111111 0 16),
([w809,w1,w0,w38,w122,w5],dL 0x0,dS 0x12280f180c1a0a1b0e0b050206090804,pH 0x111111111111111 0 16),
([w123,w1,w2,w810,w4,w5],dL 0x0,dS 0x13100e2f3611333c26413120350201340b,pH 0x111111111111111 0 17),
([w123,w1,w2,w3,w811,w5],dL 0x0,dS 0x1311100e333c264131180f440201340b,pH 0x111111111111111 0 16)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI5 : LevelN ptopR ptopT 5 ptopD5 := levelStep ptopB ptopW ptopQ ptopI4 (chunks 64 ptopD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
([w1,w2,w812,w0,w38,w122,w5],dL 0x6005f05e05d,dS 0x280d0e2d150c0a0126090b0408,pH 0x311411311111111112111 4 13),
([w1,w2,w0,w38,w122,w813,w5],dL 0x63062061,dS 0x1c0e281a29180b2d170a0526111b150c09060804,pH 0x211111111111111111111 3 20),
([w814,w1,w2,w0,w38,w122,w5],dL 0x0,dS 0x280f2e0c0a0526150b0e1a1c1b1109060804,pH 0x111111111111111111111 0 18),
([w815,w1,w2,w0,w38,w122,w5],dL 0x0,dS 0x282e150b1a0a260e0c2f05061b1c11080904,pH 0x111111111111111111111 0 18),
([w816,w123,w1,w2,w3,w4,w5],dL 0x0,dS 0x3519311c1f0903120d0c13363c110b100e0201,pH 0x111111111111111111111 0 19),
([w123,w1,w2,w3,w4,w5,w817],dL 0x0,dS 0x1c0e402f3833322641310b1f1820240a160611350d1b010212,pH 0x111111111111111111111 0 25),
([w818,w123,w1,w2,w3,w4,w5],dL 0x0,dS 0x353b1931421820240a120b1c1102010d130e361032,pH 0x111111111111111111111 0 21),
([w123,w1,w2,w819,w3,w4,w5],dL 0x143142,dS 0x1b1c1133264131420d0e354443123402010b,pH 0x211121111111111111111 2 18),
([w820,w152,w1,w2,w0,w3,w4],dL 0x0,dS 0x4a310c1f040b1c49191138321b1e0e120201,pH 0x111111111111111111111 0 18),
([w152,w1,w2,w0,w821,w3,w4],dL 0x0,dS 0x11130c4a36263c3121121f090a2206011c3402100e0b,pH 0x111111111111111111111 0 22),
([w822,w152,w1,w2,w0,w3,w4],dL 0x0,dS 0xd4a3831421c22060b12190c110201130e321036,pH 0x111111111111111111111 0 20),
([w152,w1,w2,w823,w0,w3,w4],dL 0x1f143,dS 0x110c4a3331421c154c494b0e0b1b020112,pH 0x111211111111111111111 2 17),
([w153,w1,w2,w0,w237,w4,w5],dL 0x202,dS 0x13111e292a100e02210a0f15060b08010c05,pH 0x111111111111111111111 1 18),
([w153,w99,w2,w0,w9,w4,w5],dL 0x0,dS 0x18351605124e1b100119060b110c020a,pH 0x111111111111111111111 0 16),
([w153,w1,w2,w0,w8,w4,w5],dL 0x20a,dS 0x292a020f10142115061b0c0801120b0e05,pH 0x111111111111111111111 1 17),
([w99,w2,w0,w9,w8,w4,w5],dL 0x0,dS 0x21024e08181b1612111035010c14060b05,pH 0x111111111111111111111 0 17),
([w824,w1,w2,w0,w133,w3,w5],dL 0x0,dS 0xe3d0a09052f121b0f19110234060b0804,pH 0x111111111111111111111 0 17)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := levelStep ptopB ptopW ptopQ ptopI5 (chunks 64 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD7p0 : List StD := [
([w118,w2,w0,w31,w4,w5],dL 0x3803302c037036035034,dS 0xe1c1219010a05111506080904,pH 0x433743111122266 7 13),
([w118,w2,w0,w3,w38,w5],dL 0x4504404603e036035034,dS 0x1c12190e0a05011506080904,pH 0x433743111122266 7 12),
([w1,w2,w0,w38,w122,w5],dL 0x4804305c05b,dS 0x282f0c150b0e110a05041b1c1a08060926,pH 0x433413222211111 4 17),
([w47,w26,w1,w2,w0,w20,w3,w5],dL 0xd50cd0d20d4,dS 0x150c020705221b3d3c252f1a01131912100b090411,pH 0x2212112111211111311111111111 4 21),
([w1,w2,w107,w0,w20,w3,w4,w5],dL 0xe30e200300f0e40e10cf0e00de,dS 0x13102115110f022632040b120e01,pH 0x3531311312311462221223134122 9 14),
([w1,w2,w6,w0,w133,w3,w4,w5],dL 0xe50e10de,dS 0xb3638083c32043121150c26191b110e100201,pH 0x1111111111111111111111111111 3 19),
([w47,w26,w17,w1,w2,w0,w3,w5],dL 0xd4,dS 0x3e020c091b3d252f011315220b3c1a210e1219100411,pH 0x1111111111111111111111111111 1 22),
([w17,w1,w2,w107,w0,w3,w4,w5],dL 0xf90e10e20de0cf,dS 0x1226040208380e0b19211501,pH 0x1311131215121111111122121411 5 12),
([w6,w0,w337,w4,w13,w5],dL 0x10c10b10910810a107,dS 0x191b0e1c1214011537350605,pH 0x142313514311111 6 12),
([w123,w1,w2,w3,w4,w5],dL 0x99141096091,dS 0x10363c310d120b1c1a020119403811320e,pH 0x433222111114321 4 17),
([w1,w2,w32,w0,w3,w4,w87],dL 0x14c14b14a14914d141096091,dS 0x102c2a2b051c1a114038320102120e0408,pH 0x433543548122227111161 8 17),
([w47,w26,w1,w2,w32,w0,w3,w5],dL 0x150115099,dS 0x100c220212081340381a0119360e0411,pH 0x2212112111211111222111111111 3 16),
([w1,w2,w32,w0,w3,w4,w322,w5],dL 0x14915911515814d157,dS 0x12130e0b2c082b052a383240010204,pH 0x1133114313411111111111111111 6 15),
([w1,w2,w0,w782,w3,w4,w5],dL 0x15d15c099141096091,dS 0x152a051e1c1201021911180a060e0c0408,pH 0x433543111122222111111 6 17),
([w783,w1,w2,w6,w0,w3,w4,w5],dL 0x15f153,dS 0x21190c343538083204310b36151012130e261c1a02010f,pH 0x1111111111111111111111111211 2 23),
([w1,w2,w32,w107,w0,w3,w4,w5],dL 0x930e307d1600e215314d,dS 0x110b133c17363826320240370e10120108,pH 0x1212131112251121111111111111 7 17),
([w1,w2,w0,w784,w3,w4,w5],dL 0x99141151096091,dS 0x342a0513111001020e0a060d0b0408,pH 0x544154333322221111111 5 15),
([w98,w154,w1,w2,w0,w4,w5],dL 0x16816716609915b091141,dS 0xd19110b0c0a10130201060e,pH 0x433111222111555147165 7 12),
([w98,w319,w1,w2,w0,w3,w5],dL 0x16d16c16b16a14115b096099,dS 0x190b0d0a110201060e1013,pH 0x433222111111111187615 8 11),
([w184,w40,w1,w2,w0,w3,w4],dL 0x188187186189141096091185,dS 0x1b110201190e0906151c12,pH 0x454333222258276111111 8 11),
([w47,w26,w40,w1,w2,w0,w3,w5],dL 0x9918b11b,dS 0x191213021a1509010e2211,pH 0x1111111311113113111113313113 3 11),
([w323,w40,w1,w2,w0,w3,w5],dL 0x18b19119018f185141096099,dS 0x2f35121c0e02090106111519,pH 0x343222111187161111115 8 12),
([w1,w2,w6,w0,w785,w3,w4,w5],dL 0x19600118518f195143,dS 0x1e0c113808263206311521190237120e01,pH 0x1411111111111112123111111111 6 17),
([w40,w1,w2,w107,w0,w3,w4,w5],dL 0xa1003197185,dS 0x280c3710310b0201122113190e153832,pH 0x1111111113111111111111111111 4 16),
([w47,w1,w2,w0,w3,w87],dL 0x19f19e19d1a014103e096091,dS 0x101219150e2c2a2b0522132f1101021a0904,pH 0x458222111133376 8 18),
([w79,w2,w0,w3,w4,w87],dL 0x1a41ac1ae1ad141096091,dS 0x1006111a152c2a2b0522120e09040201,pH 0x433547222611111 7 16),
([w1,w2,w320,w0,w3,w4,w87],dL 0x1b71b61b514d141096158091,dS 0x10112c2b051c1a290e22010212090408,pH 0x544254258133337111161 8 16),
([w184,w321,w1,w2,w0,w3,w4],dL 0x1bd1bc1bb14109609111b,dS 0x1b110201190e0906151c12,pH 0x114133122217265111111 7 11),
([w152,w1,w2,w0,w3,w4],dL 0x99141096091,dS 0x15383231131c0b120c0201191036113c0e,pH 0x343222111143121 4 17),
([w786,w1,w2,w0,w3,w5],dL 0x1a003e0b7096091,dS 0x121b0c0a2a0605131102012f0b0d0904,pH 0x533222111144321 5 16),
([w99,w1,w2,w0,w3,w237,w4,w5],dL 0x201,dS 0x15351812210b0e1011190a010c0206,pH 0x1111111111111111111111111111 1 15),
([w1,w2,w0,w3,w237,w4,w5],dL 0x69205204203201,dS 0x2119150a2a35021812111b060108100e340b05,pH 0x435111222211212112111 5 19),
([w153,w99,w1,w2,w0,w3,w4,w5],dL 0x201,dS 0x2f3533150e21120611190b011b0c02,pH 0x1111111111111111111111111111 1 15),
([w153,w1,w2,w0,w3,w4,w5],dL 0x69206208209207201,dS 0x2f18350803110e151902120b010c051b,pH 0x311221341211111461511 6 16),
([w99,w2,w0,w3,w9,w4,w5],dL 0x1fe01f20b201,dS 0x2f1835311b121602211119060a01100b050c,pH 0x111114222213112111122 4 18),
([w74,w99,w2,w0,w3,w4,w5],dL 0x20c20101f1fe,dS 0x1b3526101211160e0b022119150c010605,pH 0x233443223411341111111 4 17),
([w99,w1,w2,w0,w3,w8,w4,w5],dL 0x2061fd201,dS 0x1b0f1c08331835211211190e0b0c0106,pH 0x1111121111221221111121111121 3 16),
([w1,w2,w787,w6,w0,w3,w4,w5],dL 0x21007d,dS 0x121136383c3216312115190b261b0c0e100201,pH 0x1111111111111111111111111111 2 19),
([w1,w2,w788,w6,w0,w3,w4,w5],dL 0xd8,dS 0x210f1338083c320631150b362612190c1c370e020110,pH 0x1111111111111111111111111111 1 22),
([w1,w2,w107,w0,w789,w3,w4,w5],dL 0x7d0e2165234,dS 0x280f151913383c32120b0e0237362621100108,pH 0x2111111111111311111111111111 4 19),
([w790,w1,w2,w107,w0,w3,w4,w5],dL 0x32340e2,dS 0x280b373c100c362608153832211913120e0102,pH 0x1122111121111111111111111311 3 19),
([w22,w1,w2,w0,w133,w3,w4,w5],dL 0xde195,dS 0x100f3d47080204122634110e010b,pH 0x1112211111222221111122222111 2 14),
([w1,w2,w344,w75,w0,w3,w4,w5],dL 0xe12bf,dS 0x716053226121b010c1137100e380b04,pH 0x1111111111111111111221111111 2 16),
([w1,w2,w344,w0,w3,w4,w5],dL 0x2ce2cd07d2bf0e1,dS 0x3816053226121b370b0102110e10080c04,pH 0x223234235423111111111 5 17),
([w17,w1,w2,w225,w3,w4,w5],dL 0x3000082ff305303304,dS 0x361302370b12100819060d0c010e,pH 0x131553413641321222221 6 14),
([w1,w2,w0,w791,w3,w4,w5],dL 0x2f933b30033933a,dS 0x3b211324220212090e0d0110080c06,pH 0x411421111122122222211 5 15),
([w1,w2,w0,w225,w792,w3,w4,w5],dL 0x7d23434c0cf,dS 0x12153510130d36220c0919010e06,pH 0x2211111131211222313112112111 4 14),
([w793,w1,w2,w0,w3,w4,w15,w5],dL 0x3dd3db,dS 0x3b1b13350f3d2b015426121a220a090b110e0d2c0410,pH 0x1111111111111111111111211111 2 22),
([w1,w2,w0,w3,w4,w15,w794,w5],dL 0x3f33f2,dS 0x3b19103d2a2b015405261c132c08220e0d150b021104,pH 0x1111111111111111111111111111 2 22),
([w795,w1,w0,w3,w4,w5],dL 0x40035379091,dS 0x10121a110e2b3105220a08041c15090226,pH 0x222422111133331 4 17),
([w1,w2,w131,w0,w3,w4,w87],dL 0x40c40b40d3391b6091379,dS 0x100f2c2b05121a292201021c110e090408,pH 0x111511517233333222261 7 17),
([w1,w2,w796,w0,w3,w4,w5],dL 0x404111b3091410,dS 0x10150e2c2a05261c12110f1622020409,pH 0x511111511233333222221 5 16),
([w86,w1,w2,w0,w3,w129,w5],dL 0x41a07d41e41c37903e,dS 0x1803081211350e0b04191b170110,pH 0x621363412341235412316 6 14),
([w233,w1,w2,w0,w3,w42,w4,w5],dL 0x42e42d42c42b,dS 0x1a0e0b2d1b09372917043c150c3b0208,pH 0x1311111111212221111111211111 4 16),
([w45,w233,w1,w2,w0,w3,w4,w5],dL 0x43042f,dS 0x2e0c3b150b37043c110e1c1b1a0209,pH 0x1111112122111111211111111211 2 15),
([w797,w1,w2,w3,w4,w5],dL 0xb10350913d6040,dS 0x10221c0f0e02030812,pH 0x122444333312243 5 9),
([w234,w1,w2,w0,w3,w8,w4,w5],dL 0x458456457455454,dS 0x1002143311190e2a1b050f040b08120c06,pH 0x1212112141211111211111111111 5 17),
([w27,w234,w1,w2,w0,w3,w4,w5],dL 0x45941b45a,dS 0x10200c570811190e02042606120b,pH 0x1333312222332212132232212112 3 14),
([w345,w1,w2,w108,w0,w3,w4,w5],dL 0x46c1fe,dS 0x1b341c10120c0b010421350e190215,pH 0x1112221112111211111111112211 2 15),
([w345,w1,w2,w0,w3,w4,w5],dL 0x14320146c1fe11b,dS 0x10030201122135190e150c0b04,pH 0x144333114322222154322 5 13),
([w1,w798,w2,w108,w0,w3,w4,w5],dL 0x46d,dS 0x181524122b05221c210235190e0b01100c3604,pH 0x1111111111111111111111111111 1 19),
([w151,w50,w1,w63,w0,w3,w4,w5],dL 0x49718f,dS 0x3a11150930040b2a130a0c1012363b010f0d,pH 0x1111112111111122221122111122 2 18),
([w52,w1,w235,w63,w0,w3,w4,w5],dL 0x49449d09649f15749e,dS 0x101215110b093c0535020c53323b36010f04,pH 0x2121211244121111111111111151 6 18),
([w52,w236,w1,w63,w0,w3,w4,w5],dL 0x4a14a0,dS 0x100e111509460c3c0b2a350a0512133b360f01,pH 0x1112221112111211221111111111 2 19)]
set_option maxHeartbeats 0 in
noncomputable def ptopD7p1 : List StD := [
([w151,w1,w2,w235,w0,w3,w4,w5],dL 0x1214940964a315749f4a4,dS 0xc051b130f3b53320e3601122a04,pH 0x2121211215121141211111112211 7 14),
([w151,w236,w1,w2,w0,w3,w4,w5],dL 0x4924a718f4a64a8,dS 0x30340b3b130f0110120c0936040e,pH 0x2121211211121311211111111212 5 14),
([w1,w2,w799,w63,w0,w3,w4,w5],dL 0x1ea494,dS 0x19153c0522260b0c011221113510360e04,pH 0x1111111111111111111221111111 2 17),
([w1,w2,w800,w63,w0,w3,w4,w5],dL 0x1f1492,dS 0x3c05221512102111370c0b010e3604,pH 0x1111111111111111111221111111 2 15),
([w1,w2,w336,w0,w3,w4,w801,w5],dL 0x4c14b2158,dS 0xf352a080730053b1332100e0d0c3601120204,pH 0x1111111111121111111111111111 3 19),
([w1,w2,w802,w0,w3,w4,w5],dL 0x3035524d80e0099,dS 0x122a3836320213100d190e010c08,pH 0x331314114522222311122 5 14),
([w1,w2,w0,w133,w803,w3,w4,w5],dL 0x302578234,dS 0xf12193d0a081b0c021109260b0e1006,pH 0x2111111113111111111111111111 3 16),
([w804,w1,w2,w0,w133,w3,w4,w5],dL 0x195302234,dS 0x3d06120109191b100e021134080b,pH 0x1113211111211222222113113111 3 14),
([w805,w2,w0,w3,w4,w5],dL 0xaa04003e108094096,dS 0x101235370e2c311c15090506012a,pH 0x433543111126226 6 14),
([w148,w2,w0,w3,w4,w87],dL 0x5aa5ac5ab1a40961a1,dS 0x10120635152c2b0522370e04090801,pH 0x433543222611111 6 15),
([w806,w1,w2,w3,w4,w5],dL 0x103102141040094,dS 0xe091207011b1016,pH 0x233111111124311 5 8),
([w1,w2,w0,w3,w807,w4,w5],dL 0x5c85c701f,dS 0x1f0a05332f1e06121b11090f010b340804,pH 0x111111113111211111111 3 17)]
noncomputable def ptopD7 : List StD := ptopD7p0 ++ ptopD7p1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*64)).take 64) = true := by decide +kernel
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopW ptopQ ptopI6 (chunks 64 ptopD7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD8p0 : List StD := [
([w1,w2,w68,w3,w4,w5,w29],dL 0xa005009008007006,dS 0x12100d0a06050f09080e0c0b040703,pH 0x565444333322222111111 6 15),
([w26,w1,w2,w68,w3,w4,w5],dL 0xa00e00d00c00b005,dS 0x12090413070a03060e0d0b10,pH 0x155444333322222115432 6 12),
([w89,w1,w2,w3,w4,w5,w29],dL 0x14011013012007006,dS 0x12100a080d0f050e0b020c010906,pH 0x565444222211111333321 6 14),
([w26,w89,w1,w2,w3,w4,w5],dL 0x1401600c00b015011,dS 0x1209040c13020a01060e100b0d,pH 0x155444333322222115432 6 13),
([w1,w2,w0,w31,w4,w49,w5],dL 0x1f01c01e01901d01b01a,dS 0x1b1a19100f18170a16050e0b04090614,pH 0x346534343622222111111 7 16),
([w58,w1,w2,w0,w31,w4,w5],dL 0x2301d02202102001c01f,dS 0x121d140c10080415061c0a,pH 0x155222444433333222243 7 11),
([w1,w2,w69,w0,w31,w4,w5],dL 0x2601c02502401f,dS 0x111f1c0d0905191e0a040614,pH 0x155444144433333222222 5 12),
([w1,w2,w0,w31,w4,w5,w117],dL 0x2302c01c02b02a02901d028027,dS 0x21100f1f18200a050e110d09040614,pH 0x734365433722222111111 9 15),
([w106,w1,w2,w0,w31,w4,w5],dL 0x2f02e02d01c023,dS 0x130e2310141c0b04081a150922,pH 0x155222444433333122243 5 13),
([w76,w1,w2,w0,w31,w4,w5],dL 0x3203103001d01f,dS 0x112314120d080416131024,pH 0x155222444433333122243 5 11),
([w1,w2,w0,w31,w4,w5,w29],dL 0x1d01c03601900700602c,dS 0x110c21131905120e1509040614,pH 0x411115114533333222222 7 13),
([w26,w1,w2,w0,w31,w4,w5],dL 0x3900c00b029023,dS 0x2512111a150905141b130e080a0406,pH 0x221215444433333212243 5 15),
([w1,w2,w0,w3,w38,w49,w5],dL 0x4003c03f03e01b03d01a,dS 0x1b1a10180c27170a160504190b0f06080926,pH 0x241524222633333111111 7 18),
([w58,w1,w2,w0,w3,w38,w5],dL 0x3d04204102102003c040,dS 0x12101d05260c04081c150a06,pH 0x155222444433333232243 7 12),
([w1,w2,w0,w3,w38,w5,w29],dL 0x3d03c04804604700700603e,dS 0x1b280c211219130e0a05040906150826,pH 0x521141161413133222222 8 16),
([w26,w1,w2,w0,w3,w38,w5],dL 0x4903e00c00b042,dS 0x21121a0e05261b11150a040608,pH 0x414145333322222124432 5 13),
([w1,w2,w576,w0,w3,w38,w5],dL 0x3d04d04c04e04b03c,dS 0x1311270b0a050406222129080926,pH 0x355111111144444222222 6 14),
([w1,w2,w0,w3,w38,w577,w5],dL 0x4003c04f03e01b03d01a,dS 0x1b1a10180c27170a160504190b0f06080926,pH 0x246524222633333111111 7 18),
([w578,w1,w2,w0,w3,w38,w5],dL 0x3d05002102003c040,dS 0x12101d05260c04081c150a06,pH 0x155222444433333222243 6 12),
([w579,w1,w2,w0,w3,w38,w5],dL 0x3c05305205103d04e,dS 0x191a1d05260b0812060e042a,pH 0x155222444433333222243 6 12),
([w1,w2,w69,w0,w3,w38,w5],dL 0x5402503c024040,dS 0x111f1c0d090504191e08060a26,pH 0x155333133344444222222 5 13),
([w1,w2,w0,w3,w38,w5,w117],dL 0x4e04603c05504803d028027,dS 0x11211c100f1f18200a05040e0d08060926,pH 0x634355433622222111111 8 17),
([w106,w1,w2,w0,w3,w38,w5],dL 0x4005602e02d03c04e,dS 0x130e231b05261c0b040822151a09,pH 0x155222444433333122243 6 14),
([w76,w1,w2,w0,w3,w38,w5],dL 0x5703103003d040,dS 0x112326120d080413102416,pH 0x155222444433333122243 5 11),
([w1,w2,w0,w3,w580,w38,w5],dL 0x3c03d04305a059048058,dS 0x2812131c111a18152b05041b0e2c08060926,pH 0x225444252433333111111 7 18),
([w1,w2,w0,w3,w38,w5,w581],dL 0x3d03c04804606400700603e,dS 0x1b280c211219130e0a05040906150826,pH 0x561141161413133222222 8 16),
([w582,w1,w2,w0,w3,w38,w5],dL 0x67066065046040,dS 0x251b19130e052612111509060408,pH 0x221215444433333212243 5 14),
([w583,w1,w2,w0,w3,w38,w5],dL 0x6800c00b03e04e,dS 0x251121120e05261b13150a040806,pH 0x212125444433333122243 5 14),
([w217,w1,w2,w0,w3,w4,w49],dL 0x7307006f07201b01a071,dS 0x91b19180a061a0b0e021001,pH 0x614561333322222154632 7 12),
([w58,w217,w1,w2,w0,w3,w4],dL 0x7106f075021020074070,dS 0xe0b09080401120c1015060a1c,pH 0x511441331322122111111 7 13),
([w584,w1,w2,w0,w3,w4,w5],dL 0x7907801e07601b01a07a,dS 0x1a190e0b270a060210010f0904,pH 0x155444333322222626232 7 13),
([w585,w1,w2,w0,w3,w4,w5],dL 0x7c07d02207b02102007e,dS 0x1d310e10150a060804,pH 0x655444333322222625232 7 9),
([w1,w2,w0,w586,w3,w4,w5],dL 0x8101f02608007b025024,dS 0xe1f0531190b0c0a1e08040906,pH 0x445175333122222111111 7 13),
([w587,w1,w2,w0,w3,w4,w5],dL 0x7802b076028027042,dS 0x131f1006020911010e,pH 0x155444333322222266232 6 9),
([w588,w1,w2,w0,w3,w4,w5],dL 0x2f08507b02e02d086,dS 0x2310311c04060e15092208,pH 0x566444333322222256232 6 11),
([w589,w1,w2,w0,w3,w4,w5],dL 0x78032076031030088,dS 0x211c230b0931120e0816102404,pH 0x155444333322222266232 6 13),
([w590,w1,w2,w0,w3,w4,w5],dL 0x8d00300f08c03606f00707d006,dS 0x2112150a1011060201090f04,pH 0x252925333311111112231 9 12),
([w118,w28,w2,w0,w3,w4,w5],dL 0x8c08f08e006035,dS 0x1c12190102050626110e1532080409,pH 0x433543111122221221112 5 15),
([w109,w1,w6,w0,w3,w4,w5],dL 0x99098097035092096093095091,dS 0x1311100f0d02330e340b2c08,pH 0x877333111122225444222 9 12),
([w1,w90,w6,w0,w3,w4,w5],dL 0x990a30a00350960a20a109f091,dS 0x1311100e3304010d0b0a021509,pH 0x844333111155522222212 9 13),
([w1,w6,w0,w3,w15,w13,w5],dL 0xac0ad0940ab0aa044,dS 0x1b121a0e2c3901041c02370915352a,pH 0x412331641312111221222 6 15),
([w86,w1,w6,w0,w3,w4,w5],dL 0x4e0b00af0960ae091,dS 0x1c111a3a04363302120e150a0838,pH 0x454645111122221323322 6 14),
([w47,w1,w2,w0,w3,w15,w5],dL 0xb70400b603e0940b50b4091,dS 0x3b10121c0c0e2c3a2a0901132f1115191a02,pH 0x161716313321222525522 8 18),
([w218,w1,w6,w0,w3,w4,w5],dL 0xbb0350990ba09609e0b9091,dS 0x1c1219063302110e15380908,pH 0x335385111122221244422 8 12),
([w1,w146,w6,w0,w3,w4,w5],dL 0xc10350990c009609d0bf091,dS 0x10121c11152c33380401190e0a0224,pH 0x335385111124442222212 8 15),
([w110,w2,w6,w0,w3,w4,w5],dL 0x990c70960930a009f0c6091,dS 0x1311100f05023c26320b0d1604010e,pH 0x722552111144223111111 8 15),
([w47,w1,w2,w0,w20,w3,w4,w5],dL 0xd303e0d10ce0cd0b40b70ca0d20d00cb0cc0cf,dS 0x191b0911103d3801120b040e,pH 0x1412222223333731112261112766 13 12),
([w147,w1,w2,w6,w0,w3,w4,w5],dL 0xdc0d90d80da0d70dd09301f0db02107d094,dS 0x12211517320c101c0f0126,pH 0x2425241111111181111332123118 12 11),
([w1,w2,w6,w0,w20,w3,w4,w5,w29],dL 0x9d0a10120060df0e40de0070cf,dS 0x111310211937020932150b26120e01,pH 0x111441341355152113161222212111116122 9 15),
([w26,w1,w2,w6,w0,w20,w3,w4,w5],dL 0x1500b0e70cf00c0e60d40d2,dS 0x1211100b15020926321b13383c0e01,pH 0x531322316432272222121315214211333221 8 15),
([w83,w2,w6,w0,w3,w4,w5],dL 0x990e90960a10920950e8091,dS 0x131110383c26040d0b2215060e01,pH 0x722552111144223111333 8 14),
([w1,w2,w6,w0,w3,w4,w183,w5],dL 0x1f0d90ee0ac0eb0a107d0ed0ec01b094,dS 0x1b193c32211517261001,pH 0x5413336223111112222271111727 11 10),
([w47,w17,w1,w2,w0,w3,w4,w5],dL 0xf30f10f00b40f40ee0b70f20960cf,dS 0x1b09022a1c150119120e0b04,pH 0x1314142222111122221221211218 10 12),
([w17,w1,w2,w6,w0,w3,w4,w5,w29],dL 0x80f70060f80f60de0cf,dS 0x1108040231380b12132119150e01,pH 0x111331641411211112111331111221111111 7 14),
([w26,w17,w1,w2,w6,w0,w3,w4,w5],dL 0xd0fc00b0cf0fb0d40fa,dS 0x120e082601040231381b130b1a15,pH 0x411116122212221114412222441211111112 7 14),
([w79,w2,w6,w0,w3,w4,w5],dL 0x10101f1000ff0aa0fe091,dS 0x131b1211153f0636023c2632041a2138160e01,pH 0x522652111142243111111 7 19),
([w47,w1,w2,w0,w3,w13,w5],dL 0x401040cf03e0941050cb096,dS 0x10121c15022b3f190522010f373504,pH 0x131813212241372525527 8 15),
([w148,w6,w0,w3,w4,w13,w5],dL 0x10e0ac10d10a1060aa096,dS 0x191b1c123115063c0226010437350e093216,pH 0x154313615312111222222 7 18),
([w79,w6,w0,w3,w4,w13,w5],dL 0xac1010aa0441000ff10f094,dS 0xe12383c321c023735151610090106,pH 0x143212814211111163155 8 15),
([w1,w32,w6,w0,w3,w4,w13,w5],dL 0x116111115114112044110113096,dS 0x3721150c093c31262a384002321c350e1001,pH 0x1685552125131512125413333383 9 18),
([w40,w1,w6,w0,w3,w4,w13,w5],dL 0x11c11d11311b11704411a119096118,dS 0x35213126090c1b10013212370e0215,pH 0x2493331111264385665691111586 10 15),
([w47,w1,w6,w0,w3,w13,w5],dL 0xad0ac0d80441040a911e07d096,dS 0x1c12152c093c32040135372a0219100f26,pH 0x131813151121221212715 9 17),
([w1,w591,w6,w0,w3,w4,w5],dL 0x204e0af11f0350d9,dS 0xe1c111536383c3212190a0f0210010826,pH 0x433543213221326111111 6 17),
([w52,w1,w32,w6,w0,w3,w4,w5],dL 0x961211161151141220da111035,dS 0x1b21150c093c363308191c400e3238011a2602,pH 0x5443341111334111112282222228 9 19)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p1 : List StD := [
([w52,w40,w1,w6,w0,w3,w4,w5],dL 0x960da12311c11b11a12512411d035,dS 0x1b2136330a0c381912110e150102,pH 0x5443331111111123331922222222 10 14),
([w219,w2,w6,w0,w3,w4,w5],dL 0x12809609909e0c20bf127091,dS 0x1c1215052202383c2632111904010e,pH 0x522582111144243111111 8 15),
([w220,w2,w6,w0,w3,w4,w5],dL 0x12d09609909d0b80b912c091,dS 0x10121c11152b06023826320419160e01,pH 0x522582111144243311133 8 16),
([w1,w2,w6,w0,w3,w4,w97,w5],dL 0x930a104e13213109d13307d13012f007094,dS 0x12190c3c130e320d2126151001,pH 0x2614447564111412222231333323 12 13),
([w1,w2,w6,w0,w3,w4,w592,w5],dL 0x1f13d11413c13b1150ac13e0a113913a07d099,dS 0x36330e380b26311b21150c320201,pH 0x2156215115121113313341114434 13 14),
([w1,w2,w32,w134,w3,w4,w5],dL 0x9914514013f1440350a1096091,dS 0x1311100f0d3308383c2604320e0b010c18340241,pH 0x855111333122227111116 9 20),
([w1,w2,w32,w0,w3,w4,w59,w5],dL 0x8814911a146110116115114148096147091,dS 0x13191b150c2c082b16051c400e3832011a02042a,pH 0x1514142122212213333391111181 12 20),
([w47,w1,w2,w32,w0,w3,w4,w5],dL 0x3e1491210cc11609109611514e14f1140990b7,dS 0x191740021c1b38010c120e2a04,pH 0x343111111855555232112282115b 13 13),
([w1,w2,w32,w119,w6,w0,w3,w4,w5],dL 0x15309e152093091149151,dS 0x19150c120b110826043121134036383c32350e100201,pH 0x221111333312217111151111111111111111 7 22),
([w1,w2,w32,w119,w0,w3,w4,w5],dL 0x9e09311614d156096155154149151091,dS 0x212f182a0513101a4036383c3201020408,pH 0x3372221332222125555554444441 11 17),
([w98,w1,w2,w32,w6,w0,w3,w4,w5],dL 0x9d15b14909315309115a,dS 0x150c0b2416311221403538321102011913100e363c,pH 0x331111222211116111111111111111115111 7 21),
([w221,w1,w2,w32,w0,w3,w4,w5],dL 0x14909915e09615c091,dS 0xe1c1a401b09122204212416191e18,pH 0x5442222221333331111111111111 6 15),
([w1,w2,w32,w6,w0,w3,w4,w5,w29],dL 0x9d0df07d0990f8153114,dS 0x11150b13083c043121190c12363826324037100e0201,pH 0x111221231324144525116111111111111111 7 22),
([w26,w1,w2,w32,w6,w0,w3,w4,w5],dL 0xe70991490fc115,dS 0x12150c0b11082604311b13363c403810320e020135,pH 0x411222114422215111212111212111121211 5 21),
([w98,w1,w2,w0,w134,w3,w4,w5],dL 0x9d16915a16416309916615b096165091,dS 0xc102419160d0a110b0201060e,pH 0x2251114444333331111111221987 11 13),
([w154,w1,w2,w6,w0,w4,w5],dL 0x8614116e161096099093091,dS 0xd21363c0531100e2f0c02190111,pH 0x322111444611111735556 8 14),
([w319,w1,w2,w6,w0,w3,w5],dL 0x1f17009409916216f0d714107d093096035091,dS 0x100d21312f02011511171926,pH 0x644111222711181a55187 13 12),
([w1,w2,w6,w0,w593,w3,w4],dL 0x17315103517217109914109d093094091,dS 0xe100b0d19153336383c3231210c0102,pH 0x544333111122227111787 11 16),
([w594,w1,w2,w6,w0,w3,w4],dL 0x17615a03509417517409914109309e096091,dS 0x1915333832311202010e181b3c2136,pH 0x544111222711181333187 12 15),
([w1,w2,w6,w0,w3,w4,w595,w5],dL 0x1f17d1470ac11a17c17b11b17e09317917a07d099,dS 0x1c1b12210c36332631150e380b320201,pH 0x2156215115121113313341114434 14 16),
([w40,w155,w1,w2,w3,w4,w5],dL 0x9918017f096093091,dS 0x1311100f3646333c2645310906340e02180c0d0b01,pH 0x544333111111111222211 6 21),
([w40,w1,w2,w0,w3,w4,w59,w5],dL 0x8618411418111711c11b11a183096182091,dS 0x13190a060c1b020112110e091522,pH 0x1514142122333331111112122198 12 14),
([w47,w40,w1,w2,w0,w3,w4,w5],dL 0x11c03e1841230910b709611b18a09911a0cc,dS 0x171b19100209220c120e,pH 0x2421115241323131118113831221 12 10),
([w40,w1,w2,w119,w6,w0,w3,w4,w5],dL 0x18509e1510a1091184152,dS 0x1821150c1213350922310b363c020119383210110e,pH 0x221111333112217211112211112111115111 7 21),
([w40,w1,w2,w0,w3,w4,w5,w222],dL 0x11a18d18c18509918e09615d091,dS 0x210c0922190a120e0201061115,pH 0x6151441222333331111111222187 9 13),
([w98,w40,w1,w2,w6,w0,w3,w4,w5],dL 0x9d15a1840a109118515b,dS 0x2115350a06310b120c19110201130e10363c,pH 0x221211333121111211111111161111115111 7 18),
([w98,w40,w1,w2,w0,w3,w4,w5],dL 0x9d0a119309619211b19409118515b,dS 0xc351906100201110e,pH 0x2241112741263111113113221221 10 9),
([w40,w1,w2,w6,w0,w3,w4,w5,w29],dL 0xf80df099185,dS 0x1137091006310b0c1202012113190e153832,pH 0x212112133312123111131111131131111411 4 18),
([w26,w40,w1,w2,w6,w0,w3,w4,w5],dL 0xfc0990e718411b,dS 0x12150c35092606310b1b13100201110e,pH 0x411133114311131111311333153311111113 5 16),
([w155,w1,w2,w119,w0,w3,w4,w5],dL 0x9919a151096199091,dS 0xe13240b16040c0922100d211519,pH 0x2252441222333331111111111111 6 14),
([w47,w1,w2,w0,w3,w59,w5],dL 0xb70b510404003e19c096091,dS 0x121c0c2c3a2b3f0522132f1101191502101a0904,pH 0x131513222211111444476 8 20),
([w1,w2,w6,w0,w3,w4,w87],dL 0x1a40861a21a109d1411a3094091,dS 0x10121a0c36333832310e1511210102,pH 0x343534111122226111676 9 15),
([w184,w1,w2,w6,w0,w3,w4],dL 0x1a80880941a61a514109e0961a7091,dS 0xc333832311b1202010e191511363c21,pH 0x225111333611171244176 10 16),
([w79,w2,w0,w3,w4,w59,w5],dL 0x1aa0aa1001ab096040091,dS 0x3f101c06111a0e2c472a2b052212161509040201,pH 0x152414215433337111111 7 20),
([w86,w1,w0,w3,w4,w59,w5],dL 0xa81b00af1b1096040091,dS 0x3a101c111a0e2b4705222c2a120a081502040901,pH 0x152414215411111333336 7 20),
([w1,w2,w320,w0,w3,w4,w59,w5],dL 0x880b71151821b31b21141b4096040147091,dS 0x1210150c1a0e2c082a2b16051c292201020409,pH 0x1635152122212214444481111171 12 19),
([w321,w1,w2,w0,w3,w4,w59,w5],dL 0x8611b1471b91b811a1ba096182040091,dS 0x190c0a0611091b0e0201221215,pH 0x1625153133444441111113133187 11 13),
([w1,w2,w0,w3,w4,w87,w59],dL 0xad0861bf1a21a11a31be096040091,dS 0x100c1c111a0e082c2a2b0522121509010204,pH 0x225144185433337111116 10 18),
([w184,w1,w2,w0,w3,w4,w59],dL 0x881a31c01a61a51c10960ad091,dS 0x190c111a0a2a090605221b02010e151c122c2b,pH 0x112124333311111122765 9 19),
([w47,w58,w1,w2,w6,w0,w3,w5],dL 0xa90b717c01f1c307d099,dS 0x10213633020401261738111c1519,pH 0x3431115552222122212222221222 7 14),
([w47,w26,w1,w2,w6,w0,w3,w5],dL 0xa91c40d40ad07d099,dS 0x123304012610380c1115213619,pH 0x3351114442222121222222221222 6 13),
([w47,w58,w1,w2,w0,w3,w5],dL 0x960030401c507d03e0b7,dS 0x10120e170b05040c382f193215371c11,pH 0x411541331111111221221 7 16),
([w47,w26,w1,w2,w0,w3,w5],dL 0x1c61c807d1c703e0ad,dS 0x211510090b0522011b2f1a120e020411,pH 0x115133146112222222222 6 16),
([w1,w2,w6,w0,w3,w4,w322,w5],dL 0x930a11ce0860de1a309d13e1cd1cc07d099,dS 0x120c36330e380b323121260d15100201,pH 0x1165216215121114411131113343 12 16),
([w1,w2,w119,w0,w3,w4,w222],dL 0x1a31511d21d01cf0991d109d096091,dS 0xc19111b084a3338360449323c210e1512011c0248,pH 0x114184133322227111116 10 21),
([w106,w1,w2,w119,w6,w0,w3,w4],dL 0x1d60911d81d71d41d30ad1d509d151,dS 0xe191812353336263c311c0d383210020115211a,pH 0x3114312214666767558571125165 10 20),
([w323,w1,w2,w6,w0,w3,w5],dL 0x1dd1da09e1a008809407d1dc1db141099096035091,dS 0x120e0c32312f02012111152619,pH 0x5b5111222611171448176 14 13),
([w98,w221,w1,w2,w0,w3,w4],dL 0x15a0991e21e109609e091,dS 0x114d38263231180a061c0e0219211b011e12,pH 0x454333111111111222211 7 18),
([w98,w1,w2,w6,w69,w0,w3,w4],dL 0x961e70911e51e40ad09e1e61e315a09d,dS 0x1e1915112632311c0201350c0e1036210b1b123c,pH 0x4221156421742133321735551111 11 20),
([w1,w2,w324,w6,w0,w3,w4,w5],dL 0x1f11513c0931eb1ec13b1ea114,dS 0x211512363c323138260b1b19350e021001,pH 0x1446149143914365545252222522 9 17),
([w1,w2,w324,w0,w3,w4,w5],dL 0x1f11517e0991141eb1ea093,dS 0xf350826191b120b010e1a0216,pH 0x466111746133312222212 8 13),
([w596,w1,w2,w0,w3,w4,w5],dL 0x1f1ee1ed141093096091,dS 0x111b0d0c09040b0e0108211519,pH 0x544333222211111111111 7 13),
([w1,w2,w597,w0,w3,w4,w5],dL 0x31f01ef16901f1410a1162094091,dS 0x131b0b0c33080421110a01290602,pH 0x353434111122222111118 10 14),
([w1,w2,w325,w6,w0,w3,w4,w5],dL 0x11b01f17c0a11f21f317b1f111a,dS 0x210b12363c26311138321c1915370e100201,pH 0x1446148143814365545252222522 9 18),
([w1,w2,w325,w0,w3,w4,w5],dL 0x1f11b1f20991f10a11f4,dS 0xc0a371512020119110e0610,pH 0x111222111251123333323 7 12),
([w2,w6,w0,w149,w3,w4,w5],dL 0x3502409d1f60991f70a1091,dS 0xd06153601311935100b0e0c02,pH 0x433711222711152855557 8 13),
([w1,w6,w0,w120,w3,w4,w5],dL 0x9401f02509d1f91fa0a1096,dS 0x1b12111f19153c26310e020b0a341001,pH 0x533611222611142844446 8 16),
([w1,w2,w0,w598,w3,w4,w5],dL 0x691fc1f903509d0991410a1094091,dS 0x12100e21150d33080a040b0102060c,pH 0x544111333122222111118 10 15),
([w99,w1,w2,w6,w0,w3,w4,w5],dL 0x2001fd01f1e51fe09d1ff0a1,dS 0x353c26323110020112110e0b2119150c,pH 0x8221113821362144121776821111 8 16),
([w99,w1,w2,w0,w3,w4,w5],dL 0x2011fd1fe01f11b0a1,dS 0x2f353326103401121b11190e02150c210b06,pH 0x266111555144414226144 6 18),
([w1,w2,w6,w0,w3,w4,w129,w5],dL 0x7a09609d0a120e20d1fb20f07d,dS 0x150c36380b3c32312112260e34100201,pH 0x1162226112711265552141144454 9 16),
([w1,w2,w326,w6,w0,w3,w4,w5],dL 0x1512160932132152142120ad,dS 0x1c1538363c263119210d320c11350e100201,pH 0x1441143146314815545252222522 8 18),
([w1,w2,w326,w0,w3,w4,w5],dL 0x21721317e2120930ad,dS 0x3b3d05210c3502010d0e1c101104,pH 0x111222114211523333323 6 14),
([w599,w1,w2,w0,w3,w4,w5],dL 0x9e099141093096091,dS 0x20c09060b0e04192115,pH 0x544333222211111111111 6 10)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p2 : List StD := [
([w1,w2,w600,w0,w3,w4,w5],dL 0x21a21921809e0991410a1094091,dS 0x110b210c363308040e191e09012202,pH 0x544333111122222111117 9 15),
([w1,w2,w327,w6,w0,w3,w4,w5],dL 0x1d40a121c21d21b1d30ad,dS 0x120d3c26311921151138320c0e10350201,pH 0x1441142142214215545353333533 7 17),
([w1,w2,w327,w0,w3,w4,w5],dL 0x21e21c21b0ad0a121f,dS 0x2115123d02010c351b100d110e22,pH 0x111222131213124444424 6 14),
([w1,w2,w601,w0,w3,w4,w5],dL 0x22322222109d099141093096091,dS 0x100e0d0b21152c3808263204190c24010216,pH 0x544333111122221111117 9 18),
([w1,w2,w328,w6,w0,w3,w4,w5],dL 0x22915a01f22809d093225227226224,dS 0x1819151311382632311c363c210b0c350e020110,pH 0x6335532835283984434141111411 10 20),
([w1,w2,w328,w0,w3,w4,w5],dL 0x22a11517e22522401f093,dS 0x180c3b352621130b010e1c1102341610,pH 0x255111225144413333313 7 16),
([w1,w2,w6,w0,w3,w4,w223,w5],dL 0x7e0f809609d22d09322f22c22e07d,dS 0x210c3637380b3c32311526130e1210340201,pH 0x1152225112711296612131333363 10 18),
([w1,w2,w107,w6,w0,w3,w4,w5],dL 0x930a10990de09e2320e02330e11a3,dS 0x210f13383c323112150b0c362619370e100201,pH 0x1336131138513964434242222422 10 19),
([w1,w2,w107,w0,w3,w4,w5],dL 0x300f2340990e021f09e0e11a3,dS 0x21150f373832020b121908130e1001,pH 0x131314114751452222222 9 15),
([w602,w1,w2,w0,w3,w4,w5],dL 0xf00323609e141096235091,dS 0x121136383c320904010e0821191e,pH 0x244624333311111111111 8 14),
([w1,w2,w0,w20,w3,w4,w185,w5],dL 0xd10d323c23d03523b23923a0a809f096,dS 0x3b131b082b0522091110153d0e0b0104,pH 0x7624441111555533333132222222 11 16),
([w17,w1,w2,w0,w3,w4,w185,w5],dL 0xf32402432410f424223e23f0a8095035096,dS 0x3b131b110922010e1c1a15,pH 0x2536667256111113433331111113 12 11),
([w1,w2,w0,w3,w185,w13,w5],dL 0x3e0a80402460aa096,dS 0x10121a0e082b05221c3537092a11041501,pH 0x162313416311111222222 6 17),
([w22,w110,w2,w0,w3,w4,w5],dL 0xcf24c24b24809f094,dS 0x13113c260502060e0b090a160d010410,pH 0x544333111111122222212 6 16),
([w22,w1,w2,w0,w20,w3,w4,w5,w29],dL 0x2510de25325224f2500cf,dS 0x110f100937084f0138040e12130b,pH 0x111441333333131111111112111211211311 7 14),
([w26,w22,w1,w2,w0,w20,w3,w4,w5],dL 0x2572560cf254255,dS 0x121009084f0138041b130e0b11,pH 0x311115115311313222222222221111111122 5 13),
([w22,w83,w2,w0,w3,w4,w5],dL 0xcf25b25a251095094,dS 0x13110e242a3c2602040b1508220d010610,pH 0x544333111111122222212 6 17),
([w22,w17,w1,w2,w0,w3,w4,w5,w29],dL 0x25e0f725d0de25c0cf,dS 0x1147090204211912150e13,pH 0x111441511111311222222311111222222112 6 11),
([w26,w22,w17,w1,w2,w0,w3,w4,w5],dL 0x2610cf25f260,dS 0x122a47011a0902041b130b15110e,pH 0x311111113322222111312222211211111212 4 14),
([w22,w79,w2,w0,w3,w4,w5],dL 0x26301f2620aa035094,dS 0x101c1a0e15020412111606,pH 0x464546111113113333313 6 11),
([w22,w219,w2,w0,w3,w4,w5],dL 0x26624726724e0bf094,dS 0xe1c19152c0a263205040206241b10110122,pH 0x334364111121112222212 6 18),
([w22,w220,w2,w0,w3,w4,w5],dL 0x26b0cf26a24d0b9094,dS 0xe1c111526322b0204191b090816011006,pH 0x334364111121112222212 6 17),
([w1,w2,w603,w0,w3,w4,w5],dL 0x1e26d26e07824803501a,dS 0x130e1011170a0908322f0d260b160201,pH 0x575333212122236111111 7 16),
([w604,w1,w2,w0,w3,w4,w5],dL 0x25126f07d022020035,dS 0x13100b0d1a111501060e0a08,pH 0x433643111122222121252 6 12),
([w1,w2,w0,w605,w3,w4,w5],dL 0x81026251024035,dS 0x1b12100f0d0e0b0a0c08060109,pH 0x544211333211111222222 5 13),
([w22,w2,w0,w149,w3,w4,w5],dL 0x24d273091272251024035,dS 0x131211100f260d080406010b0e0c0a09,pH 0x644211333211113222222 7 16),
([w1,w2,w606,w0,w3,w4,w5],dL 0x24e27627502b078248035027,dS 0x211b100f3418200a09083c050e32040d0201,pH 0x755333122122236111111 8 18),
([w607,w1,w2,w0,w3,w4,w5],dL 0x27725108502f02d035,dS 0x120d181c150122090e08,pH 0x433453111122222211262 6 10),
([w608,w1,w2,w0,w3,w4,w5],dL 0x24d279032078030035,dS 0x1b21100f0d0e0c092401160b08,pH 0x644333111122222211252 6 13),
([w1,w2,w609,w0,w3,w4,w5],dL 0x27c03424e03607d006035,dS 0x1c12190e0a0832261115090102,pH 0x343734221111111222222 7 13),
([w1,w2,w0,w3,w329,w15,w5],dL 0x3e04027f0a80aa091,dS 0x10121a110e2c2a060522041c370215350926,pH 0x162414516431233212222 6 18),
([w109,w10,w1,w0,w3,w4,w5],dL 0x99287285286035283091094,dS 0x1311100f0d0133020447090e34380b,pH 0x755336222222222111122 8 15),
([w10,w1,w90,w0,w3,w4,w5],dL 0x9928d28c03528a09f094091,dS 0x1311100f0d3308010e0b3438,pH 0x766444222333333111113 8 12),
([w10,w1,w0,w3,w15,w13,w5],dL 0x29028228f0940aa044,dS 0x1b121a0e060839261c02372a153509,pH 0x312431631422122111112 6 15),
([w86,w10,w1,w0,w3,w4,w5],dL 0xae04e262291091094,dS 0x1c111a01363302044709120e1538,pH 0x433543222222222111122 6 14),
([w218,w10,w1,w0,w3,w4,w5],dL 0x295294035289099293091094,dS 0x1c121901330204470a110e1538,pH 0x433873222222222111122 8 13),
([w10,w1,w146,w0,w3,w4,w5],dL 0x2990352880992980bf094091,dS 0x10121c111533380801190e02,pH 0x544684322233333111113 8 12),
([w1,w610,w2,w0,w3,w4,w5],dL 0x29e29d29c0f7283094,dS 0x1a191017020c06050e3d040b01,pH 0x565222111211124111214 6 13),
([w611,w1,w2,w0,w3,w4,w5],dL 0x1f01ef2a001f29f021094,dS 0x13122f1c3511150a021b100604,pH 0x433443111111111111116 7 13),
([w1,w2,w0,w612,w3,w4,w5],dL 0x1fc1f901f2a029f28a025094,dS 0x13121b0e2f3d050a0211100b063404,pH 0x544211333222222111377 8 15),
([w10,w1,w0,w120,w3,w4,w5],dL 0x962a401f28a025094,dS 0x13121b102f333d05080a0f11020b0c0406,pH 0x454211333211113222222 6 17),
([w10,w1,w2,w0,w3,w4,w129,w5],dL 0x942882a528a2a320e07d,dS 0x100f180c16020105120e0b06,pH 0x1145114114222221111122222212 7 12),
([w1,w613,w2,w0,w3,w4,w5],dL 0x2892a92a829e2a70f7283094,dS 0x121c100e020c06050f04200b01,pH 0x756222111211124111214 8 13),
([w614,w1,w2,w0,w3,w4,w5],dL 0x2182ab28a2192aa02e094,dS 0x121b06050e200902220b1004,pH 0x334354111111111111117 7 12),
([w615,w1,w2,w0,w3,w4,w5],dL 0x28822129e2230f7031094,dS 0x1c12103d0b0e24020c151604,pH 0x754334111111111111116 7 12),
([w10,w1,w2,w0,w3,w4,w223,w5],dL 0x942882ae28322d07d,dS 0x1b100c0502010f0b0604120e37,pH 0x1134113113222221111122222212 6 13),
([w1,w616,w2,w0,w3,w4,w5],dL 0x2b22b12b32ab2aa289094,dS 0x21131915021b050612040e01,pH 0x224257211121116211116 7 12),
([w10,w118,w2,w0,w3,w4,w5],dL 0x60342b52b4289091,dS 0x1c19150204065032123801370e,pH 0x223243243511111111111 6 13),
([w1,w75,w0,w3,w4,w13,w5],dL 0x2ba2b91022b80aa096,dS 0x1b38353711182c0532100e0b0916040c2a01,pH 0x131513413412111222222 6 18),
([w52,w1,w75,w0,w3,w4,w5],dL 0x2ba09604301f2bc2bb1110b4,dS 0x120c09111005031a38041b0f013b,pH 0x544333514211111222221 8 14),
([w1,w75,w0,w3,w4,w5,w80],dL 0x2ba2bf2be2bd1290960bf,dS 0x1b1138123b15100f184a2c1605320e0b0a040c2401,pH 0x624255233312222111111 7 21),
([w130,w1,w75,w0,w3,w4,w5],dL 0x812c12c01111de2ba,dS 0x130c1b1110050312381c0401350e,pH 0x155444115322222133332 6 14),
([w1,w2,w0,w3,w4,w617,w5],dL 0x4013a1082b803e1020aa096,dS 0x1b110e182c02380522100b0916040c2a01,pH 0x154615313311117222222 8 17),
([w330,w1,w2,w75,w0,w3,w4,w5],dL 0x2ba2c207d01f2c32bb2b80b4096,dS 0xc1b0503120f0e0b013d38101c04,pH 0x3534341358135422222227154322 9 14),
([w330,w1,w2,w0,w3,w4,w5],dL 0x2ba0962c20402c42bb0b403e,dS 0xc2c031a04101c0f38013d,pH 0x141333664622222111622 8 11),
([w1,w2,w618,w75,w0,w3,w4,w5],dL 0x2bf2c501f2c72c60962bd1c9,dS 0x11510e0b0532373d1b383c0c041001,pH 0x2252442337322282377111111111 8 15),
([w619,w1,w2,w75,w0,w3,w4,w5],dL 0x2ca2bd2c80962c92c01de2ba,dS 0x131b3503121a380b01110e100c04,pH 0x1443337146614322222221843722 8 14),
([w1,w2,w75,w0,w3,w4,w5,w29],dL 0x960de2cc2cb0122b80062bf,dS 0x110f16053212371310210b0e380c0401,pH 0x3335554444113541135422222222 8 16),
([w26,w1,w2,w75,w0,w3,w4,w5],dL 0x2d00150d42cf00b2bd2ba,dS 0x25120c0b04321b131110350e381601,pH 0x2212162174244433333332122243 7 15),
([w1,w2,w0,w3,w224,w13,w5],dL 0x2d50942d32d410213a03e0aa,dS 0x1b1a370f182c390522100c350e090b16042a01,pH 0x221555444432333111111 8 19),
([w620,w1,w2,w0,w3,w4,w5],dL 0x13a0402d72d62d80ae096,dS 0x37120309011a100429171c,pH 0x355444111122222121112 7 11),
([w1,w2,w0,w3,w224,w5,w29],dL 0x942da2db2d901203e006,dS 0x1b280f021a12213713160522100e0b040c01,pH 0x512444333326243111111 7 18),
([w621,w1,w2,w0,w3,w4,w5],dL 0x10a1081020942dd0aa,dS 0x1a370d0904110e0c100b0601,pH 0x252424323411111313411 6 12),
([w622,w1,w2,w0,w3,w4,w5],dL 0x2ba01f07d2b82c42bb1110b4,dS 0xc1207031a0e100f04011c,pH 0x544333222211111614211 8 11)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p3 : List StD := [
([w1,w2,w623,w0,w3,w4,w5],dL 0x8101f2e02df1112c61c9,dS 0x1310180e4a05031a083c04400901,pH 0x445222175233321111111 7 14),
([w624,w1,w2,w0,w3,w4,w5],dL 0x2e32e41290940bf2d5,dS 0x130e1c100311150c0b0401,pH 0x155444333422222233422 6 11),
([w625,w1,w2,w0,w3,w4,w5],dL 0x852e52c01112d51de,dS 0x382c07030c10041a010e,pH 0x655444333311111165311 6 10),
([w1,w626,w2,w0,w3,w4,w5],dL 0x2e72e81350940b92aa,dS 0x120c1b0e1c100d050b0106,pH 0x155444333423342222222 6 11),
([w627,w1,w2,w0,w3,w4,w5],dL 0x2ed0960022e90360122ec00607d,dS 0x121c0b1603110210010f0c04,pH 0x151414915422222221112 9 12),
([w186,w1,w2,w0,w3,w15,w5],dL 0x402f22f30b203e035020091,dS 0x3b100d170a0906132f0f370b081102,pH 0x161517313321222424242 8 15),
([w1,w2,w24,w3,w4,w183,w5],dL 0x7d00f2f92fb2fa0eb2f70942f8,dS 0x34182408090d191a03021710060e,pH 0x912333611322232444484 9 14),
([w17,w1,w2,w24,w3,w4,w5,w29],dL 0x30230130025c2fe0080122fd2ff,dS 0x110f3708130c1210060b0219340d0e03,pH 0x2225524444112546626363333336 9 16),
([w26,w17,w1,w2,w24,w3,w4,w5],dL 0x30a30725f30630930800d0152fd,dS 0x122a220c131a3d0b02030d341024060e,pH 0x5443336648774212222321543672 9 16),
([w1,w2,w0,w3,w4,w628,w5],dL 0x4030d2430eb30e30c0962fb035,dS 0x3b1310113d1724050f2f0d060b01080904,pH 0x143514212711111111116 9 17),
([w629,w1,w2,w0,w3,w4,w5],dL 0x31030f30c141103094040096,dS 0x1208110c02011b0610,pH 0x655444111133331111117 8 9),
([w109,w1,w2,w0,w3,w4,w5,w29],dL 0x3000de25e25c09631209930c3110083130cf,dS 0xf3421100d061213370b010e,pH 0x6754443333225432254312764a69 12 12),
([w26,w109,w1,w2,w0,w3,w4,w5],dL 0x31425f09931500d306312310,dS 0x2512080c1b1306351110010b0e,pH 0x2212142153215372333672122222 8 13),
([w1,w2,w0,w630,w3,w4,w5],dL 0x31931701f31b10a31a3181031b2035099094,dS 0x351b212924220e370d16320c090806,pH 0x67683c555111111444444 12 15),
([w1,w2,w0,w631,w3,w4,w5],dL 0x31001f31c30c09203530e,dS 0x131b12353415240922110d08010e06,pH 0x411222111533333222325 7 15),
([w52,w186,w1,w2,w0,w3,w5],dL 0x31e0352fb04016f,dS 0xb03110c3a02121032373b0f,pH 0x533111443125314111111 5 12),
([w2,w150,w0,w24,w3,w4,w5],dL 0x1c932109b31f099320092091,dS 0x103c341115220336370d0802320e0906,pH 0x433111753111111222121 8 16),
([w632,w1,w2,w0,w3,w4,w5],dL 0x31032632532409b0cf035092327,dS 0x10151208020e3c37,pH 0x411111222233332333626 9 8),
([w1,w2,w0,w633,w3,w4,w5],dL 0x32b32a2f432c03509432909c12a,dS 0x1310172a05110c320e080d3604,pH 0x226179111144444333333 9 13),
([w1,w2,w0,w634,w3,w4,w5],dL 0x32f32e2f4035092330,dS 0x130b2235342a010d360e06,pH 0x411333111522222335255 6 11),
([w1,w635,w2,w0,w3,w4,w5],dL 0x3340860943330353353322aa09b,dS 0x1824092216033215080e0d0206,pH 0x114144122212937333333 9 13),
([w1,w2,w0,w24,w3,w4,w97,w5],dL 0x30109b13107d33830009412f337132,dS 0xf122c2203023409130e32100d0608,pH 0x5642221112111235542113333831 10 15),
([w1,w2,w187,w24,w3,w4,w5],dL 0x33e00f33d1ef34134033f094,dS 0x1318340a0e110d220307100617,pH 0x422332111111117111155 8 13),
([w1,w2,w636,w0,w3,w4,w5],dL 0x1f00401ef169141340094162096,dS 0x35371b0d0e213a3308050b290a060204,pH 0x252424111111111333377 9 16),
([w186,w26,w1,w2,w0,w3,w5],dL 0x34607d3452f400d03e,dS 0x100b0d051b37252f130e26350611,pH 0x422462452541211112112 6 14),
([w188,w1,w2,w0,w24,w3,w4,w5],dL 0x34a2aa2b109c34933c348094,dS 0x370201090e120d06321310,pH 0x3442222226111111111111111116 8 11),
([w1,w2,w0,w225,w3,w4,w5],dL 0x962340cf34d09c34b099305,dS 0xd2212370902130c10010e06,pH 0x411211111172171333333 8 12),
([w1,w116,w0,w3,w4,w13,w5],dL 0x10311d3513500960aa,dS 0x360e180b2c220237351509100601,pH 0x245333624321235111111 6 14),
([w52,w1,w116,w0,w3,w4,w5],dL 0x3510f70960433522fb11d0b4,dS 0xe182c2236330b0919150611020110,pH 0x544353714211111222221 8 15),
([w1,w2,w0,w3,w4,w637,w5],dL 0x4014717a1083511030aa096,dS 0x1c13191011182c082a05152f09040c0b060201,pH 0x141514313711116222222 8 19),
([w638,w1,w2,w0,w3,w4,w5],dL 0x3540963530402c42fb0b403e,dS 0x2c111004021b0f3d01,pH 0x141333664622222111622 8 9),
([w1,w2,w116,w0,w3,w4,w5,w29],dL 0x960f73593560de357358351008355006,dS 0x19372215361213210e0b020c100601,pH 0x4642223332764238142311111111 11 15),
([w26,w1,w2,w116,w0,w3,w4,w5],dL 0xd35b35a0d400b357354,dS 0x25120e1a150b35331b13360210061101,pH 0x2212162165245533333332122453 7 16),
([w1,w2,w0,w3,w331,w13,w5],dL 0x9435e35f10317a03e0aa,dS 0x1311370f180c2c3909050410350b0e2a0626,pH 0x221555444432333111111 7 18),
([w639,w1,w2,w0,w3,w4,w5],dL 0x17a2d73400400ae360096,dS 0x13122f0201111017041b,pH 0x266555111133333131113 7 10),
([w1,w2,w0,w640,w3,w4,w5],dL 0x10a1083633641030940aa,dS 0x11130d2c220e100c2a1602060b32,pH 0x464212333324515111111 7 14),
([w641,w1,w2,w0,w3,w4,w5],dL 0x35401f07d3512c42fb11d0b4,dS 0x1202100e06110f011b,pH 0x544333222211111614211 8 9),
([w1,w2,w642,w0,w3,w4,w5],dL 0x1f32308111d2e01c9,dS 0x1318120e36082211023c06091032,pH 0x422552142333231111111 6 14),
([w54,w2,w150,w0,w3,w4,w5],dL 0x31f09101f36711d1c9081,dS 0x1c153d063608090119023c1b1110,pH 0x114154211133332222222 7 14),
([w1,w2,w0,w643,w3,w4,w5],dL 0x36a2e436936112a0940bf,dS 0x1310182c06050e11240c0b020432,pH 0x466122333322515111111 7 14),
([w644,w1,w2,w0,w3,w4,w5],dL 0x852e532d11d3611de,dS 0xb2c1015060211010e,pH 0x655444333311111165311 6 9),
([w645,w1,w2,w0,w3,w4,w5],dL 0x36e36d2e80941360b92aa,dS 0x120e02060d0b221b10,pH 0x155333444322222244722 7 9),
([w1,w2,w0,w646,w3,w4,w5],dL 0x9600237237300837107d036006,dS 0x121b37020b22110e0c061001,pH 0x322112552563237111111 9 12),
([w1,w2,w0,w3,w4,w647,w5],dL 0x4037837714137603e102094096,dS 0x1b110e0b02010522100a09160d172a04,pH 0x154615313311111212227 9 16),
([w648,w1,w2,w0,w3,w4,w5],dL 0x37a0d70403792bb03503e,dS 0x101519043b010f3d0a,pH 0x141313212221222111116 7 9),
([w1,w2,w90,w0,w3,w4,w5,w29],dL 0x37c09637b01225037d0990cf,dS 0x11340a12100d160532153721130e0b010904,pH 0x2336665555331658126522242222 8 18),
([w26,w1,w2,w90,w0,w3,w4,w5],dL 0x9937f0152540d437e30637a,dS 0x25121511350c04321b130a0b100e160901,pH 0x3313163272322283555583133425 8 17),
([w1,w2,w0,w3,w332,w15,w5],dL 0x3503e3810b101a091,dS 0x35130a0801052204191502110e0b100d26,pH 0x152414312361543212222 6 17),
([w649,w1,w2,w0,w3,w4,w5],dL 0x38529c1410940402d61ee096,dS 0x350e05030901191b15042117,pH 0x266333111155551111117 8 12),
([w147,w18,w1,w2,w3,w4,w5],dL 0x9438d0d700338e38b38c2bb07d,dS 0xa16050d340e10170b0f0701043d,pH 0x133444113122226863272 9 14),
([w18,w1,w2,w20,w3,w4,w5,w29],dL 0x30230007825037c38f390008012391,dS 0x11370c34120e100d043d130701090b15,pH 0x5114443333661421174362222222 10 16),
([w26,w18,w1,w2,w20,w3,w4,w5],dL 0x39430725439339200d30601538f,dS 0x12110904150c130d3407013d0b100e0a16,pH 0x6554443352775712222241654372 9 17),
([w1,w650,w2,w0,w3,w4,w5],dL 0x1b801f397396035102078,dS 0x191b0c0b35090a0510120e0106,pH 0x544111333111111111177 7 13),
([w651,w1,w2,w0,w3,w4,w5],dL 0x39637a39a3993762bb3980350a0078,dS 0x13101b0e113432012f0d0a042a09,pH 0x686111222233332333424 10 14),
([w1,w2,w652,w0,w3,w4,w5],dL 0xa50cf39e2c639d39c0780350a0,dS 0x13101b0e2f340a0816053d0f01090d0402,pH 0x877333222411111224414 9 17),
([w1,w653,w2,w0,w3,w4,w5],dL 0x3a33a43a20880943a10780350a6,dS 0x123b0e24050d0f0c01093604,pH 0x119133155313315444444 9 12),
([w654,w1,w2,w0,w3,w4,w5],dL 0x3a73a63a53a40350a0078,dS 0x211b100e0d010f34040b0924,pH 0x447111222233332333525 7 12),
([w655,w1,w2,w0,w3,w4,w5],dL 0x3ad3ac3aa01f3973a93ab3961350a5078,dS 0x3b0a35041206110e020110,pH 0x224233254321135211656 11 11),
([w18,w1,w2,w0,w3,w4,w97,w5],dL 0x38d1320780a537c0943af3b013107d,dS 0x102c08160d02190121090515,pH 0x6354442222533521134262222522 10 12),
([w226,w18,w1,w2,w3,w4,w5],dL 0x29c3b53b33b42d6094,dS 0x1a102408160503070e193d340b020401170d,pH 0x353111111122222121144 6 18),
([w1,w656,w2,w0,w3,w4,w5],dL 0x3b93b83ba3a43b70880a6078,dS 0x211335100532040e1201,pH 0x225211268121141211144 8 10),
([w188,w18,w1,w2,w0,w3,w4,w5],dL 0x73bd3b30780a63bc3b13bb094,dS 0xe06090d19130115102104,pH 0x3442221112111212221221112117 9 11),
([w1,w2,w0,w3,w189,w15,w5],dL 0x3e3c23c1035006091,dS 0x1012191a110e0a010522041c370802150926,pH 0x122414516431333212222 6 18),
([w2,w21,w0,w3,w4,w15,w5],dL 0x3c83c70b13c60a8091,dS 0x3b13191011172b0522242a02260f322f0d080c3804,pH 0x131513413411111212221 6 21)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p4 : List StD := [
([w1,w2,w0,w3,w15,w227,w5],dL 0x353cc3c93cb0b113903e0a8,dS 0x133b35242b54050f0c110d02100b0804,pH 0x223555444411111336333 8 16),
([w1,w2,w0,w3,w4,w657,w5],dL 0x6a04a04013d1393c63790b10a8091,dS 0x1910112f0d242b01320522260f0b08020c0904,pH 0x154415313321222111116 10 19),
([w658,w1,w2,w0,w3,w4,w5],dL 0x3d004e3cd3cf0430350b13ce0a8,dS 0x12101b0e2f170a2a07040f08320c0d02,pH 0x262323111142431474317 9 16),
([w1,w2,w0,w659,w3,w4,w5],dL 0x3d73d504e3d60430943d40b2035,dS 0x200a090526120e0f0b16080c3804,pH 0x565538222244444333233 9 14),
([w660,w1,w2,w0,w3,w4,w5],dL 0x3d90943d60b23d8040091,dS 0x1202160c010d10263b0a0f,pH 0x255444363611111161111 7 11),
([w1,w2,w0,w20,w3,w4,w228,w15,w5],dL 0xb10943da3de3db3dc035,dS 0x13351a150207015405223d2b260a100e110b0904,pH 0x115216212431633113111116111111111111 7 20),
([w1,w2,w0,w3,w229,w15,w5],dL 0x400353e03e10b21790a803e,dS 0x3b130f0c2b5505090a0e0b110d381004,pH 0x113555444422222313333 8 16),
([w1,w2,w0,w3,w4,w661,w5],dL 0x4017d1471793d63e20b20a8091,dS 0x3b131910110d0a082a2b060522152f02010c0b0904,pH 0x141514313721222111116 9 21),
([w1,w2,w0,w662,w3,w4,w5],dL 0x3d60433e53e33e40b20350a8,dS 0x13102f0a092b05010e110c080d3804,pH 0x464252333311111245155 8 15),
([w1,w2,w0,w3,w4,w663,w5],dL 0x4030d0eb3eb3790940b13ea091,dS 0x3b10112f0c17240105260f0d0809060b0204,pH 0x164516313321222111117 9 18),
([w1,w2,w664,w0,w3,w4,w5],dL 0x3f03ee04304e3ed3ef0943ec0350b1,dS 0xb2a0526120e0f0c0a08060204,pH 0x656111839144444333333 10 13),
([w17,w1,w2,w0,w3,w4,w228,w15,w5],dL 0xb23f13f50353f23f4,dS 0x35102c2a0b110c0913021a1522040e,pH 0x335111131422222141333155532422211111 6 15),
([w148,w2,w0,w3,w15,w13,w5],dL 0x3b04010a3f83f73f60aa03e,dS 0x10121c55160e2c2b1101052204153509062a26,pH 0x112511711531133222222 8 19),
([w79,w2,w0,w3,w15,w13,w5],dL 0x3f72800aa0440403f903e094,dS 0x3b10121a11160e2c2b0522261c2a15060904,pH 0x121312412317111161155 8 18),
([w1,w230,w0,w3,w15,w13,w5],dL 0x3b0400433fb0a80443fa03e,dS 0x10120a390e2c02352b0522261c152a110904,pH 0x112511711541144223222 8 18),
([w86,w1,w0,w3,w15,w13,w5],dL 0x2453f70441b00a804003e3fc094,dS 0x10120a0e2b1105222c02041c353715092a0826,pH 0x131212413211111161186 9 19),
([w1,w2,w131,w0,w3,w15,w13,w5],dL 0x2d50432d30404003391b33fe0443ff03e,dS 0xf0c350e2c37392b550526101a2911221c2a0409,pH 0x1117112112211235915553393333 11 20),
([w190,w1,w2,w0,w3,w15,w13,w5],dL 0x3ff3614020431b940104004440403e403,dS 0x102b5505260e0904221b120f2a11,pH 0x22233311117a77766a6641911476 11 14),
([w1,w230,w0,w3,w4,w59,w5],dL 0x3fa10d4060a8040091,dS 0x19101c111a0e2c2a2b0631052226120a0815020904,pH 0x152414215431333111116 6 21),
([w1,w2,w131,w0,w3,w4,w59,w5],dL 0x4e0b740a0f73fe0354093391b3408040147091,dS 0x1210150c1a0e2c082a2b16051c292201020409,pH 0x1734142122212218855551111191 13 19),
([w190,w1,w2,w0,w3,w4,w59,w5],dL 0x4e0864124010354021b940f40e182040091,dS 0x19150c080626110e09100204220f12,pH 0x1524143133285661111113133169 12 15),
([w1,w2,w0,w3,w4,w15,w87],dL 0x861a41a13c20941a23791a3091,dS 0x3b10121c0c2c2b052226150e08090204,pH 0x127312612841244121117 9 16),
([w231,w86,w1,w0,w3,w4,w5],dL 0x415040035414091,dS 0x101c111a0e152b05222c2a3501120902080a04,pH 0x252425111133331111111 5 19),
([w231,w1,w2,w131,w0,w3,w4,w5],dL 0x4184161b3417040411091,dS 0x12101c0637080129093b0f3d,pH 0x4662222221555551111111111111 7 12),
([w86,w1,w2,w69,w0,w3,w4,w5],dL 0x4190351e741b41d41c41a04e040,dS 0x1c1e08030a1b1017040112,pH 0x3131341312136611322121322119 9 11),
([w76,w86,w1,w2,w0,w3,w4,w5],dL 0x3542022842104041f04e,dS 0x123b1c35170413240110,pH 0x1112221162111211112112221222 7 10),
([w2,w150,w0,w3,w4,w15,w5],dL 0x3213c24234220a8091,dS 0x13191c0c111a2b052236261b3c0e1508020904,pH 0x131413513411111212221 6 19),
([w1,w2,w0,w3,w15,w232,w5],dL 0x4271cc3c242603e0a8035,dS 0x10121a110c0e2c092b540105221c3715080402,pH 0x316431531422222111166 7 19),
([w1,w2,w0,w3,w4,w665,w5],dL 0x300f1ce1cc3c20a8379091,dS 0x3b1910121a112c010522261c0e08023c150904,pH 0x122212412631333111115 8 19),
([w233,w1,w2,w0,w3,w4,w5],dL 0x42a4283c24290430350a8,dS 0x132f110c150e0a041b1c1a09083c02,pH 0x454547111124221262216 7 15),
([w1,w2,w0,w3,w4,w666,w5],dL 0x300f43412f3c2433379094091,dS 0x3b10121c112c010526190e080915060204,pH 0x132313513741444111116 9 17),
([w1,w667,w2,w0,w3,w4,w5],dL 0x437438043094436435040035,dS 0x10150e0a090526121108020406,pH 0x424248145513665333333 8 13),
([w1,w2,w0,w668,w3,w4,w15,w5],dL 0x2ba0d343b29f43904343a0b12b8094035,dS 0x131b202b052238110c260e10090b04,pH 0x1358132232443412232447357771 11 15),
([w1,w2,w131,w3,w4,w333,w5],dL 0x3543d43f03e43e0b1091,dS 0x3717020a2b0105223d100e0d0b030c04,pH 0x154313212271532111116 7 16),
([w1,w2,w0,w3,w4,w15,w669],dL 0x3c24423f23d64410350b234d091,dS 0x3b1310110d0a09022b0522260f2f080b0c04,pH 0x125612312341247121115 9 18),
([w334,w190,w1,w2,w3,w4,w5],dL 0x354454440b2091,dS 0x13020a112b05261701190656100d0e0c3d040b,pH 0x343534111122221111111 5 19),
([w1,w2,w670,w0,w3,w4,w15,w5],dL 0xf44481b93f73540943d64470430b2446035351,dS 0x13121c1a152c2b0526110b0c22020e102a04,pH 0x2137214414821c22b11443133331 13 18),
([w2,w0,w149,w3,w4,w15,w5],dL 0x3c203544a44b0b1091,dS 0x61113190f2b0d0a08260910040c0e0b,pH 0x131414121122222513412 6 16),
([w1,w2,w0,w120,w3,w4,w15,w5],dL 0x4344d0b144c040094,dS 0x3b120f1f112b05221b260c10040a,pH 0x2315531111443411111411311111 6 14),
([w1,w2,w0,w3,w15,w129,w5],dL 0x9420d3c244f0b107d,dS 0xf18120e0b2b54010522261b081911100c04,pH 0x115311211241132111115 6 18),
([w1,w2,w0,w3,w4,w671,w5],dL 0x3c245020d44b3790350b1091,dS 0x3b3510112f0d0a09020105260f06080c0b04,pH 0x154415212231332111116 8 18),
([w234,w1,w2,w0,w3,w4,w5],dL 0x4534514520430b1040,dS 0x1f080e1005261b0c0b1206,pH 0x414222146234323353235 6 11),
([w1,w2,w335,w0,w3,w4,w15,w5],dL 0x4322145c0b20403c245b094,dS 0x3b101b022b0522151126120c360424,pH 0x3273625525111111111111211171 8 15),
([w1,w2,w0,w3,w4,w672,w5],dL 0x3c246045e22c3d645f0350b2091,dS 0x3b131910110d0a0902010522260f2f160b080c04,pH 0x141514212231337111116 9 20),
([w1,w2,w673,w0,w3,w4,w5],dL 0x4634624613d60b2040043,dS 0x21203b0e0b0c22261c101604,pH 0x121213151121761111115 7 12),
([w1,w2,w0,w3,w4,w15,w674,w5],dL 0x4690b20b129f468466043094467035,dS 0x132f3b12110c2b0522361510260e0d2c1a0b04,pH 0x1112257312131213432335525111 10 19),
([w1,w675,w2,w108,w0,w3,w4,w5],dL 0x15846f46d46b11511446e46c137096,dS 0x1b0e21152b050c01191c3538044032,pH 0x5443331113111323331322222222 10 15),
([w676,w1,w2,w108,w0,w3,w4,w5],dL 0x8646f46c47011b47111a46d177096,dS 0x352105010c19121b370e021504,pH 0x4553331118111122222723331822 10 13),
([w1,w2,w677,w108,w0,w3,w4,w5],dL 0x8615846c46d4740ad4754731a346f0961c9,dS 0xc100d33380b0522211537353c190e043601,pH 0x4343462222243321555111111111 12 18),
([w1,w2,w108,w69,w0,w3,w4,w5],dL 0xcb0960990ad46f4774761fb1e702446c,dS 0x1c1e12150b36332b05030e0c3504193801,pH 0x4647117118343113331122222222 11 17),
([w76,w1,w2,w108,w0,w3,w4,w5],dL 0x46c09608846f47847922803023046d,dS 0xe2321150c330d193602012b3710,pH 0x2551114254666633333631111463 10 14),
([w1,w678,w2,w0,w3,w4,w5],dL 0x4a0993c83c647b3430cb137,dS 0x191c02072b050c1210350e0432,pH 0x544333222272411111111 8 13),
([w77,w2,w21,w0,w3,w4,w5],dL 0x47d3430cb137099,dS 0x102b05242a08021101320e0d0c35190438,pH 0x151414111233332212222 5 17),
([w1,w2,w0,w679,w3,w4,w5],dL 0x9948248148047f38309409f,dS 0x130d0a3305220e1110340916040b0226,pH 0x766222335122411111111 8 16),
([w77,w147,w1,w2,w0,w3,w5],dL 0x48403e0943830d7,dS 0x180b0a072b0535190c58132f0110040f3811,pH 0x522332111144231111111 5 18),
([w680,w1,w2,w0,w3,w4,w5],dL 0x780994853833e20cb177,dS 0x3519100d0a0911011702040e,pH 0x355444222211111727111 7 12),
([w681,w1,w2,w0,w3,w4,w5],dL 0x3434884870994893eb094095,dS 0x1a372411060e340d02041910,pH 0x344836222611111222111 8 12),
([w1,w2,w682,w0,w3,w4,w5],dL 0x2e00810cb0991c9,dS 0x1c37151136080522041b190e023c0926,pH 0x242425132233331111111 5 16),
([w77,w2,w150,w0,w3,w4,w5],dL 0x47e48b0cb1c9099,dS 0x1c15052236080211013c1b0e37190409,pH 0x141514211133332212222 5 16),
([w683,w1,w2,w0,w3,w4,w5],dL 0x48d47e2e80940b9099,dS 0x1c1915080904060e1b0213,pH 0x141514633322222233322 6 11),
([w1,w2,w0,w684,w3,w4,w5],dL 0x26081343099024,dS 0xd1b12350504100e0c0b190626,pH 0x242132333142523111111 5 13),
([w77,w2,w0,w149,w3,w4,w5],dL 0x47e343490024099,dS 0xd1b122604110135100c0b190e,pH 0x131211414251314212122 5 13),
([w685,w1,w2,w0,w3,w4,w5],dL 0x47e032078030099,dS 0x3b350b04161b100e0c13,pH 0x141333514322222233232 5 10),
([w1,w63,w0,w20,w3,w4,w5],dL 0x7d1ca4940d149249309f096,dS 0x3b1211073c052236100b3d0e0a15040901,pH 0x533111644111121222222 8 17)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p5 : List StD := [
([w50,w1,w63,w0,w3,w4,w5],dL 0x7d1374944964920963e74951ca177,dS 0x121017113005220d090c36041537010e,pH 0x433463253111111222221 10 16),
([w1,w63,w0,w3,w4,w13,w5],dL 0x49449a4994670aa096,dS 0x111012210c352c3c0522370e150904362a01,pH 0x131413513412111222222 6 18),
([w52,w1,w63,w0,w3,w4,w5],dL 0x49446709604349c49b1ca0b4,dS 0x100e122119090c3005223d1311152a36040f01,pH 0x433453213611111222221 8 19),
([w1,w2,w235,w63,w0,w3,w4,w5],dL 0x7d49f49449e3d14a2096492137,dS 0x120e171535533c0511323b1036040c01,pH 0x5442226332222373332111111111 9 16),
([w236,w1,w2,w63,w0,w3,w4,w5],dL 0x7d4924a64a03e74a5494177096,dS 0x10171130050c0112130e153604,pH 0x7443336118111122222223331822 9 13),
([w1,w2,w0,w3,w4,w686,w5],dL 0x300f49a4671080aa096,dS 0x1b1110122135022b060522130e153609042a01,pH 0x141313514311111222222 7 19),
([w151,w1,w2,w63,w0,w3,w4,w5],dL 0x49249449709649c4a946707d0b4,dS 0x120c3005221315103b0f0d0b360104,pH 0x3435347346534611111112222311 9 15),
([w151,w1,w2,w0,w3,w4,w5],dL 0xf00309647349c2c40b403e,dS 0x12191115092b221304103b0f3601,pH 0x131413553522222111122 8 14),
([w1,w2,w63,w0,w3,w4,w49,w5],dL 0xad07a4ab13c0734aa46701a494,dS 0x11153c052212350e0b191017043601,pH 0x1314141311713417134122222222 9 15),
([w58,w1,w2,w63,w0,w3,w4,w5],dL 0x49407e1ca09617c4670744ad4ac020492,dS 0x10300c11170532370e0b3b153601,pH 0x5441113641337322222221111132 11 14),
([w1,w12,w2,w0,w3,w4,w121,w5],dL 0x4303e4b23d14b14b04af1371cd,dS 0x12100c02070b092b050e172a013b045332,pH 0x5524443333111111111112222222 9 17),
([w1,w2,w0,w20,w3,w4,w121,w5],dL 0x3e0cd0433de3da4b44af0d14b51cd4b309409f,dS 0xa072b05221315103d380e010b0904,pH 0x5513332223887342244741111111 13 15),
([w50,w1,w2,w0,w3,w4,w121,w5],dL 0x4303e4b83e74b64b44b71771cd,dS 0x100f0d0c130a3e2b050b02090104120e,pH 0x3325554444111112222221111112 9 16),
([w17,w1,w2,w0,w3,w4,w121,w5],dL 0x1cd0434b403e0943f50f34b94ba0954af,dS 0x103d2a02133e2b050c010e0b211522,pH 0x3324441111563412222221111112 11 15),
([w1,w2,w0,w3,w121,w13,w5],dL 0x4b41cd49a4bc0940aa03e,dS 0x1012210c350e2c02392b0522370904152a1301,pH 0x112411511433136222222 7 19),
([w687,w1,w2,w0,w3,w4,w5],dL 0x1cd00f0034be4bd2d70ae096,dS 0xe12213515022b2209010a130410,pH 0x433543111122222121112 8 14),
([w1,w2,w0,w3,w121,w49,w5],dL 0x944af03e0734bf01a4b4,dS 0xf0c272102350e0b2b052212131917100401,pH 0x152313111141536222222 7 18),
([w1,w2,w336,w0,w3,w4,w5],dL 0x3e3c815847b4c01ca3d1137,dS 0x3b0d1713112a020730050c0e120832041001,pH 0x225244265123331111111 8 18),
([w688,w1,w2,w0,w3,w4,w5],dL 0x3e4c64c43d94c50d148109409f,dS 0x120e0b1522090d1104011b10,pH 0x433453222511111222111 9 12),
([w1,w689,w2,w0,w3,w4,w5],dL 0x3e4c90783e74854c41ca177,dS 0x3b12100f0d17093c05221336040e01,pH 0x544333222226611111111 8 15),
([w1,w690,w2,w0,w3,w4,w5],dL 0xf34cc4cb4890940950f7,dS 0x1c120e0b050d100106,pH 0x744114333333322222222 7 9),
([w691,w1,w2,w0,w3,w4,w5],dL 0x49a1084cf09410a0aa,dS 0x10121c35150911130e050601,pH 0x454645343311111313311 6 12),
([w79,w88,w2,w0,w3,w4,w5],dL 0x4d14d01ae0aa094,dS 0x1012211a152a091b30052b0e160622133601,pH 0x334345111132222121122 5 18),
([w1,w692,w2,w0,w3,w4,w5],dL 0xf00349c2c41ca07d0b4,dS 0x10122119152a093c05223613040f01,pH 0x242524333331221111111 7 15),
([w693,w1,w2,w0,w3,w4,w5],dL 0x7301e07801a07a,dS 0x1b123516050d110c100e011304,pH 0x141333514322222323232 5 13),
([w1,w694,w2,w0,w3,w4,w5],dL 0x7402207d02007e,dS 0x1c120b130c100e050d0106,pH 0x343131534132323222222 5 11),
([w2,w21,w0,w3,w4,w5,w81],dL 0x994d84d74d60bc0b8091,dS 0x1235111b100f17302b16242a020d083c0e0c3806,pH 0x614155133311111122221 7 20),
([w695,w1,w2,w0,w3,w4,w5],dL 0x4db4dc4da4dd0350bc0b8081,dS 0x100f0c2409060e080b02320d,pH 0x117333222244432644326 8 12),
([w1,w2,w0,w696,w3,w4,w5],dL 0x1734e03da0810941710bd035,dS 0x1e3d0a0905190e0c083c0b3804,pH 0x557358222244444333233 8 13),
([w1,w2,w0,w697,w3,w4,w5],dL 0x4e34e04e40814e20bd0350b8,dS 0x1b12100f0c0a0926160e0b08010d0638,pH 0x556422333311111224144 8 16),
([w1,w2,w698,w0,w3,w4,w5],dL 0x4e94e84e70880810944e60bc035,dS 0xf1c24163c0c0e0908220b0206,pH 0x558222358244444333333 9 13),
([w1,w699,w2,w0,w3,w4,w5],dL 0x2aa47b4ef1df3cc137,dS 0x72b172a11160e400632,pH 0x655444333336511111111 6 10),
([w132,w2,w21,w0,w3,w4,w5],dL 0x1ca4f14ef1df1373c8,dS 0x122a071b3b0e0832191140,pH 0x155444115233332122222 6 11),
([w1,w2,w0,w700,w3,w4,w5],dL 0x4814f44f34f23da09409f,dS 0x13103d0a3305060e1134090b02043c,pH 0x377222446122511111111 7 15),
([w701,w1,w2,w0,w3,w4,w5],dL 0x784854f21df1773e6,dS 0x130c0910060211010e,pH 0x155444333322222366222 6 9),
([w702,w1,w2,w0,w3,w4,w5],dL 0xf54f94f84f74890940950f7,dS 0x121c100e3d0b220215163406,pH 0x744114333322222333222 8 12),
([w1,w2,w0,w3,w4,w703,w5],dL 0x4fe4fd1410cf094247096,dS 0x111c371915020601052212240e0904,pH 0x124212212711111313336 7 15),
([w704,w1,w2,w0,w3,w4,w5],dL 0x1dd1db37903503e04e,dS 0x1215190e24040a013b,pH 0x212126323332333222225 6 9),
([w1,w2,w146,w0,w3,w4,w49,w5],dL 0x2fa0cf13c50050104e4fc5035020734ff099,dS 0x2c3c052212350b0e10241a17010a04,pH 0x3383453184341589911111121111 12 15),
([w58,w1,w2,w146,w0,w3,w4,w5],dL 0x50417c38b5055010cf04e,dS 0xe0b37112c0219321c0a2404151201,pH 0x1113331113112321113113331657 7 15),
([w1,w2,w0,w20,w3,w4,w189,w5],dL 0xce50903e3020d125050a0cf508035,dS 0x121b0a072b053d371001380e0b0904,pH 0x3314442222222211111921111221 10 15),
([w17,w1,w2,w0,w3,w4,w189,w5],dL 0xf103e24050825c0350f350b50c5090cf,dS 0x100e2a080b121c01191522,pH 0x7364442222113421334212222627 11 11),
([w705,w1,w2,w0,w3,w4,w5],dL 0xf0032b14be141094235096,dS 0x1c3738020522090e011b04191e,pH 0x244524111133331111116 8 13),
([w1,w2,w706,w0,w3,w4,w5],dL 0x5110cf51050f0850c40350c2,dS 0x1b0e0f2a08052f183b010a0c0d0204,pH 0x448333522311111625515 8 15),
([w707,w1,w2,w0,w3,w4,w5],dL 0x940861765155131745145160d10c5085,dS 0x200924160b010a0e0410,pH 0x334222354231121219256 11 10),
([w48,w1,w2,w0,w20,w3,w4,w29],dL 0x30251b25008530051851a0d60d1519,dS 0x1310370705093b190138211b0e0b1e0412,pH 0x2343113116354913541112222222 10 17),
([w708,w1,w2,w0,w3,w4,w5],dL 0x51e50151d51651c0350c50c2085,dS 0x1b0e010f24120418090a0c,pH 0x119333222244432544825 9 11),
([w709,w1,w2,w0,w3,w4,w5],dL 0x3f052452352152052204e5250f30c4085,dS 0x15350a06030b100201110e,pH 0x33422235423112671a267 11 11),
([w17,w48,w1,w2,w0,w3,w4,w29],dL 0x30251950c25c0f55273000f351b,dS 0x373e0b053b1e0e01021c1921121522,pH 0x2441115741333162221251113111 9 15),
([w710,w1,w2,w0,w3,w4,w5],dL 0x5251a809449a1a503552a040085,dS 0x150e051b123509240a0106,pH 0x313138134413111531145 9 11),
([w79,w48,w2,w0,w3,w4,w5],dL 0x52c52b094091282,dS 0x1c1b2a05221a0e1509160406372c01,pH 0x111115113332222222222 5 15),
([w711,w1,w2,w0,w3,w4,w5],dL 0x52f52e52d4fc5250350c2085,dS 0x1b19150111243b040e090a,pH 0x114158222233332633326 8 11),
([w712,w1,w2,w0,w3,w4,w5],dL 0x5375365355385160860c5085,dS 0x19351716050e10040b01,pH 0x114222158211121611216 8 10),
([w226,w48,w1,w2,w0,w3,w4,w5],dL 0x53908550c53b0c553a094,dS 0x1b05060c090e1e150118241904,pH 0x2242332111211111222222111117 7 13),
([w713,w1,w2,w0,w3,w4,w5],dL 0x53e53d53c5250c4040085,dS 0x19370e0b05041017061101,pH 0x112333127311131511315 7 11),
([w48,w1,w2,w187,w0,w3,w4,w5],dL 0x5405415390855420c451853f094,dS 0xe101b05030138110437181e0a,pH 0x2252442118211142111111222222 9 13),
([w188,w48,w1,w2,w0,w3,w4],dL 0x2b15395475464be094,dS 0x193805223b06090e13021c121e0401211b,pH 0x343111111122222211155 6 17),
([w714,w1,w2,w0,w3,w4,w5],dL 0x37954a0915493430cb03e099,dS 0x100e2408072b050c0d020432,pH 0x272444333312143262555 8 12),
([w1,w2,w715,w21,w0,w3,w4,w5],dL 0x4d854b09954c4c00911ca4d6,dS 0x132a073602320c08120e100d19,pH 0x1151441337311182222221377222 8 13),
([w716,w1,w2,w21,w0,w3,w4,w5],dL 0x54f4d654d54e4ef1df099,dS 0x100d12242a0740341102190c13320e,pH 0x1443336145222222143221743622 7 15),
([w1,w2,w21,w0,w3,w4,w5,w29],dL 0x995512325500123c60074d8,dS 0x110f2a0713100d021219320e0c08,pH 0x3335554444163542222226635422 8 14),
([w26,w1,w2,w21,w0,w3,w4,w5],dL 0x3e55455355501500c4d63c8099,dS 0x120c071311350e32,pH 0x3313153117314473111411233337 9 8),
([w717,w1,w2,w0,w3,w4,w5],dL 0x4055913d5580ff09107d,dS 0x13101b0e2f0d0c240819040b0935,pH 0x151444333322222222222 7 14),
([w1,w2,w0,w3,w227,w5,w29],dL 0x7d55b55c55a01200703e,dS 0x1b280f1213190c010e100d080b02,pH 0x521444333322222161432 7 14)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p6 : List StD := [
([w718,w1,w2,w0,w3,w4,w5],dL 0x55e0010cf55f4dd0122aa,dS 0xe2a07130506111219010f24020c,pH 0x113122111114551111111 7 14),
([w1,w2,w0,w3,w4,w719,w5],dL 0x56209937803e482385383377094091,dS 0xe170a052226100d2a160b0204,pH 0x261826444422255333333 10 13),
([w110,w1,w2,w0,w3,w4,w5,w29],dL 0x37c0945630085640cf,dS 0x110f34191312090b020e,pH 0x1114413333111131111311111363 6 10),
([w26,w110,w1,w2,w0,w3,w4,w5],dL 0x39430756600d0cf5653d9,dS 0x121b1311350b09020e,pH 0x2212142134213432134742122222 7 9),
([w147,w1,w2,w0,w3,w13,w5],dL 0x10356903e094,dS 0x1310180b2c0a090504391537352a06110f01,pH 0x232423111112111222222 4 18),
([w1,w2,w0,w20,w3,w4,w97,w5],dL 0x56f0d156e2aa56d007132094,dS 0xf131002070605380e093d010b04,pH 0x3614442222222231111121111221 8 14),
([w1,w720,w2,w0,w3,w4,w5],dL 0x57217009426f57109107d,dS 0x13100e2f170a2a195804110b01020d06,pH 0x161313414322222222222 7 16),
([w118,w1,w2,w0,w20,w3,w4,w5],dL 0x43930203407d3725760d6518575035,dS 0x111b10011909380b0e,pH 0x4454224228411664111119111a84 10 9),
([w1,w2,w0,w133,w3,w4,w5],dL 0x910015772cd2343050d6579008,dS 0x370602081b1219340111100b0e,pH 0x244114111132461554567 9 13),
([w721,w1,w2,w0,w3,w4,w5],dL 0x56257d09157c3830cb03e099,dS 0x100e0a2a2b050c0d010204,pH 0x272444333312143262555 8 11),
([w1,w182,w2,w0,w3,w4,w5,w29],dL 0x9907858257f5802323e257e008581007,dS 0x213c101526190d0912130e010c02,pH 0x5754443333111116754316614311 11 14),
([w26,w1,w182,w2,w0,w3,w4,w5],dL 0x55458358400d00c5804c9099,dS 0x1202152604133c35110e01,pH 0x3313153144311773111111233387 8 11),
([w722,w1,w2,w0,w3,w4,w5],dL 0x57217d5710ff09107d,dS 0x100e0d0c0a2a19012f090b37,pH 0x151444333322222222222 6 12),
([w26,w1,w2,w0,w3,w229,w5],dL 0x5883e000d58700c07d03e,dS 0x25110d090a0e0b01370610,pH 0x141515313321222111111 7 11),
([w1,w2,w0,w723,w3,w4,w5],dL 0x13bb58b0cf3050080072aa,dS 0x111713190d09050812010c020e,pH 0x114221333322222155172 8 13),
([w724,w1,w2,w0,w3,w4,w5],dL 0x37958e09130f34309403e099,dS 0x100e2417080604020d,pH 0x272424323332333262255 8 9),
([w1,w83,w2,w0,w3,w4,w5,w29],dL 0x9509458f0cf012590099,dS 0x11340215121337220b0e0806,pH 0x1115513333441431111311111313 7 12),
([w26,w1,w83,w2,w0,w3,w4,w5],dL 0x55425f5920150cf4f9591099,dS 0x12150701130611350e0822,pH 0x3313153144311773111111233387 8 11),
([w725,w1,w2,w0,w3,w4,w5],dL 0x401ee30d26d09455807d091,dS 0x101b0e0d1724042f080b0919,pH 0x262333444511111111111 8 12),
([w1,w2,w0,w3,w183,w13,w5],dL 0x3e59509410201b096,dS 0x1a37350f0b0203100e193d17060105,pH 0x162515312321222414432 6 15),
([w17,w1,w2,w0,w3,w4,w97,w5],dL 0x24013124159a5990070942aa096,dS 0x13090e051906211501,pH 0x4516662256111113333311111111 9 9),
([w1,w2,w726,w0,w3,w4,w5],dL 0x59d59c59e4e90880f7,dS 0x2a381c191310020e0812,pH 0x223111111511111246115 6 10),
([w17,w118,w1,w2,w0,w3,w4,w5],dL 0x7d59f0f550c372035,dS 0x2a09190e1c1224020b15,pH 0x3552221112111211112142221222 6 10),
([w1,w2,w727,w3,w4,w13,w5],dL 0x10a09410833d1030055a30aa,dS 0x35370d2c22100c09160e060b2a03,pH 0x732663443423222111111 8 14),
([w728,w1,w2,w3,w4,w13,w5],dL 0x10a0941083b30111025a40aa,dS 0x35372c0d1005090e0b0c2a0106,pH 0x742664242211111333321 8 13),
([w1,w2,w0,w337,w4,w13,w5],dL 0x235a710a0941081070195a60aa,dS 0x1b1c12152c37350e092a0605,pH 0x632553863543244111111 9 12),
([w729,w1,w2,w0,w3,w4,w13],dL 0x10a09410853906f49a5a80aa,dS 0x3735152a1b0e052c121c090106,pH 0x264746422211111333321 8 13),
([w148,w2,w0,w3,w4,w59,w5],dL 0x10d5a90400aa096,dS 0x19101c0637350e2c08312b052212161509042a01,pH 0x153414315411111222222 5 20),
([w1,w2,w0,w3,w4,w13,w87],dL 0x1a41a149a1410cf1a3094096,dS 0x1110121c35152c2b010522370e092a04,pH 0x134513613813111212227 8 16),
([w338,w79,w2,w0,w3,w4,w5],dL 0x5ae2620aa094040,dS 0x121c0e1505221102092a0116061b,pH 0x414145222223223333323 5 14),
([w1,w2,w0,w3,w97,w13,w5],dL 0x49a03e5b1094007096,dS 0x10122119350e02051337150106,pH 0x122414615421222313332 6 13),
([w1,w2,w339,w3,w4,w340,w5],dL 0x5b45b65b5094102096,dS 0xd273711100f0b2c022a030c0e3d160107170509,pH 0x151414212211111313326 6 20),
([w341,w342,w1,w2,w3,w4,w5],dL 0x5ba0945b9103096,dS 0x370e101d2c2a0605180b02190a59040917010c0d,pH 0x353111434122212111111 5 20),
([w1,w0,w120,w3,w4,w13,w5],dL 0x49a5bc44c094102096,dS 0xa3537112c2a3d0105100e060b040934,pH 0x141514121122222313312 6 16),
([w1,w2,w0,w3,w13,w129,w5],dL 0x8349a5be10220e07d,dS 0x181235390e0b05100c2a041b060901,pH 0x112411311322122111112 6 15),
([w1,w2,w0,w3,w4,w730,w5],dL 0x49a20e14144c03e102094096,dS 0x1b110e18021605100b0a2a060c0409,pH 0x154615313311111212227 8 15),
([w731,w1,w2,w0,w3,w4,w5],dL 0x1020cf04010a,dS 0x1b0d0b0c050635192a01120a,pH 0x121214111121331111111 4 12),
([w1,w2,w0,w3,w4,w732,w5],dL 0x49a5c022d14145b03e094103096,dS 0x1b111018022415060105340b3609,pH 0x154615212211111313387 9 14),
([w1,w2,w733,w0,w3,w4,w5],dL 0x5c25c131a10304010a,dS 0x1b0b090e0d211036,pH 0x121213151111111214615 6 8),
([w1,w2,w0,w734,w3,w4,w5],dL 0x5c92bb02501f,dS 0x101b0f1f0b052f0c2a090406190a01,pH 0x111211113222222111112 4 15),
([w52,w1,w0,w120,w3,w4,w5],dL 0x7a5cb2bb02501f,dS 0x60503351911100c040a3b0f01,pH 0x111214113211111212222 5 13),
([w735,w1,w2,w0,w3,w4,w5],dL 0x45b30e0880f7,dS 0x1c191036113b3d0b0e09,pH 0x223111111124311111111 4 10),
([w736,w1,w2,w0,w3,w4,w5],dL 0x5cf47e3790915ce0cb03e099,dS 0x10121c150e2c08090522023c04,pH 0x262728333312113252244 8 13),
([w737,w1,w2,w0,w3,w4,w5],dL 0x1ce5d113e0ff09107d,dS 0x10121c1a0e2c08021904153709,pH 0x141516333322222222222 6 13),
([w1,w2,w0,w3,w232,w49,w5],dL 0x735d35d401b07d427,dS 0x1b1a10180c27172c061905080f0b0102,pH 0x123412111133333212253 6 16),
([w738,w1,w2,w0,w3,w4,w5],dL 0x7332707a0f7,dS 0x24211b1a020b3d100e0937,pH 0x232111111142311111111 4 11),
([w1,w2,w739,w0,w3,w4,w5],dL 0xcf01f5d62c602104007e,dS 0x21101b1d0a0601050e0b0802,pH 0x121111131333333215113 7 12),
([w740,w1,w2,w0,w3,w4,w5],dL 0x5e047e3790915df09403e099,dS 0x10121c150e2c0908060402,pH 0x262728323332333252244 8 11),
([w741,w1,w2,w0,w3,w4,w5],dL 0x4345d113e03409409107d,dS 0x10121c110e2c080415020919,pH 0x151617333322222222222 7 12),
([w1,w2,w742,w0,w3,w4,w97,w5],dL 0x1325e32aa13107d,dS 0x3b28110c2c050f211909021e06010408,pH 0x1113112222222213113221111221 5 16),
([w743,w1,w2,w0,w3,w4,w97,w5],dL 0x1315e41322aa07d,dS 0x3b281a0c21050f021304120e2a01,pH 0x1112113333211231111313333133 5 14),
([w1,w744,w2,w0,w3,w4,w5],dL 0x5e63350862aa,dS 0x24091b19130d0e1008020b,pH 0x113122111111111143211 4 11),
([w745,w1,w2,w0,w3,w4,w5],dL 0x5e701f1350402aa,dS 0x2f1708050e0b021c12010d110a,pH 0x112123111112531111111 5 13),
([w1,w2,w746,w0,w3,w4,w5],dL 0x1413785ea26d376035248377091096,dS 0x13100e1126322f0a09170d2a0116,pH 0x696444111111172333333 10 14),
([w1,w747,w2,w0,w3,w4,w5],dL 0x29e5ed5ec29c0963eb283094091,dS 0x13100e2f0d172402050111060b0408,pH 0x484333222311111111111 9 15),
([w748,w1,w2,w0,w3,w4,w5],dL 0x14158e30f30c091094251096035,dS 0x13100e112f0117060d,pH 0x686333222211132222257 9 9),
([w749,w1,w2,w0,w3,w4,w5],dL 0x29f3d91f01ef09648228a091094,dS 0x13101b0e2f0d170133110b0a,pH 0x474333111322222222222 9 12),
([w1,w2,w750,w187,w0,w3,w4,w5],dL 0x5405f12c657953f094,dS 0xe0b1b0c020538371e3d11100601040a,pH 0x2252442111122222111122111121 6 16),
([w751,w1,w2,w0,w3,w4,w5],dL 0x24d5f55f4141091094251096035,dS 0x1b12100e0b0f0c01060d,pH 0x968333222211132222257 9 10),
([w752,w1,w2,w0,w3,w4,w5],dL 0x5f603509147e37934303e099,dS 0x100d0a12080e0b0526020c0604,pH 0x242323727312111262228 8 13),
([w753,w1,w2,w0,w3,w4,w5],dL 0x1f90962880991fc03528a091094,dS 0x12101b0e2f0d33010f0c0b0a,pH 0x655333111322222222222 9 12),
([w343,w1,w2,w0,w120,w3,w4,w5],dL 0x49c5f944c2bb094,dS 0x1b0605033b0f0c120e0b3d100a0104,pH 0x3431112221111211111115143211 5 15),
([w343,w1,w2,w0,w3,w4,w5],dL 0x9649c3792bb5fa07d03e,dS 0xc06050304103b0f013d0a,pH 0x151414313321222171111 7 11),
([w754,w1,w2,w0,w3,w4,w5],dL 0x5d103555809107d,dS 0x121b2f0d0c0a04080b0919,pH 0x151333444422222222222 5 11)]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p7 : List StD := [
([w755,w1,w2,w0,w3,w4,w5],dL 0x20e4be5fc1410942d6096,dS 0xe181b06050309191e0417,pH 0x544222111133331111111 7 11),
([w1,w2,w756,w0,w3,w4,w5],dL 0x24e37e6005012751410352485ff091096,dS 0x121b100e203c05320f0b010d092404,pH 0xa69444111111172333333 11 15),
([w1,w757,w2,w0,w3,w4,w5],dL 0x36e2a72890992a8096283094091,dS 0x1b0e362a02012f0f2216200b0608,pH 0x655333222311111111111 9 14),
([w758,w1,w2,w0,w3,w4,w5],dL 0x24e312607606141091094251096035,dS 0x121b100e200f0b01220d,pH 0x968333222211132222257 10 10),
([w759,w1,w2,w0,w3,w4,w5],dL 0x21809628909921928a091094,dS 0x1b0e36012f0f33200b09,pH 0x544333111322222222222 8 10),
([w760,w1,w2,w0,w3,w4,w5],dL 0x24d60c14109160b248096035,dS 0x1b12100e0b260f0c0d1601,pH 0x867333222211132222454 8 11),
([w761,w1,w2,w0,w3,w4,w5],dL 0x60f60e03509147e56238303e099,dS 0x100a080b0c2226120e021604,pH 0x242323727912111262228 9 12),
([w762,w1,w2,w0,w3,w4,w5],dL 0x221096288099223283091094,dS 0x12101b0e2f0d2c010f0c020b24,pH 0x544333111322222222222 8 13),
([w763,w1,w2,w0,w3,w4,w5],dL 0x9649c30e2fb61107d03e,dS 0x100605043b3d0f0124,pH 0x151414313721222171111 7 9),
([w764,w1,w2,w0,w3,w4,w5],dL 0x5d103557109107d,dS 0x121b2f0d0c0a081904090b37,pH 0x151333444422222222222 5 12),
([w765,w1,w2,w0,w3,w4,w5],dL 0x22d4be614141094340096,dS 0xe120a060913101704,pH 0x544222111133331111111 7 9),
([w1,w2,w766,w0,w3,w4,w5],dL 0x4fe0344fc1410944fd24e091096035,dS 0x1c121915325009110e01,pH 0x44748a222222223415555 10 10),
([w1,w767,w2,w0,w3,w4,w5],dL 0x2b22b10965de2ab094091,dS 0x101c121915360501380e11060408,pH 0x434347222211111111111 7 14)]
noncomputable def ptopD8 : List StD := ptopD8p0 ++ ptopD8p1 ++ ptopD8p2 ++ ptopD8p3 ++ ptopD8p4 ++ ptopD8p5 ++ ptopD8p6 ++ ptopD8p7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x3 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x4 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (4*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x5 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (5*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x6 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (6*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x7 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (7*64)).take 64) = true := by decide +kernel
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopW ptopQ ptopI7 (chunks 64 ptopD8 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  · exact ptopC8x3
  · exact ptopC8x4
  · exact ptopC8x5
  · exact ptopC8x6
  · exact ptopC8x7
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD9p0 : List StD := [
([w1,w2,w68,w3,w4,w5],dL 0x5004003002001,dS 0x131211100f0d0a0906050e0c080b040703,pH 0x544333222211111 5 17),
([w89,w1,w2,w3,w4,w5],dL 0x1101000f002001,dS 0x131211100f0a080d0e050b020c010906,pH 0x544222111133321 5 16),
([w1,w2,w0,w31,w4,w5],dL 0x19018002001,dS 0x100d1c0a05120b19110e1509040614,pH 0x433143222211111 4 15),
([w1,w2,w0,w3,w4,w38,w5],dL 0x4a00300f04003e04304203b03a002001,dS 0x1b0b0a05041c15120e08060926,pH 0x641333864322222111111 11 13),
([w1,w2,w0,w3,w38,w5],dL 0x3a002001,dS 0x100d0b0a05041c12190c110e1508060926,pH 0x133113222211111 3 17),
([w1,w2,w0,w3,w4,w768],dL 0x6c06b00206d001,dS 0x1c120a050619110e1508040930,pH 0x244254333311111 5 13),
([w217,w1,w2,w0,w3,w4],dL 0x6f06e04a002001,dS 0xb191109081b0e150512021c010a06,pH 0x454222111133321 5 15),
([w28,w1,w2,w0,w3,w4,w49,w5],dL 0x6d04200f03b07701b07601f01a,dS 0x1b11100f0e0a0531020112160804,pH 0x3625353663444441111111111111 9 14),
([w58,w28,w1,w2,w0,w3,w4,w5],dL 0x6d00304207603b07f02101f07b020,dS 0x1210083102010c0515061c0a,pH 0x3552324442111111111412222211 10 12),
([w28,w1,w2,w69,w0,w3,w4,w5],dL 0x6a08300308008202501f07b024,dS 0x1f1c0d0831020105191e0a06,pH 0x3552223222444441111111111111 9 12),
([w28,w1,w2,w0,w3,w4,w5,w117],dL 0x4a00f084028076042027,dS 0x12130b1f0905310201110e0804,pH 0x2323553333444441111111111111 7 13),
([w106,w28,w1,w2,w0,w3,w4,w5],dL 0x4a00308702e07b02d042,dS 0x130e2308053102011c0b1a150922,pH 0x1553334443222222222421333322 7 14),
([w76,w28,w1,w2,w0,w3,w4,w5],dL 0x6a08a00f08008903101f076030,dS 0x23310201120d13101624,pH 0x3552224442111111111413222211 9 10),
([w28,w1,w2,w0,w3,w4,w5,w29],dL 0x7607b04a01200808b00703b08c006,dS 0x110c2113190506310201120e15080904,pH 0x3335552235444441111111111111 10 16),
([w26,w28,w1,w2,w0,w3,w4,w5],dL 0x1500d09000c08000b042,dS 0x2512111a1505063102011b130e080904,pH 0x3313153144222222222223133322 7 16),
([w1,w2,w6,w0,w24,w3,w4,w5],dL 0x9e09d09c09b00f00209a094092099093001091,dS 0x1012370d342136330106191511350e02,pH 0x4741113332111115551522221212 13 16),
([w18,w1,w2,w6,w0,w3,w4,w5],dL 0xa60a500309d09e0930020a00940990a40a1001091,dS 0x100e3436073235330d211519,pH 0x5443331111666622222721112112 14 12),
([w1,w2,w6,w0,w3,w4,w15,w5],dL 0x9d0930a10b20b100201f0ad0b30940a90a8001091,dS 0x3b131b121a36333801040e210c151102,pH 0x1426148146111113133322122212 14 16),
([w1,w2,w6,w0,w3,w4,w5,w81],dL 0x930a104a0bd0bc09d00209e0be0940b8099001091,dS 0x1c1b1936333801060e0c11153502,pH 0x2131631736111111444421222212 14 14),
([w48,w1,w2,w6,w0,w3,w4,w5],dL 0x6a0c50c40a109309e0020c20940990c309d001091,dS 0x1b1c1136353338023c0e181e19,pH 0x3343541111666622222722111112 14 13),
([w1,w2,w6,w0,w20,w3,w4,w5],dL 0x9e09d0d60d100100f09f0c90c8002093094,dS 0xe1b3d023c260b211915110110,pH 0x5442222223111223331361112636 12 13),
([w17,w1,w2,w6,w0,w3,w4,w5],dL 0xf50f300309d09e0930020010950ef0ea0940a1096,dS 0x110e3d3e3c260304311c0c380b211002011915,pH 0x5442221111111163333311112116 14 19),
([w1,w2,w6,w0,w3,w4,w13,w5],dL 0x1031020010ad01f0cf0aa0a90fd002094,dS 0xe120c023c2632373521151001,pH 0x1423137143151112122251111525 11 13),
([w1,w6,w0,w3,w4,w13,w5],dL 0xcf0020ad01f0a90fd0aa099,dS 0x1b12382c090c3c312632371521352a020e1001,pH 0x547333554312431222227 8 19),
([w52,w1,w6,w0,w3,w4,w5],dL 0xad01f1200b40a9035002,dS 0x122c090c3c32363533380801112115192a0e100226,pH 0x353635235244441111114 7 21),
([w1,w2,w6,w0,w3,w4,w5,w80],dL 0x930a112b12a12904a0010bf1260020ad094,dS 0xe3b12023c26320c1011191501,pH 0x3121441224111111333351111535 12 13),
([w64,w1,w2,w6,w0,w3,w4,w5],dL 0x6a1361350a109309e0020010b901f13412e09d094096,dS 0x2f0c3830263204311b0d36123b191513020110,pH 0x3343541111111172222213111117 15 19),
([w1,w2,w32,w6,w0,w3,w4,w5],dL 0x8809909d09e0931140961111381370a1091,dS 0x18171536113c263121191c4038320c350e100201,pH 0x7442241141224125545353333533 12 20),
([w1,w2,w6,w0,w134,w3,w4,w5],dL 0x9e09d0a90861620a103509209f099093096161091,dS 0x110d0c2115383c2632310b1910020e01,pH 0x5221114424111913323761111676 14 16),
([w40,w1,w2,w6,w0,w3,w4,w5],dL 0x8609909d09e0a111a09611d177178093091,dS 0x1817211536353c26311902010c12101138320e,pH 0x7332221131553544414542221854 12 19),
([w155,w1,w2,w6,w0,w3,w4,w5],dL 0x8809d09e0930991980a1096091,dS 0x11100e3602083c0104310c0d0b211915,pH 0x5443331111222221111111111111 9 16),
([w1,w2,w6,w0,w3,w4,w59,w5],dL 0x9d0930a101f0ad0a80aa0960a919b091,dS 0x1319121a36383c263231210c1015110e0201,pH 0x1312128132131114442651111565 11 18),
([w1,w2,w0,w3,w4,w59,w5],dL 0x6a04a00300f1af1a90ad0400a919b0a80960aa091,dS 0x13191b1c0c112c2a2b0522121a1509010e0204,pH 0x766555716543444212222 14 19),
([w47,w1,w2,w6,w0,w3,w4,w5],dL 0x9d0930a107d01f0960910b40ad1c20cb0a9099,dS 0xc1b38323101211510020b1912260e,pH 0x242524171133336121133171a266 13 15),
([w47,w1,w2,w0,w3,w4,w5],dL 0x4a00300f04003e0ad0cb1c20990b40a9,dS 0x1c15052201111910090b020e121b0f04,pH 0x141614515522222717722 11 16),
([w1,w2,w119,w6,w0,w3,w4,w5],dL 0x860a109309e01f1a30961ca1cb1c909d091,dS 0x190c38263231151311363c210d350e020110,pH 0x2442841841124225545353333533 12 18),
([w1,w2,w6,w0,w3,w4,w5,w222],dL 0xa90930a11da09d0880350b80bf09e0990961d9091,dS 0x211c1210383c26323111190c15020e01,pH 0x5141221542a11113332761111676 14 16),
([w98,w1,w2,w6,w0,w3,w4,w5],dL 0x880a109309d0961df1de0ad1e009109e,dS 0xc353832312115100201190b363c110e,pH 0x1131432432673655525652111865 11 16),
([w221,w1,w2,w6,w0,w3,w4,w5],dL 0x860a109309e09d0991e8096091,dS 0x1c111b38020832010431210e1218191e,pH 0x4335431111222221111111111111 9 16),
([w1,w2,w6,w0,w3,w4,w49,w5],dL 0x9d09601f0ad0a901b1e909901a093,dS 0x11211517353c2631191b120b1a0e021001,pH 0x1614141311716415554522222252 10 17),
([w58,w1,w2,w6,w0,w3,w4,w5],dL 0x9d09309601f0a90ad0210201f50990a1,dS 0x21172631370e12320b101138011c15,pH 0x7331116731523144424541112114 11 15),
([w1,w2,w6,w69,w0,w3,w4,w5],dL 0x6a0020960010911fb01f02509d1f80240a1,dS 0x1f1c1e0d150c353c26311912110e0b021b103401,pH 0x4331114111463115531522222252 12 20),
([w1,w2,w6,w0,w3,w4,w5,w117],dL 0x960910282110270930ad,dS 0x120b1f2115183b353d31021c190d100e1101,pH 0x1212442222211425114233333353 7 18),
([w106,w1,w2,w6,w0,w3,w4,w5],dL 0x4a09609102e02d2200a10ad,dS 0x231812353d311c0b0e1038321b190d011a15,pH 0x1332221132113244434541222224 8 18),
([w76,w1,w2,w6,w0,w3,w4,w5],dL 0xa109609123009d01f03122b030093,dS 0x2319150c3b3526310d210b3c0e361c34130110,pH 0x6331116731443122222421111112 10 19),
([w1,w2,w6,w0,w3,w4,w5,w29],dL 0x930a10080120960a900723100609909e,dS 0x1137383c323121190c0b261512130e100201,pH 0x2664441164216425554533333353 11 18),
([w26,w1,w2,w6,w0,w3,w4,w5],dL 0xd01500c23709900b09d0ad,dS 0x25120c38263231133c15350b020e111001,pH 0x2212152154215632333634122223 8 17),
([w1,w2,w0,w3,w4,w185,w5],dL 0x4a00300f19b04303e0402470a8245244001,dS 0x3b131b1c110a0b2b05221a151209040e0801,pH 0x531222573243444111111 12 18),
([w22,w1,w2,w0,w20,w3,w4,w5],dL 0x24e24d07d0d10d600f24a24900224809f,dS 0x13123d083c2638040a091b0e0b011110,pH 0x5442222223333331111111111111 11 16),
([w22,w17,w1,w2,w0,w3,w4,w5],dL 0x24d24e07d0f30f5003259258251096095,dS 0x120e3d24443c03471c0c091b02040b2a2619151110,pH 0x5443332222111112223211111211 11 21),
([w22,w1,w2,w0,w3,w4,w13,w5],dL 0x19b0fd26409601f2450020aa0cf,dS 0x101c37350e152c2604122a0109,pH 0x1137115117343332222222222222 9 13),
([w22,w1,w2,w0,w3,w4,w5,w80],dL 0x24825112912a04a2650020bf247,dS 0xe0c3b082c0a320d360412241915011011,pH 0x3114441114333332222222222222 9 17),
([w22,w64,w1,w2,w0,w3,w4,w5],dL 0x25124806a13513626801f26924d0960b9,dS 0x123b19154c0908300132471b0a0204130d1110,pH 0x3343542222111113222211111211 11 19),
([w22,w1,w2,w0,w3,w4,w49,w5],dL 0x9624700f25101b09324526c24801f01a,dS 0xe0b470412081a011b10,pH 0x3584443554235431111111111111 11 10),
([w58,w22,w1,w2,w0,w3,w4,w5],dL 0x30a124724809602127001f020251,dS 0x1d370e0b470c120a111032151c,pH 0x3441113341222222222251111122 10 13),
([w22,w1,w2,w69,w0,w3,w4,w5],dL 0x960a102527125101f024,dS 0x1f1c1e0d12350e0b0a470104191b111034,pH 0x2443332333224331111111111111 7 17),
([w22,w1,w2,w0,w3,w4,w5,w117],dL 0x96028093251248274027247,dS 0x130b1f083b353d3247040d011c0e1011,pH 0x5113334113111352222222222222 8 16),
([w106,w22,w1,w2,w0,w3,w4,w5],dL 0xa109602e27825102d247,dS 0x23353d471c0b09120e100d1b15321a,pH 0x1443331143222222222251333322 7 15),
([w76,w22,w1,w2,w0,w3,w4,w5],dL 0x9309603127a24803001f,dS 0x233b0e0b47120d2435343c1c1310,pH 0x1443331143222222222251333322 7 14),
([w22,w1,w2,w0,w3,w4,w5,w29],dL 0x24825109604a01200823100727b24524e006,dS 0x110c211937090b32470d0415120e08011310,pH 0x3334442234223451111111111111 12 18),
([w26,w22,w1,w2,w0,w3,w4,w5],dL 0x1500d23700c27d24d00b247,dS 0x251215090b0832470d041b13350e011110,pH 0x3313143145222222222223133322 8 17),
([w1,w2,w0,w3,w4,w329,w5],dL 0x4a00300f19b04003e2822810aa280099002,dS 0x1b2c2a051c123735150e06090204,pH 0x231553823511111424444 12 14),
([w10,w1,w2,w0,w24,w3,w4,w5],dL 0x28928809b09c00f092099284283001091,dS 0x10341136043237020d12350e,pH 0x5441113332654132221221111122 11 12),
([w10,w18,w1,w2,w0,w3,w4,w5],dL 0x2882890a50a600309928b28a0a0091,dS 0x1310340d02360716044347210b06120801150e35,pH 0x5443332222111111113111111211 10 20)]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p1 : List StD := [
([w10,w1,w2,w0,w3,w4,w15,w5],dL 0x28828328a19b0b10b201f0a828228e280001091,dS 0x3b131b1c0c1102380b261a15120e,pH 0x1324145134513462322221111122 13 14),
([w10,w1,w2,w0,w3,w4,w5,w81],dL 0x28328a0bc0bd04a0b8289099292001091,dS 0x1c1b111502043c380b350e,pH 0x2141331543154361222221111122 11 11),
([w10,w48,w1,w2,w0,w3,w4,w5],dL 0x28a28306a0c40c52960992972880c2091,dS 0x1b1c113602384b2204471218060b0801191e350e,pH 0x3343542222111113111111111211 11 20),
([w10,w1,w0,w3,w4,w13,w5],dL 0x3b01f09410a0fd28229a0990aa280002,dS 0x1b38052c1c12023735152a0e060904,pH 0x821552a82533233111111 11 15),
([w10,w1,w2,w0,w3,w4,w49,w5],dL 0x28801a28a09309928201f28029b28301b,dS 0x190f1a0547081b16040212350e0b,pH 0x2493332493111115243211111111 11 14),
([w58,w10,w1,w2,w0,w3,w4,w5],dL 0xa128828301f2820992800202a128a021,dS 0x1b471105120b1c150e380637,pH 0x5332221111656211111412226121 11 12),
([w10,w1,w2,w69,w0,w3,w4,w5],dL 0x240910a12a301f2882a228a025,dS 0x1f1c191e0d04114702081b06103435120e0b,pH 0x4332224222111114532211111111 9 18),
([w10,w1,w2,w0,w3,w4,w5,w117],dL 0x9102709328a2832a6028282,dS 0x130b1f041c100d470802113b3d350e,pH 0x5113334113222221113522222222 8 15),
([w106,w10,w1,w2,w0,w3,w4,w5],dL 0xa109102d2ac28a02e282,dS 0x23100d471c0b221b3d12350e1a1538,pH 0x1443332222114322222521333232 7 15),
([w76,w10,w1,w2,w0,w3,w4,w5],dL 0x9328a09101f2af0302882ad031283,dS 0x21231c04470d343513163b0b0e3610,pH 0x4331112222453122222521111212 10 15),
([w10,w1,w2,w0,w3,w4,w5,w29],dL 0x28328a0010120082310990062b0280289007,dS 0x110c211938130506470b0815040237120e,pH 0x3334442234111112234511111111 12 17),
([w26,w10,w1,w2,w0,w3,w4,w5],dL 0x1500d23709900b2b628800c282,dS 0x25121538050604470b081b131102350e,pH 0x3313142222314522222223133232 9 16),
([w1,w2,w75,w0,w3,w4,w5],dL 0x6a04a2b82b709600f111001,dS 0x13181605321b121135380c04100e0b01,pH 0x655333445222221111111 8 16),
([w1,w2,w0,w3,w4,w224,w5],dL 0x4a00204003e0432d52d32d200f001,dS 0x1c021605221b1a090c0b1210040e01,pH 0x641333222286432111111 10 15),
([w53,w1,w2,w0,w3,w4,w13,w5],dL 0x2d50022d32dc10209401f0aa,dS 0x1211100c0916030d0604011c40,pH 0x3625354344366331111111111111 8 13),
([w52,w53,w1,w2,w0,w3,w4,w5],dL 0x2d52d32de2bb01f1110b4,dS 0x1210030d0635021c1a3b0f01403d,pH 0x6554442622111111114112222211 7 14),
([w53,w1,w100,w2,w0,w3,w4,w5],dL 0x2e12c611101f1c9,dS 0x4a123d0a033c0d0637511c1a4038,pH 0x2554443333233331111111111111 5 14),
([w53,w1,w2,w0,w3,w4,w5,w80],dL 0x4a0022e21290940bf2d5,dS 0x1b130e0c0b024a0a040103360d061a40,pH 0x1313553444333332222222222222 7 16),
([w130,w53,w1,w2,w0,w3,w4,w5],dL 0x2e62c01111de2d5,dS 0x134c031c0d0612021a4035010e0b,pH 0x1554443333222222224221333322 5 14),
([w64,w53,w1,w2,w0,w3,w4,w5],dL 0x6a2e909401f2ea1350b92df,dS 0x4c030d061b1a403818161310,pH 0x1141331543222222223221111122 8 12),
([w53,w1,w2,w0,w3,w4,w5,w29],dL 0x9411104a0072eb0122d32e9006,dS 0x11121337030d06210e0c04380b0140,pH 0x3335554444223541111111111111 9 15),
([w26,w53,w1,w2,w0,w3,w4,w5],dL 0xc2ee0152df00b2d5,dS 0x2512350c0b0304010d38061b130e1a40,pH 0x3313143154222222222223133322 6 16),
([w1,w2,w0,w24,w3,w4,w15,w5],dL 0x9b00f01f0b12f42f12f00b2035001091,dS 0x3b131b0f120a0906040e113408020d,pH 0x1526151111414423133182122122 11 15),
([w1,w2,w0,w24,w3,w4,w5,w81],dL 0x4a09b0bc00f09c2f50990350bd001091,dS 0x35370a0922161134080e020d,pH 0x2151651111133321444191222122 11 12),
([w48,w1,w2,w0,w24,w3,w4,w5],dL 0x6a00f09b0992f60c5035001091,dS 0x370d34110901060802191e0a0e,pH 0x6551114442333132221222111112 9 13),
([w17,w1,w2,w24,w3,w4,w5],dL 0x2fd0920350942fc09500300f,dS 0x1211242a08220c0b3d19340206100d0e03,pH 0x844222554233313111113 8 17),
([w109,w1,w2,w0,w3,w4,w5],dL 0x6a04a00f30c09530b035003094,dS 0x1312242a220b081135060d0e0110,pH 0x644222114155455111115 9 14),
([w1,w2,w0,w24,w3,w4,w13,w5],dL 0x9b01f00f0922f40cf2f01020350941033160aa099,dS 0x34152c39220312352a373209100d0e06,pH 0x9863334443451325153552222722 14 16),
([w52,w1,w2,w0,w24,w3,w4,w5],dL 0x9b00f01f0b42f42f031d2fb035092,dS 0x1b0e120d340103350211193b06322a0f,pH 0x5442223337111112222211111117 10 16),
([w1,w100,w2,w0,w24,w3,w4,w5],dL 0x6a00f0012c61c909b0cf323322035092,dS 0xd4a0802120a22035132370e06,pH 0x5332224437111111111112228217 11 13),
([w1,w2,w0,w24,w3,w4,w5,w80],dL 0x9209b12909412a3280bf0352f4,dS 0x344a2c240a03152232371112100d0e3606,pH 0x2114445554557438664663333733 9 17),
([w130,w1,w2,w0,w24,w3,w4,w5],dL 0x4a00f1de33132d0350922f4,dS 0x1b114c0103120206372432350e,pH 0x1553334446222223333321222226 8 13),
([w64,w1,w2,w0,w24,w3,w4,w5],dL 0x9213509c01f33c0943360350b913609b,dS 0x374c0908033212021306220e0d10,pH 0x1151221223145223332334111113 11 14),
([w58,w1,w2,w24,w3,w4,w5],dL 0x1f0cf2f42f034209902000300f,dS 0x20b320c1237340a171110060d0e22,pH 0x655222845233313121113 9 15),
([w186,w1,w2,w0,w3,w4,w5],dL 0x4004a0023432f403e0033440990202f0,dS 0x9260802370d0b1b120e1004,pH 0x141514714522422616262 11 12),
([w1,w2,w0,w24,w3,w4,w5,w29],dL 0xcf00709b0122f034700609c099008,dS 0xf340822032137020d121310320e06,pH 0x2865551115111543825174444744 10 15),
([w26,w1,w2,w0,w24,w3,w4,w5],dL 0xc01534e09900d00b09b2f4,dS 0x2512350802033213060d11100e22,pH 0x2212162163216472337335122223 8 14),
([w1,w2,w116,w0,w3,w4,w5],dL 0x6a04a0f735100311d34f096001,dS 0x120e183633221915110b3502061001,pH 0x633553223444341111111 9 15),
([w1,w2,w0,w3,w4,w331,w5],dL 0x4a0400020b103e36104335e35d003001,dS 0x1c130f120805041109100b1b0c0e0626,pH 0x5413332222a5438111111 11 16),
([w54,w1,w2,w0,w3,w4,w13,w5],dL 0x36100235e36210309401f0aa,dS 0x121122430d010c06321b10,pH 0x3625354344366331111111111111 8 11),
([w52,w54,w1,w2,w0,w3,w4,w5],dL 0x36135e3652fb01f11d0b4,dS 0x12430d0135021b113b32100f3d,pH 0x6554442622111111114112222211 7 13),
([w54,w1,w100,w2,w0,w3,w4,w5],dL 0x36632311d01f1c9,dS 0x4a123d0a430d0137511b110210,pH 0x2554443333233331111111111111 5 13),
([w54,w1,w2,w0,w3,w4,w5,w80],dL 0x4a36812a0940bf361,dS 0x1b13150c0b024a430d010e22361011,pH 0x1313553444333332222222222222 6 15),
([w130,w54,w1,w2,w0,w3,w4,w5],dL 0x36b32d11d1de361,dS 0x134c431b0d36011202111035320b0e,pH 0x1554443333222222224221333322 5 15),
([w54,w64,w1,w2,w0,w3,w4,w5],dL 0x6a01f36f13609436c0b9,dS 0x4c431b0a0d01131806110210,pH 0x2252442333111112222311111111 7 12),
([w54,w1,w2,w0,w3,w4,w5,w29],dL 0x9411d04a00737000835e371006,dS 0x110f12370b43060d0121020e0c321310,pH 0x3335554444223541111111111111 9 16),
([w26,w54,w1,w2,w0,w3,w4,w5],dL 0xc37400d36c00b361,dS 0x2512350b0c4306320d02011b130e1110,pH 0x3313143154222222222223133322 6 16),
([w1,w2,w90,w0,w3,w4,w5],dL 0x6a04a0030943762480350a037509f00f096,dS 0x121516051911090a010e0d100b04,pH 0x844222114511122333333 12 14),
([w1,w2,w0,w3,w4,w332,w5],dL 0x4a04000238338603e38400f01a382099,dS 0x150209160522121b19350d01100b0e04,pH 0x1245524324a1254313333 11 16),
([w18,w1,w2,w0,w3,w4,w15,w5],dL 0xa50030b10b201f386387035382001091,dS 0x3b131b111202221a0e08211509,pH 0x1325156135414442322221111212 11 13),
([w18,w1,w2,w0,w3,w4,w5,w81],dL 0x30bc04a0a6099388035001091,dS 0x351c1b08020106110e191509,pH 0x2151441654133331222221111212 9 12),
([w18,w48,w1,w2,w0,w3,w4,w5],dL 0x6a0030a50993890350c4091,dS 0xe0d08524512160b221e0a150919,pH 0x5442223332111116111111112111 8 14),
([w18,w1,w2,w20,w3,w4,w5],dL 0x38f09f0350a009438a00300f,dS 0x1312340a160c110e04073d100d010b0915,pH 0x833222553144325111111 8 17),
([w18,w1,w2,w0,w3,w4,w13,w5],dL 0xa50031030a009401f3863823951020cf,dS 0x371b124316040e0121351509,pH 0x1483332222148321143212222722 11 12),
([w52,w18,w1,w2,w0,w3,w4,w5],dL 0xa500301f38638239b0352bb0a0,dS 0x111b0e430b06350215090f01193b,pH 0x5442221111333212222131111111 9 14),
([w18,w1,w100,w2,w0,w3,w4,w5],dL 0x33230a539f0cf0a02c6,dS 0xe4a120a11430b373c0951211519,pH 0x3441112221522123341221111111 7 14),
([w18,w1,w2,w0,w3,w4,w5,w80],dL 0xa50bf12a0353a00a0094129386,dS 0xe344a2c240410430d3601110a3b1915,pH 0x4115552222143321115232222322 9 16),
([w130,w18,w1,w2,w0,w3,w4,w5],dL 0x33a80352c00a0386,dS 0x134c430b061202150a21010e35,pH 0x1553332222444323333241222222 6 13),
([w64,w18,w1,w2,w0,w3,w4,w5],dL 0xa01360a601f0943b10b93ae0350a5135,dS 0x122f4c080443011302193b15100d0916,pH 0x2241112331234131115113221221 11 16),
([w18,w1,w2,w3,w4,w49,w5],dL 0x1f3860cf0993b201a38200300f,dS 0x34190a12351605180c020d0117100e1a040b,pH 0x231523723542344111111 9 18),
([w18,w1,w2,w0,w3,w4,w5,w29],dL 0xcf0070080060993b63820a6012,dS 0x11340212371305430b0e0d010409192115,pH 0x3334441111223412234161111111 9 17),
([w26,w18,w1,w2,w0,w3,w4,w5],dL 0xc00d09900b3be0a5015386,dS 0x2512054301040b1b130e110d091535,pH 0x3312223142314252222223132332 8 15),
([w48,w1,w2,w0,w3,w4,w15,w5],dL 0x6d3c23c43c53c303500104e091,dS 0x131c1b1109082b1a0e15020a,pH 0x1232122126414443533333111113 9 12),
([w1,w12,w2,w0,w3,w4,w15,w5],dL 0x3d13c20011373cc3ca0b13c90350a8,dS 0x11131b0e0c08070b092b052226172a3b5304,pH 0x2375234234111111111112322217 10 18)]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p2 : List StD := [
([w1,w2,w0,w20,w3,w4,w15,w5],dL 0xd13c20430a80b13da3d30943d209f0350b2,dS 0x3b130f09072b05261b113d0a100b380e04,pH 0x2436641111111125555153433333 12 17),
([w50,w1,w2,w0,w3,w4,w15,w5],dL 0x3e73c21773e63e03df0b20350a8,dS 0x3b131b0f3e0b020c110a260912040e,pH 0x2574243233111112572211111117 9 15),
([w17,w1,w2,w0,w3,w4,w15,w5],dL 0xf30a83c20430b20943f13e93e80950350b1,dS 0x3b131b082a3e05263d12220e0b021a1c0415,pH 0x2534441111222413533331111213 12 18),
([w1,w2,w0,w3,w15,w13,w5],dL 0x20010a80690400cf06d3fd0aa094035,dS 0x3b1b1a0c372c392b550522261c09120e15352a1104,pH 0x272444721428222331333 11 21),
([w1,w230,w2,w0,w3,w4,w15,w5],dL 0x1af0010b10b204304004203540509103b0d90a8,dS 0x131b1c11150b2b05221a0812260a0e04,pH 0x6325537635113111131142322222 13 16),
([w1,w2,w0,w3,w4,w15,w59,w5],dL 0x6d0b20b12800350aa4070940a80a9040091,dS 0x3b101c111a0e2c082a2b052226120c09150204,pH 0x1143276113211368113441131117 12 19),
([w231,w1,w2,w0,w3,w4,w15,w5],dL 0xf72820b10b20a92804130a8040091,dS 0x1910150222040812093d3b0f,pH 0x1524142154313331551111111111 10 12),
([w86,w1,w2,w0,w3,w4,w15,w5],dL 0xa80942470400911af2450ae035043,dS 0x131b1c1211151a0e04080a26,pH 0x1135117115211221431111131963 10 12),
([w86,w1,w2,w0,w3,w4,w5],dL 0x4a00300f19b2470ae1af245096035,dS 0x131c0b1522350a08121b0411010e10,pH 0x343634234255455252225 10 15),
([w1,w100,w2,w0,w3,w4,w15,w5],dL 0x6d3232c60b10b20011c93c24254240350a8,dS 0x130e1b1c111a154a0802120a2b0522263d095104,pH 0x2364235234111111111112322216 12 20),
([w64,w1,w2,w0,w3,w4,w15,w5],dL 0x1361350a80b10b23c40940b94324310400353c2,dS 0xc4c090522260d3b150802132b120410,pH 0x1161441354135226556662111116 13 16),
([w1,w2,w131,w0,w3,w4,w15,w5],dL 0x4e0b20402d504343c0350912d304b0b1,dS 0x131b0a082b05261c29123d221a0e0904,pH 0x7326631131173145535112322222 11 16),
([w1,w2,w0,w3,w4,w15,w333,w5],dL 0x6d3820400b101a03503e4400b22f0091,dS 0x3b0c0a2b0522260f100b0d080e04,pH 0x1182574112331236112481121117 11 14),
([w334,w1,w2,w0,w3,w4,w15,w5],dL 0x3862f03824430b1035040091,dS 0x123710080b0c3b150a,pH 0x1625154144313331661111111111 8 9),
([w190,w1,w2,w0,w3,w4,w15,w5],dL 0x4e0f70b104304036103509135e4490510b2,dS 0x131b0a09083d2b052604111202220e,pH 0x7423331111666612422221111512 12 15),
([w1,w2,w69,w0,w3,w4,w15,w5],dL 0x6d3c20250a800102408344e0b101f,dS 0x1f1c0d1b0e0b2b01540522261e100a11120c04,pH 0x1151111112111121113211111115 10 19),
([w76,w1,w2,w0,w3,w4,w15,w5],dL 0x310a803008a45d0b201f,dS 0x110f230e0b015426120d1c3b0c242b131004,pH 0x1151112222111321111211222225 7 18),
([w1,w2,w0,w3,w4,w228,w15,w5],dL 0x3c20b10b204306d035465091464058040,dS 0x11100d1508090b052226133b2c0e022b04,pH 0x4473225553111356163662322222 11 17),
([w769,w1,w2,w0,w3,w4,w15,w5],dL 0x3c246a03504e06d091,dS 0x351109083b1c121a0e1502040a,pH 0x1232122125212441211113231111 6 13),
([w1,w2,w108,w0,w3,w4,w5],dL 0x4a00300f0ad4720cb0a9096001,dS 0x1b373633382b05221221150c19040e350201,pH 0x353635232244441111111 9 18),
([w77,w1,w12,w2,w0,w3,w4,w5],dL 0x47e3cc0cf47c3433c90cb137,dS 0x190e0c070b09041b11013b100d023553,pH 0x3554442222222421111111111111 8 16),
([w77,w1,w2,w0,w20,w3,w4,w5],dL 0x47e0d100f3da3d248338309409f,dS 0x35190c09020711010e0b38041b10,pH 0x5442223333222221111111111111 9 14),
([w77,w50,w1,w2,w0,w3,w4,w5],dL 0x47e3e60cf4863833e00cb177,dS 0x350c3e0b021b110112260d1038370e,pH 0x3554442222111112224211111111 8 15),
([w77,w17,w1,w2,w0,w3,w4,w5],dL 0x47e0f30033f13e948a094343095,dS 0x350e0b3e0c0911011c151b02192210,pH 0x5442223332111112222311111111 9 15),
([w77,w1,w100,w2,w0,w3,w4,w5],dL 0x34338347e48c1c90cf0cb,dS 0xe1b1c19154a09123d0a3f041101023751,pH 0x2425241111111113333333233333 7 17),
([w77,w64,w1,w2,w0,w3,w4,w5],dL 0x34338313513609406d48e43247e0b9,dS 0xe371509221b11010d2b021910,pH 0x2242342666111112222511111111 10 13),
([w77,w1,w2,w69,w0,w3,w4,w5],dL 0xcb09402547e08348f343024,dS 0x1f1c1e0d12350a041102010e0b26191b1034,pH 0x4332225222543221111111111111 8 18),
([w77,w76,w1,w2,w0,w3,w4,w5],dL 0xcb09403147e08a491383030,dS 0x233b190b26120d241102010e2b1c373410,pH 0x4332225432111115222211111111 8 17),
([w1,w2,w63,w0,w3,w4,w5],dL 0x300f46704a4981ca096001,dS 0x13213c0522150c0b12113510040e3601,pH 0x544564324233331111111 8 16),
([w1,w2,w0,w3,w4,w121,w5],dL 0x300f00203e04304a4644bb001,dS 0xc2b0522152112100b021309040e01,pH 0x331222453245321111111 9 15),
([w88,w1,w12,w2,w0,w3,w4,w5],dL 0x7d4c33d14c24c01ca137,dS 0x120e172a07350b0930041b13063b3253100d36,pH 0x5443332222222321111111111111 7 19),
([w88,w1,w2,w0,w20,w3,w4,w5],dL 0x6a07d00f0024c80d14c74c409409f,dS 0xe0b0c0a090207301b06120401381310,pH 0x6442223333222221111111111111 10 16),
([w50,w88,w1,w2,w0,w3,w4,w5],dL 0x7d4b73e74ca4c41771ca,dS 0x17093e30041b13060b020d3710120e01,pH 0x6443331111222225222221111122 7 16),
([w17,w88,w1,w2,w0,w3,w4,w5],dL 0x307d4c44ba0940f34cd0954c0,dS 0xe0b2a3e301b060c13103619222115,pH 0x6331114531222224222221111122 9 15),
([w88,w1,w2,w0,w3,w4,w13,w5],dL 0x6d4c44c010210300249a4ce4640940aa,dS 0x110e123735150930221b062a040d210110,pH 0x2324245234232221111111111111 11 17),
([w52,w88,w1,w2,w0,w3,w4,w5],dL 0x2bb2fb4c04c449c4644d20b41ca,dS 0xe1219152a30221b0d06353d0209103b0f0113,pH 0x4335431111222225222221111122 9 19),
([w88,w1,w2,w0,w3,w4,w49,w5],dL 0x6d0941ca00f01b0734d34644c401a,dS 0x1121350b301b0612190e1704360110,pH 0x2324242322523421111111111111 10 15),
([w58,w88,w1,w2,w0,w3,w4,w5],dL 0x30214c41ca0944640744d40204c0,dS 0x21371730041b36060c0a0e0b103b153213,pH 0x4331114531222224222221111122 10 17),
([w1,w12,w2,w0,w3,w4,w5,w81],dL 0x4a0013d11374d90bc0353cc0b8,dS 0x130e0802070b09302b160c3c355306,pH 0x6323553444111111111117333316 9 15),
([w1,w2,w0,w20,w3,w4,w5,w81],dL 0x4df0b80bc0d14de09409f3da0350bd,dS 0x35130a07302b0910163c113d0e0b1b0638,pH 0x4336661111111125555157444444 10 17),
([w50,w1,w2,w0,w3,w4,w5,w81],dL 0x4a1774e10bd0350b83e6,dS 0x35113e01300b02060c093c370e,pH 0x6313553444222223333322222226 7 13),
([w17,w1,w2,w0,w3,w4,w5,w81],dL 0xb80f30bd0944e50350950bc3f1,dS 0x83e302b3c0e0b020635161c1915,pH 0x3115552222111521333332222423 9 14),
([w64,w1,w2,w0,w3,w4,w81],dL 0xb84ea0350940b906d06a04a,dS 0x816213b120e15191c090213061b30,pH 0x223237235514444111114 8 15),
([w218,w1,w2,w0,w3,w4,w5],dL 0x4ec00300f24d4eb0b906d26803506a094,dS 0x1c1509081b06111001350e,pH 0x224254154165466111116 11 11),
([w1,w2,w770,w0,w3,w4,w5],dL 0x300f2aa4ed1df09600106d,dS 0x211510333826161213110e35020601,pH 0x111115413344442222222 8 15),
([w132,w1,w12,w2,w0,w3,w4,w5],dL 0x4f04ef1df1373cc,dS 0x130e073b0b094b1b01533511400234,pH 0x1554443333333432222221222222 5 15),
([w132,w1,w2,w0,w20,w3,w4,w5],dL 0x4a00f4f54f209409f3da,dS 0x13100b0c02074b1b010e16384011,pH 0x1553334444333332222221222222 7 14),
([w132,w50,w1,w2,w0,w3,w4,w5],dL 0x4f64f21df1773e6,dS 0x3e4b120b023c1b01370e40381134,pH 0x1554443333222223334321222222 5 14),
([w132,w17,w1,w2,w0,w3,w4,w5],dL 0x34fa0944ef0953f1,dS 0xe3e4b0c091b01210619021140,pH 0x1553334443222223333421222222 6 13),
([w1,w2,w146,w0,w3,w4,w5],dL 0x300f0944fc24e2964fb04a0c20bf035096,dS 0xb152c3c0522121c19110a100e012404,pH 0x556596111111111333333 12 16),
([w1,w2,w0,w3,w4,w189,w5],dL 0x303e00f0025070cf04a50d0063c3099,dS 0x101c0a080b2b05221512190901370e0204,pH 0x325442512471266313333 11 17),
([w48,w1,w12,w2,w0,w3,w4,w5],dL 0x6a50e5120c40cf0c23d1,dS 0xe07530b094b1112353219241e18,pH 0x1151441222122421354221111111 7 14),
([w48,w1,w2,w0,w20,w3,w4,w5],dL 0x400c409f0d65180350c25170940c50d1,dS 0x11100b09074b05381b04190e011e0a3d,pH 0x1141221225133251332233111111 11 16),
([w50,w48,w1,w2,w0,w3,w4,w5],dL 0x6a0cf51f0c50353e70c2,dS 0x3e4b12060b021e180a010e37,pH 0x2252441111233312222131111111 7 12),
([w17,w48,w1,w2,w0,w3,w4,w5],dL 0xc20f50400c550c0940955260350f30c4,dS 0xe0b2a3e4b0502011e3d1c19152224,pH 0x2241112331233135221221113111 11 15),
([w48,w1,w2,w0,w3,w4,w13,w5],dL 0x6d0010aa1021035280cf0990c23c352904009449a,dS 0x1c0e2a094b052204181b01371e2c,pH 0x1161441354155221352222111111 14 14),
([w52,w48,w1,w2,w0,w3,w4,w5],dL 0x2bb2fb0c40c503506d5303c349c0c2,dS 0xe1109221235021e3d2c01190f,pH 0x2242341111266612222151111111 10 13),
([w48,w1,w2,w0,w3,w4,w80],dL 0x5320bf06d0350c253106a09404a,dS 0x1c192c2405211b110e361e3b2201120a,pH 0x334394155532425111111 9 16),
([w48,w1,w2,w0,w3,w4,w49,w5],dL 0xcf01b53306d01a0995343c30c5073,dS 0x110f02350b4b1b1a05120a01041e0e1918,pH 0x1121241322123421234261111111 10 17),
([w58,w48,w1,w2,w0,w3,w4,w5],dL 0x215440c50cf06d0993c35430200740c4,dS 0xb4b05041e0e111c0a18153237,pH 0x2241112541256163221221116111 11 13),
([w48,w1,w2,w0,w3,w4,w29],dL 0xcf0990063c354506a04a,dS 0x1c1937090b05223b1b0201210e13041e12,pH 0x123243243724355111111 7 17),
([w1,w2,w21,w0,w3,w4,w5],dL 0x6a04a0993c609154800f002137,dS 0x17242a071b08121911320c0e100d02,pH 0x644333554122221111121 9 15),
([w1,w2,w0,w3,w4,w227,w5],dL 0x4a00107d0403cc55700f3c9002,dS 0xc0601021b0d08123504100e0b,pH 0x521444333311111772431 9 13),
([w1,w12,w2,w0,w3,w4,w5,w29],dL 0x4a1370060cf3d13c955d01250e007,dS 0x2a070b0913100d531219080e02320c,pH 0x5654443333111111111312654311 10 15)]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p3 : List StD := [
([w26,w1,w12,w2,w0,w3,w4,w5],dL 0xb56001500c3d13cc,dS 0x251207530b0911100d02321b130e0c0835,pH 0x2212142133213432154332122222 6 17),
([w110,w1,w2,w0,w3,w4,w5],dL 0x6a04a00f4820a0561003091094,dS 0x120d0a160b0419091110020e,pH 0x644333554322422222222 9 12),
([w1,w2,w0,w20,w3,w4,w13,w5],dL 0xd149a00f3da1023d2568103094002096,dS 0x35370a051b3d0604100e010b,pH 0x1625151111414422122723133172 11 12),
([w1,w2,w0,w20,w3,w4,w5,w80],dL 0x4a56b00f12956a3da09412a002096,dS 0x1315100906053d110e04010b,pH 0x2151661111133321222721444172 10 12),
([w64,w1,w2,w0,w20,w3,w4,w5],dL 0x6a04000f0d157056c136094002096,dS 0x120e3d020a0b0401061310,pH 0x6551114442111113331311111111 10 11),
([w147,w1,w2,w0,w3,w4,w5],dL 0x7e04a2bb0010403da07d03e0035730213d2,dS 0x132a380b0e11101c090412010f,pH 0x131413223261366515255 12 13),
([w1,w2,w0,w20,w3,w4,w5,w29],dL 0x4a00f09609f0060120d10073d25740d6008,dS 0xf37071904380912130e100b01,pH 0x4643331111111155543752643175 12 13),
([w26,w1,w2,w0,w20,w3,w4,w5],dL 0xb01500c57a00d0d13da,dS 0x2512070438091b133501110e0b10,pH 0x2212132135214652143652122222 7 14),
([w1,w182,w2,w0,w3,w4,w5],dL 0x6a04a0783e257b003177002091,dS 0x120a153c261711190d02090e1001,pH 0x655444222211511111111 9 14),
([w1,w2,w0,w3,w4,w229,w5],dL 0x4a00110207d0403e65860033e0002,dS 0x381b06370d091204100b0e,pH 0x521444333311111772481 10 11),
([w50,w1,w2,w0,w3,w4,w5,w29],dL 0x1770060cf5890083e058a007,dS 0x110f3e13100d090b020c380137120e,pH 0x3335554444111112235411111111 8 15),
([w26,w50,w1,w2,w0,w3,w4,w5],dL 0xb58c00d3e700c3e6,dS 0x25123e35100d0c380b02011b1311090e,pH 0x3313142222315422222223133232 6 16),
([w1,w83,w2,w0,w3,w4,w5],dL 0x6a04a2830033eb09209458d09500f091,dS 0x13120d15242a38110b220835020e1006,pH 0x744222554211411111111 11 16),
([w1,w2,w0,w3,w4,w183,w5],dL 0x4a2fb00104001b3f13e959400f07d,dS 0x1c150b0212091a051b1906080e1001,pH 0x542333222261636111116 10 15),
([w17,w1,w2,w0,w3,w4,w13,w5],dL 0xf300349a1021033f15960943e9002096,dS 0x351b09370b0e05011c1506,pH 0x1325156135131114144411111111 11 11),
([w17,w1,w2,w0,w3,w4,w5,w80],dL 0x312904a5970940023f1096,dS 0x3b12020a0e010611051915,pH 0x3121551225111111444411111111 8 11),
([w17,w64,w1,w2,w0,w3,w4,w5],dL 0x6a0400035990f3598094135096,dS 0x120e0b4d2a3e041b240c093b10191506,pH 0x5442221111333215111111112111 9 16),
([w17,w1,w2,w0,w3,w4,w5,w29],dL 0x309609500800600759b3e90f5012,dS 0x1112373e1310020c0e0b080601192115,pH 0x3334441111223412234151111111 10 16),
([w26,w17,w1,w2,w0,w3,w4,w5],dL 0xd00b00c5a00f30153f1,dS 0x25123e100102080c1b130e350b061a15,pH 0x3312223142314252222223132332 7 16),
([w148,w1,w2,w0,w3,w4,w13,w5],dL 0x6d1a910210309600210a5a20400425a503b0940aa,dS 0x1c15090137350e162a1b06,pH 0x2374435234233421111111111111 14 11),
([w1,w2,w0,w3,w4,w13,w59,w5],dL 0x6d1031022450aa5ad0400cf0a9094096,dS 0x11101c0c37350e2c2b060105221215092a04,pH 0x1173446113511361131112212227 11 18),
([w338,w1,w2,w0,w3,w4,w13,w5],dL 0x5af0a90400aa0960cf,dS 0x19101c37350e1508093901061204,pH 0x2116214216222223333333213333 6 14),
([w79,w1,w2,w0,w3,w4,w13,w5],dL 0xaa0962821a90400ff28010a094,dS 0x1c1537350e161b0609,pH 0x1345135136134111131111141148 9 9),
([w79,w1,w2,w0,w3,w4,w5],dL 0x1f04a00300f19b2820ff1a9280094091,dS 0x131c150616111b09123510020e,pH 0x343634534511411151111 11 13),
([w64,w1,w2,w0,w3,w4,w13,w5],dL 0x6d49a5285b24320940965b0,dS 0x113b37354d1b2c120e1509050106,pH 0x2111211215242223233321222222 8 14),
([w1,w2,w339,w0,w3,w4,w13,w5],dL 0x5b010210309604c0403cc5b30cf,dS 0x1b0e2c02390506220421372a29350901,pH 0x1152113112111161111111111115 9 16),
([w1,w2,w0,w3,w4,w13,w340,w5],dL 0x3e904010201b5b71033d2094096,dS 0x3537180c172c16051b0e2a100b060409,pH 0x1173165113441371131112112226 9 16),
([w341,w1,w2,w0,w3,w4,w13,w5],dL 0x3f13d23e95b8102094040096,dS 0x12111009050c1c1506,pH 0x1625154144166113133311111111 8 9),
([w342,w1,w2,w0,w3,w4,w13,w5],dL 0x5b01020403e65bb1030cf,dS 0x35191b390b060412370e2a01,pH 0x1113112222141121111212122222 7 12),
([w1,w2,w69,w0,w3,w4,w13,w5],dL 0x20960835bd10202501f,dS 0x1f0c1c0d35390e0b052a041e1b12090601,pH 0x1121111113111132122221111112 7 17),
([w76,w1,w2,w0,w3,w4,w13,w5],dL 0x9608a0315bf10301f,dS 0x1c21230c390e0b04120d3b01372c1016,pH 0x1141112222111321111211222222 6 16),
([w1,w2,w0,w3,w4,w771,w13,w5],dL 0x49a06d5281021030960595c30400cf,dS 0x511c180e1502392b051b2c2a043706350901,pH 0x2511413111211131111111111114 10 18),
([w772,w1,w2,w0,w3,w4,w13,w5],dL 0x49a5c40945b006d096,dS 0x1121121b37350e1509050106,pH 0x1232122125121114144413231111 6 12),
([w1,w773,w2,w0,w3,w4,w5],dL 0x1f04a00300f07d0ad0b45c50a9002091,dS 0x1c15023c32121b191110090e01,pH 0x344634222213412111111 11 13),
([w52,w1,w2,w69,w0,w3,w4,w5],dL 0x349c5ca2bb06d02501f,dS 0x1c093502191e05060f01,pH 0x1111141113212221111122122222 7 10),
([w52,w76,w1,w2,w0,w3,w4,w5],dL 0xf5cc2fb03101f,dS 0x11233a04120d3502102c163b130f01,pH 0x1113332222111321333232122222 5 15),
([w1,w2,w150,w0,w3,w4,w5],dL 0x1f00300f42208104a5cd0910021c9,dS 0x211c15360b0d09081b19110e3c0210,pH 0x544574134322221111121 10 15),
([w1,w2,w0,w3,w4,w232,w5],dL 0x300f00104a5d20cf07d424002,dS 0x10121c0b2c091506080e05370201,pH 0x221552632511111333331 9 14),
([w1,w100,w2,w0,w3,w4,w49,w5],dL 0xf5d542432301b01f,dS 0x1b2111184a120a020605513c,pH 0x1111111413222221222221111122 6 12),
([w58,w1,w100,w2,w0,w3,w4,w5],dL 0x30cf5d70212c601f,dS 0x111d4a120a3c193751051c153806,pH 0x1112221132111231112112125222 6 14),
([w219,w1,w2,w0,w3,w4,w5],dL 0x5da00300f2884fb0c206d29606a091094,dS 0x1c152c22041219100a11020e,pH 0x334354364625422222222 11 12),
([w1,w774,w2,w0,w3,w4,w5],dL 0x5dc00300f08506d06a5db1de002091,dS 0x1c2c26321b19150a1102100e01,pH 0x544564222211411111111 10 13),
([w1,w220,w2,w0,w3,w4,w5],dL 0x1f00300f2895de2680b84eb0940b904a091,dS 0x15362b121c09113516080e021006,pH 0x225285245411111111111 12 14),
([w1,w2,w0,w3,w4,w97,w5],dL 0x300f0010075e204a07d06d,dS 0xc0b0d02150e0913050608191001,pH 0x333444321431545222225 8 14),
([w64,w1,w2,w0,w3,w4,w49,w5],dL 0x6d09653301b5e513607301f,dS 0x110c274c1202350e0b041b0119180610,pH 0x2212112313211432111112222222 8 16),
([w58,w64,w1,w2,w0,w3,w4,w5],dL 0x5440960215e807413501f,dS 0x1d4c370e0b0401190c3818103b131506,pH 0x3312223142311215332332122222 7 16),
([w775,w1,w2,w0,w3,w4,w5],dL 0x4a00201f3860780355eb382003091,dS 0x35080f011202161b110d09190e0b,pH 0x344222535213125111111 10 14),
([w226,w1,w2,w0,w3,w4,w5],dL 0x4a0010f70943f15ee3e9003096,dS 0x350211011a10081c0e171219150b04,pH 0x344222114263421111111 9 15),
([w1,w776,w2,w0,w3,w4,w5],dL 0x4a07d00201f2f40355ef0202f000f091,dS 0x1c1509020b121b08323711100e06,pH 0x355222635213521111111 11 14),
([w1,w2,w187,w0,w3,w4,w5],dL 0x4a0013da0210945f009600f3d2,dS 0x130b1c1512051b060138350a0e111004,pH 0x144222314663362555536 9 16),
([w1,w2,w0,w149,w3,w4,w5],dL 0x44b0020cf03504a5f300f091024,dS 0xa09191b0d12350b11080c020e1006,pH 0x544174333156463111311 9 15),
([w1,w2,w0,w120,w3,w4,w5],dL 0x144c09402504a5f809600f,dS 0x1f060512351b0e11040a0b341001,pH 0x433523111555211666615 8 14),
([w1,w2,w0,w3,w4,w129,w5],dL 0x207a00104a5fb08300f07d,dS 0x18120b05091b06020e3401191004,pH 0x332444222251342111111 8 14),
([w777,w1,w2,w0,w3,w4,w5],dL 0x60200203507860100309106d,dS 0x3b353d0501120402091b1915180d110e,pH 0x144333114321236222222 8 16),
([w778,w1,w2,w0,w3,w4,w5],dL 0x6040010f709460300309606d,dS 0x2a0402081b011c130612110d100e0b,pH 0x144333124315432222222 8 15),
([w1,w779,w2,w0,w3,w4,w5],dL 0x60800203506d06a60502d00f091,dS 0x1c1512353d02081b110d3219100e22,pH 0x544222564211411111111 9 15),
([w1,w2,w780,w0,w3,w4,w5],dL 0x109402e60900f09606d,dS 0x151a05060d3812010b0e11101b0904,pH 0x144333524525253666625 7 15),
([w1,w781,w2,w0,w3,w4,w5],dL 0xcf07845f00203560d04a030003091,dS 0x213b09351119022b0b083c1b0e0d1016,pH 0x445222465211111111111 10 16),
([w1,w2,w335,w0,w3,w4,w5],dL 0xf700145b09404a610031003096,dS 0xe13152c0605360b1c11011210340424,pH 0x544222314333312666613 9 16),
([w1,w2,w0,w3,w4,w223,w5],dL 0x200107e08a04a61300307d,dS 0xf090b0605120e1c13023401371004,pH 0x442333222241532111111 8 15),
([w118,w1,w2,w0,w3,w4,w5],dL 0x300f00207d03561606a0913c3,dS 0x1c15370b320f100102121119090e,pH 0x334314314531225322222 9 14),
([w188,w1,w2,w0,w3,w4,w5],dL 0x300f0012aa09461706a432096,dS 0x121538060d02110135081310210e04,pH 0x334324314135451311111 9 15)]
noncomputable def ptopD9 : List StD := ptopD9p0 ++ ptopD9p1 ++ ptopD9p2 ++ ptopD9p3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x2 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x3 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (3*64)).take 64) = true := by decide +kernel
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := levelStep ptopB ptopW ptopQ ptopI8 (chunks 64 ptopD9 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  · exact ptopC9x2
  · exact ptopC9x3
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([w28,w1,w2,w0,w3,w4,w5],dL 0x4a06a06900f00303b017002001,dS 0x100d1c0a05310201120b19110e1508090406,pH 0x433143222211111111111 9 18),
([w1,w2,w6,w0,w3,w4,w5],dL 0x6a04a00300f0a90020a7001,dS 0xc36383c26323121191512350b1b0d0e02110110,pH 0x422142742533231111131 8 20),
([w22,w1,w2,w0,w3,w4,w5],dL 0x4a06a00f0030a7002245238001,dS 0x131c150a3c26324704123509081b0d0e0b011110,pH 0x322132432411111111111 9 20),
([w10,w1,w2,w0,w3,w4,w5],dL 0x4a06a00f0030a700128027e002,dS 0x131c1536381b470811060d100402120b350e,pH 0x322132111143241111111 9 18),
([w53,w1,w2,w0,w3,w4,w5],dL 0x4a06a0022d32d100f001,dS 0x1310180a093516030d06120e0c041c380b011a40,pH 0x433222143211111111111 7 20),
([w1,w2,w0,w24,w3,w4,w5],dL 0x6a04a00200f2f02ef001003,dS 0x340a0935082203371b321202110d0e1006,pH 0x433143113214315222522 8 17),
([w54,w1,w2,w0,w3,w4,w5],dL 0x4a06a00235e35c003001,dS 0x13180a093522430d01120b061b020e0c321110,pH 0x433222143211111111111 7 19),
([w18,w1,w2,w0,w3,w4,w5],dL 0x4a06a00200300138238000f,dS 0x340a1235161b4301020b0e11100d0421091915,pH 0x322111132143214111111 8 19),
([w1,w2,w0,w3,w4,w15,w5],dL 0x4a00300f00206d0693c0001,dS 0x3b131c0c1a0805222615090b12110e0d1b021004,pH 0x431222463245321131111 8 20),
([w77,w1,w2,w0,w3,w4,w5],dL 0x4a00f00300206d06947a001,dS 0x1c3715120922041101190b0d350e02261b10,pH 0x322432432111111111111 8 18),
([w88,w1,w2,w0,w3,w4,w5],dL 0xf00300246404a4ae001,dS 0x1530221b0621350e090b040d3612011310,pH 0x422342342111111111111 7 17),
([w1,w2,w0,w3,w4,w5,w81],dL 0x300f00204a4d500106d,dS 0x1c153035090b0d3c1b19100206110e,pH 0x211333111311131122222 7 15),
([w132,w1,w2,w0,w3,w4,w5],dL 0xf0030024ee00106d,dS 0x13090b4b1b011235063c3402210e1140,pH 0x133113113122222122222 6 16),
([w48,w1,w2,w0,w3,w4,w5],dL 0xf00300206a0013c350604a,dS 0x1c09350b4b220d01120e1110021b04180a191e,pH 0x112132132113244111111 8 19),
([w1,w12,w2,w0,w3,w4,w5],dL 0x4a06a0013c955600f002,dS 0x17242a073b35530b09061b0412111908320e100c0d02,pH 0x433222111111121143211 7 22),
([w1,w2,w0,w20,w3,w4,w5],dL 0x6a04a00100f3d2002567003,dS 0x3d0a3507061b190438120109110e0b10,pH 0x422111111333253142153 8 16),
([w50,w1,w2,w0,w3,w4,w5],dL 0x4a06a0013e0585003002,dS 0x170a3e061b040b02110d0901100c3812370e,pH 0x433222111114321111111 7 18),
([w17,w1,w2,w0,w3,w4,w5],dL 0x4a06a0030010023e959300f,dS 0x3d242a353e04020c0e111001081c12060b1915,pH 0x322111432113214111111 8 19),
([w1,w2,w0,w3,w4,w13,w5],dL 0x4a00300f00106d0020695a1,dS 0x1c152a37060d041b35120b01090e10,pH 0x423111462132313452113 8 15),
([w52,w1,w2,w0,w3,w4,w5],dL 0x4a00f00300106d0695c6002,dS 0xe0b152a060d35021b103d1911093b010f,pH 0x322432111143211111111 8 17),
([w1,w100,w2,w0,w3,w4,w5],dL 0xf00300142404a5d0002,dS 0x154a1237513d0a04060d0911190e0b083c211b0210,pH 0x322342111131111342111 7 21),
([w1,w2,w0,w3,w4,w5,w80],dL 0x300f04a0015d90025d806d,dS 0xc3b4a3504060d150b360a121001110e19,pH 0x311222111213123114213 8 17),
([w130,w1,w2,w0,w3,w4,w5],dL 0xf0030015dd00206d,dS 0x154c10060d1202110a360b011b21350e,pH 0x133113222211312122222 6 16),
([w64,w1,w2,w0,w3,w4,w5],dL 0xf00306a0010024325e104a,dS 0x154c3504021b3b091901080d0e0b06121310,pH 0x112132132413214111111 8 18),
([w1,w2,w0,w3,w4,w49,w5],dL 0x4a00200100f06d0695e9003,dS 0x35170219011b121a04080e0b10,pH 0x135212135141321413251 8 13),
([w58,w1,w2,w0,w3,w4,w5],dL 0x4a00300200106906d5f200f,dS 0x170c0e121001020a1137060b1c15,pH 0x422111342133211111111 8 14),
([w1,w2,w69,w0,w3,w4,w5],dL 0x200108304a5f700f,dS 0x1f1c1e0d09350a110601020804121b190e0b1034,pH 0x322111311134211342111 6 20),
([w1,w2,w0,w3,w4,w5,w117],dL 0x20015fe00f5fd06d003,dS 0xb1f3b353d1c0d0102210408111910180e,pH 0x412133111112231125341 7 17),
([w106,w1,w2,w0,w3,w4,w5],dL 0x200160a00f06d,dS 0x23353d101801021c0b0e1b12190d09221a15,pH 0x133222113211321122222 5 18),
([w76,w1,w2,w0,w3,w4,w5],dL 0xf00200108a04a612003,dS 0x233b0935041901020d2124161c0e340b1310,pH 0x322111342134211111111 7 18),
([w1,w2,w0,w3,w4,w5,w29],dL 0x300f00200104a06961506a,dS 0xc370906021521190d0b0113100408120e,pH 0x343222113211321143211 8 17),
([w26,w1,w2,w0,w3,w4,w5],dL 0x61804a06d,dS 0x251215090601021b130d0b040835110e10,pH 0x221213213121311212222 3 17)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopW ptopQ ptopI9 (chunks 64 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([w1,w2,w0,w3,w4,w5],dL 0x693bf,dS 0x1c150a350102091b06110d0812190e0b0410,pH 0x211121121112111 2 18)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK ptopT ptopK ptopP 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI11 : LevelN ptopR ptopT 11 ptopD11 := levelStep ptopB ptopW ptopQ ptopI10 (chunks 64 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_46668

theorem PEqualNP.Outside.L_meta_46668 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  exact PEqualNP.Outside.L_meta_46668.replaceShort s h
