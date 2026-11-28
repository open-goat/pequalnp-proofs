import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25591_aux

def block91 (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0

theorem block_bits91 (w : Nat) (t : Int → Bool) (b : Int) (i : Nat) :
    (block91 w t b).testBit i = (decide (i<w) && t (b+1+(i:Int))) := by
  induction w with
  | zero => simp [block91]
  | succ w ih =>
    have step : block91 (w+1) t b = block91 w t b ||| ((t (b+1+(w:Int))).toNat <<< w) := by
      simp [block91,List.range_succ,List.foldl_append]
    have bit (v : Bool) : (v.toNat <<< w).testBit i = (decide (w=i) && v) := by
      cases v <;> simp [Nat.one_shiftLeft,Nat.testBit_two_pow]
    rw [step,Nat.testBit_or,ih,bit]
    by_cases lo : i<w
    · have ne : w≠i := by omega
      simp [lo,ne,Nat.lt_succ_of_lt lo]
    · by_cases eq : w=i
      · subst w; simp
      · have hi : ¬i<w+1 := by omega
        simp [lo,eq,hi]

theorem block_lt91 (w : Nat) (t : Int → Bool) (b : Int) : block91 w t b < 2^w := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [block_bits91,Nat.not_lt.mpr hi]

theorem block_bit91 (w : Nat) (t : Int → Bool) (b : Int) (i : Nat) (hi : i<w) :
    (block91 w t b).testBit i = t (b+1+(i:Int)) := by
  simp [block_bits91,hi]

theorem block_congr91 {w : Nat} {t u : Int → Bool} {b : Int}
    (agree : ∀ i : Nat, i<w → t (b+1+(i:Int))=u (b+1+(i:Int))) :
    block91 w t b=block91 w u b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<w
  · simpa [block_bits91,hi] using agree i hi
  · simp [block_bits91,hi]

theorem block_congr_interval91 {w : Nat} {t u : Int → Bool} {b : Int}
    (agree : ∀ p : Int, b<p → p≤b+(w:Int) → t p=u p) : block91 w t b=block91 w u b :=
  block_congr91 (fun i hi => agree _ (by omega) (by omega))

theorem block_mod91 {w m : Nat} (t : Int → Bool) (b : Int) (hw : w≤m) :
    block91 m t b % 2^w = block91 w t b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<w
  · simp [Nat.testBit_mod_two_pow,block_bits91,hi,lt_of_lt_of_le hi hw]
  · simp [Nat.testBit_mod_two_pow,block_bits91,hi]

end PEqualNP.Outside.L_meta_25591_aux

namespace PEqualNP.Outside.L_meta_25591_aux
def mix91 (x : Int→Bool) (z : Int) := xor (xor (x (z-1)) (x z)) (x (z+1))
def evolve91 (x inj : Int→Bool) (z : Int) :=
  xor (xor (mix91 x z) (!(mix91 x (z+1)) && mix91 x (z+2))) (inj z)
def fits91 (w : Nat) (b : Int) (x : Int→Bool) (mask : Nat) (t : Int→Bool) : Prop :=
  (∀ z ≤ b, t z=x z) ∧ mask.testBit (block91 w t b)=true
def tails91 (w mask : Nat) := (List.range (2^(2*w+5))).filter (fun p => mask.testBit (p%2^w))
def trial91 (b : Int) (x : Int→Bool) (c : Nat) (s : Int) :=
  if s≤b then x s else c.testBit (s-b-1).toNat
def fixed91 (w : Nat) (b : Int) (x inj : Int→Bool) (mask off : Nat) :=
  (tails91 w mask).all (fun p=>evolve91 (trial91 b x p) inj (b-2+(off:Int)) == evolve91 x inj (b-2+(off:Int)))
def advance91 (w : Nat) (b : Int) (x inj : Int→Bool) (mask : Nat) :=
  let f := b-3+(((List.range (w+5)).takeWhile (fixed91 w b x inj mask)).length : Int)
  (f,(tails91 w mask).foldl (fun acc c=>acc ||| ((1:Nat) <<< block91 w (evolve91 (trial91 b x c) inj) f)) 0)

theorem tailsMem91 {w m p : Nat} :
    p∈tails91 w m ↔ p<2^(2*w+5) ∧ m.testBit (p%2^w)=true := by simp [tails91]

theorem trialBlock91 (w : Nat) (b : Int) (x : Int→Bool) (p : Nat) :
    block91 w (trial91 b x p) b = p%2^w := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<w
  · rw [block_bit91 _ _ _ _ hj,Nat.testBit_mod_two_pow]
    simp [trial91,hj,show ¬b+1+(j:Int)≤b by omega,show (b+1+(j:Int)-b-1).toNat=j by omega]
  · have h1 := block_lt91 w (trial91 b x p) b
    have h2 := Nat.mod_lt p (by positivity : 0<2^w)
    have h3 : 2^w≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (h1.trans_le h3),Nat.testBit_lt_two_pow (h2.trans_le h3)]

theorem trialFits91 {w : Nat} {b : Int} {x : Int→Bool} {mask p : Nat} (hp : p∈tails91 w mask) :
    fits91 w b x mask (trial91 b x p) := by
  refine ⟨fun s h => by simp [trial91,h],?_⟩
  rw [trialBlock91]
  exact (tailsMem91.mp hp).2

theorem codeMem91 {w : Nat} {b : Int} {x t : Int→Bool} {mask : Nat} (fit : fits91 w b x mask t) :
    block91 (2*w+5) t b∈tails91 w mask := by
  apply tailsMem91.mpr
  exact ⟨block_lt91 _ _ _,by rw [block_mod91 t b (by omega : w≤2*w+5)];exact fit.2⟩

theorem codeEq91 {w : Nat} {b : Int} {x t : Int→Bool} {mask : Nat} (fit : fits91 w b x mask t)
    (s : Int) (hi : s≤b+(2*w+5:Nat)) :
    trial91 b x (block91 (2*w+5) t b) s=t s := by
  unfold trial91
  split
  · exact (fit.1 _ (by omega)).symm
  · rw [block_bit91 _ _ _ _ (by omega : (s-b-1).toNat<2*w+5)]
    congr 1
    omega

theorem evolveEq91 {x t inj : Int→Bool} {z : Int} (h : ∀ (i : Int), (z-1 ≤ i) → (i ≤ z+3) → x i=t i) :
    evolve91 x inj z=evolve91 t inj z := by
  unfold evolve91 mix91
  repeat first | rw [h _ (by omega) (by omega)]

theorem fixedIff91 {w : Nat} {b : Int} {x inj : Int→Bool} {mask j : Nat} (hj : j≤w+4) :
    fixed91 w b x inj mask j=true ↔ ∀ t, fits91 w b x mask t →
      evolve91 t inj (b-2+(j:Int))=evolve91 x inj (b-2+(j:Int)) := by
  constructor
  · intro h t ht
    have a := List.all_eq_true.mp h _ (codeMem91 ht)
    have eq := evolveEq91 (inj:=inj) (z:=b-2+(j:Int))
      (fun s _ hs => codeEq91 ht s (by omega))
    exact eq.symm.trans (beq_iff_eq.mp a)
  · intro h
    apply List.all_eq_true.mpr
    intro c hc
    exact beq_iff_eq.mpr (h _ (trialFits91 hc))

theorem last91 {w : Nat} {b : Int} {x inj : Int→Bool} {mask : Nat}
    (ok : mask.testBit (block91 w x b)=true) : fixed91 w b x inj mask (w+4)=false := by
  let v := b+(w:Int)+1
  let t (z:Int) := if z=v then !(x z) else x z
  have ht : fits91 w b x mask t := by
    refine ⟨fun s hs => by simp [t,show s≠v by dsimp [v];omega],?_⟩
    have eq : block91 w t b=block91 w x b := by
      apply block_congr91
      intro j hj
      simp [t,show b+1+(j:Int)≠v by dsimp [v];omega]
    rwa [eq]
  have lastSite : b-2+((w+4:Nat):Int)=v+1 := by dsimp [v];omega
  cases hg : fixed91 w b x inj mask (w+4) with
  | false => rfl
  | true =>
    have same := (fixedIff91 (le_refl _) |>.mp hg) t ht
    rw [lastSite] at same
    have ne1 : v+1≠v := by omega
    have ne2 : v+1+1≠v := by omega
    have ne3 : v+1+1+1≠v := by omega
    have ne4 : v+1+2≠v := by omega
    have ne5 : v+1+2+1≠v := by omega
    simp only [evolve91,mix91,t,show v+1-1=v by omega,ite_true,ne1,ne2,ne3,ne4,ne5,
      show v+1+1-1=v+1 by omega,show v+1+2-1=v+1+1 by omega,ite_false] at same
    generalize x v = A at same
    generalize x (v+1) = B at same
    generalize x (v+1+1) = C at same
    generalize (!(xor (xor B C) (x (v+1+1+1))) && xor (xor C (x (v+1+2))) (x (v+1+2+1))) = D at same
    generalize inj (v+1)=J at same
    revert same
    cases A <;> cases B <;> cases C <;> simp

end PEqualNP.Outside.L_meta_25591_aux

namespace PEqualNP.Outside.L_meta_25591_aux

theorem prefixLen91 (S : Nat→Bool) (n : Nat) :
    let z := ((List.range n).takeWhile S).length
    z≤n ∧ (z<n → S z=false) ∧ ∀ j<z, S j=true := by
  induction n with
  | zero => simp
  | succ n ih =>
    let z := ((List.range n).takeWhile S).length
    change z≤n ∧ (z<n → S z=false) ∧ ∀ j<z, S j=true at ih
    obtain ⟨le,bad,ok⟩ := ih
    dsimp only
    rw [List.range_succ,List.takeWhile_append,List.length_range]
    by_cases eq : z=n
    · have same : ((List.range n).takeWhile S).length=n := eq
      rw [ite_eq_left same]
      cases h : S n with
      | false =>
        simpa [List.takeWhile,h] using (show n≤n+1 ∧ (n<n+1 → S n=false) ∧ ∀ j<n,S j=true from
          ⟨by omega,fun _=>h,eq ▸ ok⟩)
      | true =>
        simp only [List.takeWhile_cons,h,ite_true,List.takeWhile_nil,List.length_append,List.length_range,
          List.length_cons,List.length_nil,Nat.zero_add,Nat.le_refl,lt_irrefl,false_implies,true_and]
        intro j hj
        by_cases jn : j=n
        · simpa [jn] using h
        · exact ok j (by omega)
    · have ne : ((List.range n).takeWhile S).length≠n := eq
      rw [ite_eq_right ne]
      exact ⟨by change z≤_;omega,fun _=>bad (by omega),ok⟩

theorem stop91 (w : Nat) (S : Nat→Bool) (last : S (w+4)=false) :
    let z:=((List.range (w+5)).takeWhile S).length
    z≤w+4 ∧ S z=false ∧ ∀ j<z,S j=true := by
  let z:=((List.range (w+5)).takeWhile S).length
  obtain ⟨a,b,c⟩ := prefixLen91 S (w+5)
  change z≤w+5 at a
  change ∀ j<z,S j=true at c
  have lim : z≤w+4 := by
    by_contra! gt
    have h := c _ gt
    simp [last] at h
  exact ⟨lim,b (by omega),c⟩

end PEqualNP.Outside.L_meta_25591_aux

namespace PEqualNP.Outside.L_meta_25591_aux

theorem foldBits91 (c : Nat→Nat) (L : List Nat) (j acc : Nat) :
    ((L.foldl (fun a x=>a ||| ((1:Nat) <<< c x)) acc).testBit j=true) ↔
      acc.testBit j=true ∨ ∃ x∈L,c x=j := by
  induction L generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    simp only [Nat.testBit_or,Nat.one_shiftLeft,Nat.testBit_two_pow,
      Bool.or_eq_true,decide_eq_true_eq,List.mem_cons]
    aesop

theorem exact91 (w : Nat) (b : Int) (x inj : Int→Bool) (mask : Nat)
    (ok : mask.testBit (block91 w x b)=true) :
    let result := advance91 w b x inj mask
    let f := result.1
    b-3 ≤ f ∧ f ≤ b+(w:Int)+1 ∧
    (∀ t, fits91 w b x mask t → ∀ j ≤ f,evolve91 t inj j=evolve91 x inj j) ∧
    (∃ t, fits91 w b x mask t ∧ evolve91 t inj (f+1)≠evolve91 x inj (f+1)) ∧
    ∀ val : Fin (2^w), result.2.testBit val.val=true ↔
      ∃ t, fits91 w b x mask t ∧ block91 w (evolve91 t inj) f=val.val := by
  let fix := fixed91 w b x inj mask
  let z := ((List.range (w+5)).takeWhile fix).length
  let f := b-3+(z:Int)
  obtain ⟨lim,stop,before⟩ := stop91 w fix (last91 ok)
  change z≤w+4 at lim
  change fix z=false at stop
  change ∀ j<z,fix j=true at before
  refine ⟨by change b-3≤f;dsimp [f];omega,by change f≤_;dsimp [f];omega,?_,?_,?_⟩
  · intro t ht j hj
    change j≤f at hj
    by_cases low : j≤b-3
    · exact evolveEq91 (fun p _ hp => ht.1 _ (by omega))
    · let off := (j-(b-2)).toNat
      have ho : off<z := by dsimp [off,f] at *;omega
      have e : b-2+(off:Int)=j := by dsimp [off];omega
      have eq := ((fixedIff91 (by omega : off≤w+4)).mp (before off ho)) t ht
      simpa only [e] using eq
  · have neg : ¬∀ t, fits91 w b x mask t →
        evolve91 t inj (b-2+(z:Int))=evolve91 x inj (b-2+(z:Int)) := by
      intro h
      have ff := (fixedIff91 lim).mpr h
      change fix z=true at ff
      rw [ff] at stop
      contradiction
    push Not at neg
    obtain ⟨t,ht,ne⟩ := neg
    refine ⟨t,ht,?_⟩
    change evolve91 t inj (f+1)≠evolve91 x inj (f+1)
    simpa only [show f+1=b-2+(z:Int) by dsimp [f];omega] using ne
  · intro v
    change ((tails91 w mask).foldl (fun a c=> a ||| ((1:Nat) <<< block91 w (evolve91 (trial91 b x c) inj) f)) 0).testBit v.val = true ↔ _
    rw [foldBits91]
    simp only [Nat.zero_testBit,Bool.false_eq_true,false_or]
    constructor
    · rintro ⟨p,hp,eq⟩
      exact ⟨_,trialFits91 hp,eq⟩
    · rintro ⟨t,ht,eq⟩
      refine ⟨_,codeMem91 ht,?_⟩
      apply Eq.trans _ eq
      apply block_congr_interval91
      intro j _ hj
      exact evolveEq91 (fun p _ hp => codeEq91 ht p (by dsimp [f] at hj;omega))

end PEqualNP.Outside.L_meta_25591_aux

open PEqualNP.Outside.L_meta_25591_aux in
theorem PEqualNP.Outside.L_meta_25591 : let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x injection : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (allowedMask : Nat) =>
  let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => allowedMask.testBit (pattern % 2^w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b-2+(offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)
∀ (w : Nat) (b : Int) (x inj : Int → Bool) (mask : Nat),
  mask.testBit (block w x b) = true →
  let next := advance w b x inj mask
  let f := next.1
  b-3 ≤ f ∧ f ≤ b+(w : Int)+1 ∧
    (∀ t : Int → Bool, fits w b x mask t → ∀ j ≤ f, evolve t inj j = evolve x inj j) ∧
    (∃ t : Int → Bool, fits w b x mask t ∧ evolve t inj (f+1) ≠ evolve x inj (f+1)) ∧
    (∀ value : Fin (2^w), next.2.testBit value.val = true ↔
      ∃ t : Int → Bool, fits w b x mask t ∧ block w (evolve t inj) f = value.val) := by
  exact exact91
