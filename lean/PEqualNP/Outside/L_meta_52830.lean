import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52830

open PEqualNP.CircuitLowerBounds
abbrev Row:=Fin 256
abbrev Wire:=Row → Bool
def bin (d a b:Nat):Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d:Nat):Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bin_comm_flip (d:Nat) (hd:d < 4) (a b:Nat):bin d a b = bin (flipOp d) b a:=by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma flipOp_lt {d:Nat} (hd:d < 4):flipOp d < 4:=by
  interval_cases d <;> decide
lemma testBit_bin (d a b r:Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r:=by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b:Nat) (ha:a < 2^256) (hb:b < 2^256):bin d a b < 2^256:=by
  have h1:∀ x y:Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256:=fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2:∀ x y:Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256:=fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3:∀ x y:Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256:=fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b:Nat) (ha:a.testBit 0 = false) (hb:b.testBit 0 = false) :
    (bin d a b).testBit 0 = false:=by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T:Nat):Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U:Finset Nat) (a b d:Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h:Live T k S):∀ a ∈ S, a ≠ 0:=by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩:=h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩:=h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h:Live T k S):S.card ≤ k + 1:=by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩:=h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩:=h
    have hu:bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht:=ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1:=Finset.card_insert_le a (insert b U)
    have h2:=Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h:Live T k S) {r s:Nat} (hd:T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s:=by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩:=h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩:=h
    obtain ⟨v, hv, hvd⟩:=ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha:a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire:=Bool × Nat
def swZero:SWire:=(false, 0)
def swFlip (a:SWire):SWire:=(!a.1, a.2)
def opIdx (s t:Bool):Nat:=if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b:SWire):SWire:=(a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b:SWire):SWire:=swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j:Nat) (a:SWire):Bool:=a.1 != a.2.testBit j
lemma swRead_zero (j:Nat):swRead j swZero = false:=by simp [swRead, swZero]
lemma swRead_flip (j:Nat) (a:SWire):swRead j (swFlip a) = !(swRead j a):=by
  cases a with | mk s v => cases s <;> cases h:v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j:Nat) (a b:SWire):swRead j (swMeet a b) = (swRead j a && swRead j b):=by
  obtain ⟨s, u⟩:=a; obtain ⟨t, v⟩:=b
  cases s <;> cases t <;> cases hu:u.testBit j <;> cases hv:v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j:Nat) (a b:SWire):swRead j (swJoin a b) = (swRead j a || swRead j b):=by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w:List SWire) (g:Gate):SWire :=
  let arg:=fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs:List Gate) (w:List SWire):List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g:Gate):Bool:=match g.op with | .not => false | _ => true
def reps (w:List SWire):List Nat:=w.map Prod.snd
def simple (w:List SWire) (z:Nat):Prop:=z = 0 ∨ z ∈ reps w
def priced (w:List SWire) (paid:Bool) (z:Nat):Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bin_eq_cases (d a b:Nat) (hd:d < 4) (h:a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b:=by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t:Bool):opIdx s t < 4:=by cases s <;> cases t <;> decide
lemma get_simple (w:List SWire) (i:Nat):simple w (w.getD i swZero).2:=by
  simp only [List.getD_eq_getElem?_getD]
  cases eq:w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma made_priced (w:List SWire) (d:Nat) (a b:SWire) (hd:d < 4)
    (pa:simple w a.2) (pb:simple w b.2):priced w true (bin d a.2 b.2):=by
  by_cases h:a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swGate_priced (w:List SWire) (g:Gate):priced w (isBin g) (swGate w g).2:=by
  obtain ⟨op, xs⟩:=g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w:List SWire) (hw:∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g:Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false:=by
  have hz:(0:Nat) < 2^256 ∧ (0:Nat).testBit 0 = false:=⟨by decide, by decide⟩
  have hg (i:Nat):(w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false:=by
    simp only [List.getD_eq_getElem?_getD]
    cases eq:w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩:=g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs:List Gate) (w:List SWire)
    (hw:∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false:=by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j:Nat) (w:List SWire) (i:Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero):=by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w:List SWire) (g:Gate)
    (legal:(g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j:Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false):=by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩:=g
  obtain ⟨hop, hlen⟩:=legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j:Nat) (gs:List Gate) (w:List SWire)
    (legal:∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h:Live T k S) (op:priced w p z)
    (sub:∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w:=by
  by_cases needed:z ∈ S
  · by_cases avail:z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha:a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U:=S.erase (bin d a b)
        have tail:Live T k (insert (bin d a b) U):=by
          simpa [U, Finset.insert_erase needed] using h
        have old (x:Nat) (hx:x ∈ U):x ∈ reps w:=by
          obtain ⟨ne, mem⟩:=Finset.mem_erase.mp hx
          exact (by simpa using sub x mem:x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh:bin d a b ∉ insert a (insert b U):=by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT:T ≠ 0) (gs:List Gate) (w:List SWire)
    (found:T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w:=by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩:=ih (w ++ [swGate w g]) found
    have sub':∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2]:=by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩:=pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e:isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a:Wire):Wire:=fun r => !(a r)
def comb2 (isOr:Bool) (a b:Wire):Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d:Nat) (a b:Wire):Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a:Wire):Prop:=∃ b:Bool, a = fun _ => b
noncomputable def wcost (a:Wire):Nat:=by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs:List Wire):Nat:=(xs.map wcost).sum
def Avail (pool:List Wire) (v:Wire):Prop:=v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs:List Wire):Prop:=∀ a ∈ xs, Avail pool a
def Reach (roots:List Wire):Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op:Bool) (bank:List Wire) (a b:Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α:Type} (save:Bool) (x:α) (xs:List α):List α:=if save then x :: xs else xs
def Run (goal:Wire):Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op:Nat) (ka kb:Bool) (a b:Wire) (rest:List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a:Wire):invW (invW a) = a:=by funext r; simp [invW]
lemma invW_const {a:Wire} (h:Constant a):Constant (invW a):=by
  obtain ⟨v, rfl⟩:=h; exact ⟨!v, rfl⟩
lemma wcost_inv (a:Wire):wcost (invW a) = wcost a:=by
  have h:Constant (invW a) ↔ Constant a:=⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc:Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank:List Wire} {a:Wire} (h:Avail bank a):Avail bank (invW a):=by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank:List Wire} {v:Wire} (w:Wire) (h:Avail bank v):Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op:Bool) {a b:Wire} {bank:List Wire} (h:Constant a ∨ Constant b)
    (ha:Avail bank a) (hb:Avail bank b):Avail bank (comb2 op a b):=by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op:Bool) {a b:Wire} (ha:Constant a) (hb:Constant b) :
    Constant (comb2 op a b):=by
  obtain ⟨v, rfl⟩:=ha; obtain ⟨w, rfl⟩:=hb; cases op <;> exact ⟨_, rfl⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma extend_comb (roots:List Wire) {p bank a b} (d:Nat) (hd:d < 4)
    (hp:Reach roots p bank) (ha:Avail bank a) (hb:Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b):=by
  have hprep:∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b:=by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩:=hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c:Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx:Constant x <;> by_cases hcy:Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx:¬Constant x:=fun h => c (Or.inl h)
    have hcy:¬Constant y:=fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a:Wire) (xs:List Wire) (k:Bool):wmass xs ≤ wmass (kept k a xs):=by
  cases k <;> simp [kept, wmass]
lemma contraction {goal:Wire} (nc:¬Constant goal) {s ws} (h:Run goal s ws)
    (roots:List Wire) {p bank} (hp:Reach roots p bank) (hs:Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s:=by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem:goal ∈ ws:=h.mem_iff.mp (by simp)
    have hlen:wmass ws = wcost goal:=by
      have:=(h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩:=h
    have hsa:Avail bank a:=hs a (perm.mem_iff.mp (by simp))
    have hsb:Avail bank b:=hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩:=extend_comb roots op hd hp hsa hsb
    have ht:Supply T (comb4 op a b :: kept ka a (kept kb b rest)):=by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩:=ih tail hT ht
    have hm1:=wmass_kept a (kept kb b rest) ka
    have hm2:=wmass_kept b rest kb
    have hp_eq:wmass ws = wcost a + wcost b + wmass rest:=by
      have:=(perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons:wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)):=rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f:Row → Row) (a:Wire):Wire:=fun r => a (f r)
lemma restrict_run (f:Row → Row) {goal s ws} (h:Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)):=by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩:=h
    have htail:=ih tail
    have hk:∀ (k:Bool) (x:Wire) (l:List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)):=by
      intro k x l; cases k <;> rfl
    have hc:restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b):=by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a:Nat):Wire:=fun r => a.testBit r.val
lemma obs_bin (d a b:Nat):obs (bin d a b) = comb4 d (obs a) (obs b):=by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α:Type} (c:Bool) (x:α) (l:List α) (hl:l.Nodup) (hx:x ∉ l) :
    (kept c x l).Nodup:=by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h:Live T k S) (v:List Nat) (nd:v.Nodup) (eqv:v.toFinset = S) :
    Run (obs T) k (v.map obs):=by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩:=h
    have hp:[T].Perm v:=List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩:=h
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tl:=kept ka a mid
    have er:rest.toFinset = (U.erase a).erase b:=by simp [rest]
    have ar:a ∉ rest:=by simp [rest]
    have br:b ∉ rest:=by simp [rest]
    have hr:rest.Nodup:=Finset.nodup_toList _
    have bm:mid.Nodup:=kept_nodup kb b rest hr br
    have am:a ∉ mid:=by cases hkb:kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl:tl.Nodup:=kept_nodup ka a mid bm am
    have htl:tl.toFinset = U:=by
      have kf (c:Bool) (x:Nat) (l:List Nat):(kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset:=by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha':a ∈ U <;> by_cases hb':b ∈ U <;> by_cases ja:j = a <;> by_cases jb:j = b <;>
        simp_all [ka, kb]
    have hf:bin d a b ∉ tl:=fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog:=ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk:∀ (c:Bool) (x:Nat) (l:List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs):=by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm:(a :: b :: rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja:j = a <;> by_cases jb:j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f:Wire):Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r:Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f:Wire) (r:Nat) :
    (normPack f).testBit r = if h:r < 256 then (f ⟨r, h⟩ != f 0) else false:=by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r:Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h:r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a:Nat} (ha:a < 2^256) (h0:a.testBit 0 = false) :
    normPack (obs a) = a:=by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr:r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f:Wire):normPack (invW f) = normPack f:=by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr:r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f:Wire} (h:Constant f):normPack f = 0:=by
  obtain ⟨b, rfl⟩:=h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr:r < 256 <;> simp [hr]
lemma normPack_comb2 (op:Bool) (a b:Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b):=by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr:r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0:a 0 <;> cases hb0:b 0 <;>
      cases har:a ⟨r, hr⟩ <;> cases hbr:b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank:List Wire} {v:Wire} (h:Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack:=by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma reach_to_live_sub {roots:List Wire} {p bank} (h:Reach roots p bank)
    {T k S} (run:Live T k S) (sub:∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack:=by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩:=h
    obtain ⟨d, hd, eq⟩:=normPack_comb2 op a b
    let w:=prev.map (fun f => (false, normPack f))
    have hreps:reps w = prev.map normPack:=by simp [w, reps, List.map_map, Function.comp_def]
    have hp:priced w true (normPack (comb2 op a b)):=by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub':∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)]:=by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩:=pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩:=ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots:List Nat) (T:Nat) (L:Nat):Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T:Nat) (cap:Nat) (S:Finset Nat):Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T:Nat) (roots:List Nat) (a:Nat):Prop :=
  ∃ r s:Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h:Live T k S) (roots:List Nat) (a:Nat)
    (sub:∀ v ∈ S, v ∈ roots) (he:Essential T roots a):a ∈ S:=by
  obtain ⟨r, s, hd, hiso⟩:=he
  obtain ⟨v, hv, hvd⟩:=live_sep h hd
  by_cases veq:v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower_of_impossible {roots:List Nat} {T L:Nat}
    (hT0:T ≠ 0) (hTlt:T < 2^256) (hTb0:T.testBit 0 = false)
    (hR:∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (ess:∀ a ∈ roots, Essential T roots a)
    (noRun:Impossible T L roots.toFinset):Lower roots T (L + 1):=by
  intro p bank hr ha
  have hnormT:normPack (obs T) = T:=normPack_eq_of_obs hTlt hTb0
  have hnz:normPack (obs T) ≠ 0:=by rwa [hnormT]
  have hm:T ∈ bank.map normPack:=by
    have h1:=(avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩:=reach_to_live_sub hr (T:=T) (k:=0) (S:={T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap:(roots.map obs).map normPack = roots:=by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq:roots.toFinset = S:=by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T:Nat} (hT0:T ≠ 0) (hTlt:T < 2^256) (hTb0:T.testBit 0 = false) :
    ¬Constant (obs T):=by
  intro hc
  have h:=normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw:List Nat) (T d:Nat) (L:Nat):Prop :=
  ∃ (f:Row → Row) (roots:List Nat),
    (∀ r:Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a:Nat):Bool:=(a &&& d == 0) || (a &&& d == d)
def availM (d:Nat) (pm:List Nat) (a:Nat):Bool :=
  let m:=a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f:Row → Row} {d a b:Nat} (dom:∀ r:Row, d.testBit (f r).val = true)
    (eq:(a &&& d) = (b &&& d)):restrictW f (obs a) = restrictW f (obs b):=by
  funext r
  have h:=congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f:Row → Row} {d a:Nat} (dom:∀ r:Row, d.testBit (f r).val = true)
    (eq:(a &&& d) = 0):restrictW f (obs a) = fun _ => false:=by
  funext r
  have h:=congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f:Row → Row} {d a:Nat} (dom:∀ r:Row, d.testBit (f r).val = true)
    (eq:(a &&& d) = d):restrictW f (obs a) = fun _ => true:=by
  funext r
  have h:=congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f:Row → Row} {d a b:Nat} (dom:∀ r:Row, d.testBit (f r).val = true)
    (eq:(a &&& d) = (d ^^^ (b &&& d))):restrictW f (obs a) = invW (restrictW f (obs b)):=by
  funext r
  have h:=congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f:Row → Row) (bank:List Wire) (pool:List Nat):Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f:Row → Row} {d a:Nat} {bank:List Wire} {pool:List Nat}
    (dom:∀ r:Row, d.testBit (f r).val = true)
    (hs:poolSupply f bank pool)
    (ok:availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)):=by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv:=avail_inv (hs v hv)
    have hcomp:restrictW f (obs a) = invW (restrictW f (obs v)):=by
      have hx:(a &&& d) = d ^^^ (v &&& d):=by
        have:=congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice:=Nat × Nat × Nat
def choiceVal (c:Choice):Nat:=bin c.1 c.2.1 c.2.2
def choiceOK (d:Nat) (pm:List Nat) (c:Choice):Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d:Nat) (pool:List Nat):List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma pay_choice {f:Row → Row} {d:Nat} {roots bank q} {pool:List Nat}
    (dom:∀ r:Row, d.testBit (f r).val = true)
    (hp:Reach roots q bank) (hs:poolSupply f bank pool)
    (c:Choice) (valid:choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool):=by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha:=availM_sound dom hs valid.1.2
  have hb:=availM_sound dom hs valid.2
  have hprep:∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y:=by
    have hd:=valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩:=hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv:restrictW f (obs (choiceVal c)) = comb2 op x y:=by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d:Nat} {f:Row → Row} (dom:∀ r:Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp:Reach roots q bank) (hs:poolSupply f bank pool)
    (cs:List Choice) {res} (ok:makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩:=pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩:=ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d:Nat} {f:Row → Row} (dom:∀ r:Row, d.testBit (f r).val = true)
    (ws:List Nat):ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)):=by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h:isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc:Constant (restrictW f (obs a)):=by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom:Nat
  lb:Nat
  paid:Nat
  wires:List Nat
  pm:List Nat
def ValidPool (_raw:List Nat) (T:Nat) (c:BoundPool):Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f:Row → Row) (roots:List Nat) (bank:List Wire),
    (∀ r:Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw:List Nat) (cs:List Choice) (d lb:Nat):Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl:Slice raw T d L)
    (h:materialize raw cs d L = some c):ValidPool raw T c:=by
  unfold materialize at h
  cases he:makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩:=sl
    obtain ⟨bank, hr, hs⟩:=makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c:BoundPool) (k:Nat) (rest:List Nat) (op:Choice):Bool :=
  let z:=choiceVal op
  let extra:=!(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid:ValidPool raw T c) {k rest op}
    (nd:(choiceVal op :: rest).Nodup) (cut:scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩:=valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n:Nat) (out:List Wire) (hr:Reach (roots.map obs) n out)
      (hsup:poolSupply f out (choiceVal op :: rest))
      (hle:n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat):False:=by
    have hcov:Supply out (((choiceVal op :: rest).map obs).map (restrictW f)):=by
      intro v hv
      obtain ⟨_, hm, rfl⟩:=List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩:=List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo:=lo q next hq hav
    have hcm:=count_constM dom (choiceVal op :: rest)
    have hineq:=cut.1.1
    omega
  cases hav:availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok:choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true:=by
      have h2:=cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩:=pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt:poolSupply f out c.wires:=fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o:Nat) (r:Row):Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f:Row → Row) (a:Nat):Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r:Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f:Row → Row) (a:Nat) (r:Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val:=by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r:Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f:Row → Row) (a:Nat):renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r:Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f:Row → Row) (a:Nat):obs (renameW f a) = restrictW f (obs a):=by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f:Row → Row) (d a b:Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b):=by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr:r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x:Nat):(renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f:Row → Row):renameW f 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr:r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:256 ≤ r)))
lemma renameW_inj (f:Row → Row) (onto:Function.Surjective f) {a b:Nat}
    (ha:a < 2^256) (hb:b < 2^256) (eq:renameW f a = renameW f b):a = b:=by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr:r < 256
  · obtain ⟨q, hq⟩:=onto ⟨r, hr⟩
    have h:=congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge:256 ≤ r:=by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide:0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide:0 < 2) hge))]
lemma live_renameW {T k S} (h:Live T k S) (hS:∀ a ∈ S, a < 2^256) (f:Row → Row)
    (onto:Function.Surjective f):Live (renameW f T) k (S.image (renameW f)):=by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩:=h
    have hTlt:T < 2^256:=hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩:=h
    have halt:a < 2^256:=hS a (by simp)
    have hblt:b < 2^256:=hS b (by simp)
    have hUlt:∀ x ∈ U, x < 2^256:=fun x hx => hS x (by simp [hx])
    have hzlt:bin d a b < 2^256:=bin_lt d a b halt hblt
    have htail_lt:∀ x ∈ insert (bin d a b) U, x < 2^256:=by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr:=ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩:=Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b:List Wire):wmass (a ++ b) = wmass a + wmass b:=by simp [wmass]
lemma wmass_consts (xs:List Wire) (hc:∀ x ∈ xs, Constant x):wmass xs = xs.length:=by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have:=ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower_slice {roots other:List Nat} {T G:Nat}
    (hT0:T ≠ 0) (hTlt:T < 2^256) (hTb0:T.testBit 0 = false)
    (hR:∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0:G ≠ 0) (hGlt:G < 2^256) (hGb0:G.testBit 0 = false)
    (f:Row → Row) (eq:renameW f T = G)
    (covered:∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles:Finset Nat) (necessary:∀ a ∈ singles, Essential T roots a)
    (constant:∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L:Nat) (prior:Lower other G L):Lower roots T (L + singles.card):=by
  classical
  intro p bank hr ha
  have hnormT:normPack (obs T) = T:=normPack_eq_of_obs hTlt hTb0
  have hm:T ∈ bank.map normPack:=by
    have h1:=(avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩:=reach_to_live_sub hr (T:=T) (k:=0) (S:={T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap:(roots.map obs).map normPack = roots:=by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS:singles ⊆ S:=fun a hs => raw_required run roots a sub (necessary a hs)
  let front:=singles.toList ++ (S \ singles).toList
  have nd:front.Nodup:=by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe:front.toFinset = S:=by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc:restrictW f (obs T) = obs G:=(obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup:Supply (other.map obs) ((front.map obs).map (restrictW f)):=by
    intro v hv
    obtain ⟨_, hm', rfl⟩:=List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩:=List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo:=prior q next hq (gc ▸ hav)
  have hmass:singles.card ≤ wmass ((front.map obs).map (restrictW f)):=by
    simp only [front, List.map_append, wmass_append]
    let xs:=(singles.toList.map obs).map (restrictW f)
    have hc:∀ v ∈ xs, Constant v:=by
      intro v hv
      obtain ⟨_, hm', rfl⟩:=List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩:=List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen:=wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have:=hbound
  omega
def VAR (i:Nat):Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j:Nat) (r:Row):Row :=
  let bi:=r.val.testBit i
  let bj:=r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j:Nat) (w:Nat):Nat :=
  let a:=VAR i
  let b:=VAR j
  let m10:=a ^^^ (a &&& b)
  let m01:=b ^^^ (a &&& b)
  let msame:=ALL256 ^^^ (m10 ||| m01)
  let d:=(1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps:List (Nat × Nat)) (r:Row):Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps:List (Nat × Nat)) (w:Nat):Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapRow_invol (i j:Nat) (hi:i < 8) (hj:j < 8) (r:Row) :
    swapRow i j (swapRow i j r) = r:=by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapWord_testBit (i j:Nat) (hij:i < j) (hj:j < 8) (w:Nat) (hw:w < 2^256) (r:Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val:=by
  have hi:i < 8:=by omega
  have hspec:∀ r:Row,
      let a:=VAR i; let b:=VAR j
      let m10:=a ^^^ (a &&& b); let m01:=b ^^^ (a &&& b); let msame:=ALL256 ^^^ (m10 ||| m01)
      let d:=(1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)):=by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr:=hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms:(ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩:=hr.1 hms
    rw [heq]
    by_cases hd:(1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd:(1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapWord_lt (i j:Nat) (hij:i < j) (hj:j < 8) (w:Nat):swapWord i j w < 2^256:=by
  have hi:i < 8:=by omega
  have h1:(ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256:=by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2:((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256:=by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3:((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256:=by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1:(w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2:((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256:=by
    have hle:(w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)):=Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)):=Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)):=Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))):=(Nat.shiftLeft_eq _ _).symm
      _ < 2^256:=h2
  have e3:((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256:=by
    have hle:(w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)):=Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)):=Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)):=Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))):=(Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256:=h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j:Nat) (hij:i < j) (hj:j < 8) (w:Nat) (hw:w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w:=by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr:r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps:List (Nat × Nat)):Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps:List (Nat × Nat)) (hv:swapsValid swaps = true)
    (w:Nat) (hw:w < 2^256):permWord swaps w = renameW (permRow swaps) w:=by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr:r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw:=ih hv.2 w hw
    have hlt:permWord ps w < 2^256:=ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr:r < 256
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps:List (Nat × Nat)) (hv:swapsValid swaps = true) :
    Function.Surjective (permRow swaps):=by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩:=ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps:List (Nat × Nat)) (hv:swapsValid swaps = true) (r:Row) :
    permRow swaps.reverse (permRow swaps r) = r:=by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1:permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))):=by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n:Nat} {ws:List Nat} (hi:Impossible T n ws.toFinset)
    (swaps:List (Nat × Nat)) (hv:swapsValid swaps = true)
    (hT:T < 2^256) (hfix:permWord swaps T = T)
    (hw:∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset:=by
  intro k hk run
  have hr:∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256:=by
    intro a ha
    obtain ⟨x, hx, rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr:swapsValid swaps.reverse = true:=by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2:∀ r:Row, permRow swaps (permRow swaps.reverse r) = r:=by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word:∀ x:Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x:=by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr:r < 256
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run':=live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT':renameW (permRow swaps.reverse) T = T:=by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS':(ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset:=by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor:=Nat × Nat × Nat
def dbin (d:Nat) (x y:Decor):Decor:=(bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x:Decor):Nat:=x.2.1 ^^^ x.2.2
def projBits (rows:List Nat) (w:Nat):Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows:List Nat) (w i:Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r:=by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide:0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0:(if w.testBit r then (1:Nat) else 0).testBit (i + 1) = false:=by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide:1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows:List Nat) (d a b:Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b):=by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg:List Nat) (x:Decor):Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d:Nat) (hx:faithful pos neg x) (hy:faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T:Nat) (pos neg:List Nat):Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n:Nat):Nat:=(1 <<< n) - 1
abbrev Cov:=Nat × Nat × Nat
def addCov (z:Nat) (c:Cov):Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v:List Decor):Cov:=v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c:Cov) (a:Nat):Nat:=c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c:Cov) (a b:Nat):Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c:Cov) (a:Nat):takeOne (addCov a c) a = c.1:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c:Cov) (a b:Nat):takeTwo (addCov a (addCov b c)) a b = c.1:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c:Cov) (a b:Nat):addCov a (addCov b c) = addCov b (addCov a c):=by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r:List Decor} (h:l.Perm r):coverage l = coverage r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws:List Decor) (a:Decor) (k:Bool):List Decor:=if k then ws else ws.erase a
def delTwo (ws:List Decor) (a b:Decor) (ka kb:Bool):List Decor:=delOne (delOne ws a ka) b kb
def restCov (c:Cov) (a b:Nat) (ka kb:Bool):Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws:List Decor} (a:Decor) (ha:a ∈ ws) (k:Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a):=by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws:List Decor} (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a ≠ b) (ka kb:Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb:=by
  cases ka <;> cases kb
  · have hbm:b ∈ ws.erase a:=(List.mem_erase_of_ne ne.symm).mpr hb
    have hp:ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws:List Decor) (i:Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true:=by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws:List Decor}
    (gp:goodPairs T pos neg) (hf:∀ x ∈ ws, faithful pos neg x)
    (h:Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length:=by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm:(fullMask pos.length).testBit i = decide (i < pos.length):=by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi:i < pos.length
  · have ⟨hp, hn⟩:=gp.2 i hi
    have hsep:T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0):=by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩:=live_sep h hsep
    obtain ⟨x, hx, rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx:=hf x hx
    have hpi:pos[i]? = some (pos.getD i 0):=by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni:neg[i]? = some (neg.getD i 0):=by
      have hi':i < neg.length:=gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit:(dsep x).testBit i = true:=by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12:x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0):=by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1:x.1.testBit (pos.getD i 0) <;> cases h2:x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc:=(cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a:Nat):List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats:List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a:Nat) (l:List Nat):(insertNat a l).Perm (a :: l):=by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h:a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l:List Nat):(sortNats l).Perm l:=by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l:List Nat):(sortNats l).toFinset = l.toFinset:=by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws:List Nat) (a b d:Nat) (ka kb:Bool):List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l:List Nat} (nd:l.Nodup) (a:Nat) :
    (l.erase a).toFinset = l.toFinset.erase a:=by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap:Nat} {ws:List Nat} (nd:ws.Nodup) (out:T ∉ ws)
    (stepOK:∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb:Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩:=h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩:=h
    have am:a ∈ ws:=List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm:b ∈ ws:=List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh:bin d a b ∉ ws:=fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz:bin d a b ≠ 0:=live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er:rest.toFinset = (ws.toFinset.erase a).erase b:=by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c:Bool) (x:Nat) (l:List Nat):(kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset:=by
      cases c <;> simp [kept]
    have ke:(kept ka a (kept kb b rest)).toFinset = U:=by
      rw [kf, kf, er, he]; ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases ja:j = a <;> by_cases jb:j = b <;> simp_all [ka, kb]
    have rn:rest.Nodup:=(nd.erase _).erase _
    have ar:a ∉ rest:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br:b ∉ rest:=(nd.erase a).not_mem_erase
    have nk:=kept_nodup kb b rest rn br
    have ax:a ∉ kept kb b rest:=by cases kb <;> simp [kept, ar, hab]
    have ndc:(childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc:(childTwo ws a b d ka kb).toFinset = insert (bin d a b) U:=by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc:=live_size tail
    have hlen:(childTwo ws a b d ka kb).length ≤ cap:=by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws:List Decor) (a:Decor) (k:Bool):(delOne ws a k).Sublist ws:=by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws:List Decor) (a b:Decor) (ka kb:Bool):(delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws:List Decor) (a b:Decor) (ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1):=by
  have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
    (ha:a ∈ ws) (hb:b ∈ ws) (eq:a.1 = b.1):a = b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
    (ha:a ∈ ws) (hb:b ∈ ws) (ne:a.1 ≠ b.1) (d:Nat) (ka kb:Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  have wn:ws.Nodup:=nd.of_map
  have dn:(delOne ws a ka).Nodup:=wn.sublist (delOne_sub ws a ka)
  have m1 (l:List Decor) (hl:l.Nodup) (x y:Decor) (c:Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true):=by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v:Nat):v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true):=by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  have hkeep (c:Bool) (x:Nat) (l:List Nat) (v:Nat):v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l:=by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va:v = a.1 <;> by_cases vb:v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v:List Nat) (nd:v.Nodup) (a b:Nat) (d:Nat) (hd:d < 4) (ka kb:Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset:=by
  have hkeep (c:Bool) (x:Nat) (l:List Nat) (y:Nat):y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l:=by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m:Nat):List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o:Nat):Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w:Nat):Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr:=((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p:Nat → Bool) (l:List Nat) (r:Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r):=by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa:p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra:r = a
      · subst hra; simp [hpa]
      · have h1:(decide (a ≤ r) && (1:Nat).testBit (r - a)) = false:=by
          by_cases hle:a ≤ r
          · have hpos:r - a ≠ 0:=by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide:1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf:p a = false:=Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra:r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w:Nat):fixWord z o w = renameW (fixRow z o) w:=by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr:r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma subcube_fixRow (z o:Nat) (hz:z < 256) (ho:o < 256) (hzo:(z &&& o) = 0) (r:Row) :
    (subcube z o).testBit (fixRow z o r).val = true:=by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem:(fixRow z o r).val ∈ List.range 256:=List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127:((r.val &&& (255 ^^^ z)) ||| o) < 256:=by
    have hr:=r.isLt
    have hlt1:(r.val &&& (255 ^^^ z)) < 256:=Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n:=8) hlt1 ho
  have hval:(fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o):=Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi:(z.testBit i && o.testBit i) = false:=by
      have:=congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi:i < 8
    · have h7:(255:Nat).testBit i = true:=by interval_cases i <;> decide
      cases hzb:z.testBit i <;> cases hob:o.testBit i <;> simp_all [h7]
    · have hzf:z.testBit i = false:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T:Nat) (roots:List Nat) (a r s:Nat):Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h:checkEss1 T roots a r s = true):Essential T roots a:=by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other:List Nat) (w:Nat):Bool:=w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other:List Nat} {f:Row → Row} {a:Nat} (ok:freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)):=by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have:=r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w:Nat):Bool:=w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w:Nat} (h:checkProper w = true):w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false:=by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs:List Nat):Bool:=rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs:List Nat} (h:checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false:=by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps:List (Nat × Nat)) (roots1:List Nat) (T1:Nat) (roots2:List Nat) (T2:Nat):Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok:carryOK swaps roots1 T1 roots2 T2 = true)
    (hL:Lower roots2 T2 L):Lower roots1 T1 L:=by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩:=ok
  have ⟨p1a, p1b, p1c⟩:=checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩:=checkProper_sound hT2
  have hR1':=checkRoots_sound hR1
  have heq':renameW (permRow swaps) T1 = T2:=(permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov':∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)):=fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o:Nat) (roots:List Nat) (T:Nat) (other:List Nat) (G:Nat)
    (essPairs:List (Nat × Nat × Nat)):Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of {z o roots T other G essPairs L} (ok:liftCheck z o roots T other G essPairs = true)
    (hL:Lower other G L):Lower roots T (L + essPairs.length):=by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩:=ok
  have ⟨p1a, p1b, p1c⟩:=checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩:=checkProper_sound hG
  have hR':=checkRoots_sound hR
  have heq':renameW (fixRow z o) T = G:=(fixWord_eq_renameW z o T).symm.trans heq
  have hcov':∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)):=fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard:(essPairs.map Prod.fst).toFinset.card = essPairs.length:=by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc:=(hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have:=r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T:Nat) (pos neg:List Nat):Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok:goodPairsCheck T pos neg = true):goodPairs T pos neg:=by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T:Nat) (autos:List (List (Nat × Nat))):Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok:autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T:=by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg:List Nat) (base:List Decor):Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok:baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256:=by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h:=ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots:List Nat) (T:Nat) (essPairs:List (Nat × Nat × Nat)):Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg:List Nat):faithful pos neg (0, 0, 0):=by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α:Type} {P:α → Prop} {a:α} {l:List α} (ha:P a) (hl:∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x:=by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec:=Nat × List (Nat × Nat × Nat)
abbrev NodeSpec:=List Nat × List Nat × List Nat
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma var_testBit (i:Fin 8) (r:Row):(VAR i.val).testBit r.val = r.val.testBit i.val:=by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead:Nat) (raw:List Nat) (T:Nat) (qRoots:List Nat) (qGoal:Nat):Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    decide (zDead < 256) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead:Nat) (hz:z < 256) (hd:zDead < 256) (ho:o < 256)
    (hzo:((z ||| zDead) &&& o) = 0) (r:Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true:=by
  have hsub:=subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n:=8) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa:(fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb:z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok:sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior:Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL:=by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩:=ok
  have ⟨g0, glt, gb0⟩:=checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
inductive BT (α:Type) where
  | empty:BT α
  | leaf:α → BT α
  | node:BT α → BT α → BT α
def btGet {α:Type} (d:α):BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α:Type}:Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α:Type} (d0:α):Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α:Type} (P:α → Prop):BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α:Type} {P:α → Prop} {d:α} {t:BT α} (ht:btAll P t) (hd:P d) (i:Nat) :
    P (btGet d t i):=by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α:Type} {P:α → Prop} {depth:Nat} {t:BT α} {i:Nat} {v:α}
    (ht:btAll P t) (hv:P v):btAll P (btSet depth t i v):=by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α:Type} {P:α → Prop} {d0:α} {depth:Nat} {t:BT α} {i:Nat} {f:α → α}
    (ht:btAll P t) (hd0:P d0) (hf:∀ x, P x → P (f x)):btAll P (btUpdate d0 depth t i f):=by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α:Type} (depth:Nat) (l:List α):BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α:Type} {P:α → Prop} {depth:Nat} {l:List α}
    (h:∀ x ∈ l, P x):btAll P (btOfList depth l):=by
  unfold btOfList
  have hgo:∀ (xs:List α) (acc:Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2:=by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i:Nat):Nat :=
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o:Nat):Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i:Nat) (hi:i < 8) (r:Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true):=by
  have hall:ALL256.testBit r.val = true:=by
    simp only [ALL256]; have hr:=r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar:(VAR i).testBit r.val = r.val.testBit i:=var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma subcubeFast_eq_subcube (z o:Nat) (hz:z < 256) (ho:o < 256) (hzo:(z &&& o) = 0) :
    subcubeFast z o = subcube z o:=by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr:r < 256
  · have hsub:(subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)):=by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i:Nat) (hi:i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true:=by
      have hzi:(z.testBit i && o.testBit i) = false:=by
        have:=congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz':z.testBit i <;> cases ho':o.testBit i <;> cases hr':r.testBit i <;> simp_all
    have heq_iff:(((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i:=by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi:i < 8
          · exact (h i hi).1
          · have hzf:z.testBit i = false:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi:i < 8
          · exact (h i hi).2
          · have hof:o.testBit i = false:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide:0 < 2) (by omega:8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have:=hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩,
        (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i:Nat):(fastBitMask z o i).testBit r = false:=by
      have hle:256 ≤ r:=by omega
      have ha:ALL256 < 2^256:=by decide
      have hv:VAR i < 2^256:=by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0:Nat) < 2^256; decide
      have hlt_m:fastBitMask z o i < 2^256:=by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide:0 < 2) hle))
    have hsub:(subcube z o).testBit r = false:=by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok:sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior:Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL:=by
  have ok2:=ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws:List Nat):Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks:BT (List (List Nat))) (ws:List Nat):Bool :=
  let s:=sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools:List BoundPool) (autos:List (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))) (k:Nat) (rest:List Nat) (op:Choice):Bool :=
  let ws:=choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT:T < 2^256)
    (hPools:∀ c ∈ pools, ValidPool raw T c)
    (hAutos:∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev:btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd:(choiceVal op :: rest).Nodup)
    (hlt:∀ x ∈ choiceVal op :: rest, x < 2^256)
    (h:closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem:=List.contains_iff_mem.mp hhit
    have hb:∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp:=hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩:=hAutos sw hsw
    have hvr:swapsValid sw.reverse = true:=by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen:∀ (l:List (Nat × Nat)), swapsValid l = true →
        ∀ r:Row, permRow l.reverse (permRow l r) = r:=by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1:permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))):=by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2:∀ r:Row, permRow sw (permRow sw.reverse r) = r:=by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w:∀ x:Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x:=by
      intro x hx
      have h1:=permWord_eq_renameW sw hsv x hx
      have h2:=permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr:r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide:0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide:0 < 2) (by omega)))]
    have hfixr:permWord sw.reverse T = T:=by
      have:=hinv_w T hT; rwa [hfix] at this
    have hmap_lt:∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256:=by
      intro a ha
      obtain ⟨x, hx, rfl⟩:=List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot:=rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback:(((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest):=by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool:=BoundPool × List Nat × Nat
def prepPool (vals:List Nat) (c:BoundPool):Option FastPool :=
  let miss:=vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp:FastPool) (k:Nat) (a b d:Nat) (ka kb:Bool):Bool :=
  let c:=fp.1
  let miss:=fp.2.1
  let totC:=fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA:=if !ka && isConstM c.dom a then 1 else 0
    let dropB:=if !kb && isConstM c.dom b then 1 else 0
    let z:=bin d a b
    let cRest:=totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn:=availM c.dom c.pm z
    let extra:=if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α:Type} [BEq α] [LawfulBEq α] (p:α → Bool) {l:List α} {x:α} (hx:x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p:=by
  have hp:=List.perm_cons_erase hx
  have h1:=List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p:Nat → Bool) {ws:List Decor} {a b:Decor}
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws) (hab:a.1 ≠ b.1) (ka kb:Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0):=by
  have hne:a ≠ b:=fun e => hab (congrArg Prod.fst e)
  have hmap_erase:∀ (l:List Decor) (x:Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1:=by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx:y = x
      · subst hyx; simp
      · have hne1:y.1 ≠ x.1:=by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1:(y == x) = false:=beq_false_of_ne hyx
        have h2:(y.1 == x.1) = false:=beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm:b ∈ ws.erase a:=(List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1:((ws.erase a).map Prod.fst).Nodup:=((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1:a.1 ∈ ws.map Prod.fst:=List.mem_map_of_mem ha
    have hb1:b.1 ∈ (ws.map Prod.fst).erase a.1:=(List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1:=countP_erase p ha1
    have c2:=countP_erase p hb1
    cases hpa:p a.1 <;> cases hpb:p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1:=countP_erase p (List.mem_map_of_mem (f:=Prod.fst) ha)
    cases hpa:p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1:=countP_erase p (List.mem_map_of_mem (f:=Prod.fst) hb)
    cases hpb:p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP:ValidPool raw T c) (hprep:prepPool (ws.map Prod.fst) c = some fp)
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws) (hab:a.1 ≠ b.1)
    (ndc:(bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut:fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset:=by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub:=(delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail:((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true:=by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf:availM c.dom c.pm w = false:=Bool.eq_false_iff.mpr hna
        have hmem_ws:w ∈ ws.map Prod.fst:=hsub.subset hw
        have hm:=hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab:a ≠ b:=fun e => hab (congrArg Prod.fst e)
        have hnot_in:∀ (x:Decor) (kx:Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True:=fun _ _ _ _ _ => trivial
        have hmem_del:∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b):=by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1:(delTwo ws a b false kb).Sublist (ws.erase a):=by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1:=hsub1.subset hu
            intro heq; subst heq
            have hnd_ws:ws.Nodup:=List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws:ws.Nodup:=List.Nodup.of_map Prod.fst nd
            have hnd2:(delOne ws a ka).Nodup:=by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2:=List.Nodup.not_mem_erase hnd2 (a:=b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩:=List.mem_map.mp hw
        have ⟨hna', hnb'⟩:=hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq:u = a:=unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq:u = b:=unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt:=countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op:=(d, a.1, b.1)) (rest:=(delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz:availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz:isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz:availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat)))
    (prevBks:BT (List (List Nat)))
    (d:Nat) (a b z:Decor) (ka kb:Bool):Bool :=
  let len:=1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs:=restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest:=(delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))) (a b:Decor) (d:Nat):Bool :=
  let z:=dbin d a b
  let go:=evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))):List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT:T < 2^256) (gp:goodPairs T pos neg) (hf:∀ w ∈ ws, faithful pos neg w)
    (nd:(ws.map Prod.fst).Nodup) (hlt:∀ w ∈ ws, w.1 < 2^256)
    (ha:a ∈ ws) (hb:b ∈ ws) (ne:a ≠ b) (hcap:0 < cap) (_hd:d < 4)
    (hPools:∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos:∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev:btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz:bin d a.1 b.1 ≠ 0) (hfr:bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test:evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset:=by
  let z:=dbin d a b
  let rest:=delTwo ws a b ka kb
  let child:=(z :: rest).map Prod.fst
  have sub:rest.Sublist ws:=delTwo_sub ws a b ka kb
  have ndc:child.Nodup:=by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc:∀ x ∈ child, x < 2^256:=by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩:=List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b:(z.1 == 0) = false:=beq_false_of_ne hnz
  have hfr_b:(ws.any (fun v => v.1 == z.1)) = false:=by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩:=List.any_eq_true.mp h
    have hvz:v.1 = bin d a.1 b.1:=beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq:1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length:=by
    have hdl:=delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz:=live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen:child.length ≤ cap:=by omega
  have hcov:=cov_required gp (ws:=z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq:(coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z:=by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b:(((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false:=by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt:¬(child.length > cap):=by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1:a.1 ≠ b.1:=fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp:fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩:=List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩:=hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f:fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false:=Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw:=raw) (op:=(d, a.1, b.1)) (rest:=rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h:testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b:Decor} (ha:a ∈ l) (hb:b ∈ l) (ne:a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true):=by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm:=(List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT:T < 2^256) (gp:goodPairs T pos neg)
    (hf:∀ w ∈ ws, faithful pos neg w) (nd:(ws.map Prod.fst).Nodup)
    (hlt:∀ w ∈ ws, w.1 < 2^256) (out:T ∉ ws.map Prod.fst)
    (hPools:∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos:∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev:btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks:cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0:k = 0:=by omega
    subst hk0
    obtain ⟨hS, _⟩:=h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0:cap = 0
  · subst h0
    intro k hk h
    have hk0:k = 0:=by omega
    subst hk0
    obtain ⟨hS, _⟩:=h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap:0 < cap:=by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩:=List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩:=List.mem_map.mp hb
  have ab:a ≠ b:=fun e => ne (congrArg Prod.fst e)
  have one (x y:Decor) (d':Nat) (hd':d' < 4) (hx:x ∈ ws) (hy:y ∈ ws) (nxy:x.1 ≠ y.1)
      (k1 k2:Bool) (hnz':bin d' x.1 y.1 ≠ 0) (hfr':bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht:testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset:=by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem:evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true:=by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl:=flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth:Nat) (base:List Decor) (steps:List (Nat × Nat × Nat)):BT Decor :=
  let init:=(base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a:=btGet (0, 0, 0) p.2 s.2.1
    let b:=btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase:∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps):=by
  have hdef:faithful pos neg (0, 0, 0) ∧ (0:Nat) < 2^256:=⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base):=btAll_ofList hbase
  have hgo:∀ (ss:List (Nat × Nat × Nat)) (acc:Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2:=by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha:=btAll_get hacc hdef s.2.1
      have hb:=btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth:Nat) (W:BT Decor) (raw:List Nat) (slices:BT (Option (Nat × Nat)))
    (pspecs:List PoolSpec):BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs:=chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W:BT Decor} {raw T} {slices:BT (Option (Nat × Nat))} {pspecs:List PoolSpec}
    (hSlices:btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs):=by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩:=List.mem_map.mp ho
  dsimp only at hmat
  have hsl:=btAll_get (d:=none) hSlices (fun _ h => by simp at h) slIdx
  cases heq:btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W:BT Decor) (T fmask:Nat)
    (poolTable:BT (Option BoundPool)) (autosTable:BT (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))) (k:Nat) (ns:NodeSpec):Bool :=
  let ws:=ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals:=ws.map Prod.fst
  let fpools:=ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos:=ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W:BT Decor) (T fmask:Nat)
    (poolTable:BT (Option BoundPool)) (autosTable:BT (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))) (k:Nat) (nodes:List NodeSpec):Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W:BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT:T < 2^256) (gp:goodPairs T pos neg)
    (hW:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable:btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos:btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev:btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok:checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset):=by
  have hdef:faithful pos neg (0, 0, 0) ∧ (0:Nat) < 2^256:=⟨faithful_zero pos neg, by decide⟩
  have hget (idx:Nat):faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws:=ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap:ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1:=by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩:=List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩:=List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩:=List.mem_filterMap.mp hfp
      cases heq:btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc:=btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq:fp.1 = c:=by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩:=List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W:BT Decor) (ns:NodeSpec):List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W:BT Decor) (nodes:List NodeSpec):BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs:=nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W:BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes:List NodeSpec}
    (hT:T < 2^256) (gp:goodPairs T pos neg)
    (hW:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable:btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos:btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev:btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes:checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes):=by
  have hmem:∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset:=fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit:btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty:BT (List (List Nat))):=trivial
  generalize (BT.empty:BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks:BT (List (List Nat))} {essPairs:List (Nat × Nat × Nat)}
    (ok:forestRootCheck roots T essPairs = true)
    (hTop:btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot:bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1):=by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩:=ok
  have ⟨p1, p2, p3⟩:=checkProper_sound hT
  have hR':=checkRoots_sound hR
  have hEss':∀ a ∈ roots, Essential T roots a:=fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩:=hess a ha
    exact checkEss1_sound he
  have hImp:Impossible T cap (sortNats roots).toFinset:=by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
lemma checkNodesBT_mem {W:BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT:T < 2^256) (gp:goodPairs T pos neg)
    (hW:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable:btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos:btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev:btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes:checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset:=by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
def identifyRow (z o i j:Nat) (r:Row):Row :=
  let mask:=if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (255 ^^^ (1 <<< j)) ||| mask) % 256, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f:Row → Row} {raw R:List Nat} {T G D L:Nat}
    (proper:checkProper G = true) (inDomain:∀ r:Row, D.testBit (f r).val = true)
    (covered:raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped:renameW f T = G) (bound:Lower R G L):Slice raw T D L:=by
  have ⟨g0,glt,gb0⟩:=checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound
def evalInput (r:Row):Fin 8 → Bool:=fun i => r.val.testBit i.val
def packInput (x:Fin 8 → Bool):Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0:=Bool.toNat_le (x 0); have h1:=Bool.toNat_le (x 1); have h2:=Bool.toNat_le (x 2)
    have h3:=Bool.toNat_le (x 3); have h4:=Bool.toNat_le (x 4); have h5:=Bool.toNat_le (x 5)
    have h6:=Bool.toNat_le (x 6); have h7:=Bool.toNat_le (x 7); omega⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma evalInput_packInput (x:Fin 8 → Bool):evalInput (packInput x) = x:=by
  funext i
  have h:∀ (b0 b1 b2 b3 b4 b5 b6 b7:Bool) (j:Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false):=by decide +kernel
  have hi:=h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma sw_extract_full (T:Nat) (hT0:T ≠ 0) (hTlt:T < 2^256) (hTb0:T.testBit 0 = false)
    (gs:List Gate) (o:Nat)
    (legal:∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he:∀ r:Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255:=by
  let seeds:List SWire:=(varsOf 255).map (fun v => (false, v))
  have hseeds_lt:∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false:=by
    intro u hu
    obtain ⟨v, hv, rfl⟩:=List.mem_map.mp hu
    have hall:(varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true:=by decide +kernel
    have h1:=List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final:=swExec gs seeds
  let out:=final.getD o swZero
  have hfinal_lt:out.2 < 2^256 ∧ out.2.testBit 0 = false:=by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq:final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r:Row):seeds.map (swRead r.val) = List.ofFn (evalInput r):=by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7:i < 8:=by simpa using hi2
      have hv:(varsOf 255)[i]? = some (VAR i):=by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget:(varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i:=by
        have:=List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r:Row):swRead r.val out = T.testBit r.val:=by
    have h1:=(swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0:out.1 = false:=by
    have h0:=hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2:out.2 = T:=by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr:r < 256
    · have h:=hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound:T ∈ reps final:=by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩:=extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T:Nat) (hT0:T ≠ 0) (hTlt:T < 2^256) (hTb0:T.testBit 0 = false)
    (L:Nat) (hLow:Lower (varsOf 255) T L)
    (wit:List Gate) (wo:Nat) (hwLen:wit.length ≤ L + 1)
    (hwMono:∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn:(Fin 8 → Bool) → Bool)
    (hEdgeT:∀ r:Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR:∀ r:Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates:List Gate) (o:Nat)
    (legal:∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec:∀ x:Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates':List Gate) (o':Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x:Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x:=by
  have hwEval:∀ x:Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x:=by
    intro x
    have hx:=evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn:∃ g ∈ gates, g.op = .not
  · have hlt:gates.countP isBin < gates.length:=by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩:=hn
      have bad:=List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩:=sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd:S.toList.Nodup:=Finset.nodup_toList S
    have hrun:=live_to_run hlive S.toList hnd (by simp)
    have hsup:Supply ((varsOf 255).map obs) (S.toList.map obs):=fun v hv => by
      obtain ⟨a, ha, rfl⟩:=List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo:=hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩:=legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim

def readWord (w:Nat):Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => (x &&& ((1 <<< w) - 1)) :: readWord w n (x >>> w)
def unpackWords (w:Nat) (x:List (Nat × Nat)):List Nat :=
  x.flatMap fun (n, v) => readWord w n v
def readChoices:Nat → List Nat → List (Nat × Nat × Nat)
  | n + 1, a :: b :: c :: rest => (a,b,c) :: readChoices n rest
  | _, _ => []
def readSpecs (cs:Array (Nat × Nat × Nat)):Nat → List Nat → List PoolSpec
  | n + 1, s :: k :: rest =>
      (s, (rest.take k).map fun i => cs.getD i (0,0,0)) :: readSpecs cs n (rest.drop k)
  | _, _ => []
def readNodes:Nat → List Nat → List NodeSpec
  | n + 1, p :: q :: r :: rest =>
      ((rest.take p), ((rest.drop p).take q), ((rest.drop (p+q)).take r)) ::
        readNodes n (rest.drop (p+q+r))
  | _, _ => []
def varStep (b lim mask:Nat):List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | a :: rest, acc, off =>
    let q:=acc + ((a &&& mask) <<< off)
    if a < lim then q :: varStep b lim mask rest 0 0
    else varStep b lim mask rest q (off + b)
def varNats (b:Nat) (x:List Nat):List Nat :=
  let lim:=1 <<< b
  varStep b lim (lim - 1) x 0 0
def unruns:List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, prev =>
      let y:=x >>> 1
      if x &&& 1 == 0 then y :: unruns xs y
      else List.replicate y prev ++ unruns xs prev
def shifts (xs:List Nat):List Nat :=
  (xs.foldl (fun (v, ys) x => let q:=v+x; (q, q::ys)) ((0,[]):Nat × List Nat)).2.reverse
def rankShifts (xs:List Nat):List Nat :=
  (xs.foldl (fun (v, ys) x =>
    let q:=if x &&& 1 == 0 then v + (x >>> 1) else v - ((x >>> 1) + 1)
    (q,q::ys)) ((0,[]):Nat × List Nat)).2.reverse
def readDeltaNodes:Nat → List Nat → List NodeSpec
  | n + 1, p :: q :: r :: rest =>
      (shifts (rest.take p), rankShifts ((rest.drop p).take q), shifts ((rest.drop (p+q)).take r)) ::
        readDeltaNodes n (rest.drop (p+q+r))
  | _, _ => []
lemma someSlice {R T d k} (h:Slice R T d k) :
    ∀ p:Nat × Nat, some (d,k) = some p → Slice R T p.1 p.2:=by
  intro p he
  cases he
  exact h
def lookSpec (count:Nat) (cs:Array (Nat × Nat × Nat))
    (chunks:Array Nat) (index:Nat):Option PoolSpec :=
  if index < count then
    let code:=(chunks.getD (index / 30) 0) >>> (29 * (index % 30))
    let sl:=code &&& 255
    let ids:=[(code >>> 8) &&& 127, (code >>> 15) &&& 127, (code >>> 22) &&& 127]
    some (sl, ids.filterMap fun i => if i = 0 then none else cs[i-1]?)
  else none
def nodePools (nodes:List NodeSpec):List Nat :=
  (nodes.flatMap fun x => x.2.1).eraseDups
def lookupPoolsBT (pdepth:Nat) (W:BT Decor) (raw:List Nat) (slices:BT (Option (Nat × Nat)))
    (pspecs:Nat → Option PoolSpec) (used:List Nat):BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs:=chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma lookupPoolsBT_sound {pdepth} {W:BT Decor} {raw T} {slices:BT (Option (Nat × Nat))}
    {pspecs:Nat → Option PoolSpec} {used:List Nat}
    (hSlices:btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (lookupPoolsBT pdepth W raw slices pspecs used):=by
  unfold lookupPoolsBT
  have hinit:btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty:BT (Option BoundPool)):=trivial
  generalize (BT.empty:BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps:pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl:btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d:=none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma blockOk {W:BT Decor} {raw pos neg T slices autos prev k nodes}
    (specs:Nat → Option PoolSpec) (depth:Nat)
    (hT:T < 2^256) (pairs:goodPairs T pos neg)
    (wf:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (sl:btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices)
    (au:btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (pv:btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prev)
    (ok:checkNodesBT W T (fullMask pos.length)
      (lookupPoolsBT depth W raw slices specs (nodePools nodes)) autos prev k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset :=
  checkNodesBT_mem hT pairs wf (lookupPoolsBT_sound sl) au pv ok

lemma blockGroup {W:BT Decor} {raw pos neg T slices autos prev k} {blocks:List (List NodeSpec)}
    (specs:Nat → Option PoolSpec) (depth:Nat)
    (hT:T < 2^256) (pairs:goodPairs T pos neg)
    (wf:btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (sl:btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices)
    (au:btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (pv:btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prev)
    (ok:blocks.all (fun ns => checkNodesBT W T (fullMask pos.length)
        (lookupPoolsBT depth W raw slices specs (nodePools ns)) autos prev k ns) = true) :
    ∀ b ∈ blocks, ∀ ns ∈ b, Impossible T k (nodeValsBT W ns).toFinset:=by
  intro b hb
  exact blockOk specs depth hT pairs wf sl au pv (List.all_eq_true.mp ok b hb)
lemma allCat {α:Type} {P:α → Prop} {x y:List α}
    (h:∀ a ∈ x, P a) (g:∀ a ∈ y, P a):∀ a ∈ x ++ y, P a:=by
  intro a ha
  rcases List.mem_append.mp ha with hx | hy
  · exact h a hx
  · exact g a hy
def tabBT {α:Type} (f:Nat → α):Nat → Nat → Nat → BT α
  | 0, base, _ => BT.leaf (f base)
  | d+1, base, gap => BT.node (tabBT f d base (2*gap)) (tabBT f d (base+gap) (2*gap))
lemma tabBT_all {α:Type} {P:α → Prop} {f:Nat → α} (all:∀ i, P (f i))
    (d base gap:Nat):btAll P (tabBT f d base gap):=by
  induction d generalizing base gap with
  | zero => exact all base
  | succ d ih => exact ⟨ih base (2*gap), ih (base+gap) (2*gap)⟩
def bucketRefs:Nat → Nat → List Nat
  | 0, _ => []
  | k+1, v => if v = 0 then [] else ((v &&& 4095) - 1) :: bucketRefs k (v >>> 12)
def readNodeRef (blocks:List (List NodeSpec)) (i:Nat):Option NodeSpec :=
  (blocks[i / 8]?).bind fun b => b[i % 8]?
def refBuckets (W:BT Decor) (blocks:List (List NodeSpec)) (rs:Array Nat):BT (List (List Nat)) :=
  tabBT (fun i => (bucketRefs 1024 (rs.getD i 0)).filterMap
    fun j => (readNodeRef blocks j).map (nodeValsBT W)) 6 0 1
lemma refBuckets_all {W:BT Decor} {blocks:List (List NodeSpec)} {rs:Array Nat} {T k:Nat}
    (hall:∀ b ∈ blocks, ∀ ns ∈ b, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (refBuckets W blocks rs):=by
  apply tabBT_all
  intro i xs hx
  obtain ⟨j, _, he⟩:=List.mem_filterMap.mp hx
  unfold readNodeRef at he
  cases hb:blocks[j / 8]? with
  | none => simp [hb] at he
  | some b =>
    cases hn:b[j % 8]? with
    | none => simp [hb,hn] at he
    | some ns =>
      simp only [hb, hn, Option.bind_some, Option.map_some, Option.some.injEq] at he
      exact he ▸ hall b (List.mem_of_getElem? hb) ns (List.mem_of_getElem? hn)
def unpackPrior (W:BT Decor):Nat → Nat → List (List Nat)
  | 0, _ => []
  | steps + 1, code =>
    if code == 0 then [] else
    let n:=code &&& 15
    let rest:=code >>> 4
    (readWord 8 n rest).map (fun i => (btGet (0,0,0) W i).1) ::
      unpackPrior W steps (rest >>> (8 * n))
def fastPrior (W:BT Decor) (codes:Array Nat):BT (List (List Nat)) :=
  tabBT (fun i => unpackPrior W 1024 (codes.getD i 0)) 6 0 1
def priorEq:BT (List (List Nat)) → BT (List (List Nat)) → Bool
  | .empty, .empty => true
  | .leaf x, .leaf y => x == y
  | .node a b, .node c d => priorEq a c && priorEq b d
  | _, _ => false
lemma priorEq_sound {x y:BT (List (List Nat))} (h:priorEq x y = true):x = y:=by
  induction x generalizing y with
  | empty => cases y <;> simp_all [priorEq]
  | leaf z => cases y <;> simp_all [priorEq]
  | node a b ia ib =>
    cases y with
    | empty => simp [priorEq] at h
    | leaf z => simp [priorEq] at h
    | node c d =>
      simp only [priorEq, Bool.and_eq_true] at h
      rw [ia h.1, ib h.2]
abbrev RouteState:=List (Nat × Nat)
def routeAdvance:RouteState → Nat × RouteState
  | [] => (0, [])
  | (v, 0) :: xs => (v, xs)
  | (v, n + 1) :: xs => (v, (v, n) :: xs)
def routeSeq {α:Type} (f:α → RouteState → Bool × RouteState) :
    List α → RouteState → Bool × RouteState
  | [], r => (true, r)
  | a :: as, r =>
      let s:=f a r
      if s.1 then routeSeq f as s.2 else s
lemma routeSeq_imp {α:Type} (f:α → RouteState → Bool × RouteState) (g:α → Bool)
    (h:∀ a r, (f a r).1 = true → g a = true) (xs:List α) (rs:RouteState) :
    (routeSeq f xs rs).1 = true → xs.all g = true:=by
  induction xs generalizing rs with
  | nil => simp [routeSeq]
  | cons a xs ih =>
    intro ok
    by_cases q:(f a rs).1 = true
    · simp only [routeSeq, q, ite_true] at ok
      simp only [List.all_cons, h a rs q, Bool.true_and]
      exact ih _ ok
    · have sq:(f a rs).1 = false:=Bool.eq_false_iff.mpr q
      simp [routeSeq, sq] at ok
def routeEasy (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (a b z:Decor) (ka kb:Bool):Bool :=
  let len:=1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs:=restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
      z.1 == 0 || ws.any (fun v => v.1 == z.1)
lemma routeEasy_sound {cap n fmask ws cov a b z ka kb d fpools autos prev} :
    routeEasy cap n fmask ws cov a b z ka kb = true →
    evalMoveBT cap n fmask ws cov fpools autos prev d a b z ka kb = true:=by
  simp only [routeEasy, evalMoveBT]
  split_ifs <;> tauto
lemma evalMoveBT_mono {cap n fmask ws cov a b z ka kb d fpools autos prev fs sa}
    (hp:fs.Sublist fpools) (ha:sa.Sublist autos) :
    evalMoveBT cap n fmask ws cov fs sa prev d a b z ka kb = true →
    evalMoveBT cap n fmask ws cov fpools autos prev d a b z ka kb = true:=by
  have move:closeChildBT [] sa prev (cap-1) ((delTwo ws a b ka kb).map Prod.fst) (d,a.1,b.1) = true →
      closeChildBT [] autos prev (cap-1) ((delTwo ws a b ka kb).map Prod.fst) (d,a.1,b.1) = true:=by
    simp only [closeChildBT, List.any_nil, Bool.false_or, List.any_eq_true]
    intro ⟨sw, hsw, hb⟩
    exact ⟨sw, ha.subset hsw, hb⟩
  have cover:fs.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true →
      fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true:=by
    intro ht
    obtain ⟨p, pm, ph⟩:=List.any_eq_true.mp ht
    exact List.any_eq_true.mpr ⟨p, hp.subset pm, ph⟩
  simp only [evalMoveBT]
  split_ifs <;> first | tauto | exact move
def routeMove (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat)))
    (prev:BT (List (List Nat))) (d:Nat) (a b z:Decor) (ka kb:Bool)
    (routes:RouteState):Bool × RouteState :=
  if routeEasy cap n fmask ws cov a b z ka kb then (true, routes)
  else
    let (r, tail):=routeAdvance routes
    if r == 0 then (evalMoveBT cap n fmask ws cov fpools autos prev d a b z ka kb, tail)
    else if r ≤ fpools.length then
      (((fpools.drop (r - 1)).take 1).any (fun fp => fastPoolCut fp (cap-1) a.1 b.1 d ka kb), tail)
    else
      (closeChildBT [] ((autos.drop (r - fpools.length - 1)).take 1) prev (cap-1)
         ((delTwo ws a b ka kb).map Prod.fst) (d,a.1,b.1), tail)
lemma routeMove_sound {cap n fmask ws cov fpools autos prev d a b z ka kb routes} :
    (routeMove cap n fmask ws cov fpools autos prev d a b z ka kb routes).1 = true →
    evalMoveBT cap n fmask ws cov fpools autos prev d a b z ka kb = true:=by
  unfold routeMove
  split
  · intro _
    exact routeEasy_sound ‹_›
  · generalize routeAdvance routes = rq
    rcases rq with ⟨r,tail⟩
    dsimp only
    split
    · exact id
    · split
      · intro h
        have hh:((fpools.drop (r - 1)).take 1).any
            (fun fp => fastPoolCut fp (cap-1) a.1 b.1 d ka kb) = true:=h
        apply evalMoveBT_mono (fs:=(fpools.drop (r - 1)).take 1)
            ((List.take_sublist _ _).trans (List.drop_sublist _ _)) (sa:=[]) (List.nil_sublist _)
        simp only [evalMoveBT, hh, ite_true]
        split_ifs <;> rfl
      · intro h
        apply evalMoveBT_mono (List.nil_sublist _) (sa:=(autos.drop (r - fpools.length - 1)).take 1)
            ((List.take_sublist _ _).trans (List.drop_sublist _ _))
        simp only [evalMoveBT, List.any_nil, Bool.false_eq_true, ite_false]
        split_ifs <;> first | rfl | exact h
def routePair (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat))) (prev:BT (List (List Nat)))
    (a b:Decor) (d:Nat) (r:RouteState):Bool × RouteState :=
  let z:=dbin d a b
  routeSeq (fun p => routeMove cap n fmask ws cov fpools autos prev d a b z p.1 p.2)
    [(false,false),(true,false),(false,true),(true,true)] r
lemma routePair_sound {cap n fmask ws cov fpools autos prev a b d r} :
    (routePair cap n fmask ws cov fpools autos prev a b d r).1 = true →
    testPairBT cap n fmask ws cov fpools autos prev a b d = true:=by
  intro h
  have h':=routeSeq_imp _ _ (fun _ _ ht => routeMove_sound ht) _ _ h
  simpa [List.all, testPairBT, Bool.and_assoc] using h'
def testAllRoute (cap n fmask:Nat) (ws:List Decor) (cov:Cov)
    (fpools:List FastPool) (autos:List (List (Nat × Nat))) (prev:BT (List (List Nat))) :
    List Decor → RouteState → Bool × RouteState
  | [], r => (true, r)
  | a :: bs, r =>
      let h:=routeSeq (fun b => routeSeq (routePair cap n fmask ws cov fpools autos prev a b) [0, 1, 2, 3]) bs r
      if h.1 then testAllRoute cap n fmask ws cov fpools autos prev bs h.2 else h
lemma testAllRoute_sound {cap n fmask ws cov fpools autos prev} (zs:List Decor) (r:RouteState) :
    (testAllRoute cap n fmask ws cov fpools autos prev zs r).1 = true →
    testAllBT cap n fmask ws cov fpools autos prev zs = true:=by
  induction zs generalizing r with
  | nil => simp [testAllBT]
  | cons a bs ih =>
    intro h
    unfold testAllRoute at h
    generalize eq:routeSeq
      (fun b => routeSeq (routePair cap n fmask ws cov fpools autos prev a b) [0, 1, 2, 3]) bs r = res at h
    by_cases hs:res.1 = true
    · simp only [hs, ite_true] at h
      unfold testAllBT
      rw [ih _ h, Bool.and_true]
      rw [← eq] at hs
      exact routeSeq_imp _ _ (fun _ _ hf => routeSeq_imp _ _ (fun _ _ hp => routePair_sound hp) _ _ hf) _ _ hs
    · have hf:res.1 = false:=Bool.eq_false_iff.mpr hs
      simp [hf] at h
def checkNodeRoute (W:BT Decor) (T fmask:Nat)
    (poolTable:BT (Option BoundPool)) (autosTable:BT (List (Nat × Nat)))
    (prevBks:BT (List (List Nat))) (k:Nat) (ns:NodeSpec) (routes:RouteState):Bool :=
  if routes.isEmpty then checkNodeBT W T fmask poolTable autosTable prevBks k ns else
  let ws:=ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals:=ws.map Prod.fst
  let fpools:=ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos:=ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || (testAllRoute k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws routes).1)
lemma checkNodeRoute_sound {W T fmask poolTable autosTable prevBks k ns r}
    (ok:checkNodeRoute W T fmask poolTable autosTable prevBks k ns r = true) :
    checkNodeBT W T fmask poolTable autosTable prevBks k ns = true:=by
  unfold checkNodeRoute at ok
  split at ok
  · exact ok
  · simp only [checkNodeBT, Bool.and_eq_true, Bool.or_eq_true] at *
    exact ⟨ok.1, ok.2.imp id (testAllRoute_sound _ _)⟩
def checkNodesRoute (W:BT Decor) (T fmask:Nat) (P:BT (Option BoundPool))
    (A:BT (List (Nat × Nat))) (B:BT (List (List Nat))) (k:Nat) :
    List NodeSpec → List RouteState → Bool
  | [], _ => true
  | a :: as, rs => checkNodeRoute W T fmask P A B k a (rs.headD []) &&
      checkNodesRoute W T fmask P A B k as (rs.drop 1)
lemma checkNodesRoute_sound {W T fmask P A B k} (xs:List NodeSpec) (rs:List RouteState)
    (ok:checkNodesRoute W T fmask P A B k xs rs = true) :
    checkNodesBT W T fmask P A B k xs = true:=by
  induction xs generalizing rs with
  | nil => rfl
  | cons a as ih =>
    simp only [checkNodesRoute, Bool.and_eq_true] at ok
    simp only [checkNodesBT, List.all_cons, Bool.and_eq_true]
    exact ⟨checkNodeRoute_sound ok.1, ih _ ok.2⟩
def readRouteRows:Nat → List Nat → List RouteState
  | n + 1, k :: rest =>
    ((rest.take k).map (fun x => (x &&& 31, x >>> 5))) :: readRouteRows n (rest.drop k)
  | _, _ => []
def aG:List Nat:=varsOf 21
def aC:Nat:=0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def dv:List Nat:=[17,20,5,5,20,17]
def dw:List Nat:=[16,16,1,4,4,1]
def iT:Nat:=fullMask 6
def iU:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,51,3)]
def tZ:List (Nat × Nat × Nat):=[]
def cG:BT Decor:=buildWiresBT 2 iU tZ
def ua:List (List (Nat × Nat)):=[[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def dx:BT (List (Nat × Nat)):=btOfList 3 ua
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ub:goodPairs aC dv dw:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uc:∀ x ∈ iU, faithful dv dw x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ud:btAll (fun x => faithful dv dw x ∧ x.1 < 2^256) cG:=buildWiresBT_faithful uc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ue:btAll (fun sw => swapsValid sw = true ∧ permWord sw aC = aC) dx:=btAll_ofList (autos_of (by decide +kernel))
def uf:List (Option (Nat × Nat)):=[]
def iV:BT (Option (Nat × Nat)):=btOfList 1 uf
def ug:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 0 []
def dy:BT (Option BoundPool):=buildPoolsBT 1 cG aG iV ug
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uh:btAll (fun o => ∀ p, o = some p → Slice aG aC p.1 p.2) iV:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aG aC p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma ui:btAll (fun o => ∀ c, o = some c → ValidPool aG aC c) dy:=buildPoolsBT_sound uh
def dz:BT (List (List Nat)):=BT.empty
lemma uj:btAll (fun bk => ∀ xs ∈ bk, Impossible aC (3 - 1) xs.toFinset) dz:=trivial
def iW:List NodeSpec:=readDeltaNodes 1 (unpackWords 2 [(6,1283)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uk:checkNodesBT cG aC iT dy dx dz 3 iW = true:=by decide +kernel
def iX:List NodeSpec:=iW
set_option maxRecDepth 20000 in
lemma ul:checkNodesBT cG aC iT dy dx dz 3 iX = true:=uk
def um:BT (List (List Nat)):=buildBucketsBT cG iX
set_option maxRecDepth 20000 in
lemma un:btAll (fun bk => ∀ xs ∈ bk, Impossible aC 3 xs.toFinset) um:=buildBucketsBT_sound (by decide) ub ud ui ue uj ul
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aI:Lower aG aC 4:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) un (by decide +kernel)
def bh:List Nat:=varsOf 149
def bl:Nat:=0xfffffffffffffffffffffffffffffffffafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bq:Lower bh bl 5:=lift_of (z:=128) (o:=0) (essPairs:=[(VAR 7,0,128)]) (by decide +kernel) aI
def iY:List Nat:=varsOf 212
def iZ:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uo:Lower iY iZ 5:=carry_of (swaps:=[(5,6),(3,6),(1,6),(4,6),(6,7),(2,6),(0,4)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def cV:List Nat:=varsOf 69
def cW:Nat:=0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cX:Lower cV cW 4:=carry_of (swaps:=[(5,6),(4,6)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def dA:List Nat:=varsOf 81
def dB:Nat:=0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jc:Lower dA dB 4:=carry_of (swaps:=[(5,6),(3,6),(4,6),(2,4)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def dC:List Nat:=varsOf 84
def dD:Nat:=0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jd:Lower dC dD 4:=carry_of (swaps:=[(5,6),(3,6),(1,6),(4,6),(2,4),(0,2)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def aP:List Nat:=varsOf 85
def az:Nat:=0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def dE:List Nat:=[17,20,5,5,20,17,65,80,68,80,65,68]
def dF:List Nat:=[16,16,1,4,4,1,1,16,4,64,64,64]
def ca:Nat:=fullMask 12
def je:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1133,100),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2334,280),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,691,131),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,4032,3584)]
def up:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,1,2),(1,4,5),(3,2,4),(3,3,7)]
def bn:BT Decor:=buildWiresBT 4 je up
def uq:List (List (Nat × Nat)):=[[],[(4,6)],[(2,4)],[(2,6)],[(0,2)],[(0,4)],[(0,6)],[(4,6),(2,4)],[(4,6),(2,6)],[(4,6),(0,2)],[(2,4),(0,2)],[(2,6),(0,2)],[(2,4),(0,4)],[(4,6),(0,4)],[(2,6),(0,4)],[(2,6),(0,6)],[(4,6),(0,6)],[(2,4),(0,6)],[(4,6),(2,4),(0,2)],[(4,6),(2,6),(0,2)],[(4,6),(2,4),(0,4)],[(4,6),(2,6),(0,4)],[(4,6),(2,6),(0,6)],[(4,6),(2,4),(0,6)]]
def bN:BT (List (Nat × Nat)):=btOfList 5 uq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cY:goodPairs az dE dF:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ur:∀ x ∈ je, faithful dE dF x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cZ:btAll (fun x => faithful dE dF x ∧ x.1 < 2^256) bn:=buildWiresBT_faithful ur
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma da:btAll (fun sw => swapsValid sw = true ∧ permWord sw az = az) bN:=btAll_ofList (autos_of (by decide +kernel))
def us:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,4),some (subcubeFast 4 0,4),some (subcubeFast 16 0,4),some (subcubeFast 64 0,4)]
def jf:BT (Option (Nat × Nat)):=btOfList 2 us
def ut:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 4 (unpackWords 2 [(8,12816)])
def bO:BT (Option BoundPool):=buildPoolsBT 2 bn aP jf ut
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uu:Slice aP az (subcubeFast 64 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=aG) (qGoal:=aC) (by decide +kernel) aI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uv:Slice aP az (subcubeFast 16 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cV) (qGoal:=cW) (by decide +kernel) cX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uw:Slice aP az (subcubeFast 4 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dA) (qGoal:=dB) (by decide +kernel) jc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ux:Slice aP az (subcubeFast 1 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dC) (qGoal:=dD) (by decide +kernel) jd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uy:btAll (fun o => ∀ p, o = some p → Slice aP az p.1 p.2) jf:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aP az p.1 p.2) (forall_cons (someSlice ux) (forall_cons (someSlice uw) (forall_cons (someSlice uv) (forall_cons (someSlice uu) (fun _ h => (List.not_mem_nil h).elim)))))
lemma db:btAll (fun o => ∀ c, o = some c → ValidPool aP az c) bO:=buildPoolsBT_sound uy
def dG:BT (List (List Nat)):=BT.empty
lemma uz:btAll (fun bk => ∀ xs ∈ bk, Impossible az (3 - 1) xs.toFinset) dG:=trivial
def jg:List NodeSpec:=readDeltaNodes 2 (unpackWords 3 [(16,0xe48022049614)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uA:checkNodesBT bn az ca bO bN dG 3 jg = true:=by decide +kernel
def jh:List NodeSpec:=jg
set_option maxRecDepth 20000 in
lemma uB:checkNodesBT bn az ca bO bN dG 3 jh = true:=uA
def dH:BT (List (List Nat)):=buildBucketsBT bn jh
set_option maxRecDepth 20000 in
lemma uC:btAll (fun bk => ∀ xs ∈ bk, Impossible az 3 xs.toFinset) dH:=buildBucketsBT_sound (by decide) cY cZ db da uz uB
def ji:List NodeSpec:=readDeltaNodes 3 (unpackWords 3 [(29,0x5248028d09209a12249255)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uD:checkNodesBT bn az ca bO bN dH 4 ji = true:=by decide +kernel
def jj:List NodeSpec:=ji
set_option maxRecDepth 20000 in
lemma uE:checkNodesBT bn az ca bO bN dH 4 jj = true:=uD
def dI:BT (List (List Nat)):=buildBucketsBT bn jj
set_option maxRecDepth 20000 in
lemma uF:btAll (fun bk => ∀ xs ∈ bk, Impossible az 4 xs.toFinset) dI:=buildBucketsBT_sound (by decide) cY cZ db da uC uE
def jk:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(16,0xac8490249125)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uG:checkNodesBT bn az ca bO bN dI 5 jk = true:=by decide +kernel
def jl:List NodeSpec:=jk
set_option maxRecDepth 20000 in
lemma uH:checkNodesBT bn az ca bO bN dI 5 jl = true:=uG
def dJ:BT (List (List Nat)):=buildBucketsBT bn jl
set_option maxRecDepth 20000 in
lemma uI:btAll (fun bk => ∀ xs ∈ bk, Impossible az 5 xs.toFinset) dJ:=buildBucketsBT_sound (by decide) cY cZ db da uF uH
def jm:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(17,0x81212022201110644)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uJ:checkNodesBT bn az ca bO bN dJ 6 jm = true:=by decide +kernel
def jn:List NodeSpec:=jm
set_option maxRecDepth 20000 in
lemma uK:checkNodesBT bn az ca bO bN dJ 6 jn = true:=uJ
def uL:BT (List (List Nat)):=buildBucketsBT bn jn
set_option maxRecDepth 20000 in
lemma uM:btAll (fun bk => ∀ xs ∈ bk, Impossible az 6 xs.toFinset) uL:=buildBucketsBT_sound (by decide) cY cZ db da uI uK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bA:Lower aP az 7:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 6,1,65)]) (by decide +kernel) uM (by decide +kernel)
def jo:List Nat:=varsOf 133
def jp:Nat:=0xfafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uN:Lower jo jp 4:=carry_of (swaps:=[(6,7),(5,7),(4,7)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def jq:List Nat:=varsOf 145
def jr:Nat:=0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uO:Lower jq jr 4:=carry_of (swaps:=[(6,7),(5,7),(3,7),(4,7),(2,4)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def js:List Nat:=varsOf 148
def jt:Nat:=0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uP:Lower js jt 4:=carry_of (swaps:=[(6,7),(5,7),(3,7),(1,7),(4,7),(2,4),(0,2)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def ju:List Nat:=varsOf 149
def jv:Nat:=0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uQ:Lower ju jv 7:=carry_of (swaps:=[(6,7)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def jw:List Nat:=varsOf 193
def jx:Nat:=0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uR:Lower jw jx 4:=carry_of (swaps:=[(6,7),(5,6),(3,6),(4,7),(2,6)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def jy:List Nat:=varsOf 196
def jz:Nat:=0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uS:Lower jy jz 4:=carry_of (swaps:=[(6,7),(5,6),(3,6),(1,6),(4,7),(2,6),(0,2)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def jA:List Nat:=varsOf 197
def jB:Nat:=0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uT:Lower jA jB 7:=carry_of (swaps:=[(5,7),(6,7),(4,6)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def jC:List Nat:=varsOf 208
def jD:Nat:=0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jE:Lower jC jD 4:=carry_of (swaps:=[(6,7),(5,6),(3,7),(1,7),(4,7),(2,6),(0,4)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def jF:List Nat:=varsOf 209
def jG:Nat:=0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uU:Lower jF jG 7:=carry_of (swaps:=[(5,7),(3,7),(6,7),(4,6),(2,4)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def jH:List Nat:=varsOf 212
def jI:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uV:Lower jH jI 7:=carry_of (swaps:=[(5,7),(3,7),(1,7),(6,7),(4,6),(2,4),(0,2)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def aJ:List Nat:=varsOf 213
def ad:Nat:=0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def dK:List Nat:=[17,20,5,5,20,17,65,129,192,192,68,65,80,132,144,68,129,132,80,144,17,193,148,80,5,145,148,5,17,65,21,5,17,20,193,208,192,193,196,208,144,84,65,21,68]
def dL:List Nat:=[16,16,1,4,4,1,1,1,64,128,4,64,16,4,16,64,128,128,64,128,4,1,4,1,64,16,16,0,0,0,16,128,128,128,128,128,1,64,64,64,4,16,16,4,16]
def jJ:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc25fb3108ed,0x1000a000e4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1a42cd42a41e,0x90000502418),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xb8b56dc5033,0x160046005003),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x16fc20a49f40,0xe001048900),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x1fc066b6380,0xf800b0200)]
def uW:List (Nat × Nat × Nat):=[(0,0,1),(1,0,1),(1,0,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,6),(1,4,7),(1,8,10),(1,8,13),(1,8,14),(1,10,13),(1,10,14),(1,13,14),(3,4,7),(1,4,8),(3,4,13),(0,7,8),(1,7,8),(2,3,6),(3,3,6),(1,3,7),(3,3,7),(1,3,8),(1,4,6),(3,4,6),(3,3,14),(1,3,21),(1,4,27),(3,3,22),(0,1,3),(1,1,3),(1,2,3),(1,4,38),(3,4,38),(1,4,39),(3,4,39),(2,31,39),(1,32,43),(1,32,39),(2,6,39),(0,2,4),(1,2,4),(2,38,49),(3,3,49),(3,3,40),(3,2,6),(3,2,30),(3,6,54),(1,2,32),(3,2,40),(1,1,4),(3,1,7),(3,1,10),(3,1,42),(3,1,28),(3,1,13),(3,2,13),(1,3,64),(3,1,14),(3,1,39),(1,2,27),(1,0,3),(3,0,3),(1,0,4),(2,0,4),(3,0,28),(3,0,16),(3,3,16),(0,4,16),(3,3,45),(1,1,73),(1,4,69),(3,1,49),(3,0,49),(3,0,13),(3,0,58),(0,0,42),(3,0,42),(3,0,20),(3,1,20),(3,3,20),(3,4,56),(2,16,72),(1,3,76),(1,3,5),(3,5,45),(0,3,25),(3,3,71),(0,58,71),(0,4,25),(1,0,12),(1,4,75),(1,0,52),(1,0,9),(1,25,101),(3,9,25),(1,0,11),(1,25,104),(3,11,25),(1,4,94),(2,4,94),(2,16,94),(1,0,55),(1,0,26),(2,75,92),(3,4,65),(1,3,80),(0,7,71),(3,0,22),(1,1,116),(1,1,85),(3,48,88),(1,38,117),(3,3,117),(1,2,37),(3,37,86),(1,0,60),(1,1,84),(2,19,84)]
def ag:BT Decor:=buildWiresBT 7 jJ uW
def uX:List (List (Nat × Nat)):=[[],[(6,7)],[(4,6)],[(4,7)],[(2,4)],[(2,6)],[(2,7)],[(0,2)],[(0,4)],[(0,6)],[(0,7)],[(6,7),(4,6)],[(6,7),(4,7)],[(6,7),(2,4)],[(4,6),(2,4)],[(4,7),(2,4)],[(4,6),(2,6)],[(6,7),(2,6)],[(4,7),(2,6)],[(4,7),(2,7)],[(6,7),(2,7)],[(4,6),(2,7)],[(6,7),(0,2)],[(4,6),(0,2)],[(4,7),(0,2)],[(2,4),(0,2)],[(2,6),(0,2)],[(2,7),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(4,6),(0,4)],[(4,7),(0,4)],[(2,6),(0,4)]]
def uY:BT (List (Nat × Nat)):=btOfList 6 uX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ak:goodPairs ad dK dL:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma uZ:∀ x ∈ jJ, faithful dK dL x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma al:btAll (fun x => faithful dK dL x ∧ x.1 < 2^256) ag:=buildWiresBT_faithful uZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma an:btAll (fun sw => swapsValid sw = true ∧ permWord sw ad = ad) uY:=btAll_ofList (autos_of (by decide +kernel))
def vc:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,7),some (subcubeFast 4 0,7),some (subcubeFast 5 0,4),some (subcubeFast 16 0,7),some (subcubeFast 17 0,4),some (subcubeFast 20 0,4),some (subcubeFast 64 0,7),some (subcubeFast 65 0,4),some (subcubeFast 68 0,4),some (subcubeFast 80 0,4),some (subcubeFast 128 0,7),some (subcubeFast 129 0,4),some (subcubeFast 132 0,4),some (subcubeFast 144 0,4),some (subcubeFast 192 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,5),some (0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff,5)]
def vd:BT (Option (Nat × Nat)):=btOfList 5 vc
def ao:Nat → Option PoolSpec:=lookSpec 116 #[(1,0,2),(1,0,1),(1,1,2),(1,3,4),(1,3,6),(1,1,3),(3,4,13),(3,3,6),(1,2,3),(1,3,7),(1,3,8),(1,2,4),(1,4,6),(2,31,39),(3,4,6),(1,8,13),(2,6,39),(1,1,4),(1,7,8),(1,0,4),(3,2,6),(3,2,13),(1,0,3),(1,4,39),(3,1,49),(3,1,42),(1,4,7),(1,8,14),(3,1,14),(1,4,8),(3,0,49),(3,0,22),(1,8,10),(2,38,49),(3,1,10),(0,0,42),(3,0,42)] #[0x120000402030e14101800404180050202000820a0000201800000300000c0000082060018101800000240000600000020300002800000001c00504060818106060410500000014000000800000020000001800010000000802000000806041030000040400000020000000,0x200001303243018000244c0ca122606009030000441018020140400f040638682030034101800034040001a00004850000000030000082800012140000c060000006800000386090800006090000281018014040400016022c50203000000500002800000040c0000901,0x203c0200f8c06007c60080360418009360000f1b030000f008000002c01d360600d81010070d819a3024000003006004810a00600830032300001218000060101000008500302400b89021400b810a003008300003004000180000b020600541030024080c01504140018500,0x25121401298060094c01a5302404000001e90c090100604808c121004004180201184030030200801810000220c060108401002430500182404000300c6031e031218185203c0c18006061400f03060018f01800018280170c060000603]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ve:Slice aJ ad (0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff) 5:=mappedSlice (f:=identifyRow 0 0 7 6) (R:=bh) (G:=bl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vf:Slice aJ ad (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 5:=mappedSlice (f:=identifyRow 0 0 2 0) (R:=iY) (G:=iZ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) uo
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vg:Slice aJ ad (subcubeFast 192 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=aG) (qGoal:=aC) (by decide +kernel) aI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vh:Slice aJ ad (subcubeFast 144 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cV) (qGoal:=cW) (by decide +kernel) cX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vi:Slice aJ ad (subcubeFast 132 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dA) (qGoal:=dB) (by decide +kernel) jc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vj:Slice aJ ad (subcubeFast 129 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dC) (qGoal:=dD) (by decide +kernel) jd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vk:Slice aJ ad (subcubeFast 128 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aP) (qGoal:=az) (by decide +kernel) bA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vl:Slice aJ ad (subcubeFast 80 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=jo) (qGoal:=jp) (by decide +kernel) uN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vm:Slice aJ ad (subcubeFast 68 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=jq) (qGoal:=jr) (by decide +kernel) uO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vn:Slice aJ ad (subcubeFast 65 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=js) (qGoal:=jt) (by decide +kernel) uP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vo:Slice aJ ad (subcubeFast 64 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ju) (qGoal:=jv) (by decide +kernel) uQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vp:Slice aJ ad (subcubeFast 20 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=jw) (qGoal:=jx) (by decide +kernel) uR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vq:Slice aJ ad (subcubeFast 17 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=jy) (qGoal:=jz) (by decide +kernel) uS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vr:Slice aJ ad (subcubeFast 16 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=jA) (qGoal:=jB) (by decide +kernel) uT
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vs:Slice aJ ad (subcubeFast 5 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=jC) (qGoal:=jD) (by decide +kernel) jE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vt:Slice aJ ad (subcubeFast 4 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=jF) (qGoal:=jG) (by decide +kernel) uU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vu:Slice aJ ad (subcubeFast 1 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=jH) (qGoal:=jI) (by decide +kernel) uV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ap:btAll (fun o => ∀ p, o = some p → Slice aJ ad p.1 p.2) vd:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aJ ad p.1 p.2) (forall_cons (someSlice vu) (forall_cons (someSlice vt) (forall_cons (someSlice vs) (forall_cons (someSlice vr) (forall_cons (someSlice vq) (forall_cons (someSlice vp) (forall_cons (someSlice vo) (forall_cons (someSlice vn) (forall_cons (someSlice vm) (forall_cons (someSlice vl) (forall_cons (someSlice vk) (forall_cons (someSlice vj) (forall_cons (someSlice vi) (forall_cons (someSlice vh) (forall_cons (someSlice vg) (forall_cons (someSlice vf) (forall_cons (someSlice ve) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def vv:BT (List (List Nat)):=BT.empty
lemma jK:btAll (fun bk => ∀ xs ∈ bk, Impossible ad (3 - 1) xs.toFinset) vv:=trivial
def jL:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb110041af3120042d2a330042c3e2b3860145639700428473870141813218014),(14,7056281496205337)]))
def jM:List NodeSpec:=readDeltaNodes 5 (varNats 3 (unpackWords 4 [(50,0x1ad4a220044c684a400412f2b4f00418e68100043b4f681004)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvw:∀ b ∈ ([jL,jM]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 3 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an jK (by decide +kernel)
def vy:BT (List (List Nat)):=refBuckets ag [jL,jM] #[0,0,0,0,0,0,0,0,0,0,1,0,0,16386,7,0,0,0,0,0,0,0,0,0,13,0,0,0,9,0,0,0,8,0,0,0,10,0,0,0,0,0,0,5,0,0,0,0,0,6,0,0,0,0,0,0,12,0,0,3,11,0,0,0]
set_option maxRecDepth 20000 in
lemma bP:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 3 xs.toFinset) vy:=refBuckets_all batchvw
def jN:List NodeSpec:=readDeltaNodes 8 (unpackWords 4 [(64,0x56d413005e51313015f1313005854130050815413115ea13130157032134205),(6,6238512)])
def jO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6c93573e327006832138eacc24d0ac279d19849a772cb00d),(57,0x230f89204d30cc76519449a703cdacd481ae9995529)]))
def jP:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2052d02c2b38242055a111000514c32a18111153c5c3e2a44211542c1f312105),(38,0x31aa191a3a1d01151e1a2d2910015131914960)]))
def jQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86e601a82bca29035197924034db8924034dd8ca54c6004d),(53,0x1932d14a6e28134f3b1b9800d32aabe60035d54e)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvz:∀ b ∈ ([jN,jO,jP,jQ]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 4 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an bP (by decide +kernel)
def jR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9a0ec65e8920d0678fa84906a954a6f40034cabe59000d),(58,0xed5120034fb8ddde2402693c1961e4860d3ee37c509)]))
def jS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd36996b28034ca65a9200d739991601a6ec668f1b5904d),(53,0x232bd19641a0ccb2caf54926998b94a00d3b644a)]))
def jT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xebc2d92683ba9db209aa3b9b201a4cd0c440342f5fcd904d),(53,0x1acd87c20835e73ad8c44135999570ee41269321)]))
def jU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9a0ad94ec9069e15e57e4206adcc90c44035f33531100d),(55,0xf3d5520034cf8faa9001ab52ae20034dd8cf8a98c)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvD:∀ b ∈ ([jR,jS,jT,jU]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 4 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an bP (by decide +kernel)
def jV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa558faabab8126bf1c51000d33d2a6300069bb1d4c54804d),(61,0x1fb124806bbf1db3e4a04d61c854a92069bb132198c009)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvH:∀ b ∈ ([jV]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 4 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an bP (by decide +kernel)
def vI:BT (List (List Nat)):=refBuckets ag [jN,jO,jP,jQ,jR,jS,jT,jU,jV] #[0,0,64,0,0,213013,39,63,0,233501,20,53,838971400,68,0,58,0,1,1040437291,0,25,11,23,4123856547844,67,22,0,0,59,0,40966,12,196611,0,0,151567,46,42,47,225308,0,0,4948741922818,208922,1191366688,1107423245,69646,0,906149926,35,0,0,0,671236126,49,7,24,266274,16,69,286753,9,5,0]
set_option maxRecDepth 20000 in
lemma aQ:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 4 xs.toFinset) vI:=refBuckets_all (allCat batchvz (allCat batchvD batchvH))
def jW:List NodeSpec:=readDeltaNodes 8 (unpackWords 5 [(64,0x210a7008509846118865a1e050844118066380903a74508c23114b0290610084430d4208441198c6),(49,0x16621170882300cc0b844108801330884017f08823280d72901212101f8444)])
def jX:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1631844018381821125161f1063931123062191b073831124061805f12112116),(61,0x193102a42211406544284b121213161a1f31068313125064402a291f21123)]))
def jY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8a924a072442855249309ce279ce73288671343cbb24964e),(64,0x24939e79ea5144238c70c87638a64338d0ee32324944e342),(9,4136137)]))
def jZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xce064ce124824e0f444a009ce878f8c9251381c6524920e),(64,0x8b29532683819a225004e4e633237225067290f56158dc92),(9,27897357)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvJ:∀ b ∈ ([jW,jX,jY,jZ]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 5 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an aQ (by decide +kernel)
def kc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x271e6706ccb1d95643273549412321d8c522c7d30d20e38e),(64,0x3e124184e719c1584f3ba40c273c7d539440273c75539440),(47,0x758b4249009c63441909241a0e7c9a61917)]))
def kd:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x54f34c5cfa4906038f06ec65539442271ea832138f89064e),(64,0xc9c03d9c24924e32e249001c0c99e8e12492705b124820e),(15,0xdc664c71c89)]))
def kg:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1212604f3111010618a3d1d111001659111100065a111000511707c1d1110406),(59,0x18018a491d1912021651977401be226918a19382e3065505c18a1d492d1)]))
def kh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38186457a94dc5028e3a187736928207280c98caee25044e),(64,0xe0d91f2792193883a19319e1b49252397c6190fea5371403),(43,0xe864c74c4920a3893c1931a89060389)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvN:∀ b ∈ ([kc,kd,kg,kh]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 5 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an aQ (by decide +kernel)
def ki:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20e55c20cf94248301ce137633f36924a273881d392480ce),(64,0xd8d98dc49061381b219f3889049c6ec75c49201381d69248),(23,0x6ce6e24800e55c20d)]))
def kj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x36d369248271b0dc49001ca9b239cdc49049c1ca6d24904e),(60,0x26fe49208399961248071a64c89001c0d8e744820e376)]))
def kk:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x21601ba1ae2d111111607e1921100165e2c3f6c312002618c42819382b330036),(51,0x1dc492d11200160018d11112116692e2110006701ba1d12d310)]))
def kl:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38db492400702e425020e593aac25040e2b9931eee25044e),(64,0x3ba9db279a6ac0f8bbf99451394382cb2f4a2c1c77a49200),(26,0x990950d0f44bc3af53c)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvR:∀ b ∈ ([ki,kj,kk,kl]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 5 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an aQ (by decide +kernel)
def kn:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x42101161e2a384210016002a5c31211161be5d1aa2c74b33103603b4b3121016),(52,0x1502a194942103165075c4210206291b4284b42103062c1e4a5a)]))
def ko:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x18a28191884213252c018b5a3121026387d1aa2e3b1f421036402a35a4210216),(60,0x4f5d2110106102bc6e312102165e4c05b4b3121036001db312101161e30)]))
def kp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38cd0ccb1c7d640472b33fcd9963a98a9019c1786625004e),(64,0x241072a145b153321139837633f531282273318267a49260),(28,0x6ec67ca728824e58fb09)]))
def kq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb8f8b63eaa4246879fe51041c16d8eab1441271f6924800e),(64,0x9219f298941139f60d8673b3218389e718baabab10301cc3),(20,0x543f0cc4a081cc3)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvV:∀ b ∈ ([kn,ko,kp,kq]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 5 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an aQ (by decide +kernel)
def kr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xcbe3a1b13c66480671a73e0f915c745af5fc26433180c34d),(64,0x392f21b0c321992019c648fd36658990cc600ce494889009),(51,0x6ec4c866640273c41d175332183919e2991201)]))
def ks:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0x5f1242271f9e515e7a202383914c49241c0dd96a54cc824e),(59,0xb1f3124820e5eab89400383be192be49249c6635e337)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchvZ:∀ b ∈ ([kr,ks]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 5 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an aQ (by decide +kernel)
def wb:BT (List (List Nat)):=refBuckets ag [jW,jX,jY,jZ,kc,kd,kg,kh,ki,kj,kk,kl,kn,ko,kp,kq,kr,ks] #[1493471262,0,409607,1879191557,1594155018,6804839186448,0x4b04303601600f,0x8d04c03d02802401c,23,58,434226,91,110606,0,0x8b08508305a038,8385537970194,102,512047,1745158221,0x8607f06b03e033022,1896013844,71,33,5842313408564,9622790811691,93,118,217112,159773,9760179286035,2,495658,466989,2282057796,0x8406e04200d008,294977,1476575263,97,60,3780259155977,135,507963,2114084865,1862623244,401440,0,128,3,421925,143,413753,0,25,6,446534,138,479313,64,2181234714,0x8908105201500b,385107,1946599508,303108,119]
set_option maxRecDepth 20000 in
lemma cb:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 5 xs.toFinset) wb:=refBuckets_all (allCat batchvJ (allCat batchvN (allCat batchvR (allCat batchvV batchvZ))))
def kt:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xa31211114577181802d483d2e283f121124562854310291283b2822811213675),(64,0x2c31111346022a72861211111471813102c5b24a193a6311115661931062e261),(53,0x39021c481a294c1b2e2111126701882e2111101171c104a4d5828)]))
def ku:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24f3cbed121c34d876562ca54510a1a7980c90c9d124844f),(64,0xf9c37924844f3a9e0c91198f321d8f4890cd3c3f8eca9248),(64,0x86c321e7c24906987ac61ed321239d8ac50ee4921434f543),(36,0x3df24f064ce1248389cab89079d)]))
def kv:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x5011b91b81bb5e18a492d1120666201da184b1111021770286c4c1a211110237),(64,0x47194116106a483e1ad1ba1e71111075716103a783e7d18a2851111045729433),(61,0x1701ba3e2d1111031711701ba191c11110417191c1018e222818d2d111104)]))
def kw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe4832e48c8e636924834c3cd2512490be48c865e4921630e),(64,0xd1e74503d978667152490d9ee032c48c8a533a250461e61),(64,0xf4ed8c86b94941987121232196a2490d9e4f06686626d249),(27,0x4298da4921138ae0d90c)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchwc:∀ b ∈ ([kt,ku,kv,kw]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 6 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an cb (by decide +kernel)
def ky:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xa195a42106561c351906d1dc1d91ec2a2c5a31215564707e581a287d11110346),(64,0x28b18a1aa19931210436501de2f4d1aa3b1f312102471a136401cd2881fd7e1a),(64,0x1103571b1019a18c28481d1111033741210218e15e1cf29c4b312105661f1950),(18,0x29702229c22a295d11)]))
def kz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6987aa1598c951b32c7558a211879c4256c3328b12486cf),(64,0x21b39106de7486cc7ca4921b38da6a6178e4336516ea6249),(64,0x24a283991d71b14362ea644854d3cdca856737e3665b29ca),(64,0x321989242279e69318572b298b5cb5ebf864331281c71cf2),(7,722350)]))
def kA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38ccb052c5b298924327b08eb968747e9b32e6433128238f),(64,0x7ecb45b1bd7249099ea36783ef7265ff5ac562c54cc834d),(64,0x79872ee04ac32f36454fc7924330f51ace7c57a492193cd),(64,0xaa6c698bc562c7d54870f359c61a987265ff52c3645d7c49),(20,0x24a2b12c9064ea5)]))
def kB:List NodeSpec:=readDeltaNodes 3 (varNats 2 (unpackWords 3 [(64,0xee3a49a1246d8a786ca4920e34e39426877606f7c9241a8f),(32,0x6504bc3af53c5bab89241861)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchwh:∀ b ∈ ([ky,kz,kA,kB]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 6 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an cb (by decide +kernel)
def wl:BT (List (List Nat)):=refBuckets ag [kt,ku,kv,kw,ky,kz,kA,kB] #[721526805,0,0,23,25,939679766,0,805371917,49,0,0,55,0,0,213020,40,0,0,135177,53,0,30,0,1,69644,0,0,4,0,0,0,0,0,204847,7,44,2543023370258,0,31,0x3a03903602900b008003,0,81922,35,0,771792901,0,0,0,0,36,15,0,59,159771,855810080,0,0,0,0,57350,0,29,0,184354]
set_option maxRecDepth 20000 in
lemma kC:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 6 xs.toFinset) wl:=refBuckets_all (allCat batchwc batchwh)
def kD:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x7186251187522026a2c5d223a48492111101918719310182e21f3c4121111466),(64,0x5461a1101ab3a5a21d28282b211110477118111102219938691aa3e42d11110),(64,0xa4b1a111105197541401a6c1881fb1c28a5a3121056619111041ba2828691111),(51,0x2a123025c681aa19d111105462b22101c2a2d486818a1df681a)]))
def kE:List NodeSpec:=readDeltaNodes 3 (varNats 2 (unpackWords 3 [(64,0x242a71ca3349441ba2bccd96fdd8bf3a436c5d4c4921450f),(64,0x33e7a9f2193abb2b89242aa1cb9c918ca08ff93572f95e79),(19,0xe2cc94504bc5ed)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchwm:∀ b ∈ ([kD,kE]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ad 7 (nodeValsBT ag ns).toFinset:=blockGroup ao 8 (by decide) ak al ap an kC (by decide +kernel)
def wq:BT (List (List Nat)):=refBuckets ag [kD,kE] #[0,0,0,0,0,8,0,45060,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,9,0,0,6,2,0,0,0,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,3,0,5,0,0,0,7,0,0,0]
set_option maxRecDepth 20000 in
lemma wr:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 7 xs.toFinset) wq:=refBuckets_all batchwm
def kF:List NodeSpec:=readDeltaNodes 2 (varNats 3 (unpackWords 4 [(53,0x12706925e2a6c1e5d111104661284111018f3a3e3e20211110766)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wt:∀ ns ∈ kF, Impossible ad 8 (nodeValsBT ag ns).toFinset:=blockOk ao 8 (by decide) ak al ap an wr (by decide +kernel)
def wu:BT (List (List Nat)):=refBuckets ag [kF] #[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma wv:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 8 xs.toFinset) wu:=refBuckets_all (forall_cons wt (fun _ h => (List.not_mem_nil h).elim))
def kG:List NodeSpec:=readDeltaNodes 1 (unpackWords 6 [(20,0x5c3041082018d0c080041041007145)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ww:∀ ns ∈ kG, Impossible ad 9 (nodeValsBT ag ns).toFinset:=blockOk ao 8 (by decide) ak al ap an wv (by decide +kernel)
def wx:BT (List (List Nat)):=refBuckets ag [kG] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma wy:btAll (fun bk => ∀ xs ∈ bk, Impossible ad 9 xs.toFinset) wx:=refBuckets_all (forall_cons ww (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma co:Lower aJ ad 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) wy (by decide +kernel)
def kH:List Nat:=varsOf 221
def kI:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffaa0a0fffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wz:Lower kH kI 11:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,16,24)]) (by decide +kernel) co
def cH:List Nat:=varsOf 31
def cI:Nat:=0xfefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dc:Lower cH cI 6:=lift_of (z:=2) (o:=8) (essPairs:=[(VAR 1,8,10),(VAR 3,2,10)]) (by decide +kernel) aI
def cc:List Nat:=varsOf 74
def cd:Nat:=0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ce:Lower cc cd 4:=carry_of (swaps:=[(5,6),(4,6),(2,3),(0,1)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def bD:List Nat:=varsOf 71
def bE:Nat:=0xfefefefefefefefea0a0a0a0a0a0a0a0fefefefefefefefea0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bH:Lower bD bE 5:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) cX
def dd:List Nat:=varsOf 75
def de:Nat:=0xffeeffeeffeeffeecc00cc00cc00cc00ffeeffeeffeeffeecc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dM:Lower dd de 5:=carry_of (swaps:=[(2,3),(0,1)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def dN:List Nat:=varsOf 77
def dO:Nat:=0xfffafffafffafffaa0a0a0a0a0a0a0a0fffafffafffafffaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma kJ:Lower dN dO 5:=carry_of (swaps:=[(1,3)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def dP:List Nat:=varsOf 78
def dQ:Nat:=0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma kK:Lower dP dQ 5:=carry_of (swaps:=[(2,3),(0,2),(1,2)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def aR:List Nat:=varsOf 79
def aw:Nat:=0xfffefffefffefffeeca0eca0eca0eca0fffefffefffefffeeca0eca0eca0eca0
def dR:List Nat:=[5,10,7,11,5,68,5,10,11,66,65,7,72,67,13,72,65,14,68,72,68,66,13,65,14,73]
def dS:List Nat:=[4,8,6,9,6,64,1,2,3,2,1,3,64,3,9,9,64,6,4,8,6,64,12,0,12,9]
def bQ:Nat:=fullMask 26
def kL:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x2c16d5d,0x200ed48),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1222b8e,0x122b94),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1564875,0x1560015),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x34ad18a,0x348c00a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x2bdb620,0x211020)]
def wA:List (Nat × Nat × Nat):=[(1,0,1),(1,0,4),(1,1,6),(3,1,6),(3,2,6),(0,4,5),(2,4,5),(3,4,5),(3,0,4),(1,2,10),(3,2,7),(1,1,11),(3,3,16)]
def aY:BT Decor:=buildWiresBT 5 kL wA
def wB:List (List (Nat × Nat)):=[[],[(1,3)],[(0,2)],[(2,3),(0,1)],[(1,3),(0,2)],[(1,2),(0,3)],[(2,3),(1,2),(0,1)],[(2,3),(1,3),(0,3)]]
def bI:BT (List (Nat × Nat)):=btOfList 3 wB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma df:goodPairs aw dR dS:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wC:∀ x ∈ kL, faithful dR dS x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dg:btAll (fun x => faithful dR dS x ∧ x.1 < 2^256) aY:=buildWiresBT_faithful wC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dh:btAll (fun sw => swapsValid sw = true ∧ permWord sw aw = aw) bI:=btAll_ofList (autos_of (by decide +kernel))
def wD:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 5 0,4),some (subcubeFast 8 0,5),some (subcubeFast 10 0,4)]
def kM:BT (Option (Nat × Nat)):=btOfList 3 wD
def wE:List PoolSpec:=readSpecs ((readChoices 2 (unpackWords 3 [(6,132673)])).toArray) 8 (unpackWords 3 [(18,0x9420418a0a040)])
def bJ:BT (Option BoundPool):=buildPoolsBT 4 aY aR kM wE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wF:Slice aR aw (subcubeFast 10 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cV) (qGoal:=cW) (by decide +kernel) cX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wG:Slice aR aw (subcubeFast 8 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=bD) (qGoal:=bE) (by decide +kernel) bH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wH:Slice aR aw (subcubeFast 5 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wI:Slice aR aw (subcubeFast 4 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dd) (qGoal:=de) (by decide +kernel) dM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wJ:Slice aR aw (subcubeFast 2 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dN) (qGoal:=dO) (by decide +kernel) kJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wK:Slice aR aw (subcubeFast 1 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dP) (qGoal:=dQ) (by decide +kernel) kK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wL:btAll (fun o => ∀ p, o = some p → Slice aR aw p.1 p.2) kM:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aR aw p.1 p.2) (forall_cons (someSlice wK) (forall_cons (someSlice wJ) (forall_cons (someSlice wI) (forall_cons (someSlice wH) (forall_cons (someSlice wG) (forall_cons (someSlice wF) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma di:btAll (fun o => ∀ c, o = some c → ValidPool aR aw c) bJ:=buildPoolsBT_sound wL
def dT:BT (List (List Nat)):=BT.empty
lemma wM:btAll (fun bk => ∀ xs ∈ bk, Impossible aw (4 - 1) xs.toFinset) dT:=trivial
def kN:List NodeSpec:=readDeltaNodes 3 (unpackWords 4 [(24,0xd2110005b1210005a1210005)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wN:checkNodesBT aY aw bQ bJ bI dT 4 kN = true:=by decide +kernel
def kO:List NodeSpec:=kN
set_option maxRecDepth 20000 in
lemma wO:checkNodesBT aY aw bQ bJ bI dT 4 kO = true:=wN
def dj:BT (List (List Nat)):=buildBucketsBT aY kO
set_option maxRecDepth 20000 in
lemma wP:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 4 xs.toFinset) dj:=buildBucketsBT_sound (by decide) df dg di dh wM wO
def kP:List NodeSpec:=readDeltaNodes 8 (unruns (unpackWords 5 [(64,0x5088228148388a0671c438802640e22818e388a061804a18e20108c3009020187100886108b1008c)]) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wQ:checkNodesBT aY aw bQ bJ bI dj 5 kP = true:=by decide +kernel
def kQ:List NodeSpec:=readDeltaNodes 2 (unpackWords 4 [(21,0xcc11110116a321210016)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wR:checkNodesBT aY aw bQ bJ bI dj 5 kQ = true:=by decide +kernel
def dU:List NodeSpec:=kP ++ kQ
set_option maxRecDepth 20000 in
lemma wS:checkNodesBT aY aw bQ bJ bI dj 5 dU = true:=by
  unfold dU checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨wQ,wR⟩
def dV:BT (List (List Nat)):=buildBucketsBT aY dU
set_option maxRecDepth 20000 in
lemma wT:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 5 xs.toFinset) dV:=buildBucketsBT_sound (by decide) df dg di dh wP wS
def kR:List NodeSpec:=readDeltaNodes 3 (unpackWords 4 [(41,0x10a5891111023610a582111102363026111110226)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wU:checkNodesBT aY aw bQ bJ bI dV 6 kR = true:=by decide +kernel
def kS:List NodeSpec:=kR
set_option maxRecDepth 20000 in
lemma wV:checkNodesBT aY aw bQ bJ bI dV 6 kS = true:=wU
def dW:BT (List (List Nat)):=buildBucketsBT aY kS
set_option maxRecDepth 20000 in
lemma wW:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 6 xs.toFinset) dW:=buildBucketsBT_sound (by decide) df dg di dh wT wV
def kT:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(15,9423529742677)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wX:checkNodesBT aY aw bQ bJ bI dW 7 kT = true:=by decide +kernel
def kU:List NodeSpec:=kT
set_option maxRecDepth 20000 in
lemma wY:checkNodesBT aY aw bQ bJ bI dW 7 kU = true:=wX
def wZ:BT (List (List Nat)):=buildBucketsBT aY kU
set_option maxRecDepth 20000 in
lemma xa:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 7 xs.toFinset) wZ:=buildBucketsBT_sound (by decide) df dg di dh wW wY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cp:Lower aR aw 8:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 6,1,65)]) (by decide +kernel) xa (by decide +kernel)
def kV:List Nat:=varsOf 90
def kW:Nat:=0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xb:Lower kV kW 5:=carry_of (swaps:=[(3,4),(2,3),(0,4),(1,4)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def kX:List Nat:=varsOf 91
def kY:Nat:=0xffffffeeffffffeeeeaacc00eeaacc00ffffffeeffffffeeeeaacc00eeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xc:Lower kX kY 8:=carry_of (swaps:=[(2,4)]) (roots2:=aR) (T2:=aw) (by decide +kernel) cp
def dk:List Nat:=varsOf 94
def dl:Nat:=0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dX:Lower dk dl 8:=carry_of (swaps:=[(2,4),(3,4),(1,2),(0,1)]) (roots2:=aR) (T2:=aw) (by decide +kernel) cp
def bK:List Nat:=varsOf 93
def bL:Nat:=0xfffffffffffffffffffaffa0fffaffa0fffffffffffffffffffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bR:Lower bK bL 6:=lift_of (z:=72) (o:=0) (essPairs:=[(VAR 3,0,8),(VAR 6,0,64)]) (by decide +kernel) aI
def dY:List Nat:=varsOf 91
def dZ:Nat:=0xffffffeeffffffeeffffcc00ffffcc00ffffffeeffffffeeffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma kZ:Lower dY dZ 6:=lift_of (z:=17) (o:=0) (essPairs:=[(VAR 0,64,65),(VAR 4,0,16)]) (by decide +kernel) ce
def bt:List Nat:=varsOf 93
def bu:Nat:=0xfffffffafffffffafffaa0a0fffaa0a0fffffffafffffffafffaa0a0fffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bB:Lower bt bu 8:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,16,24)]) (by decide +kernel) bA
def la:List Nat:=varsOf 93
def lc:Nat:=0xfffffffafffffffafafaf0a0fafaf0a0fffffffafffffffafafaf0a0fafaf0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xd:Lower la lc 8:=carry_of (swaps:=[(2,4)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def ld:List Nat:=varsOf 94
def lf:Nat:=0xfffffffcfffffffcffffcc00ffffcc00fffffffcfffffffcffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xe:Lower ld lf 6:=carry_of (swaps:=[(0,2)]) (roots2:=dY) (T2:=dZ) (by decide +kernel) kZ
def lg:List Nat:=varsOf 94
def lh:Nat:=0xfffffffcfffffffcfcfcccc0fcfcccc0fffffffcfffffffcfcfcccc0fcfcccc0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xf:Lower lg lh 8:=carry_of (swaps:=[(1,4),(2,4),(0,2)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def li:List Nat:=varsOf 23
def lj:Nat:=0xfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xg:Lower li lj 5:=carry_of (swaps:=[(5,6),(3,5),(1,3),(1,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def lk:List Nat:=varsOf 29
def ll:Nat:=0xfffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xh:Lower lk ll 5:=carry_of (swaps:=[(5,6),(3,5),(3,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def lm:List Nat:=varsOf 83
def ln:Nat:=0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xi:Lower lm ln 5:=carry_of (swaps:=[(3,4),(2,4)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def lp:List Nat:=varsOf 85
def lq:Nat:=0xfffffffffffffffffafaa0a0fafaa0a0fffffffffffffffffafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xj:Lower lp lq 5:=carry_of (swaps:=[(6,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def cJ:List Nat:=varsOf 87
def cK:Nat:=0xfffffefefffffefefafaa0a0fafaa0a0fffffefefffffefefafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dm:Lower cJ cK 8:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) bA
def lr:List Nat:=varsOf 89
def ls:Nat:=0xffffffaaffffffaaaaaa0000aaaa0000ffffffaaffffffaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xk:Lower lr ls 5:=carry_of (swaps:=[(2,4),(1,3)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def lt:List Nat:=varsOf 92
def lu:Nat:=0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xl:Lower lt lu 5:=carry_of (swaps:=[(3,4),(2,4),(0,2),(1,3)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def lv:List Nat:=varsOf 93
def lw:Nat:=0xfffffffafffffffafafaa0a0fafaa0a0fffffffafffffffafafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xm:Lower lv lw 8:=carry_of (swaps:=[(1,3)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dm
def lx:List Nat:=varsOf 87
def ly:Nat:=0xfffffffffffffffffefeececfefeececfffffffffffffffffefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xn:Lower lx ly 6:=carry_of (swaps:=[(1,3)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def ay:List Nat:=varsOf 95
def F:Nat:=0xfffffffefffffffefefaeca0fefaeca0fffffffefffffffefefaeca0fefaeca0
def ea:List Nat:=[5,10,7,11,5,19,20,5,10,11,20,17,66,65,7,72,19,67,13,14,22,22,68,26,68,65,66,72,14,25,76,73,26,80,21,28,13,66,72,7,10,10,80,25,28,70,82,68,69,81,66,72,22,66,17,80,5,68,65,5,66,67,7,21,20,17,21,84,81,80,84,80,70,88,65,17,65,85,21,69,81,10,10,10,11,17,69,7,65,69,82,20]
def eb:List Nat:=[4,8,6,9,6,18,16,1,2,3,4,1,2,1,3,64,3,3,9,6,18,6,64,18,4,64,6,9,12,9,12,9,24,64,1,24,12,64,8,2,9,12,16,24,12,6,18,6,64,64,18,12,4,0,4,4,16,0,3,64,3,1,4,4,64,64,64,4,1,1,64,18,4,24,16,0,0,64,16,0,16,3,0,64,8,3,4,1,4,1,16,1]
def lz:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f1fc16ed430894a2076abd,0xaa2003034000104a8076a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x49e0100703463a114bb532e,0x2200801404e08004bb5334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xac0e14dcb11b09c517c44d5,0x1400108c0d8b21055280415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x1e020000081b59f88c830a,0x10020000081b59f804000a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc216aff80d25c0f20b10c60,0x401468001044c0900900060),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x741b7f836afe462cf42b000,0x820470803002202408000)]
def xo:List (Nat × Nat × Nat):=[(1,0,1),(0,0,2),(1,0,2),(3,0,2),(1,0,4),(2,0,4),(1,0,5),(1,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(2,1,4),(0,1,5),(1,1,5),(2,1,5),(3,1,5),(0,1,12),(1,1,12),(2,1,12),(3,1,12),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(3,4,6),(1,4,12),(3,4,12),(1,4,31),(3,4,31),(0,6,12),(3,6,12),(0,6,31),(1,6,31),(2,6,31),(1,12,28),(2,12,28),(0,12,31),(1,12,31),(2,2,5),(3,2,5),(1,2,6),(3,2,6),(3,2,12),(1,4,5),(3,4,5),(0,5,6),(3,5,6),(1,4,49),(2,12,49),(3,12,49),(2,31,49),(1,1,50),(3,1,50),(1,4,50),(3,6,50),(1,2,32),(3,4,63),(1,12,63),(1,31,63),(1,2,36),(1,32,36),(2,31,32),(1,2,39),(3,5,55),(1,5,49),(0,1,45),(3,1,45),(0,4,45),(3,4,45),(0,1,76),(1,1,76),(2,1,76),(3,1,76),(1,2,76),(1,5,76),(3,5,45),(3,0,5),(3,0,20),(1,0,28),(3,0,28),(3,2,20),(0,3,20),(3,3,20),(3,4,20),(1,5,87),(1,0,49),(3,0,49),(3,0,88),(1,4,88),(3,1,51),(0,31,51),(0,4,70),(1,4,70),(2,4,70),(3,4,70),(0,5,70),(1,3,53),(1,53,87),(1,1,38),(1,38,87),(3,2,107),(3,0,31),(3,0,51),(3,0,100),(3,2,24),(0,3,24),(3,3,24),(2,24,28),(1,4,115),(1,0,38),(1,0,27),(1,28,38),(1,38,118),(1,27,38),(1,0,58),(3,0,58),(3,4,58),(1,0,119),(3,0,35),(3,2,126),(1,4,126),(3,4,126),(1,2,109),(3,2,109),(2,6,109),(3,4,72),(3,1,48),(3,5,48),(1,0,99),(0,2,117),(3,2,122),(0,4,122),(3,4,122),(0,5,122),(2,2,117),(1,4,138),(3,4,117),(1,0,29),(1,29,38),(1,0,146),(3,4,8),(0,5,8),(0,10,28),(2,8,22),(1,2,22),(2,2,22),(1,4,22),(1,28,129),(3,28,129),(1,8,34),(1,4,127),(1,1,103),(1,3,103),(1,4,103),(1,2,26),(2,12,148),(1,1,131),(0,51,86),(1,1,52),(3,2,33),(3,4,130),(1,2,85),(3,0,169),(3,4,169),(1,5,89),(1,0,83),(1,8,91),(1,45,89),(2,20,83),(0,3,40),(3,3,40),(3,7,68),(1,4,14),(2,5,14),(3,29,117),(1,46,117),(1,4,137),(2,4,137),(2,8,38),(1,22,148),(3,22,45),(1,22,83),(3,4,189),(3,11,122),(1,0,14),(2,122,150),(3,7,122),(1,3,134),(1,0,97),(1,2,196),(1,0,52),(3,2,198),(3,0,157),(1,0,131),(1,0,127),(3,3,166),(3,2,128),(1,14,76),(3,14,76),(3,14,45),(0,3,205),(3,4,175),(3,18,45),(1,3,19),(2,3,19),(1,4,19),(2,40,73),(2,40,75),(1,4,57),(3,3,78),(1,4,94),(1,76,94),(3,0,158),(3,3,164),(1,14,83),(1,4,84),(3,4,162),(1,4,47),(3,23,45),(3,3,59),(3,3,106),(3,27,117),(3,4,183),(2,122,137)]
def O:BT Decor:=buildWiresBT 8 lz xo
def xp:List (List (Nat × Nat)):=[[],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(2,4),(1,3)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(1,3),(0,4)],[(2,4),(1,3),(0,2)],[(2,4),(1,3),(0,4)]]
def xq:BT (List (Nat × Nat)):=btOfList 4 xp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Q:goodPairs F ea eb:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xr:∀ x ∈ lz, faithful ea eb x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma X:btAll (fun x => faithful ea eb x ∧ x.1 < 2^256) O:=buildWiresBT_faithful xr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Y:btAll (fun sw => swapsValid sw = true ∧ permWord sw F = F) xq:=btAll_ofList (autos_of (by decide +kernel))
def xt:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,6),some (subcubeFast 0 8,6),some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 3 0,5),some (subcubeFast 4 0,8),some (subcubeFast 5 0,5),some (subcubeFast 6 0,5),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 10 0,7),some (subcubeFast 12 0,5),some (subcubeFast 16 0,8),some (subcubeFast 17 0,5),some (subcubeFast 18 0,5),some (subcubeFast 20 0,5),some (subcubeFast 21 0,4),some (subcubeFast 24 0,5),some (subcubeFast 64 0,6),some (subcubeFast 64 2,5),some (subcubeFast 64 8,5),some (subcubeFast 66 8,4),some (subcubeFast 72 2,4),some (0x9999999999999999999999999999999999999999999999999999999999999999,8),some (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,8),some (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,8),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f,6)]
def xu:BT (Option (Nat × Nat)):=btOfList 5 xt
def Z:Nat → Option PoolSpec:=lookSpec 253 #[(1,0,5),(1,0,1),(1,2,5),(1,2,4),(0,6,12),(3,2,12),(1,1,2),(3,4,6),(1,1,5),(3,0,28),(3,2,6),(1,4,49),(3,2,20),(1,4,5),(0,5,6),(0,6,31),(1,2,39),(1,3,53),(1,4,70),(1,1,12),(3,3,24),(2,24,28),(3,6,12),(3,5,6),(1,2,6),(3,2,24),(2,31,49),(1,0,2),(1,0,4),(3,3,20),(3,1,5),(3,0,35),(1,4,12),(1,4,31),(3,1,12),(3,2,126),(3,4,12),(3,0,31),(3,2,109),(3,4,5),(1,0,28),(3,4,8),(3,4,20),(0,3,20),(1,6,31),(3,3,40),(0,0,2),(3,6,50),(1,3,103),(1,4,103),(3,5,48),(3,1,51),(3,4,45),(1,0,52),(1,1,52),(3,3,166),(0,4,45),(1,0,14),(0,1,3),(1,1,3),(1,5,89),(2,5,14),(2,1,3),(0,1,5),(1,3,19),(2,3,19),(2,1,5),(0,3,40),(2,12,28),(1,0,49),(3,1,45),(1,1,131),(3,3,164),(1,4,14),(3,0,5),(0,3,24),(1,2,26),(3,2,33),(3,2,5),(0,1,12),(2,1,12),(1,4,50),(1,1,38),(3,3,106),(3,0,2),(0,2,4),(1,0,27),(0,31,51),(2,2,4),(3,0,20),(1,2,85),(3,1,3)] #[0x8042820208002410280002408000101400000050000102800000000000e0400301030a041060000001800002020000012000c08500000c080030206000820c00001078000001000008060018100000008000000428001040a000001300000818000002800000060000002,0x6180000e050000185003008140002e0458a01052a5008280280414000001e4c80205243c10280243c08890060400782050000781000000300000810007030000001800000083000a081400000100000205001a240860b04100000901000058500120830000002a0020208,0x1d381000e9c0a00601060000602801b040a00b810a2a50086002a040c015280468a010c00680818028043001402100001402243c106002008140000028448030a003c10600003c2800c040a005820c000000480000004000001000c820c0000c850000001c00032040080303,0x83381800181010604e06030270281813806011810500011811906040c000382e0c09c080004e060002702000138140000105001808600408814021020a010030c0874e0500007c30000001a0001f020000f828000243001e121800009050078481003c241421d38100001c0c,0x3830b96830200b4181005824300005806015890200a8e04005210200003c240001e030064481003e702001f12040001c080000e050000700c01c0218000280654a0082805004140000c04a41810c00014010000a0140001c0401383020001302804a04140004a0c9110302,0x3c761801d3b0c0001d008000e800035060401c8302009808280547028029081400028080001b860070dc31c37500401ba80200014018054a008036500a00035060098186005038080001c1001a0e020000701800088140333204c880205624010280320c080300c0400e2f0c,0x2180000108012c0860096041400094020004a00000000b499098140484c0a02383028c2c106008a0430000720c01c81054ce408280000068000002311683030002186000100300428018020c00c0001f860000f03003e7618f56090c00d40828000ec300007a00000000e,0xac10000000b0012b0400af5822bd608100005508a94cb8100a65c0800096180004b0a000258280a404140060214028810c014008600013c3004f0218027810a000278100020c3004e4204001810c000c301009a040c023021930a010c01300818000006400602100018108,0x1b005ee0117582408017120400f890c007c48280b6240805a121802d09050002c84581c0c20000a82550b8103]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xv:Slice ay F (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f) 6:=mappedSlice (f:=identifyRow 0 0 4 2) (R:=dY) (G:=dZ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xw:Slice ay F (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333) 8:=mappedSlice (f:=identifyRow 0 0 4 1) (R:=bt) (G:=bu) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xx:Slice ay F (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 8:=mappedSlice (f:=identifyRow 0 0 2 1) (R:=la) (G:=lc) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) xd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xy:Slice ay F (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555) 6:=mappedSlice (f:=identifyRow 0 0 4 0) (R:=ld) (G:=lf) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) xe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xz:Slice ay F (0x9999999999999999999999999999999999999999999999999999999999999999) 8:=mappedSlice (f:=identifyRow 0 0 1 0) (R:=lg) (G:=lh) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) xf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xA:Slice ay F (subcubeFast 72 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=aG) (qGoal:=aC) (by decide +kernel) aI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xB:Slice ay F (subcubeFast 66 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=aG) (qGoal:=aC) (by decide +kernel) aI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xC:Slice ay F (subcubeFast 64 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=li) (qGoal:=lj) (by decide +kernel) xg
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xD:Slice ay F (subcubeFast 64 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=lk) (qGoal:=ll) (by decide +kernel) xh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xE:Slice ay F (subcubeFast 64 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=cH) (qGoal:=cI) (by decide +kernel) dc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xF:Slice ay F (subcubeFast 24 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=bD) (qGoal:=bE) (by decide +kernel) bH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xG:Slice ay F (subcubeFast 21 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xH:Slice ay F (subcubeFast 20 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dd) (qGoal:=de) (by decide +kernel) dM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xI:Slice ay F (subcubeFast 18 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dN) (qGoal:=dO) (by decide +kernel) kJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xJ:Slice ay F (subcubeFast 17 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dP) (qGoal:=dQ) (by decide +kernel) kK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xK:Slice ay F (subcubeFast 16 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aR) (qGoal:=aw) (by decide +kernel) cp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xL:Slice ay F (subcubeFast 12 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=lm) (qGoal:=ln) (by decide +kernel) xi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xM:Slice ay F (subcubeFast 10 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aP) (qGoal:=az) (by decide +kernel) bA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xN:Slice ay F (subcubeFast 8 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=lp) (qGoal:=lq) (by decide +kernel) xj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xO:Slice ay F (subcubeFast 8 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cJ) (qGoal:=cK) (by decide +kernel) dm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xP:Slice ay F (subcubeFast 6 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=lr) (qGoal:=ls) (by decide +kernel) xk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xQ:Slice ay F (subcubeFast 5 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=kV) (qGoal:=kW) (by decide +kernel) xb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xR:Slice ay F (subcubeFast 4 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=kX) (qGoal:=kY) (by decide +kernel) xc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xS:Slice ay F (subcubeFast 3 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=lt) (qGoal:=lu) (by decide +kernel) xl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xT:Slice ay F (subcubeFast 2 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=lv) (qGoal:=lw) (by decide +kernel) xm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xU:Slice ay F (subcubeFast 1 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) dX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xV:Slice ay F (subcubeFast 0 8) 6:=slice_fast_direct (zDead:=0) (qRoots:=lx) (qGoal:=ly) (by decide +kernel) xn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xW:Slice ay F (subcubeFast 0 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=bK) (qGoal:=bL) (by decide +kernel) bR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ac:btAll (fun o => ∀ p, o = some p → Slice ay F p.1 p.2) xu:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice ay F p.1 p.2) (forall_cons (someSlice xW) (forall_cons (someSlice xV) (forall_cons (someSlice xU) (forall_cons (someSlice xT) (forall_cons (someSlice xS) (forall_cons (someSlice xR) (forall_cons (someSlice xQ) (forall_cons (someSlice xP) (forall_cons (someSlice xO) (forall_cons (someSlice xN) (forall_cons (someSlice xM) (forall_cons (someSlice xL) (forall_cons (someSlice xK) (forall_cons (someSlice xJ) (forall_cons (someSlice xI) (forall_cons (someSlice xH) (forall_cons (someSlice xG) (forall_cons (someSlice xF) (forall_cons (someSlice xE) (forall_cons (someSlice xD) (forall_cons (someSlice xC) (forall_cons (someSlice xB) (forall_cons (someSlice xA) (forall_cons (someSlice xz) (forall_cons (someSlice xy) (forall_cons (someSlice xx) (forall_cons (someSlice xw) (forall_cons (someSlice xv) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))
def xX:BT (List (List Nat)):=BT.empty
lemma lA:btAll (fun bk => ∀ xs ∈ bk, Impossible F (4 - 1) xs.toFinset) xX:=trivial
def lB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd7a440356dda44034e8ac35100d739b6340035586fe9100d),(44,0x5f569100d5229a940034c91685100d5b1)]))
def lC:List NodeSpec:=readDeltaNodes 4 (varNats 3 (unpackWords 4 [(49,0x28a18e3b100051de1ba2f410051c87d1d200051c84c521005)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchxY:∀ b ∈ ([lB,lC]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 4 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y lA (by decide +kernel)
def ya:BT (List (List Nat)):=refBuckets O [lB,lC] #[0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,2,0,0,12,0,11,40969,0,0,0,0,0,0,0,0,0,5,0,3,0,0,0,0,0,0,4,0,0,0,0,0,0,1,7,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma bw:btAll (fun bk => ∀ xs ∈ bk, Impossible F 4 xs.toFinset) ya:=refBuckets_all batchxY
def lD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x201cac361d5a201caf52224807186c549201ca433a85100e),(51,0x75c4924038eb0924807194d98a24038ca64a4a)]))
def lE:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xbe2210116018a1891121106681bd2f22100167c1a39210006681a81a2f221016),(48,0x1b81be2a522101622f87e2a234102659189112100601cc11)]))
def lF:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb2b44310163a81be23b121016122f52100619c2c2d72100639c1ac292f221016),(43,0x1ea32b19210062ca1ab2b44310162ad451110062fa7)]))
def lG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe6c33aa8807266f35100e7e43a433a85104e52c33a85100e),(62,0x990ec6a201c8ecd2201c7486d33aa88071959bcd440394)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyb:∀ b ∈ ([lD,lE,lF,lG]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 5 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y bw (by decide +kernel)
def lH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38f86caca401c6cafad1544038c8af30d44038ee7669100e),(57,0x3a65ec9001cf197b2400703f47d140838294db0a408)]))
def lI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3273bd69100e3e736b488072b33bcef4c2502707e149120e),(55,0x643ee44900e5f6249201cbea89200381d6a25120e)]))
def lJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3ef322280071fbb88a001c0cb1cc7dc4a049c0ff9545020e),(64,0x25120e0e5c67cac30a249c14b0a489070336c7c3e669124e),(6,12211)]))
def lK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x28e0fd2ab40838fb0cbd124039dea7ec9001c7d8b624800e),(64,0xda99a92400703a433524820e735449001c11bb43ff3f2e90),(1,1)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyf:∀ b ∈ ([lH,lI,lJ,lK]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 5 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y bw (by decide +kernel)
def lL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x400394d0cbd9200394bccbd920039cf112400739a224800e),(55,0x75e65cc9001c75a65ec9001c6fe65c89201ceca49)]))
def lM:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x9c1ac24e22102629d18f311000628c18f31100063aa211100061ce18f3110006),(48,0x5ce41b918c1b22002619c1ae4b32210163ae211100063883)]))
def lN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x395c65ec9001cad32f64800e5bd33a85100e5f73a2a4900e),(64,0x3718410703be3e528920e07db9c33e37a44938df0e8a9240),(6,14753)]))
def lO:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x22110618c4a28e1120016691ac1220006028a1be211010607bc1818e39210116),(49,0x7f81bc2f221001642b18e3921010642c1e91121106411b92f)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyj:∀ b ∈ ([lL,lM,lN,lO]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 5 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y bw (by decide +kernel)
def lP:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(63,0xf4c4a20038ffa3f8fb5220139e9512400718b437e28820e)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyn:∀ b ∈ ([lP]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 5 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y bw (by decide +kernel)
def yo:BT (List (List Nat)):=refBuckets O [lD,lE,lF,lG,lH,lI,lJ,lK,lL,lM,lN,lO,lP] #[1543839821,0,96,1124323333,23,37,59,75,58,401424,872562696,55,1426173956,1627643930,0,94,409610,200715,5773224763401,48,0,63,331832,0,0,368712,7,356421,33,2,340021,0x6305b049039020,389191,0,380942,327695,44,270381,266290,13,29,364579,637648915,352298,21,0,221214,0,1174503442,31,0,0,0x3302b028014006,76,319548,0,22,323609,688025634,69633,278592,360460,303107,0]
set_option maxRecDepth 20000 in
lemma ai:btAll (fun bk => ∀ xs ∈ bk, Impossible F 5 xs.toFinset) yo:=refBuckets_all (allCat batchyb (allCat batchyf (allCat batchyj batchyn)))
def lQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x339c8a209e643319d424904f06f39124827991990e45104f),(64,0x249241ea28675092413c1d0e449241e142675092493cc867),(6,44495)]))
def lR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x464ef124a0cf0ae5148492493c1921c512483d787924900f),(64,0x87524a241e6ec492800799729df24a009eb65e125000f4ee),(3,30)]))
def lS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb19b9a20a3cdb8924900f0e552924920f21eca672124944f),(64,0xe4924047847486786f289051e0e3745b1bc9441478569b61),(28,0x3b636e37944804f3ac06f)]))
def lT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249041e6e87e37928804f0e4589b922093cef0ef8924804f),(64,0x876251049e16a77249009e65c5124007a3f42492413c1f31),(6,10516)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyp:∀ b ∈ ([lQ,lR,lS,lT]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def lU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3262492003d03242492023d78fd2492013c2f0c3ba24824f),(64,0xbf1f8c9494412787738ff4ac87d32525104d3d490924800f),(18,0xfe64a4a2003c1)]))
def lV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdf9249009ea43a52492013d48b43a928804f52192928800f),(64,0x2083c390d914a492493d4b4924800f30dd0fb4924824f5e1),(10,66145353)]))
def lW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x78733251009ea7a49240079f4e84a2003c390fb0924824f),(64,0x691669e0e5f43644ca24a3c1ca4cec5164d2259e7de49240),(25,0x3211bf1932beb931ce2)]))
def lX:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1019c2c2d25212163019c292a522121601b81e8511111117438e29e231121117),(59,0x6822f31121017019c22f4121116419a3c42d2322112719c2c2d23221017)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyu:∀ b ∈ ([lU,lV,lW,lX]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def lY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf0fea73512493d1766354e6928a27b2adce43a637b25148f),(64,0x8ca2493c2bf2cac322ea18614498790e786d8b4249289ecc),(57,0x1996f8d8a78632510cf5ec322ab18614423c2fa19f1)]))
def lZ:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xc71c441211372c1fb44111101702c1bb4411111173a81db1d82c292b44121047),(64,0xb181210663aa2851e4412102701da1ce4312111173c2c1cc43112102702be5a2),(17,0x4e1c818a2c1f486f2)]))
def ma:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x4121247019c32f4121116058739e22b4412113751303bc7b19c1ed2b18121436),(64,0x482d2b441211273019c2c2b4412121723ee1cc2b44121027303a842cd38e32b4),(22,0x3c8486f2b7112112703bc)]))
def mb:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x279c015718614513c2db1f19bd9289478521f699cf25124f),(64,0x28f0e4321d9928927a877c75c653ab25128f72e4ae30c288),(40,0x6fec643798614493c2b7391ca63251)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyy:∀ b ∈ ([lY,lZ,ma,mb]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mc:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x703ea293a3211111734819c4f18111111704814f451111176048292e45111217),(64,0x9c1c858191111160481f584412111729a18b19c6f4412103603a81eb71111111),(2,1)]))
def md:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc6e3d12493c1923971d22d0f44928f0f2d7291de632512cf),(64,0xe454ecc94513cf73e57731928847856f3c9249078326c7c),(35,0xed1928804f3e1f718c94413d4)]))
def me:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3ae7c92810783a57192510785a564a2013d698ed9944804f),(64,0x9f144800f0bfcbd5a144824f7b1b6944800f30d94a240078),(3,121)]))
def mf:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x270781f21110107023ee5c5c58121101375c2d91111100175c791ae21110017),(57,0x2aa1cf63111211707c3211101074d82da3121100173ee5c619e12110)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyC:∀ b ∈ ([mc,md,me,mf]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mg:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xbd5cc94413c390dd0dac94493ce91d649401e758ab24a00f),(64,0x5e1fcd94924827b90da77ac94413c1df1b0ef5928927b90c),(16,69952688394255)]))
def mh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x25104f5be3629cef5928847852664a2013c3914d1924924f),(64,0x798bdc4924107960fd0924860f721deb249209ee4561deb),(12,1977913921)]))
def mi:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3bf38924927836e4be84924147af79249001eee32a24800f),(64,0x2810783b570928107852c3bc54928127804fb49249278374),(10,30841097)]))
def mj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8663ed449009ea5e4924007852f449041c58329f6a24860f),(64,0x449001e0fb8ca892083c2963449041e0cde1f3144a249e6e),(6,63671)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyG:∀ b ∈ ([mg,mh,mi,mj]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def ml:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd5a24848f33ccae8ca2402783765a924804f0f65a924820f),(64,0x7242492093dc8bf8c9248279f339723ab25108f60cb62915),(27,0xded148aceb7689251e62)]))
def mm:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x5158c3965a11102175158a7a65911112171b81da5e211100171b8165a1110017),(51,0x19b5e1111100701ac4d111110171f9111110060395e21110017)]))
def mn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x27adccf149deec94423dc857f9928827bf219b9fb124904f),(64,0x9e0cca7e892083c2367ce4eca24147b3668e63a45fa249),(29,0x1d17e892003ccf0fcbf449)]))
def mo:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x71a918f211100073ea5b2b81111101719c3875a111001758a797591111017),(48,0x5bc4a3e5821110177b55811210077b5d11111007618f2111)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyK:∀ b ∈ ([ml,mm,mn,mo]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mq:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11912201370225be22ab581111114739c1ab58111110173c58a493f582111027),(64,0x7e18a21ff591111015730285be7e192111022705d828f582111011704fa5843e),(22,0x5ea2985911110117063d8)]))
def mr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2003c3f56449041e0db939b1249051e16c6dc96d892482cf),(64,0x3cdd1cf4924804f5e2f1f84924047af1ecea24804f7e2e89),(20,0x6fd16b96851209)]))
def ms:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x60cf1eaf224844f06ed16d168892093c1bf65af5a144824f),(64,0x7fab4249249eccb11240078314aa724a049eef32224800f),(27,0x11b6c5e2962d0a241678)]))
def mu:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x17068c4c4b211101173068a4b4b2111021719c2f5821110017028d5812110107),(56,0x19c2db582111001702b6c211101070296c111201075d81af58111110)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyO:∀ b ∈ ([mq,mr,ms,mu]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x33c53197224827232d449001e4cb512400785275a924804f),(64,0xbd124107932f449001ee786cab4249209e6e87f5a224804f),(4,140)]))
def mw:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xc321110174c7b5a31121017019c6d3f582111117418f21110007318f21110007),(51,0x402a18f211102072c18d1112000769c26858111110275be4918)]))
def mx:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x76f18f2111000702c95de6d18c321111271c8591111000745d82dd5821110117),(61,0x6ac3ad3121100174c18f1fa3112101702af5a3112101719c1a818f2111001)]))
def my:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb729223a533e44900c3c2d0c32c2a9481479de99f124900f),(64,0xba9249009e74c67e492003c3da3f8c991ba99f9248261e8c),(34,0x1490cf8a24007af948492403d3)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyS:∀ b ∈ ([mv,mw,mx,my]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mz:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11120706838181111107484a2b2b1812101728a19e2111000728919e12110007),(55,0x12bc7111111075ba1a84e711210175be1818872111017603882b181)]))
def mA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3c92482783ae5e928804f5a2f4a2400785f67b99d444824f),(64,0x8658b4289059e1698d9ccea224127bf8d94cea144027a3bf),(30,0x2d7196ad0a24127846ff97)]))
def mB:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1e85d112100176a2d211100073bb1111100071885d1211000706c2b21110107),(52,0x183c19a2f1811111173c2e19e2b181210176ea7b2b2b18121017)]))
def mC:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3cc0fec67e675092513c1d299d424920f3819a9d1424940f),(64,0xe4a201e1fb133e12412796ab3b94420783bdca686750a209),(23,0xf55a2849201ef7571)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchyW:∀ b ∈ ([mz,mA,mB,mC]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xce9fc92083cfd14ea144007833c47d449049e7d87924900f),(64,0x6e45bd53a849249ea435d91424904f522ff9b9524804f6bc),(15,8614398165007)]))
def mE:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1075be491887211101768e4a7f721110173683a8711111117302ff3d21110117),(49,0x698394e722100176b2c211100073bd11111000706d2a21110)]))
def mF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x44804f3c83faf4944227af2af4a2400799e3b4c90f44904f),(64,0xc67c4dc91049e0fba3875a492493dddcc289001e7d99df19),(36,0x9e367c54b9cd4dc51209a783ee)]))
def mG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xfe928804f30fd4924807b979d0a2400783f58a1bf124824f),(64,0x3c83678b687c36c29048e07dcf925020f5ae2492003c19b1),(18,728013644010505)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchza:∀ b ∈ ([mD,mE,mF,mG]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def mH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x291e7da6424a001e7eae125000f20ff4dab68ef3e52504ce),(64,0x91e583bf37128860f301d71ba93724422790b47213e4249),(40,0xb4721f39249051e42d1c86737e249)]))
def mI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc4924107980f9ce8892103dc87c3e4249209e1e90924804f),(64,0x241479be2d4944007b91e87c8492413dc8bca492402798a7),(13,14735363145)]))
def mJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2413ccb0f911240078721939f2224824f075cf9f6928824f),(64,0x32d3e4249209e6f3e4449001eceb8dc7c8892093c1c7c849),(19,0xc52d251041ee4)]))
def mK:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(60,0x7d4b4944007b5362492083cffce249201ea4a6128800f)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchze:∀ b ∈ ([mH,mI,mJ,mK]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 6 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y ai (by decide +kernel)
def zi:BT (List (List Nat)):=refBuckets O [lQ,lR,lS,lT,lU,lV,lW,lX,lY,lZ,ma,mb,mc,md,me,mf,mg,mh,mi,mj,ml,mm,mn,mo,mq,mr,ms,mu,mv,mw,mx,my,mz,mA,mB,mC,mD,mE,mF,mG,mH,mI,mJ,mK] #[4312780902,0x14a1450f50e60e00d60ce062,0x10f0ff08d08a080075,0x13a1170f60d90bb06105d04a03b039,85865883159191660,0x12d1230e40a807c05e,4345565242,82772407865364542,23916861181956,0x15213f1300c90be0a0011,5218734089,3406274589,9553433600064,75442097792139282,0x13412712105f05a031,0xc504e02f019,22200988840024,0x1090b109a06d05b024,89,80801326241792075,3054002308,0xf003800a002,0x13b1221080dc074025,0x14012f06f06702e00e,17733501038693,93188699923742824,0x1331130f40d70d30c409d056048001,18351825563763,0xee0ed06e057052016,0x14713d1320fe0f80c0021,0x151092077054047008,5688824132,0x1241190f10d10c80ac09706904f037,4749054130,0x15a14c12e0e10dd0cd0ba09e08307202a01f01800b,790661,5822394391,0xf30d40a5081,5252026411,3490156656,87277586648567868,0x15014f14e11a10e0ae,0x1410c30b80a109f08e003,0x12911c0e50bd026015,0xeb0c609b09103f027,1409159,0x1461161140a707f053036029013,0xfb09c08f089088071,89522926394867739,4798390287,0x15913c0ef0cf05103201c010,0x1561050b709908c064060,0xec0b4043035014007,84176002036740126,0x11d1100e80c20b50af09800c,0x1550e20d5046045023,0x10a1071040d20a407d044,22886924853324,0x1421380fa0ea0a2022006005,0x12c1251180bf0aa09508206b04902000d,126,0x1570f20e30a60a309603402d,0x1351200f70df0b0078028,5705597205]
set_option maxRecDepth 20000 in
lemma aE:btAll (fun bk => ∀ xs ∈ bk, Impossible F 6 xs.toFinset) zi:=refBuckets_all (allCat batchyp (allCat batchyu (allCat batchyy (allCat batchyC (allCat batchyG (allCat batchyK (allCat batchyO (allCat batchyS (allCat batchyW (allCat batchza batchze))))))))))
def mL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3c924a67854ce6e50ce72249261e428ba714321c4924a354),(64,0xe0fccd362b8e2492498a071e6a1ca538924926a843ce28ad),(64,0x7c928167848c58e86c51e249409ca1f0fab650cea1250061),(12,3178965117)]))
def mM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x26cccdc494414a108cf0d94924948f20f76bf8d9892504cf),(64,0xb22b578619c924826a84230f87678d9ceb8ea6f249211ea0),(64,0x20a50df1c50ec6f2492035083267a9d72c6f249213502321),(15,998248452681)]))
def mN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4a05f198ec492412a2d91d79249202502b16c95e492482d4),(64,0x86c3f124920b5029168b9b09d89248262815ca1b0ea89241),(47,0x1458ec492412a03e45143b124905280cd8e)]))
def mO:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x81b2c18b1111102571041cc4d18b1ee2c6a1111102671fe18b19c7b111110037),(64,0xb29c1cb1211016607c18c1fd2aa18911111014701fd2aa189112101261025a1a),(61,0x7c6f3e1fc181dd1211015603c3d1ca591c8181db11111016706c24b1cc1d)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzj:∀ b ∈ ([mL,mM,mN,mO]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def mP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8492414a07f187ee6e5665cdc4924135420ef8f90924844f),(64,0x81e557f164c92496a306caa6c75aa5ced2492118786e454e),(64,0x4513d121c8e6a7fc678664d226187108c57e563899249462),(14,826370610377)]))
def mQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x58c6492498a03e2df2fdfca18c924931420cf14e6924944f),(64,0xd8d9ced1c31924926280ebcdd158ac3192492d40b1997b1e),(64,0x994d8cee6eaf86786730c289c71c1db9e78c64924a502bb2),(47,0x503163363ee361dd586731928b3cf4c940c)]))
def mR:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x72105b19c4f43111113218353029a18b19c4f441111437302e84c4e431121227),(64,0x102c295b19c19a71111124707d3cc485843111111318029a18b19c5844111113),(46,0x2102c739e2d43111113318318022a7d19c298711111347)]))
def mS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24924a8885f66e7efd86e319249662842da19e1d9924948f),(64,0x9938c92826a07619eb249209502ba191924904a81587de63),(64,0xabe86ccca2423cf51598ed1f561f1c649401aa30f68f5a65),(18,6833383002258204)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzn:∀ b ∈ ([mP,mQ,mR,mS]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def mT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8c503bf1997864cf924905a86dc7f8665e19738ca240314),(64,0x6a03a456c50eafe367649241354301db1f719978a48f9249),(64,0x87dcfe5232492118a05b27fbe492414a056c5b23abe49241),(31,0xc1f1786dec924849460dc6f)]))
def mU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xcc92496a03be3bd6492412a220c95fc74aacc77ac924b30f),(64,0x50b07f33c3243292490d280ef8fcc92482540e4cb75e1bfb),(64,0x249209513216b158accc924831285853451587fc6524921b),(11,483450469)]))
def mV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3e66492424a308db94739b723ed249211c787e9949248214),(64,0xcc92484540a4a65249208502d62b0eb0ca492414a30a68bc),(64,0xf1c7d586fec924847a81790db0e86c6b42492098a3066f9d),(14,1664238099725)]))
def mW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24c2a1d21f145fe289019cc2fb1f61dcc86c3ff649242354),(64,0x326856ed12426a3065914561bab24921351a20cf0cc75649),(64,0x19e69067872d0924865468a20cf0e5a9248389ec19a47af),(23,0xa6c64e6786c8bf249)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzr:∀ b ∈ ([mT,mU,mV,mW]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def mX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24908e3d833c555a492422a1611b72d8cd4cf15a4924334f),(64,0x4cf6885e45b99e19e2f8924831a8c19e236e5b19a99e1fb1),(64,0x24904d51833477e522b32f192494d4614d8c9ccf17f99249),(49,0x1a4a0678748bf4490693c1cfc766332f15f99)]))
def mY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc66a678ae84924334f06787ad0924825460cf0f5a924844f),(64,0x8db96c66a67867a4924334f067876abf24920950b08db96),(64,0x3b42492013cef8f8a2d222480ce3ad3a6562bb12500ce34c),(3,124)]))
def mZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x61ed11b71fccd91fd5249211ca307432fcac3245a12494cf),(64,0xee924905a81f912961f5724920b501b345a187e5892482d4),(64,0x501b665b23a19092482d460cf219e1d9e249212502f16c8e),(25,0x33ee6ed0f8b424920a)]))
def nf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24920a5185219f73768e2d092484d46148b646a9c92484d4),(64,0x2c19e35692490ca84a07632f86787e5a2248319e16c8fab4),(64,0xe6a411b72d8cd4cf0cbc924830d3d07ccd319e197a2484ce),(29,0x140c86598cf0feb44490d9)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzw:∀ b ∈ ([mX,mY,mZ,nf]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def ng:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x915ac92492a3f71d6b249209e5832196633c3fad092486d4),(64,0x3a7cb55e193324920b5185219f73768e55a124909a80cf0c),(64,0x294616d94fcd961fd5ad12426a140c8763658658d1243678),(22,0x2de19e1b72d09248)]))
def nh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9592494cf53632733c5752492033d4d8c9ccf1cb092480cf),(64,0x766332f15f1924904c502b0cb8fdd9249254614d8c9ccf1c),(64,0x528c236e5b19a99e196aa49242354301f16849242278526),(17,99060829327945)]))
def ni:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xeb64fe3212490128c19e1923c492422a252c3275c9248094),(64,0x50237e8ac57a94f24925a8703be37de75b147699d4249461),(64,0x2413143483ed72f36cca1f71e49259878324ca6571e49249),(23,0xdf22f1dafe5d4509)]))
def nj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x98eb15bd799433e3ca24238f08e932996abc3f3e49241354),(64,0x2413140745ff76c3e19492482d40b58a45565092414a1073),(64,0x24908c503b22b73b97361ee2849209aa05a671f5629e1e49),(50,0x237ecae38ec672492098a30f43e4571c6d339)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzA:∀ b ∈ ([ng,nh,ni,nj]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def nl:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5df86687feaeca1d71e51211e7b0b63673b43ac3c92484d4),(64,0x50d7942490528d872437f4b65e1d273bc8afa492433cf216),(64,0x24905a816d15c71d0da492416a038eda19cda492414a0776),(63,0x5a20fb8d86d94dbb19f19d424934c3c3be1daf3bc8adc79)]))
def nm:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x698a13185b433c6772490623d361f98f73e4675092418d4),(64,0xd21b0d9b99fe3e1d29e49259a7a6885ae31dbdfb199d4249),(64,0x2490715199f630f867c673c92496a1f0e94f24920150d20c),(44,0x616e6786d33a84921251228833c3619d4)]))
def nn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2193cf20cf1e36a849219511617aa7c64cac67624920c314),(64,0x32733c76d509242679e418a474dca124869435833c74fc49),(64,0x2436a03af8ac4b424920a5110b733c5e653a84921a508536),(22,0xd60dff18a474fa49)]))
def no:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2095019ee56192294f24925288830ebe9dfe76d3c92486d4),(64,0xb0d529e4a2095183b487c391b0d84924231407c98dc66249),(64,0xa7a2486943515b433c5cfa492434a18599e387c249219502),(14,758306709396)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzE:∀ b ∈ ([nl,nm,nn,no]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def np:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x50f26432cc6786487924909a848334a6436fc6487a2486cf),(64,0x24920a501bf63168aaf492482d461d8b636587f529e89213),(64,0x9975e924908a8599f236e5b19a99e3d09248471e0c5a2cbd),(29,0x1441d3c3d5c492418542dd)]))
def nq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x31a86a214b8cf0c87d24920c4a3074a6dd8d955c79249494),(64,0x20b503923b31997874cc92482628d10e19253e68e53c9248),(64,0x20b503c66d0ff0cafe33f37124904d501d6e332f0e94c249),(50,0x1906cf8ff1477f2890d9c0eda1997867a74249)]))
def nt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249219a7980cf0ea7fa492422a29b19399e29e9b212480cf),(64,0xa492434a2462dccf15c7fa492434a186046dcb633533c5a7),(64,0xdbe7f2d612490d9e7906786d867e492432a3216e6786fa7f),(41,0x107d98eb54b8e95f24a099e6180eb39)]))
def nu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4133c83f7cafeb68758e12504cf20ff4dab6875ea92504cf),(64,0x841b9787ee6e3a6721bb1b89248472841d159d6d0e90c849),(64,0x90924826a80f86c32f5a92490528c1b968e43743a124909a),(44,0x61c869f2124908a80fd0c3ad561df1b0f)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzI:∀ b ∈ ([np,nq,nt,nu]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def nv:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x24921350a212d978e2902969249061c78721d4f909248254),(64,0x86c561f212490528c2df1b14e7c8492424a30fe31786d3e4),(28,0x60e86c3ec32924909280f)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzM:∀ b ∈ ([nv]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 7 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y aE (by decide +kernel)
def zN:BT (List (List Nat)):=refBuckets O [mL,mM,mN,mO,mP,mQ,mR,mS,mT,mU,mV,mW,mX,mY,mZ,nf,ng,nh,ni,nj,nl,nm,nn,no,np,nq,nt,nu,nv] #[536617,0xd90b00a906b06205d021,0xae06704c04902a,0xc60c10ab09b099058,2097475629,0xa40a003202f,8866775613465,0xdd0ce0ac03401b,3741773832,8178792402962,0,3439894629,3070619739,0xb806404201d,0xbe0a206a053028,2416193539,0xcf0bf072050,150,0xb60a504a026024,0xaa07e059005,61,3221504016,3590901844,0xe20ad09104003b00d,0xe506c01e006,426001,0xd80c808500b,0xcc0c30b206004b,622641,3104522250,0xc209e092020007,917690,0,2063966217,0xa807a06604803e018,868519,3657982012,0xd507c078033030001,0,7697521135644,130,0xbb09304503a02b,3389636627,0x9f08006e02e025,0xa60a109706105e,3507171415,2131136546,471153,3859345489,3825287180,0,0xcb0bd0b10a3047,315415,815118,0xd309a08904e,0xd709508e08b07406d02300f,823395,0xe30de084039004,0xdb09407905c016015,3289104438,9277783797762,0xe10d00b5056055052037,0xdc0d208c08807601a,0xc50af09d03f]
set_option maxRecDepth 20000 in
lemma cq:btAll (fun bk => ∀ xs ∈ bk, Impossible F 7 xs.toFinset) zN:=refBuckets_all (allCat batchzj (allCat batchzn (allCat batchzr (allCat batchzw (allCat batchzA (allCat batchzE (allCat batchzI batchzM)))))))
def nw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6a3c4928234f60c57350f24941187906f7898a1c4924a34f),(64,0x36d3b650ea4924827a841d9c32526786e2492423542164e4),(64,0xf8d8bc249211a785299e19f9f728b7249209a78573f0ea66),(48,0x20df95ed394ef148e4249211e790a48ad33a)]))
def nx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2168fd33e3ad52e52924908d3c8762fd4f0c50ce4924234f),(64,0x38f242d0ffceb0cf132492cc3c3f9eeb58b9b1ca4924134f),(64,0x9a3ba993e7192490d4519a490acaa6ce7a94d0cf0c64924e),(64,0x472858362b218b4e8cdcc9f3cc924867a85871590f329fea),(34,0x18571f39da1dab98cf168c9248)]))
def ny:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf17bcc325864e678b7649241eaa80fb8c9ccf149492482cf),(64,0xc67c76cf65ef30c9619399e2f1924906aaa344920c5b43f1),(64,0x8a7e49241a69e4a06e8e19ed326c6786ca49241869e69282),(64,0x8b45f25253f632733c564249212879a4a06e8e19ef327867),(64,0xac9248672869282dd1b72d8eabdea68678b424920d50f417),(26,0xa0bd8f7e63f22fccf15)]))
def nz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x415fd4b8c73e74cf0fdd92490ce51832e32c50ff892484cf),(64,0xbb993653650cd0f2492cd3d046dcb633533c33e249211a79),(64,0x522c792490945085e7314d178ed7f287924908e519075f8e),(64,0xcd3c85b297bb17ea78628e1e492423d421cf9c312df2867),(24,0x6439b276e314369249)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzO:∀ b ∈ ([nw,nx,ny,nz]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 8 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y cq (by decide +kernel)
def nA:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1105718212111106ae2ed2f83c2b181111018471039a23ae4181e71111102518),(64,0x106ba1dd4d96ec39b3cd6fa4b181111047731110284aa1f82a39b2f83c2b7111),(64,0x9e29a22d2ef29819c4971111105181821036ba2df18a29a184b7111110361812),(64,0x2d95f5e3ac4e7111110571834111101b82cd13e938c48a5d1111107673111024),(14,4803777482446334)]))
def nB:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xe7e1fd111110357304ef286ea184d5b1111024731059d7986d7e1cd111110347),(64,0x6ec197e1a811111054723305f18d1cb3de185e19f11111045182603ba5f959a1),(64,0x121021fc2ed421bf4b81ad12110476121023bc3ea3c4f5c21f11120467412102),(27,0x3107b422e86d7e18e1f12110367)]))
def nC:List NodeSpec:=readDeltaNodes 2 (varNats 3 (unpackWords 4 [(59,0x1062ca19d2f28e1bf291111102518412105841fb2e4c1de1e8111110567)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchzS:∀ b ∈ ([nA,nB,nC]:List (List NodeSpec)), ∀ ns ∈ b, Impossible F 8 (nodeValsBT O ns).toFinset:=blockGroup Z 9 (by decide) Q X ac Y cq (by decide +kernel)
def zV:BT (List (List Nat)):=refBuckets O [nw,nx,ny,nz,nA,nB,nC] #[0,822247453,0,184351,36,73732,47,19,24,15,167971,0,43,0,0,0,13,188455,0,9,0,6,0,27,0,0,838873090,20,0,21,0,28,0,1,14,0,37,0,102416,38,30,0,139297,0,44,8,0,7,0,10,0,11,42,0,0,106519,196630,12,32,0,69637,0,0,0]
set_option maxRecDepth 20000 in
lemma zW:btAll (fun bk => ∀ xs ∈ bk, Impossible F 8 xs.toFinset) zV:=refBuckets_all (allCat batchzO batchzS)
def nD:List NodeSpec:=readDeltaNodes 6 (varNats 3 (unpackWords 4 [(64,0x1c07111110184751120586849d38a19c3111110557107b4a4e18341111110267),(64,0x8942985c441f1111104674111104fb4179c71819f1111106673131111039e398),(28,0x1210422ca3c42911111045712102)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zX:∀ ns ∈ nD, Impossible F 9 (nodeValsBT O ns).toFinset:=blockOk Z 9 (by decide) Q X ac Y zW (by decide +kernel)
def zY:BT (List (List Nat)):=refBuckets O [nD] #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,6,0,0,0,0,0,0,4]
set_option maxRecDepth 20000 in
lemma zZ:btAll (fun bk => ∀ xs ∈ bk, Impossible F 9 xs.toFinset) zY:=refBuckets_all (forall_cons zX (fun _ h => (List.not_mem_nil h).elim))
def nE:List NodeSpec:=readDeltaNodes 1 (unpackWords 6 [(20,0x83041041028c03101041041007106)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aa:∀ ns ∈ nE, Impossible F 10 (nodeValsBT O ns).toFinset:=blockOk Z 9 (by decide) Q X ac Y zZ (by decide +kernel)
def Ab:BT (List (List Nat)):=refBuckets O [nE] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Ac:btAll (fun bk => ∀ xs ∈ bk, Impossible F 10 xs.toFinset) Ab:=refBuckets_all (forall_cons Aa (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dp:Lower ay F 11:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 6,1,65)]) (by decide +kernel) Ac (by decide +kernel)
def ec:List Nat:=varsOf 138
def ed:Nat:=0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nF:Lower ec ed 4:=carry_of (swaps:=[(6,7),(5,7),(4,7),(2,3),(0,1)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def nG:List Nat:=varsOf 143
def nH:Nat:=0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ad:Lower nG nH 8:=carry_of (swaps:=[(6,7)]) (roots2:=aR) (T2:=aw) (by decide +kernel) cp
def ee:List Nat:=varsOf 158
def ef:Nat:=0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nI:Lower ee ef 8:=carry_of (swaps:=[(6,7),(2,4),(3,4),(1,2),(0,1)]) (roots2:=aR) (T2:=aw) (by decide +kernel) cp
def eg:List Nat:=varsOf 159
def eh:Nat:=0xfffffffefffffffefffffffefffffffefefaeca0fefaeca0fefaeca0fefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nJ:Lower eg eh 11:=carry_of (swaps:=[(6,7)]) (roots2:=ay) (T2:=F) (by decide +kernel) dp
def cL:List Nat:=varsOf 202
def cM:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cB:Lower cL cM 7:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,3),(0,1)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def ei:List Nat:=varsOf 203
def ej:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nK:Lower ei ej 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(1,2),(0,1),(0,3)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def ek:List Nat:=varsOf 206
def el:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nL:Lower ek el 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(0,1),(2,3)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def nM:List Nat:=varsOf 199
def nN:Nat:=0xfffffffffffffffffefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ae:Lower nM nN 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(1,3)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def nO:List Nat:=varsOf 205
def nP:Nat:=0xfffffffffffffffffffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Af:Lower nO nP 8:=carry_of (swaps:=[(5,7),(6,7),(4,6)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def aZ:List Nat:=varsOf 207
def aK:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffeeca0eca0eca0eca0
def em:List Nat:=[5,10,7,11,65,68,5,10,11,13,66,65,130,129,129,7,14,66,72,130,13,14,68,132,132,72,136,136,192,192]
def en:List Nat:=[4,8,6,9,64,64,1,2,3,12,2,1,2,1,128,3,12,64,64,128,9,6,4,4,128,8,8,128,64,128]
def nQ:Nat:=fullMask 30
def nR:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x10eb5d,0x10a948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2b958e,0x209584),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f18265,0xe10205),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xe35038a,0x611020a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x32460c30,0x10060030),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3d887000,0x29084000)]
def Ag:List (Nat × Nat × Nat):=[]
def cN:BT Decor:=buildWiresBT 3 nR Ag
def Ah:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(0,2)],[(6,7),(1,3)],[(2,3),(0,1)],[(6,7),(0,2)],[(1,3),(0,2)],[(1,2),(0,3)],[(6,7),(2,3),(0,1)],[(2,3),(1,2),(0,1)],[(6,7),(1,3),(0,2)],[(2,3),(1,3),(0,3)],[(6,7),(1,2),(0,3)],[(6,7),(2,3),(1,2),(0,1)],[(6,7),(2,3),(1,3),(0,3)]]
def eo:BT (List (Nat × Nat)):=btOfList 4 Ah
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ai:goodPairs aK em en:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aj:∀ x ∈ nR, faithful em en x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ak:btAll (fun x => faithful em en x ∧ x.1 < 2^256) cN:=buildWiresBT_faithful Aj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Al:btAll (fun sw => swapsValid sw = true ∧ permWord sw aK = aK) eo:=btAll_ofList (autos_of (by decide +kernel))
def Am:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 64 0,8)]
def nS:BT (Option (Nat × Nat)):=btOfList 3 Am
def An:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 5 (unpackWords 3 [(10,67903552)])
def ep:BT (Option BoundPool):=buildPoolsBT 3 cN aZ nS An
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ao:Slice aZ aK (subcubeFast 64 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=nG) (qGoal:=nH) (by decide +kernel) Ad
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ap:Slice aZ aK (subcubeFast 8 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=nM) (qGoal:=nN) (by decide +kernel) Ae
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aq:Slice aZ aK (subcubeFast 4 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ei) (qGoal:=ej) (by decide +kernel) nK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ar:Slice aZ aK (subcubeFast 2 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=nO) (qGoal:=nP) (by decide +kernel) Af
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma As:Slice aZ aK (subcubeFast 1 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ek) (qGoal:=el) (by decide +kernel) nL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma At:btAll (fun o => ∀ p, o = some p → Slice aZ aK p.1 p.2) nS:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aZ aK p.1 p.2) (forall_cons (someSlice As) (forall_cons (someSlice Ar) (forall_cons (someSlice Aq) (forall_cons (someSlice Ap) (forall_cons (someSlice Ao) (fun _ h => (List.not_mem_nil h).elim))))))
lemma Au:btAll (fun o => ∀ c, o = some c → ValidPool aZ aK c) ep:=buildPoolsBT_sound At
def es:BT (List (List Nat)):=BT.empty
lemma Av:btAll (fun bk => ∀ xs ∈ bk, Impossible aK (9 - 1) xs.toFinset) es:=trivial
def nT:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(14,1256297107502)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aw:checkNodesBT cN aK nQ ep eo es 9 nT = true:=by decide +kernel
def nU:List NodeSpec:=nT
set_option maxRecDepth 20000 in
lemma Ax:checkNodesBT cN aK nQ ep eo es 9 nU = true:=Aw
def Ay:BT (List (List Nat)):=buildBucketsBT cN nU
set_option maxRecDepth 20000 in
lemma Az:btAll (fun bk => ∀ xs ∈ bk, Impossible aK 9 xs.toFinset) Ay:=buildBucketsBT_sound (by decide) Ai Ak Au Al Av Ax
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cO:Lower aZ aK 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Az (by decide +kernel)
def et:List Nat:=varsOf 215
def eu:Nat:=0xfffffffffffffffffffffefefffffefefffffefefffffefefafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nV:Lower et eu 11:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) co
def nW:List Nat:=varsOf 216
def nX:Nat:=0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AA:Lower nW nX 5:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,64,72)]) (by decide +kernel) jE
def nY:List Nat:=varsOf 217
def nZ:Nat:=0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AB:Lower nY nZ 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,4)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def ev:List Nat:=varsOf 218
def ew:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oa:Lower ev ew 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,4),(0,1),(3,4)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def ex:List Nat:=varsOf 219
def ey:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeeeaacc00eeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ob:Lower ex ey 10:=carry_of (swaps:=[(2,4)]) (roots2:=aZ) (T2:=aK) (by decide +kernel) cO
def oc:List Nat:=varsOf 220
def od:Nat:=0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AC:Lower oc od 8:=carry_of (swaps:=[(5,7),(1,7),(6,7),(4,6),(2,4),(0,2)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def ez:List Nat:=varsOf 221
def eA:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oe:Lower ez eA 11:=carry_of (swaps:=[(1,3)]) (roots2:=et) (T2:=eu) (by decide +kernel) nV
def eB:List Nat:=varsOf 222
def eC:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma of:Lower eB eC 10:=carry_of (swaps:=[(2,4),(3,4),(1,2),(0,1)]) (roots2:=aZ) (T2:=aK) (by decide +kernel) cO
def cr:List Nat:=varsOf 215
def ct:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cC:Lower cr ct 7:=lift_of (z:=194) (o:=0) (essPairs:=[(VAR 1,0,2),(VAR 6,0,64),(VAR 7,0,128)]) (by decide +kernel) aI
def aV:List Nat:=varsOf 223
def aq:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefefaeca0fefaeca0
def eD:List Nat:=[5,10,7,11,17,20,5,10,11,13,20,17,66,65,130,129,7,14,66,72,19,26,130,19,22,13,14,68,132,25,26,72,136,136,80,80,144,144,192,192,65,68,73,82,67,129,25,131,132,137,10,65,67,19,17,146]
def eE:List Nat:=[4,8,6,9,16,16,1,2,3,12,4,1,2,1,2,1,3,12,64,64,3,24,128,18,18,9,6,4,4,9,18,8,8,128,16,64,16,128,64,128,64,64,9,18,3,128,24,3,128,9,0,3,1,1,3,18]
def og:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7af5002291ab5d,0x7a94002211a948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xb4980045f7518e,0xc8980045915184),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x102001f030665,0x1c020605),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x64403e62a038a,0x24401a222020a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xe0483c61b00c30,0x80481441a00030),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x181fcc880c3000,0x348000c0000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x83a0f31040c000,0x120a200400000)]
def AD:List (Nat × Nat × Nat):=[(1,0,2),(0,1,3),(1,1,3),(2,1,3),(1,1,5),(2,1,5),(1,1,7),(1,5,13),(3,1,14),(3,4,14),(3,5,14),(1,5,7),(1,6,18),(3,0,19),(1,4,19),(3,0,21),(3,4,21),(1,0,8),(0,1,23),(1,1,23),(2,1,23),(3,1,23),(1,5,8),(1,8,23),(3,8,23),(0,3,30),(3,3,26),(3,6,19)]
def aS:BT Decor:=buildWiresBT 6 og AD
def AE:List (List (Nat × Nat)):=[[],[(6,7)],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(6,7),(2,4)],[(6,7),(1,3)],[(2,4),(1,3)],[(6,7),(0,2)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(1,3),(0,4)],[(6,7),(2,4),(1,3)],[(6,7),(2,4),(0,2)],[(6,7),(1,3),(0,2)],[(2,4),(1,3),(0,2)],[(6,7),(2,4),(0,4)],[(2,4),(1,3),(0,4)],[(6,7),(1,3),(0,4)],[(6,7),(2,4),(1,3),(0,2)],[(6,7),(2,4),(1,3),(0,4)]]
def AF:BT (List (Nat × Nat)):=btOfList 5 AE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bS:goodPairs aq eD eE:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AG:∀ x ∈ og, faithful eD eE x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bT:btAll (fun x => faithful eD eE x ∧ x.1 < 2^256) aS:=buildWiresBT_faithful AG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bU:btAll (fun sw => swapsValid sw = true ∧ permWord sw aq = aq) AF:=btAll_ofList (autos_of (by decide +kernel))
def AH:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,10),some (subcubeFast 2 0,11),some (subcubeFast 4 0,10),some (subcubeFast 5 0,8),some (subcubeFast 8 0,11),some (subcubeFast 16 0,10),some (subcubeFast 21 0,7),some (subcubeFast 64 0,11),some (subcubeFast 65 0,8),some (subcubeFast 85 0,4),some (subcubeFast 128 0,11),some (subcubeFast 129 0,8),some (subcubeFast 149 0,4)]
def AI:BT (Option (Nat × Nat)):=btOfList 6 AH
def bV:Nat → Option PoolSpec:=lookSpec 26 #[(1,0,2),(1,5,13),(3,4,14),(1,1,7),(1,5,7),(1,6,18),(3,0,19),(1,4,19),(3,4,21)] #[0x50214000000c1220285891018200000c0c24406031018083870c041c006020e1828101000000480000014004020e000000a060808080040404000000e000000400000850000041c000000c000010400000010000040400000000000001]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AJ:Slice aV aq (subcubeFast 149 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AK:Slice aV aq (subcubeFast 129 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) dX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AL:Slice aV aq (subcubeFast 128 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=ay) (qGoal:=F) (by decide +kernel) dp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AM:Slice aV aq (subcubeFast 85 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=ec) (qGoal:=ed) (by decide +kernel) nF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AN:Slice aV aq (subcubeFast 65 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ee) (qGoal:=ef) (by decide +kernel) nI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AO:Slice aV aq (subcubeFast 64 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=eg) (qGoal:=eh) (by decide +kernel) nJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AP:Slice aV aq (subcubeFast 21 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=cL) (qGoal:=cM) (by decide +kernel) cB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AQ:Slice aV aq (subcubeFast 16 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aZ) (qGoal:=aK) (by decide +kernel) cO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AR:Slice aV aq (subcubeFast 8 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=et) (qGoal:=eu) (by decide +kernel) nV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AS:Slice aV aq (subcubeFast 5 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ev) (qGoal:=ew) (by decide +kernel) oa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AT:Slice aV aq (subcubeFast 4 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=ex) (qGoal:=ey) (by decide +kernel) ob
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AU:Slice aV aq (subcubeFast 2 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=ez) (qGoal:=eA) (by decide +kernel) oe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AV:Slice aV aq (subcubeFast 1 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=eB) (qGoal:=eC) (by decide +kernel) of
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bW:btAll (fun o => ∀ p, o = some p → Slice aV aq p.1 p.2) AI:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aV aq p.1 p.2) (forall_cons (someSlice AV) (forall_cons (someSlice AU) (forall_cons (someSlice AT) (forall_cons (someSlice AS) (forall_cons (someSlice AR) (forall_cons (someSlice AQ) (forall_cons (someSlice AP) (forall_cons (someSlice AO) (forall_cons (someSlice AN) (forall_cons (someSlice AM) (forall_cons (someSlice AL) (forall_cons (someSlice AK) (forall_cons (someSlice AJ) (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def AW:BT (List (List Nat)):=BT.empty
lemma AX:btAll (fun bk => ∀ xs ∈ bk, Impossible aq (5 - 1) xs.toFinset) AW:=trivial
def oh:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(9,29582557190)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AY:∀ ns ∈ oh, Impossible aq 5 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU AX (by decide +kernel)
def AZ:BT (List (List Nat)):=refBuckets aS [oh] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Ba:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 5 xs.toFinset) AZ:=refBuckets_all (forall_cons AY (fun _ h => (List.not_mem_nil h).elim))
def oi:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0x449001e742892003c1c65649041e43c5168207932944900f),(32,0x58ca592003d532964800f3a9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bb:∀ ns ∈ oi, Impossible aq 6 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Ba (by decide +kernel)
def Bc:BT (List (List Nat)):=refBuckets aS [oi] #[7,0,0,0,0,0,0,1,0,0,0,0,0,0,0,24581,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma oj:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 6 xs.toFinset) Bc:=refBuckets_all (forall_cons Bb (fun _ h => (List.not_mem_nil h).elim))
def ol:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8e98512400a07994490428c8462d1f4512436a190924900f),(56,0xcca512410a23294490028b9c512400a3869449002)]))
def om:List NodeSpec:=readDeltaNodes 2 (unpackWords 5 [(22,0xb10882108000412211042100008)])
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchBd:∀ b ∈ ([ol,om]:List (List NodeSpec)), ∀ ns ∈ b, Impossible aq 7 (nodeValsBT aS ns).toFinset:=blockGroup bV 6 (by decide) bS bT bW bU oj (by decide +kernel)
def Bf:BT (List (List Nat)):=refBuckets aS [ol,om] #[7,9,0,0,0,0,5,0,8,0,0,0,3,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,1,0,0,2,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Bg:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 7 xs.toFinset) Bf:=refBuckets_all batchBd
def oo:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0xa512418cf260573e49248654563c49248054372c49248054),(50,0xd523a492482545b194924900a86220ccbad8c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bh:∀ ns ∈ oo, Impossible aq 8 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Bg (by decide +kernel)
def Bi:BT (List (List Nat)):=refBuckets aS [oo] #[0,1,0,0,0,0,0,0,0,0,3,0,6,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0]
set_option maxRecDepth 20000 in
lemma Bj:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 8 xs.toFinset) Bi:=refBuckets_all (forall_cons Bh (fun _ h => (List.not_mem_nil h).elim))
def oq:List NodeSpec:=readDeltaNodes 5 (varNats 2 (unpackWords 3 [(64,0x99d2492422a1b152492402a1d972492402a0362849248254),(22,0x398f849248254302)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bk:∀ ns ∈ oq, Impossible aq 9 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Bj (by decide +kernel)
def Bl:BT (List (List Nat)):=refBuckets aS [oq] #[0,0,0,0,0,0,0,0,0,0,0,2,4,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Bm:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 9 xs.toFinset) Bl:=refBuckets_all (forall_cons Bk (fun _ h => (List.not_mem_nil h).elim))
def os:List NodeSpec:=readDeltaNodes 2 (unpackWords 4 [(28,0x30cc111111021810471111110218)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bn:∀ ns ∈ os, Impossible aq 10 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Bm (by decide +kernel)
def Bo:BT (List (List Nat)):=refBuckets aS [os] #[2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Bp:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 10 xs.toFinset) Bo:=refBuckets_all (forall_cons Bn (fun _ h => (List.not_mem_nil h).elim))
def ot:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(20,0x21061922a11111110368)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bq:∀ ns ∈ ot, Impossible aq 11 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Bp (by decide +kernel)
def Br:BT (List (List Nat)):=refBuckets aS [ot] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Bs:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 11 xs.toFinset) Br:=refBuckets_all (forall_cons Bq (fun _ h => (List.not_mem_nil h).elim))
def ou:List NodeSpec:=readDeltaNodes 1 (unpackWords 5 [(20,0x18816254c2800210842100ce7)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bt:∀ ns ∈ ou, Impossible aq 12 (nodeValsBT aS ns).toFinset:=blockOk bV 6 (by decide) bS bT bW bU Bs (by decide +kernel)
def Bu:BT (List (List Nat)):=refBuckets aS [ou] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Bv:btAll (fun bk => ∀ xs ∈ bk, Impossible aq 12 xs.toFinset) Bu:=refBuckets_all (forall_cons Bt (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bw:Lower aV aq 13:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Bv (by decide +kernel)
def ov:List Nat:=varsOf 37
def ow:Nat:=0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bx:Lower ov ow 4:=carry_of (swaps:=[(4,5)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def ox:List Nat:=varsOf 39
def oy:Nat:=0xfefefefeececececfefefefeececececfefefefeececececfefefefeecececec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma By:Lower ox oy 5:=carry_of (swaps:=[(5,6),(3,5),(1,3),(4,5),(1,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def eF:List Nat:=varsOf 45
def eG:Nat:=0xfffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oz:Lower eF eG 5:=carry_of (swaps:=[(5,6),(3,5),(4,5),(3,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def eH:List Nat:=varsOf 47
def eI:Nat:=0xfefafefaeca0eca0fefafefaeca0eca0fefafefaeca0eca0fefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oA:Lower eH eI 6:=carry_of (swaps:=[(4,5)]) (roots2:=cH) (T2:=cI) (by decide +kernel) dc
def oB:List Nat:=varsOf 101
def oC:Nat:=0xfafafafafafafafafafafafaa0a0a0a0fafafafafafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bz:Lower oB oC 5:=carry_of (swaps:=[(2,5),(1,5),(0,1),(2,7),(0,6),(4,6),(3,5)]) (roots2:=nW) (T2:=nX) (by decide +kernel) AA
def oD:List Nat:=varsOf 101
def oE:Nat:=0xfffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BA:Lower oD oE 7:=carry_of (swaps:=[(4,5)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def ba:List Nat:=varsOf 103
def aL:Nat:=0xfefefefefefefefefafafafaa0a0a0a0fefefefefefefefefafafafaa0a0a0a0
def eJ:List Nat:=[5,66,7,33,36,5,36,33,66,65,65,7,35,98,68,68,98]
def eK:List Nat:=[4,64,6,32,32,1,4,1,2,1,64,3,3,96,4,64,34]
def oF:Nat:=fullMask 17
def oG:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7853,6816),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x13906,0x11904),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc875,0x4045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x130d8,0x12018),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x1e702,0xa402)]
def BB:List (Nat × Nat × Nat):=[]
def cP:BT Decor:=buildWiresBT 3 oG BB
def BC:List (List (Nat × Nat)):=[[],[(0,2)]]
def eL:BT (List (Nat × Nat)):=btOfList 1 BC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BD:goodPairs aL eJ eK:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BE:∀ x ∈ oG, faithful eJ eK x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BF:btAll (fun x => faithful eJ eK x ∧ x.1 < 2^256) cP:=buildWiresBT_faithful BE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BG:btAll (fun sw => swapsValid sw = true ∧ permWord sw aL = aL) eL:=btAll_ofList (autos_of (by decide +kernel))
def BH:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,7)]
def oH:BT (Option (Nat × Nat)):=btOfList 1 BH
def BI:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def eM:BT (Option BoundPool):=buildPoolsBT 1 cP ba oH BI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BJ:Slice ba aL (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 7:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=oD) (G:=oE) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) BA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BK:btAll (fun o => ∀ p, o = some p → Slice ba aL p.1 p.2) oH:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice ba aL p.1 p.2) (forall_cons (someSlice BJ) (fun _ h => (List.not_mem_nil h).elim))
lemma BL:btAll (fun o => ∀ c, o = some c → ValidPool ba aL c) eM:=buildPoolsBT_sound BK
def eN:BT (List (List Nat)):=BT.empty
lemma BM:btAll (fun bk => ∀ xs ∈ bk, Impossible aL (6 - 1) xs.toFinset) eN:=trivial
def oI:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(9,2396173)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BN:checkNodesBT cP aL oF eM eL eN 6 oI = true:=by decide +kernel
def oJ:List NodeSpec:=oI
set_option maxRecDepth 20000 in
lemma BO:checkNodesBT cP aL oF eM eL eN 6 oJ = true:=BN
def BP:BT (List (List Nat)):=buildBucketsBT cP oJ
set_option maxRecDepth 20000 in
lemma BQ:btAll (fun bk => ∀ xs ∈ bk, Impossible aL 6 xs.toFinset) BP:=buildBucketsBT_sound (by decide) BD BF BL BG BM BO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bX:Lower ba aL 7:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) BQ (by decide +kernel)
def oK:List Nat:=varsOf 75
def oL:Nat:=0xffeeffeeffeeffeeeeaaeeaaeeaaeeaaffeeffeeffeeffeeeeaaeeaaeeaaeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BR:Lower oK oL 5:=carry_of (swaps:=[(3,6),(1,3),(4,6),(1,7),(2,3),(0,1)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def bF:List Nat:=varsOf 99
def aW:Nat:=0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def eO:List Nat:=[33,35,65,33,35,65,66,98]
def eP:List Nat:=[32,34,64,1,3,1,2,34]
def oM:Nat:=fullMask 8
def oN:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,210,210),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,155,131),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,228,4)]
def BS:List (Nat × Nat × Nat):=[]
def cQ:BT Decor:=buildWiresBT 2 oN BS
def BU:List (List (Nat × Nat)):=[[],[(1,5),(0,6)]]
def eQ:BT (List (Nat × Nat)):=btOfList 1 BU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BV:goodPairs aW eO eP:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BW:∀ x ∈ oN, faithful eO eP x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BX:btAll (fun x => faithful eO eP x ∧ x.1 < 2^256) cQ:=buildWiresBT_faithful BW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BY:btAll (fun sw => swapsValid sw = true ∧ permWord sw aW = aW) eQ:=btAll_ofList (autos_of (by decide +kernel))
def BZ:List (Option (Nat × Nat)):=[]
def oO:BT (Option (Nat × Nat)):=btOfList 1 BZ
def Ca:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 0 []
def eR:BT (Option BoundPool):=buildPoolsBT 1 cQ bF oO Ca
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cb:btAll (fun o => ∀ p, o = some p → Slice bF aW p.1 p.2) oO:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice bF aW p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma Cc:btAll (fun o => ∀ c, o = some c → ValidPool bF aW c) eR:=buildPoolsBT_sound Cb
def eS:BT (List (List Nat)):=BT.empty
lemma Cd:btAll (fun bk => ∀ xs ∈ bk, Impossible aW (3 - 1) xs.toFinset) eS:=trivial
def oP:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(7,299012)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ce:checkNodesBT cQ aW oM eR eQ eS 3 oP = true:=by decide +kernel
def oQ:List NodeSpec:=oP
set_option maxRecDepth 20000 in
lemma Cf:checkNodesBT cQ aW oM eR eQ eS 3 oQ = true:=Ce
def Cg:BT (List (List Nat)):=buildBucketsBT cQ oQ
set_option maxRecDepth 20000 in
lemma Ch:btAll (fun bk => ∀ xs ∈ bk, Impossible aW 3 xs.toFinset) Cg:=buildBucketsBT_sound (by decide) BV BX Cc BY Cd Cf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cD:Lower bF aW 4:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,64,66),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) Ch (by decide +kernel)
def eT:List Nat:=varsOf 105
def eU:Nat:=0xffaaffaaffaaffaaaaaaaaaa00000000ffaaffaaffaaffaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oR:Lower eT eU 4:=carry_of (swaps:=[(2,3),(1,3)]) (roots2:=bF) (T2:=aW) (by decide +kernel) cD
def aT:List Nat:=varsOf 107
def aD:Nat:=0xffeeffeeffeeffeeeeaaeeaacc00cc00ffeeffeeffeeffeeeeaaeeaacc00cc00
def eV:List Nat:=[10,33,11,35,10,11,41,65,33,66,65,66,72,35,41,72,98,42,65,66,42]
def eW:List Nat:=[8,32,9,34,2,3,40,64,1,2,1,64,64,3,9,8,34,40,3,0,34]
def cE:Nat:=fullMask 21
def oS:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x465ee,0x46524),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1b2a3d,0x152238),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x12d075,0x2c045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x13614a,0x13004a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xd9e80,6272)]
def Ci:List (Nat × Nat × Nat):=[(1,1,2),(1,1,4),(3,1,4),(3,2,6)]
def bG:BT Decor:=buildWiresBT 4 oS Ci
def Cj:List (List (Nat × Nat)):=[[],[(1,3)]]
def cu:BT (List (Nat × Nat)):=btOfList 1 Cj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eX:goodPairs aD eV eW:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ck:∀ x ∈ oS, faithful eV eW x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eY:btAll (fun x => faithful eV eW x ∧ x.1 < 2^256) bG:=buildWiresBT_faithful Ck
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eZ:btAll (fun sw => swapsValid sw = true ∧ permWord sw aD = aD) cu:=btAll_ofList (autos_of (by decide +kernel))
def Cl:List (Option (Nat × Nat)):=[some (subcubeFast 0 32,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,4),some (subcubeFast 8 0,4),some (subcubeFast 32 0,5)]
def oT:BT (Option (Nat × Nat)):=btOfList 3 Cl
def Cm:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 5 (unpackWords 3 [(10,50856193)])
def cv:BT (Option BoundPool):=buildPoolsBT 3 bG aT oT Cm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cn:Slice aT aD (subcubeFast 32 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dd) (qGoal:=de) (by decide +kernel) dM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Co:Slice aT aD (subcubeFast 8 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=bF) (qGoal:=aW) (by decide +kernel) cD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cp:Slice aT aD (subcubeFast 2 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=eT) (qGoal:=eU) (by decide +kernel) oR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cq:Slice aT aD (subcubeFast 1 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cr:Slice aT aD (subcubeFast 0 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=oK) (qGoal:=oL) (by decide +kernel) BR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cs:btAll (fun o => ∀ p, o = some p → Slice aT aD p.1 p.2) oT:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aT aD p.1 p.2) (forall_cons (someSlice Cr) (forall_cons (someSlice Cq) (forall_cons (someSlice Cp) (forall_cons (someSlice Co) (forall_cons (someSlice Cn) (fun _ h => (List.not_mem_nil h).elim))))))
lemma fa:btAll (fun o => ∀ c, o = some c → ValidPool aT aD c) cv:=buildPoolsBT_sound Cs
def fb:BT (List (List Nat)):=BT.empty
lemma Ct:btAll (fun bk => ∀ xs ∈ bk, Impossible aD (4 - 1) xs.toFinset) fb:=trivial
def oU:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(8,8720389)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cu:checkNodesBT bG aD cE cv cu fb 4 oU = true:=by decide +kernel
def oV:List NodeSpec:=oU
set_option maxRecDepth 20000 in
lemma Cv:checkNodesBT bG aD cE cv cu fb 4 oV = true:=Cu
def fc:BT (List (List Nat)):=buildBucketsBT bG oV
set_option maxRecDepth 20000 in
lemma Cw:btAll (fun bk => ∀ xs ∈ bk, Impossible aD 4 xs.toFinset) fc:=buildBucketsBT_sound (by decide) eX eY fa eZ Ct Cv
def oW:List NodeSpec:=readDeltaNodes 3 (unpackWords 4 [(32,0x22311110026082111101166111110016)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cx:checkNodesBT bG aD cE cv cu fc 5 oW = true:=by decide +kernel
def oX:List NodeSpec:=oW
set_option maxRecDepth 20000 in
lemma Cy:checkNodesBT bG aD cE cv cu fc 5 oX = true:=Cx
def fd:BT (List (List Nat)):=buildBucketsBT bG oX
set_option maxRecDepth 20000 in
lemma Cz:btAll (fun bk => ∀ xs ∈ bk, Impossible aD 5 xs.toFinset) fd:=buildBucketsBT_sound (by decide) eX eY fa eZ Cw Cy
def oY:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(14,595660673189)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CA:checkNodesBT bG aD cE cv cu fd 6 oY = true:=by decide +kernel
def oZ:List NodeSpec:=oY
set_option maxRecDepth 20000 in
lemma CB:checkNodesBT bG aD cE cv cu fd 6 oZ = true:=CA
def CC:BT (List (List Nat)):=buildBucketsBT bG oZ
set_option maxRecDepth 20000 in
lemma CD:btAll (fun bk => ∀ xs ∈ bk, Impossible aD 6 xs.toFinset) CC:=buildBucketsBT_sound (by decide) eX eY fa eZ Cz CB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cf:Lower aT aD 7:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,8,10),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) CD (by decide +kernel)
def pc:List Nat:=varsOf 101
def pd:Nat:=0xfffffffffffffffffafafafaa0a0a0a0fffffffffffffffffafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CE:Lower pc pd 5:=carry_of (swaps:=[(4,5),(6,7)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def ff:List Nat:=varsOf 109
def fg:Nat:=0xfffafffafffafffafafafafaa0a0a0a0fffafffafffafffafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pe:Lower ff fg 7:=carry_of (swaps:=[(1,3)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def fh:List Nat:=varsOf 110
def fi:Nat:=0xfffcfffcfffcfffcfcf0fcf0cc00cc00fffcfffcfffcfffcfcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pf:Lower fh fi 7:=carry_of (swaps:=[(0,2)]) (roots2:=aT) (T2:=aD) (by decide +kernel) cf
def pg:List Nat:=varsOf 79
def pi:Nat:=0xfffefffefffefffefefafefafefafefafffefffefffefffefefafefafefafefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CF:Lower pg pi 6:=carry_of (swaps:=[(1,4),(1,6),(1,3),(2,3),(0,1)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def pj:List Nat:=varsOf 103
def pk:Nat:=0xfffffffffffffffffefefefeececececfffffffffffffffffefefefeecececec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CG:Lower pj pk 6:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def pl:List Nat:=varsOf 109
def pn:Nat:=0xfffffffffffffffffffafffaffa0ffa0fffffffffffffffffffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CH:Lower pl pn 6:=carry_of (swaps:=[(4,5)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def aF:List Nat:=varsOf 111
def aj:Nat:=0xfffefffefffefffefefafefaeca0eca0fffefffefffefffefefafefaeca0eca0
def fj:List Nat:=[5,10,7,11,5,35,36,5,10,11,36,33,66,65,7,72,35,13,14,68,68,14,13,44,41,42,72,98,66,42,67,65,97,36,33,5,73,65,70,66,100,5,65,76,38,104,98]
def fk:List Nat:=[4,8,6,9,6,34,32,1,2,3,4,1,2,1,3,64,3,9,6,4,64,12,12,40,9,34,8,34,64,40,3,64,96,96,96,64,9,3,6,0,96,0,0,12,34,40,96]
def po:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x63dc1436abd,0x3041036a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x50c07a25532e,0x10604a055334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1b4a00fe44d5,0x840006c0415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x281027e6830a,0x281025e2000a),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x71072b810c60,0x71072a800060),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x6df1dc18b000,0x410f90108000)]
def CI:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,0,5),(3,0,5),(1,1,3),(1,1,5),(3,1,5),(1,2,5),(3,2,5),(3,2,6),(1,4,5),(3,4,7),(1,7,8),(3,2,8),(1,5,17),(3,3,11),(1,0,12),(1,2,22),(3,2,22),(1,12,17),(3,0,18),(1,2,26)]
def bo:BT Decor:=buildWiresBT 5 po CI
def CJ:List (List (Nat × Nat)):=[[],[(1,3)],[(0,2)],[(1,3),(0,2)]]
def CK:BT (List (Nat × Nat)):=btOfList 2 CJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cg:goodPairs aj fj fk:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CL:∀ x ∈ po, faithful fj fk x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ch:btAll (fun x => faithful fj fk x ∧ x.1 < 2^256) bo:=buildWiresBT_faithful CL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ci:btAll (fun sw => swapsValid sw = true ∧ permWord sw aj = aj) CK:=btAll_ofList (autos_of (by decide +kernel))
def CM:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,6),some (subcubeFast 0 8,6),some (subcubeFast 0 32,6),some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 2 8,5),some (subcubeFast 4 0,7),some (subcubeFast 5 32,4),some (subcubeFast 8 0,7),some (subcubeFast 10 0,5),some (subcubeFast 32 0,8),some (subcubeFast 37 0,4),some (subcubeFast 64 0,6),some (subcubeFast 64 2,5),some (subcubeFast 64 8,5),some (subcubeFast 66 8,4),some (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff,8)]
def CN:BT (Option (Nat × Nat)):=btOfList 5 CM
def cj:Nat → Option PoolSpec:=lookSpec 66 #[(1,0,1),(3,2,6),(1,0,2),(1,0,5),(1,2,5),(1,1,3),(3,4,7),(1,1,5),(3,3,11),(3,1,5),(3,2,8),(1,4,5),(3,0,5),(1,0,12)] #[0xc1400006030000182000010040000a060000406000000385080c28005080200284000010185000010000000614000000c00000010000002800000020000008000808500040420000040600000060000083000004200000000000000d00000850000001400000080000003,0x100c000060600000080000342800018100000c0400302040018101000b0814002840a00002010000140800008100000404000020500000038000001600007060000381800028280001406000000f001c1840000202800910140048803000040180000c2000000120038304,0xe14140070a08000070280002820000140c0048806]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CO:Slice aF aj (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff) 8:=mappedSlice (f:=identifyRow 0 0 6 5) (R:=aR) (G:=aw) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CP:Slice aF aj (subcubeFast 66 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=ov) (qGoal:=ow) (by decide +kernel) Bx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CQ:Slice aF aj (subcubeFast 64 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=ox) (qGoal:=oy) (by decide +kernel) By
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CR:Slice aF aj (subcubeFast 64 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=eF) (qGoal:=eG) (by decide +kernel) oz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CS:Slice aF aj (subcubeFast 64 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=eH) (qGoal:=eI) (by decide +kernel) oA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CT:Slice aF aj (subcubeFast 37 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CU:Slice aF aj (subcubeFast 32 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aR) (qGoal:=aw) (by decide +kernel) cp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CV:Slice aF aj (subcubeFast 10 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=oB) (qGoal:=oC) (by decide +kernel) Bz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CW:Slice aF aj (subcubeFast 8 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ba) (qGoal:=aL) (by decide +kernel) bX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CX:Slice aF aj (subcubeFast 5 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CY:Slice aF aj (subcubeFast 4 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aT) (qGoal:=aD) (by decide +kernel) cf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CZ:Slice aF aj (subcubeFast 2 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=pc) (qGoal:=pd) (by decide +kernel) CE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Da:Slice aF aj (subcubeFast 2 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ff) (qGoal:=fg) (by decide +kernel) pe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Db:Slice aF aj (subcubeFast 1 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fh) (qGoal:=fi) (by decide +kernel) pf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dc:Slice aF aj (subcubeFast 0 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=pg) (qGoal:=pi) (by decide +kernel) CF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dd:Slice aF aj (subcubeFast 0 8) 6:=slice_fast_direct (zDead:=0) (qRoots:=pj) (qGoal:=pk) (by decide +kernel) CG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma De:Slice aF aj (subcubeFast 0 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=pl) (qGoal:=pn) (by decide +kernel) CH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck:btAll (fun o => ∀ p, o = some p → Slice aF aj p.1 p.2) CN:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aF aj p.1 p.2) (forall_cons (someSlice De) (forall_cons (someSlice Dd) (forall_cons (someSlice Dc) (forall_cons (someSlice Db) (forall_cons (someSlice Da) (forall_cons (someSlice CZ) (forall_cons (someSlice CY) (forall_cons (someSlice CX) (forall_cons (someSlice CW) (forall_cons (someSlice CV) (forall_cons (someSlice CU) (forall_cons (someSlice CT) (forall_cons (someSlice CS) (forall_cons (someSlice CR) (forall_cons (someSlice CQ) (forall_cons (someSlice CP) (forall_cons (someSlice CO) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def Df:BT (List (List Nat)):=BT.empty
lemma Dg:btAll (fun bk => ∀ xs ∈ bk, Impossible aj (5 - 1) xs.toFinset) Df:=trivial
def pp:List NodeSpec:=readDeltaNodes 2 (unpackWords 5 [(18,0x28208420000c460c2100006)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dh:∀ ns ∈ pp, Impossible aj 5 (nodeValsBT bo ns).toFinset:=blockOk cj 7 (by decide) cg ch ck ci Dg (by decide +kernel)
def Di:BT (List (List Nat)):=refBuckets bo [pp] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0]
set_option maxRecDepth 20000 in
lemma pq:btAll (fun bk => ∀ xs ∈ bk, Impossible aj 5 xs.toFinset) Di:=refBuckets_all (forall_cons Dh (fun _ h => (List.not_mem_nil h).elim))
def pr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa892013d7cb944a209ee3abe34a2510cf4a3abe34b28830e),(64,0x24127991f4492413c19b1c7224824f08cb1e45120a3df879),(10,33084369)]))
def pt:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x74d3092413d68be51d249211e7e7d12402723e198924808f),(32,0x339249001ebe333249209ea4)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchDj:∀ b ∈ ([pr,pt]:List (List NodeSpec)), ∀ ns ∈ b, Impossible aj 6 (nodeValsBT bo ns).toFinset:=blockGroup cj 7 (by decide) cg ch ck ci pq (by decide +kernel)
def Dl:BT (List (List Nat)):=refBuckets bo [pr,pt] #[0,1,0,13,0,0,6,0,0,0,0,0,4,0,0,0,0,0,0,57349,0,10,0,0,3,0,0,0,0,0,12,0,0,2,0,0,0,0,0,0,0,0,0,11,0,8,0,0,0,0,0,0,0,0,0,0,0,9,0,0,0,0,7,0]
set_option maxRecDepth 20000 in
lemma fl:btAll (fun bk => ∀ xs ∈ bk, Impossible aj 6 xs.toFinset) Dl:=refBuckets_all batchDj
def pu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xeec59a249209aa07918eaf8a24924d3ce262ca2c4924034f),(64,0x469c825e1d14ebe35124908d501c9732658c449241354091),(64,0x24908e3d04f286ceb45f3a4924238f21e37bb9ce6cce2248),(20,0x41286c8b54e434c)]))
def pw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8be59924909286c8ad5f1c612480cf40cb1d5f1ac92484d4),(64,0x349201a720eaf976492424a233c4f28b75f3c4924138f417),(61,0x1b22b57c6e2492033cd915abe51a2480cf46436456af94)]))
def px:List NodeSpec:=readDeltaNodes 3 (varNats 3 (unpackWords 4 [(59,0x7e1df141ec2d482911111017706c15c2a1828121101564d5e761110026)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchDm:∀ b ∈ ([pu,pw,px]:List (List NodeSpec)), ∀ ns ∈ b, Impossible aj 7 (nodeValsBT bo ns).toFinset:=blockGroup cj 7 (by decide) cg ch ck ci fl (by decide +kernel)
def Dp:BT (List (List Nat)):=refBuckets bo [pu,pw,px] #[10,0,18,0,0,5,9,0,65551,0,0,0,2,12,0,0,0,0,0,0,6,0,0,0,17,0,0,0,0,0,4,0,0,0,0,11,3,0,8,0,14,0,0,1,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,77837,0,0]
set_option maxRecDepth 20000 in
lemma Dq:btAll (fun bk => ∀ xs ∈ bk, Impossible aj 7 xs.toFinset) Dp:=refBuckets_all batchDm
def py:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe7920e322ca53eaca2f912490d43c38aa84e3d42492413cf),(64,0x98cbcdd0efced14309248471e12f15e6e86ea6cca3249209),(64,0x6fcb57b3fd99e1c4924138f07cced2ddca1a4924138f40e),(64,0x86c8ad5f2e89211c7207af17a7e866e67c7d521e4924250f),(12,17407987661)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dr:∀ ns ∈ py, Impossible aj 8 (nodeValsBT bo ns).toFinset:=blockOk cj 7 (by decide) cg ch ck ci Dq (by decide +kernel)
def Ds:BT (List (List Nat)):=refBuckets bo [py] #[0,0,0,0,0,0,0,0,0,0,0,3,0,6,0,0,0,0,0,5,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,7,0,0,0,0,0,0,4,0,1,0,0]
set_option maxRecDepth 20000 in
lemma Dt:btAll (fun bk => ∀ xs ∈ bk, Impossible aj 8 xs.toFinset) Ds:=refBuckets_all (forall_cons Dr (fun _ h => (List.not_mem_nil h).elim))
def pz:List NodeSpec:=readDeltaNodes 1 (unpackWords 5 [(18,0x210810e16f8108421010a6)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Du:∀ ns ∈ pz, Impossible aj 9 (nodeValsBT bo ns).toFinset:=blockOk cj 7 (by decide) cg ch ck ci Dt (by decide +kernel)
def Dv:BT (List (List Nat)):=refBuckets bo [pz] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Dw:btAll (fun bk => ∀ xs ∈ bk, Impossible aj 9 xs.toFinset) Dv:=refBuckets_all (forall_cons Du (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cw:Lower aF aj 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) Dw (by decide +kernel)
def pA:List Nat:=varsOf 229
def pB:Nat:=0xfffffffffffffffffffffffffafafafafffffffffafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dx:Lower pA pB 10:=carry_of (swaps:=[(4,5)]) (roots2:=aJ) (T2:=ad) (by decide +kernel) co
def pC:List Nat:=varsOf 234
def pD:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffccff00ff00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dy:Lower pC pD 8:=carry_of (swaps:=[(3,5),(3,6),(4,7),(2,6),(0,5),(1,5)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dm
def pE:List Nat:=varsOf 234
def pF:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffcccccccccccc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dz:Lower pE pF 8:=carry_of (swaps:=[(5,6),(4,7),(2,6),(0,3),(1,5)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dm
def pG:List Nat:=varsOf 163
def pH:Nat:=0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DA:Lower pG pH 4:=carry_of (swaps:=[(6,7)]) (roots2:=bF) (T2:=aW) (by decide +kernel) cD
def pI:List Nat:=varsOf 169
def pJ:Nat:=0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaa00000000aaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DB:Lower pI pJ 4:=carry_of (swaps:=[(2,3),(6,7),(1,3)]) (roots2:=bF) (T2:=aW) (by decide +kernel) cD
def fm:List Nat:=varsOf 171
def fn:Nat:=0xffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaacc00cc00eeaaeeaacc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pK:Lower fm fn 7:=carry_of (swaps:=[(6,7)]) (roots2:=aT) (T2:=aD) (by decide +kernel) cf
def pL:List Nat:=varsOf 225
def pM:Nat:=0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DC:Lower pL pM 5:=carry_of (swaps:=[(4,7),(3,5),(2,7),(0,6),(1,5)]) (roots2:=bD) (T2:=bE) (by decide +kernel) bH
def pN:List Nat:=varsOf 227
def pO:Nat:=0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DD:Lower pN pO 7:=carry_of (swaps:=[(4,7),(3,7),(2,7),(0,6),(1,5)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def pP:List Nat:=varsOf 200
def pQ:Nat:=0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DE:Lower pP pQ 4:=carry_of (swaps:=[(6,7),(5,6),(1,3),(4,7),(2,6),(0,3)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def pR:List Nat:=varsOf 233
def pS:Nat:=0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DF:Lower pR pS 7:=carry_of (swaps:=[(4,7),(2,7),(0,6),(3,5),(1,5)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def cl:List Nat:=varsOf 203
def cm:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaaeeaaeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cz:Lower cl cm 8:=lift_of (z:=1) (o:=0) (essPairs:=[(VAR 0,0,1)]) (by decide +kernel) cB
def aM:List Nat:=varsOf 235
def ah:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaacc00cc00
def fo:List Nat:=[10,33,11,35,10,11,41,65,33,66,65,130,129,129,66,72,35,42,41,42,72,136,98,162,192,192,130,136,224,67,98,65,65,168,224,73,131,162,129,104,104,129,168,138,66,130,97,137,74]
def fq:List Nat:=[8,32,9,34,2,3,40,64,1,2,1,2,1,128,64,64,3,40,9,34,8,8,34,34,64,128,128,128,160,3,96,9,3,40,96,9,3,160,3,96,40,9,160,2,0,0,96,9,64]
def pT:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc259a00535ee,0x8259a0051524),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1383064cb4a3d,0x85120c90a38),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x18d8a083e8075,0x830a80360045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x45a650cf014a,0x45a650ca004a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x1518df350c680,0x140844100c080),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xae761fa03800,0x4201e002000)]
def DG:List (Nat × Nat × Nat):=[(1,1,2),(1,0,6),(1,1,4),(1,1,5),(1,2,4),(1,2,5),(1,4,5),(1,4,7),(3,0,13),(3,2,13),(3,4,13),(3,5,13),(1,0,8),(3,0,8),(1,2,8),(3,2,8),(1,5,8),(3,5,8),(1,5,10),(1,5,6),(1,8,25),(1,0,22),(3,0,22),(3,6,22),(1,0,23),(1,0,12),(3,0,12),(3,2,12),(0,2,22),(3,2,22),(1,2,23),(3,1,12),(3,5,20),(3,1,26),(1,2,39),(1,2,14),(1,0,15),(3,1,27),(3,2,27),(3,5,27),(1,5,19),(1,5,21),(1,0,37),(3,0,37),(1,1,28),(3,2,50)]
def aN:BT Decor:=buildWiresBT 6 pT DG
def DH:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(6,7),(1,3)]]
def DI:BT (List (Nat × Nat)):=btOfList 2 DH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bc:goodPairs ah fo fq:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DJ:∀ x ∈ pT, faithful fo fq x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bd:btAll (fun x => faithful fo fq x ∧ x.1 < 2^256) aN:=buildWiresBT_faithful DJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma be:btAll (fun sw => swapsValid sw = true ∧ permWord sw ah = ah) DI:=btAll_ofList (autos_of (by decide +kernel))
def DK:List (Option (Nat × Nat)):=[some (subcubeFast 0 32,8),some (subcubeFast 1 32,7),some (subcubeFast 2 0,7),some (subcubeFast 8 0,7),some (subcubeFast 10 0,5),some (subcubeFast 32 0,8),some (subcubeFast 64 0,7),some (subcubeFast 66 0,4),some (subcubeFast 72 0,4),some (subcubeFast 128 0,7),some (subcubeFast 130 0,4),some (subcubeFast 136 0,4),some (0x9999999999999999999999999999999999999999999999999999999999999999,8),some (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55,8)]
def DL:BT (Option (Nat × Nat)):=btOfList 4 DK
def bf:Nat → Option PoolSpec:=lookSpec 71 #[(1,1,2),(1,1,4),(1,2,4),(1,4,5),(1,5,8),(3,6,22),(1,2,8),(3,5,20),(1,1,5),(3,2,8),(3,2,12),(3,0,22),(3,1,12),(3,2,22),(3,5,8),(3,2,50),(3,0,37)] #[0xe0c0000008001c100000e08140000212003050200002010000001c000020c000030200001018304040418202000c10105000808080040400002020a0000003000000480000018000000800001000000082800004040000004000000000000028000003400000180000001,0xf040238282001c141028000141800d080600005021814102800a0800005040a0028201002c20100041004004040a002020100281028014080400000160018205000c1008000002820904001048205002810480000824000120c004820000241028000081400004022038200,0x34240001a0c00684000034202801c14180000806446840520141008000101400008020078205]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DM:Slice aM ah (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55) 8:=mappedSlice (f:=identifyRow 0 0 3 0) (R:=pC) (G:=pD) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Dy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DN:Slice aM ah (0x9999999999999999999999999999999999999999999999999999999999999999) 8:=mappedSlice (f:=identifyRow 0 0 1 0) (R:=pE) (G:=pF) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Dz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DO:Slice aM ah (subcubeFast 136 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=bF) (qGoal:=aW) (by decide +kernel) cD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DP:Slice aM ah (subcubeFast 130 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=eT) (qGoal:=eU) (by decide +kernel) oR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DQ:Slice aM ah (subcubeFast 128 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aT) (qGoal:=aD) (by decide +kernel) cf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DR:Slice aM ah (subcubeFast 72 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=pG) (qGoal:=pH) (by decide +kernel) DA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DS:Slice aM ah (subcubeFast 66 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=pI) (qGoal:=pJ) (by decide +kernel) DB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DT:Slice aM ah (subcubeFast 64 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fm) (qGoal:=fn) (by decide +kernel) pK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DU:Slice aM ah (subcubeFast 32 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ei) (qGoal:=ej) (by decide +kernel) nK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DV:Slice aM ah (subcubeFast 10 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=pL) (qGoal:=pM) (by decide +kernel) DC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DW:Slice aM ah (subcubeFast 8 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=pN) (qGoal:=pO) (by decide +kernel) DD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DX:Slice aM ah (subcubeFast 2 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=pR) (qGoal:=pS) (by decide +kernel) DF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DY:Slice aM ah (subcubeFast 1 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=cL) (qGoal:=cM) (by decide +kernel) cB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DZ:Slice aM ah (subcubeFast 0 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=cl) (qGoal:=cm) (by decide +kernel) cz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bg:btAll (fun o => ∀ p, o = some p → Slice aM ah p.1 p.2) DL:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice aM ah p.1 p.2) (forall_cons (someSlice DZ) (forall_cons (someSlice DY) (forall_cons (someSlice DX) (forall_cons (someSlice DW) (forall_cons (someSlice DV) (forall_cons (someSlice DU) (forall_cons (someSlice DT) (forall_cons (someSlice DS) (forall_cons (someSlice DR) (forall_cons (someSlice DQ) (forall_cons (someSlice DP) (forall_cons (someSlice DO) (forall_cons (someSlice DN) (forall_cons (someSlice DM) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def Ea:BT (List (List Nat)):=BT.empty
lemma ft:btAll (fun bk => ∀ xs ∈ bk, Impossible ah (5 - 1) xs.toFinset) Ea:=trivial
def pU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x39d30a60038e8e1853009cfa69800e562293009ce924800e),(39,0xa624a001c6c74c34a009cbc2d3601)]))
def pV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38dc7338a009cab38a001cf934a001c4935800e57928800e),(35,0xcfa4b001c7426940038f671400)]))
def pW:List NodeSpec:=readDeltaNodes 1 (unpackWords 7 [(10,0x3f2e02041010000086)])
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchEb:∀ b ∈ ([pU,pV,pW]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ah 5 (nodeValsBT aN ns).toFinset:=blockGroup bf 7 (by decide) bc bd bg be ft (by decide +kernel)
def Ee:BT (List (List Nat)):=refBuckets aN [pU,pV,pW] #[0,0,0,0,8,0,6,0,14,0,9,0,0,0,0,0,0,10,0,0,7,0,0,0,13,2,0,0,0,0,11,0,12,0,1,0,0,0,15,0,0,17,0,0,0,0,0,0,5,0,0,0,16,0,3,0,0,4,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma cA:btAll (fun bk => ∀ xs ∈ bk, Impossible ah 5 xs.toFinset) Ee:=refBuckets_all batchEb
def pX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x88cc914c230e07e28928127a3972492023c3c8e5092482cf),(64,0x90925044f06c32b24a049e8188a2820792178d125864f413),(6,33697)]))
def pY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc742492033d0369249081e89b943d12422783a194925024f),(64,0x461b892482cf58924800f7e294924804f472a4924047ad11),(2,2)]))
def pZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6e54c24a049e8e5a9249011e62b0924804f472d0924808f),(64,0xe6f32e64d28234e066ce18494093c12d14083c2c6125020f),(8,2177933)]))
def qa:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x395a4924047b0bc2cd24844f0e9a892083d03a386a24844f),(64,0x3cf449049e0e90e3d124127a5b1249041e0cd953d124127a),(4,110)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchEf:∀ b ∈ ([pX,pY,pZ,qa]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ah 6 (nodeValsBT aN ns).toFinset:=blockGroup bf 7 (by decide) bc bd bg be cA (by decide +kernel)
def qb:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24808f3a53b6379249011e0e98ead1241279b0ea6345004f),(64,0x2003d1f31f894404720e194944207851f32925024f472909),(7,516681)]))
def qc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7a38ea49240479dd928800f50fac9280279d1d32928804f),(58,0x1d62f4924824f571249001e8e8652492093cfe49240)]))
def qd:List NodeSpec:=readDeltaNodes 4 (varNats 3 (unpackWords 4 [(59,0x4b111110107265b1111100272821ea2f7112100371ef2885c111110027)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchEj:∀ b ∈ ([qb,qc,qd]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ah 6 (nodeValsBT aN ns).toFinset:=blockGroup bf 7 (by decide) bc bd bg be cA (by decide +kernel)
def Em:BT (List (List Nat)):=refBuckets aN [pX,pY,pZ,qa,qb,qc,qd] #[0,33,6,0,47,0,0,2,18,0,1,51,0,587292675,188458,0,0,0,15,0,196625,32,24,0,0,0,0,176132,5,16,21,0,28,0,0,0,9,126986,155674,0,0,184359,7,0,37,486596616,20,25,0,0,0,34,19,36,872509451,0,0,41,122893,200748,204827,0,163852,0]
set_option maxRecDepth 20000 in
lemma fu:btAll (fun bk => ∀ xs ∈ bk, Impossible ah 6 xs.toFinset) Em:=refBuckets_all (allCat batchEf batchEj)
def qe:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3b9d0cc7124920c3940644f9d0cc89250269e4388924844f),(64,0xe1fce9249049e884e1b8d8e756295d8f92490d43c920e872),(64,0xd92b9344908f3c8711b94cfd465c59250479e1fcf1249049),(14,1116213823466)]))
def qf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5e2f0c84924134f70ec6671924901a8490b65e3649241894),(64,0xe75865249211e7a0e63a197af8ea6686344908e3c19a3bdd),(64,0x9b2f0cc4924130f0b5562f1e6492416a107c56193ad1c866),(29,0x207ec762492113c1d21be9)]))
def qg:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(64,0x84924338f06630c46e562f163c924827a881fb1dc924844f),(53,0x107ce91ba2f8ea7924908d50a0a5e8ec6f354f14)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchEn:∀ b ∈ ([qe,qf,qg]:List (List NodeSpec)), ∀ ns ∈ b, Impossible ah 7 (nodeValsBT aN ns).toFinset:=blockGroup bf 7 (by decide) bc bd bg be fu (by decide +kernel)
def Eq:BT (List (List Nat)):=refBuckets aN [qe,qf,qg] #[14,0,0,0,0,15,0,0,20,3,0,0,0,0,13,2,0,8,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,6,12,10,0,0,0,0,0,0,0,7,0,0,17,0,0,20484,0,1,19,0,0,0,0,11,0,0,0,0,16]
set_option maxRecDepth 20000 in
lemma Er:btAll (fun bk => ∀ xs ∈ bk, Impossible ah 7 xs.toFinset) Eq:=refBuckets_all batchEn
def qh:List NodeSpec:=readDeltaNodes 3 (varNats 2 (unpackWords 3 [(64,0x877531f155abf9924904f3c9215eac3b9f8d33124920c38f),(39,0x49069b61d11d69fb1e49241871e0d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Es:∀ ns ∈ qh, Impossible ah 8 (nodeValsBT aN ns).toFinset:=blockOk bf 7 (by decide) bc bd bg be Er (by decide +kernel)
def Et:BT (List (List Nat)):=refBuckets aN [qh] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Eu:btAll (fun bk => ∀ xs ∈ bk, Impossible ah 8 xs.toFinset) Et:=refBuckets_all (forall_cons Es (fun _ h => (List.not_mem_nil h).elim))
def qi:List NodeSpec:=readDeltaNodes 1 (unpackWords 5 [(19,0x421044425280108421010c6)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ev:∀ ns ∈ qi, Impossible ah 9 (nodeValsBT aN ns).toFinset:=blockOk bf 7 (by decide) bc bd bg be Eu (by decide +kernel)
def Ew:BT (List (List Nat)):=refBuckets aN [qi] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0]
set_option maxRecDepth 20000 in
lemma Ex:btAll (fun bk => ∀ xs ∈ bk, Impossible ah 9 xs.toFinset) Ew:=refBuckets_all (forall_cons Ev (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dq:Lower aM ah 10:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,8,10),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Ex (by decide +kernel)
def qj:List Nat:=varsOf 253
def qk:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ey:Lower qj qk 12:=lift_of (z:=40) (o:=0) (essPairs:=[(VAR 3,16,24),(VAR 5,1,33)]) (by decide +kernel) co
def fv:List Nat:=varsOf 49
def fw:Nat:=0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ql:Lower fv fw 4:=carry_of (swaps:=[(3,5),(4,5),(2,4)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def fx:List Nat:=varsOf 52
def fy:Nat:=0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma qm:Lower fx fy 4:=carry_of (swaps:=[(3,5),(1,5),(4,5),(2,4),(0,2)]) (roots2:=aG) (T2:=aC) (by decide +kernel) aI
def fz:List Nat:=varsOf 53
def fA:Nat:=0xfffffafafafaa0a0fffffafafafaa0a0fffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dr:Lower fz fA 7:=carry_of (swaps:=[(5,6)]) (roots2:=aP) (T2:=az) (by decide +kernel) bA
def qn:List Nat:=varsOf 51
def qo:Nat:=0xffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeecccc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ez:Lower qn qo 5:=carry_of (swaps:=[(5,6),(1,5),(4,5),(1,7),(2,4)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def qp:List Nat:=varsOf 57
def qq:Nat:=0xffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EA:Lower qp qq 5:=carry_of (swaps:=[(5,6),(3,5),(4,5),(3,7),(2,4)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def qr:List Nat:=varsOf 59
def qs:Nat:=0xffffeeaaeeaacc00ffffeeaaeeaacc00ffffeeaaeeaacc00ffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EB:Lower qr qs 6:=carry_of (swaps:=[(4,5),(2,4)]) (roots2:=cH) (T2:=cI) (by decide +kernel) dc
def qt:List Nat:=varsOf 54
def qu:Nat:=0xfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfccccc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EC:Lower qt qu 5:=carry_of (swaps:=[(5,6),(1,5),(4,5),(1,7),(2,4),(0,2)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def qv:List Nat:=varsOf 60
def qw:Nat:=0xfffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ED:Lower qv qw 5:=carry_of (swaps:=[(5,6),(3,5),(1,5),(4,5),(3,7),(2,4),(0,2)]) (roots2:=bh) (T2:=bl) (by decide +kernel) bq
def qx:List Nat:=varsOf 62
def qy:Nat:=0xfffffcf0fcf0cc00fffffcf0fcf0cc00fffffcf0fcf0cc00fffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EE:Lower qx qy 6:=carry_of (swaps:=[(4,5),(2,4),(0,2)]) (roots2:=cH) (T2:=cI) (by decide +kernel) dc
def qz:List Nat:=varsOf 55
def qA:Nat:=0xfffffefefefeececfffffefefefeececfffffefefefeececfffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EF:Lower qz qA 8:=carry_of (swaps:=[(5,7),(4,6),(2,3),(0,1)]) (roots2:=cl) (T2:=cm) (by decide +kernel) cz
def qB:List Nat:=varsOf 61
def qC:Nat:=0xfffffffafffaffa0fffffffafffaffa0fffffffafffaffa0fffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EG:Lower qB qC 8:=carry_of (swaps:=[(5,7),(4,6),(2,3),(1,3),(0,3)]) (roots2:=cl) (T2:=cm) (by decide +kernel) cz
def qD:List Nat:=varsOf 63
def qE:Nat:=0xfffffefafefaeca0fffffefafefaeca0fffffefafefaeca0fffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EH:Lower qD qE 9:=lift_of (z:=2) (o:=8) (essPairs:=[(VAR 1,8,10),(VAR 3,2,10)]) (by decide +kernel) dr
def qF:List Nat:=varsOf 117
def qG:Nat:=0xfffffafafffffafafffffafafafaa0a0fffffafafffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EI:Lower qF qG 8:=lift_of (z:=32) (o:=0) (essPairs:=[(VAR 5,1,33)]) (by decide +kernel) bA
def qH:List Nat:=varsOf 117
def qI:Nat:=0xfffffffffffffafafffffafafafaa0a0fffffffffffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EJ:Lower qH qI 10:=carry_of (swaps:=[(5,7),(5,6)]) (roots2:=aJ) (T2:=ad) (by decide +kernel) co
def bM:List Nat:=varsOf 119
def aX:Nat:=0xfffffefefffffefefffffafafafaa0a0fffffefefffffefefffffafafafaa0a0
def fB:List Nat:=[5,66,7,17,20,5,20,17,36,33,33,66,65,65,7,19,35,98,36,68,68,48,48,80,80,98]
def fC:List Nat:=[4,64,6,16,16,1,4,1,4,1,32,2,1,64,3,3,3,96,32,4,64,16,32,16,64,34]
def qJ:Nat:=fullMask 26
def qK:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1f6ad,0x1d2a0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x203c806,0x201c804),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1c4175,0x80145),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x1e080d8,0xa00018),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x2670700,0x2460400),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x39a3802,0x1122002)]
def EK:List (Nat × Nat × Nat):=[]
def cR:BT Decor:=buildWiresBT 3 qK EK
def EL:List (List (Nat × Nat)):=[[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def fD:BT (List (Nat × Nat)):=btOfList 3 EL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EM:goodPairs aX fB fC:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EN:∀ x ∈ qK, faithful fB fC x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EO:btAll (fun x => faithful fB fC x ∧ x.1 < 2^256) cR:=buildWiresBT_faithful EN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EP:btAll (fun sw => swapsValid sw = true ∧ permWord sw aX = aX) fD:=btAll_ofList (autos_of (by decide +kernel))
def EQ:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,10)]
def qM:BT (Option (Nat × Nat)):=btOfList 1 EQ
def ER:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def fE:BT (Option BoundPool):=buildPoolsBT 1 cR bM qM ER
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ES:Slice bM aX (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 10:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=qH) (G:=qI) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) EJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ET:btAll (fun o => ∀ p, o = some p → Slice bM aX p.1 p.2) qM:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice bM aX p.1 p.2) (forall_cons (someSlice ES) (fun _ h => (List.not_mem_nil h).elim))
lemma EU:btAll (fun o => ∀ c, o = some c → ValidPool bM aX c) fE:=buildPoolsBT_sound ET
def fF:BT (List (List Nat)):=BT.empty
lemma EV:btAll (fun bk => ∀ xs ∈ bk, Impossible aX (9 - 1) xs.toFinset) fF:=trivial
def qN:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(10,19173390)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EW:checkNodesBT cR aX qJ fE fD fF 9 qN = true:=by decide +kernel
def qO:List NodeSpec:=qN
set_option maxRecDepth 20000 in
lemma EX:checkNodesBT cR aX qJ fE fD fF 9 qO = true:=EW
def EY:BT (List (List Nat)):=buildBucketsBT cR qO
set_option maxRecDepth 20000 in
lemma EZ:btAll (fun bk => ∀ xs ∈ bk, Impossible aX 9 xs.toFinset) EY:=buildBucketsBT_sound (by decide) EM EO EU EP EV EX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ds:Lower bM aX 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) EZ (by decide +kernel)
def qP:List Nat:=varsOf 122
def qQ:Nat:=0xffffffccffffffccffffcc00cc00cc00ffffffccffffffccffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fa:Lower qP qQ 7:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=aT) (T2:=aD) (by decide +kernel) cf
def qR:List Nat:=varsOf 121
def qS:Nat:=0xffffffffffffffffffffffaaffaaff00ffffffffffffffffffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fb:Lower qR qS 6:=carry_of (swaps:=[(4,5),(2,4)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def qT:List Nat:=varsOf 123
def qU:Nat:=0xffffffeeffffffeeffffeeaaeeaacc00ffffffeeffffffeeffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fc:Lower qT qU 10:=carry_of (swaps:=[(2,4)]) (roots2:=aF) (T2:=aj) (by decide +kernel) cw
def qV:List Nat:=varsOf 125
def qW:Nat:=0xfffffffafffffffafffffafafafaa0a0fffffffafffffffafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fd:Lower qV qW 10:=carry_of (swaps:=[(1,3)]) (roots2:=bM) (T2:=aX) (by decide +kernel) ds
def qX:List Nat:=varsOf 124
def qY:Nat:=0xfffffffffffffffffffffff0fff0ff00fffffffffffffffffffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fe:Lower qX qY 6:=carry_of (swaps:=[(1,5),(4,5),(2,4),(0,2)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def qZ:List Nat:=varsOf 126
def ra:Nat:=0xfffffffcfffffffcfffffcf0fcf0cc00fffffffcfffffffcfffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ff:Lower qZ ra 10:=carry_of (swaps:=[(2,4),(0,2)]) (roots2:=aF) (T2:=aj) (by decide +kernel) cw
def rb:List Nat:=varsOf 95
def rc:Nat:=0xfffffffefffffffefffffefafffffefafffffffefffffffefffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fg:Lower rb rc 7:=carry_of (swaps:=[(3,5),(3,4),(4,7),(3,6),(2,3),(0,1)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def bY:List Nat:=varsOf 119
def bZ:Nat:=0xfffffffffffffffffffffefefefeececfffffffffffffffffffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cn:Lower bY bZ 9:=lift_of (z:=66) (o:=0) (essPairs:=[(VAR 1,0,2),(VAR 6,0,64)]) (by decide +kernel) dr
def rd:List Nat:=varsOf 125
def re:Nat:=0xfffffffffffffffffffffffafffaffa0fffffffffffffffffffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fh:Lower rd re 9:=carry_of (swaps:=[(1,3)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def fG:List Nat:=varsOf 127
def fH:Nat:=0xfffffffefffffffefffffefafefaeca0fffffffefffffffefffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rf:Lower fG fH 12:=lift_of (z:=32) (o:=0) (essPairs:=[(VAR 5,1,33)]) (by decide +kernel) dp
def rg:List Nat:=varsOf 173
def rh:Nat:=0xfffafffafffafffafffafffafffafffafafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fi:Lower rg rh 7:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def ri:List Nat:=varsOf 174
def rj:Nat:=0xfffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0cc00cc00fcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fj:Lower ri rj 7:=carry_of (swaps:=[(6,7),(0,2)]) (roots2:=aT) (T2:=aD) (by decide +kernel) cf
def fI:List Nat:=varsOf 175
def fJ:Nat:=0xfffefffefffefffefffefffefffefffefefafefaeca0eca0fefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rk:Lower fI fJ 10:=carry_of (swaps:=[(6,7)]) (roots2:=aF) (T2:=aj) (by decide +kernel) cw
def rl:List Nat:=varsOf 183
def rm:Nat:=0xfffffefefffffefefffffefefffffefefffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fk:Lower rl rm 10:=carry_of (swaps:=[(6,7)]) (roots2:=bM) (T2:=aX) (by decide +kernel) ds
def ro:List Nat:=varsOf 184
def rp:Nat:=0xffffff00ffffff00ffffff00ffffff00ffff000000000000ffff000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fl:Lower ro rp 4:=carry_of (swaps:=[(2,4),(6,7),(0,4),(1,3)]) (roots2:=bF) (T2:=aW) (by decide +kernel) cD
def rr:List Nat:=varsOf 185
def rt:Nat:=0xffffffaaffffffaaffffffaaffffffaaffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fm:Lower rr rt 7:=carry_of (swaps:=[(2,4),(6,7),(1,3)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def ru:List Nat:=varsOf 186
def rv:Nat:=0xffffffccffffffccffffffccffffffccffffcc00cc00cc00ffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fn:Lower ru rv 7:=carry_of (swaps:=[(2,4),(6,7),(0,4)]) (roots2:=aT) (T2:=aD) (by decide +kernel) cf
def rx:List Nat:=varsOf 187
def ry:Nat:=0xffffffeeffffffeeffffffeeffffffeeffffeeaaeeaacc00ffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fo:Lower rx ry 10:=carry_of (swaps:=[(6,7),(2,4)]) (roots2:=aF) (T2:=aj) (by decide +kernel) cw
def rz:List Nat:=varsOf 188
def rA:Nat:=0xfffffff0fffffff0fffffff0fffffff0fffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fp:Lower rz rA 7:=carry_of (swaps:=[(3,4),(2,4),(0,2),(6,7),(1,3)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def rB:List Nat:=varsOf 181
def rC:Nat:=0xfffffffffffffffffffffffffffffffffffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fq:Lower rB rC 8:=carry_of (swaps:=[(4,5),(2,5),(5,7),(4,6),(2,3),(1,7),(0,7)]) (roots2:=cl) (T2:=cm) (by decide +kernel) cz
def rD:List Nat:=varsOf 189
def rE:Nat:=0xfffffffafffffffafffffffafffffffafffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fr:Lower rD rE 10:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=bM) (T2:=aX) (by decide +kernel) ds
def rF:List Nat:=varsOf 188
def rG:Nat:=0xfffffffffffffffffffffffffffffffffffffff0fff0ff00fffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fs:Lower rF rG 6:=carry_of (swaps:=[(1,5),(4,5),(6,7),(2,4),(0,2)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def rH:List Nat:=varsOf 190
def rI:Nat:=0xfffffffcfffffffcfffffffcfffffffcfffffcf0fcf0cc00fffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ft:Lower rH rI 10:=carry_of (swaps:=[(6,7),(2,4),(0,2)]) (roots2:=aF) (T2:=aj) (by decide +kernel) cw
def rJ:List Nat:=varsOf 159
def rK:Nat:=0xfffffffefffffffefffffffefffffffefffffefafffffefafffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fu:Lower rJ rK 7:=carry_of (swaps:=[(3,5),(4,7),(3,6),(2,3),(0,1)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def rL:List Nat:=varsOf 183
def rM:Nat:=0xfffffffffffffffffffffffffffffffffffffefefefeececfffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fv:Lower rL rM 9:=carry_of (swaps:=[(6,7)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def rN:List Nat:=varsOf 189
def rO:Nat:=0xfffffffffffffffffffffffffffffffffffffffafffaffa0fffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fw:Lower rN rO 9:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def rP:List Nat:=varsOf 191
def rQ:Nat:=0xfffffffefffffffefffffffefffffffefffffefafefaeca0fffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fx:Lower rP rQ 12:=carry_of (swaps:=[(6,7)]) (roots2:=fG) (T2:=fH) (by decide +kernel) rf
def rR:List Nat:=varsOf 229
def rS:Nat:=0xfffffffffffffffffafafafafafafafafafafafafafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fy:Lower rR rS 8:=carry_of (swaps:=[(6,7),(4,6),(2,7),(0,6),(3,5)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def bC:List Nat:=varsOf 231
def aU:Nat:=0xfffffffffffffffffefefefefefefefefefefefefefefefefafafafaa0a0a0a0
def fK:List Nat:=[5,66,7,33,36,5,36,33,66,65,65,130,129,129,7,35,98,130,68,68,132,132,98,162,192,192]
def fL:List Nat:=[4,64,6,32,32,1,4,1,2,1,64,2,1,128,3,3,96,128,4,64,4,128,34,34,64,128]
def rT:Nat:=fullMask 26
def rU:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf6ad,0xd2a0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xc3c906,0xc0c904),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c4075,0x140045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc180d8,0xc10018),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x34d0702,0x1090402),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3b23800,0x2222000)]
def Fz:List (Nat × Nat × Nat):=[]
def cS:BT Decor:=buildWiresBT 3 rU Fz
def FA:List (List (Nat × Nat)):=[[],[(6,7)],[(0,2)],[(6,7),(0,2)],[(2,7),(1,5),(0,6)],[(2,6),(1,5),(0,7)],[(6,7),(2,7),(1,5),(0,6)],[(6,7),(2,6),(1,5),(0,7)]]
def fM:BT (List (Nat × Nat)):=btOfList 3 FA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FB:goodPairs aU fK fL:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FC:∀ x ∈ rU, faithful fK fL x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FD:btAll (fun x => faithful fK fL x ∧ x.1 < 2^256) cS:=buildWiresBT_faithful FC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FE:btAll (fun sw => swapsValid sw = true ∧ permWord sw aU = aU) fM:=btAll_ofList (autos_of (by decide +kernel))
def FF:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,10)]
def rV:BT (Option (Nat × Nat)):=btOfList 1 FF
def FG:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def fN:BT (Option BoundPool):=buildPoolsBT 1 cS bC rV FG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FH:Slice bC aU (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 10:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=pA) (G:=pB) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Dx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FI:btAll (fun o => ∀ p, o = some p → Slice bC aU p.1 p.2) rV:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice bC aU p.1 p.2) (forall_cons (someSlice FH) (fun _ h => (List.not_mem_nil h).elim))
lemma FJ:btAll (fun o => ∀ c, o = some c → ValidPool bC aU c) fN:=buildPoolsBT_sound FI
def fO:BT (List (List Nat)):=BT.empty
lemma FK:btAll (fun bk => ∀ xs ∈ bk, Impossible aU (9 - 1) xs.toFinset) fO:=trivial
def rW:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(10,19173390)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FL:checkNodesBT cS aU rT fN fM fO 9 rW = true:=by decide +kernel
def rX:List NodeSpec:=rW
set_option maxRecDepth 20000 in
lemma FM:checkNodesBT cS aU rT fN fM fO 9 rX = true:=FL
def FN:BT (List (List Nat)):=buildBucketsBT cS rX
set_option maxRecDepth 20000 in
lemma FO:btAll (fun bk => ∀ xs ∈ bk, Impossible aU 9 xs.toFinset) FN:=buildBucketsBT_sound (by decide) FB FD FJ FE FK FM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cF:Lower bC aU 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) FO (by decide +kernel)
def rY:List Nat:=varsOf 236
def rZ:Nat:=0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FP:Lower rY rZ 7:=carry_of (swaps:=[(4,7),(3,7),(2,7),(0,2),(2,6),(3,5),(1,5)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def fP:List Nat:=varsOf 237
def fQ:Nat:=0xfffffffffffffffffffafffafffafffafffafffafffafffafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sb:Lower fP fQ 10:=carry_of (swaps:=[(1,3)]) (roots2:=bC) (T2:=aU) (by decide +kernel) cF
def sd:List Nat:=varsOf 206
def se:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0fcf0fcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FQ:Lower sd se 8:=carry_of (swaps:=[(0,2)]) (roots2:=cl) (T2:=cm) (by decide +kernel) cz
def fR:List Nat:=varsOf 238
def fS:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sf:Lower fR fS 10:=carry_of (swaps:=[(0,2)]) (roots2:=aM) (T2:=ah) (by decide +kernel) dq
def sg:List Nat:=varsOf 207
def si:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffefefafefafefafefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FR:Lower sg si 9:=carry_of (swaps:=[(5,7),(3,4),(2,3),(2,6),(0,1)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def sj:List Nat:=varsOf 237
def sk:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FT:Lower sj sk 7:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def bp:List Nat:=varsOf 239
def aO:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffefefafefaeca0eca0
def fT:List Nat:=[5,10,7,11,33,36,5,10,11,13,36,33,66,65,65,130,129,129,7,14,66,72,35,42,130,13,14,68,68,132,132,41,42,72,136,136,98,162,192,192]
def fU:List Nat:=[4,8,6,9,32,32,1,2,3,12,4,1,2,1,64,2,1,128,3,12,64,64,3,40,128,9,6,4,64,4,128,9,34,8,8,128,34,34,64,128]
def sm:Nat:=fullMask 40
def sn:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x82476b5d,0x82452948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x3105dc918e,0x3104449184),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7e0c0665,0x2c080605),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xf86a8038a,0x68288020a),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3180c00c30,0x3100800030),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xd218307000,0x4010304000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xec61038000,0x8841020000)]
def FU:List (Nat × Nat × Nat):=[]
def cT:BT Decor:=buildWiresBT 3 sn FU
def FV:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(0,2)],[(6,7),(1,3)],[(6,7),(0,2)],[(1,3),(0,2)],[(6,7),(1,3),(0,2)]]
def fV:BT (List (Nat × Nat)):=btOfList 3 FV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FW:goodPairs aO fT fU:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FX:∀ x ∈ sn, faithful fT fU x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FY:btAll (fun x => faithful fT fU x ∧ x.1 < 2^256) cT:=buildWiresBT_faithful FX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FZ:btAll (fun sw => swapsValid sw = true ∧ permWord sw aO = aO) fV:=btAll_ofList (autos_of (by decide +kernel))
def Ga:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,10),some (subcubeFast 2 0,10),some (subcubeFast 4 0,10),some (subcubeFast 32 0,10),some (subcubeFast 64 0,10),some (subcubeFast 128 0,10)]
def so:BT (Option (Nat × Nat)):=btOfList 4 Ga
def Gb:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 6 (unpackWords 3 [(12,5436612672)])
def fW:BT (Option BoundPool):=buildPoolsBT 4 cT bp so Gb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gc:Slice bp aO (subcubeFast 128 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aF) (qGoal:=aj) (by decide +kernel) cw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gd:Slice bp aO (subcubeFast 64 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fI) (qGoal:=fJ) (by decide +kernel) rk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ge:Slice bp aO (subcubeFast 32 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aZ) (qGoal:=aK) (by decide +kernel) cO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gf:Slice bp aO (subcubeFast 4 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aM) (qGoal:=ah) (by decide +kernel) dq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gg:Slice bp aO (subcubeFast 2 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fP) (qGoal:=fQ) (by decide +kernel) sb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gh:Slice bp aO (subcubeFast 1 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fR) (qGoal:=fS) (by decide +kernel) sf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gi:btAll (fun o => ∀ p, o = some p → Slice bp aO p.1 p.2) so:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice bp aO p.1 p.2) (forall_cons (someSlice Gh) (forall_cons (someSlice Gg) (forall_cons (someSlice Gf) (forall_cons (someSlice Ge) (forall_cons (someSlice Gd) (forall_cons (someSlice Gc) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma Gj:btAll (fun o => ∀ c, o = some c → ValidPool bp aO c) fW:=buildPoolsBT_sound Gi
def fX:BT (List (List Nat)):=BT.empty
lemma Gk:btAll (fun bk => ∀ xs ∈ bk, Impossible aO (11 - 1) xs.toFinset) fX:=trivial
def sp:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(16,0x2292261111110067)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gl:checkNodesBT cT aO sm fW fV fX 11 sp = true:=by decide +kernel
def sr:List NodeSpec:=sp
set_option maxRecDepth 20000 in
lemma Gm:checkNodesBT cT aO sm fW fV fX 11 sr = true:=Gl
def Gn:BT (List (List Nat)):=buildBucketsBT cT sr
set_option maxRecDepth 20000 in
lemma Go:btAll (fun bk => ∀ xs ∈ bk, Impossible aO 11 xs.toFinset) Gn:=buildBucketsBT_sound (by decide) FW FY Gj FZ Gk Gm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fY:Lower bp aO 12:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Go (by decide +kernel)
def st:List Nat:=varsOf 243
def su:Nat:=0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gp:Lower st su 10:=carry_of (swaps:=[(3,4),(2,4)]) (roots2:=bC) (T2:=aU) (by decide +kernel) cF
def sv:List Nat:=varsOf 244
def sx:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gq:Lower sv sx 8:=carry_of (swaps:=[(5,7),(1,7),(6,7),(4,7),(2,7),(0,6),(3,5)]) (roots2:=bt) (T2:=bu) (by decide +kernel) bB
def sy:List Nat:=varsOf 245
def sz:Nat:=0xfffffffffffffffffffffafafffffafafffffafafffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gr:Lower sy sz 11:=carry_of (swaps:=[(6,7),(4,6),(2,7),(0,6),(3,5)]) (roots2:=kH) (T2:=kI) (by decide +kernel) wz
def sA:List Nat:=varsOf 244
def sB:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gs:Lower sA sB 6:=carry_of (swaps:=[(1,5),(4,5),(6,7),(3,6),(2,4),(0,2)]) (roots2:=bK) (T2:=bL) (by decide +kernel) bR
def sC:List Nat:=varsOf 246
def sD:Nat:=0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gt:Lower sC sD 10:=carry_of (swaps:=[(3,4),(2,4),(0,2)]) (roots2:=bC) (T2:=aU) (by decide +kernel) cF
def fZ:List Nat:=varsOf 245
def ga:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sE:Lower fZ ga 9:=carry_of (swaps:=[(3,7),(6,7),(1,6)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def gb:List Nat:=varsOf 247
def gd:Nat:=0xfffffffffffffffffffffefefffffefefffffefefffffefefffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sF:Lower gb gd 12:=lift_of (z:=34) (o:=0) (essPairs:=[(VAR 1,64,66),(VAR 5,1,33)]) (by decide +kernel) co
def sG:List Nat:=varsOf 248
def sH:Nat:=0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ffff000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gu:Lower sG sH 7:=carry_of (swaps:=[(3,4),(2,7),(0,4),(4,6),(3,5),(1,5)]) (roots2:=ba) (T2:=aL) (by decide +kernel) bX
def sI:List Nat:=varsOf 249
def sJ:Nat:=0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gv:Lower sI sJ 10:=carry_of (swaps:=[(2,4),(1,3)]) (roots2:=bC) (T2:=aU) (by decide +kernel) cF
def sK:List Nat:=varsOf 218
def sL:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffccffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gw:Lower sK sL 8:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=cl) (T2:=cm) (by decide +kernel) cz
def sM:List Nat:=varsOf 250
def sN:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffccffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gx:Lower sM sN 10:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=aM) (T2:=ah) (by decide +kernel) dq
def sO:List Nat:=varsOf 219
def sP:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffffeeaaffffeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gy:Lower sO sP 9:=carry_of (swaps:=[(5,7),(2,3),(4,6),(0,1)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def sQ:List Nat:=varsOf 249
def sR:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gz:Lower sQ sR 7:=carry_of (swaps:=[(4,5),(1,3),(2,4)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def sS:List Nat:=varsOf 251
def sT:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GA:Lower sS sT 12:=carry_of (swaps:=[(2,4)]) (roots2:=bp) (T2:=aO) (by decide +kernel) fY
def sU:List Nat:=varsOf 252
def sV:Nat:=0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GB:Lower sU sV 10:=carry_of (swaps:=[(3,4),(2,4),(0,2),(1,3)]) (roots2:=bC) (T2:=aU) (by decide +kernel) cF
def sW:List Nat:=varsOf 221
def sX:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafffffafa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GC:Lower sW sX 7:=carry_of (swaps:=[(4,7),(1,3),(2,6),(0,3)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def sY:List Nat:=varsOf 253
def sZ:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GD:Lower sY sZ 12:=carry_of (swaps:=[(1,3)]) (roots2:=gb) (T2:=gd) (by decide +kernel) sF
def ta:List Nat:=varsOf 222
def tb:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0fffffcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GE:Lower ta tb 9:=carry_of (swaps:=[(5,7),(2,3),(0,2),(4,6),(1,2)]) (roots2:=bY) (T2:=bZ) (by decide +kernel) cn
def tc:List Nat:=varsOf 252
def td:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GF:Lower tc td 7:=carry_of (swaps:=[(3,5),(4,5),(1,3),(2,4),(0,2)]) (roots2:=cr) (T2:=ct) (by decide +kernel) cC
def te:List Nat:=varsOf 254
def tf:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GG:Lower te tf 12:=carry_of (swaps:=[(2,4),(0,2)]) (roots2:=bp) (T2:=aO) (by decide +kernel) fY
def dt:List Nat:=varsOf 223
def du:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ge:Lower dt du 10:=lift_of (z:=21) (o:=0) (essPairs:=[(VAR 0,0,1),(VAR 2,0,4),(VAR 4,0,16)]) (by decide +kernel) cB
def tg:List Nat:=varsOf 247
def th:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GH:Lower tg th 10:=carry_of (swaps:=[(5,7),(6,7),(3,6),(4,7),(2,6),(0,1)]) (roots2:=dt) (T2:=du) (by decide +kernel) ge
def ti:List Nat:=varsOf 253
def tj:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GI:Lower ti tj 10:=carry_of (swaps:=[(5,7),(6,7),(3,6),(1,3),(4,7),(2,6),(0,3)]) (roots2:=dt) (T2:=du) (by decide +kernel) ge
def N:List Nat:=varsOf 255
def C:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefffffefafefaeca0
def gf:List Nat:=[5,10,7,11,5,19,20,5,10,11,20,17,36,33,35,66,65,7,72,19,35,67,129,130,13,14,22,22,28,68,68,26,28,41,42,136,136,65,76,48,144,162,97,100,134,140,176,164,73,192,33,80,112,224,192,36,48,10,104,224,38,10,14,80,70,66,82,98,98,68,48,36,13,26,33,88,56,25,130,162,129,131,25,146,161,80,36,48,42,137,17,152,144,132,66,68,17,84,148,17,144,168,50,21,17,132,80,5,44,81,38,50,41,129,5,21,5,33,65,68,144,80,133,145,66,21,37,69,17,65,129,80,145,11,67,35,161,7,13,10,81,19,129,20,133,84,44,33]
def gg:List Nat:=[4,8,6,9,6,18,16,1,2,3,4,1,4,1,34,2,1,3,64,3,3,3,1,2,9,6,18,6,24,4,64,18,12,9,34,8,128,64,12,16,16,34,96,96,6,12,160,160,9,64,96,64,96,96,128,32,32,9,40,160,34,12,12,16,6,64,18,34,96,6,96,96,12,24,32,24,40,9,128,160,3,3,24,18,160,18,160,160,40,9,18,24,0,4,6,1,4,16,16,16,128,40,34,4,64,128,1,64,40,1,6,18,40,128,0,16,128,160,16,16,64,128,0,16,18,0,32,0,0,0,0,0,1,8,1,1,1,2,8,0,16,1,9,0,4,4,12,0]
def tk:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x977f7ec7f29890617250000050422017b6abd,0x61d0000024008203200002010002017b2a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2ae01000c040410ac21f720012048ebac32e,0x2001000c040442b002d100012048ebac334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x78600e49c5a86a04001a15080b8417f0214d5,0x700000000408160000121600030412a001415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x40c20000110200b043b006601205f9304030a,0x44420000110200b043b006601204b1100000a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x2b0192b08a5df1cac3a44811841819c080c60,0x100018c8800e0c2c0a048000018094000060),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc01804021d06001d094d81db4ce8600107000,0x4021106001d094d81db4ce0400004000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x2104a92c02402c020083f8c7b0c6060258000,0x1000900000000d2003e0c2040040000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x141140d0202343a1bc0000862f31800c00000,0x232021000d0c0000840c01000000000)]
def GJ:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,0,4),(1,0,6),(1,1,2),(0,1,3),(1,1,3),(3,1,3),(1,1,6),(1,1,7),(1,1,11),(1,2,4),(1,2,6),(1,3,7),(1,3,8),(1,4,7),(1,4,11),(1,4,20),(1,5,7),(1,7,11),(1,7,19),(1,7,20),(1,8,20),(1,11,20),(1,11,28),(3,11,28),(1,20,28),(1,11,19),(1,2,7),(1,2,8),(1,4,6),(1,5,6),(1,6,7),(3,2,34),(3,4,34),(3,7,34),(1,8,25),(3,2,32),(3,4,32),(3,6,32),(3,7,32),(1,6,33),(3,4,35),(1,7,39),(1,0,7),(1,0,19),(1,3,16),(1,7,16),(1,0,28),(1,7,38),(1,8,38),(3,2,18),(1,4,59),(3,4,59),(1,7,18),(3,0,32),(1,2,63),(3,2,63),(1,4,63),(3,4,63),(3,4,37),(1,3,17),(1,5,9),(2,5,40),(1,9,40),(1,10,40),(3,10,40),(1,16,72),(3,19,72),(3,9,40),(1,7,9),(1,7,10),(3,2,40),(3,4,40),(3,2,72),(3,1,40),(3,1,72),(3,7,72),(3,6,72),(0,3,55),(3,3,55),(3,4,73),(3,6,73),(3,4,78),(1,4,86),(3,4,86),(3,4,30),(1,5,83),(1,9,83),(1,10,96),(1,10,83),(1,19,83),(1,10,77),(3,10,77),(1,19,77),(3,7,24),(1,9,89),(1,4,74),(1,2,83),(3,4,99),(3,9,99),(3,2,96),(3,4,96),(1,4,83),(1,1,110),(3,1,110),(1,4,82),(1,6,46),(1,7,46),(1,2,77),(3,4,117),(1,4,77),(3,4,100),(1,4,85),(3,5,53),(3,1,27),(1,5,27),(3,5,27),(1,4,41),(1,2,81),(3,0,40),(1,16,122),(1,40,122),(2,40,122),(1,6,122),(3,7,132),(1,7,122),(3,0,72),(1,17,46),(3,6,130),(3,0,44),(1,0,77),(3,0,57),(1,0,45),(1,0,83),(3,4,142),(1,83,122),(3,0,97),(3,2,97),(1,2,145),(1,0,101),(1,4,146),(3,0,98),(1,83,110),(1,0,81),(3,0,51),(1,13,40),(1,14,50),(3,3,112),(1,4,113),(3,3,75),(3,0,119),(1,6,13),(3,1,116),(3,3,136),(1,5,128),(3,3,62),(1,4,123),(1,6,71)]
def E:BT Decor:=buildWiresBT 8 tk GJ
def GK:List (List (Nat × Nat)):=[[],[(6,7)],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(6,7),(2,4)],[(6,7),(1,3)],[(2,4),(1,3)],[(6,7),(0,2)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(1,3),(0,4)],[(6,7),(2,4),(1,3)],[(6,7),(2,4),(0,2)],[(6,7),(1,3),(0,2)],[(2,4),(1,3),(0,2)],[(6,7),(2,4),(0,4)],[(2,4),(1,3),(0,4)],[(6,7),(1,3),(0,4)],[(6,7),(2,4),(1,3),(0,2)],[(6,7),(2,4),(1,3),(0,4)]]
def GM:BT (List (Nat × Nat)):=btOfList 5 GK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma H:goodPairs C gf gg:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GN:∀ x ∈ tk, faithful gf gg x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma I:btAll (fun x => faithful gf gg x ∧ x.1 < 2^256) E:=buildWiresBT_faithful GN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma J:btAll (fun sw => swapsValid sw = true ∧ permWord sw C = C) GM:=btAll_ofList (autos_of (by decide +kernel))
def GO:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,10),some (subcubeFast 0 8,10),some (subcubeFast 0 32,10),some (subcubeFast 1 0,12),some (subcubeFast 1 2,7),some (subcubeFast 1 32,9),some (subcubeFast 2 0,12),some (subcubeFast 2 8,9),some (subcubeFast 2 32,7),some (subcubeFast 3 0,10),some (subcubeFast 4 0,12),some (subcubeFast 4 2,7),some (subcubeFast 4 32,9),some (subcubeFast 5 0,10),some (subcubeFast 5 32,8),some (subcubeFast 6 0,10),some (subcubeFast 7 0,7),some (subcubeFast 8 0,12),some (subcubeFast 8 2,9),some (subcubeFast 9 0,10),some (subcubeFast 9 2,6),some (subcubeFast 10 0,11),some (subcubeFast 11 0,8),some (subcubeFast 12 0,10),some (subcubeFast 16 0,12),some (subcubeFast 16 2,7),some (subcubeFast 16 32,9),some (subcubeFast 17 0,10),some (subcubeFast 17 32,8),some (subcubeFast 18 0,10),some (subcubeFast 19 0,7),some (subcubeFast 20 0,10),some (subcubeFast 20 32,8),some (subcubeFast 21 32,7),some (subcubeFast 23 32,4),some (subcubeFast 24 0,10),some (subcubeFast 26 0,8),some (subcubeFast 32 0,13),some (subcubeFast 33 0,10),some (subcubeFast 34 0,11),some (subcubeFast 35 0,8),some (subcubeFast 36 0,10),some (subcubeFast 37 0,8),some (subcubeFast 38 0,8),some (subcubeFast 42 0,10),some (subcubeFast 48 0,10),some (subcubeFast 49 0,8),some (subcubeFast 53 0,7),some (subcubeFast 64 0,12),some (subcubeFast 64 2,9),some (subcubeFast 64 8,9),some (subcubeFast 64 32,7),some (subcubeFast 65 0,10),some (subcubeFast 65 2,6),some (subcubeFast 66 0,10),some (subcubeFast 66 8,8),some (subcubeFast 67 0,7),some (subcubeFast 68 0,10),some (subcubeFast 69 0,7),some (subcubeFast 70 0,7),some (subcubeFast 71 0,4),some (subcubeFast 72 0,10),some (subcubeFast 80 0,10),some (subcubeFast 81 0,7),some (subcubeFast 82 0,7),some (subcubeFast 84 0,7),some (subcubeFast 85 32,4),some (subcubeFast 96 0,11),some (subcubeFast 97 0,8),some (subcubeFast 128 0,12),some (subcubeFast 128 2,9),some (subcubeFast 128 8,9),some (subcubeFast 128 32,7),some (subcubeFast 129 0,10),some (subcubeFast 129 2,6),some (subcubeFast 130 0,10),some (subcubeFast 132 0,10),some (subcubeFast 132 2,6),some (subcubeFast 133 0,7),some (subcubeFast 136 0,10),some (subcubeFast 138 0,8),some (subcubeFast 144 0,10),some (subcubeFast 145 0,7),some (subcubeFast 146 0,7),some (subcubeFast 148 0,7),some (subcubeFast 149 32,4),some (subcubeFast 160 0,11),some (subcubeFast 161 0,8),some (subcubeFast 192 0,9),some (subcubeFast 192 2,8),some (subcubeFast 192 8,8),some (subcubeFast 193 0,6),some (subcubeFast 193 2,5),some (subcubeFast 193 8,5),some (subcubeFast 194 8,7),some (subcubeFast 195 8,4),some (subcubeFast 196 0,6),some (subcubeFast 196 2,5),some (subcubeFast 196 8,5),some (subcubeFast 198 8,4),some (subcubeFast 200 2,7),some (subcubeFast 201 2,4),some (subcubeFast 204 2,4),some (subcubeFast 208 0,6),some (subcubeFast 208 2,5),some (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,12)]
def GP:BT (Option (Nat × Nat)):=btOfList 8 GO
def K:Nat → Option PoolSpec:=lookSpec 1475 #[(1,0,1),(1,0,6),(1,2,4),(1,2,6),(1,7,19),(1,4,20),(1,20,28),(1,11,28),(1,11,19),(1,5,6),(1,1,2),(1,1,6),(1,4,6),(1,1,11),(3,2,18),(1,2,8),(3,4,37),(1,4,59),(1,0,2),(1,0,4),(1,1,7),(1,6,7),(1,9,40),(1,7,9),(1,7,16),(3,3,55),(1,8,20),(1,2,7),(1,4,7),(1,7,10),(1,10,40),(3,4,30),(3,1,40),(1,9,83),(1,11,20),(1,10,77),(1,1,3),(3,7,72),(1,7,38),(1,7,20),(1,4,11),(3,4,73),(3,7,24),(1,8,38),(3,4,34),(1,2,83),(3,19,72),(1,4,77),(3,4,32),(1,0,19),(1,0,28),(1,7,11),(1,5,7),(3,4,78),(3,4,40),(1,7,39),(3,2,72),(3,2,32),(1,2,81),(1,4,82),(3,5,53),(1,40,122),(1,7,122),(1,6,122),(1,8,25),(3,0,72),(1,0,7),(3,0,32),(1,4,86),(3,7,132),(1,0,83),(1,10,96),(3,9,40),(1,10,83),(3,4,142),(1,4,83),(1,19,83),(3,4,96),(1,0,81),(1,9,89),(3,4,35),(0,1,3),(0,3,55),(3,4,100),(1,3,8),(1,3,7),(1,3,16),(1,3,17),(1,14,50),(1,4,85),(3,2,34),(3,2,40),(3,0,57),(3,0,51),(1,7,18),(2,5,40),(3,0,40),(1,2,77),(3,4,117),(1,5,128),(3,2,96),(1,5,83),(1,5,27)] #[0x1a0000039000029c800a0cd0003089214184130a0c2048006050c0040612000041b00001ac800004e400404001018227080c10a8004047c00004000000334000c09800040460000042a001010a000001a000004c0002024a0000031000009280000054000000c0000003,0x600000143000020480000164004042a1010125000002100120cc000906122418227120c10a890608184050660000005500001a4800a0c24000001200000610e14107800e1434000027c0030409000032c8608089c304042a000000500000108000006c003042a0000309,0x68406123420315001018a8000047c00002300000036000061080000cd8000064e000001d003008f80180460000181a0000346063009280000c5400c02140000c0300000138000003c0000014000010a00000000000011800b024a000022700000218000282400a042a0000a03,0x1120060000001000000880200460000202a0080125000000700141024000141400504150034204801a1054000082a00001450000081000c105400000320000e390000718001c089400e043e00000381e381128000002c00e0430007020a063811280000060003028a000003e,0x194260e0ca134b065099b002a307c015183600a8c0d000c62483284c9c194262a00a1330185099280184c60014264a0001318005098880284c54000009a000001e243c113921e085400f042a0000a45000050c00002854000008a000000200000128022405401102144480125,0x2a6800a13452e4ca1800265164014269600a13362c5098a80284d64b14264e00a130018509a280284c9c015180600a8c1800546050018513019426000ca13450650998002e0cd098328b258a8c032c5460c162a302819426b258a8c052c5460d962a3030b15181a58a8c1a,0xd19181a68c8c1a34301a49a320cd019426246098c18000060c003050e400028725cb0309000001d002e0d24016180600b0c1800586050000013800018984c1945e305860d9306511819426860ca1337005860f802c306c016181a00b0309065099283284c4400018360000c49,0x18a200a135e0074a1c80384cf861426ac00613510074606803874d0014268c70a1315000001d9b080460000361a0000c0a06509af0032300c019183000c8c0a00646028032306c019181800c8c0d006460d1a32300cd19183068c8c0a3430a261a323014d19183668c8c0c,0x18000001a000001100406c34000002000d0c490068c9a19284cb0c94264e0001834304ca0a97265114000189c609961d304ca21982650d8013288c00c16090000029003e70d001e287250613560050626000070d0e14268670a13362c7060d802c702400028980001351,0x2c42000160c0000b0d03284d691212c06890960a00000022242586c00328048908349448419a13065001116061201096030084b0c212c50280212c14010944c00001828042587c0212c0a010961b0084b06004258340212c340108349008419a0000586c0002c1a00b0313,0xb9626305cb140a2e58181930651680172c3e00b961b2e5819300005838b9606260001603005898c000058600002c148c202510000028800058bca2306c800004520000f1d14460d68a2306b2511835e460ca2d002c087c01608360020349460ca2196080c4d18328b25820309,0x214264a10a1315005c9a8930651913172c3601316210000b9a002e8cf80002e7200f021f3c101898036106c00036426c19437000129a00009460004062c002251b000129c9e080c240004a1a0002521000d29a00080c4c000007e012160d005cb01802e582800000b60000060,0x28267c014041b0035406a8284d0c6a808263540409006139a004e343401328c80000d4e309ca1c984e106c0271a1c0138d2a004ca2f00265168018267c00c041b303420980004cf80004a7c012933e003420b001a112400d4a1a606840900509a1a5284d0c00d082610a1345,0x528721c2940f0000224800074d00290498000004c0060e9a0026a590000529c4c1045130a4e9c805274380293a54009a95a004d4ac8026a57802926b4082135100a4e9c8052112549d08260149359527420480284d60b1d081200213513a509a1803a104c01d081200a135a,0x151f0892a8f960d3e58a05003e50e401f2c1a00f84493e509a19f2c104cf96081278a13433c582099e2c102400000924c214453058209982c102400000ce013943900006a480009cbc0004e429ca13434e34209a71a1024016082600b04090000020800001500000e3e1c29417,0x15a9268600f933e54a41262a3ea4e40002c380001f34000141a0050a4354292686a02291350114848030a4e4c290826000041e00b14868000010002c1a1c0161337000149cab5210240004a14014a53900a420b185210240292686a52934300a42098052102401f2c3e7ca1330,0x132800011160900010a4800084d17212c06017214900b909a2e42586c0212c1c0171609425898c21284d150942660000280c5a1c28680001c84028080a003850e00014068050104c02808127c21351005820e003e580c01e082600f040900602098030102402b5272015a90d,0x80a7c004021f000179d0000bd397972c3620282182e4ca21802e584c0172c1200a235a0000f1a1e288d0c01446b2000233e008ca2d0046510c02328b200f944c007cb02803ea07c000507e014021f009c681801a51300271a0a013a83400014178000a08402242920112134,0x266200a820a000099800044c9400226300011315000010500004c95317267c5c994562e4ca27b10a0cd18880a72000203a0001008000080e0d84282a5c9944b000129d000010580000826000130200c0b06800020bc0080a360000821005c99f001014700172c0a0040251,0x32c1200b150d640c122b2060854682269600113511a08992802a4cf800d2a1a34113451a0898a800009300152686101134b080898c0000c8e403206bc019024c0000a9080640d0d9032a860018413000c20480640cc40002a721011345080898a80005434002268a5411325,0x26640001d3200009ad04044d440003a720001d3100749a1800000c8000266c000135800009ac96044c9cb02262a58a820a00009a18000550c00226ac0000a4914089a58a044d14502262a001134b660c12280640cd800000b001903300058a90962a080590304960190359,0x330a72cc2834300cc1acb43a4cc802a28b4d0e933100a8a2c82084d140343a72d0e93436874209b43a1024984048a4c202510060e9c9826750cc1d082660e840900d010f8068106c0343a1a01903640001a10b26874e403206b474202016410128806474e40033a680ce8409,0x36307201b18346c609a1806c4d65b180812000025400cc29f000000bc018266400c13310000c1c80304d0c0186a7200c353430d4209986a10240006a72000353408089960000d035a020802d01040000c9a1cb206d10c1b408260da0409000c20b3308094403306b40020201,0x704980139c344e709a1a71a704d38d381200e1d320034e869c3a4d0c69c3a12006824c00709a1801a7024e02262a0000065547ca1c8000017400000b8000005f0000fa48068082801f2c1c01a13320000a2d00684cc400028b2000343900d09a18068104c034081201b135a,0xc0d3a266069d090034e8480002930000706801c1c346e5810500007014037386401b824c00dce1a006e5835b9c268600b020a00006a600009cd00163826005024c3808996002c706c19638120019c34640ce21800670256850668002933e0a0c9a1800e087c38504141c28217,0x271a12000341c0001a0d972c34280161a1c01c935a00e49ac801ad03400d6826006b409304d3a1984e344cc271a12cc6824c0060689803034242831a2601982510a0c684b4044c61c971a92e4b9d342c34e86961a7438034267c35a1d131ad0e868d687424c1304300098251,0x36812001a83400c941f004ec8e53835068c81a843007c9a8803e584c4050414004024c741419a0010143401f2c12000020100141898030744c0183a1214196130a0cb04a83a4d0c0283a6858113180058e849d044c5400326b0b43824c000c9ad00064d6402726860138d13,0x187068000271c0001ba4806e60d1b98268600037320001b9c8076dcd1db7268601d961b00dcb018000dcd00006e6201b93430060b098030586c000707201c2834000140700009ce40000e5e000006200001ac00504d0da82262a6098225304c116006808040340400001b413,0x3d0612f590300005461280640c540320600c818c4500c819380004c0000c268a5461325003099280004c44000262a7cb131d74201a48000d0bc03c2e7201e160e00d01148000d038034042e01a020f6808992b4044c5403630126098211304c10a98260819b182c12000383e,0x16264e0001327265461280004d2c000188a24195300000b0300100d640320696000004b0000b0000640d14b15184258a8c25640cb0ab206589c0151842c818c562c546013e640d0deb20696f5903367ac8198bd640d15eb20660f59161d640cb16007ac875eb2062a01eb20f,0xc133a4e0098c51304ce8a8010308400066a20198c516614b0e802c3005985066c0000c5200cc1a300003150016184200e93360000e9b002c7400b1d262a0001346007498a80004d14b96260c00b9345005c99800005874415184200b934b2e5898a802e583c0132c4e00b1315,0x16184a68c8c027ac81af407ac86203d641501e83030000019be640d59eb206b200000487ac81a3bf7ac8f9fbd6472fde833400586013d640d19e96181a01eb2187ac8188807ac82803d0606019032500c818880003008000184acc28327660c622b30a0c54c133a6c5c99d30,0xc132c006099627304cb0a96184c9400018ac000353600009ab1826d4d8c136a2a6098c2500d499b006a3060035262a01a8c0a00d46018001048400000bc0048336006461080323094000002400d0c450068c981a323084d19184a00d190632c819619640c9c483044a2418211,0x14343a64a1a133e08089a328684cc54343a6200013471a7498a801a4d1400d262a6c20125406c20a9b080444999184a0001301346499380004d78c8c264a5cb13250000034972c4c45b18262a00c1300006098880304c54018260c202821d62201a4b6304cd8016181c00c1336,0x46620119d431a10e8980008d646843a1200f233e005ce9c9e1a104cf230a7c34203493c7119f0038106c01e1a5400f0d0e00511b200288d78f0d081200b9332005c99897263514b9626465cb131d0000e9d1726750d9852c460069d0e2c34e89961a7424202268ea1a1332,0xb961a1308b9343005c6a480844d6804226b308b93302e58681800024f800906b4000160100241a196120c4c00906b25848309120c122802c34040161a0060b0d133058684802c3434b0d262aa1a13433ea099f001074e40080a730d19d43845d19f002e74d000046b40002332,0x405064c00403498a5c998422e4cfa118267c20283031014116800014e80002ea40001754000068080003400c131a2a013a3432e4c6a7802e3530b931aac00ba343882010fc22e8d0c04246b40212359406c687000080ec69b082a5c98d4b00011a18046950c01726865cb0d13,0x90498004821d0024107800104bc0008274000413f0024198800001a000806b00138d01009c680004e34440271a0c9c69315549c68694064d600000a7e0001f410000faa1f0a4cf8a0326b450193593e58a12a71a4c940182603104053e00201ad080a0d0c40506262028309,0xb32064f1a03d1b8d01e86c07ac94603d649901e834980f590ec07ac83e03d0613019032c7ac81b23e7a586df3d2c1b01e961b7ac819ec07a5835eb206b400016027ac818900425808000001101903567ac8b0c3d64582803d06680048223100c1258806095800904a20048332,0x2117467b08ba336006c2138a36105451b080c00504490001292a30808b000a08268c2022700289a280144c5400000b4024961b0124b0f80005846422429321121349088b04804258bc000428a00021300084b1296640c563a12c4a01096218e84b00804258710b2068a8590330,0x1121266088b13150000014cd42583404c426931096259884b06cc2c4c566a12c1531093459858993ca42580c04b4292025a1349684b06809658265212c1b1cb13278e84b0547424d163a126611cb131542589928000d10551f28980003409000052718262854017467a00ba336,0x288906920000050010cb00001294704a5a438241161da2241a1802e4d58017707200bb834000002b0000e0ea81f26a340f933e00dd1a1b72c4c540502c373db93436e5899280009ce8000009400000359c890a4ce4484d27222c51390960d01389804e445825116264e8909345,0x154a420005600ac55290d1120c4c0090448004d51ba22418480010c000433800012d221862410e800094fc0004a8200025024610108a3080819184042a9249351a890b06880a088e2080498000084e845c9a2c22e58280092c5d44483360000029d33230844822c460002545,0x433a860219c43007020980381024000867200202458610112c3080854000048a0218225010c10c0086085405a26b368b93560000ba600005d240430414021821f000001e000025380002e7e0048217006c20380361056d17269600b934f016529080b05484057127c000252f,0x5c86860002843010dc1c8000a0f802786870cb0218865810ac32c082800004ac000001c86e01160014091618a042a00000660000031c30a0cf6da80836021a83200001ad0086a0c61a8043e021a84300021a1c30808b218506860004341861419b008614e400404a20219d39,0xbab2000493f00f0b06b4041055a02084ad420215007c228803e510c05d4e6000104450058e87000411440343a86d0104183a1010a962a0860b15044a00b021500281258000092c00404960020218005410c00000862d85867d6c20251001c2950786087c000b8920005c34,0x34043001a021100d010a80680818034044a0005e430002f2d00017964385045370b0225882029c802e9cd0016043001a82157028103001038840273887746824c2c7010c16380854b9304ac28e02150000e218038086001c042a7cb04233e5820eaa3e510e234043e0005d5a,0xbe02c2e5f0160f725c99f392e4d44000c09c000603a0001a2180000080038142a00035150000b0a8001254803c2e98f0b9629785cb0bbc2e583c0172c2ee4b9343017c10300007ce80003e9c00f9749007cb9a1f2c5044f96280c5c9b443005da13002ed06c017682600bb409,0x662c2a00000144484b1480ca4d68022429801121394484b0b808e583e5212c3000013128e84b0c008e85140474260023961501930a280c984c32612c2a032160300031ad00018d640632c1b8a493430184b0c00c258280612c4a0000044000002b8050d0f8028688600b962b,0x5e5600033ad00019d64066428a0332130]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GQ:Slice N C (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333) 12:=mappedSlice (f:=identifyRow 0 0 4 1) (R:=qj) (G:=qk) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ey
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GR:Slice N C (subcubeFast 208 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=eF) (qGoal:=eG) (by decide +kernel) oz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GS:Slice N C (subcubeFast 208 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=eH) (qGoal:=eI) (by decide +kernel) oA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GT:Slice N C (subcubeFast 204 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=fv) (qGoal:=fw) (by decide +kernel) ql
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GU:Slice N C (subcubeFast 201 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=fx) (qGoal:=fy) (by decide +kernel) qm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GV:Slice N C (subcubeFast 200 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=fz) (qGoal:=fA) (by decide +kernel) dr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GW:Slice N C (subcubeFast 198 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=fv) (qGoal:=fw) (by decide +kernel) ql
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GX:Slice N C (subcubeFast 196 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=qn) (qGoal:=qo) (by decide +kernel) Ez
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GY:Slice N C (subcubeFast 196 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=qp) (qGoal:=qq) (by decide +kernel) EA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GZ:Slice N C (subcubeFast 196 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=qr) (qGoal:=qs) (by decide +kernel) EB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ha:Slice N C (subcubeFast 195 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=fx) (qGoal:=fy) (by decide +kernel) qm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hb:Slice N C (subcubeFast 194 8) 7:=slice_fast_direct (zDead:=0) (qRoots:=fz) (qGoal:=fA) (by decide +kernel) dr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hc:Slice N C (subcubeFast 193 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=qt) (qGoal:=qu) (by decide +kernel) EC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hd:Slice N C (subcubeFast 193 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=qv) (qGoal:=qw) (by decide +kernel) ED
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma He:Slice N C (subcubeFast 193 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=qx) (qGoal:=qy) (by decide +kernel) EE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hf:Slice N C (subcubeFast 192 8) 8:=slice_fast_direct (zDead:=0) (qRoots:=qz) (qGoal:=qA) (by decide +kernel) EF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hg:Slice N C (subcubeFast 192 2) 8:=slice_fast_direct (zDead:=0) (qRoots:=qB) (qGoal:=qC) (by decide +kernel) EG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hh:Slice N C (subcubeFast 192 0) 9:=slice_fast_direct (zDead:=0) (qRoots:=qD) (qGoal:=qE) (by decide +kernel) EH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hi:Slice N C (subcubeFast 161 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) dX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hj:Slice N C (subcubeFast 160 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=ay) (qGoal:=F) (by decide +kernel) dp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hk:Slice N C (subcubeFast 149 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cc) (qGoal:=cd) (by decide +kernel) ce
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hl:Slice N C (subcubeFast 148 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aT) (qGoal:=aD) (by decide +kernel) cf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hm:Slice N C (subcubeFast 146 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ff) (qGoal:=fg) (by decide +kernel) pe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hn:Slice N C (subcubeFast 145 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fh) (qGoal:=fi) (by decide +kernel) pf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ho:Slice N C (subcubeFast 144 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aF) (qGoal:=aj) (by decide +kernel) cw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hp:Slice N C (subcubeFast 138 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=qF) (qGoal:=qG) (by decide +kernel) EI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hq:Slice N C (subcubeFast 136 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bM) (qGoal:=aX) (by decide +kernel) ds
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hr:Slice N C (subcubeFast 133 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=qP) (qGoal:=qQ) (by decide +kernel) Fa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hs:Slice N C (subcubeFast 132 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=qR) (qGoal:=qS) (by decide +kernel) Fb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ht:Slice N C (subcubeFast 132 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qT) (qGoal:=qU) (by decide +kernel) Fc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hu:Slice N C (subcubeFast 130 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qV) (qGoal:=qW) (by decide +kernel) Fd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hv:Slice N C (subcubeFast 129 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=qX) (qGoal:=qY) (by decide +kernel) Fe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hw:Slice N C (subcubeFast 129 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qZ) (qGoal:=ra) (by decide +kernel) Ff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hx:Slice N C (subcubeFast 128 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=rb) (qGoal:=rc) (by decide +kernel) Fg
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hy:Slice N C (subcubeFast 128 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=bY) (qGoal:=bZ) (by decide +kernel) cn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hz:Slice N C (subcubeFast 128 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=rd) (qGoal:=re) (by decide +kernel) Fh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HA:Slice N C (subcubeFast 128 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=fG) (qGoal:=fH) (by decide +kernel) rf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HB:Slice N C (subcubeFast 97 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ee) (qGoal:=ef) (by decide +kernel) nI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HC:Slice N C (subcubeFast 96 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=eg) (qGoal:=eh) (by decide +kernel) nJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HD:Slice N C (subcubeFast 85 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=ec) (qGoal:=ed) (by decide +kernel) nF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HE:Slice N C (subcubeFast 84 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fm) (qGoal:=fn) (by decide +kernel) pK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HF:Slice N C (subcubeFast 82 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rg) (qGoal:=rh) (by decide +kernel) Fi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HG:Slice N C (subcubeFast 81 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ri) (qGoal:=rj) (by decide +kernel) Fj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HH:Slice N C (subcubeFast 80 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fI) (qGoal:=fJ) (by decide +kernel) rk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HI:Slice N C (subcubeFast 72 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rl) (qGoal:=rm) (by decide +kernel) Fk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HJ:Slice N C (subcubeFast 71 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=ro) (qGoal:=rp) (by decide +kernel) Fl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HK:Slice N C (subcubeFast 70 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rr) (qGoal:=rt) (by decide +kernel) Fm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HL:Slice N C (subcubeFast 69 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ru) (qGoal:=rv) (by decide +kernel) Fn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HM:Slice N C (subcubeFast 68 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rx) (qGoal:=ry) (by decide +kernel) Fo
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HN:Slice N C (subcubeFast 67 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rz) (qGoal:=rA) (by decide +kernel) Fp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HO:Slice N C (subcubeFast 66 8) 8:=slice_fast_direct (zDead:=0) (qRoots:=rB) (qGoal:=rC) (by decide +kernel) Fq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HP:Slice N C (subcubeFast 66 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rD) (qGoal:=rE) (by decide +kernel) Fr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HQ:Slice N C (subcubeFast 65 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=rF) (qGoal:=rG) (by decide +kernel) Fs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HR:Slice N C (subcubeFast 65 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rH) (qGoal:=rI) (by decide +kernel) Ft
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HS:Slice N C (subcubeFast 64 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=rJ) (qGoal:=rK) (by decide +kernel) Fu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HT:Slice N C (subcubeFast 64 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=rL) (qGoal:=rM) (by decide +kernel) Fv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HU:Slice N C (subcubeFast 64 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=rN) (qGoal:=rO) (by decide +kernel) Fw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HV:Slice N C (subcubeFast 64 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=rP) (qGoal:=rQ) (by decide +kernel) Fx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HW:Slice N C (subcubeFast 53 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=cL) (qGoal:=cM) (by decide +kernel) cB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HX:Slice N C (subcubeFast 49 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ek) (qGoal:=el) (by decide +kernel) nL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HY:Slice N C (subcubeFast 48 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aZ) (qGoal:=aK) (by decide +kernel) cO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HZ:Slice N C (subcubeFast 42 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aJ) (qGoal:=ad) (by decide +kernel) co
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ia:Slice N C (subcubeFast 38 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=nY) (qGoal:=nZ) (by decide +kernel) AB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ib:Slice N C (subcubeFast 37 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=ev) (qGoal:=ew) (by decide +kernel) oa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ic:Slice N C (subcubeFast 36 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=ex) (qGoal:=ey) (by decide +kernel) ob
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Id:Slice N C (subcubeFast 35 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=oc) (qGoal:=od) (by decide +kernel) AC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ie:Slice N C (subcubeFast 34 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=ez) (qGoal:=eA) (by decide +kernel) oe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma If:Slice N C (subcubeFast 33 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=eB) (qGoal:=eC) (by decide +kernel) of
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ig:Slice N C (subcubeFast 32 0) 13:=slice_fast_direct (zDead:=0) (qRoots:=aV) (qGoal:=aq) (by decide +kernel) Bw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ih:Slice N C (subcubeFast 26 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=rR) (qGoal:=rS) (by decide +kernel) Fy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ii:Slice N C (subcubeFast 24 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bC) (qGoal:=aU) (by decide +kernel) cF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ij:Slice N C (subcubeFast 23 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=pP) (qGoal:=pQ) (by decide +kernel) DE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ik:Slice N C (subcubeFast 21 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=cL) (qGoal:=cM) (by decide +kernel) cB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Il:Slice N C (subcubeFast 20 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=cl) (qGoal:=cm) (by decide +kernel) cz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Im:Slice N C (subcubeFast 20 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aM) (qGoal:=ah) (by decide +kernel) dq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma In:Slice N C (subcubeFast 19 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rY) (qGoal:=rZ) (by decide +kernel) FP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Io:Slice N C (subcubeFast 18 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fP) (qGoal:=fQ) (by decide +kernel) sb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ip:Slice N C (subcubeFast 17 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=sd) (qGoal:=se) (by decide +kernel) FQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iq:Slice N C (subcubeFast 17 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fR) (qGoal:=fS) (by decide +kernel) sf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ir:Slice N C (subcubeFast 16 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=sg) (qGoal:=si) (by decide +kernel) FR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Is:Slice N C (subcubeFast 16 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=sj) (qGoal:=sk) (by decide +kernel) FT
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma It:Slice N C (subcubeFast 16 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=bp) (qGoal:=aO) (by decide +kernel) fY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iu:Slice N C (subcubeFast 12 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=st) (qGoal:=su) (by decide +kernel) Gp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iv:Slice N C (subcubeFast 11 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=sv) (qGoal:=sx) (by decide +kernel) Gq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iw:Slice N C (subcubeFast 10 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=sy) (qGoal:=sz) (by decide +kernel) Gr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ix:Slice N C (subcubeFast 9 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=sA) (qGoal:=sB) (by decide +kernel) Gs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iy:Slice N C (subcubeFast 9 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sC) (qGoal:=sD) (by decide +kernel) Gt
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iz:Slice N C (subcubeFast 8 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=fZ) (qGoal:=ga) (by decide +kernel) sE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IA:Slice N C (subcubeFast 8 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=gb) (qGoal:=gd) (by decide +kernel) sF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IB:Slice N C (subcubeFast 7 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=sG) (qGoal:=sH) (by decide +kernel) Gu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IC:Slice N C (subcubeFast 6 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sI) (qGoal:=sJ) (by decide +kernel) Gv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ID:Slice N C (subcubeFast 5 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=sK) (qGoal:=sL) (by decide +kernel) Gw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IE:Slice N C (subcubeFast 5 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sM) (qGoal:=sN) (by decide +kernel) Gx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IF:Slice N C (subcubeFast 4 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=sO) (qGoal:=sP) (by decide +kernel) Gy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IG:Slice N C (subcubeFast 4 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=sQ) (qGoal:=sR) (by decide +kernel) Gz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IH:Slice N C (subcubeFast 4 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=sS) (qGoal:=sT) (by decide +kernel) GA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma II:Slice N C (subcubeFast 3 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sU) (qGoal:=sV) (by decide +kernel) GB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IJ:Slice N C (subcubeFast 2 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=sW) (qGoal:=sX) (by decide +kernel) GC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IK:Slice N C (subcubeFast 2 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=fZ) (qGoal:=ga) (by decide +kernel) sE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IL:Slice N C (subcubeFast 2 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=sY) (qGoal:=sZ) (by decide +kernel) GD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IM:Slice N C (subcubeFast 1 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=ta) (qGoal:=tb) (by decide +kernel) GE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IN:Slice N C (subcubeFast 1 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=tc) (qGoal:=td) (by decide +kernel) GF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IP:Slice N C (subcubeFast 1 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=te) (qGoal:=tf) (by decide +kernel) GG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IQ:Slice N C (subcubeFast 0 32) 10:=slice_fast_direct (zDead:=0) (qRoots:=dt) (qGoal:=du) (by decide +kernel) ge
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IR:Slice N C (subcubeFast 0 8) 10:=slice_fast_direct (zDead:=0) (qRoots:=tg) (qGoal:=th) (by decide +kernel) GH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IS:Slice N C (subcubeFast 0 2) 10:=slice_fast_direct (zDead:=0) (qRoots:=ti) (qGoal:=tj) (by decide +kernel) GI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma M:btAll (fun o => ∀ p, o = some p → Slice N C p.1 p.2) GP:=btAll_ofList (P:=fun (o:Option (Nat × Nat)) => ∀ p, o = some p → Slice N C p.1 p.2) (forall_cons (someSlice IS) (forall_cons (someSlice IR) (forall_cons (someSlice IQ) (forall_cons (someSlice IP) (forall_cons (someSlice IN) (forall_cons (someSlice IM) (forall_cons (someSlice IL) (forall_cons (someSlice IK) (forall_cons (someSlice IJ) (forall_cons (someSlice II) (forall_cons (someSlice IH) (forall_cons (someSlice IG) (forall_cons (someSlice IF) (forall_cons (someSlice IE) (forall_cons (someSlice ID) (forall_cons (someSlice IC) (forall_cons (someSlice IB) (forall_cons (someSlice IA) (forall_cons (someSlice Iz) (forall_cons (someSlice Iy) (forall_cons (someSlice Ix) (forall_cons (someSlice Iw) (forall_cons (someSlice Iv) (forall_cons (someSlice Iu) (forall_cons (someSlice It) (forall_cons (someSlice Is) (forall_cons (someSlice Ir) (forall_cons (someSlice Iq) (forall_cons (someSlice Ip) (forall_cons (someSlice Io) (forall_cons (someSlice In) (forall_cons (someSlice Im) (forall_cons (someSlice Il) (forall_cons (someSlice Ik) (forall_cons (someSlice Ij) (forall_cons (someSlice Ii) (forall_cons (someSlice Ih) (forall_cons (someSlice Ig) (forall_cons (someSlice If) (forall_cons (someSlice Ie) (forall_cons (someSlice Id) (forall_cons (someSlice Ic) (forall_cons (someSlice Ib) (forall_cons (someSlice Ia) (forall_cons (someSlice HZ) (forall_cons (someSlice HY) (forall_cons (someSlice HX) (forall_cons (someSlice HW) (forall_cons (someSlice HV) (forall_cons (someSlice HU) (forall_cons (someSlice HT) (forall_cons (someSlice HS) (forall_cons (someSlice HR) (forall_cons (someSlice HQ) (forall_cons (someSlice HP) (forall_cons (someSlice HO) (forall_cons (someSlice HN) (forall_cons (someSlice HM) (forall_cons (someSlice HL) (forall_cons (someSlice HK) (forall_cons (someSlice HJ) (forall_cons (someSlice HI) (forall_cons (someSlice HH) (forall_cons (someSlice HG) (forall_cons (someSlice HF) (forall_cons (someSlice HE) (forall_cons (someSlice HD) (forall_cons (someSlice HC) (forall_cons (someSlice HB) (forall_cons (someSlice HA) (forall_cons (someSlice Hz) (forall_cons (someSlice Hy) (forall_cons (someSlice Hx) (forall_cons (someSlice Hw) (forall_cons (someSlice Hv) (forall_cons (someSlice Hu) (forall_cons (someSlice Ht) (forall_cons (someSlice Hs) (forall_cons (someSlice Hr) (forall_cons (someSlice Hq) (forall_cons (someSlice Hp) (forall_cons (someSlice Ho) (forall_cons (someSlice Hn) (forall_cons (someSlice Hm) (forall_cons (someSlice Hl) (forall_cons (someSlice Hk) (forall_cons (someSlice Hj) (forall_cons (someSlice Hi) (forall_cons (someSlice Hh) (forall_cons (someSlice Hg) (forall_cons (someSlice Hf) (forall_cons (someSlice He) (forall_cons (someSlice Hd) (forall_cons (someSlice Hc) (forall_cons (someSlice Hb) (forall_cons (someSlice Ha) (forall_cons (someSlice GZ) (forall_cons (someSlice GY) (forall_cons (someSlice GX) (forall_cons (someSlice GW) (forall_cons (someSlice GV) (forall_cons (someSlice GU) (forall_cons (someSlice GT) (forall_cons (someSlice GS) (forall_cons (someSlice GR) (forall_cons (someSlice GQ) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def IT:BT (List (List Nat)):=BT.empty
lemma IU:btAll (fun bk => ∀ xs ∈ bk, Impossible C (6 - 1) xs.toFinset) IT:=trivial
def tm:List NodeSpec:=readDeltaNodes 2 (unpackWords 7 [(20,0xd8087161204200001f30248240820400007)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IV:∀ ns ∈ tm, Impossible C 6 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J IU (by decide +kernel)
def IW:BT (List (List Nat)):=refBuckets E [tm] #[0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma gh:btAll (fun bk => ∀ xs ∈ bk, Impossible C 6 xs.toFinset) IW:=refBuckets_all (forall_cons IV (fun _ h => (List.not_mem_nil h).elim))
def tn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x877d21bb1bcb84a00a80dd4a25220a867f9486d44e353054),(64,0x2028b7f0f531ecde9105476aca67ccc910145e1b29489002),(33,0x3b5787a8664880a35a9ea1992)]))
def tp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x145b3c7288d3b244250c34fa7f49101478f3cf50cc91054),(64,0x5394482a057cf92c762a148951636424a4005153e9e74491),(35,0x7e9e2b12ca728905457df14e96)]))
def tq:List NodeSpec:=readDeltaNodes 1 (varNats 2 (unpackWords 3 [(24,0xb492278dc4f24c254)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchIX:∀ b ∈ ([tn,tp,tq]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 7 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J gh (by decide +kernel)
def Ja:BT (List (List Nat)):=refBuckets E [tn,tp,tq] #[0,0,0,6,0,16,0,36865,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,13,0,0,0,0,2,0,0,12,0,0,0,0,0,0,0,4,8,0,0,10,0,0,0,61447,0,0,0,0,5,17,0,0,0,0,14,0,11]
set_option maxRecDepth 20000 in
lemma aH:btAll (fun bk => ∀ xs ∈ bk, Impossible C 7 xs.toFinset) Ja:=refBuckets_all batchIX
def tr:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x5c8482f1651112111932042191c21b474ee2d2161423319184e312111110019),(64,0x195886d36311221011904fe482d363222111193a5a1896884e2d3652210418),(35,0x44191e6bc18d19121141051818b36311221)]))
def ts:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc6c3d92510153fd8ad361ec92882a9b7452986c3cc251055),(64,0xd9c90cf552894884aac8dff1d2d48d566867aab25221451d),(64,0x861ff1ffac6656dcaf55c79220e3d5923a648ab25220aa74),(19,0xb4f9daab25220a)]))
def tt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf23b4d319291095576ce470d3c94882aad7c365591291054),(64,0x559291055576ce42bb84a44154cff1931a6325220aa65fd6),(64,0x3c9ae2fbe36ab5635220f3cdd22d0cc718d244154cff2d97),(4,910)]))
def tu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xaedd8da65362c6a441ea1c8cb0cd51a647368ee2df48850f),(64,0xc6476ae92441aa2ba632d5d2251054475cac994f79d3c3fe),(64,0x515d31b6ac524882a2ba632d58a4910543f3962da1d377a4),(41,0x39b6771871e8944155dff3b57489441)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJb:∀ b ∈ ([tr,ts,tt,tu]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5318ea2510557ae86ce71a912882aab1df33b4e352251095),(64,0x54cba19777bec64a62e9244350dba3eae5d2251055736c6c),(64,0x9e1bfab6e59eeba4910d436e3778b5eb5f8c8e531749220c),(38,0x1cb16d0dfd5b72c73b5749220c54e)]))
def tw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a8074a5124a24aae799c90f3752894884a8375289251055),(64,0x5f43ac2894490953accbe8f1b732512425559f1b73249248),(60,0x48c9be30ecac64a44355ff163a58b1d958c94886a9d66)]))
def tx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x64a4418aacb7dccb24563e6d64a44354dd21b9fcc9449055),(64,0x38c44a20aaf996487e7cdac94884aaf6e556f299648b1a6d),(64,0x8adb9fc635cc488394559df1db99fec7631be91069ee6563),(34,0x1fb219335d24882a1311d74337)]))
def ty:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc63a61d4e488314376d0c3ba49220a86cd32b0e662251055),(64,0x5a6cbc5cc78c48831476ec73e7546944150eba9972b7656d),(64,0xd33ea1bd24910d53e6c7f8b7f4e9a47cfe92488314353ba6),(37,0x3db77e6cadb9195c462443511b5d)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJf:∀ b ∈ ([tv,tw,tx,ty]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a3f7c329bd265105448db61972f21924861d0cc62488394),(64,0xdeec6cc6f2e128135476ec6d3968792482a3f7c54fe93288),(64,0x24a00c54eff451f2b9250055334b8f9caa512802a8322e91),(27,0xb7b96f7a98efe638de57)]))
def tA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x49252e5253ee90df8e8e124807a8743e6b0e329eba248095),(64,0x54a249002a0fbbe3763a2ac92412a9df586fc74559248055),(64,0x449201541def867ae42892412a907dfe298d94a4484543e6),(13,128656599721)]))
def tB:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0x10421000281088210bb83f9d66d83de8e791c601a93fa4888e2084103901cf0750f0210882100029),(64,0x417da355ee20821080282fb468bdc410421005002578a0c262c607f149e190821084882fb468bc32),(44,0x11a5634b681175648af816445406421040840b32149e19082108001)]))
def tC:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x31803ffe5874a7182a21111219028881fdc3fd92eda18ec18a59732d22211618),(64,0x182a21111719049e1969e7f4a7182a2111131943ada29bb2fda1c97182a21111),(64,0x92c2222105184289b3ea1d9e397182822111131907c2aea3b83d81a5a86c1e61),(41,0x21aac6d1a4a3f2112112191b8826885fd2dfe6b1)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJj:∀ b ∈ ([tz,tA,tB,tC]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x543f6f32c98d36a87f489252af3fb1d3e7f9d943fa4490d5),(64,0x3ce8912435425ad8ed5e1e7444a252a67b71b94c7f489201),(64,0xe7448924aa0edaade63a7c72879d122496aa325c74f8dd54),(45,0x1d27cadb9fe64331fd22484a8534b8daa1)]))
def tE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdb6326874f9eaa450fe9124354a7f2b6e7698b43fa2512d5),(64,0x923e6557928920aa65923e6657124a20aa6674ea492880a9),(64,0x953adb8ddebf7e323ea544a44355fbf1fd43aa25220aa65),(23,0xb687fb948e2b11291)]))
def tF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x12a6c3e72892400a996486658f8492882a9cbabc9449015),(64,0x44920154ebf2971deeca6a512480d43a7c7dde394cf0a249),(53,0x1df487ee51248054371f3944920054ef347e99e1)]))
def tG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20aaa6c49249002a9fb8dd8924920254fbbe27ec51248055),(64,0x215566f0df17c4924905536650924a002aacfa390dd89249),(41,0x1be556db8f46f649202542d9c849250)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJn:∀ b ∈ ([tD,tE,tF,tG]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x76add43a32886a196487750e8c9241514b71ea9bd9248055),(64,0xa65921d143a32490543a7ced594aa1d1944154c9a397ab6e),(64,0x3ec9159b13754492884a8535449288055536314b5124a20a)]))
def tI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2afdce53752492482abf713af2512402a8536449288055),(64,0xaa77f32c6f6a9250055055f664b1d95249252aac849249),(47,0x1597abefcd2ca7249252aafb619d6539249)]))
def tJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x55322d72b3787f4b29c92486a980c3f4f15cb2951448495),(64,0x157f9dd5c492880a9b56c64a492880a9dfcca558dee1250),(50,0x15332b8925101554caaf25124054e362bc9449)]))
def tK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a4186bf092514157ee3bf57928920154ef95e49448015),(64,0xca12512957ee325579289201556caf24a2400a9f22bc9289),(47,0x945a498c3e98d425200c541f6fab493278d)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJr:∀ b ∈ ([tH,tI,tJ,tK]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x90dd9e3a124a20aaadb8da6ce74249441557c77a49448015),(64,0x4bdb96fb9964872c69d4928935532c90d8f9d0944905532c),(64,0x8aab0e8492892a9f2e3b6ab7f0e961cfa86528920c543bae),(29,0x2d6d8b9b55389441501964)]))
def tM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5aed973cd331c4a24c54c3fd90ff6d5aed9770cc71288314),(64,0x2510557ef8553f9e4920a8fdf0994de792482a1a97d0ff6d),(64,0xd55adcf655daea2510553a7f0d87554c44a20aaa63aaaca),(32,0x3aff8ef22d6e5e9b79eea251)]))
def tN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x955aea6cfa198f70a25109556f8a2d6e37f331eea2510d5),(64,0x2482a2d6feb79b1b0cc7ba89442556bf2d7e367331eea251),(64,0x2482a3b763757cea792482a3b0e87c3192482a3b0ee7c319),(15,6979924476697)]))
def tO:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0xa9b0ce6c25124054dd8cc6c24944054cb24716863249054),(56,0x7ee3ef57928920154fb95e494480157b99cd84a248)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchJv:∀ b ∈ ([tL,tM,tN,tO]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 8 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J aH (by decide +kernel)
def tP:BT (List (List Nat)):=refBuckets E [tr,ts,tt,tu,tv,tw,tx,ty,tz,tA,tB,tC,tD,tE,tF,tG,tH,tI,tJ,tK,tL,tM,tN,tO] #[0,2617770105,17,0xb50b20a606c041,872562691,0,655510,8,0xa70a1061058050,0,696438,2399645779,85,651297,0xb60b107704e02a,5636322553869,2198249520,0xac0a209709203d,0xbd0b308d07f05f018,0x7505d05b043025004,634885,0xbe08806801f01e01d,1661087745,0x9e07c02701b,0,109,0xba06605e04403e,0x8907a05704c037017,188444,2483576850,294919,344096,553017,0xae09a022006,749626,766008,1912823858,2768482330,573569,19,0x6405904d04a015,0,0x9007006f031019009,602242,2869497998,286780,9554322821186,716816,0xb00a807302f,0xb80a90a309d06704b,0xb40ad099016,258086,9072581586946,14,9141704147054,0x7e05c05102800a,86,438343,0xa4071033029,0x9804502c014,0xb906906502b,2500206645,0xbc07d05a04002d00c,0]
def Jz:BT (List (List Nat)):=fastPrior E #[0,0x70605040201009e2e92007271e040302010098207810604030201009,0x7060513640309018,0x7270b420403020181b071405040308012d917341f06050302012e94e0706050403013f2d9391d070b053503018,0x71f06050a03012e4c949073a140504030901948281110050a0403029,0,0x15110605040e020032948070605420302012e9,0x70605130a0901588,0x71f0605040301434c97407060504020100a2948072605030201872e94f1724261f05030180710060403020100899,0,0x221d340b050403012990706040302010090539,0x2845050403020100329070605040302010091917260503020100878,0x17260503090201878,0x24340605040e030132949071405040e0309019,0x7270b040302013f81b0714050403018c2d907060403020100907a9070604020100587a8070605630a03096a019,0x1d1b17260503090183707840604030201009284f1f051303017070605130a036009019,0x7271f040301875284e072605030201872e9480706050a03012e4c9,0x33340b040302012a8071f060572040301879480706050302013f2e928340504030201533291b172605030901528,0x7060504020100a42e91b071405040301802d9283405040e03020132937070605610403020091d072605030901598394e14050a03017,0x7060403020100908201734261f05030201917261f0503020187833070b040309012a807181405030901598284e1005130a03018,0x48070605040301434c94828071005130a03019,0x70605a5030201002e907060563620403090194838072605030201879490714050403090180714050a6903090180714050a030901598,0x48072605030201005e94e073a1814050403019070b310504030208019,0x706056f030201002e907060561040302019194f07140503090159807140504030901598,0,0x4e0706050302013f2e9,0x1b070605040301872d93407261f050302012e91707261f050302013f933394e0b04030201839070b050309012a8,0x70605040309930100907060561040302010094817260503020100882280710040302010091b1714050309015984e072614050a0e03019,0x706050a030902016e949071405030901598,0x4807060572040301879070605040309018e9294f071f0605130e03019,0x28111005040302002e907100605130a0301569,0x481726050302018784e07181405040e03019,0x7060504030901009293807140b05040e03019,0x7140b050403012d4190706059d030201002e9071405040e0309016794807100605130a03019,0x33240b040302018c807260b050309012a8,0x1b070605420302012e917071405030901598,0x72306050403013f2d91b1714053503017071f06050a0301522e9,0x24341f06050403012e93928240b05350301839284e14050a03018,0x70605040302010097907271e04030201002e9,0x48070605130a0e03019,0x7261f05040301875291c4f07261f05030188207100604030201009288610040302010084f071e1f06051303019,0,0x3728340504030201329390706050309012d59949390706050309012a9480706050a0302015e9174e181405030174928241005040309019,0x281105040302005332907271f42040302018,0x3322340b0403020182807050402010058329281105040e030200329,0x11071084060403020093339240b040309018,0x7060504036002019190706056f030201006e928171005030201002e93322070b040309018,0x490714050403018c52948070605130a03018,0x1b071405720403019f934140b050403012980706040302018e007a9480706050a0301522e9,0x33070b420403020181d340b05040301298071f0605040301872d907060504020100582e907261f050302012e4392886071004030201009,0x1b0714050403012d41907140b05040308012d9070605040201009c2e948071e0605130a03019,0x2239070b050309012a94907181405030901599,0x4807271f04030187529480726050403018752924100605040309015a928111005130a03098,0x70605130a036001539,0x7271f040302013f882070604030201008078406040302010053922490706050309012a9,0x7060535040302019194817261f050302018790723060504020100589494f0714050309015994924100605040309019,0x172605030902018b8,0x200706050403013f2d92028111005040302009,0x71f0605420302012e9390706050302013f2e924071f06050a03012e9070605630a040309019,0x480706050403013f2d9281110040302007a80706050a04036002019070605130a0e0301559,0x33070b040302013f84e0726050403018752907261f05030201872e90706050a040309016b9,0x48070605040301872d9480726050302012e439381107140b050403019,0x1b070605690302012e907060561040302000f9484f17261f05030201928170b050309012a80706050a036002016e9070605130a0360018,0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ae:Jz = tP:=priorEq_sound (by decide +kernel)
set_option maxRecDepth 20000 in
lemma af:btAll (fun bk => ∀ xs ∈ bk, Impossible C 8 xs.toFinset) tP:=refBuckets_all (allCat batchJb (allCat batchJf (allCat batchJj (allCat batchJn (allCat batchJr batchJv)))))
def gi:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249241595ca4651249055571bd9449241555ca2aca251055),(64,0xd09249240316572ca38524402a8761b992492492b3b0dac9),(35,0xa589de4924920259cf0ffd4b11)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JA:∀ ns ∈ gi, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gi (readRouteRows 8 (unpackWords 4 [(16,0x212143218000000)])) (by decide +kernel)))
def gj:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2222137192018944c4d5a4de2f16141112261901e1594a674ce2161211231719),(64,0x91211221171901cc1bd3ae3b96887b3631122115193201451ac19b7c4ee2d361),(64,0x229c28d1d7bc1d76131221071978e1b1912112210119019d441dc1dd1d78a4c1),(38,0x501ef2ca2bf229e5b842c614112126193a84fb)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JB:∀ ns ∈ gj, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gj (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0xb173a18b4c1c931ca741431ca741428b4a18938a49448918a1182cd4a493ce3d),(64,0x8918315958a4e21818b4a71c931c94a1cc4a1cb1891cb4c28d18a1c932c94c18),(64,0x228d491852ca28f4918f11a4918b18d11918a118492cc494e314e11cb1894d22),(64,0xa493a41ca31311ca548a2894e4c9628a18918a4893118b4a3c92e11a128b4919),(64,0xb4c1892122c92f014b494b148a41ca41ca18894b14e4d4c2c9181894f3893134),(64,0x4918c2184a1ce4d3494b1894a4e4a31381cb1cc374b14a1464c14a58938d4894),(16,0x1cc17418a1ce494d)]))) (by decide +kernel)))
def gk:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xba4571d0e3492493d507d894bd291d3ef8b7361ec92893d5),(64,0x8732492492b03748a43a1cd12492560adcaea729b29ead21),(64,0xa123ae30ed319f144944935506e98cb8e64924925606e99e),(64,0xee58e4aa33ccca6875d8c91528948b5d552d86d85128920a),(8,6821986)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JC:∀ ns ∈ gk, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gk (readRouteRows 8 (unpackWords 9 [(64,0x309944823210040c1400000002510894084112884442313810020621908060801084c8012100446180318c040101004c6072180444011428588411280445210108c820240808421b),(41,0x6627004c84d00c1498015268e4421138045001158a8522311484460220868000230994c863128908262128904602)])) (by decide +kernel)))
def gl:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5a68ed5592912f28d908c74e766737315b72ae2ad244c514),(64,0x52fced54a25220aa1192e59ff5f98c33c365a6cd0d969a4c),(64,0xa51291455094867b0cf5632e32deed5a78a436aac9489555),(64,0x2914a2a60515fa2d2758cd95bb38698c948a39530297e7b2),(64,0x7238e12912a286053e334325c7efccd719af37c56ec57559),(28,0xf133d3319a1df1de4326)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JD:∀ ns ∈ gl, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gl (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1061114dd114dd144cd45448b6448909b0284514554e51ba26a30468a24610dd13514234442a9857),(64,0x68691171d826c38b8a86150c699a2ac22e29284a34cd10c242a18a92a4d33455578aa2a18a27a459),(64,0x748570a11138991548d1248530d226a06c02492e921d2454d2450d209acab9241c4593506001b9d1),(64,0x22482c8a83248551151219242b08c8905288a82945c51548d1248941450288d110f8a69046119a46),(60,0x161920ca2184cd26455312441b44d3444d234456298a6298a68bac689c8721c8921a2eb9a25)]))) (by decide +kernel)))
def gm:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf3193f59196432e32d8ae95dce6c6698ed96ae2ac9489715),(64,0xb8dba198e30a4914a2a0cfb986cb1d3a7c64cab25224d503),(64,0xb2c365eeadb43265a1996692255510771f643ffebe57aa74),(64,0xd56476d0ef298b657b7268a99ca4912ba80dd79c74b8df79),(64,0x2d749225450c38f33eca4cffaadb8cad6262441ea2324c6f),(44,0x765cf2c5129105539448ff149cafa6326)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JE:∀ ns ∈ gm, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gm (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1104185053248c2150524852a8aa680a15154d1174897244309889124c8a2282c204c53142b68453),(64,0x845414ba6288a4c89ac190453344530c2267545c88a6174d550ca2220853208618485321a2311053),(64,0x1522a90d4898b5134cd1160e839a46a1a2699a26298a691a8689a66898aa28a46c044111d94432a1),(64,0xab22b54432a2aa4d2a236226294953355284a0d1350d3348d531cc7344d434cd230b2714849548d4),(64,0x344d234485310d234cd1348d130b0515c540ca63b44d616226a9a86986d1348d434c368885538602),(43,0x54148d474c540da22a324a98922544491522691a22c1d04348d3)]))) (by decide +kernel)))
def gn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x571b163494528a058f3fc579dec7fd56dc65362c524893d5),(64,0x3a756dcaf362e61289554541bb4375a7e86ed1f763f6ab6e),(64,0x54cbb196d4ddfb3b5748944b8a1abe36786fbd1d21dec575),(64,0x8ba44a215542b6e76ac522512550e58b686ff4ed0ef62975),(64,0x542ba6772c5225125538d8e78b48b5e77a77b1ff55b7294d),(41,0x5ae721cefe7a3ee72f861c6a44a254)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JF:∀ ns ∈ gn, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gn (readRouteRows 8 (unpackWords 9 [(64,0x31584060501814c662b080c48050f084466471892c2e7c089202090082402a30082a420404014086531d84040601010c463b08084a06118848b0103b8488654080810a620c0d440e),(64,0x3488550412101a02a35103c000505384192115c0f44a3020b7c8080482012653098cc464038180e0632984c6623201c0c0d03088026203b8b0329c08a102a20082a0204030100c64),(31,0x14c6010100404630390c0421010a58209720840c851088982680b80042057481dc244)])) (by decide +kernel)))
def gq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x44a25550198c5e5cbdfd434c32487fae5f14c62e91289595),(64,0xb9dae7f8d7d22512b281e95fe4fd4dc6f3b65ff864cee31d),(64,0xf8ef3b957b61db394c5d22512b2a71d0caa5ca4ea7cace96),(64,0x25105507eeb5495f94996bf1b3ae912893d408de95c6ef15),(64,0x3ae3bd86cb56d0e9699ae56dc73b5748944acabd2c76ae89),(30,0x3d2c32e5d124a24aa0da62)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JG:∀ ns ∈ gq, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gq (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x21c8a21a6693a2522882c22c8a08d409146a0b44a222b245631452698a28b8a2514502a9a222443c),(64,0x298a6350d134cd228ae616452560d354430906d13483088b288aa4152226298a6298a699a4e89c87),(64,0x1a02a1848721c295845414592451190c221d4d513485a4495112d123a0e83a0e8350d134cd2298a6),(64,0x90ed1354d4348d3744d5350d234cd1399060d852284ac8a24609991449117483288a4b0ac5114868),(55,0x521886690dd151228a0991164911656158a4641905394e1d8155250308a1d20ea6a)]))) (by decide +kernel)))
def gr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x97652de97d17955b5fbe1a672894885d5766c74289251055),(64,0xd4d49fde1d2144928a3d535d9b290a24944954cf9ce63f61),(64,0xf62b3436e6492492aaa829f43a428924928ac685ad8ad8e6),(64,0xac924924ac14da1b7144924925608edf1d36375e7c94ce8e),(11,536558182)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JH:∀ ns ∈ gr, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gr (readRouteRows 8 (unpackWords 8 [(64,0x23220a616322242741050a23022908140005616463626423220801280964232224230226071400210341230103610be1852184e12a2207090709060806081700),(7,27399496228)])) (by decide +kernel)))
def gt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x921f0ce512912aaabd8becbde72fa9924871a67289488396),(64,0xb167a732491735f48944a8a9ab5c8cf1490fbd1de65b5e64),(64,0x5719373e43bd8b6bcc9245e1b1124a21554e37c30f98df4f),(64,0x38f9a2b6e57aa7624925651cba295736224944158e5bc73c),(64,0xcb3f9924a2ce556b219a32492482a84efce6cfda8dfb29e5),(24,0x310323f72c64b575ad)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JI:∀ ns ∈ gt, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gt (readRouteRows 8 (unpackWords 9 [(64,0x3a84502410894522101190c26203304c66208884044102c8508281099882666089c840104a8d4412308284205308214223139844c2930808c661721882421120044a23010180208),(57,0x22030084803708880e02408081241010204a100000488276200882e9808a302030300c0c830300c0de1155841681010140405410140405708084605308900081)])) (by decide +kernel)))
def gu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf8cd0a249441541d7f3b78a691e577abcd8ecac64a249395),(64,0xdb63afefcf1e37c3b1c7e64a24839632c91585128920aaa5),(64,0xf9924924954c32cb8ef4a25124954c52fc76e5124a24aa61),(29,0x5af86ee8924924aa16bb3)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JJ:∀ ns ∈ gu, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gu (readRouteRows 8 (varNats 3 (unpackWords 4 [(44,0x1cd4a4936547005cb4928a491ca494d7474e491c)]))) (by decide +kernel)))
def gv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe632492492b03748f631924924958192fce4329e49249256),(64,0x97e7213792492495827f1ba45bdcff36b2512498a8374865),(64,0x66ac627fa9bc3b6739b5924a29aa0dd22d8d8c924924ac0c),(38,0xc4119647657343a7cb2d4dac9251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JK:∀ ns ∈ gv, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gv (readRouteRows 8 (unpackWords 9 [(47,0x8408023080c04050300842080383086a141005844321185040102984082107000010121014884121184c441218844662068000000)])) (by decide +kernel)))
def gw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd8ecf9b5928924c581db653ecfdddf9f1db3e6d64a249355),(64,0xf23a6f38e24920c542accd3e52b38c44a25aa0edb29f674e),(64,0x7fa666f21931f9aa6248a3d4066ff2bce30924924ac99c66),(64,0x50c08fc6476ccf4b4fb21f3d66c9e3bdaa7128a5543028fc),(53,0x1903b7c3649d2d8c8ff46e3eece6b0c6b984a296)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JL:∀ ns ∈ gw, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gw (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x14c5122a219482a912229065124c232446688a42887aa88a4428ca1e48934451511224a9854444cb),(64,0x99a46894c530a400924e88c520924289a42a0c2290a2a91a2698452184520d8415489308c23088d1),(64,0x34cd2244560985740b4e8ba828ba61c45541244a9890217a2690611384d2350d3349911542691a86),(64,0xa84a2b1c7115451355d41543698a52155915502b0aa615222549ca689a8699a4488ae12a0c5344d4),(64,0x53a82a865215a615b22aa05815482b444c8320d1350921584699222b04a729cd1350921544699222),(5,1350180)]))) (by decide +kernel)))
def gx:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0xaa44210422080292cb8288d241042208029006b63c879f93f4113f318c9fb3492151241042208568),(64,0x272e4fe83a3b441088213a00ad8b1a14364dc05130c8208441091201f60390d6210422084291ee83),(64,0xa485ab8bda0d85449041088207245e14326817a6f1e622c2c490e8649c22081270163910f44b12fe),(23,0x209f908b2a8841c6841ccc5ec3b81)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JM:∀ ns ∈ gx, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gx (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x45324b54991350d21443ec1a24c8a1114ce299cd4348d37445530aa6350d215583744a361853),(64,0xa445308ca328ca329a4e88c5428b220aa448882308c4488c51184ae886520b24288a469861135039),(64,0x348d121485344d3348d120ac50ec5114dd113222ba241f44920ea2a9050194454090c4310c431a41),(64,0xa22229a224aa221b499a2489309a6c88d8e1a4e938d6d1a0c8307e688d2e9890690f5131cc7344d3),(5,6955556)]))) (by decide +kernel)))
def gy:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa67fb2f8f5d22512b2ae526a7ef86c98c98cbd53112883d4),(64,0x9d4735cadb8cb574894498a07eb9e3bea3ae3be5f19747b4),(64,0xb2275c462442aa036f95cdb39af36ff9fc7ae91289315077),(64,0xf2c7e4ab5f97fe1b4ea8c2512aa872fa39979e28f7dcd46e),(64,0x6eda186f4912892a9bafc8de92251055714f6a5e432396b)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JN:∀ ns ∈ gy, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gy (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x118461185214d5424c58906d1348d1248308a24889a4711a8699a4e89242a88d434cd2744a62983c),(64,0x10c9144d9154c431122893228907089a2229a2290a51112a28a3a22d13015865129ca729ca715446),(64,0x14951148d1248d1151121459234492088a891222286530ca21c083c8865414a2ca0aa1b44a88a243),(64,0x98aa328ac71c0d375836a07521ca26a9a66b1a869244689aa699ac6a1242b88d13a0e80e51114911),(64,0x1922ea0521b445690aa184d511a913320c8320c8350911582691262b0ca729ca729cd42445509a44),(2,0)]))) (by decide +kernel)))
def gz:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0xa83e4838c8a795d83016202ad831207222042208509600815e8da14c55d0ab66903930422088e8),(64,0x161ec30821085680070d90602c4055b2c81c88a1104254084409075f0af1276c2e87222042208108),(64,0xe17b523f418061f6c8f00cfa5f4964710410846a4103dd12b57d1f10c2418545a90ab746851f0bda),(64,0x16e02d6489f0842b2072e1e41a48b1996b60d8320ec821042103525fd0327b082104210052650075)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JO:∀ ns ∈ gz, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gz (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xb4521b4c36906a288a468aa61d5451758588a02914a22a04d434cd50d222904d234cd574442a1c3b),(64,0x886d5744580e26288a92344d6350d5394d33487a88644b04960865441a85095112491175c514aa41),(64,0xdaa2360a1331cc7344d5350d230b0734c3f1444ea06d555195544d217a2615a23d4c92934510ca82),(64,0x68a2b345520b0d144d11350a729cd22445509a65158e688b8152a2aa87540fa484a12689aa6a1a44),(64,0x24512145122649232ccb16114144aa2a8570f002a29d24ba82aba2294cd4320c834891158269aa81),(14,0x511846688cd16922c)]))) (by decide +kernel)))
def gA:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb1aae5c1b2a221121171941ac924b8287b81c8b1c8e2a1bda2d5e61111111918),(64,0x1111011911ea41aa42c9c198f7f1aae6b1b2a222111118190222ffa2fff1e8c1),(64,0x9019b962d9e2f9b1afc2c1b9d198c49b2aac1a82f2f222112111b191a82f2221),(64,0x1a1842059a58f1eae19a9283ae28881b61c241121371942eca3e22211111111),(45,0x5ae1ea2adb49c49948c2bee2bdd1b9c19ae283d611111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JP:∀ ns ∈ gA, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gA (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xa0753344550c2264190641906a1a6488ac11643892a2252245394e5394e6a1a6488aa128ac73485b),(64,0x15c55244521609112a2248a42b0a81b92224451214454344d34444a88a42a922240ae2b064292a2e),(64,0x59a26098d131a28a8a2350d4298a42a304c144e93a457220881505202246888511485114cd114851),(64,0x74442a14d10f4d6086163548aa92428924a89aea892488902809284a85468a432986520e80288891),(46,0x5164d4e9a22eb06111603888a87150e6a1a6c89322c445228a45348d3)]))) (by decide +kernel)))
def gB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x37e98dfa75248659229922494418a9bfd86432b871249055),(64,0xfa1d69972f219248eae66311289395075971933c89449255),(64,0xb8afb1bb732490e34cc92251072c6ec643e98892482aa50e),(64,0x86649128a51506df31d36eff914d21b623ea489449aaad21),(40,0x303b7e7f55a673e56ca6476e32490f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JQ:∀ ns ∈ gB, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gB (readRouteRows 8 (unpackWords 9 [(64,0x1089042657100404063098802020310882020328d421810990ca230300444070000484610120404814209802852099582020081cc40103885c6e20b8038443408910222125041000),(31,0x204140133010c20500814c2023089c502670888880104b84122191c8832a210808c2e2)])) (by decide +kernel)))
def gC:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x8839e2f929d1fbc2962f2221121061a02ba2af68e283ae28882e2a2231211618),(64,0xae1ec22211211518404e3e19c81ec7fb281a8819ae2d293d6111112181918c1b),(64,0x3be6bf1ebc7db2bae318b611111018182f9e1ec222111110119426b86ad6ce2b),(62,0x2fa49c3d281a8819ae3b1b3d71111161801dba658223111111192398e2e89)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JR:∀ ns ∈ gC, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gC (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x92a21b4ca1c4541b483334494148c115467545142871114836888965503489c5138a511e263f4830),(64,0xaa248a8ed170155145d50fa21d51511185230692445121ca63d45e125111750c691d957605149228),(56,0x744926444628716162277447298a83a449293802899d70c222b06131443890bd416030)]))) (by decide +kernel)))
def gD:List NodeSpec:=readDeltaNodes 8 (varNats 5 (unpackWords 6 [(64,0x81004249d051047b81b14b60737460410410401c80889082af26009ae026e15e40f52e61b14b6590746041041040389),(64,0x4204110a07288e064f419fa49208104104204010943f46e4795360b748204104108100424e4790a04b6242802041041),(61,0x311b11b51e91f41dee35704b0410420011890403d64c1dbc0e904904204108008424233e46c382f1c492081041)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JS:∀ ns ∈ gD, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gD (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x34cd474462a9cd10e0d11b22898a48992a89b22ca1224904d24444e6092a4a9161444d5890741c51),(64,0x24851548308aa68644d22224a9b241149114845324432a3ac1844520e22490aa2354d47447c90a62),(64,0x912251499309462089d418822188220ec94148511948644593144532485114914090348ad13650d1),(53,0x291c91158d27503091a8289d55244525443298a2293a2292a21a0c41248d330a22)]))) (by decide +kernel)))
def gE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x90de5724a04aa7c9b1f8de5724a00aa77fe198aa49250056),(64,0x563149a39a63679563d4b21b34c643a2e49240515067b72),(64,0x3d62492402b033db948653d724920958f9f432194f5c9248),(33,0x1f658ff3d62492402b1f658e5)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JT:∀ ns ∈ gE, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gE (readRouteRows 8 (unpackWords 8 [(29,0x4162210306210543240201084322c123020123078315000000)])) (by decide +kernel)))
def gF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x90d98e8ab24904e54df8fea92492402b1bf1915249248056),(64,0xc64ee42892426a83bdb8fb152892412a853d314f155273ee),(64,0xb21e7ce512480550f9d4fbf63ee54a24905aa42b32f29f7e),(28,0x3ecd8c87455124900ac7d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JU:∀ ns ∈ gF, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gF (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x92189214a492390572491ca18d4f218918a1ce2cb1cc2494a38974e4b3cc2d00),(64,0x41414a3c94a4924892189214a4923921249518941894a18941894b2894a49218),(15,582823447937481)]))) (by decide +kernel)))
def gG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd4dfb446fdf9fa78a75f1251211ca83bfd14322a89248256),(64,0xab1faf86dabe2492482a83f5d0d87c24924825620edae3b5),(64,0xe745c924806aa94f127fe3a6e8ddee524c6e321d17249202),(64,0xd3ceec8a53e5b0e3a2a8924826aca786cf63b7776eca499c),(32,0x327b8e9d524924805606edf1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JV:∀ ns ∈ gG, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gG (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x2497462351c0054e14b1814a7189728c4b21894b4a1c94b4a28c4918b4a49380),(53,0x213413562161b18a1cd1ca118b4c523c92ca1cb24c91d4931819)]))) (by decide +kernel)))
def gH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x448055476df1d94b8cf15249248062c64f71f95249248056),(64,0x90d971f96d959f9914e67fb25cc78c4496aaa7fbb199fe49),(64,0x72fe6fdb299f3322484b287cfb1913e6644900aa72c1d98f),(64,0x56dca67de3112422a98163b4b5cd639a573ccae8fcb4d9f6),(59,0x6ddf236f94d93e3f7a645a48adb9489f3322480a2a60)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JW:∀ ns ∈ gH, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gH (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x887a025c30b2b2893aa493222544d85443299a220a824c8584344970acd10ca41d80220888310500),(64,0x88713386110da460c221880896494e907d33a0e8350d234c22e07d1298a6350d234ca2b991116c5e),(22,0x114444524449544452145120d304)]))) (by decide +kernel)))
def gI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x994de29ed57e8b53d43224492b2a6037ed95efbc62248455),(64,0xea19912425d55e6ca67cc8912402a830ccfef8e53786cf5d),(64,0x20954c0663b698ed2d4e698c8ecd0cb7752ea6cfb2f36531),(64,0x925877b9f98db23b4ed8e2a191224847ac1493c5fbe64489),(64,0x93e323b719248aa33244a2d4554b2439532128920158c0f1),(22,0x980efb197c46dbfb)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JX:∀ ns ∈ gI, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gI (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x14da5394ec1b1429b03e0046488a46d0c9128a24928515a2448924149c244482259a225850608a00),(64,0x912a150a260a551592414ba6e9078019051284c1489283a1a04aa24990911502434552320c868dab),(24,0x2149430611158d23448690b02baa22)]))) (by decide +kernel)))
def gJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x912951240715541b7ccf6f4dd739af36ff9ca8fa9224a355),(64,0xe8924825573c3f5895ca2dbe76f36dc7ccfd95c922b6e371),(64,0x2128aac11dee8b19275d6b63fd4c7f449251ca852e98e94f),(64,0x874a7d4892492a9811b7ee8dd2c4a5f95bfaf363b287f489),(64,0x44900d58e26fbba325b9f9f1fb756dc723fa44908e542966),(27,0x61db64a6d8ed8ec723fa)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JY:∀ ns ∈ gJ, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gJ (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x19a4334911258914310c16914148eb3ac59454520ed5208a8a98a42892418544614d1111c5214430),(64,0x90a2290a22b288a160511552348ae28860290a64544523891111c56384920a0550c4048889124862),(39,0x128289483118d1648513485624453154687445419dd178034)]))) (by decide +kernel)))
def gK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3a1e892480560b5994c7f4492412a852cd0eb4fa91249255),(64,0x7ed865ba3d0f3a244904f54cf6e5f9d0f4492402b19edca6),(64,0x3ce88924a315067b7299437a2492095823347f48b4f0eba7),(64,0x6ed7196454e9f3fd4c79d11249462cb046fde29b63b63a5),(2,22)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JZ:∀ ns ∈ gK, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gK (readRouteRows 8 (unpackWords 8 [(50,0x12261230504212506092102416201224182a142010524014261062312006103012342082722254461a24661220f00000000)])) (by decide +kernel)))
def gL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc7650f3a244909ac6046ebfa7fecfcf8ed943ce891242395),(64,0x3a6b0dd774b7d15bf2d32b6e32198fe91242555302536c76),(64,0xd0fe8924a39553690ea4924900aa64f7287f2512402a9812),(64,0xcb3b2ab6e7a9ca63fa2492cc5952f646fb31d3ad32b6e7aa),(47,0x60476ddfb71db1c7650fe91242316548325)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ka:∀ ns ∈ gL, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gL (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x918e1894d1b1584b4c1a14f4b2d2c9534256ca494a4c184e289184b74d28971d),(64,0x4d16571b491ca4e4a1894b4a28b174d4a4e1c9184c28001cb211ca1cb5914a1c),(20,0x49249264531811ca3141)]))) (by decide +kernel)))
def gM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb0fe7524924a31553691e84924900aaa6d73b8fe4a248055),(64,0x7cfe752492493165ccbec32c91f7a124924355079fd3b32c),(64,0x9e9fd124900aa6031fb71db291e3a92892135818fdb9e37c),(28,0x3a7f1588925100aa64de1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kb:∀ ns ∈ gM, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gM (readRouteRows 8 (unpackWords 8 [(37,0x410302050405422104032505c182412341e223620884230281020102060105010b0000)])) (by decide +kernel)))
def gN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x25147ac6048c4759e3f29b6fa67f22efdf15e7544928a595),(64,0x91c5622494498b181186dd21b74a75b629a4364321bcea89),(64,0x972d3637636ebce9ec5adca4722251251ca85a43a78f1be1),(64,0xbd124a20154d3028b486edcfaf490c864722251259ab1a61),(64,0x77c76ecbabc944900d542fe678df0e3a9d4924925aca6d23),(8,4615090)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kc:∀ ns ∈ gN, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gN (readRouteRows 8 (unpackWords 8 [(64,0x16205030406212807092123242225228122078102084102072610212322210504064164062302250907080981044124612a29212528a122230c010b41272613),(12,0xa24321232225e124e1090000)])) (by decide +kernel)))
def gO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x241ca9d64ca5c4924900aa6031fb73c6f8bbc75251242316),(64,0x62a77fa3875249248056494bee3e7b57d54b6e3af3e1249),(64,0xd798fdb8ed8f8cea49249462c61975ea4ff1db1f0f849249),(64,0x8a56492128a164188ed6a9b658ef345799e144920c39541f),(44,0x38a9b6535a7590eb69d763a6abab2586f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kd:∀ ns ∈ gO, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gO (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x3152691a2291a229a2848926288a4288a4c0224288891118d1248551445424493145c024823218a6),(64,0x99a4911a83158e49443d34c9714d012486708a42899417482548a2290441148243843c4448218462),(34,0x55148d5149150e282b20c5358d2508d416a2338ca6)]))) (by decide +kernel)))
def gP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc76951d663a7eac9b1fb9449209ca03bdb8df14a51248255),(64,0x9ca24900aa1594c3afa7690ebea8ac931bb294a24904f541),(64,0xb4ed31f77ccfd8a24904e542b248a9f3944920955592450f),(64,0xc512482628123b787694eb6288fbe447ee512482a2a123a1),(22,0x1dae50edbab2fc7f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ke:∀ ns ∈ gP, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gP (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x444d46800eb2a66bba8e8ba4caa1d2492c4a9a41a4c5220830a1a62a445411192388934487e88660),(64,0xc264a2264945a289241349150cb0220c4320c8eb8869110641bac1c085139a2898a260c246a8452),(20,0x148a1b4832a3a4e99a82d4492)]))) (by decide +kernel)))
def gQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24920e55434cbb2db196ec6793b33633790e88d84928a3d5),(64,0x53686eabe2492482563f7d8db65335f91f26aacde1baaf89),(64,0x96c894b3d71d567d8dd89249219ea9fae8e43e12492402b0),(64,0xab07159bc78cf0924920a5898159bc5e2f89249219589812),(37,0x3f6e7968a7fd5f61bd43a9249241)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kf:∀ ns ∈ gQ, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gQ (readRouteRows 8 (unpackWords 8 [(64,0x428327262a05040504296127260801281200000461626123024123222126212322212423022405140201620182262722254466a2414241020941020822a3a117),(11,0x4403020105010600006766)])) (by decide +kernel)))
def gR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xcef50e8c92402aab6e37f5f124924154cb24597c49249055),(64,0xf3192d7f2b6e3a450e8c9249aa033db94aa9bd92482555bd),(64,0x8c92422a84a3de23bdd1cbd5b73fd4aa1d192493d50ef877),(38,0x196487a87464920954c065921e4e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kg:∀ ns ∈ gR, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gR (readRouteRows 8 (unpackWords 9 [(57,0x3054a01510940465908100e04038901001040884a2101818060611860c323b108dc406d0a08c2633118646a250c08c26331184080502014c219000000000)])) (by decide +kernel)))
def gS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb72f1199124a20e58c9ee3d485124805537e3cea51248055),(64,0xde63b7e7490dfe9b7fcfc362249451caaba2b6ade3f32b56),(64,0x249449cb23bc4f6916d1c9399fec6ba664492883d621fda1),(64,0xaadb8dcb64512482a987fb9cf8ef6f334d0da67fb1bcf332),(21,0x2b6e572d9144920a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kh:∀ ns ∈ gS, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gS (readRouteRows 8 (unpackWords 8 [(49,0x6145232602040707610304020705060108a2c1252261262221446281c4084102076361120206216324022521080000)])) (by decide +kernel)))
def gT:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0x670c2e44688021068476a0dfd95a311d6e13340c384789c1920018d602fd899a170b911a221834),(64,0x23440220342003386031d11a201041a068017f018d6c197e81d2e44688860d1402678b9344020832),(35,0x1dda0fb83d03c5d1a2008c1a2009d707837e81cf170)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ki:∀ ns ∈ gT, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gT (readRouteRows 8 (unpackWords 7 [(45,0x2081850c103000308181080428700012624a8d101108d101c98d1254c8c1210e4e161080c285)])) (by decide +kernel)))
def gU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xaca6bf1f329719a3fc924920358c0aeb61d3a249248456),(64,0x241555260377b0ed32b3426ea492490dacae972d5fe49249),(64,0xd2f5668f1ba92492436b1a94db47129bee8d4aeda1d79249),(60,0xaed31dccf09249209582bb5875a8924920958980e9b1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kj:∀ ns ∈ gU, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gU (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x496315214181ca1c974744a495a4a494c65652cb1d84a1593982e12361547000),(2,0)]))) (by decide +kernel)))
def gV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb9f5d5e4a2480d649256ecffb8ddbbf7c529c75449288516),(64,0x555dee3a5249248055314464f72e7294944900c591da5327),(64,0x972d6c5fb98944900f54dfff474923f95b71931fc944900d),(64,0xd8e361d1924805532c90ce752892402aa3e6b8e9fd46dfa3),(3,237)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kk:∀ ns ∈ gV, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gV (readRouteRows 8 (unpackWords 8 [(38,0x222607812405812301820a2142a1c2412405412302410b00000081070602050403012809)])) (by decide +kernel)))
def gW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3162c238c5eec77f32c763d12490cd58cb24355e51248055),(64,0xd8efe652aca5449242356301cacb1597abefc6aca5449242),(64,0x24d599064d16327eb5b1dab192924a2cc54c0adcaceafca7),(64,0x5a68ff3b2bc92492cc581936c77f94bb3c6f8ff5a1d49249),(58,0xc06cf0e9343a5fd4dec39ee49249462ac83268b1927)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kl:∀ ns ∈ gW, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gW (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x918a1354662cb22c974516151a4935434a74e184941253651849546375826190),(34,0x494b428a51228962491b18934a14e54171)]))) (by decide +kernel)))
def gX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8a9fcea49249462c603678e99ff33dca6f62af424924a355),(64,0x2492480d6303f7678df0ecf1d4944909ac83f7679fd39964),(64,0x249052c15bae565d55da43265792492416b1f3fca4c6290f),(64,0x4c5990f3fad32c98d36abc92492dac1597557690c9d5e49),(33,0x52ecbe876b62971f55e49249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Km:∀ ns ∈ gX, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gX (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x14d4c161801432152121351ca1354518b214614d72894c4d4b4a49648972491b),(11,3659619470098)]))) (by decide +kernel)))
def gY:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0x279a2008c1a0ad81c11b8211880642f124d10141a32f83c88d10041901b2c0f0da1384f344011834),(64,0xa39a200141a06b40d6c19c38da37c4688080c80d8e071c0f0da1344f3440120340333834e8187032),(28,0x6fe04a39a200041a069c0d3818538185102)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kn:∀ ns ∈ gY, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gY (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x154373c92189418a4938b4a2c91913124495724924312718b54215014b214327),(4,530)]))) (by decide +kernel)))
def gZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24a04c5969343e3e4924900ac0d3ee916d62561e492492d6),(64,0x24920b59696e316e4924900ac15d3c5265a4bd693c52b3c9),(64,0x2492404b1f3fca4c61d71e4924901ac0cb15b3e52e33adc9),(54,0x15cb5ca79e2931876e792492403565a5b8c3b55b9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ko:∀ ns ∈ gZ, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound gZ (readRouteRows 8 (varNats 3 (unpackWords 4 [(40,0x212143570212135249243502315415704a449435)]))) (by decide +kernel)))
def hA:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 3 (unpackWords 4 [(64,0x9a781f262c01cc849c485e1d20242c06fe845e1d20222c04edc5c28a1d20222c),(64,0xc79fa7e98583ba1d202182c183edc3ac6c2e78224520062c268dc1fb83ac1fe1),(54,0x48ae1db82cd818e681f262a79fa7e981ba3ba1d20042c01fc19b9)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kp:∀ ns ∈ hA, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hA (readRouteRows 8 (varNats 3 (unpackWords 4 [(46,0x4a1894a3894a4118a31894a1b04c532150289234a45000)]))) (by decide +kernel)))
def hB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9f3b565a9d0925129664199fb8c96ad6c76b9ce84928b315),(64,0x3757ce849249662c0cb2c7f58e9db1d793a12492498b054e),(64,0x4d6301b3c32df0cb24394e7424924a6b320c9a2cb7dccb24),(64,0xb4ec65921cf9d0924928e599367865be19648aa90e849249),(52,0x303fa732c90daf9d09249292c60366f0c9a2cbd)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kq:∀ ns ∈ hB, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hB (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x5628a3141561c934a495654171a18921435604a2892ca494a3c9351745161528),(29,0x4a4e4c4b1c9264f51581b28a3141)]))) (by decide +kernel)))
def hC:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0x840b0eaa9017a23860322864608421089e902ab40c9c93042108421490049e1e80c021104210082a),(64,0xc6078c168a68646084210888929fff11b321f78a0fcc108421091050139d61886bf0441067e3f265),(64,0x846b48803fc0528168a107a6084210886915a0a806825e036d9210618a191821084203a8a50eb22),(39,0xc40148d5d085a3e19e36e28ed856d9f1555a450dc3230421)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kr:∀ ns ∈ hC, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hC (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x4445534514444544454d5352c4b051258218aa2340d0370dc183c301485114c4711c4b12c5217400),(64,0x44828918530ca21b8a222445209042f4455644541886890c431ea2554c4312262189910c241f0495),(64,0x9a41114920da6394435150511122898ac1148572a8448a242889d1149110f241248222924184c54),(64,0x44caac1d475256958c91285ac887543058c88d9170a81f4c551122890a21d49d1149110e24111092),(16,0x32a4a8b891148a691958)]))) (by decide +kernel)))
def hD:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0x2944255243c5cb6ea3b6547eacc09a164c10842112100273c3c751db0f1f242010d83238421084a8),(64,0x2f6c6d072920821104022a55bb1f0920821084200a4c5cf0bc6545fb0bf32dfc3b906f08441004c9),(64,0x68821104012a4058d472d0e572dfc91d5a2084410048902b7a2486d108210802148c01e54b0b1a3d),(17,0x17f058d51644cb7f16e7)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ks:∀ ns ∈ hD, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hD (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xe222c4c5150a29142294447a9078e892a1c443092a24a0a51312267445e987d1148388aa64d4831),(64,0x3380888891548562444688891154d3444543449209c5314434422a7454d2150c2a18862188621852),(64,0x98a261549124853145ca91a26a22221449214d512924298a2d007521444c88a829985554452244e1),(13,0x69328289a8c89a42)]))) (by decide +kernel)))
def hE:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xdb2f1dfa18b5e71d211111451a642c9b248e819cb6b81dca1e971d2111112619),(64,0x3c2a71d211210241a301bbe7af22b9e1fad29882a71d21121026196220182c85),(64,0x4311110011906c72d4311110111901b8a1c83c43111111181c03aa39c18dc1da),(47,0x28049e922cda2d8b3dfe1dca1cc4396111112619298873c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kt:∀ ns ∈ hE, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hE (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1505338aa289cd1404e180a2499487148c13050961244999111b222a922290a68888e69205535031),(59,0x322290653144563ba26a9222344d214cd640aaaa062000094144462146734592144d230611)]))) (by decide +kernel)))
def hF:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0xc405a2590f11834216f81768fac9f8c12c60c4480d006c1bc80c4419064036e8c0f87271c4020832),(64,0xd208b120320d0998131044784851584f0bc41162506419ef0185030e0f01b344001834222103f2c8),(37,0x372088f090a2b0ac1608324480c0088f07dc0b8ac0e83)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ku:∀ ns ∈ hF, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hF (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x24513350368add23445415452444428924a986d232a2d08822184472444288c8510a23150a209c00),(41,0xa906542459208a8e8943a90b131f244c45869b2428924488a65)]))) (by decide +kernel)))
def hH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb62d0c64920154c3bef1690d8bca64921bd7331889249356),(64,0x8c9241543f7c54fe6324904aa1fbe194de6324904aaaf961),(64,0xca9a0e9e3b7e5bd8b4d1fcbe3612492518b1d76c75c6e331),(64,0xd1fc4c949249292ca5f61d34e8dbe2bae5ad8af361249241),(12,13991606452)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kv:∀ ns ∈ hH, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hH (readRouteRows 8 (varNats 3 (unpackWords 4 [(46,0x18d4e2c928a4c3c94b7494c31526700001c9254136118)]))) (by decide +kernel)))
def hI:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0xd0ded27f45c856161a2420340239c65e81e2f0cf285878901a208385179e165c2f052449a221834),(64,0xa0b0711040118340e087ad998a0876270e2208023068800b381703187184f0b0d110c1a210400a30),(63,0x2083a58d2a27300d070c0ac2b3c445068240b38170318703226058688860d00ed4190b0633c0ec2)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kw:∀ ns ∈ hI, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hI (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0x51417494a13454931425494a3415171894b4a157641181a18a13455493254496),(18,0x345249276341a494a3)]))) (by decide +kernel)))
def hJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc6d339b092492dac6207eb96bf2c74b0d98ce6c24924b316),(64,0x2d6066f94bb1f7687752e322bc9249209ab1883cb5deade6),(64,0x974325ceedccff65173612892018b038f876c67aaf249248),(64,0xe6736128920a5883ac3aff8ef22d6e5e9b79b0924928c58c),(64,0x57a9b48ad94c8ac914cafb0df97a6c649201eaa3b4e64fa2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kx:∀ ns ∈ hJ, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hJ (readRouteRows 8 (varNats 3 (unpackWords 4 [(64,0xc018a314189657289218c1351312146349264157189312146518143249257619),(34,0x38f3ce4c938c2ca3893cb1cd1894c118b1)]))) (by decide +kernel)))
def hK:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0x8b73242892402aab6e7faf0a24900aa7fb61b57851248055),(64,0xd14875e49249092c6cf73bec53ec6f86d866ec924031457d),(64,0xdbc53e249248262a79316db672446ea492490d2cb23a5eac),(17,430792007811029)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ky:∀ ns ∈ hK, Impossible C 9 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J af (by rw [← ae]; exact (checkNodesRoute_sound hK (readRouteRows 7 (varNats 4 (unpackWords 5 [(61,0x699a2690a628aa851144298a2292262886140c00025a26906d11485489a4e88c832135160000)]))) (by decide +kernel)))
def tQ:BT (List (List Nat)):=refBuckets E [gi,gj,gk,gl,gm,gn,gq,gr,gt,gu,gv,gw,gx,gy,gz,gA,gB,gC,gD,gE,gF,gG,gH,gI,gJ,gK,gL,gM,gN,gO,gP,gQ,gR,gS,gT,gU,gV,gW,gX,gY,gZ,hA,hB,hC,hD,hE,hF,hH,hI,hJ,hK] #[0x18a1570d404102301b,0x18d11110e0b000b,0x14e1441430f90bf09208b06e01c,0x10a1040fc0e307e075022007,0x1421130df0d90c5081048030016,5251674187,27628065529927,0x18013a132118021,0x1731660fb0d70c30a308f06505d03d001,0x18114b12e0f30c609104d045025,25292895473673,0x18312612310f08d,0x18c1270c00b405904603f03901d,76578996154175539,0x19117a15011c0ed07a,99375857021927522,0x19316d15e14011e0cf0cb07d012,0x16c16816312b0da0d30b3097089013,0x17116711b0ff0f1086,0x17b16f1250f50e10a1098029018,0x1200e40ae08e068060,0x1971940ec07202c,0x13c10709d06d06a019,0x1581520fe0c809507f06f06b017,0x16a0ca07006c049027,0x18818517713f124,0x1300ef0e905c05102b,0x18417d1190fd0ce0b60ad01e015,0x14d1221060d20c40ab05e058,1167488,0x1381090b505f054014,14,0x1791761651150eb0ea0e2090043,0x1451361020e60d5066042,98258132802977798,0x1370db0c20ba08a024010004,0x17e14a13e0d60cc0bb084052026,0x18b13108c05b055020,0x19618718217215c1210e00aa09e08501f,5973159986,27012140240942,23023105298444,6796185869,716876,0x1170b704f03402800d,4161650746,0x16e12f11f0b80a708302d,0x17412809c07905601a,0x1480ee0e70d80a005a037,0x16b1601331290f40a406704a03b00a003,0x1551140f004003802f011,0x15111a0c70bc0a50a209f08807407102a008005,93468800125304951,823350,18833432584260,26324039721108,0x17c16913b12c10c1050fa0e80d10bd0b90b10a8093057053,0x18f15f12a0de078076,0x1861751350be099002,0x18e16214610809b08703e031,0x19015a1490b206400f,0x15b15615314713d10107b,25843691315354,1232976]
def Kz:BT (List (List Nat)):=fastPrior E #[0x1b070605040302012e43a34071f0605040302012ea07260605030201002e9221d280706050a030901a072614050a0e030901948070605130a0309019,0x1b07260605030201002ea0706056204030902018ea22391b07060504030901a07107306050403020100a28071005130a0309019,0x88740706050403020100a07360605040302010032a11070605040e03020032a1d1b07060535040301920170726060503020100a280b05040302015b839284e0b0504030201939240b050403090184828070605130a03019,0x7270604030201002e94807271e0403020100907230605040302010053a4939070605040309012da070b050403090201299174e260b050302018070605130a030155820070605040302080100a,0x7060504160302010032a07060562040309020100a0726730504030201009072606055c03020100948072605030201002e92838170b05040302019480706050a04030152907181405040e03090190706050a04090201589,0x706050403020100542ea4907140b050403090190706050a030902012e9,0x330706720403020100920280710050403020100a070b0605040309012d90706050a04030201529,0x49480706050403020187a07060542040309020192048070605040302013fa070605616f0403020100a48071f0605130a03019,0x70b060504030208012ea170714050302010059907060535040302018e00a484e0726050403020187a072605040302010087928071004030201007a93339070b0403090201907140b0535040e030193811070b060504030201a0706050a0403096a0201a1c07140b05040308019,0x48070605040302018759a071e060504030201002ea20480706050403020187a8228070604030201009072605040309020187928384e0b050403020190706050a04030975019491d2807060504030901a1d0726050a0309018,0x28240b05040302018c9078184060403020100907261f05030201005e91107100605130a03099,0x1b07060504030201872ea39070605036802010093928070605030201002ea3349070604030902019070b050403097f02019,0x7060504030201007b2ea33200706040302010091d1b0726050403090191b28172605030902019071f06050a0302012e9284f1f050403020180706050a040360090201a220706050a040309019070605130a0309014d9,0x330706040309020159907271f04030201005e9820784060403020100907140b050403015b81d071805040309018,0x334807060403020100933070b0403020100879071f06054204030201907060561040360020100a07230605040302013f91b07260504030901529,0x331d340b040302018204e070605040302013fa280726050309020159907060535040302018a9381707140b050403019,0x70672040302010047907270b04030201878221d28340b0504030201a070605040e0302010030a0706050403600201006ea07261f050403020187948072605040e03020100a2239070b05040309019284e10050a040302019,0x491b071405040301002da1b071405720403010091b1714050403010052937280705040302010032a07060504030201003f94838072605030201009070646050402010058911071006040302007a9331d070b04030901848280710050a04030201a,0x3339240b040302010094907140504030100529070646056f0403020100a07060561040302010053a2807840604030201009221d28070b0504030901a,0x3322070b0403020100907270b04030201002e9072606050368020100907068304030201007a9224907060504030901920071006050403020100a281110053504030200939280714050a0309019070605130a030901539,0x706050403020100536ea390706050309020159928100504030201005b94e0b0504030201518384e07140b0504030191b171405040309018,0x70605950403020100907a6040302010052820072c06050403020100a3928240b0504030901949071405040309018,0x3707060504030201002ea2007271f0403020100928381710050403020100a1724260b050309018491b07140504030901928071f05130a03018,0x71f0605040302012e43a48071f06050403018752a07060561350403020100a4828072605030201002ea1b070605040309012d91d28170b050403090192224070b05040309019071405040309015980706050a030902015e9,0x491b071405040302018ca48072605040302010092207260b050403090191b07140504030901599480706050a0302012e917071814050309018,0x1b07060504030208012ea4948070605040301002da28070b054204030201920070605040e03020100a0706050403680201009,0x480706054204030201907060403020100537a92039070605030201002ea28110b05350403020194f071f0605040e030201a284f1405040309018,0x481b0706054204030201a331d070b040302019990706050403090201006ca07060561040302010094807261e050403020100a4817260503020100828384e10050403020100a071f0605130a0e03019071006050a0403020156a,0x4807230605030201002ea3948070605030201002ea4807271f040302018794807261f05030201002ea480726050403020187937072306050403020100a1707140b05350301848071f06050a04030152a,0x7060504030201006e928380b05040302018,0x4b07060504030201002ea20072706040302010092838172605030201009174e140b050403018071f06050a0302015e948071006050a04030201a,0x71e0605130a0309019,0x1d28070b05040302013fa39070b050403020187907140b05040301002d9070605626f0403090201a07230605040302018a9070605040302018d00922493907060504030901a33284e0b0403020181d28071805040309019,0x45070605040302010032a07060504030201002e71a0706053504030201949070605040309400100920070605040302010091b071405350403018391d0706050a0309019,0x1d340b05040302012a9071f060504030201872ea0706050a770309020190706050a0403096a0191c07261405030801009,0x48070605040302012e43a20070605040302013f928384e26050302010094f1707261f050302019223928070b0504030901a4e072614050a03018282410050a04030901920070b06050403020801a,0x491b0706050403020187a20071e06050403020100a07060504030902017894e07260504030201879072605040e0302010055a48170726050302010091d28070b05350403019480706050a040e030201a281714050a0309018,0x3e07060504030201002ea48070605040302013f9070b050403097f0181107140b053504030194f071e1f060504030201a4f071f06051303018,0x7060562040360020100a481b070605040302013fa201b0706050403020187a070b060542040302019340b05040302012a822492807060504030901a07060504030901002d9070605350402010058948281710050403020100a2838070b05040302019071e1f0605130a03019,0x7140b05040302018c9240b05040309015184e071814050403018,0x1b07060504030201802ea34070605040e03020132a3807140b0504030184928071405040309019,0x740706050403020100a1a22070b0504030902019071405040309016784e07100605130a03019,0x70605040302018e006ea17071f0605030201002ea1b28070605040309012da,0x2807100504030201002ea48280706050a0302012ea,0x7060561040309020100a4817260503090201009480706050a040302019490718140504030901922071406050a030901937070605130a0309019,0x70604030201008584e070605040302013f9221d0706050a0309019,0x2007270b040302010094807060504030201872ea0706050403090201006ea482817260503020100907810604030201007a91707060503090201599490714050a040309019,0x70b0605040302012e43a3339071f040302010092838100504030201009394e0b0504030201848071e06050a04030201a48070605130a03018,0x7060579040e03020100a2007230605040302013fa2039070605040302013fa484e072605030201002ea17100605040302010056a48071f06050a0302012ea494f071405040309019,0x1b071405040301002d9391d340b050403020192048070605030201002ea33070604030201002e982070604030201007a907108406040302010091a4e140b04030170706050a040309015290706050a040309012a9281110050a040309029070b0504030208012b9,0x48071f06054204030201a0706050403600201009280784040302010080706050a040360020153a07140605040309015a90714050a040309014a94f24100605040309019,0x71f06050403018752907064605040302018e00a28072605030201002e94817261f0503020100937070604030201007a90710060504030201002fa48171006050403020100a391d070b050403090193328240b04030901828240b05350403018284e14050a04030180706050403020801003fa070b0605040302080121a,0x48072306050403020187a07060504030902010096a49390706050309020159a4807261f050403020187a381707260b050302019,0x7260504030902018b94907140605040309019,0x7060504030902018f92028070605040302013fa82070604030201008491d070605040309019,0x1b07060542040302019491d1b07060504030901a491b070605040309012da1b07060572040309019,0x33070b04030201002a91b071405040302018c94828070605040302013fa28070504030201005332a1d0706050403090159907271f0403020187807060535040302018e939070605030201002e907261f05030201002e9170726050302010055917260503090201004d90710060504030201002ea28380710050403020100a4907060504030901529071f06050a0403015290706050a040e03020155a,0x391b070605030201002ea28340b05040302012a9280705040e0302010032a204e070605030201002ea384e07260b0503020191b172605030902018,0x481b070605040301002da0712060504030201002ea0706050403027001002ea201707261f0503020100a11072310060504030200a22070b0504030208019,0x1b07060572040302019fa340b057e04030201874070605040e03020100a07271f04030201002e9482811100504030200928070b05040309012a90706050a04036002019073a181405040309019,0x481b07a6040302010092234140b050403020194807060504030201005ea071006055c0403020100a491707140504030901917241006050a0309019,0x221d340b0504030201948071f0605040302013fa20071f06050403020187a070605049b0302010032a0706050403020100532ea07060535040302013f91b07260503090201599,0x33070b04030201878070605040e030201002ea86071006040302010092811104605040302009,0x48070605040301875290706056404030902019]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aA:Kz = tQ:=priorEq_sound (by decide +kernel)
set_option maxRecDepth 20000 in
lemma aB:btAll (fun bk => ∀ xs ∈ bk, Impossible C 9 xs.toFinset) tQ:=refBuckets_all (forall_cons JA (forall_cons JB (forall_cons JC (forall_cons JD (forall_cons JE (forall_cons JF (forall_cons JG (forall_cons JH (forall_cons JI (forall_cons JJ (forall_cons JK (forall_cons JL (forall_cons JM (forall_cons JN (forall_cons JO (forall_cons JP (forall_cons JQ (forall_cons JR (forall_cons JS (forall_cons JT (forall_cons JU (forall_cons JV (forall_cons JW (forall_cons JX (forall_cons JY (forall_cons JZ (forall_cons Ka (forall_cons Kb (forall_cons Kc (forall_cons Kd (forall_cons Ke (forall_cons Kf (forall_cons Kg (forall_cons Kh (forall_cons Ki (forall_cons Kj (forall_cons Kk (forall_cons Kl (forall_cons Km (forall_cons Kn (forall_cons Ko (forall_cons Kp (forall_cons Kq (forall_cons Kr (forall_cons Ks (forall_cons Kt (forall_cons Ku (forall_cons Kv (forall_cons Kw (forall_cons Kx (forall_cons Ky (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))
def hM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc16caf38af17a66cf32892493d50e1a4c555c54651289395),(64,0x26aaae8e284924a00ac0e87464924924ac15c6564924924a),(64,0x709249201582b9470924a209582961ff9aa78ae3315ca488),(7,784564)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KA:∀ ns ∈ hM, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hM (readRouteRows 8 (unpackWords 11 [(64,0x104214710220000000000210a084428410c6004040210106049192104c3088088254829c61101204310408631c230c410c41440782318514c188408a524201cc09a32424184284224228df2086106204528e118620862019),(33,0x40c1082314208c508220420881082204208851861044784031015c8286028210c4084411810c420581081)])) (by decide +kernel)))
def hN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2b0571d892492412b3972d9c249248056574597249248056),(64,0x84e28924a272c8c90cb4c9b3b492492018a85729c9249241),(64,0x28d59a0b45263ff5d4916b99c51291672a0cb0daf74fc334),(35,0x6852c52d3a9b265ae361c5124a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KB:∀ ns ∈ hN, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hN (readRouteRows 8 (unpackWords 10 [(64,0x104a2e8d011894120807109c30980318864184041844238d0210c0201c6608c2219041190230882639461010a108c22098440040707ce1388a1390a1408a118864b8d6120b61e0881d08100000000000),(60,0x211a13904100c06084e210c02018e108c4108844004073844300406088213144310443188210941f2040908504204081856401c6131061024011080600807088610208101c01c080700b85)])) (by decide +kernel)))
def hO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x26db96b9fc7324924a39640f30fa8ec6dd0e87148924a396),(64,0x3614492492560fee6cc62bcfbe2f4a249249356415f95d54),(64,0xc4a282ff29aade3d9df0cbfbbbab6e36aa512913d4541f2e),(64,0xcb1492261ea328832453dc6e9dcfd4be19338ab252269ca1),(64,0x9f63ae864cd6289489a6aa6920d58ffa293536cc6d90c98c),(16,48998995521465)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KC:∀ ns ∈ hO, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hO (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x89ac498504904e289a8688a6491a6488d02a2aa288a435489111c5424c47544531222714c5514870),(64,0x24c47544532445223a28a850290a2ab14d1248d1388649126690a22b0a22a04d40a06289c5219a44),(64,0x750d134c9234cd11505131222a9a2690d523445424c461445314853144520fc6218a818451315cd2),(64,0xf45135485458ac858ac1b44d370cd25a24448aa448aa1b44d368cd24a244160a4c00d334866906d1),(64,0x62224e122a4449a345930a511264d164c510caea88dec88dac88dc69aa226322253222484530da42),(64,0x14c3488ce515c668a91139221c48e294851448d114cc91ba2532cae90c871ba252208e9188720b81),(64,0x89a4a88a61b455350cd2408d15222808b97244d3349d131565344d3349d131124344a44105614d91),(64,0x3883688d4c989020c2223322a988c215a269a2269222699a4e89a6691a2699a4e8ba86890a428baa),(12,0x449464887c8aa43)]))) (by decide +kernel)))
def hQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x48944c5144c907eced3bd8f533fa7ecadb8d8b148944d3d5),(64,0x98c99ecb324945a8a98887a48efdd1da2933fbbb74326317),(64,0x36c87790c99eeba24944c51567077676f5758a4bcfd63e6d),(64,0x57fa7fb0cd2b7268672892516b2ac907d9d7f97dd5f21fb5),(64,0x39dbddb9d954da19a94492494a2c6106499592b9a396abf6),(64,0xf22f31b21bf53bd8b6bcc9245cce5124a269eb20f5fd2d34),(64,0x973b2c764ae6ab4f1697bb63de2b6e54dad124935554b241),(7,311875)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KD:∀ ns ∈ hQ, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hQ (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x8890c88901358d114ace8a02a0aa615865154828644d534dd134982744d434dd13492274482a9c71),(64,0x244570e2293445332c6691a243308c88a6548cd234485511d1315251784a8a09126022987910ea6a),(64,0xa82a9052c88d0719a468baee88cc519a468baae8945730ea1844530ca234905919a4911a2908a98),(64,0x29a468ba8e8905628e6298a469865175093348308892155049106d1351113491114cd15482b34554),(64,0xe45521a91312492264418455312441f44d3444d2444935482c0c22a90568898e639a468bace890a4),(64,0x9b24159222db421851530b02a9056c91d0741a26a1a6e91a25314c689a869ba468945730e6243241),(64,0x1922698ae2b0a4ea9a2416423544571585224c2915057158551682a64594765511b1d35444b1c248),(64,0x89248888282450159a2490584905428ba6e90ae6993433449908cd175dd634882c2242b8ac69905a),(64,0xba22a90561b45488a266190d13496274462a98d11d99140501306516509112451454911205113aee),(56,0x1061115051650d25444a09b26886d9745816045434430905ac8a2a8290d1349c20da22)]))) (by decide +kernel)))
def hU:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x111111111a42048e1a1acb4fc69c1b8d6ae29c18cd6ca1a987e3111111131b19),(64,0x21111111111a42026ad1abc1a4c69b2ae19ae483e311111113181a018be7e121),(64,0xdc1da12c31111111271a2019881fbb26e5ea1acc29431111111261a018be18b1),(64,0x1a1106da6cd51ba228e5a86e818a68381111111319192019848e1e9d6bc5bf1e),(52,0x42027a87eb6ee4a84c3de19f95be1ed6ba1da592d3111111131c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KE:∀ ns ∈ hU, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hU (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x44d920b03c8b82e545a16b24741d0689a6e91a241703ea2a2462286298a68aacc448d13158535071),(64,0x3ba28a8a28a0a220cac28a9124ba2a0a8912482b2482a145d2407114b2690fc015b222d1a64c8a92),(64,0x8a022a224288a221885474457448e164951348912065144828144531489644452344ec91aa1e0091),(64,0x390e4511d7744a4510d11d45434456099514224845c52544d224c269882864452345228aa88a8a46),(64,0xc32428a2669122a98942744d3444d2444530c22a90588898a6298a62bac1b449954c2b0fa2a444e4),(64,0x8ba6a912e48861a11224d342d44493668920bcd170a24491216102d0b451148d1698a62856d08e02),(7,2759893040)]))) (by decide +kernel)))
def hV:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb3e3b2aac3622211213719205ea69c1bdf69a36ad1baa69e19b3111111121819),(64,0x9a4c641111111241a721ceb41925c6b2ace2d622211111271a18101cb81c9b73),(64,0xb4e592bae2f6241111136191a81c9c1dbf7c2a9a2e62231111051920196a192a),(64,0x919421121319184027af281b6ca6cb2aca18a3192221121218193602b1dde1dd),(33,0x1302c829ce29c9229a829bd29f85918a4)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KF:∀ ns ∈ hV, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hV (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x49a41e445093a229b22c9aa235055234488391d7348d317a2a9852184485311d6348d33152534459),(64,0xb3a4ea8a2eb8b1117a6a89aea38a26a8a26b24c69204689a64e5155459113543c88aaca07e114d11),(64,0x149d1754512515208ae499102886562506934cd7144552506909242b8a2492a2490ac298ac195c50),(64,0xb242892622ba2298a4e89264904c28ba8889264904a68924498893248511505115cd455c869aa41),(64,0xb4dd17505154c5290f111daa2944309a241a459244d12351d2445955443534492144d218a42994d3),(64,0x6449474438a9a22b1a26a208691c46a8ed3445920c288aa249448308a28899a2e98a2c9aa4293a21),(64,0x4875216056148d434c911582693222b1242b8aa291a8699222a84d26445509456392248871414552),(64,0x514586509a14993264520fa290a4510ca61845541284a98922544491c22691a2692a81505530a5d1),(60,0x14452544520da2a09a6c19a4a10a22a60528a8348a42699a4432c81b44e134cd221544744c5)]))) (by decide +kernel)))
def hX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3ed36cf1eca9889452ea0321d79ffc724864c72a93289354),(64,0x367f0f5d22514ba8605b7cf4dd1b357a6cee94ebdd972f3d),(64,0xd8c991d5244a269ea981dbe19fca75e8cf9cca5aadcacebe),(64,0x9ac32cd8c98ca7530925134e54e4485a6322ffe33bd7f36c),(64,0xca191dfdf9b3f3736fb8c999d526510728aa242f71973ff9),(64,0x67ba19ecafd91c9299f3f57db3d7d7778a5f8c3aa30945a),(58,0xe4827bd324875b8df0eff9974c64cfb892449314559)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KG:∀ ns ∈ hX, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hX (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x15503a0e1115151151d10e24a888c4844a328ca328c911542693a24190641906488a813489144c55),(64,0xb45570b05662c5c31a8d21a6c19aec11a22aa45531a8699aa68952548a48148c6a1a6691a2240902),(64,0x35983348a82a0d42445509aa69150540ce339a8488a6134cd219c6718aa71d856544565455a0c2e1),(64,0xb04d264456450d234c911542693222a84a2b1c7322d9114d5156830b07525585c48b89351a434581),(64,0x20aa617112161620da61d45d4120d254c4910ed1348d1355520b02298691505520a030a1a4699222),(64,0x98902545521a8d35486710a513491134c3e8aa41585530a43288aa1348d37543488a81348d3751d1),(64,0x21c82b1c725443298691448328aa64d44d234c911582693a2691a6488aa13489145036745d30c22a),(64,0xa06d164962c871222d02d90d5694d360cd1584d2358d534c91158269194641a86a9a6488a8134887),(64,0xa1a2709a468aa61585520b021851520a43489a6490aa2350911542691a25314c688f42a9a66ab262),(42,0x930e2829861148541250369aa82489511245489a4889a6692046)]))) (by decide +kernel)))
def hY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa9032fb52d763a5ebdf979e9fbc5b6864cb43b988924b555),(64,0xb7c37fbd197e336366aa533ccace7686c932e664892498ba),(64,0xb52df43a5eedabdd0ff29b2772fcbff17c92249262caa243),(64,0x4903668f63253b5c75b56922b6e32b88c249261eaa38c0b7),(64,0x382f365e5e6cf0c8ed98cb6f5b4cbfd0c99dee1a4924b555),(64,0xc8196487ccf5fccf3c667969e67f73a64cbd309249296556),(46,0x3dec7f244924925606ff6295c30924924a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KH:∀ ns ∈ hY, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hY (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x86145582a4445540aa8348d43559115424b2a4160ad16222299c5339a46a1a6c88a6118aa734474),(64,0xb42893a2f444d51a0682505321a669122298462ba0d11fc49549540c22a91948b0751358328a82b),(64,0xaad9514cd13545a4583a92ac6ab0d15502e0aac1606153a4e92505721ac691222bb2a178a2c65156),(64,0xb04d6348941588159222db02aa86170ac2a92a816a22340d06a9222984d33489414c831590689222),(64,0x148a69922293a2290442a1cd11e0aa8a9512551445d513ac21d491724d145448e0c28649926a9222),(64,0x4050124d9614222932aa9856e8a51135095150a699222a3a22a2a280a82aa854114c568a91134895),(64,0x52224498869ba4c88ac1161110ca41506d161a22a1ca434dd2644550945639a2398a410e26290611),(64,0x8aa4158711150c2a14d215168a3a2414cc688be689a8e90a8692a62508388ba4888a8c9aa415b241),(57,0xaac91224912a1d4962588510dae68a2e888b01845520b11114d42994d274d9126430)]))) (by decide +kernel)))
def hZ:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11204e1dd19c2aaa2aaf19ba19ae1d3d421111157190398e6a1e21111111111a),(64,0xe78e18a4f3c4311110618411025bc2abc18a2aaf1992bfa3a2c1111111471918),(64,0x1b2a2221121218190285dc7ce2bad4aa2c8e18a6c1f52111117186a95ec281b9),(64,0xe1baf3ae281a8819ae293d22211111371a401fac19bb4bd4eb5f91a9a3ff2bae),(49,0x398838eb429ac1ecb3de2bae18e2221111117192201af81f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KI:∀ ns ∈ hZ, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound hZ (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xb0691485888aa814865115426a9a66a2841f45015a22aa05029445209a4699a8813a22154e688e20),(64,0x29ca77543c8aa81485530a05288a4111846749d110aa63445d14452345930d222c043098a2eb1a2e),(64,0xa1a22b0b9114ca2994d1348d3245153443b144520c22c9b281b455424c328aa81585530a83288aa1),(64,0x19c668ba4688aa8886520a03288a8330cd17489144cd10f15154951259514585889285150a689a46),(64,0x5555254c511a43e9ba22c0522899284a8c6aa4a6924468a426992d427a22b9224a3a42a2a43e4457),(64,0x2444875c5143a41945228875334501522220a026a124142a2a0ea42a924ea8acc91a269222c90697),(64,0x744349a22899a26a9a4711a26a1a6a88b010c2aa88901551134489288a628ba860991124911454d4),(22,0x9544552254388aa4143222b0614)]))) (by decide +kernel)))
def ic:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x36cf15c7d38924b5d40649def0c8b4915b72e7d499249355),(64,0x30924925e5990b4d0dd3f465fa1f63ba55efcbcf56fa39bd),(64,0x249272a0c37e7a6495ca39bc3e633786e5b5eb4f8df0dcbd),(64,0xcaff8cab5b9de6644928a5d5067b946fdf0d931931b21849),(64,0xa67fb2f8cc89249262eb10adcb699dbe1dacaadcaee6ed9e),(64,0xb8d911249259caa243962da2bfbdbd59c915df2d7ab7c7b4),(64,0xf2b9b6735e6dff3f8cc892492cd589076cb4d8f93a7368ad),(11,1215756397)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KJ:∀ ns ∈ ic, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ic (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x18aa734874255540da2693224a32a185151118328985488f130fa22904c288614548260d224f483a),(64,0x8b05a444cc40b861b102e0cd4690d115522a98d5350d12a4a816c509391214ce2998d3350d119c67),(64,0x92a2293a227b26cd926291224a84d50c24f0b1028b941458920bc9121c516a422c0a4a88ac1a5030),(64,0x444d344452445120d22490aa234dd516a2a984e29485411a6ea3a24154c688a6688a4a8a24899222),(64,0x350d16a22c094521ba26a061a148a35a86e89a818585228ce61985a38bc49879214c3890ce2744d2),(64,0xb111405888a2a16926162a2f1184611846148720e28888b01d44591522291a22904d20fa2c44581),(64,0xa02aa04e2844d2345d274442998d1148515856888951469197445514c980b832890e4390e438a8c),(64,0xe26292a2293a223922231a419445454432a87540ca2aab282cba274450889a668ba6e88a4194555),(41,0x888a468924688a8891222aa2428b24a89241120922444724446)]))) (by decide +kernel)))
def ie:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0xdc272042110048480f090ea148421084400854101a7834fa388a7a14b26f58540a42108422008ca),(64,0x84034a868100bb9175d2d3c38445599e5a0c4e72042108404328803179d14ac296c25ee87ab93b6),(64,0x2165a2d32436a46c5c679c85848421084210050a4080880745ed465bc0b6e8a02a9e961dcea08421),(45,0x411134586d37786d242208421004e901e78144e9084210842008560)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KK:∀ ns ∈ ie, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ie (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x8aa134822a846244d012486691c231326238a27458531322298a42886d454453149d114c5214458),(64,0xe221d512291a22b1a22a9a2290ae248a46a12534443e92288929124443e922889243091b02a80d3),(64,0x98a2a08654148930a4328a444a1a48a124489244a124498501945015545d14a2caa229144d6744d5),(64,0x245d639a8489264604429ba2490ac4c1a848926458a829aa4498a4709a6709c22099524444699a46),(64,0x24c34a9262898d324432a20d3645d2344531505339a6488a62890d31044134c5a14430a922954d52),(64,0x55104244e142a287450115ac394876aa28e8a0910caca92aa4e4c39012448924488d12485288a429),(3,8840)]))) (by decide +kernel)))
def ig:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x54924920958c5085378a6f5feafd8cde474e8aa24920c356),(64,0x2492432b10e63bcf0f93f7268669f25f1249242356076867),(64,0x20958ec6ef7a9a93e4b96b9d8b2c892403952603f5f15569),(64,0xc6ef6a3acb1dd399edcae3a2e492425550679f1f8e8aa249),(45,0x33db9487455124904ac6030dc75b39bbe)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KL:∀ ns ∈ ig, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ig (readRouteRows 8 (unpackWords 10 [(64,0x104c2184220840610424384a2184222840208c42084e21846208000084060046420463184020988111022018851044208402184020242248c220840218402020a5684060882318821008610080718829),(64,0x84e448405028080a8051842618464b8c279080b008e3305a6084c33a642029c2070002842408824088a170aa1c8c25504c2304c3091c2204c33994130a81058001042208c0200cc101c81018c201885),(3,230598)])) (by decide +kernel)))
def ii:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24904d581fa18698afa64377d8dbe2d71b968a9249241557),(64,0xc0f96e7a2a4924904ac0fb2f3e6d0f975377f949319baa49),(64,0xbe788df373a7d0ed319fa24a24239507cb71972a4924904a),(64,0xaaca852d86da89249209581fefcfb90924920958c074de9),(64,0x4487348ac5aec6fbbb96e524c64b17f6ad2456dc9f78c449),(6,111369)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KM:∀ ns ∈ ii, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ii (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1482898a21951912485134822a924289a4298a818449234451088c5110641854148452418a321c35),(64,0x348d10c28a9a2488a023b48328aa8c9a24889c910ca628800489241154328924624891119d314493),(64,0x54442a98308ac2b0aa810c02a985a1f4432b930003aa1b503e9861238a2aa2a66a922609c51350d3),(64,0x144d916226a9282a90931546288b42a8691705c1550219855308621d44d2250522126290c5115852),(30,0x520fa8c98a4b41224d8a2ca302190a2c9ac2f)]))) (by decide +kernel)))
def ij:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb9df0cf2d374f8dded31758db645aec64c7a86448920e5d5),(64,0x8a733fd92e66489249aa2c0f9f6333e642512412b135121c),(64,0x8ad8adb95c94a492418b2a89a605278ed90df6f76c8acfcc),(64,0xfe2b6e34f88924831754d681f31fbe3eec7797a7758643f7),(64,0x4cf889248056311c4d9365e432c8779b9c7fdb1ffcea186f),(64,0x8647aeaae915be9d31d6993d864ff298fe89248317554ba4),(43,0x6056dca63ea4492422b1c9058ef7d77f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KN:∀ ns ∈ ij, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ij (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x150c2a18d274459545e10c42a904300c226d0ca328a6514ca691a23150ae88b6a8b02e749a28447b),(64,0x486d334441484950a8868a2e15aa2c0da42c0036d0b02bb05838b489309227042844d2444da21886),(64,0x88a6118a85569115482c0da2c0e223b88550d2e4932223449534896144d854512444940a55169241),(64,0x14cd17643a8ac2d08a61a485430a86350921504c88a81161115482e0da2e4445328a6534c9214c4c),(64,0xc2a417a22aa2c5429a4d106d1265520b8388aa6614ca69304e88c5433a24d2a4160b1116c2a91d92),(64,0xf06d5544af454e4390d134cd2244570988c21aa917036caa29687191d40293228ab246bb22cbb224),(41,0xa99116d130ca4a98581d458162228320c689a6691222c04a2)]))) (by decide +kernel)))
def ik:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x4f3d22111110211a182028ec6d8248e5d97dd281a8819ae4823f21111103191a),(64,0x111110361a18207b81deb6cc2f992eae6a2dff48dc729721111103181a404998),(64,0xdaa1dc9189a19ea1da4a738211111041a1a182048e59d39cf19e3f8a1da712f2),(64,0x8202e1eaa281ec28cf2f884fc69e5f3f211111031819622022ebc58c2ec1ffb1),(64,0x111021b1a17112dc1d8c3bd21f82db91a1cb29ec4c81bfc3a38211111041b191),(40,0x4042c824e187ae5ae6ec2cab2bfa1bc2e2a3f112)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KO:∀ ns ∈ ik, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ik (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x89ae54485134942a81144444ac12a4c1a4ec92249282a44492145d20a83a99c388b03a918388ac3b),(64,0x14d12144924585234501f08c4904611846118a22c9a2ea0a24b1a4a8885114c5114d08a8a249156c),(64,0x88a468b8a6298295845558561248d160ec488a8288a8889a47349d11322209d11149d34545234521),(64,0x324e2f45520a83888b440911112226b92448883888a4b0ad1145c5125c920ac681a02a18453685a2),(64,0x5482d0e223c045244522b4c51149514492891a244188e99242b08568aa415861121ca474c9215445),(64,0x915054150541aa699242a88d1269560b9115482f4448721c8721cd434c9215044154ee88b6eb3111),(64,0x44d520898288991131d124c523456708b28a22416854608b08aa24160a82cb222922c194d1625038),(10,0x9224452344d2)]))) (by decide +kernel)))
def il:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdbf365cb4cadb8e531fd124906a8b03e5b94c7f249248256),(64,0x90ea492490d4541f2dce43f92492412b1c8909e9a191d9a2),(64,0x9d58193dc71d4924920958981d52c9d33be877d4cbe632c),(64,0x623bd8b7d0cbed7b6463d267eecaffd69f1be2f8ea49249),(50,0x3f3c32444924904ac0c9fe779fc924920958c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KP:∀ ns ∈ il, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound il (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x9924299a468a282644526444148528992415090610ac29302c14cd1688e510aa29242914cd158b60),(64,0x4512288b61b445215852159d20c222d0ad114c5514c5554d2254561189251454288b239452116004),(64,0x3a6491a2ecb284caa4e3458d0a0c830a2f0bc522456a09ca728a2e0b8d214804b8b08a1a21a5051),(1,0)]))) (by decide +kernel)))
def im:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd16d0ddb9b71dec3679ccb969b3922ffc32391124924c716),(64,0x80e9fc37a24924845640c93652744924908ac4d302cbcb1d),(64,0x30252232ed0cbbd52cd1e3b5ddebf3b763a9d49249212cb1),(64,0x58c074fe3d112492422b1813b6d335bd4f747b1249242315),(64,0xd4924921acb1301ba5a7cfa23ff9cffbc3b654f8492490ce),(47,0x4c08cde29a2df47f486296daf553498ed99)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KQ:∀ ns ∈ im, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound im (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x3a228c8a28c0a24a288a14c52689a2a8a2661982b35d1685a4892617924170a84904302acab15470),(64,0x88b920c1d444d915582608a4b0aca82a0aa2a8553458c888e23892248a468ad9114c00244e488ae1),(64,0x348951052288a4e988281459234c9209c511483d00ad15489888c240ca2692a260d221e489289434),(64,0x24430912c28b42d1482a184681a051605829052b09ca728a2b0ac5216893548e1358922451425514),(14,0x92244488a28135912)]))) (by decide +kernel)))
def io:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x21b6aa68b4bea1aa49121111041819022d83aed7ed24a8a1da59111111101719),(64,0x1111111461a42102fbe3fff68e5226bb4ca81fd121111041818421018da618cb),(64,0x13103219ca19dd44cdc3e5e11111110461a73542bba18a2bbd319a2ae81d1d2c),(64,0x311a1401e49ab6f82aca39bb4aea183911111110361a01d853c11111110111a),(18,0x14029882d391111111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KR:∀ ns ∈ io, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound io (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x48ac6ba8468a424aa2c6a13d117851407d11543491251304e289a45b4453151530da241a06594435),(64,0x444d31da42b22691932e98b422455316428baa22f54d312c5642c5635d82345613547ea1a6248ac2),(64,0x39a224122238a41944552a4c2c945736059286941542b0982c08b0b09a82b4ca1484c15045848494),(64,0x1505234462b9222a8a8288b42245120ba48a0a4aa9a8245952245920892688944889229065354822),(64,0x4483401264892e48aaa80aa8709aca89d161548888c5a24455150510da4688c59244551505154c55),(36,0x3acaaba8291cd24509144928906d1349089069339a47)]))) (by decide +kernel)))
def ip:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdf99ac374d16d628653d9248072a4c0adb9c8be249248656),(64,0x24847aa0c9729ace66f0dbee5bdca137b24904d5543e6ca5),(64,0x3e5b94aa42892412a981edaa334d9f76e8e5eadb94aa1d19),(64,0x93e76fae4d0eb8cf6e46644928b5d53e5b97ea42892402a8),(64,0x8afeae9ccff652ba6644924967aec876c7ae3e45bc46dbfb),(21,0x1a605fe86cce58b6)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KS:∀ ns ∈ ip, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ip (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x7459544854886c1d445214c5214c5290b510d26a93a22b06114483488b920ea82a86114485488680),(64,0x11a86890532a2280a19245c5488e01d44530d2460c241a44c19445a9ba2ca2241a455254dd234d92),(64,0x744931455265c5255c28245028449315853158d12485311a688a429549570d222a0aa2a0aa689a48),(64,0x7061235d910cb64ca246d130891222e4c3488ace28bc53b0a2e14d2608d16a22c44c92a135114000),(22,0x514545414cc708a481450292859)]))) (by decide +kernel)))
def iq:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2bfa3e2a211111114191a53101aa1dbc2de91c9c1c992dfe693f21111111461a),(64,0x37195401cfc18e93d284b2bfa382a2121111361952205a4b858a4398199f284b),(64,0x11110571a018fc28d211111110111a2203d3cd9223d983d9f4df828d21111111),(64,0x1111111021919404dde1d7f11111110211a512202fde4af9196674e9e1ce2111),(30,0x40469a69b3d9f23daa3d9f54ebe1b9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KT:∀ ns ∈ iq, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iq (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1683890a22a1a22904553445209aca9044754512088e688906b1c309ba4111d5112891124d274456),(64,0x982634456344591605115c5514446c2a269128152a2b3443699a2a0b024345150b4920b151606d2),(64,0x98a01b44520c222259d1112888924cb2227144e29447498651155910c2814b2414069126a41e2a2b),(64,0xa0e40159920caa1d50328aaaaa1907424c692046a9a8688e531583292aaaa222892841d4d5545054),(64,0xa8a82b8a22b045b0865351222d309115454148516058e90aa2a1a682445849222a8a8290a290a426),(64,0x1685316853354d43445e90b02859630da4aaa281e49571432a0e321c80c831224c122eaba8a92022),(11,0x3aa1b51d155554)]))) (by decide +kernel)))
def ir:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3fa24924b517076fe3a6784924904ac14da1b7a249248256),(64,0xb8caa9d1124906aab134c37638cb1498f5b4374eedd8c865),(64,0xee62492486aac4f2419a45368b787690ed61bbfab1bedcad),(64,0xd1f32a9492492095d440dbe6365c74c9daa5dcc86ff1dbb3),(64,0x24924b395066d23afdd9e5ffaedd8caa1d49249209cb833d),(39,0x6a47dcbcb4cf3d7fc8f7c67b729fa)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KU:∀ ns ∈ ir, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ir (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x93b028a9d27443a9ba22b124169a2e0ea4e88ae4905668b03c2449714c52418242922908b495bc00),(64,0x20ac7401d151222c8b02b9286c3a269282a444488875330711607522871158708a222292224a9326),(61,0x288a41e445e98691158e2a9d955443298e541583292a224b22243268aa2449443944c5229051)]))) (by decide +kernel)))
def iu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9ef3edd0df35526f1cc744492423d5075fb29fa249248256),(64,0x8a4d9e366bd4735cadb8e949249219eaa84e9ee3ff9cef63),(64,0x726e9cda2b6e3799b124924135656dc6fe8924920158c214),(64,0xba758df6e56dcbaa74649219ea981dbb1cb64512484560a4),(64,0xb0df7c4ad94c8b4915b71b578512482a2aa106cd949a2be2),(7,56735)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KV:∀ ns ∈ iu, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iu (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xca4c8a244892e3e4451144c2a445644dd1449114485ea92ea89128a2248a0fd1251511205c906e0),(64,0xa4592154348b802a9a26a1a2a90696144d6345448a1514a2284445214c520ca6c89262d449314853),(64,0xbb24184501c4470987d1251520a83488fd20fa24aaa4148a910e004887120d28489a48888260e261),(51,0x3a24c12c4b8a24932c14922914223c4c551d224a489425221912ca8924e89ac8)]))) (by decide +kernel)))
def iv:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x49fc1da5438211111031f1a2bb82d1b491211110011a1a8c2d5a21211110011a),(64,0xe48fe3dbb3aac19ae1a492111110518192616224822bc8222e81983983cd39e9),(64,0x2fb81aac7f1891111111319191c01aba288111111102119242105da29fe3dcd1),(64,0xa1aec1fba1e1fcb298858391111111031c1a3101a3bcb298828fd29886be2fcb),(55,0x521201ce4dcd18d81e9e1729884f111111105719140422bc27e2ee4)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KW:∀ ns ∈ iv, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iv (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x5451214d550ca648a286992410c02958a2e7844189ac8906448a1428b1a110608b92410c05116c00),(64,0x89a681acab29a4c10a515482d152671a48921a4a13222a91240ea2a90542e445c112289126194452),(64,0x344e6398d17486638d1150a1160611290a4345d2190a328ae4344700045244c5274dd64455214c3c),(64,0x4458b62d2749dc1705c289545520c83342d0b451164d234459444580e241f454150d43345688a912),(64,0x50c388b0528b11141854418543485340d5158aa4410308a4528a43888bee9a24c8aa81205a179a2d),(34,0x5214a6e8aa469a05116c329219151c5551c5534853)]))) (by decide +kernel)))
def iw:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 3 (unpackWords 4 [(64,0xfc42922a2242045bee43ee81bb8798a29a87aec3c3f8e4a886c19e1d201a2e2c),(64,0xa382c21803a3eec3c1fea2adc188286a1d2061a2e04a8819a41d20222c028fc3),(64,0x18a1d20181e2e54207cda5b87984e86ac286ca83c3eee41e8c2bd81c18a1d201),(62,0x1804a9c3bc41d20422c028fc48c42922a26203c1d88429ac3c3f8e4a886c1c)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KX:∀ ns ∈ iw, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iw (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x3a688a241c445645d810c02c459a6bb051715c549525785e2d861117c8c220882302c168308b05b),(64,0x906088b42d44dc6934514a92a7adeb186227875131cc76a1a81b84d0ea2382262914828910139940),(49,0x2a2298452158e28ac22ca0a1510280c436892ac9128e99a4e88b8d08a62)]))) (by decide +kernel)))
def ix:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0xe36818061f80671f0f103f303ad0b4c20527344000681b0194169cd100420d1407eb089344020832),(64,0x479cd100420d00e8f0f4734401083411807c103ea061be127a1d64bbd8348d0987344030601a1035),(64,0x43205a49ddc2e7e7f70da285e688040c0341200445348ac0f1d264af70b6e1fc383440338340275c),(5,10488344)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KY:∀ ns ∈ ix, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound ix (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xc30314893122229322a7496292c5264522904d554922924521602320c82298428a022928e90c000),(64,0x348514091138546b850e9928cb8a468a436912acb8a468a0500009224522a1a47488264855248a49),(64,0x24c9115cd1348931444152222904c40a05228a220b24489a468882290aa4986115490225951249d1),(14,0xd1151531492890512)]))) (by decide +kernel)))
def iy:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3fdcaed55d21db2b4f849249063ab033db96c6f249248256),(64,0x3a7c77a492490d454b214ba27f2f719b5c75f3bc6dd8d9b6),(64,0x325ab5b0ed0e8492496a2a983ae56eb54da3ba9974c62db6),(64,0xf74325c74f9feb53a124925aab321df1dd5df0cb8cd4efee),(64,0xcc832cd1fd63a76cb4274249248662ec83fdd53f625e394d),(64,0xa6d0d9be47dd2a3e488ff6e7eeefcf8ed9f3a1249241aba),(52,0x641db64a6d9e7eee64fa1d9f3a1249243397251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KZ:∀ ns ∈ iy, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iy (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x2ca22d3a4e7451269a2ea2b048928e0862a8a24f144e53942a60430244d230cc30a5617122690ae0),(64,0x98a8298a8a92a2259249749114494815948158d2344829a2c3d452715527154d23448299aa2b1525),(64,0x84d1174d288a42691a2a4452899a2691a2e9910722a42a4561844d2345d3218a428ae63445a0f222),(64,0x91b2493a6291a6a10b44510245044b0a8c83202830541504d2614e5384e508ba154c3291a2e92a21),(64,0x8b05129ca70adc178b2e8bcd1790c43054c0b058745868b05d248911482419822b8aaa664920c226),(49,0x88a262912c809d02c9429390270c05491a6c88a4e88911635121443014586)]))) (by decide +kernel)))
def iz:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xeeb3c9a5ae7dc2828196112141a18022d84feb382d4f9a1da1ea111111101719),(64,0xe4fbf3ca813c9f44a58dc3d31961111141919644248c4da18db4fb84fad2ede2),(64,0x2f2a61111141a180288d4bae4fdb3cba1c8818a3a619711111618346038ef4ba),(64,0x49a2edf4eae3ca1587111105744206c39b2de92dec1dca1d893aab393cbe1d8a),(64,0x111371844201c8c1df91e82de3f9d24ba3cd86de1e81c1b2a61111141a192acc),(31,0x4205999258e58b49dc6de1e83c59611)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma La:∀ ns ∈ iz, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iz (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xa1aa689a66398e6164e2c224814a22a86920da28906d1304e289a45b4453151530da241a06594437),(64,0x88ae138b092445708eaa932a889a819443e99a4b11a8d21aae29a2c09a6691a86a9a269a14941a46),(64,0x15a41851560b42aa856889a8699ac6a9a4488b015502a0aa61605150f22c144d809a8699ac6a9a44),(64,0x3487e89a468946519ac68aa413a228b06913542691a2419066b122899222a045075030b2d4c187d5),(64,0x49a8d21a4689d0741a8691d0741a22a871370a66b8cd1298a6350d2298a628ae624c5518ea194951),(64,0xe49c254cba88b648b262d48d3344d43485e89a6689a84922a68b85114c30a29510ea468b022da56e),(64,0x1643091a21f5c56429d20ca8289161d50d7614511542b144cb1556e154d8694d425a6a91a2292a21),(42,0x965543888ae184cd1404d6498d5514d316a82c487688648c0657)]))) (by decide +kernel)))
def iA:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x7892c8a431f11111041a1941102bb2a9c49a29fd3be87ce1e811b3d711114718),(64,0x2111110111a01eec6d1942111110111a34603d8e6cf228ed4bae2acd2eaf3dde),(64,0xd211111041c1a202adc3aaf28ca1bfb2c292dfe6f71d211210271905afa6a31d),(64,0x7f81e8e18d1d2111110319192640648ba184e1c8d188a27ff47ee6992c8a5e71),(64,0x88c2adc1eff6e97fa7ef2dfe7e71d21111105181a1840249dc49d92a3bdc6e92),(8,1646395875)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lb:∀ ns ∈ iA, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iA (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x354448085645032b122ea9c52a2912144520a851355621da66a2112144520a0513552891a64b4450),(64,0x145668ab4169281b45a289ac129ca7368d434c9115425158e488aa11543892a2260a46b095112c52),(64,0x91a280945428e531fa22b8bd14aa6c8874000a468912ea07530b19a5502e444c8320da350d324456),(64,0x444532482e345e2a0ca328ca328a6d13453144542444d14c7c0da4888ac2a445409a41945088a026),(64,0x9a09114822d5d889aa2752243a230888a488a34761d8759d62913210c1d12188621886685a88a42d),(64,0x88655150c2a088621995171d1522289a46944c5446452544925542b0da26985124090890a86c0b22),(64,0x9122720a2821a249044d248911303498a4a88a4e8896290a61a4456448512482a14c920a45116c48),(13,0x888a4888a4688aa8)]))) (by decide +kernel)))
def iB:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xbcf18fa18d91ef94bae1bd91dba2943961111104191a01b8a493c43111101119),(64,0x1b439711110251919041dfd1e881dca7ec1e85d3961111102619772049dc78a2),(64,0xb1f9e1da4b4111111104191a01b8a1fc411111111119190381e9d4bae7cd19ae),(64,0xd81fbf1eca19de1ac1bf3d42111113619281207981ecb38be4fa918d83dd81fb),(48,0x2019c82c82e12fa5db2888652a42111110271b182048eb2f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lc:∀ ns ∈ iB, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iB (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x450d67645152a4e88753285888924ca12c161a2d14c3e9142a44492444940a8488ac533454290e40),(64,0x9aa698a21c4878a2a6240692550968aaa33ba6a92a8a90ce25443b144a439a22baa85320d116056),(64,0x654308983a88bd30ca269065455427645532624c89a4c8aa81312ac8a26e8982a90a628865354456),(64,0x44851692468ac51394e509581c44c43102450542c322293a2b0b09150b601444a89241d4452255d4),(64,0x87d2444560ca41d448709a41944e889c2691a280945429ed3496110e4930fa469b22293a2244549),(25,0x48a282988c11485728a4808a484a030)]))) (by decide +kernel)))
def iC:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0xb5152678db8a3b617b23ae83c0c88208421080a851d802de4696c7f80a502d041e90410842100caa),(64,0xb17d3476c2816079904108421010e90087dc1b71476c3c7c90806c19106108420099270884024782),(64,0xf0859a1b81a04210842122d22016562ca67a4033922df57e86b2c3d20c2108446494620169d3c747),(64,0xc30a4e2a6f4841cf8bdf88be93c59a0fe2e8681084210848b5108203707b7914b9042cf041e4890),(64,0x9f00e382bd442ad1d622ec2f40580df88bf510c07744ef28c6058d049108421084202864a21040),(4,230466)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ld:∀ ns ∈ iC, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iC (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x912229222291a22a2244a9a2e90446344d2088e491222406d31e22292a2293a2230a4299a4614454),(64,0x1605731a4e88a44a05a18443a9942b4444184582987d22854889029445120a4d150a668a45217032),(64,0x444e489c3888e130ca2290a9154c9890a273445415d910c2413b2289ba270aa4292a2c244aab1156),(64,0xc5c5898a8b145488a2418454888f52151510c241406514852144d91548550ea22a14328889615592),(64,0x20aa63447c74830b0ad53582eb0615142680d2648505091c56913d1791110ca42a9855214c533a41),(64,0x8b0225b0468b911685029a091154223944185453394e53aa2290e517ba22a044620830a0a6621886),(64,0x12111170ac2b0ac285c16928721c8721c5136c2c0c22f24cc330cc330be10c34cca341844481883e),(64,0xdc3089144511c4706610d511306110d8691a46d1b4341066214454144531d5921459a4644812048),(31,0x3a219922380e42f8e285a16761d82a8a42b0681)]))) (by decide +kernel)))
def iD:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0x3283641001e2a9621ab026b829224d100ca0d0c4011ffe3a3a1c70c8609db2a1411742c344033836),(64,0x876c814a04ac05dc1093e1f3c0f0fcb2310158586880c0e03412008ec113a12900f1782c142c3440),(64,0x2fb85f5974f06d4e36cd10081a06481088401095a0787d7916c0e82b0b0d1018a0d9822088044e01),(64,0x2fe01e2a96206184fe8af0b0d100cc0d106ad0d4f2bfc24136688023068422fc8fc11ed191fc0ab0),(3,6208)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Le:∀ ns ∈ iD, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iD (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x88a8e8a248892414124138693144d26443092a26444e298a229076a8905718ac908a4808a4a4a0af),(64,0x145a170a265194f43d01d44a92a5a769da2da22d445c17922d1c9121448540cc718aca4551129248),(64,0xd31121615114c2290a2908b47285015988138641b44934445324911149d1151810c1117043245031),(64,0x15951460920e262a0b22a0b21850553226c24561b4581e445215c5215c3090aa634c42a1c30d2c72),(64,0x904e28ba471595224453344e2907a4907110ca41945d274cd20888688a4e886d270a229605515855),(31,0x6d12559225192644329061174dd11052690504)]))) (by decide +kernel)))
def iE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x248672e793118f7874f0dd265ac3f2b6e2a4529249243517),(64,0xa6c2492483145da06fb71f2ee7cbb1d29f22d347cfc6c249),(64,0xa743614492028b1eb2065b95b22b0ed6192e59df699fec73),(64,0xbec2bc361449211eb39ac3e6dcdd8ef64567e645a48adb8d),(64,0x9e39b6735e6dff1d5cc492490ce5884a6d22b65322b24532),(64,0x80eb2478d9a7736ce6bcdbfe3365292492433963524b6f1c),(48,0x34c0659739b6735e6dff1fd7851248662a69)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lf:∀ ns ∈ iE, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iE (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xb8611184c20a0a714521171640a42a0cc44888d115042b1c269a4a80a1ea89504398415852150a6e),(64,0x945d32545111222a04930e434892c1112c4a8444a8a44c06d10da68a06510da44b84546445309241),(64,0xa3a4c88a468a241e4c30a2491120520ea21f48e288721944d608922912e1120520da2ca0a4489241),(64,0xb489564494744d63485111c523aa21848369ba41120d1124d640a439443a0c2468aa862451229224),(48,0x549110ca468865224594448a28487c994d254457644560c243f44be90681)]))) (by decide +kernel)))
def iF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb0a249072a41b3cc6cdf9b3ccefb14cafb17324289242395),(64,0xb9f37f24924806ac64d8e9bd32d98cb3f33e90e96c3ae3a1),(64,0x966ea59d2537f96b61df92492423d573e3fd956b24537ead),(64,0x914bbe73fa8cc7699597f6acd32b365f1ba9249243596692),(64,0x2015905b7f4fd3c3f4d4e6959ae566c75c4924909455440f),(48,0x75db1d71b8dc512482567f4866a6e371449)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lg:∀ ns ∈ iF, Impossible C 10 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J aB (by rw [← aA]; exact (checkNodesRoute_sound iF (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x8890293a2239a4889c5089242b0aa291a2e91a2292221a483088a42a0a6291a2e91a2315485d4453),(64,0xd22ca04d4445d34542498652744d2345e194492655d1112ce889156587488f9425a64d49ca89a4e),(64,0x888d1149ae88ae224d180b053348541722609c3e8a4348a2a2b5092a8ed30c2480e222e49e488712),(64,0x15885214828a5131524e8aa6490791150768a83c88b2493aeeb05450952548ae2b048b0ac8d23a64),(45,0x3a61b485115c5614553548914052289a6691c5638a22a0aa288615)]))) (by decide +kernel)))
def tR:BT (List (List Nat)):=refBuckets E [hM,hN,hO,hQ,hU,hV,hX,hY,hZ,ic,ie,ig,ii,ij,ik,il,im,io,ip,iq,ir,iu,iv,iw,ix,iy,iz,iA,iB,iC,iD,iE,iF] #[0xbf0a3087039032029,3020582972,3489955871,0xf00cb0a60a1,0xf10ee0c20a907a077073028,0xf20b7056009,4077666488,0xf405f04100e,0xae060037017007,7353873350683,1040595,2902843483,73762044008046597,639102,0xb009a05d04904200f004,4228677748,72629684755693598,210,100,0xd60b5054034020003,0xba06e052006,405592,249,0xbb0b30a4097,0xea0e40bc09408906f06904c025,0xfd0f70bd0ab04d,1028159,0x1080f60d80cc0c5068,4161548308,0xd40ce09f09d09609003b,207,0xb108e04b031,0xe9095059008,0xdc0b209108607f07c04e019,0xec04f02d027,0xc1050026016,213,0,0xe70d90c9012,182,17596196139076,0xaa0a207006705103d013,0xdb0b90ac06c062,18077585461361,0x9b092076057043021,528397,4278747268,0xc605c02e01d015,0xe10ca0c70a508007504702c01c,0xfa06103800c,72355358215557251,0xe50dd03e00a,0xc00a809808f06a,0xaf09907b07204a002,0xeb0e608a07d06603a033,3893194899,856185,0xda078046010,0xe202b02a01800b001,0xde065055036,3741966405,0xe00be082022,368657,0x1051030cd08c08b06d023]
def Lh:BT (List (List Nat)):=fastPrior E #[0x7060504030902018b94939280706050403090201b072c2306050403020100a4e07260b050403020194e07140b0504030180706050a04030201559,0x28070504030201003292039280706050403020100b28170b0504030902019,0x48071f060504030201002eb070b0504030902015191d280706050a04030901a,0x49480706050403020100a74070605040302010093948280706050403020100b07060504036009020100a,0x49481b0706050403020100b1b0706050403020187907230605040e03020100a07060504030902019800a484e0726050403020100a39071f050403020100907261f05040e03020100a48071f06050a04030201a,0x48070605040302010059a20480706050403020100a38071006050403020100a1c071206050403020100a,0x20481b0706050403020100b070605040e0302010032a07060504030201002e9,0x1b07060504030201002ea284e10050403020100949170706050403090201a11071006050a04030902a,0x33390706040309020100a48280710050403020100a28240b05040309018072614050a03090181c071406050403080100a,0x1b280726050403090201a24070b06053504030190706050a04030902014da4e071406050a0403019,0x39070605040302010052a1734140b05040302019,0x7060504036802010051a28071046050403020100a37070605350403020100a,0x7060504030201006d9240b0504030201005191707140b05040309019071814050403090181c071006050403020800a,0x7060504030902018e9204e0706050403020100a,0x3348070604030201009391b0706050403090201a1a4e1006040302010093328070b0403090201928070b053504030201907100605130a030901907230b06050403020801a,0x33481b07060403020100a07231e06050403020100a07261e1f050403020100a,0x331b070604030201999070605040302010041949070b06050403090201a07140b053504030180706050a040309020153a,0x2434140b050403018,0x7100605040302010056a,0x33340b040302017070605040302010087928171005040309020100a2407260b0504030901928071f050a0403020191c070b06050403020801a,0x70605040309020187928072326050403020100a11071006460504030200a0726140513030801009,0x48071006050403020100a07100604030201007a9,0x4948280706050403020100b,0x706050403090201002ea2807231f050403020100a3928071f050403020100a1d1b070605040309019,0x391d070b050403020100a3328240b040302010092048280706050403020100b4807271f04030201009070605040302010030948072605040302010091707261f05030201009070b0605040302015b9071f06050a040e030201a,0x481b0706040302010047a07060572040302010052a2807060504030201002ea07060504036802010091b07060504030901529,0x1b2807060504030201002eb3817070b060504030201a,0x331d0706040302010099a0706057204030201009340b0504030201508071f06050403020187948070605040e03020100a2817260503090201009,0x1b070605720403020100a07231f0605040e03020100b071e06050a0403090201a,0x1a34140b0403020182048071f06050403020100b07064605040302010053a07060504030902018e00a072706040302010056920070605350403020100a39070b0504030902019,0x71f060504030201002ea,0x33480706040309020100a28072306050403020100a384e070b060504030201a1a07140b040309018,0x28070b0504030201002aa480727060403020100928071005350403020100a0706051304030201003ba,0x49170714050403020100a33482807060403020100a07060535040302010065a07060504030902010041a0726060504030201005da2007060504030201009491b0706050403090201a280714050a040309019,0x70b057e0403020100907060504030902015991107270b040309020194f071f0605040302019,0x48070605040302010091b070605040309020159a071e1f06050a04030201a071f0605130a03018,0x1d340b05040302018,0,0x28070b05040302018793328340b04030201848071e06050403020100a4e071006050a04030201a,0x4807060504030201879,0x3307060403020100529481b0706050403020187a28111005040309020094e07270b040302018,0x71f05040302010051907060504036002010053a48072605040309020100a0706050403090201005ea11071006053504030200a174e0b0605040302019370706050a0403090201a,0x4907140b050403020100a4807060504030201002ea07060504036809020100a284e2605040302010090710060504030201005ba,0x7c331d07060403020100a0706050403020100769481b07060504030201002eb48280726050403020100a,0x331b07060403090201907271f040e03020100907260504030201005593817071006050403020100b1b07060535040302019480706050a040302019,0x49390706050403090201a0706053c04030201009,0x28070605720403020100a20072306050403020100a20390706050403020100a,0x70605040e0302010055a072c0605350403020100a28110b05040309020191d0706050a04030901928070605130a0309019,0x4807270b0403020100948072306050403020100a071f060504030201005ea39480706050403020100a49070605040309020100a4807261f050403020100a3928070b050403090201a11070b06053504030201a4f07140605040309019,0x39481b0706050403020100b384e071006050403020100b1707260b050309020190706050403020801002ba,0x7060403020100524793328070b04030201999070605040360020100907060535040302010053a20070605040309020100a,0x70b0605040302018791b0714050403010052938070b06050403020190706051304030201003da,0x7060577040309020100a0706050403090201989491b280706050403090201b20280706050403020100a38170726060503020100a,0x3328071f0403020100928070605040309020159a07260605040302010056a0726050403090201004da284e0b0504030201807190b0504030208019,0x331d070b04030201009070b060504030201002ea28070604030201007a920072606050403020100a37070646050403020100a1b072605040309020191b071405040309018,0x221d28070b050403020100b1d28340b0504030201907271e1f04030201009,0x70605790403020100948072606050403020100a,0x1b17140504030201009384e0726060503020100a1d28070b0504030901924071006050a04030901a,0x3928240b050403020100a1107260b050403090201a1107140b0504030901917071406050a030901922070605040302080100a07140b0513040308019,0x491b0714050403020100a0706050409020100589174e1006050403020100a2407270b040309018,0x7140504030201005990706056f040309020100a1a4e0b06040302018,0x1b071405040302010059a482807060504030201002eb0706050403090201008ca480706050a0403090201a,0x7231006050403020100a280710050a0403090201a,0x7060504036002018e00a07060566040375020100a48071f06050403020187a1b280706053504030201a07840604030201008280723050403020100948280706050a04030201a]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bx:Lh = tR:=priorEq_sound (by decide +kernel)
set_option maxRecDepth 20000 in
lemma bz:btAll (fun bk => ∀ xs ∈ bk, Impossible C 10 xs.toFinset) tR:=refBuckets_all (forall_cons KA (forall_cons KB (forall_cons KC (forall_cons KD (forall_cons KE (forall_cons KF (forall_cons KG (forall_cons KH (forall_cons KI (forall_cons KJ (forall_cons KK (forall_cons KL (forall_cons KM (forall_cons KN (forall_cons KO (forall_cons KP (forall_cons KQ (forall_cons KR (forall_cons KS (forall_cons KT (forall_cons KU (forall_cons KV (forall_cons KW (forall_cons KX (forall_cons KY (forall_cons KZ (forall_cons La (forall_cons Lb (forall_cons Lc (forall_cons Ld (forall_cons Le (forall_cons Lf (forall_cons Lg (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))
def iG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x37f3363373e4559449249caa0bc3d5acf8ae51924924a396),(64,0x38e5746a12492813d63be3b77a2f4f90f8cb24906a80e37e),(64,0xb8ae4924908f5829aa9a1dcc98ae4925104c581f2a3743af),(64,0xb657a93a9f1e66c6524924904e59052e53d331ff1bbaf5c),(39,0x15a74ebd8ccbcf90cce1449241396)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Li:∀ ns ∈ iG, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iG (readRouteRows 8 (unpackWords 11 [(64,0xc401c0106404c38432b23108288b090200e008418c21484044286304250c4081e10801c110a61c230c408074c2088008070c4704b11a11c4210211e100402061363284210211e100401c810a5246384419e128430c51027),(64,0x1483846208101068471884146284931a1146508908a314d094e110118e218211271c8084820a1106510428c4044190108651487843106404a385418820c809460882186104520e10c60849184102e110410a614888492921),(64,0x12284510a5148d987080814220862884082294931a22c63084090304400c411c310c50c148220426105086204248802902102989109220c21111096200201460c2310820d3114118658421962002014a08e3102088518a1),(64,0x108184a20812c41104094210830810882052184320610c80040384100e484111c13c4484310452042048136314c40840982246a04a10c3104590b080200e508419a4046204040270c418441008244394218a23c828852861),(29,0x2204661871a614ca284418e21c208840882708118a18e1046204418a200601c010a410c190b0885)])) (by decide +kernel)))
def iH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x30b70eb0ff147e92492403d55ef3bc5f19319dc2c9240315),(64,0x33f5ee5ae38a24924a3960ccb4c91fcff72c761249241395),(64,0xaa9c4a2485b1936325eb477432654a2522a1ca20fc3fc3e5),(64,0xdd4915b71f8a249249a7ac8c209867d8db21932c5124a261),(64,0x3268bd90cbb9d24739931b5924924e3d52ca0f7ce5cbac6f),(9,23367909)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lj:∀ ns ∈ iH, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iH (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xcc3a8ba829485a88ad354430a3a428a24c8a26a89a61b49110d2669069124d1244513644524443a),(64,0xe241b44521522890e910e5d20da2eaaa4e8871317a8ebaa48886970f281845151428eb2a4888b96),(64,0x4483a89d11248348a247748308b26a88bca90651549d35483089827144d2344d317a8c9222ca9d15),(64,0x90ba88a19139a2ca0a42b08e291a28444e11524710b95144d514a28a1a280a24c88e5314a21d50e1),(64,0xa0a2ca0a2ca1a2e445888a1115a229444e128ce3162c289ac1e44a2688625083e8944810c4711228),(64,0x94446245d230854a8a28a9a2c90501d44c154826644d27448348cd2744d27448338cd26451317c30),(64,0x41a21959540b02a90501d450889502995029ba26a2c669204c8a26689722907510c24611a26444c1),(64,0x1259112022a06d214a28a1a419452148611459540ac2a9052c8954299d429ba26a306692841e4501),(64,0xc2290fa2834453220668948921a4e8988821a23c8528893248a111260d1658925448b6448c35151),(57,0x29b2234145819a28244309203ab8a28b9a2498751605520a99119963344a6694d274452)]))) (by decide +kernel)))
def iI:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xa29db1ab2aac7a192221121519183601c8a1c9d19b198629ea6221111111361a),(64,0x195310282df3de29be2a9f1bbe7dc392211112147191911302bac2a992e298c5),(64,0xbfe18a1c221111111661a18181307a2aba2aab26ee1bae6b18a3b22211111518),(64,0x111127181206e829de2a9f22aa85918a5a4111111137193221102859d6885cc1),(63,0x1902868f1bec7ad2bfe18a1f221211112619301e2b8e2afb22aec6b18a3c223)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lk:∀ ns ∈ iI, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iI (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x14cd5414d2388d3344e135096b3a42a865254d5111c28a2249448914551334593545d31459654879),(64,0x1b866a9a868a0261a86691c6d44c78554d374452145920f26e8a24a8aa6138452a2a6a890e114cd1),(64,0x918a64547d14434a07d5614d4510d15045692846ab0a6a28868a8263a8c691aa6a1a290986b19a47),(64,0x90502f49625444809a8a21a2909a6819a4b11a2809a46a1a2498ae375cd2394e5350d124c561bac6),(64,0x8b5930ac2290691487515a22699a46898252248e8b11434476151910f26a8892114c32a05410c26a),(64,0x88aa17559115514344b6245135449264d233492234521152e48a241a45888a43099a468a0252288e),(64,0x5482764c5415853348911582eb3222b32229854288a41945530b02a904e1d454888a62a0aa299a44),(64,0x48a4c89c27144520ca2a90d02544670aa42988e29222a92a623885289a6889a4689aaa9056e8a5d3),(64,0x88716145160fa290aa4148691384d220d43348548a02a90502a44a13488340cd2645133447164857),(64,0x1c22691a270906918651148348a03c89a46894241a0648a26688a0288a4184501349021443892042),(64,0x98fd1348911582eb0651149910c2614055209c3c89a4488aa175491450d11543289248b1a2691a28),(23,0x651148308b26a88ce1148368aa4a)]))) (by decide +kernel)))
def iJ:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x8b411111113191911202d8e288b2c5d81dbc2aff71af818be3d2221111141919),(64,0xe3a9f7981cd2cfc2a21111111418193103f8282abc1cdf1cdb7a2bb828b18981),(64,0x110661b403ee39cd4619d18ce1efa4c817211111202181a211049a5fc1ce93a9),(64,0x838fd189828ae2ce4d1911111110461a3171101db2d99191839fa2ce77211111),(64,0x3c8c6e1911111110111a181038f9328e39fa2ce1a721211110351a41810238f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ll:∀ ns ∈ iJ, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iJ (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x35cd42445709aac11a6731cc88a82d0aa818542a0a2688b511348d42445209aaa11a623091634495),(64,0x20ae2345d734ce43a286b122aa0a4a88794544aa0a26a160309a2a292922d08d4590d1504d5508d3),(64,0x9aaa3509511a8225245a11a2b09aaa11a2a09a62c105811a2ec1a6822082a8616544ca0c2cc45857),(64,0x2852c886160a82aa052144d1162222288a488a41748d311448a9a2488a4c88ac6a924a886150a82e),(64,0xaa22964557170526445465830a065355954165095a0d1484d6508d4488d3394e5244570bae699ca7),(64,0xf4c5092a6248838aa45154d5214cd6148d62450148a2699a46a93d40f22a9aa48aa22a15a2a9aa48),(64,0x344a15a228b05429aa2b34c9264d5254c92151512852a8a2c814d51485561fcd60c26eb1a4ab3241),(64,0x8445f2489324955244e1392249aa4488655088e10ca6490ce1b4452244532555245451622a2987d4),(64,0x386123889138a95144d514a2a0a24c88e53172290a241a443298a22a06123ba4184593162280a243),(64,0x886150a028986910e261a49d34459416a2ea9c28987110daa281a2891c545445609c511485611d92),(32,0x7d134dd25443c90a2230a2284d521ea23d5052)]))) (by decide +kernel)))
def iK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9558d64291df2af755bc375b9dd399edc743d224920c3d6),(64,0x211eb181490daffc7696a979fceba43ad9cfdfc7f2a49249),(64,0x2492482563019fdc6dc6db399753a698e9a73fdd17c89249),(64,0x3be32798fdb5364b8c961d7e3267de44a248597581f2e36a),(64,0x3a687ec7f956922b6e47d48924851459b2c944873c53dc94),(64,0x58ffa2f3ad3d7eec64c79d112490aaaa948a241b1e9bbba4),(64,0xb3ce6eda2db43265a1fc924920e51630a4892149fe5b2f3d),(26,0xd289064fb3b657ce9a1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lm:∀ ns ∈ iK, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iK (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x91a2809a8494d1164830b09614511252242887950e22874c510ca6e88612759214511243241b5877),(64,0xe445564dd80e24888612507921d05164d1140a26a87110e2c29050c8865440a41944553449238902),(64,0x245488aa415043ea2a44509514a85716857144d5144d2508d13509298a41c59110c2cb306530eaa1),(64,0x544571da21a48368a26892441c44d414222a3222848368a268921920daa2b9aa689aa688acc9122a),(64,0x54c21885520b8d15482d0aa61607110caa5f80d17507a8871340a41d44d4144923090293a2699228),(64,0x15028144d234cd154c21a8552086668aa410c82a985e1a44d350cd23085115027144d234c91450d1),(64,0x906d3684341459260430144530f242889ac906d31446c145521b041f44d2444d33451358cd248851),(64,0xbc3a8860889a4498a4314456148513514264452458308a4290aa615922ea283a8ad910ca85b8a62),(64,0x48a26c0a11450920f2648b45155029444d524c5518a22b0aa289a8e13222aaa2c0b02a9843008614),(64,0x8a22690c8a1988b23a2e0948a23a22c222b0da2c0e223b8a4c88a4939224c8a2c9a42964c38a0a24),(64,0x548290da2b0e22599a21849421a8c2d0c3cc92289865150612195a3315e57443244457444300da21),(64,0x154527559115422a3222905ca8aa41606d172222b0a62b0a6290a6268a4eb3a2d44d58644520a951),(64,0x448993485165052228924a244ca24aa09220fa26a2226906d1485a892a81506d2154531545314853),(4,72999)]))) (by decide +kernel)))
def iL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x85120c3a5e643fcc6fd79b0ef7432eebff1c88924920f556),(64,0x90cb219ae5273ae3bfddcfcffb4514864c7c249248397549),(64,0x52f3adf9fd0f9ca249061ea052e919f0924920958c462217),(64,0x7b99729ff395d329e656dcea94924920f3d6311094b4c536),(64,0x888527f96cad969c7f922df2bf193287464920d514312258),(64,0x26a8b180c9e1f4eb4c96f334f8cd6c32657a90a24908f551),(55,0x6a242db476f8b4bd59fa93af8eb8cf6e74cc89249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ln:∀ ns ∈ iL, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iL (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x9043044456150561505115056145d634c92159144454888b4c345d8585550a82a9aa4163221960ba),(64,0x54915259921444e0ea42b8a82b8a8288a82b8a2eb9a6490ae20b5111743014430c05e15542d0aa6a),(64,0x30a4c30a4413442c304c8924c11224da22d1c223c8522d2224d1a22ab24288966932a28954aa87d3),(64,0xd82a0b82a0a26c0b8334434a8a28a9a24ca2218865338a4e38a4413c42c384c8934888601f4453),(64,0x5502c0aa4140b912f4d14a22809cc8306d5344e358cc350cd515a8689c6919868192a899a83b4852),(64,0x14cd460cd2488528a82a145540b42a9054284453154512a0532a053351a334902645130ea280a051),(64,0xa0a22e0a2184851160514515224501d4951450d20e22b0ac515502e0aa415861114c56144a914cc9),(64,0x3446548c5288c8b1948c23a22b222d0f22312445128468904913a22ba22a15222b222815c24c1a2a),(64,0xd282e449514c5514cd1754d1158308aa81486911485314853345d22451355c308aa8140a91151d8),(64,0x4aca6924468a9114a264d5152144491445564830b89ac8898a9a24c448ba88ea1944965445441288),(42,0xd2344d2545926591275d122443698a23486d30ea22c052289528)]))) (by decide +kernel)))
def iM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x517303da57d796af3436fd55d719f48a6d0cd91249242516),(64,0x58985121ffb1b253fe3258e4b4c8b4915b7194fe8924920f),(64,0xd23d1e3a7995be73f5d0fd657f7cf7867ba19a2249248316),(64,0x322d2456dcb9fd144920c3960679f1f94a4924904ac6b20c),(64,0x3b6bd63a4f8eb6f367b1d932a74449241ae2a6b217d71a6f),(64,0xea6bdcb4eb643a5864a492490d7553642db2d9d93a7be76c),(54,0xc0a5f9fe8924921159908cbfc464d9d97ab2c56c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lo:∀ ns ∈ iM, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iM (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x358d434c9692a22a8b4288616551134454888695559140f24194455164d15599444d114b22195075),(64,0x49224905449052a8ac26b9326aa224c9a21f5856a2a62a8b0c9a45155954154572a455144570a451),(64,0xa2a41124520db028a5110c24ea0a2d4445299a2c0bd1110584892417124162a2f14a468a42b44441),(64,0x34c944543290a22da24a8898c8896144d5464832a1384898262452149224912290a4912555208946),(64,0xa0a22a854288a42a890293a2699a8a90a22ea24a889cc889a154d1444851154291445215447149d1),(64,0x88a4139a2eaa19209c388865517c068a244d8a511482c0fa229056a8aa6288ac194c3a886140d228),(64,0x44497344d40c2428890ab061214447349540c2271622484c3e88a4148a218542a648290d224f483e),(64,0x9a45494e69934a88c310c26f44d5440a86345c13488821c82aa1d316dd17061168711244d4744d2),(64,0x24d8336122e07d9607191e05164d166451268b8892222a34e2e90cd38ba6345c13495548aa634430),(64,0xe0aa2e0aa4d8ba12685c21a42a0a62a0a6ea1a44190681783ec39181585315853159a4b306691466),(16,0x12e28a341b49a893042)]))) (by decide +kernel)))
def iN:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0x10081806880127c4608d100820d0c20261020a1c0d051d13162ff4bb70b8f279c24092688060d034),(64,0x26028707eb3b9e0e38fce1b3d0615c085e688040c03440073c0604bc097931b590a980c2b8149cd),(64,0xce1142d9a2020300c888208044f301b405281f1a4e7c2bf031a60319f830fc1b440e0d10141b0688),(64,0x11c19184036a498c848fe094e0612557cde6071e16438344030641a1182023b067030ec98c76b82),(27,0x200ab705025e48c71bfd0617a0e3c4f1a2)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lp:∀ ns ∈ iN, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iN (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xf26b1ac3a88b62a8b62a8a22a8b6a8b111584d325a22c8f126a242b51888ac3ea1303c4961c4853),(64,0x1505234452745210f241a443090ae184d110e26a44c908aaaab0613444389a43898b600d2e18595a),(64,0x9283092a6e886d354436ba221c4921c4856344d2344d20a4914865114c3c887d20da2248b0915059),(64,0x289869232c8b47488f869a2290ca2cc2a21f4c3688d2490aa248a4149a22aba2909a63f519644438),(64,0x98a96644d375c329b43888aa159a22a85c2890af20691461910c05888a4151a22905828904d106d1),(64,0x21564348568b05890a6230a441a86693222a8d230fa2a1d222e9a6288a8169a22a058289a6c8b026),(64,0x34dd221d0430aa64454150a22a4d41c449b148541243a92441a6051460d124911449111485511c52),(64,0x89a6b19a2a44855158551585115855144d3748862902c0b09144c388b1111605716057144570a851),(64,0x4b222a0aa28baa690c851948820f5140711168d36455366513142489ba4a08b42a2962a0a22a0542),(42,0x51407110f24e88a6142a668a02690a22b8ac28bac690ce618e51)]))) (by decide +kernel)))
def iO:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x8d2b981d3c431111471844204bae4f9f158ec58ef3c8c1d8a481942111114719),(64,0x44ee4ef3cac3beb4fde1ca1e1c3d6111115181841104b8f4bae588959cc6b2a),(64,0x5aca2e643111104619344202b8c1cd289f1cb84cef5abe3642111110561a1311),(64,0xa74110182fa82fad24cfe3ee1e82f66111110571941102b8c1e9289f1ccc4cfb),(64,0x8818a619431111027196362205cc4bae29e96ca3ca958a818a31942111110671),(21,0x402288d4bae599b3dfa1c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lq:∀ ns ∈ iO, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iO (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0xa1222b84d234cd1350e5395511202184d511203092c5235c4488ac1348d3344d4314c8a9242b087f),(64,0x1584488aa128a4434d1521514110a21e0515483c9aa41405530ea8a891088a42692c469a8668a026),(64,0x288a498a2724593744d20a0229ba2a448d3588d159a22b04c2910d34588611a28448d3488d14a244),(64,0x34c9415886b1222b04d3314c535124124e2c88d1504d341d8728ac52505221a4488a4134c45122a2),(64,0x88aa1a50d524dd275512444309204aa2a623924ca8bec8a241c50309a46944cd45904b40b62345a1),(64,0xa8b2194c3890a1115aca89a6b18a26a8a269244689ac3d51137545114953444309a861851554483c),(64,0x89a4a11a2385113144d5144d24089144cd4645120d222a865425456549d54491144922451123924c),(64,0x34922350e5614d314434b1a2e98a2194d11549510da4a1226892092644590cac19483c89a6289aa2),(64,0x14829144540c26a90501b452289ace8a0513542598751649110c28688ac689a4b11a82f4cd1158d1),(64,0xb0a46a1a6693222b3222905628a26a8aa41506d158a26b045215c55148d434cd26445545c9115591),(64,0x89aae8a0513502293282d2c5264c5848a41b45541284a9890215a2691a2692a81605530b43a90ae2),(55,0xb910e243944d7358d274516545520a5d13551135cd63489144c911511115dd67490e)]))) (by decide +kernel)))
def iP:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x3394311110361962203d8975de5f959a8599d5ae82dbd2ddc71d211111041919),(64,0x96ae69f59ce28cf1adc7dc43961111107181918104bae59cf4bdc1f9b2dee18a),(64,0xc2dca588f4eae3ca5843111101718501b8a7d411111110211a43313204ffc4ff),(64,0x1918201c8c19bb5ef1ba3bad58a3cd86de1e81b2a421111103191a01ea4de1de),(64,0xbe81dfb2dca1e81b3d43111102619205adb1cc58e3cd86de1e818d4211111026),(11,2219839895795)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lr:∀ ns ∈ iP, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iP (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x314c50a8308aae16061168a26b0485214d1350d321488a9222a04541424b148d612a2250a46a0893),(64,0x88a413a26a9050e89ace89c5135422f852c88a48b865355c5a42968345a135d4434cc5314d1358d3),(64,0x84ce69065154c7688a42a0ac291a6691a2c92a6149241b44d64445215055148d3348914509115438),(64,0x849e291aa234c9214c4488a61350661a2c490a6214cd1548290da2a144d50aa4148a269849b0ca21),(64,0x86e0145520a24c8a28915c30a0d284b86692c468b026a1aa490aa22445509a85314c29b24a889a1),(64,0x74830889418496244dd2509511e5d14585691a86a9a43b44d434cd218aa75459455828748d5744d3),(64,0x66055645541448a0ea8e88ac150a2750aca60ac6aaca68ac26a13d3149511624c12a66945d215c4a),(64,0xb22a1944e135104345013545a9a248887121ea229071111c30920489b24a887a490a21854572a5d2),(64,0x34503b51131445309c51348e2344e899a84a445339a4689a41b44474490245112389511cc9415222),(31,0x12a231a428861235512644d3144530a05134902)]))) (by decide +kernel)))
def iQ:List NodeSpec:=readDeltaNodes 8 (varNats 4 (unpackWords 5 [(64,0xd8421084210158920842006170c649c4c5e456c8c44468f83014681ed499c0ba1a0421084210158a),(64,0xb4875f96fe1dc3408421084202a5410884035959ba61027ba4a7915ea33217ea2ff05fc937354e44),(64,0x806840c402eee5de84981a9324faade8f00dc2b0842200d0810821006b01d782bec91d925217f63),(64,0x5271721af02745690ab115202cd85068681084210840552c6200845eece6d50da890f8d162108441),(64,0x8421080cb51c651080ae0b7015f68cc519c0bfb1da43afcb7f0b4288421084210192a3890200616),(35,0xca11080da3ac782b8246be20ff85bc076b1e020d021)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ls:∀ ns ∈ iQ, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iQ (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x78e510c51114c5514c5514c5514c550c262b946519462a14d11344d14c50938523504888a46988b6),(64,0xc2a2a90ba2cb4311656d1645d164d10c0269384815d02a0ac2a0ac2a0ac2a0ac185057310c432361),(64,0xf86517871112c5812c580c2429984811442a2076cb830cbd121f034e2b4890ae2c0ae2c0ae2c0ae2),(64,0x6447214452b8a62b0a62b2a28b8a4180aa2e8aa68862135dc2b0a651305a2305a0c2829988a21422),(64,0x154540fa22b054688ac162a2e4458128a8524a6890a226ba225b222507122ca22cba42a458a9ba4a),(64,0x88ae688a8689a662aca691a22b9a22a1a269990a31a45424a299a4288aee92222c3a4184455150d1),(64,0x99a8691a2699a8691a2732cc2f54d3350d2344e851cc8498d50fc528b2829445734454344d31ca46),(64,0x89c688accd304cb144cb145e1707d409aa688615687d2268920924c8b0540924381a6e91a2aa2a46),(64,0x1582a545e88b855150a4d4d921444c7444d76181c493e8ac3c88be2865d81449519c67144eb08d62),(64,0xb098e90a22c49a244dd2609511743e90a22bba4888b2e9222ac0a22a8a8a8954289141f44560a8d1),(64,0xd24c66c593691817281a44560c0551c0553b4551745534431445e8a12d345c4e1da41809532e224)]))) (by decide +kernel)))
def iR:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xa9a1e8382c1211110618195cea1ad4911111110011a5cea1ac4911111110011a),(64,0x4b9c3b893cd86de1e81de1111111047197352202dc81cfc3fcb2eea29fd299c2),(64,0xc18e95dc828f11111110319195414d8a218b82bc12111100618721a03add189d),(64,0x11110271a24dca7ae5ced5dfa1b81211110051832078b4cbb7e83cfa4ccf218e),(34,0x2027b4cde19eb19ee4cdd5e881991b4912)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lt:∀ ns ∈ iR, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iR (readRouteRows 8 (varNats 4 (unpackWords 5 [(64,0x1485a148d17222d1e26b12c4648a42c8a468b1115a2469929114926a0a228514244d14489511c400),(64,0x48ac68ad1150aa2a1472987d21644a9921114904920520d222e485015452660573551465da2688ca),(64,0xd95113545a2aa22baaa194c5689aa699a23b48d534c91450d21dacd15a22a0aa2a0aa1a445740ac8),(64,0x925d40da6e92a8a9a162b8b62b9a8699a42f450a1585a158d434cd2399860da2aa2261e45590faa2),(64,0x644d3152490e244c5454a205aa13d15506290e5344913451130d1550ca8691aa6a07d10fa63b4476),(5,2973142)]))) (by decide +kernel)))
def iS:List NodeSpec:=readDeltaNodes 1 (varNats 2 (unpackWords 3 [(52,0x2429e23ec90cf32977eb7f61d72ea5289243396)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lu:∀ ns ∈ iS, Impossible C 11 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J bz (by rw [← bx]; exact (checkNodesRoute_sound iS (readRouteRows 1 (unpackWords 11 [(30,0x210650c27941096510c084e30a5486024c1c8448401d514e14c4084010071c2008040c100401d0101d)])) (by decide +kernel)))
def Lv:BT (List (List Nat)):=refBuckets E [iG,iH,iI,iJ,iK,iL,iM,iN,iO,iP,iQ,iR,iS] #[1510187048,27,1610936371,0,72,69633,0,49,0,0,54,106508,1577230375,327703,1040404525,59,87,8,0,311332,48,92,0,1493516309,155680,0,60,299030,218148866,167970,1308700675,68,1241657360,282667,0,922927129,331837,81938,10,0,47,29,348184,91,266255,307230,6529524965390,0,50,290853,97,0,229422,135175,57,1443102726,93,213001,315397,274495,360479,82,1392623620,0]
set_option maxRecDepth 20000 in
lemma cU:btAll (fun bk => ∀ xs ∈ bk, Impossible C 11 xs.toFinset) Lv:=refBuckets_all (forall_cons Li (forall_cons Lj (forall_cons Lk (forall_cons Ll (forall_cons Lm (forall_cons Ln (forall_cons Lo (forall_cons Lp (forall_cons Lq (forall_cons Lr (forall_cons Ls (forall_cons Lt (forall_cons Lu (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def tS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xffaf8cf94309249401caa064a65c8c3cdf4f91924924a3d5),(64,0x997249249062ab058c7a1b32d3ab14b1424925027aaaa9a1),(64,0x867c66e7c8e1249248272c6120ff158a6e7c3a43bd37434c),(64,0xfc9449211aa8723994f49d31fe287e24924827aa1dc74a75),(62,0x104e9f61f2af71f2a962e4924908f5503ed3ff5f65e9f21)]))
def tT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5e3c9124924e5152c920d94cdb3beb8e6c64c5124924e395),(64,0xd2e864ff99eec7a24924835459450940cf6c32ef5c4cc9e6),(64,0x364996d31931f51249242aa2c61641f79d3ce6ed71bb4a61),(64,0x53e8a4dced263265f124924287aa6148a243c67921c7fbfa),(64,0xf2e56c952b3ece73263f2289241a7aa6244a20eb8ef3d3ac),(64,0x374eb7914bf1fd1249241aaac0cbac7f92492412aa6c878c),(36,0x4cb0fdd0c9275768adbd4f2bd7e)]))
def tU:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x51819522112105a3bd1ce48f1afb4981ba819a2948fb49ee3811111110181b19),(64,0x9d4cfa5be186411111110571a131101c3d84bae4f8f33baa1dbc1e5941111111),(64,0x101871a315111201b84fae1f18e5a1e1942111110186197411038da1fe81de5a),(64,0xee4786c1e3c431111075187311211069e4bae59c91b82fca1adc7dc394111111),(64,0x11110618191a71104bae59ef5ace58ef2cfa2d881f412111105619181711204f),(36,0x7111202cda1e8d5bd1ce4f881e1ca1e3d421)]))
def tV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8a9648374d949f1beeea7b72da7a62df78f1b0924920d515),(64,0x54a249071eab41272c3a7fcef263befceb3c5b42a924941a),(64,0xdd6df63e43a2a8924838f54c31920c4f4f5dfb23e6f14b16),(64,0x76d48cf71f27a69faece424924867aa618c9093bf1dedaf6),(64,0x30c2c83f6c67957b8ddbadbc874e7cc7c8bc289241ca28d0),(64,0x8520ed8efdddb8d9be5e69cfde29edc7c8e9b0924920f516),(59,0x7b30a412f3fcacf7a9275bdd8f90fd4924920f3953d9)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchLw:∀ b ∈ ([tS,tT,tU,tV]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 12 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J cU (by decide +kernel)
def tW:List NodeSpec:=readDeltaNodes 2 (varNats 2 (unpackWords 3 [(64,0x289241e7aa5208c3bffd2536f16da75e6d8cf0924920c515),(50,0xc30a2439e63a598dfbf57c77cea7b71f22ea5)]))
set_option maxRecDepth 65000 in
set_option maxHeartbeats 0 in
lemma batchLA:∀ b ∈ ([tW]:List (List NodeSpec)), ∀ ns ∈ b, Impossible C 12 (nodeValsBT E ns).toFinset:=blockGroup K 12 (by decide) H I M J cU (by decide +kernel)
def LB:BT (List (List Nat)):=refBuckets E [tS,tT,tU,tV,tW] #[25,1,11,21,19,0,0,0,0,0,20,0,22,14,0,29,0,18,0,31,0,0,0,17,0,9,0,0,5,0,7,0,0,0,24,16,28,49156,15,0,0,23,30,27,0,26,0,0,131082,0,0,8,0,6,33,0,0,0,12290,13,0,34,0,0]
set_option maxRecDepth 20000 in
lemma LC:btAll (fun bk => ∀ xs ∈ bk, Impossible C 12 xs.toFinset) LB:=refBuckets_all (allCat batchLw batchLA)
def tX:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0xd91249241e7aa6121cd15f54c743bc267e6dc4924920c515),(64,0x3e478c24924850e54d48960f9775b7cedf8dda5567c64db3),(64,0x325c94d969d6d152492483cf55427125037637dd0cb6c3b7),(64,0x49224921290eb949cff8ff948512485ce50c30a241b3ecbe),(59,0x6244940ef2e311d245a6fd6df674ff94a492490a28a9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LD:∀ ns ∈ tX, Impossible C 13 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J LC (by decide +kernel)
def LE:BT (List (List Nat)):=refBuckets E [tX] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,4,0,0,0,0,0,0,0,0,0,0,5,0,0,0]
set_option maxRecDepth 20000 in
lemma LF:btAll (fun bk => ∀ xs ∈ bk, Impossible C 13 xs.toFinset) LE:=refBuckets_all (forall_cons LD (fun _ h => (List.not_mem_nil h).elim))
def tY:List NodeSpec:=readDeltaNodes 1 (varNats 2 (unpackWords 3 [(45,0x1491a81932f8d87dcdf95fb8924920f3d4)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LG:∀ ns ∈ tY, Impossible C 14 (nodeValsBT E ns).toFinset:=blockOk K 12 (by decide) H I M J LF (by decide +kernel)
def LH:BT (List (List Nat)):=refBuckets E [tY] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]
set_option maxRecDepth 20000 in
lemma LI:btAll (fun bk => ∀ xs ∈ bk, Impossible C 14 xs.toFinset) LH:=refBuckets_all (forall_cons LG (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LJ:Lower N C 15:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) LI (by decide +kernel)

def edgeFn (x:Fin 8 → Bool):Bool:=(x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
def edgeList:List Nat:=[0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]
def graphFn (x:Fin 8 → Bool):Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)
def witness:List Gate:=[⟨.or,[1,3]⟩,⟨.or,[2,4]⟩,⟨.or,[3,6]⟩,⟨.or,[1,7]⟩,⟨.or,[6,7]⟩,⟨.or,[0,9]⟩,⟨.or,[5,12]⟩,⟨.and,[10,11]⟩,⟨.and,[13,14]⟩,⟨.and,[0,9]⟩,⟨.and,[2,4]⟩,⟨.and,[8,12]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩]
theorem witnessBasis:∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2:=by
  simp [witness]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem graphCorrect:∀ x:Fin 8 → Bool, edgeFn x = graphFn x:=by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tableCorrect:∀ r:Row, edgeFn (evalInput r) = C.testBit r.val:=by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect:∀ r:Row, Circuit.eval ⟨witness,23⟩ (List.ofFn (evalInput r)) = C.testBit r.val:=by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem conclude (gates:List Gate) (o:Nat) (legal:(∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2))
    (spec:∀ x:Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = graphFn x) :
    ∃ (gs:List Gate) (out:Nat), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length ≤ gates.length ∧
    ∀ x:Fin 8 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = graphFn x:=by
  have eq:∀ x:Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeFn x :=
    fun x => (spec x).trans (graphCorrect x).symm
  obtain ⟨gs,out,legal',size,compute⟩:=replace_of_lower C (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 15 LJ witness 23 (by decide) witnessBasis edgeFn tableCorrect
    witnessCorrect gates o legal eq
  exact ⟨gs,out,legal',size,fun x => (compute x).trans (graphCorrect x)⟩
end PEqualNP.Outside.L_meta_52830
theorem PEqualNP.Outside.L_meta_52830 :
  ∀ (gates:List PEqualNP.CircuitLowerBounds.Gate) (o:ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j:Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x:Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates':List PEqualNP.CircuitLowerBounds.Gate) (o':ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x:Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]:List ℕ).getD (2 * i + 1) 0) false = true):=by
  intro gates o legal _ spec
  exact PEqualNP.Outside.L_meta_52830.conclude gates o legal spec
