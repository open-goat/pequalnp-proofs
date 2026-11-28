import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_52830


open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
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
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
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
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
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
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    decide (zDead < 256) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 256) (hd : zDead < 256) (ho : o < 256)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 8) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
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
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
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
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
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
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
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
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
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
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩,
        (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
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
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^256 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
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
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (255 ^^^ (1 <<< j)) ||| mask) % 256, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound

def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim


def readWord (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => (x &&& ((1 <<< w) - 1)) :: readWord w n (x >>> w)

def unpackWords (w : Nat) (x : List (Nat × Nat)) : List Nat :=
  x.flatMap fun (n, v) => readWord w n v

def readChoices : Nat → List Nat → List (Nat × Nat × Nat)
  | n + 1, a :: b :: c :: rest => (a,b,c) :: readChoices n rest
  | _, _ => []

def readSpecs (cs : Array (Nat × Nat × Nat)) : Nat → List Nat → List PoolSpec
  | n + 1, s :: k :: rest =>
      (s, (rest.take k).map fun i => cs.getD i (0,0,0)) :: readSpecs cs n (rest.drop k)
  | _, _ => []

def readNodes : Nat → List Nat → List NodeSpec
  | n + 1, p :: q :: r :: rest =>
      ((rest.take p), ((rest.drop p).take q), ((rest.drop (p+q)).take r)) ::
        readNodes n (rest.drop (p+q+r))
  | _, _ => []
def varStep (b lim mask : Nat) : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | a :: rest, acc, off =>
    let q := acc + ((a &&& mask) <<< off)
    if a < lim then q :: varStep b lim mask rest 0 0
    else varStep b lim mask rest q (off + b)

def varNats (b : Nat) (x : List Nat) : List Nat :=
  let lim := 1 <<< b
  varStep b lim (lim - 1) x 0 0

def unruns : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, prev =>
      let y := x >>> 1
      if x &&& 1 == 0 then y :: unruns xs y
      else List.replicate y prev ++ unruns xs prev

def shifts (xs : List Nat) : List Nat :=
  (xs.foldl (fun (v, ys) x => let q := v+x; (q, q::ys)) ((0,[]) : Nat × List Nat)).2.reverse

def readDeltaNodes : Nat → List Nat → List NodeSpec
  | n + 1, p :: q :: r :: rest =>
      (shifts (rest.take p), shifts ((rest.drop p).take q), shifts ((rest.drop (p+q)).take r)) ::
        readDeltaNodes n (rest.drop (p+q+r))
  | _, _ => []

lemma someSlice {R T d k} (h : Slice R T d k) :
    ∀ p : Nat × Nat, some (d,k) = some p → Slice R T p.1 p.2 := by
  intro p he
  cases he
  exact h

def lookSpec (count : Nat) (cs : Array (Nat × Nat × Nat))
    (chunks : Array Nat) (index : Nat) : Option PoolSpec :=
  if index < count then
    let code := (chunks.getD (index / 30) 0) >>> (29 * (index % 30))
    let sl := code &&& 255
    let ids := [(code >>> 8) &&& 127, (code >>> 15) &&& 127, (code >>> 22) &&& 127]
    some (sl, ids.filterMap fun i => if i = 0 then none else cs[i-1]?)
  else none

def nodePools (nodes : List NodeSpec) : List Nat :=
  (nodes.flatMap fun x => x.2.1).eraseDups

def lookupPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : Nat → Option PoolSpec) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma lookupPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : Nat → Option PoolSpec} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (lookupPoolsBT pdepth W raw slices pspecs used) := by
  unfold lookupPoolsBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc

lemma blockOk {W : BT Decor} {raw pos neg T slices autos prev k nodes}
    (specs : Nat → Option PoolSpec) (depth : Nat)
    (hT : T < 2^256) (pairs : goodPairs T pos neg)
    (wf : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (sl : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices)
    (au : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (pv : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prev)
    (ok : checkNodesBT W T (fullMask pos.length)
      (lookupPoolsBT depth W raw slices specs (nodePools nodes)) autos prev k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset :=
  checkNodesBT_mem hT pairs wf (lookupPoolsBT_sound sl) au pv ok

def tabBT {α : Type} (f : Nat → α) : Nat → Nat → Nat → BT α
  | 0, base, _ => BT.leaf (f base)
  | d+1, base, gap => BT.node (tabBT f d base (2*gap)) (tabBT f d (base+gap) (2*gap))

lemma tabBT_all {α : Type} {P : α → Prop} {f : Nat → α} (all : ∀ i, P (f i))
    (d base gap : Nat) : btAll P (tabBT f d base gap) := by
  induction d generalizing base gap with
  | zero => exact all base
  | succ d ih => exact ⟨ih base (2*gap), ih (base+gap) (2*gap)⟩

def bucketRefs : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, v => if v = 0 then [] else ((v &&& 4095) - 1) :: bucketRefs k (v >>> 12)

def readNodeRef (blocks : List (List NodeSpec)) (i : Nat) : Option NodeSpec :=
  (blocks[i / 8]?).bind fun b => b[i % 8]?

def refBuckets (W : BT Decor) (blocks : List (List NodeSpec)) (rs : Array Nat) : BT (List (List Nat)) :=
  tabBT (fun i => (bucketRefs 1024 (rs.getD i 0)).filterMap
    fun j => (readNodeRef blocks j).map (nodeValsBT W)) 6 0 1

lemma refBuckets_all {W : BT Decor} {blocks : List (List NodeSpec)} {rs : Array Nat} {T k : Nat}
    (hall : ∀ b ∈ blocks, ∀ ns ∈ b, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (refBuckets W blocks rs) := by
  apply tabBT_all
  intro i xs hx
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hx
  unfold readNodeRef at he
  cases hb : blocks[j / 8]? with
  | none => simp [hb] at he
  | some b =>
    cases hn : b[j % 8]? with
    | none => simp [hb,hn] at he
    | some ns =>
      simp only [hb, hn, Option.bind_some, Option.map_some, Option.some.injEq] at he
      exact he ▸ hall b (List.mem_of_getElem? hb) ns (List.mem_of_getElem? hn)


def aE:List Nat:=varsOf 21
def aB:Nat:=0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0
def dO:List Nat:=[17,20,5,5,20,17]
def dP:List Nat:=[16,16,1,4,4,1]
def hF:Nat:=fullMask 6
def hH:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,51,3)]
def vR:List (Nat × Nat × Nat):=[]
def cI:BT Decor:=buildWiresBT 2 hH vR
def vS:List (List (Nat × Nat)):=[[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def dQ:BT (List (Nat × Nat)):=btOfList 3 vS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vT:goodPairs aB dO dP:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vU:∀ x ∈ hH, faithful dO dP x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vV:btAll (fun x => faithful dO dP x ∧ x.1 < 2^256) cI:=buildWiresBT_faithful vU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vW:btAll (fun sw => swapsValid sw = true ∧ permWord sw aB = aB) dQ:=btAll_ofList (autos_of (by decide +kernel))
def vX:List (Option (Nat × Nat)):=[]
def hI:BT (Option (Nat × Nat)):=btOfList 1 vX
def vY:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 0 []
def dR:BT (Option BoundPool):=buildPoolsBT 1 cI aE hI vY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma vZ:btAll (fun o => ∀ p, o = some p → Slice aE aB p.1 p.2) hI:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aE aB p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma wa:btAll (fun o => ∀ c, o = some c → ValidPool aE aB c) dR:=buildPoolsBT_sound vZ
def dS:BT (List (List Nat)):=BT.empty
lemma wb:btAll (fun bk => ∀ xs ∈ bk, Impossible aB (3 - 1) xs.toFinset) dS:=trivial
def hJ:List NodeSpec:=readDeltaNodes 1 (unpackWords 2 [(6,1283)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wc:checkNodesBT cI aB hF dR dQ dS 3 hJ = true:=by decide +kernel
def hK:List NodeSpec:=hJ
set_option maxRecDepth 20000 in
lemma wd:checkNodesBT cI aB hF dR dQ dS 3 hK = true:=wc
def we:BT (List (List Nat)):=buildBucketsBT cI hK
set_option maxRecDepth 20000 in
lemma wg:btAll (fun bk => ∀ xs ∈ bk, Impossible aB 3 xs.toFinset) we:=buildBucketsBT_sound (by decide) vT vV wa vW wb wd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aG:Lower aE aB 4:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) wg (by decide +kernel)
def aU:List Nat:=varsOf 149
def aV:Nat:=0xfffffffffffffffffffffffffffffffffafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aZ:Lower aU aV 5:=lift_of (z:=128) (o:=0) (essPairs:=[(VAR 7,0,128)]) (by decide +kernel) aG
def hM:List Nat:=varsOf 212
def hN:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wh:Lower hM hN 5:=carry_of (swaps:=[(5,6),(3,6),(1,6),(4,6),(6,7),(2,6),(0,4)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def dc:List Nat:=varsOf 69
def dd:Nat:=0xfafafafafafafafaa0a0a0a0a0a0a0a0fafafafafafafafaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma de:Lower dc dd 4:=carry_of (swaps:=[(5,6),(4,6)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def dT:List Nat:=varsOf 81
def dU:Nat:=0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma hO:Lower dT dU 4:=carry_of (swaps:=[(5,6),(3,6),(4,6),(2,4)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def dV:List Nat:=varsOf 84
def dW:Nat:=0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma hQ:Lower dV dW 4:=carry_of (swaps:=[(5,6),(3,6),(1,6),(4,6),(2,4),(0,2)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def aP:List Nat:=varsOf 85
def aw:Nat:=0xfffffafafffffafafafaa0a0fafaa0a0fffffafafffffafafafaa0a0fafaa0a0
def dX:List Nat:=[17,20,5,5,20,17,65,80,68,80,65,68]
def dY:List Nat:=[16,16,1,4,4,1,1,16,4,64,64,64]
def cd:Nat:=fullMask 12
def hU:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1133,100),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2334,280),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,691,131),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,4032,3584)]
def wi:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,1,2),(1,4,5),(3,2,4),(3,3,7)]
def bz:BT Decor:=buildWiresBT 4 hU wi
def wj:List (List (Nat × Nat)):=[[],[(4,6)],[(2,4)],[(2,6)],[(0,2)],[(0,4)],[(0,6)],[(4,6),(2,4)],[(4,6),(2,6)],[(4,6),(0,2)],[(2,4),(0,2)],[(2,6),(0,2)],[(2,4),(0,4)],[(4,6),(0,4)],[(2,6),(0,4)],[(2,6),(0,6)],[(4,6),(0,6)],[(2,4),(0,6)],[(4,6),(2,4),(0,2)],[(4,6),(2,6),(0,2)],[(4,6),(2,4),(0,4)],[(4,6),(2,6),(0,4)],[(4,6),(2,6),(0,6)],[(4,6),(2,4),(0,6)]]
def bN:BT (List (Nat × Nat)):=btOfList 5 wj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma df:goodPairs aw dX dY:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wk:∀ x ∈ hU, faithful dX dY x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dg:btAll (fun x => faithful dX dY x ∧ x.1 < 2^256) bz:=buildWiresBT_faithful wk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dh:btAll (fun sw => swapsValid sw = true ∧ permWord sw aw = aw) bN:=btAll_ofList (autos_of (by decide +kernel))
def wl:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,4),some (subcubeFast 4 0,4),some (subcubeFast 16 0,4),some (subcubeFast 64 0,4)]
def hV:BT (Option (Nat × Nat)):=btOfList 2 wl
def wm:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 4 (unpackWords 2 [(8,12816)])
def bO:BT (Option BoundPool):=buildPoolsBT 2 bz aP hV wm
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wp:Slice aP aw (subcubeFast 64 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=aE) (qGoal:=aB) (by decide +kernel) aG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wq:Slice aP aw (subcubeFast 16 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dc) (qGoal:=dd) (by decide +kernel) de
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wr:Slice aP aw (subcubeFast 4 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dT) (qGoal:=dU) (by decide +kernel) hO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wt:Slice aP aw (subcubeFast 1 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dV) (qGoal:=dW) (by decide +kernel) hQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wu:btAll (fun o => ∀ p, o = some p → Slice aP aw p.1 p.2) hV:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aP aw p.1 p.2) (forall_cons (someSlice wt) (forall_cons (someSlice wr) (forall_cons (someSlice wq) (forall_cons (someSlice wp) (fun _ h => (List.not_mem_nil h).elim)))))
lemma di:btAll (fun o => ∀ c, o = some c → ValidPool aP aw c) bO:=buildPoolsBT_sound wu
def dZ:BT (List (List Nat)):=BT.empty
lemma wv:btAll (fun bk => ∀ xs ∈ bk, Impossible aw (3 - 1) xs.toFinset) dZ:=trivial
def hX:List NodeSpec:=readDeltaNodes 2 (unpackWords 3 [(16,0xe48021049614)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ww:checkNodesBT bz aw cd bO bN dZ 3 hX = true:=by decide +kernel
def hY:List NodeSpec:=hX
set_option maxRecDepth 20000 in
lemma wx:checkNodesBT bz aw cd bO bN dZ 3 hY = true:=ww
def ea:BT (List (List Nat)):=buildBucketsBT bz hY
set_option maxRecDepth 20000 in
lemma wy:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 3 xs.toFinset) ea:=buildBucketsBT_sound (by decide) df dg di dh wv wx
def hZ:List NodeSpec:=readDeltaNodes 3 (unpackWords 3 [(29,0x5248028709209a09249255)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wz:checkNodesBT bz aw cd bO bN ea 4 hZ = true:=by decide +kernel
def ic:List NodeSpec:=hZ
set_option maxRecDepth 20000 in
lemma wA:checkNodesBT bz aw cd bO bN ea 4 ic = true:=wz
def eb:BT (List (List Nat)):=buildBucketsBT bz ic
set_option maxRecDepth 20000 in
lemma wB:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 4 xs.toFinset) eb:=buildBucketsBT_sound (by decide) df dg di dh wy wA
def ie:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(16,0xac8248249125)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wC:checkNodesBT bz aw cd bO bN eb 5 ie = true:=by decide +kernel
def ig:List NodeSpec:=ie
set_option maxRecDepth 20000 in
lemma wD:checkNodesBT bz aw cd bO bN eb 5 ig = true:=wC
def ec:BT (List (List Nat)):=buildBucketsBT bz ig
set_option maxRecDepth 20000 in
lemma wE:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 5 xs.toFinset) ec:=buildBucketsBT_sound (by decide) df dg di dh wB wD
def ii:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(17,0x81212011101110644)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wF:checkNodesBT bz aw cd bO bN ec 6 ii = true:=by decide +kernel
def ij:List NodeSpec:=ii
set_option maxRecDepth 20000 in
lemma wG:checkNodesBT bz aw cd bO bN ec 6 ij = true:=wF
def wH:BT (List (List Nat)):=buildBucketsBT bz ij
set_option maxRecDepth 20000 in
lemma wI:btAll (fun bk => ∀ xs ∈ bk, Impossible aw 6 xs.toFinset) wH:=buildBucketsBT_sound (by decide) df dg di dh wE wG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bE:Lower aP aw 7:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 6,1,65)]) (by decide +kernel) wI (by decide +kernel)
def ik:List Nat:=varsOf 133
def il:Nat:=0xfafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wJ:Lower ik il 4:=carry_of (swaps:=[(6,7),(5,7),(4,7)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def im:List Nat:=varsOf 145
def io:Nat:=0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wK:Lower im io 4:=carry_of (swaps:=[(6,7),(5,7),(3,7),(4,7),(2,4)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def ip:List Nat:=varsOf 148
def iq:Nat:=0xfffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wL:Lower ip iq 4:=carry_of (swaps:=[(6,7),(5,7),(3,7),(1,7),(4,7),(2,4),(0,2)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def ir:List Nat:=varsOf 149
def iu:Nat:=0xfffffafafffffafafffffafafffffafafafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wM:Lower ir iu 7:=carry_of (swaps:=[(6,7)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def iv:List Nat:=varsOf 193
def iw:Nat:=0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wN:Lower iv iw 4:=carry_of (swaps:=[(6,7),(5,6),(3,6),(4,7),(2,6)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def ix:List Nat:=varsOf 196
def iy:Nat:=0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wO:Lower ix iy 4:=carry_of (swaps:=[(6,7),(5,6),(3,6),(1,6),(4,7),(2,6),(0,2)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def iz:List Nat:=varsOf 197
def iA:Nat:=0xfffffffffffffffffafafafafafafafafafafafafafafafaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wP:Lower iz iA 7:=carry_of (swaps:=[(5,7),(6,7),(4,6)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def iB:List Nat:=varsOf 208
def iC:Nat:=0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma iD:Lower iB iC 4:=carry_of (swaps:=[(6,7),(5,6),(3,7),(1,7),(4,7),(2,6),(0,4)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def iE:List Nat:=varsOf 209
def iF:Nat:=0xffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wQ:Lower iE iF 7:=carry_of (swaps:=[(5,7),(3,7),(6,7),(4,6),(2,4)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def ed:List Nat:=varsOf 212
def ee:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma iG:Lower ed ee 7:=carry_of (swaps:=[(5,7),(3,7),(1,7),(6,7),(4,6),(2,4),(0,2)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def aD:List Nat:=varsOf 213
def Z:Nat:=0xfffffffffffffffffffffafafffffafafffffafafffffafafafaa0a0fafaa0a0
def ef:List Nat:=[17,20,5,5,20,17,65,129,192,192,68,65,80,132,144,68,129,132,80,144,17,193,148,80,5,145,148,5,17,65,21,5,17,20,193,208,192,193,196,208,144,84,65,21,68]
def eg:List Nat:=[16,16,1,4,4,1,1,1,64,128,4,64,16,4,16,64,128,128,64,128,4,1,4,1,64,16,16,0,0,0,16,128,128,128,128,128,1,64,64,64,4,16,16,4,16]
def PA:Nat:=fullMask 45
def iH:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc25fb3108ed,0x1000a000e4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1a42cd42a41e,0x90000502418),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xb8b56dc5033,0x160046005003),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x16fc20a49f40,0xe001048900),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x1fc066b6380,0xf800b0200)]
def wR:List (Nat × Nat × Nat):=[(0,0,1),(1,0,1),(1,0,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,6),(1,4,7),(1,8,10),(1,8,13),(1,8,14),(1,10,13),(1,10,14),(1,13,14),(3,4,7),(1,4,8),(3,4,13),(0,7,8),(1,7,8),(2,3,6),(3,3,6),(1,3,7),(3,3,7),(1,3,8),(1,4,6),(3,4,6),(3,3,14),(1,3,21),(1,4,27),(3,3,22),(0,1,3),(1,1,3),(1,2,3),(1,4,38),(3,4,38),(1,4,39),(3,4,39),(2,31,39),(1,32,43),(1,32,39),(2,6,39),(0,2,4),(1,2,4),(2,38,49),(3,3,49),(3,3,40),(3,2,6),(3,2,30),(3,6,54),(1,2,32),(3,2,40),(1,1,4),(3,1,7),(3,1,10),(3,1,42),(3,1,28),(3,1,13),(3,2,13),(1,3,64),(3,1,14),(3,1,39),(1,2,27),(1,0,3),(3,0,3),(1,0,4),(2,0,4),(3,0,28),(3,0,16),(3,3,16),(0,4,16),(3,3,45),(1,1,73),(1,4,69),(3,1,49),(3,0,49),(3,0,13),(3,0,58),(0,0,42),(3,0,42),(3,0,20),(3,1,20),(3,3,20),(3,4,56),(2,16,72),(1,3,76),(1,3,5),(3,5,45),(0,3,25),(3,3,71),(0,58,71),(0,4,25),(1,0,12),(1,4,75),(1,0,52),(1,0,9),(1,25,101),(3,9,25),(1,0,11),(1,25,104),(3,11,25),(1,4,94),(2,4,94),(2,16,94),(1,0,55),(1,0,26),(2,75,92),(3,4,65),(1,3,80),(0,7,71),(3,0,22),(1,1,116),(1,1,85),(3,48,88),(1,38,117),(3,3,117),(1,2,37),(3,37,86),(1,0,60),(1,1,84),(2,19,84)]
def ae:BT Decor:=buildWiresBT 7 iH wR
def wS:List (List (Nat × Nat)):=[[],[(6,7)],[(4,6)],[(4,7)],[(2,4)],[(2,6)],[(2,7)],[(0,2)],[(0,4)],[(0,6)],[(0,7)],[(6,7),(4,6)],[(6,7),(4,7)],[(6,7),(2,4)],[(4,6),(2,4)],[(4,7),(2,4)],[(4,6),(2,6)],[(6,7),(2,6)],[(4,7),(2,6)],[(4,7),(2,7)],[(6,7),(2,7)],[(4,6),(2,7)],[(6,7),(0,2)],[(4,6),(0,2)],[(4,7),(0,2)],[(2,4),(0,2)],[(2,6),(0,2)],[(2,7),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(4,6),(0,4)],[(4,7),(0,4)],[(2,6),(0,4)]]
def wT:BT (List (Nat × Nat)):=btOfList 6 wS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ai:goodPairs Z ef eg:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wU:∀ x ∈ iH, faithful ef eg x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aj:btAll (fun x => faithful ef eg x ∧ x.1 < 2^256) ae:=buildWiresBT_faithful wU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ak:btAll (fun sw => swapsValid sw = true ∧ permWord sw Z = Z) wT:=btAll_ofList (autos_of (by decide +kernel))
def wV:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,7),some (subcubeFast 4 0,7),some (subcubeFast 5 0,4),some (subcubeFast 16 0,7),some (subcubeFast 17 0,4),some (subcubeFast 20 0,4),some (subcubeFast 64 0,7),some (subcubeFast 65 0,4),some (subcubeFast 68 0,4),some (subcubeFast 80 0,4),some (subcubeFast 128 0,7),some (subcubeFast 129 0,4),some (subcubeFast 132 0,4),some (subcubeFast 144 0,4),some (subcubeFast 192 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,5),some (0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff,5)]
def wW:BT (Option (Nat × Nat)):=btOfList 5 wV
def al:Nat → Option PoolSpec:=lookSpec 116 #[(1,0,2),(1,0,1),(1,1,2),(1,3,4),(1,3,6),(1,1,3),(3,4,13),(3,3,6),(1,2,3),(1,3,7),(1,3,8),(1,2,4),(1,4,6),(2,31,39),(3,4,6),(1,8,13),(2,6,39),(1,1,4),(1,7,8),(1,0,4),(3,2,6),(3,2,13),(1,0,3),(1,4,39),(3,1,49),(3,1,42),(1,4,7),(1,8,14),(3,1,14),(1,4,8),(3,0,49),(3,0,22),(1,8,10),(2,38,49),(3,1,10),(0,0,42),(3,0,42)] #[0x120000402030e14101800404180050202000820a0000201800000300000c0000082060018101800000240000600000020300002800000001c00504060818106060410500000014000000800000020000001800010000000802000000806041030000040400000020000000,0x200001303243018000244c0ca122606009030000441018020140400f040638682030034101800034040001a00004850000000030000082800012140000c060000006800000386090800006090000281018014040400016022c50203000000500002800000040c0000901,0x203c0200f8c06007c60080360418009360000f1b030000f008000002c01d360600d81010070d819a3024000003006004810a00600830032300001218000060101000008500302400b89021400b810a003008300003004000180000b020600541030024080c01504140018500,0x25121401298060094c01a5302404000001e90c090100604808c121004004180201184030030200801810000220c060108401002430500182404000300c6031e031218185203c0c18006061400f03060018f01800018280170c060000603]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wX:Slice aD Z (0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff) 5:=mappedSlice (f:=identifyRow 0 0 7 6) (R:=aU) (G:=aV) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) aZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wY:Slice aD Z (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 5:=mappedSlice (f:=identifyRow 0 0 2 0) (R:=hM) (G:=hN) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) wh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma wZ:Slice aD Z (subcubeFast 192 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=aE) (qGoal:=aB) (by decide +kernel) aG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xa:Slice aD Z (subcubeFast 144 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dc) (qGoal:=dd) (by decide +kernel) de
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xb:Slice aD Z (subcubeFast 132 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dT) (qGoal:=dU) (by decide +kernel) hO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xc:Slice aD Z (subcubeFast 129 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dV) (qGoal:=dW) (by decide +kernel) hQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xd:Slice aD Z (subcubeFast 128 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aP) (qGoal:=aw) (by decide +kernel) bE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xe:Slice aD Z (subcubeFast 80 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=ik) (qGoal:=il) (by decide +kernel) wJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xf:Slice aD Z (subcubeFast 68 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=im) (qGoal:=io) (by decide +kernel) wK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xg:Slice aD Z (subcubeFast 65 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=ip) (qGoal:=iq) (by decide +kernel) wL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xh:Slice aD Z (subcubeFast 64 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ir) (qGoal:=iu) (by decide +kernel) wM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xi:Slice aD Z (subcubeFast 20 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=iv) (qGoal:=iw) (by decide +kernel) wN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xj:Slice aD Z (subcubeFast 17 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=ix) (qGoal:=iy) (by decide +kernel) wO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xk:Slice aD Z (subcubeFast 16 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=iz) (qGoal:=iA) (by decide +kernel) wP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xl:Slice aD Z (subcubeFast 5 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=iB) (qGoal:=iC) (by decide +kernel) iD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xm:Slice aD Z (subcubeFast 4 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=iE) (qGoal:=iF) (by decide +kernel) wQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xn:Slice aD Z (subcubeFast 1 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ed) (qGoal:=ee) (by decide +kernel) iG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma an:btAll (fun o => ∀ p, o = some p → Slice aD Z p.1 p.2) wW:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aD Z p.1 p.2) (forall_cons (someSlice xn) (forall_cons (someSlice xm) (forall_cons (someSlice xl) (forall_cons (someSlice xk) (forall_cons (someSlice xj) (forall_cons (someSlice xi) (forall_cons (someSlice xh) (forall_cons (someSlice xg) (forall_cons (someSlice xf) (forall_cons (someSlice xe) (forall_cons (someSlice xd) (forall_cons (someSlice xc) (forall_cons (someSlice xb) (forall_cons (someSlice xa) (forall_cons (someSlice wZ) (forall_cons (someSlice wY) (forall_cons (someSlice wX) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def xo:BT (List (List Nat)):=BT.empty
lemma iI:btAll (fun bk => ∀ xs ∈ bk, Impossible Z (3 - 1) xs.toFinset) xo:=trivial
def iJ:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x9b110041af3120042d2a330041a3e2b386014563970041847387014413218014),(13,441017593512833)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xp:∀ ns ∈ iJ, Impossible Z 3 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak iI (by decide +kernel)
def iK:List NodeSpec:=readDeltaNodes 5 (varNats 3 (unpackWords 4 [(50,0x1ad4a220044c684a400412f2b4f00418e68100043b4f681004)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xq:∀ ns ∈ iK, Impossible Z 3 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak iI (by decide +kernel)
def xr:BT (List (List Nat)):=refBuckets ae [iJ,iK] #[0,0,0,0,0,0,0,0,0,0,1,0,0,16386,7,0,0,0,0,0,0,0,0,0,13,0,0,0,9,0,0,0,8,0,0,0,10,0,0,0,0,0,0,5,0,0,0,0,0,6,0,0,0,0,0,0,12,0,0,3,11,0,0,0]
set_option maxRecDepth 20000 in
lemma bP:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 3 xs.toFinset) xr:=refBuckets_all (forall_cons xp (forall_cons xq (fun _ h => (List.not_mem_nil h).elim)))
def iL:List NodeSpec:=readDeltaNodes 8 (unpackWords 4 [(64,0x56d413005751313015f13130058541300504154131157a13130157032134205),(6,6238512)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xt:∀ ns ∈ iL, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2d926ae7c64e00d0a138eacc24d066279d19849a772cb00d),(54,0x987c4902698a9d94651269c0f36b35206baaaaa5)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xu:∀ ns ∈ iM, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iN:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2052d02c2b38242055a111000512a32a18111153c2e3e2a44211542c1f312105),(36,0x359191a3a1d011571a2d2910015131914960)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xv:∀ ns ∈ iN, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd0dcc035057945206a32f248069b7124806af4ca54c6004d),(51,0xa55a294dc50269e76373001a65557cc006baa9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xw:∀ ns ∈ iO, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9a0ec65e8920d0678fa84906a954a6f40034cabe59000d),(56,0x3b544800d7b9bbbc4804d27832c3c90c1af737c509)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xx:∀ ns ∈ iP, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x401a6d32d65006994cb52401ae73322c0357a668f1b5904d),(51,0x8caf4659068556595ea924d331729401a76c89)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xy:∀ ns ∈ iQ, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xebc2d92683ba9db209aa3b9b201a4cd0c440342f5fcd904d),(51,0x6b361f0820d3dceb631104d6aaae1dc824d2a1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xz:∀ ns ∈ iR, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9a0ad94ec9069e15e57e4206adcc90c44035f33531100d),(54,0x1e7aaa400699f1f55200356a55c4006af4cf8a98c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xA:∀ ns ∈ iS, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def iT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x34999f55757024d7e38a2001a67a54c6000d5e9d4c54804d),(59,0x7ec49201a77e76cf928135872152a481abd264331801)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xB:∀ ns ∈ iT, Impossible Z 4 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak bP (by decide +kernel)
def xC:BT (List (List Nat)):=refBuckets ae [iL,iM,iN,iO,iP,iQ,iR,iS,iT] #[0,0,64,0,0,213013,39,63,0,233501,20,53,838971400,68,0,58,0,1,1040437291,0,25,11,23,4123856547844,67,22,0,0,59,0,40966,12,196611,0,0,151567,46,42,47,225308,0,0,4948741922818,208922,1191366688,1107423245,69646,0,906149926,35,0,0,0,671236126,49,7,24,266274,16,69,286753,9,5,0]
set_option maxRecDepth 20000 in
lemma aQ:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 4 xs.toFinset) xC:=refBuckets_all (forall_cons xt (forall_cons xu (forall_cons xv (forall_cons xw (forall_cons xx (forall_cons xy (forall_cons xz (forall_cons xA (forall_cons xB (fun _ h => (List.not_mem_nil h).elim))))))))))
def iU:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x7011182b13132356445112130367011444513132552854310112123211213666),(64,0x1b64182f121303602f121120161c4181801b3f12135062f5401914413f124445)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xD:∀ ns ∈ iU, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def iV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8a2251a4e7c838eac94c1c955c1e7464a301ca05f944a24e),(64,0x53945164e59f643919651a0e30c0a995f44a64e6a186030e),(27,0xab20cc6244980e34c314)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xE:∀ ns ∈ iV, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def iW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8a924a072441855249309c713dce73288671341ebb24964e),(64,0x24924e3cf7a945108e47287638a64338d07732324944e342),(6,15987)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xF:∀ ns ∈ iW, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def iX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x419c14ae124824e0f444a009ce83cf8c9251381c6524920e),(64,0xe0d8b29532683819a225004e275551b9128339c31e2b1b92),(5,6810)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xG:∀ ns ∈ iX, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def iY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x440271e670b558ecab21939aa4a04a8ea322c7d30d20e38e),(64,0x5173e124184e719c0cc4f3ba40c271e7d539440271e75539),(41,0x399684920138c688321248341cf934c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xH:∀ ns ∈ iY, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def iZ:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11111605a11110106197541b3d1110406705d294b1210216719018163c220316),(47,0x31c349662110316007a1c111111618e11110006049781c1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xI:∀ ns ∈ iZ, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jc:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11212604f31110106493d1d111001659111100065a111000511707c1d1110406),(54,0x18049491d191202165197740382f111819382e3065502e491d492d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xJ:∀ ns ∈ jc, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jd:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x19c128af529b8a051c7430ee6d25040e50294caee25044e),(64,0x60389e168f93c90c9c438a533c36924a471bd287f529b8a),(33,0x714a74c4920a3893c1931a89)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xK:∀ ns ∈ jd, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def je:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x41cab8419f284906039c2bd33f36924a271c41d392480ce),(64,0x217a6cc6e248309c16867ce2241272f4eb892402703ad249),(19,0x6ce6e24800e55c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xL:∀ ns ∈ je, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa6da6d24904e361b892003955a39cdc49049c1ca6d24904e),(58,0x9bf924820e665849201c699322400703639d1208397)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xM:∀ ns ∈ jf, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jg:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb49249383f9544804e37ac7f7632804729928a9d0ced80ce),(64,0x280270065a4928939ca6e44800e3c2f5d26d6422705e9b71),(10,499798889)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xN:∀ ns ∈ jg, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x71b6924800e05c84a041cb275584a081c57529eee25044e),(64,0x98eea76c9e69ab07977f328a2728705965e945838ef49240),(20,0x2642543413e1371)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xO:∀ ns ∈ jh, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def ji:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xa5a421011672a384210016002a5c3121116382f2a2c74b33103603b4b3121016),(48,0x15019194942103165075c4210206291b4284b42103062c74)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xP:∀ ns ∈ ji, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2d1ab03275b32884719dc58dc777cc44338c0ab5b188844e),(64,0xcca21138de660b753b288670076eca20939e614aa2a64862),(23,0x15ebd44820e20cf9d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xQ:∀ ns ∈ jj, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jk:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2163430119d11114064c191a63d3100265948191a394191003605c2a1120016),(55,0x5d19e4b12101161a1ec1111010619045a14a310216305d19f4a112)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xR:∀ ns ∈ jk, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jl:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3bbcb63eaa4246879fe51041c0db4eab1441271f6924800e),(64,0x3a433e531282273ec1b0ce766430713ce317557562060398),(19,0xa87e1989410398)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xS:∀ ns ∈ jl, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jm:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1a1282a40036124821100162f1c1a21e2a220036561f036d2b1c1a1282a40455),(64,0x5d1282a3100161e10381b4a310306119c4a211001611b81a4282a22003613f1a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xT:∀ ns ∈ jm, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def jn:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0xdd7c49089cf9ea2bcf440470722989248382f56a54cc824e),(57,0x2c7cc49208397aae25000e077c64af924927198d3cc)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xU:∀ ns ∈ jn, Impossible Z 5 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak aQ (by decide +kernel)
def xV:BT (List (List Nat)):=refBuckets ae [iU,iV,iW,iX,iY,iZ,jc,jd,je,jf,jg,jh,ji,jj,jk,jl,jm,jn] #[1493471262,0,409607,1879191557,1594155018,6804839186448,0x4b04303601600f,0x8d04c03d02802401c,23,58,434226,91,110606,0,0x8b08508305a038,8385537970194,102,512047,1745158221,0x8607f06b03e033022,1896013844,71,33,5842313408564,9622790811691,93,118,217112,159773,9760179286035,2,495658,466989,2282057796,0x8406e04200d008,294977,1476575263,97,60,3780259155977,135,507963,2114084865,1862623244,401440,0,128,3,421925,143,413753,0,25,6,446534,138,479313,64,2181234714,0x8908105201500b,385107,1946599508,303108,119]
set_option maxRecDepth 20000 in
lemma ce:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 5 xs.toFinset) xV:=refBuckets_all (forall_cons xD (forall_cons xE (forall_cons xF (forall_cons xG (forall_cons xH (forall_cons xI (forall_cons xJ (forall_cons xK (forall_cons xL (forall_cons xM (forall_cons xN (forall_cons xO (forall_cons xP (forall_cons xQ (forall_cons xR (forall_cons xS (forall_cons xT (forall_cons xU (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))
def jo:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x931031b135312111145771818011a1443f121124562854310611152111213675),(64,0x1101171c102291182c3111134601544612111114718131011b15446311115661),(31,0x390161c45191b2e211112670482e211)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xW:∀ ns ∈ jo, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def jp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249049e797da24367ba66594a8a21434f30290c9d124844f),(64,0x34f541fdc37924844f3a9e1484d30c3b1e91219a783f9d95),(64,0x55c481e765943cf84920d30f58c3da6412cec6650ee49214),(24,0x3df24f0a5709241c4e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xX:∀ ns ∈ jp, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def jq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xbc9514a6d25038e39076a8a7249089e7850ec665912484cf),(64,0x7d3c792483cd3c9c43ae191f464349241869e6531b342369),(64,0xf5570924184f55c214e4a865a6d24906187aa612710eb864),(28,0x2785e9f8da492193c93c2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xY:∀ ns ∈ jq, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def jr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x30f2429c951cc6d249069879a4a24920de4a865e4921630e),(64,0xb49243479d1407d372ae2a4921b3dc0a62545299d128230f),(64,0x21138ae0abde50d72928330e2412a196a2490d9e4f0ac549),(11,1100274249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma xZ:∀ ns ∈ jr, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def js:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xf2b1d19195a42106561c3519013a3b5192c5a31215564703f2c5187d11110346),(64,0x4b312105661f19504949181993121043650382b1c1a3b1f312102471a1364013),(60,0x29701118e119295d111103571b104d4a18481d1111033741210153d12e2a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ya:∀ ns ∈ js, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def jt:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2e384d45b4a1111054719058148191a391a1210247610119a19181a11110337),(64,0xb1a42c1b4a211019572e1905f3b1e5a4b12103362105c4591e9111103362d523),(59,0x1a01ab282a11110217751430116c2b1c1a282a11206661e211121203916)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yb:∀ ns ∈ jt, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def ju:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20d34e332c0c996ca62490c9ec173933b8b2e6433128238f),(64,0x2bd2490c9e687e9b0da6f5c924267a8d9e0bdcdef18b1533),(64,0x264c7e5975f1241e61cbb80ca4cc62a7e3c921987a8d63af),(52,0x24a2b12c9064c4936ae7ac7d54870f359c61a98)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yc:∀ ns ∈ ju, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def jv:List NodeSpec:=readDeltaNodes 3 (varNats 2 (unpackWords 3 [(64,0x3dc749341256c65c6ca4920e34e3942683bd06f7c9241a8f),(29,0x3281f49b8ccb757124830c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yd:∀ ns ∈ jv, Impossible Z 6 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak ce (by decide +kernel)
def ye:BT (List (List Nat)):=refBuckets ae [jo,jp,jq,jr,js,jt,ju,jv] #[721526805,0,0,23,25,939679766,0,805371917,49,0,0,55,0,0,213020,40,0,0,135177,53,0,30,0,1,69644,0,0,4,0,0,0,0,0,204847,7,44,2543023370258,0,31,0x3a03903602900b008003,0,81922,35,0,771792901,0,0,0,0,36,15,0,59,159771,855810080,0,0,0,0,57350,0,29,0,184354]
set_option maxRecDepth 20000 in
lemma jw:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 6 xs.toFinset) ye:=refBuckets_all (forall_cons xW (forall_cons xX (forall_cons xY (forall_cons xZ (forall_cons ya (forall_cons yb (forall_cons yc (forall_cons yd (fun _ h => (List.not_mem_nil h).elim)))))))))
def jx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a1e6a40b84ae94514a89242aa1eab20c30f27228924c38e),(64,0xaf9c49c8ce89241879e542490eb8643c9391b49241ea1c8d),(64,0x2602623a29155b328834e3952484bd51472924834c396243),(64,0xd16a67a4920d30e33a441895349bca91553ac4920d54f34c),(12,13711971185)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yf:∀ ns ∈ jx, Impossible Z 7 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak jw (by decide +kernel)
def jy:List NodeSpec:=readDeltaNodes 3 (varNats 2 (unpackWords 3 [(64,0x329bd5e79242a71ca33494423a137936194c5d4c4921450f),(61,0x38b3251416371e7744dc6657124855439739231940bf89)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yg:∀ ns ∈ jy, Impossible Z 7 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak jw (by decide +kernel)
def yh:BT (List (List Nat)):=refBuckets ae [jx,jy] #[0,0,0,0,0,8,0,45060,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,9,0,0,6,2,0,0,0,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,3,0,5,0,0,0,7,0,0,0]
set_option maxRecDepth 20000 in
lemma yi:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 7 xs.toFinset) yh:=refBuckets_all (forall_cons yf (forall_cons yg (fun _ h => (List.not_mem_nil h).elim)))
def jz:List NodeSpec:=readDeltaNodes 2 (varNats 2 (unpackWords 3 [(63,0x51e09bca8763d7a4920c38e26430921d7d43c844920f38e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yj:∀ ns ∈ jz, Impossible Z 8 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak yi (by decide +kernel)
def yk:BT (List (List Nat)):=refBuckets ae [jz] #[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma yl:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 8 xs.toFinset) yk:=refBuckets_all (forall_cons yj (fun _ h => (List.not_mem_nil h).elim))
def jA:List NodeSpec:=readDeltaNodes 1 (unpackWords 5 [(20,0xb8c211080cd18200842101ca5)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ym:∀ ns ∈ jA, Impossible Z 9 (nodeValsBT ae ns).toFinset:=blockOk al 8 (by decide) ai aj an ak yl (by decide +kernel)
def yn:BT (List (List Nat)):=refBuckets ae [jA] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma yo:btAll (fun bk => ∀ xs ∈ bk, Impossible Z 9 xs.toFinset) yn:=refBuckets_all (forall_cons ym (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bF:Lower aD Z 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) yo (by decide +kernel)
def cJ:List Nat:=varsOf 221
def cK:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffaa0a0fffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dj:Lower cJ cK 11:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,16,24)]) (by decide +kernel) bF
def cA:List Nat:=varsOf 31
def cB:Nat:=0xfefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0fefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cL:Lower cA cB 6:=lift_of (z:=2) (o:=8) (essPairs:=[(VAR 1,8,10),(VAR 3,2,10)]) (by decide +kernel) aG
def cf:List Nat:=varsOf 74
def cg:Nat:=0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ch:Lower cf cg 4:=carry_of (swaps:=[(5,6),(4,6),(2,3),(0,1)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def ba:List Nat:=varsOf 71
def bc:Nat:=0xfefefefefefefefea0a0a0a0a0a0a0a0fefefefefefefefea0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bh:Lower ba bc 5:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) de
def dk:List Nat:=varsOf 75
def dl:Nat:=0xffeeffeeffeeffeecc00cc00cc00cc00ffeeffeeffeeffeecc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eh:Lower dk dl 5:=carry_of (swaps:=[(2,3),(0,1)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def ei:List Nat:=varsOf 77
def ej:Nat:=0xfffafffafffafffaa0a0a0a0a0a0a0a0fffafffafffafffaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jB:Lower ei ej 5:=carry_of (swaps:=[(1,3)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def ek:List Nat:=varsOf 78
def el:Nat:=0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jC:Lower ek el 5:=carry_of (swaps:=[(2,3),(0,2),(1,2)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def aJ:List Nat:=varsOf 79
def ap:Nat:=0xfffefffefffefffeeca0eca0eca0eca0fffefffefffefffeeca0eca0eca0eca0
def em:List Nat:=[5,10,7,11,5,68,5,10,11,66,65,7,72,67,13,72,65,14,68,72,68,66,13,65,14,73]
def en:List Nat:=[4,8,6,9,6,64,1,2,3,2,1,3,64,3,9,9,64,6,4,8,6,64,12,0,12,9]
def bQ:Nat:=fullMask 26
def jD:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x2c16d5d,0x200ed48),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1222b8e,0x122b94),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1564875,0x1560015),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x34ad18a,0x348c00a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x2bdb620,0x211020)]
def yp:List (Nat × Nat × Nat):=[(1,0,1),(1,0,4),(1,1,6),(3,1,6),(3,2,6),(0,4,5),(2,4,5),(3,4,5),(3,0,4),(1,2,10),(3,2,7),(1,1,11),(3,3,16)]
def bl:BT Decor:=buildWiresBT 5 jD yp
def yq:List (List (Nat × Nat)):=[[],[(1,3)],[(0,2)],[(2,3),(0,1)],[(1,3),(0,2)],[(1,2),(0,3)],[(2,3),(1,2),(0,1)],[(2,3),(1,3),(0,3)]]
def bI:BT (List (Nat × Nat)):=btOfList 3 yq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dm:goodPairs ap em en:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yr:∀ x ∈ jD, faithful em en x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dp:btAll (fun x => faithful em en x ∧ x.1 < 2^256) bl:=buildWiresBT_faithful yr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dq:btAll (fun sw => swapsValid sw = true ∧ permWord sw ap = ap) bI:=btAll_ofList (autos_of (by decide +kernel))
def yt:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 5 0,4),some (subcubeFast 8 0,5),some (subcubeFast 10 0,4)]
def jE:BT (Option (Nat × Nat)):=btOfList 3 yt
def yu:List PoolSpec:=readSpecs ((readChoices 2 (unpackWords 3 [(6,132673)])).toArray) 8 (unpackWords 3 [(18,0x9420418a0a040)])
def bJ:BT (Option BoundPool):=buildPoolsBT 4 bl aJ jE yu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yv:Slice aJ ap (subcubeFast 10 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dc) (qGoal:=dd) (by decide +kernel) de
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yw:Slice aJ ap (subcubeFast 8 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ba) (qGoal:=bc) (by decide +kernel) bh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yx:Slice aJ ap (subcubeFast 5 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yy:Slice aJ ap (subcubeFast 4 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) eh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yz:Slice aJ ap (subcubeFast 2 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ei) (qGoal:=ej) (by decide +kernel) jB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yA:Slice aJ ap (subcubeFast 1 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ek) (qGoal:=el) (by decide +kernel) jC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yB:btAll (fun o => ∀ p, o = some p → Slice aJ ap p.1 p.2) jE:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aJ ap p.1 p.2) (forall_cons (someSlice yA) (forall_cons (someSlice yz) (forall_cons (someSlice yy) (forall_cons (someSlice yx) (forall_cons (someSlice yw) (forall_cons (someSlice yv) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma dr:btAll (fun o => ∀ c, o = some c → ValidPool aJ ap c) bJ:=buildPoolsBT_sound yB
def eo:BT (List (List Nat)):=BT.empty
lemma yC:btAll (fun bk => ∀ xs ∈ bk, Impossible ap (4 - 1) xs.toFinset) eo:=trivial
def jF:List NodeSpec:=readDeltaNodes 3 (unpackWords 4 [(24,0xd2110005b1210005a1210005)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yD:checkNodesBT bl ap bQ bJ bI eo 4 jF = true:=by decide +kernel
def jG:List NodeSpec:=jF
set_option maxRecDepth 20000 in
lemma yE:checkNodesBT bl ap bQ bJ bI eo 4 jG = true:=yD
def ds:BT (List (List Nat)):=buildBucketsBT bl jG
set_option maxRecDepth 20000 in
lemma yF:btAll (fun bk => ∀ xs ∈ bk, Impossible ap 4 xs.toFinset) ds:=buildBucketsBT_sound (by decide) dm dp dr dq yC yE
def jH:List NodeSpec:=readDeltaNodes 8 (unruns (unpackWords 5 [(62,0x142208a0520e22818e710e200990388a0638e2281860094638804230c01204061c402218f1008c)]) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yG:checkNodesBT bl ap bQ bJ bI ds 5 jH = true:=by decide +kernel
def jI:List NodeSpec:=readDeltaNodes 2 (unpackWords 4 [(21,0x6c111101165321210016)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yH:checkNodesBT bl ap bQ bJ bI ds 5 jI = true:=by decide +kernel
def ep:List NodeSpec:=jH ++ jI
set_option maxRecDepth 20000 in
lemma yI:checkNodesBT bl ap bQ bJ bI ds 5 ep = true:=by
  unfold ep checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨yG,yH⟩
def es:BT (List (List Nat)):=buildBucketsBT bl ep
set_option maxRecDepth 20000 in
lemma yJ:btAll (fun bk => ∀ xs ∈ bk, Impossible ap 5 xs.toFinset) es:=buildBucketsBT_sound (by decide) dm dp dr dq yF yI
def jJ:List NodeSpec:=readDeltaNodes 3 (unpackWords 4 [(41,0x10231911110236102312111102363013111110226)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yK:checkNodesBT bl ap bQ bJ bI es 6 jJ = true:=by decide +kernel
def jK:List NodeSpec:=jJ
set_option maxRecDepth 20000 in
lemma yL:checkNodesBT bl ap bQ bJ bI es 6 jK = true:=yK
def et:BT (List (List Nat)):=buildBucketsBT bl jK
set_option maxRecDepth 20000 in
lemma yM:btAll (fun bk => ∀ xs ∈ bk, Impossible ap 6 xs.toFinset) et:=buildBucketsBT_sound (by decide) dm dp dr dq yJ yL
def jL:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(15,9423345193301)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yN:checkNodesBT bl ap bQ bJ bI et 7 jL = true:=by decide +kernel
def jM:List NodeSpec:=jL
set_option maxRecDepth 20000 in
lemma yO:checkNodesBT bl ap bQ bJ bI et 7 jM = true:=yN
def yP:BT (List (List Nat)):=buildBucketsBT bl jM
set_option maxRecDepth 20000 in
lemma yQ:btAll (fun bk => ∀ xs ∈ bk, Impossible ap 7 xs.toFinset) yP:=buildBucketsBT_sound (by decide) dm dp dr dq yM yO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bK:Lower aJ ap 8:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 6,1,65)]) (by decide +kernel) yQ (by decide +kernel)
def eu:List Nat:=varsOf 90
def ev:Nat:=0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jN:Lower eu ev 5:=carry_of (swaps:=[(3,4),(2,3),(0,4),(1,4)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def dt:List Nat:=varsOf 91
def du:Nat:=0xffffffeeffffffeeeeaacc00eeaacc00ffffffeeffffffeeeeaacc00eeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ew:Lower dt du 8:=carry_of (swaps:=[(2,4)]) (roots2:=aJ) (T2:=ap) (by decide +kernel) bK
def dv:List Nat:=varsOf 94
def dw:Nat:=0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ex:Lower dv dw 8:=carry_of (swaps:=[(2,4),(3,4),(1,2),(0,1)]) (roots2:=aJ) (T2:=ap) (by decide +kernel) bK
def aR:List Nat:=varsOf 93
def aS:Nat:=0xfffffffffffffffffffaffa0fffaffa0fffffffffffffffffffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma aW:Lower aR aS 6:=lift_of (z:=72) (o:=0) (essPairs:=[(VAR 3,0,8),(VAR 6,0,64)]) (by decide +kernel) aG
def ey:List Nat:=varsOf 91
def ez:Nat:=0xffffffeeffffffeeffffcc00ffffcc00ffffffeeffffffeeffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma jO:Lower ey ez 6:=lift_of (z:=17) (o:=0) (essPairs:=[(VAR 0,64,65),(VAR 4,0,16)]) (by decide +kernel) ch
def bd:List Nat:=varsOf 93
def be:Nat:=0xfffffffafffffffafffaa0a0fffaa0a0fffffffafffffffafffaa0a0fffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bn:Lower bd be 8:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,16,24)]) (by decide +kernel) bE
def jP:List Nat:=varsOf 93
def jQ:Nat:=0xfffffffafffffffafafaf0a0fafaf0a0fffffffafffffffafafaf0a0fafaf0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yR:Lower jP jQ 8:=carry_of (swaps:=[(2,4)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def jR:List Nat:=varsOf 94
def jS:Nat:=0xfffffffcfffffffcffffcc00ffffcc00fffffffcfffffffcffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yS:Lower jR jS 6:=carry_of (swaps:=[(0,2)]) (roots2:=ey) (T2:=ez) (by decide +kernel) jO
def jT:List Nat:=varsOf 94
def jU:Nat:=0xfffffffcfffffffcfcfcccc0fcfcccc0fffffffcfffffffcfcfcccc0fcfcccc0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yT:Lower jT jU 8:=carry_of (swaps:=[(1,4),(2,4),(0,2)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def jV:List Nat:=varsOf 23
def jW:Nat:=0xfefeececfefeececfefeececfefeececfefeececfefeececfefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yU:Lower jV jW 5:=carry_of (swaps:=[(5,6),(3,5),(1,3),(1,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def jX:List Nat:=varsOf 29
def jY:Nat:=0xfffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yV:Lower jX jY 5:=carry_of (swaps:=[(5,6),(3,5),(3,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def jZ:List Nat:=varsOf 83
def kc:Nat:=0xffffeeeeffffeeeeaaaa0000aaaa0000ffffeeeeffffeeeeaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yW:Lower jZ kc 5:=carry_of (swaps:=[(3,4),(2,4)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def eA:List Nat:=varsOf 85
def eB:Nat:=0xfffffffffffffffffafaa0a0fafaa0a0fffffffffffffffffafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma kd:Lower eA eB 5:=carry_of (swaps:=[(6,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def cM:List Nat:=varsOf 87
def cN:Nat:=0xfffffefefffffefefafaa0a0fafaa0a0fffffefefffffefefafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dx:Lower cM cN 8:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) bE
def kg:List Nat:=varsOf 89
def kh:Nat:=0xffffffaaffffffaaaaaa0000aaaa0000ffffffaaffffffaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yX:Lower kg kh 5:=carry_of (swaps:=[(2,4),(1,3)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def ki:List Nat:=varsOf 92
def kj:Nat:=0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yY:Lower ki kj 5:=carry_of (swaps:=[(3,4),(2,4),(0,2),(1,3)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def kk:List Nat:=varsOf 93
def kl:Nat:=0xfffffffafffffffafafaa0a0fafaa0a0fffffffafffffffafafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma yZ:Lower kk kl 8:=carry_of (swaps:=[(1,3)]) (roots2:=cM) (T2:=cN) (by decide +kernel) dx
def kn:List Nat:=varsOf 87
def ko:Nat:=0xfffffffffffffffffefeececfefeececfffffffffffffffffefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma za:Lower kn ko 6:=carry_of (swaps:=[(1,3)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def aq:List Nat:=varsOf 95
def B:Nat:=0xfffffffefffffffefefaeca0fefaeca0fffffffefffffffefefaeca0fefaeca0
def eC:List Nat:=[5,10,7,11,5,19,20,5,10,11,20,17,66,65,7,72,19,67,13,14,22,22,68,26,68,65,66,72,14,25,76,73,26,80,21,28,13,66,72,7,10,10,80,25,28,70,82,68,69,81,66,72,22,66,17,80,5,68,65,5,66,67,7,21,20,17,21,84,81,80,84,80,70,88,65,17,65,85,21,69,81,10,10,10,11,17,69,7,65,69,82,20]
def eD:List Nat:=[4,8,6,9,6,18,16,1,2,3,4,1,2,1,3,64,3,3,9,6,18,6,64,18,4,64,6,9,12,9,12,9,24,64,1,24,12,64,8,2,9,12,16,24,12,6,18,6,64,64,18,12,4,0,4,4,16,0,3,64,3,1,4,4,64,64,64,4,1,1,64,18,4,24,16,0,0,64,16,0,16,3,0,64,8,3,4,1,4,1,16,1]
def PB:Nat:=fullMask 92
def kp:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f1fc16ed430894a2076abd,0xaa2003034000104a8076a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x49e0100703463a114bb532e,0x2200801404e08004bb5334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xac0e14dcb11b09c517c44d5,0x1400108c0d8b21055280415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x1e020000081b59f88c830a,0x10020000081b59f804000a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xc216aff80d25c0f20b10c60,0x401468001044c0900900060),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x741b7f836afe462cf42b000,0x820470803002202408000)]
def zb:List (Nat × Nat × Nat):=[(1,0,1),(0,0,2),(1,0,2),(3,0,2),(1,0,4),(2,0,4),(1,0,5),(1,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(2,1,4),(0,1,5),(1,1,5),(2,1,5),(3,1,5),(0,1,12),(1,1,12),(2,1,12),(3,1,12),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(3,4,6),(1,4,12),(3,4,12),(1,4,31),(3,4,31),(0,6,12),(3,6,12),(0,6,31),(1,6,31),(2,6,31),(1,12,28),(2,12,28),(0,12,31),(1,12,31),(2,2,5),(3,2,5),(1,2,6),(3,2,6),(3,2,12),(1,4,5),(3,4,5),(0,5,6),(3,5,6),(1,4,49),(2,12,49),(3,12,49),(2,31,49),(1,1,50),(3,1,50),(1,4,50),(3,6,50),(1,2,32),(3,4,63),(1,12,63),(1,31,63),(1,2,36),(1,32,36),(2,31,32),(1,2,39),(3,5,55),(1,5,49),(0,1,45),(3,1,45),(0,4,45),(3,4,45),(0,1,76),(1,1,76),(2,1,76),(3,1,76),(1,2,76),(1,5,76),(3,5,45),(3,0,5),(3,0,20),(1,0,28),(3,0,28),(3,2,20),(0,3,20),(3,3,20),(3,4,20),(1,5,87),(1,0,49),(3,0,49),(3,0,88),(1,4,88),(3,1,51),(0,31,51),(0,4,70),(1,4,70),(2,4,70),(3,4,70),(0,5,70),(1,3,53),(1,53,87),(1,1,38),(1,38,87),(3,2,107),(3,0,31),(3,0,51),(3,0,100),(3,2,24),(0,3,24),(3,3,24),(2,24,28),(1,4,115),(1,0,38),(1,0,27),(1,28,38),(1,38,118),(1,27,38),(1,0,58),(3,0,58),(3,4,58),(1,0,119),(3,0,35),(3,2,126),(1,4,126),(3,4,126),(1,2,109),(3,2,109),(2,6,109),(3,4,72),(3,1,48),(3,5,48),(1,0,99),(0,2,117),(3,2,122),(0,4,122),(3,4,122),(0,5,122),(2,2,117),(1,4,138),(3,4,117),(1,0,29),(1,29,38),(1,0,146),(3,4,8),(0,5,8),(0,10,28),(2,8,22),(1,2,22),(2,2,22),(1,4,22),(1,28,129),(3,28,129),(1,8,34),(1,4,127),(1,1,103),(1,3,103),(1,4,103),(1,2,26),(2,12,148),(1,1,131),(0,51,86),(1,1,52),(3,2,33),(3,4,130),(1,2,85),(3,0,169),(3,4,169),(1,5,89),(1,0,83),(1,8,91),(1,45,89),(2,20,83),(0,3,40),(3,3,40),(3,7,68),(1,4,14),(2,5,14),(3,29,117),(1,46,117),(1,4,137),(2,4,137),(2,8,38),(1,22,148),(3,22,45),(1,22,83),(3,4,189),(3,11,122),(1,0,14),(2,122,150),(3,7,122),(1,3,134),(1,0,97),(1,2,196),(1,0,52),(3,2,198),(3,0,157),(1,0,131),(1,0,127),(3,3,166),(3,2,128),(1,14,76),(3,14,76),(3,14,45),(0,3,205),(3,4,175),(3,18,45),(1,3,19),(2,3,19),(1,4,19),(2,40,73),(2,40,75),(1,4,57),(3,3,78),(1,4,94),(1,76,94),(3,0,158),(3,3,164),(1,14,83),(1,4,84),(3,4,162),(1,4,47),(3,23,45),(3,3,59),(3,3,106),(3,27,117),(3,4,183),(2,122,137)]
def M:BT Decor:=buildWiresBT 8 kp zb
def zc:List (List (Nat × Nat)):=[[],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(2,4),(1,3)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(1,3),(0,4)],[(2,4),(1,3),(0,2)],[(2,4),(1,3),(0,4)]]
def zd:BT (List (Nat × Nat)):=btOfList 4 zc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma N:goodPairs B eC eD:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ze:∀ x ∈ kp, faithful eC eD x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma O:btAll (fun x => faithful eC eD x ∧ x.1 < 2^256) M:=buildWiresBT_faithful ze
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Q:btAll (fun sw => swapsValid sw = true ∧ permWord sw B = B) zd:=btAll_ofList (autos_of (by decide +kernel))
def zf:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,6),some (subcubeFast 0 8,6),some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 2 8,5),some (subcubeFast 3 0,5),some (subcubeFast 4 0,8),some (subcubeFast 5 0,5),some (subcubeFast 6 0,5),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 10 0,7),some (subcubeFast 12 0,5),some (subcubeFast 16 0,8),some (subcubeFast 17 0,5),some (subcubeFast 18 0,5),some (subcubeFast 20 0,5),some (subcubeFast 21 0,4),some (subcubeFast 24 0,5),some (subcubeFast 64 0,6),some (subcubeFast 64 2,5),some (subcubeFast 64 8,5),some (subcubeFast 66 8,4),some (subcubeFast 72 2,4),some (0x9999999999999999999999999999999999999999999999999999999999999999,8),some (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,8),some (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,8),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f,6)]
def zg:BT (Option (Nat × Nat)):=btOfList 5 zf
def X:Nat → Option PoolSpec:=lookSpec 253 #[(1,0,5),(1,0,1),(1,2,5),(1,2,4),(0,6,12),(3,2,12),(1,1,2),(3,4,6),(1,1,5),(3,0,28),(3,2,6),(1,4,49),(3,2,20),(1,4,5),(0,5,6),(0,6,31),(1,2,39),(1,3,53),(1,4,70),(1,1,12),(3,3,24),(2,24,28),(3,6,12),(3,5,6),(1,2,6),(3,2,24),(2,31,49),(1,0,2),(1,0,4),(3,3,20),(3,1,5),(3,0,35),(1,4,12),(1,4,31),(3,1,12),(3,2,126),(3,4,12),(3,0,31),(3,2,109),(3,4,5),(1,0,28),(3,4,8),(3,4,20),(0,3,20),(1,6,31),(3,3,40),(0,0,2),(3,6,50),(1,3,103),(1,4,103),(3,5,48),(3,1,51),(3,4,45),(1,0,52),(1,1,52),(3,3,166),(0,4,45),(1,0,14),(0,1,3),(1,1,3),(1,5,89),(2,5,14),(2,1,3),(0,1,5),(1,3,19),(2,3,19),(2,1,5),(0,3,40),(2,12,28),(1,0,49),(3,1,45),(1,1,131),(3,3,164),(1,4,14),(3,0,5),(0,3,24),(1,2,26),(3,2,33),(3,2,5),(0,1,12),(2,1,12),(1,4,50),(1,1,38),(3,3,106),(3,0,2),(0,2,4),(1,0,27),(0,31,51),(2,2,4),(3,0,20),(1,2,85),(3,1,3)] #[0x8042820209002410300002408000101600000060000103000000000000e0400301030a041068000001c00002020000013000c08580000c080030206000820d0000108000000140000806001810000000800000042c001040c000001400000818000002c00000060000002,0x61a0000e060000185803008180002e0458a01062a500830028041800000204c80206243c10300243c08890060400782060000781000000340000812007030000001800000083400a081600000110000205801a240860b04120000901000058580120834000002c0020209,0x1d381200e9c0b00601068000602c01b040c00b810b2a50086802a040c015280468a010d00680818028043401402120001402243c10680200818000002a448030b003c10680003c2c00c040c005820d000000500000004000001200c820d0000c858000002000032040080303,0x83381a00181010604e068302702c1813806011810600011811906040c00038300c09c090004e068002702400138160000106001808680408818021020c010030d0874e0580007c34000001c0001f020000f830000243401e121a00009060078481003c241821d38120001c0d,0x3832b96830200b4181005824340005806015890200a8e04805210240003c260001e030064481003e702401f12040001c090000e058000700c01c021a000280754a0083005004180000c04a41810d00014010000a0180001c0401383020001303004a04180004a0e9110302,0x3c761a01d3b0d0001d008000e800035060401c830200980830054702c029081600028090001b868070dc35c37500401ba80200014018054a008036500c00035070098186805038080001c1201a0e020000701800088180333204c880206624010300320c080300c0400e2f0d,0x21a0000109012c0868096041800094020004a00000000bc99098180484c0c02383028c2c106808a0434000720e01c81064ce40830000006c00000251168303000218680010034042801a020c00d0001f868000f03403e761af56090d00d40830000ec340007a00000000f,0xac12000000c0012b0480af5826bd608120005509a94cb8100a65c08000961a0004b0b000258300a404180060216028810d014008680013c3404f021a027810b000278100020c3404e4204001810d000c301009a040c023021b30a010d01300818000006800602120018109,0x1c005ee0117582408017120400f890d007c48300b6240805a121a02d09060002c84d81c0c24000a82750b8103]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zh:Slice aq B (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f) 6:=mappedSlice (f:=identifyRow 0 0 4 2) (R:=ey) (G:=ez) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) jO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zi:Slice aq B (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333) 8:=mappedSlice (f:=identifyRow 0 0 4 1) (R:=bd) (G:=be) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zj:Slice aq B (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 8:=mappedSlice (f:=identifyRow 0 0 2 1) (R:=jP) (G:=jQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) yR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zk:Slice aq B (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555) 6:=mappedSlice (f:=identifyRow 0 0 4 0) (R:=jR) (G:=jS) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) yS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zl:Slice aq B (0x9999999999999999999999999999999999999999999999999999999999999999) 8:=mappedSlice (f:=identifyRow 0 0 1 0) (R:=jT) (G:=jU) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) yT
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zm:Slice aq B (subcubeFast 72 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=aE) (qGoal:=aB) (by decide +kernel) aG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zn:Slice aq B (subcubeFast 66 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=aE) (qGoal:=aB) (by decide +kernel) aG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zo:Slice aq B (subcubeFast 64 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=jV) (qGoal:=jW) (by decide +kernel) yU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zp:Slice aq B (subcubeFast 64 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=jX) (qGoal:=jY) (by decide +kernel) yV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zq:Slice aq B (subcubeFast 64 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=cA) (qGoal:=cB) (by decide +kernel) cL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zr:Slice aq B (subcubeFast 24 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ba) (qGoal:=bc) (by decide +kernel) bh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zt:Slice aq B (subcubeFast 21 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zu:Slice aq B (subcubeFast 20 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) eh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zv:Slice aq B (subcubeFast 18 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ei) (qGoal:=ej) (by decide +kernel) jB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zw:Slice aq B (subcubeFast 17 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ek) (qGoal:=el) (by decide +kernel) jC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zx:Slice aq B (subcubeFast 16 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aJ) (qGoal:=ap) (by decide +kernel) bK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zy:Slice aq B (subcubeFast 12 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=jZ) (qGoal:=kc) (by decide +kernel) yW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zz:Slice aq B (subcubeFast 10 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aP) (qGoal:=aw) (by decide +kernel) bE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zA:Slice aq B (subcubeFast 8 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=eA) (qGoal:=eB) (by decide +kernel) kd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zB:Slice aq B (subcubeFast 8 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cM) (qGoal:=cN) (by decide +kernel) dx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zC:Slice aq B (subcubeFast 6 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=kg) (qGoal:=kh) (by decide +kernel) yX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zD:Slice aq B (subcubeFast 5 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=eu) (qGoal:=ev) (by decide +kernel) jN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zE:Slice aq B (subcubeFast 4 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dt) (qGoal:=du) (by decide +kernel) ew
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zF:Slice aq B (subcubeFast 3 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ki) (qGoal:=kj) (by decide +kernel) yY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zG:Slice aq B (subcubeFast 2 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=eA) (qGoal:=eB) (by decide +kernel) kd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zH:Slice aq B (subcubeFast 2 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=kk) (qGoal:=kl) (by decide +kernel) yZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zI:Slice aq B (subcubeFast 1 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dv) (qGoal:=dw) (by decide +kernel) ex
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zJ:Slice aq B (subcubeFast 0 8) 6:=slice_fast_direct (zDead:=0) (qRoots:=kn) (qGoal:=ko) (by decide +kernel) za
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zK:Slice aq B (subcubeFast 0 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=aR) (qGoal:=aS) (by decide +kernel) aW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Y:btAll (fun o => ∀ p, o = some p → Slice aq B p.1 p.2) zg:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aq B p.1 p.2) (forall_cons (someSlice zK) (forall_cons (someSlice zJ) (forall_cons (someSlice zI) (forall_cons (someSlice zH) (forall_cons (someSlice zG) (forall_cons (someSlice zF) (forall_cons (someSlice zE) (forall_cons (someSlice zD) (forall_cons (someSlice zC) (forall_cons (someSlice zB) (forall_cons (someSlice zA) (forall_cons (someSlice zz) (forall_cons (someSlice zy) (forall_cons (someSlice zx) (forall_cons (someSlice zw) (forall_cons (someSlice zv) (forall_cons (someSlice zu) (forall_cons (someSlice zt) (forall_cons (someSlice zr) (forall_cons (someSlice zq) (forall_cons (someSlice zp) (forall_cons (someSlice zo) (forall_cons (someSlice zn) (forall_cons (someSlice zm) (forall_cons (someSlice zl) (forall_cons (someSlice zk) (forall_cons (someSlice zj) (forall_cons (someSlice zi) (forall_cons (someSlice zh) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))
def zL:BT (List (List Nat)):=BT.empty
lemma kq:btAll (fun bk => ∀ xs ∈ bk, Impossible B (4 - 1) xs.toFinset) zL:=trivial
def kr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd7a440356dda44034e8ac35100d739b6340035586fe9100d),(44,0x5f569100d5229a940034c91685100d5b1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zM:∀ ns ∈ kr, Impossible B 4 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q kq (by decide +kernel)
def ks:List NodeSpec:=readDeltaNodes 4 (varNats 3 (unpackWords 4 [(49,0x28a18e3b100051de1ba2f410051c87d1d200051c84c521005)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zN:∀ ns ∈ ks, Impossible B 4 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q kq (by decide +kernel)
def zO:BT (List (List Nat)):=refBuckets M [kr,ks] #[0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,2,0,0,12,0,11,40969,0,0,0,0,0,0,0,0,0,5,0,3,0,0,0,0,0,0,4,0,0,0,0,0,0,1,7,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma bB:btAll (fun bk => ∀ xs ∈ bk, Impossible B 4 xs.toFinset) zO:=refBuckets_all (forall_cons zM (forall_cons zN (fun _ h => (List.not_mem_nil h).elim)))
def kt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x201cac361d5a201caf52224807186c549201ca433a85100e),(51,0x75c4924038eb0924807194d98a24038ca64a4a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zP:∀ ns ∈ kt, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def ku:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xbe2210116018a1891121106381bd2f22100167c1a39210006381a81a2f221016),(46,0x5c1be2a522101611bc7e2a234102659189112100606a11)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zQ:∀ ns ∈ ku, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kv:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb2b44310161d81be23b121016122f52100619c2c2d7210061ce1ac292f221016),(43,0x1ea32b19210061a91ab2b44310162ad451110061bd7)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zR:∀ ns ∈ kv, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe6c33aa8807266f35100e3f43a433a85104e52c33a85100e),(62,0x990ec6a201c8ecd2201c7486d33aa88071959bcd440394)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zS:∀ ns ∈ kw, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def ky:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x38f86caca401c6cafad1544038c8af30d44038ee7669100e),(57,0x3a65ec9001cf197b2400703f47d140838294db0a408)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zT:∀ ns ∈ ky, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3273bd69100e3e736b4880719abbcef4c2502707e149120e),(55,0x643ee44900e5f6249201cbea89200381d6a25120e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zU:∀ ns ∈ kz, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc7de6445000e3f771140038299cc7dc4a049c0ff9545020e),(64,0xcc9448381d399f2b0c28927052c292241c15b4f87ccd2249),(4,190)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zV:∀ ns ∈ kA, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x28e0fd2ab40838fb0cbd124039dea7ec9001c7d8b624800e),(64,0x3b533524800e074866a49041ce6a892003815ec3ff3f2e90)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zW:∀ ns ∈ kB, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kC:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x400394d0cbd9200394bccbd920039cf112400739a224800e),(55,0x75e65cc9001c75a65ec9001c6fe65c89201ceca49)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zX:∀ ns ∈ kC, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4729e997b24007296197b240073b3224800e3ae32f64800e),(64,0x32c5d2011cae36e53b488273b7224800e3a43ae36c4ae488),(9,49521525)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zY:∀ ns ∈ kD, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x395c65ec9001cad32f64800e5bd33a85100e5f73a2a4900e),(64,0x26e30820e077c7ca51241c1eddc33e37a44938df0e8a9240),(5,1844)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma zZ:∀ ns ∈ kE, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kF:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xf2211064a4a28e1120016691ac1220006028a1be211010603de1818e39210116),(48,0x3fc1bc2f221001642b18e3921010642c1e91121106411b92)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aa:∀ ns ∈ kF, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def kG:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(62,0x1e989440073fe3f8fb5220139e9512400718b437e28820e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ab:∀ ns ∈ kG, Impossible B 5 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q bB (by decide +kernel)
def Ac:BT (List (List Nat)):=refBuckets M [kt,ku,kv,kw,ky,kz,kA,kB,kC,kD,kE,kF,kG] #[1543839821,0,96,1124323333,23,37,59,75,58,401424,872562696,55,1426173956,1627643930,0,94,409610,200715,5773224763401,48,0,63,331832,0,0,368712,7,356421,33,2,340021,0x6305b049039020,389191,0,380942,327695,44,270381,266290,13,29,364579,637648915,352298,21,0,221214,0,1174503442,31,0,0,0x3302b028014006,76,319548,0,22,323609,688025634,69633,278592,360460,303107,0]
set_option maxRecDepth 20000 in
lemma ah:btAll (fun bk => ∀ xs ∈ bk, Impossible B 5 xs.toFinset) Ac:=refBuckets_all (forall_cons zP (forall_cons zQ (forall_cons zR (forall_cons zS (forall_cons zT (forall_cons zU (forall_cons zV (forall_cons zW (forall_cons zX (forall_cons zY (forall_cons zZ (forall_cons Aa (forall_cons Ab (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def kH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9cce7228827a86633a849209e0de7224904f51990e45104f),(64,0xe7924920f31433a849209e0e87224920f06133a849249ea1),(3,86)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ad:∀ ns ∈ kH, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x264ef124a0cf0675148492493c1921c512483d787924900f),(64,0xd0ea494483cdd8925000f53a9df24a009eb65e125000f277),(2,3)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ae:∀ ns ∈ kI, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb19b9a20a3cdb8924900f0e552924920f20faa672124944f),(64,0x6fe492404782e433c37944828f0d78b637928828f067379),(22,0x1da6dc6f289009ee6)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Af:∀ ns ∈ kJ, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc4924107af0fc6f251009e0e8b137244127bb8ef8924804f),(64,0x521d894412785a9dc9240279971449001e4fd0924904f07c),(4,100)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ag:∀ ns ∈ kK, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3262492003c83242492023cdcfd2492013c1b8c3ba24824f),(64,0x3c2fcfc64a4a2093c1275396a7d32525104d3d490924800f),(14,0xfe64a4a200)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ah:∀ ns ∈ kL, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdf9249009e643a52492013cc8b43a928804f52192928800f),(64,0x2410783a1b2294924927a969249001e62f0fb4924824f371),(9,8268169)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ai:∀ ns ∈ kM, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x78733251009ea7a49240079f4e84a2003c1d0fb0924824f),(64,0x89a459a7866f86c899449478664a765164d2259e7de49240),(17,880253322185843)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aj:∀ ns ∈ kN, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kO:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x17104e2c2d2521216304e292a522121605c1e851111111741cb29e231121117),(53,0x3822f3112101704e22f412111644d1e42d232211274e2c2d23221)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ak:∀ ns ∈ kO, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb8fea73512493d13b5354e6928a27b266e743a637b25148f),(64,0xc6328924f067e699945d430c28930f20eb8db168492513da),(52,0x54dbd653c319288679bb28aac6185108f06f867)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Al:∀ ns ∈ kP, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x58fdcc3092413c2c6ee61849249ee676250ca6730c28830f),(64,0xe1da75c6328924f7963ac31928847833f36ac7b8618512cf),(50,0xcee452a5147799d428838e3b550d78c30a211)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Am:∀ ns ∈ kQ, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kR:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xb4412124704e32f412111602841cb22b4412113751301a83e181ed2b18121436),(64,0x701de282d2b44121127304e2c2b4412121711fb1cc2b44121027302f1a922832),(17,0x1e8286f2b7112112)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma An:∀ ns ∈ kR, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kS:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1271cb24e4412101760014e4412121701ad1e32f311211270281ed2b71121117),(63,0x31fd282f44121117019b3869431121127038283a31121117186f6b293931121)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ao:∀ ns ∈ kS, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kT:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x701f9293a3211111732819c4f18111111702814f451111176028292e45111217),(61,0x4e1c858191111160281f58441211174b4a46f4412103601d81eb71111111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ap:∀ ns ∈ kT, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kU:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xf711111107028d1ea2e721111170481cb1c85872111127071ab286f431121137),(63,0x1d83112100171e1ee43112101718038193a3112121741cb2bb43112102702a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aq:∀ ns ∈ kU, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3ae7c92810783a57192510785a564a2013cd94ed9944804f),(64,0x9f144800f06febd5a144824f7b1b6944800f30d94a240078),(3,121)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ar:∀ ns ∈ kV, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20f04fdcdcbc5a14482cf372da9249009e6e7a9b7224804f),(64,0x7e3449041ead8b6cca240279fb9b8e33e289011e1e8fa248),(21,0x3353af399251278)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma As:∀ ns ∈ kW, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xbd5cc94413c1d0dd0dac94493ce91d649401e758ab24a00f),(64,0xe6e3f9b2924904f3a1b4ef59288278779b0ef59289279d0c),(15,8744086049281)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma At:∀ ns ∈ kX, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x64a209e6deb29cef5928847852664a2013c1d14d1924924f),(64,0x20f317b8924820f2c1fa12490c1e743bd6492413ce8ac3bd),(11,247239240)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Au:∀ ns ∈ kY, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def kZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x877e7124924f0b72be84924147af79249001eee32a24800f),(64,0x24a041e0ed5c24a041e0c98ef1524a049e013ed249249e17),(8,481892)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Av:∀ ns ∈ kZ, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def la:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8663ed449009ea5e4924007852f449041c58329f6a24860f),(64,0xdd12400783ee32a24820f0a58d124107856e3e62894493d7),(4,994)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Aw:∀ ns ∈ la, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xbab449091eaeaae8ca2402783765a924804f0f65a924820f),(64,0x30b921249049e745fc6492413dea74e8eac94423d8536322),(24,0x67d8645675bb44928f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ax:∀ ns ∈ lc, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def ld:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x17512ca3965a1110217512c97a65911112175c1da5e211100175c165a1110017),(49,0x19b5e1111100701ac4d111110171f9111110060395e211100)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ay:∀ ns ∈ ld, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24f3719149deec94423ce857f99288279fa19b9fb124904f),(64,0x24804f06653f449041e0ad7b93b289051ed6b1cc748bf449),(25,0x1d17e892003d5c7e5fa)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Az:∀ ns ∈ lf, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lg:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x100071a918f211100071f95b2b8111110174e3875a11100172c9797591111017),(47,0x2de4a3e5821110177b55811210077b5d11111007618f211)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AA:∀ ns ∈ lg, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdf95675a1249261e75c6ceb4249209ef2d2a94feb444908f),(64,0xfdfcaa24848f0bd8a5eb4449049e15f4d88fc552902cf04a),(57,0x5f55345a924824f0cfb0fea527feb524904d3d8516)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AB:∀ ns ∈ lh, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def li:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24800f0fd5912410785b973624920a3c1b56e56d892482cf),(64,0x49ebc73d2492013cdc6e7e1249011e6e7b3a892013df8ba),(16,0xbf8b5cb4289)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AC:∀ ns ∈ li, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7b0ae7abc892113c2f62da2d112412785fd5af5a144824f),(64,0x67807fab4249249eccb112400784a553925024f779911240),(22,0x15b6372962d0a241)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AD:∀ ns ∈ lj, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lk:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24824f61c954ea7449089eae37ad1124027852d5a144820f),(64,0x6776224820f06576125020f5ec36f5a124904f0e4cac53a),(19,0xae5b75a224804f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AE:∀ ns ∈ lk, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def ll:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xeae53197224827232d449001e4cb512400785275a924804f),(64,0x32f449041e4cbd1240079d71b2ad0924827af0feb4449009),(2,2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AF:∀ ns ∈ ll, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lm:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x8c321110172a7b5a3112101704e6d3f582111117418f21110007318f21110007),(50,0x402a18f211102072c18d1112000738e16858111110272df491)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AG:∀ ns ∈ lm, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def ln:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe0d94eb9da658d124a3ce916a492003cc5ec5bd5a224824f),(64,0xfb325104f0adeb664a209eae36432f449009eef32f449001),(26,0x1cd9db5944804f331979)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AH:∀ ns ∈ ln, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x537324274a67c8920187836232c2a9481479de99f124900f),(64,0xe5dd4924804f3a633f249001e0fb0fea526ea67e49209879),(31,0xa4867c512003d7ca4249201)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AI:∀ ns ∈ lp, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lq:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x11120706838181111107284a2b2b1812101728a19e2111000728919e12110007),(55,0x12bc7111111072dd1a84e711210172df1818872111017603882b181)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AJ:∀ ns ∈ lq, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3c92482783ae5e928804f5a2f4a24007837d7b99d444824f),(64,0xc658b4289059e0d94d9ccea2241279fcd94cea14402793bf),(29,0x36732d5a144824f057fcd)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AK:∀ ns ∈ lr, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def ls:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x27b98da892003dddc924800f3245e944800f0ec33a24820f),(64,0x24927bc6e33e33a85104f7757b99ccea14413c1f22f49440),(14,1406817328801)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AL:∀ ns ∈ ls, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3cc07fa67e675092513c1d299d424920f3819a9d1424940f),(64,0x3c94403c1fb267c24824f2d567728840f0eeea686750a209),(22,0x1eab45092403deeae)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AM:∀ ns ∈ lt, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x99d3f9241079fa29d428800f0ae47d449049e7d87924900f),(64,0xece8b7aa75092493cc86bb22849209e645ff372a49009ed7),(14,0xfab6449001)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AN:∀ ns ∈ lu, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24827b93a99fe7a24827b3a3b21e492493d85ff3ea24824f),(64,0x9ee736224800f77d2492003c3b4cc892083d6fd4a6487a),(15,0xe5875571e91)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AO:∀ ns ∈ lv, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x289009e7907f5e928844f5e55e944800f573b4c90f44904f),(64,0x7bd33e26e48824f0f78e1d6924924f77730a24007bdabbe3),(31,0x9eb5c4c99cd4dc51209a78)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AP:∀ ns ∈ lw, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3fd251009e61fa924900f72f3a144800f0fcca1bf124824f),(64,0x24f216b8db0f86d852091c0fb9f24a041eb5c49240078336),(16,6925627069008)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AQ:∀ ns ∈ lx, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def ly:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249291e7da6424a001e7eae125000f2177facef3e52504ce),(64,0xc492123cb077e6e2510c1e60739ba937244227906c3a13e4),(35,0xd8743e724920a3c8361d0ce6f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AR:∀ ns ∈ ly, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc4924107980f9ce8892103ce87c3e4249209e1e90924804f),(64,0x241479be2d49440079d1e87c8492413ce8bca492402798a7),(12,3073100873)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AS:∀ ns ∈ lz, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x248279961f2224800f0743273e4449049e1cef9f6928824f),(64,0xd0cb4f909248279bcf91124007b739b8f91124127838f909),(17,54199421505657)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AT:∀ ns ∈ lA, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def lB:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(60,0x7d4b4944007b5362492083cffce249201ea4a6128800f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AU:∀ ns ∈ lB, Impossible B 6 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ah (by decide +kernel)
def AV:BT (List (List Nat)):=refBuckets M [kH,kI,kJ,kK,kL,kM,kN,kO,kP,kQ,kR,kS,kT,kU,kV,kW,kX,kY,kZ,la,lc,ld,lf,lg,lh,li,lj,lk,ll,lm,ln,lp,lq,lr,ls,lt,lu,lv,lw,lx,ly,lz,lA,lB] #[4312780902,0x14a1450f50e60e00d60ce062,0x10f0ff08d08a080075,0x13a1170f60d90bb06105d04a03b039,85865883159191660,0x12d1230e40a807c05e,4345565242,82772407865364542,23916861181956,0x15213f1300c90be0a0011,5218734089,3406274589,9553433600064,75442097792139282,0x13412712105f05a031,0xc504e02f019,22200988840024,0x1090b109a06d05b024,89,80801326241792075,3054002308,0xf003800a002,0x13b1221080dc074025,0x14012f06f06702e00e,17733501038693,93188699923742824,0x1331130f40d70d30c409d056048001,18351825563763,0xee0ed06e057052016,0x14713d1320fe0f80c0021,0x151092077054047008,5688824132,0x1241190f10d10c80ac09706904f037,4749054130,0x15a14c12e0e10dd0cd0ba09e08307202a01f01800b,790661,5822394391,0xf30d40a5081,5252026411,3490156656,87277586648567868,0x15014f14e11a10e0ae,0x1410c30b80a109f08e003,0x12911c0e50bd026015,0xeb0c609b09103f027,1409159,0x1461161140a707f053036029013,0xfb09c08f089088071,89522926394867739,4798390287,0x15913c0ef0cf05103201c010,0x1561050b709908c064060,0xec0b4043035014007,84176002036740126,0x11d1100e80c20b50af09800c,0x1550e20d5046045023,0x10a1071040d20a407d044,22886924853324,0x1421380fa0ea0a2022006005,0x12c1251180bf0aa09508206b04902000d,126,0x1570f20e30a60a309603402d,0x1351200f70df0b0078028,5705597205]
set_option maxRecDepth 20000 in
lemma aC:btAll (fun bk => ∀ xs ∈ bk, Impossible B 6 xs.toFinset) AV:=refBuckets_all (forall_cons Ad (forall_cons Ae (forall_cons Af (forall_cons Ag (forall_cons Ah (forall_cons Ai (forall_cons Aj (forall_cons Ak (forall_cons Al (forall_cons Am (forall_cons An (forall_cons Ao (forall_cons Ap (forall_cons Aq (forall_cons Ar (forall_cons As (forall_cons At (forall_cons Au (forall_cons Av (forall_cons Aw (forall_cons Ax (forall_cons Ay (forall_cons Az (forall_cons AA (forall_cons AB (forall_cons AC (forall_cons AD (forall_cons AE (forall_cons AF (forall_cons AG (forall_cons AH (forall_cons AI (forall_cons AJ (forall_cons AK (forall_cons AL (forall_cons AM (forall_cons AN (forall_cons AO (forall_cons AP (forall_cons AQ (forall_cons AR (forall_cons AS (forall_cons AT (forall_cons AU (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))
def lC:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc62b4f249299e16260339c8924987904984c321c4924a354),(64,0x50928030f0b346ab8e2492498a038d49a94e249249aa1079),(57,0x379c61f5f24a059e0946b8b28f124a04e50bc71867)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AW:∀ ns ∈ lC, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xea02b466e24a20a5082ae3652492523c83b980d9892504cf),(64,0x24909a80a86d33b30ce4924135420d29e74f54ea6f249211),(58,0x38b1f492490528be38c3b1bc92480d420c3e9b96379)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AX:∀ ns ∈ lD, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4a037998ec492412a1b49d7924920250198da55e492482d4),(64,0xb5c58fc492482d406478e309d8924826280ce61b0ea89241),(41,0x3163b124904a81e86287624920a502)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AY:∀ ns ∈ lE, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lF:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x101261012d4a6418b11111025710123f2b61a6a1111102673d4a47b111110037),(64,0x1db11111016705429148281cb12110166013d4a1a18911111014707f1a189112),(31,0x21f1d6941dd12110156011e1d2d3b4)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma AZ:∀ ns ∈ lF, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xca9d092482940b998fe8dcb9b8924826a843bcf90924844f),(64,0x6492518a0469baac992492d460cc6f3e191da4924230f08d),(60,0x302b8da9928a27a243fde3a033269130c38828cfccce2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ba:∀ ns ∈ lG, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd8f58c6492498a079fe743d4319249262842b94e6924944f),(64,0x2494a07a1b4dab386324924c502f1459586324925a80d54d),(64,0xe63251679e99282ca5539d1630ce6185138e381db9ef18c9),(20,0x282355aef31630c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bb:∀ ns ∈ lH, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lI:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1111372102e284f4311111321835304b4a44f441111437301b82a4e431121227),(64,0x298711111347102d119719a71111124703f1ab28584311111131804b4a458441),(31,0x210641cb2d4311111331831802d1197)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bc:∀ ns ∈ lI, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe6324924a88874ddd190dc632492cc50836c571d9924948f),(64,0xf39b938c92826a03b19eb2492095019e191924904a80cc7d),(64,0x60af513a9326366651211e79866abc5163e38c9280354609)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bd:∀ ns ∈ lJ, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24908c501dfaa6e3267c92482d45bbf953719738ca240314),(64,0x7c92482d40e432554c331b3b249209aa181daf754dca48f9),(64,0x4946175f3dcfea464924231406d2ff7c9248294066c6d275),(18,6888287573414472)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Be:∀ ns ∈ lK, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6fef324925a81de77ac924825444198fe8dc77ac924b30f),(64,0x9492486d42c190dc6486524921a503bcfcc9248254066e6e),(64,0x3ac3799492482544c8366332b3324920c4a160cb0c331ff1),(1,0)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bf:∀ ns ∈ lL, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb8f9992490928c1369b8c3293ed249211c787e9949248214),(64,0x77324921150292994924821406cc663ac3292490528c1961),(64,0xf8c8e2f11cb1bfb249211ea03745b38b35a124904c51856f),(3,194)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bg:∀ ns ∈ lM, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd5924930a8e478c5fe289019cc1beaf1438c3ff649242354),(64,0xec1f0fb0c856ed12426a30a686198dd5924909a8d10ae331),(64,0xc61b22fc9240679a42b8e5a12490ca8d1442b8e5a9248389),(5,10708)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bh:∀ ns ∈ lN, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x27ec4924238f615caab492484542c13b990da55a4924334f),(64,0xc62ff3249299ed1064c6e3219e2f8924831a8c2b89dcc86d),(64,0x3f1daaa6e57e649241354615877e645665e324929a8c29d4),(28,0x349415c748bf4490693c3)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bi:∀ ns ∈ lO, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x277321b4aba12490cd3c2b8f5a124904a8c2b8f5a924844f),(64,0x24a019c69809dcc86d267a4924334f0ae3b55f924904a858),(47,0xf1da1249009eef78c5a4449019ce5464576)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bj:∀ ns ∈ lP, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2d460fb09dcc86d27f5492484728c38a7e663245a12494cf),(64,0x3693bba492416a03f4264c7d5c92482d40b586c47e589248),(64,0x8492414a05b53693a19092482d4615d15c7678924849406e),(13,23592378134)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bk:∀ ns ∈ lQ, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5a12490528c29f190dce2d092484d460c86d26a9c92484d4),(64,0x242671615cd5a492432a1283aa7cae3f2d112418cf06d27d),(64,0x3fad11243679a90277321b49979249061a7a0a29aab8cbd1),(12,10780043950)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bl:∀ ns ∈ lR, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc648ad64924950fdceb5924904f2c28a6aae3fad092486d4),(64,0x4490d9e1798da4c99924905a8c29f190dce55a124909a815),(64,0x571b72d0924829461d3343763fab5a2484d42828ead31963),(5,878)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bm:∀ ns ∈ lS, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xea631c9592494cf53a98c5752492033d4ea631cb092480cf),(64,0x24844f064a76aa9b95f1924904c50198cb8fdd9249254614),(61,0x36232c589248294609dcc86d265aa924908d50c0f2d09)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bn:∀ ns ∈ lT, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3cda5fc64249202518571923c492422a13263275c9248094),(64,0x24924a80afe1995ea53c92496a1c14b5def18ed33a84928c),(64,0xb8c5d45092413143483ac7bac61f71e49259878525532b8f),(8,773737)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bo:∀ ns ∈ lU, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20a50844eae674c33e3ca24238f057f4c3293f3e49241354),(64,0x472ca787924904c501b638b1f0ca492416a0366322ab2849),(64,0x3e3d0cecda672492118a03b4337369c61ee2849209aa033f),(29,0x2bfa6767633924904c518)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bp:∀ ns ∈ lV, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xcf3c824c3a2b1d30eb8f28908f3d8369b563ac3c92484d4),(64,0xa492414a03bd30d7942490528d83ae721369b8c332be9249),(64,0xe0eb8ef8c56e3c92482d406d86767436924905a81bb619cd),(34,0xb441d63dd630cf8cea1249a61)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bq:∀ ns ∈ lW, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20d31426306d8ae6772490623d360fb4c3a74675092418d4),(64,0x24900a8690e2b233cf3a53c924b34f4d106f3674f333a849),(64,0x512288571b0cea124838a8d5f53c67c673c92496a3c74a79),(23,0xc1b8c86d33a849212)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Br:∀ ns ∈ lX, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2490c9e790ae78daa124865445837b914a6667624920c314),(64,0x4a10a75318edaa12484cf3c846474dca1248694358573a7e),(64,0x323a7d24921b5039f1992d09248294441b8c8bcca7509243),(9,28061690)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bs:∀ ns ∈ lY, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def lZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc492412a057733192294f24925288873d46476d3c92486d4),(64,0x2432a0331aa53c94412a30ec8f326c36124908c503d29b8c),(64,0x5cb0fca53d12434a1a89b62b973e92490d28616ae70f849),(2,11)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bt:∀ ns ∈ lZ, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def ma:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x44909a879514d55c6487924909a848514d55c6487a2486cf),(64,0x8d8b2f492482940bfa8d8aaf492482d460ec6d5a63fa94f),(64,0xb8924830a859daaebd24921150b5793b990da5e84924238f),(11,1359895674)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bu:∀ ns ∈ ma, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def mb:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2418d4351064eae321f492483128c394ff0d955c79249494),(64,0x3092482d4074876aa9b8e99924904c51a20fdce3a7729e49),(64,0x33d3a124905a80f56c76aa6e33f37124904d5039baa6e3a5),(35,0xc85af7f18efe5121b383b62a6e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bv:∀ ns ∈ mb, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def mc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2b4e4924334f302b8ea7fa492422a29d4c629e9b212480cf),(64,0xc6437d3fd24921a51230dc64571fe92490d2861809dcc86d),(64,0x4133cc3039b3a7f5ac24921b3cf215c6d867e492432a320d),(21,0x10bdce7321d2be49)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bw:∀ ns ∈ mc, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def md:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86424a099e42d79b218758e12504cf2177fac75ea92504cf),(64,0x86e8742492135085cccb9b11b8dd8dc4924239421fce2c74),(64,0x502e663fa371b0f90924826a81e58cbd6a492414a30b9b0e),(19,0xc1d0d3e4249211)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Bx:∀ ns ∈ md, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def me:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x24921350a209b4dc71902969249061c783a1d4f909248254),(64,0x81e59587c8492414a306deb29cf90924849460fe8dc6d3e4),(22,0x187163ec329249092)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma By:∀ ns ∈ me, Impossible B 7 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q aC (by decide +kernel)
def Bz:BT (List (List Nat)):=refBuckets M [lC,lD,lE,lF,lG,lH,lI,lJ,lK,lL,lM,lN,lO,lP,lQ,lR,lS,lT,lU,lV,lW,lX,lY,lZ,ma,mb,mc,md,me] #[536617,0xd90b00a906b06205d021,0xae06704c04902a,0xc60c10ab09b099058,2097475629,0xa40a003202f,8866775613465,0xdd0ce0ac03401b,3741773832,8178792402962,0,3439894629,3070619739,0xb806404201d,0xbe0a206a053028,2416193539,0xcf0bf072050,150,0xb60a504a026024,0xaa07e059005,61,3221504016,3590901844,0xe20ad09104003b00d,0xe506c01e006,426001,0xd80c808500b,0xcc0c30b206004b,622641,3104522250,0xc209e092020007,917690,0,2063966217,0xa807a06604803e018,868519,3657982012,0xd507c078033030001,0,7697521135644,130,0xbb09304503a02b,3389636627,0x9f08006e02e025,0xa60a109706105e,3507171415,2131136546,471153,3859345489,3825287180,0,0xcb0bd0b10a3047,315415,815118,0xd309a08904e,0xd709508e08b07406d02300f,823395,0xe30de084039004,0xdb09407905c016015,3289104438,9277783797762,0xe10d00b5056055052037,0xdc0d208c08807601a,0xc50af09d03f]
set_option maxRecDepth 20000 in
lemma ct:btAll (fun bk => ∀ xs ∈ bk, Impossible B 7 xs.toFinset) Bz:=refBuckets_all (forall_cons AW (forall_cons AX (forall_cons AY (forall_cons AZ (forall_cons Ba (forall_cons Bb (forall_cons Bc (forall_cons Bd (forall_cons Be (forall_cons Bf (forall_cons Bg (forall_cons Bh (forall_cons Bi (forall_cons Bj (forall_cons Bk (forall_cons Bl (forall_cons Bm (forall_cons Bn (forall_cons Bo (forall_cons Bp (forall_cons Bq (forall_cons Br (forall_cons Bs (forall_cons Bt (forall_cons Bu (forall_cons Bv (forall_cons Bw (forall_cons Bx (forall_cons By (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))
def mf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x349b92789250469ec232a47924a08c3c8389301c4924a34f),(64,0x269e1194caa98718752492413d420bce9c61b8924908d508),(64,0x8e4249211e790a759d38c5e124908d3c2329b4ce62dc9248),(15,4482354562316)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BA:∀ ns ∈ mf, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def mg:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24904d3c871736286452924908d3c84745f230ce4924234f),(64,0x53a98c063249271c79217873c744c924b30f04fcbe38c729),(64,0x4647992490cf50b0af463dcd30c3338c92486a28cd2482a5),(43,0xc13a3ee9c62d1924908e50b0a744f334)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BB:∀ ns ∈ mg, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def mh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x449211b53f5f78e5318b7649241eaa80eaa63149492482cf),(64,0xc6436524920c34f34940d3ea51da7d394c62f1924906aaa3),(64,0x84924250f34940ed8f86438c8a7e49241a69e4a076a7c321),(64,0x219ca1a4a0b426d38c8a3a56849241aa1e81369cf1b190ac),(25,0x1411f0cb0dc9e56b249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BC:∀ ns ∈ mh, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def mi:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x469e503274b9b69e7f3f7649243394614ea630ff892484cf),(64,0x24908e519054b4cb4c066879249669e813b990da4cf89248),(64,0x24908f5083af39136538c3963c92484a28427f9a6c462879),(51,0xc83ad276e8c3692490cd3c8474369b4c463879)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BD:∀ ns ∈ mi, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def mj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4512483e43772f19d42490a1879075a4edd18f1e49242354),(64,0x95def18a7509241879ec92143b452bdcaa619cf24920d3d4),(64,0x2d4a7924906a8a2211f3a95def18a73c9248672851049f3a),(64,0xea3309241d31bcabd786e5e9249079c7b248275ca5539d16),(38,0x9241b31bca91da64315c79249069)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BE:∀ ns ∈ mj, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def ml:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xd7291e1fd11111035730182ac18d44d5b111102473102cf4a3b41cd111110347),(64,0x4674121013ad53a1a811111054723306a4b381a45e19f11111045182601a81a),(64,0xa3b418e1f1211036712105d213917e41ad12110476121011de1eb61e221f1112),(8,822219700)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BF:∀ ns ∈ ml, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def mm:List NodeSpec:=readDeltaNodes 2 (varNats 3 (unpackWords 4 [(54,0x1033e1c4f281bf291111102518412101b2a1b2c22e1e8111110567)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BG:∀ ns ∈ mm, Impossible B 8 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q ct (by decide +kernel)
def BH:BT (List (List Nat)):=refBuckets M [mf,mg,mh,mi,mj,ml,mm] #[0,822247453,0,184351,36,73732,47,19,24,15,167971,0,43,0,0,0,13,188455,0,9,0,6,0,27,0,0,838873090,20,0,21,0,28,0,1,14,0,37,0,102416,38,30,0,139297,0,44,8,0,7,0,10,0,11,42,0,0,106519,196630,12,32,0,69637,0,0,0]
set_option maxRecDepth 20000 in
lemma BI:btAll (fun bk => ∀ xs ∈ bk, Impossible B 8 xs.toFinset) BH:=refBuckets_all (forall_cons BA (forall_cons BB (forall_cons BC (forall_cons BD (forall_cons BE (forall_cons BF (forall_cons BG (fun _ h => (List.not_mem_nil h).elim))))))))
def mn:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x242861e69281bb9cf1d0324920d34f20cae9c9024924238f),(64,0x38f3092412af865a6033f24920e38f6592483af3ac381e49),(53,0x144226caf2329249061a794427f9a6e49f24920c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BJ:∀ ns ∈ mn, Impossible B 9 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q BI (by decide +kernel)
def BK:BT (List (List Nat)):=refBuckets M [mn] #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,6,0,0,0,0,0,0,4]
set_option maxRecDepth 20000 in
lemma BL:btAll (fun bk => ∀ xs ∈ bk, Impossible B 9 xs.toFinset) BK:=refBuckets_all (forall_cons BJ (fun _ h => (List.not_mem_nil h).elim))
def mo:List NodeSpec:=readDeltaNodes 1 (unpackWords 5 [(20,0x10c2108414b08010842101c86)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BM:∀ ns ∈ mo, Impossible B 10 (nodeValsBT M ns).toFinset:=blockOk X 9 (by decide) N O Y Q BL (by decide +kernel)
def BN:BT (List (List Nat)):=refBuckets M [mo] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma BO:btAll (fun bk => ∀ xs ∈ bk, Impossible B 10 xs.toFinset) BN:=refBuckets_all (forall_cons BM (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dy:Lower aq B 11:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 6,1,65)]) (by decide +kernel) BO (by decide +kernel)
def dz:List Nat:=varsOf 138
def dA:Nat:=0xffccffccffccffccffccffccffccffcccc00cc00cc00cc00cc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eE:Lower dz dA 4:=carry_of (swaps:=[(6,7),(5,7),(4,7),(2,3),(0,1)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def dB:List Nat:=varsOf 143
def dC:Nat:=0xfffefffefffefffefffefffefffefffeeca0eca0eca0eca0eca0eca0eca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eF:Lower dB dC 8:=carry_of (swaps:=[(6,7)]) (roots2:=aJ) (T2:=ap) (by decide +kernel) bK
def mq:List Nat:=varsOf 153
def mr:Nat:=0xffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000aaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BP:Lower mq mr 5:=carry_of (swaps:=[(6,7),(2,4),(1,3)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def ms:List Nat:=varsOf 154
def mu:Nat:=0xffffffccffffffccffffffccffffffcccc00cc00cc00cc00cc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BQ:Lower ms mu 5:=carry_of (swaps:=[(3,4),(6,7),(2,3),(0,4),(1,4)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def eG:List Nat:=varsOf 155
def eH:Nat:=0xffffffeeffffffeeffffffeeffffffeeeeaacc00eeaacc00eeaacc00eeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mv:Lower eG eH 8:=carry_of (swaps:=[(6,7),(2,4)]) (roots2:=aJ) (T2:=ap) (by decide +kernel) bK
def mw:List Nat:=varsOf 156
def mx:Nat:=0xfffffff0fffffff0fffffff0fffffff0f0f00000f0f00000f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BR:Lower mw mx 5:=carry_of (swaps:=[(3,4),(6,7),(2,4),(0,2),(1,3)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def eI:List Nat:=varsOf 158
def eJ:Nat:=0xfffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00fcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma my:Lower eI eJ 8:=carry_of (swaps:=[(6,7),(2,4),(3,4),(1,2),(0,1)]) (roots2:=aJ) (T2:=ap) (by decide +kernel) bK
def mz:List Nat:=varsOf 157
def mA:Nat:=0xfffffffffffffffffffffffffffffffffffaffa0fffaffa0fffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BS:Lower mz mA 6:=carry_of (swaps:=[(6,7)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def eK:List Nat:=varsOf 159
def eL:Nat:=0xfffffffefffffffefffffffefffffffefefaeca0fefaeca0fefaeca0fefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mB:Lower eK eL 11:=carry_of (swaps:=[(6,7)]) (roots2:=aq) (T2:=B) (by decide +kernel) dy
def cO:List Nat:=varsOf 202
def cP:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cC:Lower cO cP 7:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,3),(0,1)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def cQ:List Nat:=varsOf 203
def cR:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeecc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dD:Lower cQ cR 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(1,2),(0,1),(0,3)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def dE:List Nat:=varsOf 206
def dF:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eM:Lower dE dF 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(0,1),(2,3)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def mC:List Nat:=varsOf 199
def mD:Nat:=0xfffffffffffffffffefefefefefefefefefefefefefefefea0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BU:Lower mC mD 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(1,3)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def mE:List Nat:=varsOf 205
def mF:Nat:=0xfffffffffffffffffffafffafffafffafffafffafffafffaa0a0a0a0a0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BV:Lower mE mF 8:=carry_of (swaps:=[(5,7),(6,7),(4,6)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def bo:List Nat:=varsOf 207
def aK:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffeeca0eca0eca0eca0
def eN:List Nat:=[5,10,7,11,65,68,5,10,11,13,66,65,130,129,129,7,14,66,72,130,13,14,68,132,132,72,136,136,192,192]
def eO:List Nat:=[4,8,6,9,64,64,1,2,3,12,2,1,2,1,128,3,12,64,64,128,9,6,4,4,128,8,8,128,64,128]
def mG:Nat:=fullMask 30
def mH:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x10eb5d,0x10a948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2b958e,0x209584),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f18265,0xe10205),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xe35038a,0x611020a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x32460c30,0x10060030),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3d887000,0x29084000)]
def BW:List (Nat × Nat × Nat):=[]
def cS:BT Decor:=buildWiresBT 3 mH BW
def BX:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(0,2)],[(6,7),(1,3)],[(2,3),(0,1)],[(6,7),(0,2)],[(1,3),(0,2)],[(1,2),(0,3)],[(6,7),(2,3),(0,1)],[(2,3),(1,2),(0,1)],[(6,7),(1,3),(0,2)],[(2,3),(1,3),(0,3)],[(6,7),(1,2),(0,3)],[(6,7),(2,3),(1,2),(0,1)],[(6,7),(2,3),(1,3),(0,3)]]
def eP:BT (List (Nat × Nat)):=btOfList 4 BX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BY:goodPairs aK eN eO:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma BZ:∀ x ∈ mH, faithful eN eO x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ca:btAll (fun x => faithful eN eO x ∧ x.1 < 2^256) cS:=buildWiresBT_faithful BZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cb:btAll (fun sw => swapsValid sw = true ∧ permWord sw aK = aK) eP:=btAll_ofList (autos_of (by decide +kernel))
def Cc:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 64 0,8)]
def mI:BT (Option (Nat × Nat)):=btOfList 3 Cc
def Cd:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 5 (unpackWords 3 [(10,67903552)])
def eQ:BT (Option BoundPool):=buildPoolsBT 3 cS bo mI Cd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ce:Slice bo aK (subcubeFast 64 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dB) (qGoal:=dC) (by decide +kernel) eF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cf:Slice bo aK (subcubeFast 8 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=mC) (qGoal:=mD) (by decide +kernel) BU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cg:Slice bo aK (subcubeFast 4 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cQ) (qGoal:=cR) (by decide +kernel) dD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ch:Slice bo aK (subcubeFast 2 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=mE) (qGoal:=mF) (by decide +kernel) BV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ci:Slice bo aK (subcubeFast 1 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dE) (qGoal:=dF) (by decide +kernel) eM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cj:btAll (fun o => ∀ p, o = some p → Slice bo aK p.1 p.2) mI:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bo aK p.1 p.2) (forall_cons (someSlice Ci) (forall_cons (someSlice Ch) (forall_cons (someSlice Cg) (forall_cons (someSlice Cf) (forall_cons (someSlice Ce) (fun _ h => (List.not_mem_nil h).elim))))))
lemma Ck:btAll (fun o => ∀ c, o = some c → ValidPool bo aK c) eQ:=buildPoolsBT_sound Cj
def eR:BT (List (List Nat)):=BT.empty
lemma Cl:btAll (fun bk => ∀ xs ∈ bk, Impossible aK (9 - 1) xs.toFinset) eR:=trivial
def mJ:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(14,628158140462)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cm:checkNodesBT cS aK mG eQ eP eR 9 mJ = true:=by decide +kernel
def mK:List NodeSpec:=mJ
set_option maxRecDepth 20000 in
lemma Cn:checkNodesBT cS aK mG eQ eP eR 9 mK = true:=Cm
def Co:BT (List (List Nat)):=buildBucketsBT cS mK
set_option maxRecDepth 20000 in
lemma Cp:btAll (fun bk => ∀ xs ∈ bk, Impossible aK 9 xs.toFinset) Co:=buildBucketsBT_sound (by decide) BY Ca Ck Cb Cl Cn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cD:Lower bo aK 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Cp (by decide +kernel)
def dG:List Nat:=varsOf 215
def dH:Nat:=0xfffffffffffffffffffffefefffffefefffffefefffffefefafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eS:Lower dG dH 11:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,64,66)]) (by decide +kernel) bF
def eT:List Nat:=varsOf 216
def eU:Nat:=0xffffffffffffffffffffff00ffffff00ffffff00ffffff000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mL:Lower eT eU 5:=lift_of (z:=8) (o:=0) (essPairs:=[(VAR 3,64,72)]) (by decide +kernel) iD
def eV:List Nat:=varsOf 217
def eW:Nat:=0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mM:Lower eV eW 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,4)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def eX:List Nat:=varsOf 218
def eY:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffcccc00cc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mN:Lower eX eY 8:=carry_of (swaps:=[(5,7),(6,7),(4,6),(2,4),(0,1),(3,4)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def eZ:List Nat:=varsOf 219
def fa:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeeeaacc00eeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mO:Lower eZ fa 10:=carry_of (swaps:=[(2,4)]) (roots2:=bo) (T2:=aK) (by decide +kernel) cD
def fb:List Nat:=varsOf 220
def fc:Nat:=0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0f0f00000f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mP:Lower fb fc 8:=carry_of (swaps:=[(5,7),(1,7),(6,7),(4,6),(2,4),(0,2)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def fd:List Nat:=varsOf 221
def ff:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafafaa0a0fafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mQ:Lower fd ff 11:=carry_of (swaps:=[(1,3)]) (roots2:=dG) (T2:=dH) (by decide +kernel) eS
def fg:List Nat:=varsOf 222
def fh:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfcf0cc00fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mR:Lower fg fh 10:=carry_of (swaps:=[(2,4),(3,4),(1,2),(0,1)]) (roots2:=bo) (T2:=aK) (by decide +kernel) cD
def bR:List Nat:=varsOf 215
def bS:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffefeececfefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ci:Lower bR bS 7:=lift_of (z:=194) (o:=0) (essPairs:=[(VAR 1,0,2),(VAR 6,0,64),(VAR 7,0,128)]) (by decide +kernel) aG
def mS:List Nat:=varsOf 221
def mT:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffaffa0fffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cq:Lower mS mT 7:=carry_of (swaps:=[(1,3)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def ao:List Nat:=varsOf 223
def ac:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefefaeca0fefaeca0
def fi:List Nat:=[5,10,7,11,17,20,5,10,11,13,20,17,66,65,130,129,7,14,66,72,19,26,130,19,22,13,14,68,132,25,26,72,136,136,80,80,144,144,192,192,65,68,73,82,67,129,25,131,132,137,10,65,67,19,17,146]
def fj:List Nat:=[4,8,6,9,16,16,1,2,3,12,4,1,2,1,2,1,3,12,64,64,3,24,128,18,18,9,6,4,4,9,18,8,8,128,16,64,16,128,64,128,64,64,9,18,3,128,24,3,128,9,0,3,1,1,3,18]
def PC:Nat:=fullMask 56
def mU:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7af5002291ab5d,0x7a94002211a948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xb4980045f7518e,0xc8980045915184),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x102001f030665,0x1c020605),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x64403e62a038a,0x24401a222020a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xe0483c61b00c30,0x80481441a00030),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x181fcc880c3000,0x348000c0000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x83a0f31040c000,0x120a200400000)]
def Cr:List (Nat × Nat × Nat):=[(1,0,2),(0,1,3),(1,1,3),(2,1,3),(1,1,5),(2,1,5),(1,1,7),(1,5,13),(3,1,14),(3,4,14),(3,5,14),(1,5,7),(1,6,18),(3,0,19),(1,4,19),(3,0,21),(3,4,21),(1,0,8),(0,1,23),(1,1,23),(2,1,23),(3,1,23),(1,5,8),(1,8,23),(3,8,23),(0,3,30),(3,3,26),(3,6,19)]
def aT:BT Decor:=buildWiresBT 6 mU Cr
def Cs:List (List (Nat × Nat)):=[[],[(6,7)],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(6,7),(2,4)],[(6,7),(1,3)],[(2,4),(1,3)],[(6,7),(0,2)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(1,3),(0,4)],[(6,7),(2,4),(1,3)],[(6,7),(2,4),(0,2)],[(6,7),(1,3),(0,2)],[(2,4),(1,3),(0,2)],[(6,7),(2,4),(0,4)],[(2,4),(1,3),(0,4)],[(6,7),(1,3),(0,4)],[(6,7),(2,4),(1,3),(0,2)],[(6,7),(2,4),(1,3),(0,4)]]
def Ct:BT (List (Nat × Nat)):=btOfList 5 Cs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bT:goodPairs ac fi fj:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cu:∀ x ∈ mU, faithful fi fj x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bU:btAll (fun x => faithful fi fj x ∧ x.1 < 2^256) aT:=buildWiresBT_faithful Cu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bV:btAll (fun sw => swapsValid sw = true ∧ permWord sw ac = ac) Ct:=btAll_ofList (autos_of (by decide +kernel))
def Cv:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,7),some (subcubeFast 0 8,7),some (subcubeFast 1 0,10),some (subcubeFast 2 0,11),some (subcubeFast 3 0,8),some (subcubeFast 4 0,10),some (subcubeFast 5 0,8),some (subcubeFast 6 0,8),some (subcubeFast 7 0,5),some (subcubeFast 8 0,11),some (subcubeFast 11 0,7),some (subcubeFast 16 0,10),some (subcubeFast 17 0,8),some (subcubeFast 20 0,8),some (subcubeFast 21 0,7),some (subcubeFast 64 0,11),some (subcubeFast 64 2,6),some (subcubeFast 65 0,8),some (subcubeFast 67 0,5),some (subcubeFast 68 0,8),some (subcubeFast 69 0,5),some (subcubeFast 70 0,5),some (subcubeFast 80 0,8),some (subcubeFast 85 0,4),some (subcubeFast 128 0,11),some (subcubeFast 128 2,6),some (subcubeFast 129 0,8),some (subcubeFast 132 0,8),some (subcubeFast 133 0,5),some (subcubeFast 144 0,8),some (subcubeFast 149 0,4),some (subcubeFast 192 0,6),some (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,11)]
def Cw:BT (Option (Nat × Nat)):=btOfList 6 Cv
def bW:Nat → Option PoolSpec:=lookSpec 26 #[(1,0,2),(1,5,13),(3,4,14),(1,1,7),(1,5,7),(1,6,18),(3,0,19),(1,4,19),(3,4,21)] #[0x50230000001e122028d091018440000c1c24406061018087870c043c006021e1828103000000b8000002c004021e000001806080818004040c000001e0000009000008c0000043c000001c000010900000028000040c00000040000003]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cx:Slice ao ac (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333) 11:=mappedSlice (f:=identifyRow 0 0 4 1) (R:=cJ) (G:=cK) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) dj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cy:Slice ao ac (subcubeFast 192 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=cA) (qGoal:=cB) (by decide +kernel) cL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Cz:Slice ao ac (subcubeFast 149 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CA:Slice ao ac (subcubeFast 144 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aJ) (qGoal:=ap) (by decide +kernel) bK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CB:Slice ao ac (subcubeFast 133 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=eu) (qGoal:=ev) (by decide +kernel) jN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CC:Slice ao ac (subcubeFast 132 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dt) (qGoal:=du) (by decide +kernel) ew
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CD:Slice ao ac (subcubeFast 129 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dv) (qGoal:=dw) (by decide +kernel) ex
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CE:Slice ao ac (subcubeFast 128 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=aR) (qGoal:=aS) (by decide +kernel) aW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CF:Slice ao ac (subcubeFast 128 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=aq) (qGoal:=B) (by decide +kernel) dy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CG:Slice ao ac (subcubeFast 85 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=dz) (qGoal:=dA) (by decide +kernel) eE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CH:Slice ao ac (subcubeFast 80 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dB) (qGoal:=dC) (by decide +kernel) eF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CI:Slice ao ac (subcubeFast 70 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=mq) (qGoal:=mr) (by decide +kernel) BP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CJ:Slice ao ac (subcubeFast 69 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=ms) (qGoal:=mu) (by decide +kernel) BQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CK:Slice ao ac (subcubeFast 68 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eG) (qGoal:=eH) (by decide +kernel) mv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CL:Slice ao ac (subcubeFast 67 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=mw) (qGoal:=mx) (by decide +kernel) BR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CM:Slice ao ac (subcubeFast 65 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eI) (qGoal:=eJ) (by decide +kernel) my
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CN:Slice ao ac (subcubeFast 64 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=mz) (qGoal:=mA) (by decide +kernel) BS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CO:Slice ao ac (subcubeFast 64 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=eK) (qGoal:=eL) (by decide +kernel) mB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CP:Slice ao ac (subcubeFast 21 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=cO) (qGoal:=cP) (by decide +kernel) cC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CQ:Slice ao ac (subcubeFast 20 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cQ) (qGoal:=cR) (by decide +kernel) dD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CR:Slice ao ac (subcubeFast 17 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dE) (qGoal:=dF) (by decide +kernel) eM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CS:Slice ao ac (subcubeFast 16 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bo) (qGoal:=aK) (by decide +kernel) cD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CT:Slice ao ac (subcubeFast 11 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ed) (qGoal:=ee) (by decide +kernel) iG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CU:Slice ao ac (subcubeFast 8 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=dG) (qGoal:=dH) (by decide +kernel) eS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CV:Slice ao ac (subcubeFast 7 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=eT) (qGoal:=eU) (by decide +kernel) mL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CW:Slice ao ac (subcubeFast 6 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eV) (qGoal:=eW) (by decide +kernel) mM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CX:Slice ao ac (subcubeFast 5 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eX) (qGoal:=eY) (by decide +kernel) mN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CY:Slice ao ac (subcubeFast 4 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=eZ) (qGoal:=fa) (by decide +kernel) mO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma CZ:Slice ao ac (subcubeFast 3 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=fb) (qGoal:=fc) (by decide +kernel) mP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Da:Slice ao ac (subcubeFast 2 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=fd) (qGoal:=ff) (by decide +kernel) mQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Db:Slice ao ac (subcubeFast 1 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fg) (qGoal:=fh) (by decide +kernel) mR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dc:Slice ao ac (subcubeFast 0 8) 7:=slice_fast_direct (zDead:=0) (qRoots:=bR) (qGoal:=bS) (by decide +kernel) ci
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dd:Slice ao ac (subcubeFast 0 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=mS) (qGoal:=mT) (by decide +kernel) Cq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bX:btAll (fun o => ∀ p, o = some p → Slice ao ac p.1 p.2) Cw:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice ao ac p.1 p.2) (forall_cons (someSlice Dd) (forall_cons (someSlice Dc) (forall_cons (someSlice Db) (forall_cons (someSlice Da) (forall_cons (someSlice CZ) (forall_cons (someSlice CY) (forall_cons (someSlice CX) (forall_cons (someSlice CW) (forall_cons (someSlice CV) (forall_cons (someSlice CU) (forall_cons (someSlice CT) (forall_cons (someSlice CS) (forall_cons (someSlice CR) (forall_cons (someSlice CQ) (forall_cons (someSlice CP) (forall_cons (someSlice CO) (forall_cons (someSlice CN) (forall_cons (someSlice CM) (forall_cons (someSlice CL) (forall_cons (someSlice CK) (forall_cons (someSlice CJ) (forall_cons (someSlice CI) (forall_cons (someSlice CH) (forall_cons (someSlice CG) (forall_cons (someSlice CF) (forall_cons (someSlice CE) (forall_cons (someSlice CD) (forall_cons (someSlice CC) (forall_cons (someSlice CB) (forall_cons (someSlice CA) (forall_cons (someSlice Cz) (forall_cons (someSlice Cy) (forall_cons (someSlice Cx) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))
def De:BT (List (List Nat)):=BT.empty
lemma Df:btAll (fun bk => ∀ xs ∈ bk, Impossible ac (5 - 1) xs.toFinset) De:=trivial
def mV:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(9,29582557190)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dg:∀ ns ∈ mV, Impossible ac 5 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Df (by decide +kernel)
def Dh:BT (List (List Nat)):=refBuckets aT [mV] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Di:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 5 xs.toFinset) Dh:=refBuckets_all (forall_cons Dg (fun _ h => (List.not_mem_nil h).elim))
def mW:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0x449001e742892003c1c65649041e43c5168207932944900f),(32,0x58ca592003d532964800f3a9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dj:∀ ns ∈ mW, Impossible ac 6 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Di (by decide +kernel)
def Dk:BT (List (List Nat)):=refBuckets aT [mW] #[7,0,0,0,0,0,0,1,0,0,0,0,0,0,0,24581,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma mX:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 6 xs.toFinset) Dk:=refBuckets_all (forall_cons Dj (fun _ h => (List.not_mem_nil h).elim))
def mY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x51d30a2480140f3289208519051b1f4512436a190924900f),(55,0x1994a24821446528920051738a24801470d289200)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dl:∀ ns ∈ mY, Impossible ac 7 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV mX (by decide +kernel)
def mZ:List NodeSpec:=readDeltaNodes 2 (unpackWords 5 [(22,0xb10882108000412211042100008)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dm:∀ ns ∈ mZ, Impossible ac 7 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV mX (by decide +kernel)
def Dn:BT (List (List Nat)):=refBuckets aT [mY,mZ] #[7,9,0,0,0,0,5,0,8,0,0,0,3,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,1,0,0,2,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Do:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 7 xs.toFinset) Dn:=refBuckets_all (forall_cons Dl (forall_cons Dm (fun _ h => (List.not_mem_nil h).elim)))
def nf:List NodeSpec:=readDeltaNodes 6 (unruns (unpackWords 6 [(60,0x2a068b08008242a88b08000240810200631e88210508020638220099e2c200609091c2c20000905942c2000090)]) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dp:∀ ns ∈ nf, Impossible ac 8 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Do (by decide +kernel)
def Dq:BT (List (List Nat)):=refBuckets aT [nf] #[0,1,0,0,0,0,0,0,0,0,3,0,6,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0]
set_option maxRecDepth 20000 in
lemma Dr:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 8 xs.toFinset) Dq:=refBuckets_all (forall_cons Dp (fun _ h => (List.not_mem_nil h).elim))
def ng:List NodeSpec:=readDeltaNodes 5 (unruns (unpackWords 6 [(44,0x32e0b08008240802268b08010241448b08000241a58b0800024005102c2002090)]) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ds:∀ ns ∈ ng, Impossible ac 9 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Dr (by decide +kernel)
def Dt:BT (List (List Nat)):=refBuckets aT [ng] #[0,0,0,0,0,0,0,0,0,0,0,2,4,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Du:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 9 xs.toFinset) Dt:=refBuckets_all (forall_cons Ds (fun _ h => (List.not_mem_nil h).elim))
def nh:List NodeSpec:=readDeltaNodes 2 (unpackWords 4 [(28,0x306c111111021810271111110218)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dv:∀ ns ∈ nh, Impossible ac 10 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Du (by decide +kernel)
def Dw:BT (List (List Nat)):=refBuckets aT [nh] #[2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Dx:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 10 xs.toFinset) Dw:=refBuckets_all (forall_cons Dv (fun _ h => (List.not_mem_nil h).elim))
def ni:List NodeSpec:=readDeltaNodes 1 (unpackWords 4 [(20,0x21011121111111110368)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Dy:∀ ns ∈ ni, Impossible ac 11 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV Dx (by decide +kernel)
def Dz:BT (List (List Nat)):=refBuckets aT [ni] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma DA:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 11 xs.toFinset) Dz:=refBuckets_all (forall_cons Dy (fun _ h => (List.not_mem_nil h).elim))
def nj:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(20,0x68266a2092490ff)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DB:∀ ns ∈ nj, Impossible ac 12 (nodeValsBT aT ns).toFinset:=blockOk bW 6 (by decide) bT bU bX bV DA (by decide +kernel)
def DC:BT (List (List Nat)):=refBuckets aT [nj] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma DD:btAll (fun bk => ∀ xs ∈ bk, Impossible ac 12 xs.toFinset) DC:=refBuckets_all (forall_cons DB (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fk:Lower ao ac 13:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) DD (by decide +kernel)
def nl:List Nat:=varsOf 103
def nm:Nat:=0xfffffffffefefefefefefefea0a0a0a0fffffffffefefefefefefefea0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DE:Lower nl nm 8:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def nn:List Nat:=varsOf 109
def no:Nat:=0xfffffffffffafffafffafffaa0a0a0a0fffffffffffafffafffafffaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DF:Lower nn no 8:=carry_of (swaps:=[(4,5)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def np:List Nat:=varsOf 37
def nq:Nat:=0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DG:Lower np nq 4:=carry_of (swaps:=[(4,5)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def nt:List Nat:=varsOf 39
def nu:Nat:=0xfefefefeececececfefefefeececececfefefefeececececfefefefeecececec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DH:Lower nt nu 5:=carry_of (swaps:=[(5,6),(3,5),(1,3),(4,5),(1,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def fl:List Nat:=varsOf 45
def fm:Nat:=0xfffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0fffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nv:Lower fl fm 5:=carry_of (swaps:=[(5,6),(3,5),(4,5),(3,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def fn:List Nat:=varsOf 47
def fo:Nat:=0xfefafefaeca0eca0fefafefaeca0eca0fefafefaeca0eca0fefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nw:Lower fn fo 6:=carry_of (swaps:=[(4,5)]) (roots2:=cA) (T2:=cB) (by decide +kernel) cL
def nx:List Nat:=varsOf 101
def ny:Nat:=0xfafafafafafafafafafafafaa0a0a0a0fafafafafafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DI:Lower nx ny 5:=carry_of (swaps:=[(2,5),(1,5),(0,1),(2,7),(0,6),(4,6),(3,5)]) (roots2:=eT) (T2:=eU) (by decide +kernel) mL
def nz:List Nat:=varsOf 101
def nA:Nat:=0xfffffffffafafafafafafafaa0a0a0a0fffffffffafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DJ:Lower nz nA 7:=carry_of (swaps:=[(4,5)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def bp:List Nat:=varsOf 103
def aL:Nat:=0xfefefefefefefefefafafafaa0a0a0a0fefefefefefefefefafafafaa0a0a0a0
def fq:List Nat:=[5,66,7,33,36,5,36,33,66,65,65,7,35,98,68,68,98]
def fs:List Nat:=[4,64,6,32,32,1,4,1,2,1,64,3,3,96,4,64,34]
def nB:Nat:=fullMask 17
def nC:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7853,6816),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x13906,0x11904),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc875,0x4045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x130d8,0x12018),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x1e702,0xa402)]
def DK:List (Nat × Nat × Nat):=[]
def cT:BT Decor:=buildWiresBT 3 nC DK
def DL:List (List (Nat × Nat)):=[[],[(0,2)]]
def ft:BT (List (Nat × Nat)):=btOfList 1 DL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DM:goodPairs aL fq fs:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DN:∀ x ∈ nC, faithful fq fs x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DO:btAll (fun x => faithful fq fs x ∧ x.1 < 2^256) cT:=buildWiresBT_faithful DN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DP:btAll (fun sw => swapsValid sw = true ∧ permWord sw aL = aL) ft:=btAll_ofList (autos_of (by decide +kernel))
def DQ:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,7)]
def nD:BT (Option (Nat × Nat)):=btOfList 1 DQ
def DR:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def fu:BT (Option BoundPool):=buildPoolsBT 1 cT bp nD DR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DS:Slice bp aL (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 7:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=nz) (G:=nA) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) DJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DT:btAll (fun o => ∀ p, o = some p → Slice bp aL p.1 p.2) nD:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bp aL p.1 p.2) (forall_cons (someSlice DS) (fun _ h => (List.not_mem_nil h).elim))
lemma DU:btAll (fun o => ∀ c, o = some c → ValidPool bp aL c) fu:=buildPoolsBT_sound DT
def fv:BT (List (List Nat)):=BT.empty
lemma DV:btAll (fun bk => ∀ xs ∈ bk, Impossible aL (6 - 1) xs.toFinset) fv:=trivial
def nE:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(9,2396173)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma DW:checkNodesBT cT aL nB fu ft fv 6 nE = true:=by decide +kernel
def nF:List NodeSpec:=nE
set_option maxRecDepth 20000 in
lemma DX:checkNodesBT cT aL nB fu ft fv 6 nF = true:=DW
def DY:BT (List (List Nat)):=buildBucketsBT cT nF
set_option maxRecDepth 20000 in
lemma DZ:btAll (fun bk => ∀ xs ∈ bk, Impossible aL 6 xs.toFinset) DY:=buildBucketsBT_sound (by decide) DM DO DU DP DV DX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bY:Lower bp aL 7:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) DZ (by decide +kernel)
def fw:List Nat:=varsOf 75
def fx:Nat:=0xffeeffeeffeeffeeeeaaeeaaeeaaeeaaffeeffeeffeeffeeeeaaeeaaeeaaeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nG:Lower fw fx 5:=carry_of (swaps:=[(3,6),(1,3),(4,6),(1,7),(2,3),(0,1)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def nH:List Nat:=varsOf 106
def nI:Nat:=0xffccffccffccffccff00ff00cc00cc00ffccffccffccffccff00ff00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ea:Lower nH nI 5:=carry_of (swaps:=[(4,5),(3,5),(3,6),(2,6),(0,5),(1,5)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def nJ:List Nat:=varsOf 106
def nK:Nat:=0xffccffccffccffcccccccccccc00cc00ffccffccffccffcccccccccccc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Eb:Lower nJ nK 5:=carry_of (swaps:=[(4,5),(5,6),(2,6),(0,3),(1,5)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def bG:List Nat:=varsOf 99
def aX:Nat:=0xeeeeeeeeeeeeeeeeaaaaaaaa00000000eeeeeeeeeeeeeeeeaaaaaaaa00000000
def fy:List Nat:=[33,35,65,33,35,65,66,98]
def fz:List Nat:=[32,34,64,1,3,1,2,34]
def nL:Nat:=fullMask 8
def nM:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,210,210),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,155,131),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,228,4)]
def Ec:List (Nat × Nat × Nat):=[]
def cU:BT Decor:=buildWiresBT 2 nM Ec
def Ed:List (List (Nat × Nat)):=[[],[(1,5),(0,6)]]
def fA:BT (List (Nat × Nat)):=btOfList 1 Ed
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ee:goodPairs aX fy fz:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ef:∀ x ∈ nM, faithful fy fz x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Eg:btAll (fun x => faithful fy fz x ∧ x.1 < 2^256) cU:=buildWiresBT_faithful Ef
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Eh:btAll (fun sw => swapsValid sw = true ∧ permWord sw aX = aX) fA:=btAll_ofList (autos_of (by decide +kernel))
def Ei:List (Option (Nat × Nat)):=[]
def nN:BT (Option (Nat × Nat)):=btOfList 1 Ei
def Ej:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 0 []
def fB:BT (Option BoundPool):=buildPoolsBT 1 cU bG nN Ej
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ek:btAll (fun o => ∀ p, o = some p → Slice bG aX p.1 p.2) nN:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bG aX p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma El:btAll (fun o => ∀ c, o = some c → ValidPool bG aX c) fB:=buildPoolsBT_sound Ek
def fC:BT (List (List Nat)):=BT.empty
lemma Em:btAll (fun bk => ∀ xs ∈ bk, Impossible aX (3 - 1) xs.toFinset) fC:=trivial
def nO:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(7,299012)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma En:checkNodesBT cU aX nL fB fA fC 3 nO = true:=by decide +kernel
def nP:List NodeSpec:=nO
set_option maxRecDepth 20000 in
lemma Eo:checkNodesBT cU aX nL fB fA fC 3 nP = true:=En
def Ep:BT (List (List Nat)):=buildBucketsBT cU nP
set_option maxRecDepth 20000 in
lemma Eq:btAll (fun bk => ∀ xs ∈ bk, Impossible aX 3 xs.toFinset) Ep:=buildBucketsBT_sound (by decide) Ee Eg El Eh Em Eo
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cE:Lower bG aX 4:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,64,66),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) Eq (by decide +kernel)
def fD:List Nat:=varsOf 105
def fE:Nat:=0xffaaffaaffaaffaaaaaaaaaa00000000ffaaffaaffaaffaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma nQ:Lower fD fE 4:=carry_of (swaps:=[(2,3),(1,3)]) (roots2:=bG) (T2:=aX) (by decide +kernel) cE
def aN:List Nat:=varsOf 107
def az:Nat:=0xffeeffeeffeeffeeeeaaeeaacc00cc00ffeeffeeffeeffeeeeaaeeaacc00cc00
def fF:List Nat:=[10,33,11,35,10,11,41,65,33,66,65,66,72,35,41,72,98,42,65,66,42]
def fG:List Nat:=[8,32,9,34,2,3,40,64,1,2,1,64,64,3,9,8,34,40,3,0,34]
def cF:Nat:=fullMask 21
def nR:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x465ee,0x46524),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1b2a3d,0x152238),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x12d075,0x2c045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x13614a,0x13004a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xd9e80,6272)]
def Er:List (Nat × Nat × Nat):=[(1,1,2),(1,1,4),(3,1,4),(3,2,6)]
def bH:BT Decor:=buildWiresBT 4 nR Er
def Es:List (List (Nat × Nat)):=[[],[(1,3)]]
def cu:BT (List (Nat × Nat)):=btOfList 1 Es
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fH:goodPairs az fF fG:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Et:∀ x ∈ nR, faithful fF fG x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fI:btAll (fun x => faithful fF fG x ∧ x.1 < 2^256) bH:=buildWiresBT_faithful Et
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma fJ:btAll (fun sw => swapsValid sw = true ∧ permWord sw az = az) cu:=btAll_ofList (autos_of (by decide +kernel))
def Eu:List (Option (Nat × Nat)):=[some (subcubeFast 0 32,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,4),some (subcubeFast 8 0,4),some (subcubeFast 32 0,5),some (0x9999999999999999999999999999999999999999999999999999999999999999,5),some (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55,5)]
def nS:BT (Option (Nat × Nat)):=btOfList 3 Eu
def Ev:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 5 (unpackWords 3 [(10,50856193)])
def cv:BT (Option BoundPool):=buildPoolsBT 3 bH aN nS Ev
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ew:Slice aN az (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55) 5:=mappedSlice (f:=identifyRow 0 0 3 0) (R:=nH) (G:=nI) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ea
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ex:Slice aN az (0x9999999999999999999999999999999999999999999999999999999999999999) 5:=mappedSlice (f:=identifyRow 0 0 1 0) (R:=nJ) (G:=nK) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Eb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ey:Slice aN az (subcubeFast 32 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=dk) (qGoal:=dl) (by decide +kernel) eh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ez:Slice aN az (subcubeFast 8 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=bG) (qGoal:=aX) (by decide +kernel) cE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EA:Slice aN az (subcubeFast 2 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=fD) (qGoal:=fE) (by decide +kernel) nQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EB:Slice aN az (subcubeFast 1 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EC:Slice aN az (subcubeFast 0 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=fw) (qGoal:=fx) (by decide +kernel) nG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ED:btAll (fun o => ∀ p, o = some p → Slice aN az p.1 p.2) nS:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aN az p.1 p.2) (forall_cons (someSlice EC) (forall_cons (someSlice EB) (forall_cons (someSlice EA) (forall_cons (someSlice Ez) (forall_cons (someSlice Ey) (forall_cons (someSlice Ex) (forall_cons (someSlice Ew) (fun _ h => (List.not_mem_nil h).elim))))))))
lemma fK:btAll (fun o => ∀ c, o = some c → ValidPool aN az c) cv:=buildPoolsBT_sound ED
def fL:BT (List (List Nat)):=BT.empty
lemma EE:btAll (fun bk => ∀ xs ∈ bk, Impossible az (4 - 1) xs.toFinset) fL:=trivial
def nT:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(8,8720389)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EF:checkNodesBT bH az cF cv cu fL 4 nT = true:=by decide +kernel
def nU:List NodeSpec:=nT
set_option maxRecDepth 20000 in
lemma EG:checkNodesBT bH az cF cv cu fL 4 nU = true:=EF
def fM:BT (List (List Nat)):=buildBucketsBT bH nU
set_option maxRecDepth 20000 in
lemma EH:btAll (fun bk => ∀ xs ∈ bk, Impossible az 4 xs.toFinset) fM:=buildBucketsBT_sound (by decide) fH fI fK fJ EE EG
def nV:List NodeSpec:=readDeltaNodes 3 (unpackWords 3 [(32,0x2592480b088924139924900e)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EI:checkNodesBT bH az cF cv cu fM 5 nV = true:=by decide +kernel
def nW:List NodeSpec:=nV
set_option maxRecDepth 20000 in
lemma EJ:checkNodesBT bH az cF cv cu fM 5 nW = true:=EI
def fN:BT (List (List Nat)):=buildBucketsBT bH nW
set_option maxRecDepth 20000 in
lemma EK:btAll (fun bk => ∀ xs ∈ bk, Impossible az 5 xs.toFinset) fN:=buildBucketsBT_sound (by decide) fH fI fK fJ EH EJ
def nX:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(14,560629846181)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EL:checkNodesBT bH az cF cv cu fN 6 nX = true:=by decide +kernel
def nY:List NodeSpec:=nX
set_option maxRecDepth 20000 in
lemma EM:checkNodesBT bH az cF cv cu fN 6 nY = true:=EL
def EN:BT (List (List Nat)):=buildBucketsBT bH nY
set_option maxRecDepth 20000 in
lemma EO:btAll (fun bk => ∀ xs ∈ bk, Impossible az 6 xs.toFinset) EN:=buildBucketsBT_sound (by decide) fH fI fK fJ EK EM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cj:Lower aN az 7:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,8,10),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) EO (by decide +kernel)
def nZ:List Nat:=varsOf 101
def oa:Nat:=0xfffffffffffffffffafafafaa0a0a0a0fffffffffffffffffafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EP:Lower nZ oa 5:=carry_of (swaps:=[(4,5),(6,7)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def fO:List Nat:=varsOf 109
def fP:Nat:=0xfffafffafffafffafafafafaa0a0a0a0fffafffafffafffafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ob:Lower fO fP 7:=carry_of (swaps:=[(1,3)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def oc:List Nat:=varsOf 78
def od:Nat:=0xfffcfffcfffcfffcfcf0fcf0fcf0fcf0fffcfffcfffcfffcfcf0fcf0fcf0fcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EQ:Lower oc od 5:=carry_of (swaps:=[(3,6),(4,6),(3,7),(2,3),(0,1)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def fQ:List Nat:=varsOf 110
def fR:Nat:=0xfffcfffcfffcfffcfcf0fcf0cc00cc00fffcfffcfffcfffcfcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oe:Lower fQ fR 7:=carry_of (swaps:=[(0,2)]) (roots2:=aN) (T2:=az) (by decide +kernel) cj
def of:List Nat:=varsOf 79
def og:Nat:=0xfffefffefffefffefefafefafefafefafffefffefffefffefefafefafefafefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ER:Lower of og 6:=carry_of (swaps:=[(1,4),(1,6),(1,3),(2,3),(0,1)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def oh:List Nat:=varsOf 103
def oi:Nat:=0xfffffffffffffffffefefefeececececfffffffffffffffffefefefeecececec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ES:Lower oh oi 6:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def oj:List Nat:=varsOf 109
def ol:Nat:=0xfffffffffffffffffffafffaffa0ffa0fffffffffffffffffffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ET:Lower oj ol 6:=carry_of (swaps:=[(4,5)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def aA:List Nat:=varsOf 111
def af:Nat:=0xfffefffefffefffefefafefaeca0eca0fffefffefffefffefefafefaeca0eca0
def fS:List Nat:=[5,10,7,11,5,35,36,5,10,11,36,33,66,65,7,72,35,13,14,68,68,14,13,44,41,42,72,98,66,42,67,65,97,36,33,5,73,65,70,66,100,5,65,76,38,104,98]
def fT:List Nat:=[4,8,6,9,6,34,32,1,2,3,4,1,2,1,3,64,3,9,6,4,64,12,12,40,9,34,8,34,64,40,3,64,96,96,96,64,9,3,6,0,96,0,0,12,34,40,96]
def PD:Nat:=fullMask 47
def om:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x63dc1436abd,0x3041036a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x50c07a25532e,0x10604a055334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1b4a00fe44d5,0x840006c0415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x281027e6830a,0x281025e2000a),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x71072b810c60,0x71072a800060),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x6df1dc18b000,0x410f90108000)]
def EU:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,0,5),(3,0,5),(1,1,3),(1,1,5),(3,1,5),(1,2,5),(3,2,5),(3,2,6),(1,4,5),(3,4,7),(1,7,8),(3,2,8),(1,5,17),(3,3,11),(1,0,12),(1,2,22),(3,2,22),(1,12,17),(3,0,18),(1,2,26)]
def bA:BT Decor:=buildWiresBT 5 om EU
def EV:List (List (Nat × Nat)):=[[],[(1,3)],[(0,2)],[(1,3),(0,2)]]
def EW:BT (List (Nat × Nat)):=btOfList 2 EV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck:goodPairs af fS fT:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma EX:∀ x ∈ om, faithful fS fT x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cl:btAll (fun x => faithful fS fT x ∧ x.1 < 2^256) bA:=buildWiresBT_faithful EX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cm:btAll (fun sw => swapsValid sw = true ∧ permWord sw af = af) EW:=btAll_ofList (autos_of (by decide +kernel))
def EY:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,6),some (subcubeFast 0 8,6),some (subcubeFast 0 32,6),some (subcubeFast 1 0,7),some (subcubeFast 1 32,5),some (subcubeFast 2 0,7),some (subcubeFast 2 8,5),some (subcubeFast 4 0,7),some (subcubeFast 4 32,5),some (subcubeFast 5 32,4),some (subcubeFast 8 0,7),some (subcubeFast 10 0,5),some (subcubeFast 32 0,8),some (subcubeFast 37 0,4),some (subcubeFast 64 0,6),some (subcubeFast 64 2,5),some (subcubeFast 64 8,5),some (subcubeFast 66 8,4),some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,8),some (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff,8),some (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff,8)]
def EZ:BT (Option (Nat × Nat)):=btOfList 5 EY
def cn:Nat → Option PoolSpec:=lookSpec 66 #[(1,0,1),(3,2,6),(1,0,2),(1,0,5),(1,2,5),(1,1,3),(3,4,7),(1,1,5),(3,3,11),(3,1,5),(3,2,8),(1,4,5),(3,0,5),(1,0,12)] #[0xc1800006030000182800010040000a060000407000000485080c30005080200284000010186000010000000618000000e0000001000000300000002000000a000808600040428000040600000070000083800004280000000000000f000008600000018000000a0000003,0x100e0000607000000a0000343000018140000c0500302050018101400b0818002840c00002010000140800008140000405000020600000040000001a000070700003818000283000014060000011001c1850000203000910180048803000040180000c2800000160038305,0xe14180070a0a000070300002828000140e0048807]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fa:Slice aA af (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff) 8:=mappedSlice (f:=identifyRow 0 0 6 5) (R:=aJ) (G:=ap) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) bK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fb:Slice aA af (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff) 8:=mappedSlice (f:=identifyRow 0 0 5 3) (R:=nl) (G:=nm) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) DE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fc:Slice aA af (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 8:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=nn) (G:=no) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) DF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fd:Slice aA af (subcubeFast 66 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=np) (qGoal:=nq) (by decide +kernel) DG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fe:Slice aA af (subcubeFast 64 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=nt) (qGoal:=nu) (by decide +kernel) DH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ff:Slice aA af (subcubeFast 64 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=fl) (qGoal:=fm) (by decide +kernel) nv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fg:Slice aA af (subcubeFast 64 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=fn) (qGoal:=fo) (by decide +kernel) nw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fh:Slice aA af (subcubeFast 37 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fi:Slice aA af (subcubeFast 32 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aJ) (qGoal:=ap) (by decide +kernel) bK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fj:Slice aA af (subcubeFast 10 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=nx) (qGoal:=ny) (by decide +kernel) DI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fk:Slice aA af (subcubeFast 8 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=bp) (qGoal:=aL) (by decide +kernel) bY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fl:Slice aA af (subcubeFast 5 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fm:Slice aA af (subcubeFast 4 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=fw) (qGoal:=fx) (by decide +kernel) nG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fn:Slice aA af (subcubeFast 4 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aN) (qGoal:=az) (by decide +kernel) cj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fo:Slice aA af (subcubeFast 2 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=nZ) (qGoal:=oa) (by decide +kernel) EP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fp:Slice aA af (subcubeFast 2 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fO) (qGoal:=fP) (by decide +kernel) ob
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fq:Slice aA af (subcubeFast 1 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=oc) (qGoal:=od) (by decide +kernel) EQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fr:Slice aA af (subcubeFast 1 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fQ) (qGoal:=fR) (by decide +kernel) oe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fs:Slice aA af (subcubeFast 0 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=of) (qGoal:=og) (by decide +kernel) ER
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ft:Slice aA af (subcubeFast 0 8) 6:=slice_fast_direct (zDead:=0) (qRoots:=oh) (qGoal:=oi) (by decide +kernel) ES
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fu:Slice aA af (subcubeFast 0 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=oj) (qGoal:=ol) (by decide +kernel) ET
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma co:btAll (fun o => ∀ p, o = some p → Slice aA af p.1 p.2) EZ:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aA af p.1 p.2) (forall_cons (someSlice Fu) (forall_cons (someSlice Ft) (forall_cons (someSlice Fs) (forall_cons (someSlice Fr) (forall_cons (someSlice Fq) (forall_cons (someSlice Fp) (forall_cons (someSlice Fo) (forall_cons (someSlice Fn) (forall_cons (someSlice Fm) (forall_cons (someSlice Fl) (forall_cons (someSlice Fk) (forall_cons (someSlice Fj) (forall_cons (someSlice Fi) (forall_cons (someSlice Fh) (forall_cons (someSlice Fg) (forall_cons (someSlice Ff) (forall_cons (someSlice Fe) (forall_cons (someSlice Fd) (forall_cons (someSlice Fc) (forall_cons (someSlice Fb) (forall_cons (someSlice Fa) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
def Fv:BT (List (List Nat)):=BT.empty
lemma Fw:btAll (fun bk => ∀ xs ∈ bk, Impossible af (5 - 1) xs.toFinset) Fv:=trivial
def oo:List NodeSpec:=readDeltaNodes 2 (unpackWords 5 [(18,0x28208420000c460c2100006)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fx:∀ ns ∈ oo, Impossible af 5 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm Fw (by decide +kernel)
def Fy:BT (List (List Nat)):=refBuckets bA [oo] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0]
set_option maxRecDepth 20000 in
lemma oq:btAll (fun bk => ∀ xs ∈ bk, Impossible af 5 xs.toFinset) Fy:=refBuckets_all (forall_cons Fx (fun _ h => (List.not_mem_nil h).elim))
def os:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe6a24804f37ae5128827938c86944a219e8986434b28830e),(64,0xa7a24824f51f4492413c2b4e3912412782a679144828f3f1),(4,249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Fz:∀ ns ∈ os, Impossible af 6 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm oq (by decide +kernel)
def ot:List NodeSpec:=readDeltaNodes 6 (unruns (unpackWords 6 [(50,0x98908500eba418908008e81a2881c20023a8b9068908010e79e10508000230272424200010e)]) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FA:∀ ns ∈ ot, Impossible af 6 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm oq (by decide +kernel)
def FB:BT (List (List Nat)):=refBuckets bA [os,ot] #[0,1,0,13,0,0,6,0,0,0,0,0,4,0,0,0,0,0,0,57349,0,10,0,0,3,0,0,0,0,0,12,0,0,2,0,0,0,0,0,0,0,0,0,11,0,8,0,0,0,0,0,0,0,0,0,0,0,9,0,0,0,0,7,0]
set_option maxRecDepth 20000 in
lemma fU:btAll (fun bk => ∀ xs ∈ bk, Impossible af 6 xs.toFinset) FB:=refBuckets_all (forall_cons Fz (forall_cons FA (fun _ h => (List.not_mem_nil h).elim)))
def ou:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x81126e35a249209aa066146428924934f449a62c4924034f),(64,0x7df71124234e40990e70d35124908d50264ee6988924826a),(61,0x204c339361869849211c7a06c589e61749248471e4130f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FC:∀ ns ∈ ou, Impossible af 7 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm fU (by decide +kernel)
def ov:List NodeSpec:=readDeltaNodes 8 (unpackWords 5 [(64,0x10902e2827205c108421004c7102d750c210842010915990c4084210006710367814610842100868),(52,0xacc9608421080033d66440c410840019c28acc8828421000a6100f058c2108420)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FD:∀ ns ∈ ov, Impossible af 7 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm fU (by decide +kernel)
def ow:List NodeSpec:=readDeltaNodes 3 (unpackWords 5 [(44,0x438ba065884210840139c190d524804410802534c873042100046)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FE:∀ ns ∈ ow, Impossible af 7 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm fU (by decide +kernel)
def FF:BT (List (List Nat)):=refBuckets bA [ou,ov,ow] #[10,0,18,0,0,5,9,0,65551,0,0,0,2,12,0,0,0,0,0,0,6,0,0,0,17,0,0,0,0,0,4,0,0,0,0,11,3,0,8,0,14,0,0,1,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,77837,0,0]
set_option maxRecDepth 20000 in
lemma FG:btAll (fun bk => ∀ xs ∈ bk, Impossible af 7 xs.toFinset) FF:=refBuckets_all (forall_cons FC (forall_cons FD (forall_cons FE (fun _ h => (List.not_mem_nil h).elim))))
def ox:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8606492413cf241a61c5a86844924350f0512482492413cf),(64,0x271e0ee89d19349248271e8171586180c249211c78249b0d),(64,0x31744908e390261949bde24f24921287836a66d50c389248),(12,17360672086)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FH:∀ ns ∈ ox, Impossible af 8 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm FG (by decide +kernel)
def FI:BT (List (List Nat)):=refBuckets bA [ox] #[0,0,0,0,0,0,0,0,0,0,0,3,0,6,0,0,0,0,0,5,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,7,0,0,0,0,0,0,4,0,1,0,0]
set_option maxRecDepth 20000 in
lemma FJ:btAll (fun bk => ∀ xs ∈ bk, Impossible af 8 xs.toFinset) FI:=refBuckets_all (forall_cons FH (fun _ h => (List.not_mem_nil h).elim))
def oy:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(18,0x9214e4124912e)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FK:∀ ns ∈ oy, Impossible af 9 (nodeValsBT bA ns).toFinset:=blockOk cn 7 (by decide) ck cl co cm FJ (by decide +kernel)
def FL:BT (List (List Nat)):=refBuckets bA [oy] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma FM:btAll (fun bk => ∀ xs ∈ bk, Impossible af 9 xs.toFinset) FL:=refBuckets_all (forall_cons FK (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cp:Lower aA af 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) FM (by decide +kernel)
def cG:List Nat:=varsOf 239
def cH:Nat:=0xfffffffffffffffffffffffffffffffffffefffefffefffefefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cV:Lower cG cH 11:=lift_of (z:=128) (o:=0) (essPairs:=[(VAR 7,0,128)]) (by decide +kernel) cp
def oz:List Nat:=varsOf 239
def oA:Nat:=0xfffffffffffffffffffefffefffefffefffffffffffffffffefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FN:Lower oz oA 11:=carry_of (swaps:=[(6,7)]) (roots2:=cG) (T2:=cH) (by decide +kernel) cV
def fV:List Nat:=varsOf 239
def fW:Nat:=0xfffffffffffffffffffffffffffefffefffffffffffefffeffffffffeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oB:Lower fV fW 11:=lift_of (z:=32) (o:=0) (essPairs:=[(VAR 5,0,32)]) (by decide +kernel) cD
def oC:List Nat:=varsOf 181
def oD:Nat:=0xfffffffffffffafafffffffffffffafafffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FO:Lower oC oD 10:=carry_of (swaps:=[(5,6)]) (roots2:=aD) (T2:=Z) (by decide +kernel) bF
def fX:List Nat:=varsOf 229
def fY:Nat:=0xfffffffffffffffffffffffffafafafafffffffffafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oE:Lower fX fY 10:=carry_of (swaps:=[(4,5)]) (roots2:=aD) (T2:=Z) (by decide +kernel) bF
def oF:List Nat:=varsOf 241
def oG:Nat:=0xffffffffffffffffffffffffffffaaaaffffffffffffaaaaffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FP:Lower oF oG 10:=carry_of (swaps:=[(3,5),(4,5),(2,4)]) (roots2:=aD) (T2:=Z) (by decide +kernel) bF
def oH:List Nat:=varsOf 244
def oI:Nat:=0xfffffffffffffffffffffffffffff0f0fffffffffffff0f0fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FQ:Lower oH oI 10:=carry_of (swaps:=[(3,5),(1,5),(4,5),(2,4),(0,2)]) (roots2:=aD) (T2:=Z) (by decide +kernel) bF
def bL:List Nat:=varsOf 245
def bf:Nat:=0xfffffffffffffffffffffffffffffafafffffffffffffafafffffafafafaa0a0
def fZ:List Nat:=[17,20,5,5,20,17,36,33,33,68,65,65,132,129,129,36,68,132,48,48,80,80,144,144,96,96,160,160,192,192]
def ga:List Nat:=[16,16,1,4,4,1,4,1,32,4,1,64,4,1,128,32,64,128,16,32,16,64,16,128,32,64,32,128,64,128]
def oJ:Nat:=fullMask 30
def oK:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6dad,9380),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3925e,4696),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xfc0033,0x540003),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xf0c81c0,0x5088100),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x33310e00,0x12210800),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3cc27000,0x28824000)]
def FR:List (Nat × Nat × Nat):=[]
def cW:BT Decor:=buildWiresBT 3 oK FR
def FT:List (List (Nat × Nat)):=[[],[(6,7)],[(5,6)],[(5,7)],[(4,5)],[(4,6)],[(4,7)],[(2,4)],[(2,5)],[(2,6)],[(2,7)],[(0,2)],[(0,4)],[(0,5)],[(0,6)],[(0,7)],[(6,7),(5,6)],[(6,7),(5,7)],[(6,7),(4,5)],[(5,6),(4,5)],[(5,7),(4,5)],[(5,6),(4,6)],[(6,7),(4,6)],[(5,7),(4,6)],[(5,7),(4,7)],[(6,7),(4,7)],[(5,6),(4,7)],[(6,7),(2,4)],[(5,6),(2,4)],[(5,7),(2,4)],[(4,5),(2,4)],[(4,6),(2,4)],[(4,7),(2,4)]]
def gb:BT (List (Nat × Nat)):=btOfList 6 FT
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FU:goodPairs bf fZ ga:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FV:∀ x ∈ oK, faithful fZ ga x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FW:btAll (fun x => faithful fZ ga x ∧ x.1 < 2^256) cW:=buildWiresBT_faithful FV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma FX:btAll (fun sw => swapsValid sw = true ∧ permWord sw bf = bf) gb:=btAll_ofList (autos_of (by decide +kernel))
def FY:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,10),some (subcubeFast 4 0,10),some (subcubeFast 16 0,10),some (subcubeFast 32 0,10),some (subcubeFast 64 0,10)]
def oL:BT (Option (Nat × Nat)):=btOfList 3 FY
def FZ:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 5 (unpackWords 3 [(10,67903552)])
def gd:BT (Option BoundPool):=buildPoolsBT 3 cW bL oL FZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ga:Slice bL bf (subcubeFast 64 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=oC) (qGoal:=oD) (by decide +kernel) FO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gb:Slice bL bf (subcubeFast 32 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aD) (qGoal:=Z) (by decide +kernel) bF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gc:Slice bL bf (subcubeFast 16 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fX) (qGoal:=fY) (by decide +kernel) oE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gd:Slice bL bf (subcubeFast 4 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=oF) (qGoal:=oG) (by decide +kernel) FP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ge:Slice bL bf (subcubeFast 1 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=oH) (qGoal:=oI) (by decide +kernel) FQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gf:btAll (fun o => ∀ p, o = some p → Slice bL bf p.1 p.2) oL:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bL bf p.1 p.2) (forall_cons (someSlice Ge) (forall_cons (someSlice Gd) (forall_cons (someSlice Gc) (forall_cons (someSlice Gb) (forall_cons (someSlice Ga) (fun _ h => (List.not_mem_nil h).elim))))))
lemma Gg:btAll (fun o => ∀ c, o = some c → ValidPool bL bf c) gd:=buildPoolsBT_sound Gf
def ge:BT (List (List Nat)):=BT.empty
lemma Gh:btAll (fun bk => ∀ xs ∈ bk, Impossible bf (11 - 1) xs.toFinset) ge:=trivial
def oM:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(14,628158140462)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gi:checkNodesBT cW bf oJ gd gb ge 11 oM = true:=by decide +kernel
def oN:List NodeSpec:=oM
set_option maxRecDepth 20000 in
lemma Gj:checkNodesBT cW bf oJ gd gb ge 11 oN = true:=Gi
def Gk:BT (List (List Nat)):=buildBucketsBT cW oN
set_option maxRecDepth 20000 in
lemma Gl:btAll (fun bk => ∀ xs ∈ bk, Impossible bf 11 xs.toFinset) Gk:=buildBucketsBT_sound (by decide) FU FW Gg FX Gh Gj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gm:Lower bL bf 12:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Gl (by decide +kernel)
def gf:List Nat:=varsOf 247
def gg:Nat:=0xfffffffffffffffffffffffffffffefefffffffffffffefefffffefefafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma oO:Lower gf gg 13:=lift_of (z:=2) (o:=0) (essPairs:=[(VAR 1,32,34)]) (by decide +kernel) Gm
def oP:List Nat:=varsOf 251
def oQ:Nat:=0xffffffffffffffffffffffffffffffffffffffeeffffffeeffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gn:Lower oP oQ 11:=carry_of (swaps:=[(2,4)]) (roots2:=cG) (T2:=cH) (by decide +kernel) cV
def oR:List Nat:=varsOf 251
def oS:Nat:=0xffffffffffffffffffffffeeffffffeeffffffffffffffffffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Go:Lower oR oS 11:=carry_of (swaps:=[(2,4),(6,7)]) (roots2:=cG) (T2:=cH) (by decide +kernel) cV
def oT:List Nat:=varsOf 234
def oU:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffccff00ff00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gp:Lower oT oU 8:=carry_of (swaps:=[(3,5),(3,6),(4,7),(2,6),(0,5),(1,5)]) (roots2:=cM) (T2:=cN) (by decide +kernel) dx
def oV:List Nat:=varsOf 234
def oW:Nat:=0xffffffffffffffffffccffccffccffccffccffccffccffcccccccccccc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gq:Lower oV oW 8:=carry_of (swaps:=[(5,6),(4,7),(2,6),(0,3),(1,5)]) (roots2:=cM) (T2:=cN) (by decide +kernel) dx
def oX:List Nat:=varsOf 163
def oY:Nat:=0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gr:Lower oX oY 4:=carry_of (swaps:=[(6,7)]) (roots2:=bG) (T2:=aX) (by decide +kernel) cE
def oZ:List Nat:=varsOf 169
def pc:Nat:=0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaa00000000aaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gs:Lower oZ pc 4:=carry_of (swaps:=[(2,3),(6,7),(1,3)]) (roots2:=bG) (T2:=aX) (by decide +kernel) cE
def gh:List Nat:=varsOf 171
def gi:Nat:=0xffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaacc00cc00eeaaeeaacc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pd:Lower gh gi 7:=carry_of (swaps:=[(6,7)]) (roots2:=aN) (T2:=az) (by decide +kernel) cj
def pe:List Nat:=varsOf 225
def pf:Nat:=0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gt:Lower pe pf 5:=carry_of (swaps:=[(4,7),(3,5),(2,7),(0,6),(1,5)]) (roots2:=ba) (T2:=bc) (by decide +kernel) bh
def pg:List Nat:=varsOf 227
def ph:Nat:=0xffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gu:Lower pg ph 7:=carry_of (swaps:=[(4,7),(3,7),(2,7),(0,6),(1,5)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def gj:List Nat:=varsOf 200
def gk:Nat:=0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff000000000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pi:Lower gj gk 4:=carry_of (swaps:=[(6,7),(5,6),(1,3),(4,7),(2,6),(0,3)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def pj:List Nat:=varsOf 233
def pk:Nat:=0xffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaa00000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gv:Lower pj pk 7:=carry_of (swaps:=[(4,7),(2,7),(0,6),(3,5),(1,5)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def bZ:List Nat:=varsOf 203
def ca:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaaeeaaeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cq:Lower bZ ca 8:=lift_of (z:=1) (o:=0) (essPairs:=[(VAR 0,0,1)]) (by decide +kernel) cC
def aH:List Nat:=varsOf 235
def ag:Nat:=0xffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaacc00cc00
def gl:List Nat:=[10,33,11,35,10,11,41,65,33,66,65,130,129,129,66,72,35,42,41,42,72,136,98,162,192,192,130,136,224,67,98,65,65,168,224,73,131,162,129,104,104,129,168,138,66,130,97,137,74]
def gm:List Nat:=[8,32,9,34,2,3,40,64,1,2,1,2,1,128,64,64,3,40,9,34,8,8,34,34,64,128,128,128,160,3,96,9,3,40,96,9,3,160,3,96,40,9,160,2,0,0,96,9,64]
def PE:Nat:=fullMask 49
def pl:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc259a00535ee,0x8259a0051524),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1383064cb4a3d,0x85120c90a38),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x18d8a083e8075,0x830a80360045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x45a650cf014a,0x45a650ca004a),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x1518df350c680,0x140844100c080),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xae761fa03800,0x4201e002000)]
def Gw:List (Nat × Nat × Nat):=[(1,1,2),(1,0,6),(1,1,4),(1,1,5),(1,2,4),(1,2,5),(1,4,5),(1,4,7),(3,0,13),(3,2,13),(3,4,13),(3,5,13),(1,0,8),(3,0,8),(1,2,8),(3,2,8),(1,5,8),(3,5,8),(1,5,10),(1,5,6),(1,8,25),(1,0,22),(3,0,22),(3,6,22),(1,0,23),(1,0,12),(3,0,12),(3,2,12),(0,2,22),(3,2,22),(1,2,23),(3,1,12),(3,5,20),(3,1,26),(1,2,39),(1,2,14),(1,0,15),(3,1,27),(3,2,27),(3,5,27),(1,5,19),(1,5,21),(1,0,37),(3,0,37),(1,1,28),(3,2,50)]
def aM:BT Decor:=buildWiresBT 6 pl Gw
def Gx:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(6,7),(1,3)]]
def Gy:BT (List (Nat × Nat)):=btOfList 2 Gx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bq:goodPairs ag gl gm:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Gz:∀ x ∈ pl, faithful gl gm x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bt:btAll (fun x => faithful gl gm x ∧ x.1 < 2^256) aM:=buildWiresBT_faithful Gz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bu:btAll (fun sw => swapsValid sw = true ∧ permWord sw ag = ag) Gy:=btAll_ofList (autos_of (by decide +kernel))
def GA:List (Option (Nat × Nat)):=[some (subcubeFast 0 32,8),some (subcubeFast 1 32,7),some (subcubeFast 2 0,7),some (subcubeFast 3 32,4),some (subcubeFast 8 0,7),some (subcubeFast 10 0,5),some (subcubeFast 32 0,8),some (subcubeFast 64 0,7),some (subcubeFast 65 32,4),some (subcubeFast 66 0,4),some (subcubeFast 72 0,4),some (subcubeFast 128 0,7),some (subcubeFast 130 0,4),some (subcubeFast 136 0,4),some (0x9999999999999999999999999999999999999999999999999999999999999999,8),some (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55,8)]
def GB:BT (Option (Nat × Nat)):=btOfList 4 GA
def bw:Nat → Option PoolSpec:=lookSpec 71 #[(1,1,2),(1,1,4),(1,2,4),(1,4,5),(1,5,8),(3,6,22),(1,2,8),(3,5,20),(1,1,5),(3,2,8),(3,2,12),(3,0,22),(3,1,12),(3,2,22),(3,5,8),(3,2,50),(3,0,37)] #[0xe0e000000a001c100000e081800002160030502000020100000024000020e000030200001020304040418202000c10106000808080040400002020c000000400000058000001c000000a00001000000083000004040000004000000000000030000003c000001c0000001,0xf040238282001c141030000141c00d080800005021814103000a0800005040c0028201002c20100041004004040c0020201002810300140804000001a0018206000c100800000302090400104820600281058000082c000120e004820000241030000081800004022038200,0x342c0001a0e00684000034203001c141c0000808446840620141008000101800008020078206]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GC:Slice aH ag (0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55) 8:=mappedSlice (f:=identifyRow 0 0 3 0) (R:=oT) (G:=oU) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Gp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GD:Slice aH ag (0x9999999999999999999999999999999999999999999999999999999999999999) 8:=mappedSlice (f:=identifyRow 0 0 1 0) (R:=oV) (G:=oW) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Gq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GE:Slice aH ag (subcubeFast 136 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=bG) (qGoal:=aX) (by decide +kernel) cE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GF:Slice aH ag (subcubeFast 130 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=fD) (qGoal:=fE) (by decide +kernel) nQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GG:Slice aH ag (subcubeFast 128 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aN) (qGoal:=az) (by decide +kernel) cj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GH:Slice aH ag (subcubeFast 72 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=oX) (qGoal:=oY) (by decide +kernel) Gr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GI:Slice aH ag (subcubeFast 66 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=oZ) (qGoal:=pc) (by decide +kernel) Gs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GJ:Slice aH ag (subcubeFast 65 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=dz) (qGoal:=dA) (by decide +kernel) eE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GK:Slice aH ag (subcubeFast 64 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=gh) (qGoal:=gi) (by decide +kernel) pd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GM:Slice aH ag (subcubeFast 32 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cQ) (qGoal:=cR) (by decide +kernel) dD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GN:Slice aH ag (subcubeFast 10 0) 5:=slice_fast_direct (zDead:=0) (qRoots:=pe) (qGoal:=pf) (by decide +kernel) Gt
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GO:Slice aH ag (subcubeFast 8 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=pg) (qGoal:=ph) (by decide +kernel) Gu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GP:Slice aH ag (subcubeFast 3 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=gj) (qGoal:=gk) (by decide +kernel) pi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GQ:Slice aH ag (subcubeFast 2 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=pj) (qGoal:=pk) (by decide +kernel) Gv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GR:Slice aH ag (subcubeFast 1 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=cO) (qGoal:=cP) (by decide +kernel) cC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GS:Slice aH ag (subcubeFast 0 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=bZ) (qGoal:=ca) (by decide +kernel) cq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bx:btAll (fun o => ∀ p, o = some p → Slice aH ag p.1 p.2) GB:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aH ag p.1 p.2) (forall_cons (someSlice GS) (forall_cons (someSlice GR) (forall_cons (someSlice GQ) (forall_cons (someSlice GP) (forall_cons (someSlice GO) (forall_cons (someSlice GN) (forall_cons (someSlice GM) (forall_cons (someSlice GK) (forall_cons (someSlice GJ) (forall_cons (someSlice GI) (forall_cons (someSlice GH) (forall_cons (someSlice GG) (forall_cons (someSlice GF) (forall_cons (someSlice GE) (forall_cons (someSlice GD) (forall_cons (someSlice GC) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))
def GT:BT (List (List Nat)):=BT.empty
lemma gn:btAll (fun bk => ∀ xs ∈ bk, Impossible ag (5 - 1) xs.toFinset) GT:=trivial
def pn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x273a614c00738e1853009cfa69800e332293009ce924800e),(37,0x2989280072ce986940138dc5a6c0)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GU:∀ ns ∈ pn, Impossible ag 5 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gn (by decide +kernel)
def po:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x72e7338a009cab38a001cf934a001c4935800e57928800e),(34,0x19f4960038e84d280071ece280)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GV:∀ ns ∈ po, Impossible ag 5 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gn (by decide +kernel)
def pp:List NodeSpec:=readDeltaNodes 1 (unpackWords 6 [(10,0xfee041081000046)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GW:∀ ns ∈ pp, Impossible ag 5 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gn (by decide +kernel)
def GX:BT (List (List Nat)):=refBuckets aM [pn,po,pp] #[0,0,0,0,8,0,6,0,14,0,9,0,0,0,0,0,0,10,0,0,7,0,0,0,13,2,0,0,0,0,11,0,12,0,1,0,0,0,15,0,0,17,0,0,0,0,0,0,5,0,0,0,16,0,3,0,0,4,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma cw:btAll (fun bk => ∀ xs ∈ bk, Impossible ag 5 xs.toFinset) GX:=refBuckets_all (forall_cons GU (forall_cons GV (forall_cons GW (fun _ h => (List.not_mem_nil h).elim))))
def pq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x409c5548a6118707ca24a049e5ae492404783cb5092482cf),(64,0x21c32124a089e1632b24a049e8188a28207920dcd125864f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GY:∀ ns ∈ pq, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def pr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x859d092480cf40da4924207a2ba87a24844f0e194925024f),(61,0x251b892482cf58924800f3f294924804f2d52492023cd)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma GZ:∀ ns ∈ pr, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def pt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20f0baa6125024f2d6a4924047a561249009e5ad0924808f),(61,0x105b8e2ec9a50469c15ae18494093c12d14083c2c61250)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ha:∀ ns ∈ pt, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def pu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe5ab4924808f60dc59a49089e1d35124107a0e386a24844f),(63,0x173cf449049e1c871e892093d2d8924820f0ad54f449049)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hb:∀ ns ∈ pu, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def pw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x521249011ee530de49240478729d5a24824f58ea6345004f),(64,0x3f1249001e5ea7e251011c83865251081e0c7cca494093cb)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hc:∀ ns ∈ pw, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def px:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x1e59d4924808f3bb251001e61f5925004f71d32928804f),(54,0x3997a4924127ab8924800f4e194924824f3f9249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hd:∀ ns ∈ px, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def py:List NodeSpec:=readDeltaNodes 4 (varNats 3 (unpackWords 4 [(55,0x4b111110107135b111110027181792f7112100377c45c111110027)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma He:∀ ns ∈ py, Impossible ag 6 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu cw (by decide +kernel)
def Hf:BT (List (List Nat)):=refBuckets aM [pq,pr,pt,pu,pw,px,py] #[0,33,6,0,47,0,0,2,18,0,1,51,0,587292675,188458,0,0,0,15,0,196625,32,24,0,0,0,0,176132,5,16,21,0,28,0,0,0,9,126986,155674,0,0,184359,7,0,37,486596616,20,25,0,0,0,34,19,36,872509451,0,0,41,122893,200748,204827,0,163852,0]
set_option maxRecDepth 20000 in
lemma gq:btAll (fun bk => ∀ xs ∈ bk, Impossible ag 6 xs.toFinset) Hf:=refBuckets_all (forall_cons GY (forall_cons GZ (forall_cons Ha (forall_cons Hb (forall_cons Hc (forall_cons Hd (forall_cons He (fun _ h => (List.not_mem_nil h).elim))))))))
def pz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe49096449e7124920c39404f262a89250269e41c8924844f),(64,0x8f3c1fde2492093c1fdd2492093d10493174a17c92486a1),(45,0x205d3915564d12423cf20c24ae6534b24a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hg:∀ ns ∈ pz, Impossible ag 7 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gq (by decide +kernel)
def pA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3df75532124904d3ce75571924901a84906d373649241894),(64,0x2482d42118b18f2ce1949248479e8159d2e2c6344908e3c1),(54,0x107e9d8924844f055ab386624920987833333bcc9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hh:∀ ns ∈ pA, Impossible ag 7 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gq (by decide +kernel)
def pB:List NodeSpec:=readDeltaNodes 4 (varNats 2 (unpackWords 3 [(64,0xb8a909248671e1548ae66372c7924904f5107e9dc924844f),(36,0x2095e38b9d4f249211aa14092e3)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hi:∀ ns ∈ pB, Impossible ag 7 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu gq (by decide +kernel)
def Hj:BT (List (List Nat)):=refBuckets aM [pz,pA,pB] #[14,0,0,0,0,15,0,0,20,3,0,0,0,0,13,2,0,8,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,6,12,10,0,0,0,0,0,0,0,7,0,0,17,0,0,20484,0,1,19,0,0,0,0,11,0,0,0,0,16]
set_option maxRecDepth 20000 in
lemma Hk:btAll (fun bk => ∀ xs ∈ bk, Impossible ag 7 xs.toFinset) Hj:=refBuckets_all (forall_cons Hg (forall_cons Hh (forall_cons Hi (fun _ h => (List.not_mem_nil h).elim))))
def pC:List NodeSpec:=readDeltaNodes 3 (varNats 3 (unpackWords 4 [(64,0x1110314e1c11a711111046704119319553111110177111041c21151111110467)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hl:∀ ns ∈ pC, Impossible ag 8 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu Hk (by decide +kernel)
def Hm:BT (List (List Nat)):=refBuckets aM [pC] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma Hn:btAll (fun bk => ∀ xs ∈ bk, Impossible ag 8 xs.toFinset) Hm:=refBuckets_all (forall_cons Hl (fun _ h => (List.not_mem_nil h).elim))
def pD:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(19,0x4904d4c1249136)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ho:∀ ns ∈ pD, Impossible ag 9 (nodeValsBT aM ns).toFinset:=blockOk bw 7 (by decide) bq bt bx bu Hn (by decide +kernel)
def Hp:BT (List (List Nat)):=refBuckets aM [pD] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0]
set_option maxRecDepth 20000 in
lemma Hq:btAll (fun bk => ∀ xs ∈ bk, Impossible ag 9 xs.toFinset) Hp:=refBuckets_all (forall_cons Ho (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cX:Lower aH ag 10:=lower_of_forestBT (essPairs:=[(VAR 0,32,33),(VAR 1,8,10),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Hq (by decide +kernel)
def dI:List Nat:=varsOf 251
def dJ:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffffeeaaffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma gr:Lower dI dJ 11:=lift_of (z:=16) (o:=0) (essPairs:=[(VAR 4,0,16)]) (by decide +kernel) cX
def pE:List Nat:=varsOf 253
def pF:Nat:=0xfffffffffffffffffffffffffffffffafffffffffffffffafffffffafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hr:Lower pE pF 13:=carry_of (swaps:=[(1,3)]) (roots2:=gf) (T2:=gg) (by decide +kernel) oO
def pG:List Nat:=varsOf 253
def pH:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafffaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hs:Lower pG pH 12:=lift_of (z:=40) (o:=0) (essPairs:=[(VAR 3,16,24),(VAR 5,1,33)]) (by decide +kernel) bF
def pI:List Nat:=varsOf 254
def pJ:Nat:=0xfffffffffffffffffffffffffffffffffffffffcfffffffcfffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ht:Lower pI pJ 11:=carry_of (swaps:=[(2,4),(0,2)]) (roots2:=cG) (T2:=cH) (by decide +kernel) cV
def pK:List Nat:=varsOf 254
def pL:Nat:=0xfffffffffffffffffffffffffffffffcfffffffffffffffcfffffffffcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hu:Lower pK pL 11:=carry_of (swaps:=[(2,4),(3,4),(1,2),(0,1)]) (roots2:=fV) (T2:=fW) (by decide +kernel) oB
def pM:List Nat:=varsOf 254
def pN:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hv:Lower pM pN 11:=carry_of (swaps:=[(0,2)]) (roots2:=dI) (T2:=dJ) (by decide +kernel) gr
def pO:List Nat:=varsOf 254
def pP:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0fcf0fcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hw:Lower pO pP 11:=carry_of (swaps:=[(0,2),(2,4)]) (roots2:=dI) (T2:=dJ) (by decide +kernel) gr
def gt:List Nat:=varsOf 49
def gu:Nat:=0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pQ:Lower gt gu 4:=carry_of (swaps:=[(3,5),(4,5),(2,4)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def gv:List Nat:=varsOf 52
def gw:Nat:=0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma pR:Lower gv gw 4:=carry_of (swaps:=[(3,5),(1,5),(4,5),(2,4),(0,2)]) (roots2:=aE) (T2:=aB) (by decide +kernel) aG
def gx:List Nat:=varsOf 53
def gy:Nat:=0xfffffafafafaa0a0fffffafafafaa0a0fffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dK:Lower gx gy 7:=carry_of (swaps:=[(5,6)]) (roots2:=aP) (T2:=aw) (by decide +kernel) bE
def pS:List Nat:=varsOf 51
def pT:Nat:=0xffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeeccccffffeeeeeeeecccc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hx:Lower pS pT 5:=carry_of (swaps:=[(5,6),(1,5),(4,5),(1,7),(2,4)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def pU:List Nat:=varsOf 57
def pV:Nat:=0xffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hy:Lower pU pV 5:=carry_of (swaps:=[(5,6),(3,5),(4,5),(3,7),(2,4)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def pW:List Nat:=varsOf 59
def pX:Nat:=0xffffeeaaeeaacc00ffffeeaaeeaacc00ffffeeaaeeaacc00ffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Hz:Lower pW pX 6:=carry_of (swaps:=[(4,5),(2,4)]) (roots2:=cA) (T2:=cB) (by decide +kernel) cL
def pY:List Nat:=varsOf 54
def pZ:Nat:=0xfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfccccc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HA:Lower pY pZ 5:=carry_of (swaps:=[(5,6),(1,5),(4,5),(1,7),(2,4),(0,2)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def qa:List Nat:=varsOf 60
def qb:Nat:=0xfffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HB:Lower qa qb 5:=carry_of (swaps:=[(5,6),(3,5),(1,5),(4,5),(3,7),(2,4),(0,2)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def qc:List Nat:=varsOf 62
def qd:Nat:=0xfffffcf0fcf0cc00fffffcf0fcf0cc00fffffcf0fcf0cc00fffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HC:Lower qc qd 6:=carry_of (swaps:=[(4,5),(2,4),(0,2)]) (roots2:=cA) (T2:=cB) (by decide +kernel) cL
def qe:List Nat:=varsOf 55
def qf:Nat:=0xfffffefefefeececfffffefefefeececfffffefefefeececfffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HD:Lower qe qf 8:=carry_of (swaps:=[(5,7),(4,6),(2,3),(0,1)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def qg:List Nat:=varsOf 61
def qh:Nat:=0xfffffffafffaffa0fffffffafffaffa0fffffffafffaffa0fffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HE:Lower qg qh 8:=carry_of (swaps:=[(5,7),(4,6),(2,3),(1,3),(0,3)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def qi:List Nat:=varsOf 63
def qj:Nat:=0xfffffefafefaeca0fffffefafefaeca0fffffefafefaeca0fffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HF:Lower qi qj 9:=lift_of (z:=2) (o:=8) (essPairs:=[(VAR 1,8,10),(VAR 3,2,10)]) (by decide +kernel) dK
def qk:List Nat:=varsOf 117
def ql:Nat:=0xfffffafafffffafafffffafafafaa0a0fffffafafffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HG:Lower qk ql 8:=lift_of (z:=32) (o:=0) (essPairs:=[(VAR 5,1,33)]) (by decide +kernel) bE
def qm:List Nat:=varsOf 117
def qn:Nat:=0xfffffffffffffafafffffafafafaa0a0fffffffffffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HH:Lower qm qn 10:=carry_of (swaps:=[(5,7),(5,6)]) (roots2:=aD) (T2:=Z) (by decide +kernel) bF
def bM:List Nat:=varsOf 119
def bg:Nat:=0xfffffefefffffefefffffafafafaa0a0fffffefefffffefefffffafafafaa0a0
def gz:List Nat:=[5,66,7,17,20,5,20,17,36,33,33,66,65,65,7,19,35,98,36,68,68,48,48,80,80,98]
def gA:List Nat:=[4,64,6,16,16,1,4,1,4,1,32,2,1,64,3,3,3,96,32,4,64,16,32,16,64,34]
def qo:Nat:=fullMask 26
def qp:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1f6ad,0x1d2a0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x203c806,0x201c804),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1c4175,0x80145),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x1e080d8,0xa00018),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x2670700,0x2460400),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x39a3802,0x1122002)]
def HI:List (Nat × Nat × Nat):=[]
def cY:BT Decor:=buildWiresBT 3 qp HI
def HJ:List (List (Nat × Nat)):=[[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def gB:BT (List (Nat × Nat)):=btOfList 3 HJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HK:goodPairs bg gz gA:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HL:∀ x ∈ qp, faithful gz gA x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HM:btAll (fun x => faithful gz gA x ∧ x.1 < 2^256) cY:=buildWiresBT_faithful HL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HN:btAll (fun sw => swapsValid sw = true ∧ permWord sw bg = bg) gB:=btAll_ofList (autos_of (by decide +kernel))
def HO:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,10)]
def qq:BT (Option (Nat × Nat)):=btOfList 1 HO
def HP:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def gC:BT (Option BoundPool):=buildPoolsBT 1 cY bM qq HP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HQ:Slice bM bg (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 10:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=qm) (G:=qn) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) HH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HR:btAll (fun o => ∀ p, o = some p → Slice bM bg p.1 p.2) qq:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bM bg p.1 p.2) (forall_cons (someSlice HQ) (fun _ h => (List.not_mem_nil h).elim))
lemma HS:btAll (fun o => ∀ c, o = some c → ValidPool bM bg c) gC:=buildPoolsBT_sound HR
def gD:BT (List (List Nat)):=BT.empty
lemma HT:btAll (fun bk => ∀ xs ∈ bk, Impossible bg (9 - 1) xs.toFinset) gD:=trivial
def qr:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(10,19173390)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HU:checkNodesBT cY bg qo gC gB gD 9 qr = true:=by decide +kernel
def qs:List NodeSpec:=qr
set_option maxRecDepth 20000 in
lemma HV:checkNodesBT cY bg qo gC gB gD 9 qs = true:=HU
def HW:BT (List (List Nat)):=buildBucketsBT cY qs
set_option maxRecDepth 20000 in
lemma HX:btAll (fun bk => ∀ xs ∈ bk, Impossible bg 9 xs.toFinset) HW:=buildBucketsBT_sound (by decide) HK HM HS HN HT HV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dL:Lower bM bg 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) HX (by decide +kernel)
def qt:List Nat:=varsOf 122
def qu:Nat:=0xffffffccffffffccffffcc00cc00cc00ffffffccffffffccffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HY:Lower qt qu 7:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=aN) (T2:=az) (by decide +kernel) cj
def qv:List Nat:=varsOf 121
def qw:Nat:=0xffffffffffffffffffffffaaffaaff00ffffffffffffffffffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma HZ:Lower qv qw 6:=carry_of (swaps:=[(4,5),(2,4)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def qx:List Nat:=varsOf 123
def qy:Nat:=0xffffffeeffffffeeffffeeaaeeaacc00ffffffeeffffffeeffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ia:Lower qx qy 10:=carry_of (swaps:=[(2,4)]) (roots2:=aA) (T2:=af) (by decide +kernel) cp
def qz:List Nat:=varsOf 117
def qA:Nat:=0xfffffffffffffffffffffafafafaa0a0fffffffffffffffffffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ib:Lower qz qA 8:=carry_of (swaps:=[(2,4),(5,7),(4,6),(2,3),(1,6),(0,6)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def qB:List Nat:=varsOf 125
def qC:Nat:=0xfffffffafffffffafffffafafafaa0a0fffffffafffffffafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ic:Lower qB qC 10:=carry_of (swaps:=[(1,3)]) (roots2:=bM) (T2:=bg) (by decide +kernel) dL
def qD:List Nat:=varsOf 124
def qE:Nat:=0xfffffffffffffffffffffff0fff0ff00fffffffffffffffffffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Id:Lower qD qE 6:=carry_of (swaps:=[(1,5),(4,5),(2,4),(0,2)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def qF:List Nat:=varsOf 126
def qG:Nat:=0xfffffffcfffffffcfffffcf0fcf0cc00fffffffcfffffffcfffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ie:Lower qF qG 10:=carry_of (swaps:=[(2,4),(0,2)]) (roots2:=aA) (T2:=af) (by decide +kernel) cp
def qH:List Nat:=varsOf 95
def qI:Nat:=0xfffffffefffffffefffffefafffffefafffffffefffffffefffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma If:Lower qH qI 7:=carry_of (swaps:=[(3,5),(3,4),(4,7),(3,6),(2,3),(0,1)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def cb:List Nat:=varsOf 119
def cc:Nat:=0xfffffffffffffffffffffefefefeececfffffffffffffffffffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cr:Lower cb cc 9:=lift_of (z:=66) (o:=0) (essPairs:=[(VAR 1,0,2),(VAR 6,0,64)]) (by decide +kernel) dK
def qJ:List Nat:=varsOf 125
def qK:Nat:=0xfffffffffffffffffffffffafffaffa0fffffffffffffffffffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ig:Lower qJ qK 9:=carry_of (swaps:=[(1,3)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def gE:List Nat:=varsOf 127
def gF:Nat:=0xfffffffefffffffefffffefafefaeca0fffffffefffffffefffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma qM:Lower gE gF 12:=lift_of (z:=32) (o:=0) (essPairs:=[(VAR 5,1,33)]) (by decide +kernel) dy
def qN:List Nat:=varsOf 139
def qO:Nat:=0xffeeffeeffeeffeeffeeffeeffeeffeeeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ih:Lower qN qO 5:=carry_of (swaps:=[(1,3),(1,4),(1,7),(2,3),(0,1)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def qP:List Nat:=varsOf 173
def qQ:Nat:=0xfffafffafffafffafffafffafffafffafafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ii:Lower qP qQ 7:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def qR:List Nat:=varsOf 174
def qS:Nat:=0xfffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0cc00cc00fcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ij:Lower qR qS 7:=carry_of (swaps:=[(6,7),(0,2)]) (roots2:=aN) (T2:=az) (by decide +kernel) cj
def qT:List Nat:=varsOf 143
def qU:Nat:=0xfffefffefffefffefffefffefffefffefefafefafefafefafefafefafefafefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ik:Lower qT qU 6:=carry_of (swaps:=[(1,7),(4,7),(1,6),(1,3),(2,3),(0,1)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def gG:List Nat:=varsOf 175
def gH:Nat:=0xfffefffefffefffefffefffefffefffefefafefaeca0eca0fefafefaeca0eca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma qV:Lower gG gH 10:=carry_of (swaps:=[(6,7)]) (roots2:=aA) (T2:=af) (by decide +kernel) cp
def qW:List Nat:=varsOf 183
def qX:Nat:=0xfffffefefffffefefffffefefffffefefffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Il:Lower qW qX 10:=carry_of (swaps:=[(6,7)]) (roots2:=bM) (T2:=bg) (by decide +kernel) dL
def qY:List Nat:=varsOf 184
def qZ:Nat:=0xffffff00ffffff00ffffff00ffffff00ffff000000000000ffff000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Im:Lower qY qZ 4:=carry_of (swaps:=[(2,4),(6,7),(0,4),(1,3)]) (roots2:=bG) (T2:=aX) (by decide +kernel) cE
def ra:List Nat:=varsOf 185
def rb:Nat:=0xffffffaaffffffaaffffffaaffffffaaffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma In:Lower ra rb 7:=carry_of (swaps:=[(2,4),(6,7),(1,3)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def rc:List Nat:=varsOf 154
def rd:Nat:=0xffffffccffffffccffffffccffffffccffffcc00ffffcc00ffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Io:Lower rc rd 5:=carry_of (swaps:=[(4,7),(2,3),(0,1)]) (roots2:=aU) (T2:=aV) (by decide +kernel) aZ
def re:List Nat:=varsOf 186
def rf:Nat:=0xffffffccffffffccffffffccffffffccffffcc00cc00cc00ffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ip:Lower re rf 7:=carry_of (swaps:=[(2,4),(6,7),(0,4)]) (roots2:=aN) (T2:=az) (by decide +kernel) cj
def rg:List Nat:=varsOf 155
def rh:Nat:=0xffffffeeffffffeeffffffeeffffffeeffffeeaaffffeeaaffffeeaaffffeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iq:Lower rg rh 6:=carry_of (swaps:=[(4,7),(4,6),(1,3),(2,3),(0,1)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def ri:List Nat:=varsOf 187
def rj:Nat:=0xffffffeeffffffeeffffffeeffffffeeffffeeaaeeaacc00ffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ir:Lower ri rj 10:=carry_of (swaps:=[(6,7),(2,4)]) (roots2:=aA) (T2:=af) (by decide +kernel) cp
def rk:List Nat:=varsOf 188
def rl:Nat:=0xfffffff0fffffff0fffffff0fffffff0fffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Is:Lower rk rl 7:=carry_of (swaps:=[(3,4),(2,4),(0,2),(6,7),(1,3)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def rm:List Nat:=varsOf 181
def ro:Nat:=0xfffffffffffffffffffffffffffffffffffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma It:Lower rm ro 8:=carry_of (swaps:=[(4,5),(2,5),(5,7),(4,6),(2,3),(1,7),(0,7)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def rp:List Nat:=varsOf 189
def rq:Nat:=0xfffffffafffffffafffffffafffffffafffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iu:Lower rp rq 10:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=bM) (T2:=bg) (by decide +kernel) dL
def rr:List Nat:=varsOf 158
def rt:Nat:=0xfffffffcfffffffcfffffffcfffffffcfffffcf0fffffcf0fffffcf0fffffcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iv:Lower rr rt 6:=carry_of (swaps:=[(4,7),(4,6),(2,3),(0,1)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def ru:List Nat:=varsOf 188
def rv:Nat:=0xfffffffffffffffffffffffffffffffffffffff0fff0ff00fffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iw:Lower ru rv 6:=carry_of (swaps:=[(1,5),(4,5),(6,7),(2,4),(0,2)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def rx:List Nat:=varsOf 190
def ry:Nat:=0xfffffffcfffffffcfffffffcfffffffcfffffcf0fcf0cc00fffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ix:Lower rx ry 10:=carry_of (swaps:=[(6,7),(2,4),(0,2)]) (roots2:=aA) (T2:=af) (by decide +kernel) cp
def rz:List Nat:=varsOf 159
def rA:Nat:=0xfffffffefffffffefffffffefffffffefffffefafffffefafffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iy:Lower rz rA 7:=carry_of (swaps:=[(3,5),(4,7),(3,6),(2,3),(0,1)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def rB:List Nat:=varsOf 183
def rC:Nat:=0xfffffffffffffffffffffffffffffffffffffefefefeececfffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Iz:Lower rB rC 9:=carry_of (swaps:=[(6,7)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def rD:List Nat:=varsOf 189
def rE:Nat:=0xfffffffffffffffffffffffffffffffffffffffafffaffa0fffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IA:Lower rD rE 9:=carry_of (swaps:=[(6,7),(1,3)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def rF:List Nat:=varsOf 191
def rG:Nat:=0xfffffffefffffffefffffffefffffffefffffefafefaeca0fffffefafefaeca0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IB:Lower rF rG 12:=carry_of (swaps:=[(6,7)]) (roots2:=gE) (T2:=gF) (by decide +kernel) qM
def rH:List Nat:=varsOf 211
def rI:Nat:=0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeaaaa0000aaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IC:Lower rH rI 8:=carry_of (swaps:=[(5,7),(1,7),(6,7),(4,6),(2,4),(1,3)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def rJ:List Nat:=varsOf 229
def rK:Nat:=0xfffffffffffffffffafafafafafafafafafafafafafafafafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ID:Lower rJ rK 8:=carry_of (swaps:=[(6,7),(4,6),(2,7),(0,6),(3,5)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def bC:List Nat:=varsOf 231
def aO:Nat:=0xfffffffffffffffffefefefefefefefefefefefefefefefefafafafaa0a0a0a0
def gI:List Nat:=[5,66,7,33,36,5,36,33,66,65,65,130,129,129,7,35,98,130,68,68,132,132,98,162,192,192]
def gJ:List Nat:=[4,64,6,32,32,1,4,1,2,1,64,2,1,128,3,3,96,128,4,64,4,128,34,34,64,128]
def rL:Nat:=fullMask 26
def rM:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf6ad,0xd2a0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xc3c906,0xc0c904),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c4075,0x140045),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc180d8,0xc10018),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x34d0702,0x1090402),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3b23800,0x2222000)]
def IE:List (Nat × Nat × Nat):=[]
def cZ:BT Decor:=buildWiresBT 3 rM IE
def IF:List (List (Nat × Nat)):=[[],[(6,7)],[(0,2)],[(6,7),(0,2)],[(2,7),(1,5),(0,6)],[(2,6),(1,5),(0,7)],[(6,7),(2,7),(1,5),(0,6)],[(6,7),(2,6),(1,5),(0,7)]]
def gK:BT (List (Nat × Nat)):=btOfList 3 IF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IG:goodPairs aO gI gJ:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IH:∀ x ∈ rM, faithful gI gJ x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma II:btAll (fun x => faithful gI gJ x ∧ x.1 < 2^256) cZ:=buildWiresBT_faithful IH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IJ:btAll (fun sw => swapsValid sw = true ∧ permWord sw aO = aO) gK:=btAll_ofList (autos_of (by decide +kernel))
def IK:List (Option (Nat × Nat)):=[some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,10)]
def rN:BT (Option (Nat × Nat)):=btOfList 1 IK
def IL:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 1 (unpackWords 1 [(2,0)])
def gL:BT (Option BoundPool):=buildPoolsBT 1 cZ bC rN IL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IM:Slice bC aO (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 10:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=fX) (G:=fY) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) oE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IN:btAll (fun o => ∀ p, o = some p → Slice bC aO p.1 p.2) rN:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice bC aO p.1 p.2) (forall_cons (someSlice IM) (fun _ h => (List.not_mem_nil h).elim))
lemma IP:btAll (fun o => ∀ c, o = some c → ValidPool bC aO c) gL:=buildPoolsBT_sound IN
def gM:BT (List (List Nat)):=BT.empty
lemma IQ:btAll (fun bk => ∀ xs ∈ bk, Impossible aO (9 - 1) xs.toFinset) gM:=trivial
def rO:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(10,19173390)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IR:checkNodesBT cZ aO rL gL gK gM 9 rO = true:=by decide +kernel
def rP:List NodeSpec:=rO
set_option maxRecDepth 20000 in
lemma IS:checkNodesBT cZ aO rL gL gK gM 9 rP = true:=IR
def IT:BT (List (List Nat)):=buildBucketsBT cZ rP
set_option maxRecDepth 20000 in
lemma IU:btAll (fun bk => ∀ xs ∈ bk, Impossible aO 9 xs.toFinset) IT:=buildBucketsBT_sound (by decide) IG II IP IJ IQ IS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cz:Lower bC aO 10:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,64,66),(VAR 2,1,5),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) IU (by decide +kernel)
def rQ:List Nat:=varsOf 236
def rR:Nat:=0xfffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0f0f0f0f000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IV:Lower rQ rR 7:=carry_of (swaps:=[(4,7),(3,7),(2,7),(0,2),(2,6),(3,5),(1,5)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def rS:List Nat:=varsOf 205
def rT:Nat:=0xfffffffffffffffffffafffafffafffafffafffafffafffafafafafafafafafa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IW:Lower rS rT 6:=carry_of (swaps:=[(5,7),(4,7),(2,6),(0,3)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def gN:List Nat:=varsOf 237
def gO:Nat:=0xfffffffffffffffffffafffafffafffafffafffafffafffafafafafaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rU:Lower gN gO 10:=carry_of (swaps:=[(1,3)]) (roots2:=bC) (T2:=aO) (by decide +kernel) cz
def rV:List Nat:=varsOf 206
def rW:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0fcf0fcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IX:Lower rV rW 8:=carry_of (swaps:=[(0,2)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def gP:List Nat:=varsOf 238
def gQ:Nat:=0xfffffffffffffffffffcfffcfffcfffcfffcfffcfffcfffcfcf0fcf0cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rX:Lower gP gQ 10:=carry_of (swaps:=[(0,2)]) (roots2:=aH) (T2:=ag) (by decide +kernel) cX
def rY:List Nat:=varsOf 207
def rZ:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffefefafefafefafefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IY:Lower rY rZ 9:=carry_of (swaps:=[(5,7),(3,4),(2,3),(2,6),(0,1)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def sa:List Nat:=varsOf 237
def sb:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffafffaffa0ffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma IZ:Lower sa sb 7:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def sd:List Nat:=varsOf 231
def se:Nat:=0xfffffffffffffffffffffffffefefefefffffffffefefefefefefefea0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ja:Lower sd se 11:=carry_of (swaps:=[(4,5),(1,3)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dj
def sf:List Nat:=varsOf 237
def sg:Nat:=0xfffffffffffffffffffffffffffafffafffffffffffafffafffafffaa0a0a0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jb:Lower sf sg 11:=carry_of (swaps:=[(4,5)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dj
def aY:List Nat:=varsOf 239
def aI:Nat:=0xfffffffffffffffffffefffefffefffefffefffefffefffefefafefaeca0eca0
def gR:List Nat:=[5,10,7,11,33,36,5,10,11,13,36,33,66,65,65,130,129,129,7,14,66,72,35,42,130,13,14,68,68,132,132,41,42,72,136,136,98,162,192,192]
def gS:List Nat:=[4,8,6,9,32,32,1,2,3,12,4,1,2,1,64,2,1,128,3,12,64,64,3,40,128,9,6,4,64,4,128,9,34,8,8,128,34,34,64,128]
def si:Nat:=fullMask 40
def sj:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x82476b5d,0x82452948),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x3105dc918e,0x3104449184),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7e0c0665,0x2c080605),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xf86a8038a,0x68288020a),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3180c00c30,0x3100800030),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xd218307000,0x4010304000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xec61038000,0x8841020000)]
def Jc:List (Nat × Nat × Nat):=[]
def da:BT Decor:=buildWiresBT 3 sj Jc
def Jd:List (List (Nat × Nat)):=[[],[(6,7)],[(1,3)],[(0,2)],[(6,7),(1,3)],[(6,7),(0,2)],[(1,3),(0,2)],[(6,7),(1,3),(0,2)]]
def gT:BT (List (Nat × Nat)):=btOfList 3 Jd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Je:goodPairs aI gR gS:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jf:∀ x ∈ sj, faithful gR gS x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jg:btAll (fun x => faithful gR gS x ∧ x.1 < 2^256) da:=buildWiresBT_faithful Jf
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jh:btAll (fun sw => swapsValid sw = true ∧ permWord sw aI = aI) gT:=btAll_ofList (autos_of (by decide +kernel))
def Ji:List (Option (Nat × Nat)):=[some (subcubeFast 1 0,10),some (subcubeFast 2 0,10),some (subcubeFast 4 0,10),some (subcubeFast 8 0,10),some (subcubeFast 32 0,10),some (subcubeFast 64 0,10),some (subcubeFast 128 0,10),some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,11),some (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff,11)]
def sk:BT (Option (Nat × Nat)):=btOfList 4 Ji
def Jj:List PoolSpec:=readSpecs ((readChoices 0 []).toArray) 6 (unpackWords 3 [(12,6527393856)])
def gU:BT (Option BoundPool):=buildPoolsBT 4 da aY sk Jj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jk:Slice aY aI (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff) 11:=mappedSlice (f:=identifyRow 0 0 5 3) (R:=sd) (G:=se) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ja
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jl:Slice aY aI (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 11:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=sf) (G:=sg) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Jb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jm:Slice aY aI (subcubeFast 128 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aA) (qGoal:=af) (by decide +kernel) cp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jn:Slice aY aI (subcubeFast 64 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gG) (qGoal:=gH) (by decide +kernel) qV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jo:Slice aY aI (subcubeFast 32 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bo) (qGoal:=aK) (by decide +kernel) cD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jp:Slice aY aI (subcubeFast 8 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bC) (qGoal:=aO) (by decide +kernel) cz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jq:Slice aY aI (subcubeFast 4 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aH) (qGoal:=ag) (by decide +kernel) cX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jr:Slice aY aI (subcubeFast 2 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gN) (qGoal:=gO) (by decide +kernel) rU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Js:Slice aY aI (subcubeFast 1 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gP) (qGoal:=gQ) (by decide +kernel) rX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jt:btAll (fun o => ∀ p, o = some p → Slice aY aI p.1 p.2) sk:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice aY aI p.1 p.2) (forall_cons (someSlice Js) (forall_cons (someSlice Jr) (forall_cons (someSlice Jq) (forall_cons (someSlice Jp) (forall_cons (someSlice Jo) (forall_cons (someSlice Jn) (forall_cons (someSlice Jm) (forall_cons (someSlice Jl) (forall_cons (someSlice Jk) (fun _ h => (List.not_mem_nil h).elim))))))))))
lemma Ju:btAll (fun o => ∀ c, o = some c → ValidPool aY aI c) gU:=buildPoolsBT_sound Jt
def gV:BT (List (List Nat)):=BT.empty
lemma Jv:btAll (fun bk => ∀ xs ∈ bk, Impossible aI (11 - 1) xs.toFinset) gV:=trivial
def sm:List NodeSpec:=readDeltaNodes 1 (unpackWords 3 [(16,40209637216311)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Jw:checkNodesBT da aI si gU gT gV 11 sm = true:=by decide +kernel
def sn:List NodeSpec:=sm
set_option maxRecDepth 20000 in
lemma Jx:checkNodesBT da aI si gU gT gV 11 sn = true:=Jw
def Jy:BT (List (List Nat)):=buildBucketsBT da sn
set_option maxRecDepth 20000 in
lemma Jz:btAll (fun bk => ∀ xs ∈ bk, Impossible aI 11 xs.toFinset) Jy:=buildBucketsBT_sound (by decide) Je Jg Ju Jh Jv Jx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma gW:Lower aY aI 12:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Jz (by decide +kernel)
def so:List Nat:=varsOf 243
def sp:Nat:=0xffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeeeffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JA:Lower so sp 10:=carry_of (swaps:=[(3,4),(2,4)]) (roots2:=bC) (T2:=aO) (by decide +kernel) cz
def sq:List Nat:=varsOf 244
def sr:Nat:=0xfffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JB:Lower sq sr 8:=carry_of (swaps:=[(5,7),(1,7),(6,7),(4,7),(2,7),(0,6),(3,5)]) (roots2:=bd) (T2:=be) (by decide +kernel) bn
def st:List Nat:=varsOf 245
def su:Nat:=0xfffffffffffffffffffffafafffffafafffffafafffffafafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JC:Lower st su 11:=carry_of (swaps:=[(6,7),(4,6),(2,7),(0,6),(3,5)]) (roots2:=cJ) (T2:=cK) (by decide +kernel) dj
def sv:List Nat:=varsOf 244
def sx:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JD:Lower sv sx 6:=carry_of (swaps:=[(1,5),(4,5),(6,7),(3,6),(2,4),(0,2)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def sy:List Nat:=varsOf 246
def sz:Nat:=0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfcfffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JE:Lower sy sz 10:=carry_of (swaps:=[(3,4),(2,4),(0,2)]) (roots2:=bC) (T2:=aO) (by decide +kernel) cz
def gX:List Nat:=varsOf 245
def gY:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sA:Lower gX gY 9:=carry_of (swaps:=[(3,7),(6,7),(1,6)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def gZ:List Nat:=varsOf 247
def hA:Nat:=0xfffffffffffffffffffffefefffffefefffffefefffffefefffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma sB:Lower gZ hA 12:=lift_of (z:=34) (o:=0) (essPairs:=[(VAR 1,64,66),(VAR 5,1,33)]) (by decide +kernel) bF
def sC:List Nat:=varsOf 248
def sD:Nat:=0xffffffffffffffffffffff00ffffff00ffffff00ffffff00ffff000000000000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JF:Lower sC sD 7:=carry_of (swaps:=[(3,4),(2,7),(0,4),(4,6),(3,5),(1,5)]) (roots2:=bp) (T2:=aL) (by decide +kernel) bY
def sE:List Nat:=varsOf 217
def sF:Nat:=0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JG:Lower sE sF 6:=carry_of (swaps:=[(5,7),(4,7),(4,6),(2,6),(0,3)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def sG:List Nat:=varsOf 249
def sH:Nat:=0xffffffffffffffffffffffaaffffffaaffffffaaffffffaaffffaaaaaaaa0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JH:Lower sG sH 10:=carry_of (swaps:=[(2,4),(1,3)]) (roots2:=bC) (T2:=aO) (by decide +kernel) cz
def sI:List Nat:=varsOf 218
def sJ:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffccffffcc00ffffcc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JI:Lower sI sJ 8:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=bZ) (T2:=ca) (by decide +kernel) cq
def sK:List Nat:=varsOf 250
def sL:Nat:=0xffffffffffffffffffffffccffffffccffffffccffffffccffffcc00cc00cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JJ:Lower sK sL 10:=carry_of (swaps:=[(2,4),(0,4)]) (roots2:=aH) (T2:=ag) (by decide +kernel) cX
def sM:List Nat:=varsOf 219
def sN:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffffeeaaffffeeaa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JK:Lower sM sN 9:=carry_of (swaps:=[(5,7),(2,3),(4,6),(0,1)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def sO:List Nat:=varsOf 249
def sP:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffaaff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JL:Lower sO sP 7:=carry_of (swaps:=[(4,5),(1,3),(2,4)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def sQ:List Nat:=varsOf 251
def sR:Nat:=0xffffffffffffffffffffffeeffffffeeffffffeeffffffeeffffeeaaeeaacc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JM:Lower sQ sR 12:=carry_of (swaps:=[(2,4)]) (roots2:=aY) (T2:=aI) (by decide +kernel) gW
def sS:List Nat:=varsOf 220
def sT:Nat:=0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fffff0f0fffff0f0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JN:Lower sS sT 6:=carry_of (swaps:=[(5,7),(1,7),(4,7),(4,6),(3,6),(2,6),(0,3)]) (roots2:=aR) (T2:=aS) (by decide +kernel) aW
def sU:List Nat:=varsOf 252
def sV:Nat:=0xfffffffffffffffffffffff0fffffff0fffffff0fffffff0fffff0f0f0f00000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JO:Lower sU sV 10:=carry_of (swaps:=[(3,4),(2,4),(0,2),(1,3)]) (roots2:=bC) (T2:=aO) (by decide +kernel) cz
def sW:List Nat:=varsOf 221
def sX:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafffffafa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JP:Lower sW sX 7:=carry_of (swaps:=[(4,7),(1,3),(2,6),(0,3)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def sY:List Nat:=varsOf 253
def sZ:Nat:=0xfffffffffffffffffffffffafffffffafffffffafffffffafffffafafafaa0a0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JQ:Lower sY sZ 12:=carry_of (swaps:=[(1,3)]) (roots2:=gZ) (T2:=hA) (by decide +kernel) sB
def ta:List Nat:=varsOf 222
def tb:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0fffffcf0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JR:Lower ta tb 9:=carry_of (swaps:=[(5,7),(2,3),(0,2),(4,6),(1,2)]) (roots2:=cb) (T2:=cc) (by decide +kernel) cr
def tc:List Nat:=varsOf 252
def td:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff0fff0ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JS:Lower tc td 7:=carry_of (swaps:=[(3,5),(4,5),(1,3),(2,4),(0,2)]) (roots2:=bR) (T2:=bS) (by decide +kernel) ci
def te:List Nat:=varsOf 254
def tf:Nat:=0xfffffffffffffffffffffffcfffffffcfffffffcfffffffcfffffcf0fcf0cc00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JT:Lower te tf 12:=carry_of (swaps:=[(2,4),(0,2)]) (roots2:=aY) (T2:=aI) (by decide +kernel) gW
def dM:List Nat:=varsOf 223
def dN:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefffffefafffffefa
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma hB:Lower dM dN 10:=lift_of (z:=21) (o:=0) (essPairs:=[(VAR 0,0,1),(VAR 2,0,4),(VAR 4,0,16)]) (by decide +kernel) cC
def tg:List Nat:=varsOf 247
def th:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffefefefeecec
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JU:Lower tg th 10:=carry_of (swaps:=[(5,7),(6,7),(3,6),(4,7),(2,6),(0,1)]) (roots2:=dM) (T2:=dN) (by decide +kernel) hB
def ti:List Nat:=varsOf 253
def tj:Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffafffaffa0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JV:Lower ti tj 10:=carry_of (swaps:=[(5,7),(6,7),(3,6),(1,3),(4,7),(2,6),(0,3)]) (roots2:=dM) (T2:=dN) (by decide +kernel) hB
def E:List Nat:=varsOf 255
def A:Nat:=0xfffffffffffffffffffffffefffffffefffffffefffffffefffffefafefaeca0
def hC:List Nat:=[5,10,7,11,5,19,20,5,10,11,20,17,36,33,35,66,65,7,72,19,35,67,129,130,13,14,22,22,28,68,68,26,28,41,42,136,136,65,76,48,144,162,97,100,134,140,176,164,73,192,33,80,112,224,192,36,48,10,104,224,38,10,14,80,70,66,82,98,98,68,48,36,13,26,33,88,56,25,130,162,129,131,25,146,161,80,36,48,42,137,17,152,144,132,66,68,17,84,148,17,144,168,50,21,17,132,80,5,44,81,38,50,41,129,5,21,5,33,65,68,144,80,133,145,66,21,37,69,17,65,129,80,145,11,67,35,161,7,13,10,81,19,129,20,133,84,44,33]
def hD:List Nat:=[4,8,6,9,6,18,16,1,2,3,4,1,4,1,34,2,1,3,64,3,3,3,1,2,9,6,18,6,24,4,64,18,12,9,34,8,128,64,12,16,16,34,96,96,6,12,160,160,9,64,96,64,96,96,128,32,32,9,40,160,34,12,12,16,6,64,18,34,96,6,96,96,12,24,32,24,40,9,128,160,3,3,24,18,160,18,160,160,40,9,18,24,0,4,6,1,4,16,16,16,128,40,34,4,64,128,1,64,40,1,6,18,40,128,0,16,128,160,16,16,64,128,0,16,18,0,32,0,0,0,0,0,1,8,1,1,1,2,8,0,16,1,9,0,4,4,12,0]
def PF:Nat:=fullMask 148
def tk:List Decor:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x977f7ec7f29890617250000050422017b6abd,0x61d0000024008203200002010002017b2a88),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2ae01000c040410ac21f720012048ebac32e,0x2001000c040442b002d100012048ebac334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x78600e49c5a86a04001a15080b8417f0214d5,0x700000000408160000121600030412a001415),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x40c20000110200b043b006601205f9304030a,0x44420000110200b043b006601204b1100000a),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x2b0192b08a5df1cac3a44811841819c080c60,0x100018c8800e0c2c0a048000018094000060),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc01804021d06001d094d81db4ce8600107000,0x4021106001d094d81db4ce0400004000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x2104a92c02402c020083f8c7b0c6060258000,0x1000900000000d2003e0c2040040000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x141140d0202343a1bc0000862f31800c00000,0x232021000d0c0000840c01000000000)]
def JW:List (Nat × Nat × Nat):=[(1,0,1),(1,0,2),(1,0,4),(1,0,6),(1,1,2),(0,1,3),(1,1,3),(3,1,3),(1,1,6),(1,1,7),(1,1,11),(1,2,4),(1,2,6),(1,3,7),(1,3,8),(1,4,7),(1,4,11),(1,4,20),(1,5,7),(1,7,11),(1,7,19),(1,7,20),(1,8,20),(1,11,20),(1,11,28),(3,11,28),(1,20,28),(1,11,19),(1,2,7),(1,2,8),(1,4,6),(1,5,6),(1,6,7),(3,2,34),(3,4,34),(3,7,34),(1,8,25),(3,2,32),(3,4,32),(3,6,32),(3,7,32),(1,6,33),(3,4,35),(1,7,39),(1,0,7),(1,0,19),(1,3,16),(1,7,16),(1,0,28),(1,7,38),(1,8,38),(3,2,18),(1,4,59),(3,4,59),(1,7,18),(3,0,32),(1,2,63),(3,2,63),(1,4,63),(3,4,63),(3,4,37),(1,3,17),(1,5,9),(2,5,40),(1,9,40),(1,10,40),(3,10,40),(1,16,72),(3,19,72),(3,9,40),(1,7,9),(1,7,10),(3,2,40),(3,4,40),(3,2,72),(3,1,40),(3,1,72),(3,7,72),(3,6,72),(0,3,55),(3,3,55),(3,4,73),(3,6,73),(3,4,78),(1,4,86),(3,4,86),(3,4,30),(1,5,83),(1,9,83),(1,10,96),(1,10,83),(1,19,83),(1,10,77),(3,10,77),(1,19,77),(3,7,24),(1,9,89),(1,4,74),(1,2,83),(3,4,99),(3,9,99),(3,2,96),(3,4,96),(1,4,83),(1,1,110),(3,1,110),(1,4,82),(1,6,46),(1,7,46),(1,2,77),(3,4,117),(1,4,77),(3,4,100),(1,4,85),(3,5,53),(3,1,27),(1,5,27),(3,5,27),(1,4,41),(1,2,81),(3,0,40),(1,16,122),(1,40,122),(2,40,122),(1,6,122),(3,7,132),(1,7,122),(3,0,72),(1,17,46),(3,6,130),(3,0,44),(1,0,77),(3,0,57),(1,0,45),(1,0,83),(3,4,142),(1,83,122),(3,0,97),(3,2,97),(1,2,145),(1,0,101),(1,4,146),(3,0,98),(1,83,110),(1,0,81),(3,0,51),(1,13,40),(1,14,50),(3,3,112),(1,4,113),(3,3,75),(3,0,119),(1,6,13),(3,1,116),(3,3,136),(1,5,128),(3,3,62),(1,4,123),(1,6,71)]
def C:BT Decor:=buildWiresBT 8 tk JW
def JX:List (List (Nat × Nat)):=[[],[(6,7)],[(2,4)],[(1,3)],[(0,2)],[(0,4)],[(6,7),(2,4)],[(6,7),(1,3)],[(2,4),(1,3)],[(6,7),(0,2)],[(2,4),(0,2)],[(1,3),(0,2)],[(2,4),(0,4)],[(6,7),(0,4)],[(1,3),(0,4)],[(6,7),(2,4),(1,3)],[(6,7),(2,4),(0,2)],[(6,7),(1,3),(0,2)],[(2,4),(1,3),(0,2)],[(6,7),(2,4),(0,4)],[(2,4),(1,3),(0,4)],[(6,7),(1,3),(0,4)],[(6,7),(2,4),(1,3),(0,2)],[(6,7),(2,4),(1,3),(0,4)]]
def JY:BT (List (Nat × Nat)):=btOfList 5 JX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma F:goodPairs A hC hD:=goodPairs_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma JZ:∀ x ∈ tk, faithful hC hD x ∧ x.1 < 2^256:=base_of (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma H:btAll (fun x => faithful hC hD x ∧ x.1 < 2^256) C:=buildWiresBT_faithful JZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma I:btAll (fun sw => swapsValid sw = true ∧ permWord sw A = A) JY:=btAll_ofList (autos_of (by decide +kernel))
def Ka:List (Option (Nat × Nat)):=[some (subcubeFast 0 2,10),some (subcubeFast 0 8,10),some (subcubeFast 0 32,10),some (subcubeFast 1 0,12),some (subcubeFast 1 2,7),some (subcubeFast 1 32,9),some (subcubeFast 2 0,12),some (subcubeFast 2 8,9),some (subcubeFast 2 32,7),some (subcubeFast 3 0,10),some (subcubeFast 3 32,6),some (subcubeFast 4 0,12),some (subcubeFast 4 2,7),some (subcubeFast 4 32,9),some (subcubeFast 5 0,10),some (subcubeFast 5 32,8),some (subcubeFast 6 0,10),some (subcubeFast 6 32,6),some (subcubeFast 7 0,7),some (subcubeFast 8 0,12),some (subcubeFast 8 2,9),some (subcubeFast 9 0,10),some (subcubeFast 9 2,6),some (subcubeFast 10 0,11),some (subcubeFast 11 0,8),some (subcubeFast 12 0,10),some (subcubeFast 16 0,12),some (subcubeFast 16 2,7),some (subcubeFast 16 32,9),some (subcubeFast 17 0,10),some (subcubeFast 17 32,8),some (subcubeFast 18 0,10),some (subcubeFast 18 32,6),some (subcubeFast 19 0,7),some (subcubeFast 20 0,10),some (subcubeFast 20 32,8),some (subcubeFast 21 32,7),some (subcubeFast 23 32,4),some (subcubeFast 24 0,10),some (subcubeFast 26 0,8),some (subcubeFast 32 0,13),some (subcubeFast 33 0,10),some (subcubeFast 34 0,11),some (subcubeFast 35 0,8),some (subcubeFast 36 0,10),some (subcubeFast 37 0,8),some (subcubeFast 38 0,8),some (subcubeFast 40 0,11),some (subcubeFast 42 0,10),some (subcubeFast 44 0,8),some (subcubeFast 48 0,10),some (subcubeFast 49 0,8),some (subcubeFast 52 0,8),some (subcubeFast 53 0,7),some (subcubeFast 64 0,12),some (subcubeFast 64 2,9),some (subcubeFast 64 8,9),some (subcubeFast 64 32,7),some (subcubeFast 65 0,10),some (subcubeFast 65 2,6),some (subcubeFast 65 32,6),some (subcubeFast 66 0,10),some (subcubeFast 66 8,8),some (subcubeFast 67 0,7),some (subcubeFast 68 0,10),some (subcubeFast 68 32,6),some (subcubeFast 69 0,7),some (subcubeFast 69 32,5),some (subcubeFast 70 0,7),some (subcubeFast 71 0,4),some (subcubeFast 72 0,10),some (subcubeFast 80 0,10),some (subcubeFast 80 32,6),some (subcubeFast 81 0,7),some (subcubeFast 82 0,7),some (subcubeFast 84 0,7),some (subcubeFast 84 32,5),some (subcubeFast 85 32,4),some (subcubeFast 96 0,11),some (subcubeFast 97 0,8),some (subcubeFast 100 0,8),some (subcubeFast 112 0,8),some (subcubeFast 128 0,12),some (subcubeFast 128 2,9),some (subcubeFast 128 8,9),some (subcubeFast 128 32,7),some (subcubeFast 129 0,10),some (subcubeFast 129 2,6),some (subcubeFast 130 0,10),some (subcubeFast 130 8,8),some (subcubeFast 132 0,10),some (subcubeFast 132 2,6),some (subcubeFast 133 0,7),some (subcubeFast 136 0,10),some (subcubeFast 138 0,8),some (subcubeFast 144 0,10),some (subcubeFast 145 0,7),some (subcubeFast 146 0,7),some (subcubeFast 148 0,7),some (subcubeFast 149 32,4),some (subcubeFast 160 0,11),some (subcubeFast 161 0,8),some (subcubeFast 164 0,8),some (subcubeFast 176 0,8),some (subcubeFast 192 0,9),some (subcubeFast 192 2,8),some (subcubeFast 192 8,8),some (subcubeFast 193 0,6),some (subcubeFast 193 2,5),some (subcubeFast 193 8,5),some (subcubeFast 194 8,7),some (subcubeFast 195 8,4),some (subcubeFast 196 0,6),some (subcubeFast 196 2,5),some (subcubeFast 196 8,5),some (subcubeFast 198 8,4),some (subcubeFast 200 2,7),some (subcubeFast 201 2,4),some (subcubeFast 204 2,4),some (subcubeFast 208 0,6),some (subcubeFast 208 2,5),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,11),some (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555,11),some (0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555,11),some (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555,11),some (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,12),some (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,13),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f,11),some (0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f,11),some (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,11),some (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff,13),some (0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff,11),some (0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff,11),some (0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff,11),some (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff,13),some (0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff,13)]
def Kb:BT (Option (Nat × Nat)):=btOfList 8 Ka
def J:Nat → Option PoolSpec:=lookSpec 1475 #[(1,0,1),(1,0,6),(1,2,4),(1,2,6),(1,7,19),(1,4,20),(1,20,28),(1,11,28),(1,11,19),(1,5,6),(1,1,2),(1,1,6),(1,4,6),(1,1,11),(3,2,18),(1,2,8),(3,4,37),(1,4,59),(1,0,2),(1,0,4),(1,1,7),(1,6,7),(1,9,40),(1,7,9),(1,7,16),(3,3,55),(1,8,20),(1,2,7),(1,4,7),(1,7,10),(1,10,40),(3,4,30),(3,1,40),(1,9,83),(1,11,20),(1,10,77),(1,1,3),(3,7,72),(1,7,38),(1,7,20),(1,4,11),(3,4,73),(3,7,24),(1,8,38),(3,4,34),(1,2,83),(3,19,72),(1,4,77),(3,4,32),(1,0,19),(1,0,28),(1,7,11),(1,5,7),(3,4,78),(3,4,40),(1,7,39),(3,2,72),(3,2,32),(1,2,81),(1,4,82),(3,5,53),(1,40,122),(1,7,122),(1,6,122),(1,8,25),(3,0,72),(1,0,7),(3,0,32),(1,4,86),(3,7,132),(1,0,83),(1,10,96),(3,9,40),(1,10,83),(3,4,142),(1,4,83),(1,19,83),(3,4,96),(1,0,81),(1,9,89),(3,4,35),(0,1,3),(0,3,55),(3,4,100),(1,3,8),(1,3,7),(1,3,16),(1,3,17),(1,14,50),(1,4,85),(3,2,34),(3,2,40),(3,0,57),(3,0,51),(1,7,18),(2,5,40),(3,0,40),(1,2,77),(3,4,117),(1,5,128),(3,2,96),(1,5,83),(1,5,27)] #[0x1c000004000002a0000a0ce800308ac14184150a0c204800605380040612000041d00001b4800005000040400101822a080c10b800404880000400000033a000c09b00040468000042e001010b000001d000004d80020250000003700000940000005c000000c0000003,0x6c000014e0000204800001a4004042e1010128000002680120cd80090612241822a120c10b89060818405066c000006300001ab000a0c24000001200000710e14108000e1438000028e00304090000334860808a8304042e0000005000001200000074003042e0000309,0x68406123420317001018b800004880000234000003d000061200000cf40000654000001f003009100180468000181c0000353063009400000c5c00c02160000c030000015000000400000016000010b00000000000014c00b0250000022a00000270000282400a042e0000a03,0x1120060000001000000980200468000202e0080128000000780141024000141600504170034204801a105c000082e00001520000081000c105c00000360000e40000071b001c08a000e0444000003f1e381140000003000e0434007020b06381140000006800302a40000047,0x194260e0ca1358065099e802a3088015183a00a8c0e000c62b03284ca8194262e00a1336185099400184c680142650000131a005098980284c5c00000b60000021243c115121e085c00f042e0000a52000050d0000285c00000a4000000200000140022405c01102164480128,0x2a7400a13522e4ca1b002651a401426b000a133d2c5098b80284da4b14265400a130018509a900284ca8015180600a8c1a00546058018516819426000ca1352065099b002e0ce898328d258a8c032c5460d162a302c19426d258a8c052c5460e962a3034b15181c58a8c1c,0xd19181c68c8c1c34301ab1a320ce819426286098c1a000060d0030510000028805cb03090000021002e0d58016180600b0c1a00586058000017000018b44c1946e305860e9306514c194269c0ca133e0058611002c3074016181c00b0309065099403284c4c000183a0000c56,0x18be00a136e0074a2000384d1c61426c8006135f0074607003874e801426a670a131700000221b080468000361c0000c0b06509b70032300c019183400c8c0b006460280323074019181a00c8c0e006460e1a32300cd19183468c8c0b3430a2d1a323014d19183a68c8c0d,0x1a000001c000001280406c38000002400d0c560068c9d19284cc0c942654000183a304ca0b9726514800018b8609961f304ca27182650f401328a600c16090000030003e70e801e28805061364005062d000070e8e14269c70a133d2c7060e802c702400028b4000135f,0x2c48000160d0000b0e03284da91212c06890960b00000022242587400328048908356448419d13065001116061201096030084b0d212c502c0212c16010945a0000182804258880212c0a010961d0084b06804258380212c380108356008419d000058740002c1c00b0315,0xb9626345cb140b2e58181930651a80172c4400b961d2e581948000583cb96062a0001603005898d000058680002c168c2025f000002f800058d4a2306e800004600000f2114460da8a2306d2511836e460ca35002c0888016083a0020356460ca2716080c5518328d25820309,0x214265010a1317005c9af930651d13172c3a01316240000b9d002e8d1c0002e8000f02223c1018a8036107400036486c1943e000129d000094680040630002251d00012a01e080c240004a1c0002524000d29d00080c540000092012160e005cb01802e582c00000d60000070,0x28268e014041d003540728284d386a8082a3540409006139d004e343801328e80000d5c309ca20184e10740271a1e0138d2d004ca37002651a8018268e00c041d303420a80004d1c0004a8e0129347003420c001a115800d4a1c606840900509a725284d3800d082a10a1352,0x528801c29410000022b000074e802904b4000005a0060e9d0026a5d000052b84c1045f30a4ea00052743c0293a5a009a96a004d4b48026a5b802926d4082135f00a4ea00052115949d082a0149369527420480284da0b1d0812002135f3a509a7003a105401d081200a136a,0x151f08aca8f960e3e58a05803e510001f2c1c00f84563e509a71f2c1054f96081278a134e3c5820a9e2c102400000ac4c21452305820a982c102400000ee013944000006ab00009cd40004e489ca134e4e3420aa71a1024016082a00b04090000025800001880000e441c29419,0x15a9269c00f934754a412d2a3ea5000002c3c0001f3a000141d0050a439429269ca02291550114848030a500c29082a000042100b14870000012802c1a1e016133e00014a02b5210240004a16014a54000a420c18521024029269ca52934e00a420a8052102401f2c447ca1336,0x132800011160900010ab000084e97212c06017215600b909d2e4258740212c1e0171609425898d21284d49094266c000280d5a1c28700001c90028080a003850f00014070050105402808127c2135f005820f003e580c01e082a00f0409006020a8030102402b5280015a90e,0x80a8e004022200017a10000bd717972c3a202821a2e4ca27002e58540172c1200a236a0000f1d1e288d3801446d20002347008ca350046513802328d200f945a007cb02803ea08800050920140222009c681801a51680271a0a013a83a000141a8000a09002242ac011213a,0x266e00a820b000099b00044ca000226340011317000010580004ca1317268e5c994642e4ca2eb10a0ce98880a8000020420001009000080fcd84282e5c9945800012a100001060000082a000130200c0b07000020d40080a3a0000824005c9a3801014780172c0a004025f,0x32c1200b150e640c1293206085c68226b0001135f1a08994002a4d1c00d2a1c34113521a0898b80000968015269c1011358080898d0000c90003206dc019025a0000a9200640d399032a9c0018415000c20480640cdc0002a801011352080898b8000543800226a45411328,0x26700001d3800009b504044d7c0003a800001d3700749a7000000e0000267a000136800009b496044ca8b02262e58a820b00009a70000553800226c80000a5614089ac0a044d48502262e0011358660c12900640cf400000d001903360058a92162a080590304b00190369,0x330a80cc2834e00cc1b4b43a4ce002a28d4d0e933700a8a3482084d480343a80d0e934e687420ab43a102498404a44c2025f0060ea018267538c1d082a60e840900d0111006810740343a1c01903740001a123268750003206d47420201641012f806475000033a740ce8409,0x36308001b183a6c609a7006c4da5b180812000026200cc2a3800000d4018267000c13370000c2000304d380186a8000c353a30d420a986a10240006a80000353a08089980000d039a020802d01040000c9a203206d1381b4082a0da0409000c20c3308097c03306d40020201,0x704b40139c3a4e709a7271a705538d381200e1d380034e871c3a4d3869c3a12006825a00709a7001a7024e02262e0000075547ca20000001b400000d8000006f0000fab0068082c01f2c1e01a13380000a3500684cdc00028d2000344000d09a700681054034081201b136a,0xc0d3a2a6069d090034e8480002968000707401c1c3a6e5810580007014037387001b825a00dce1d006e5839b9c269c00b020b00006ad00009ce8016382a005025a3808998002c707419638120019c3a640ce2700067025685067400293470a0c9a7000e088838504161c28219,0x271a12000341e0001a0e972c342c0161a1e01c936a00e49b4801ad03800d682a006b409304d3a7184e3454c271a12cc6825a006068a803034242831a2a019825f0a0c684b4044c69c971aace4b9d3a2c34e87161a743c034268e35a1d151ad0e870d687424c130434009825f,0x36812001a83a00c9423804ec9013835074c81a84e007c9af803e58544050416004025a741419d0010143801f2c120000201001418a803074540183a1214196150a0cb04a83a4d380283a74581131a0058e849d044c5c00326d0b43825a000c9b500064da4027269c0138d15,0x187074000271e0001bab006e60e9b98269c00037380001ba00076dce9db7269c01d961d00dcb018000dce80006e6e01b934e0060b0a80305874000708001c283a000140780009d000000e6a000007200001b400504d39a82262e6098228304c118006808040340400001b415,0x3d0612f590300005461400640c5c0320600c818c5200c819500004c0000c26a45461328003099400004c4c000262e7cb131f74201ab0000d0d403c2e8001e160f00d01160000d03c034043201a0210680899434044c5c03630126098213304c10b98260819b182c120003847,0x162654000132a265461400004d6000018a424195360000b0300100da403206b000000580000b0000640d48b15184858a8c28640cb0bb20658a80151848c818c642c546013e640d39eb206b0f59033d7ac819bbd640d49eb2066cf59161f640cb18007ac87deb2062e01eb210,0xc133a540098c5f304ce8b8010309000066be0198c5f6614b0f802c3005985067a0000c6000cc1a980003188016184800e933d0000e9e802c7400b1d262e0001353007498b80004d48b96260c00b9352005c99b0000587c415184800b93582e5898b802e58400132c5400b1317,0x16185068c8c027ac81b7407ac86a03d641701e8303000001cbe640d91eb206d200000557ac81aa3f7ac91dfbd6480fde833a00586013d640d4de96181c01eb21a7ac8189807ac82c03d0606019032800c8189800030080001850cc2832a660c629330a0c5cc133a7a5c99d36,0xc132c00609962a304cb0b96184ca000018c8000353d00009b21826d4f4c136a2e6098c2800d499e806a3068035262e01a8c0b00d46018001049000000dc004833d0064612003230a0000002800d0c520068c9b1a323090d19185000d190632c819819640ca848304502418213,0x14343a70a1a134708089a9a8684cdd4343a6e00013541a7498b801a4d4800d262e6c20128406c20b9b08044c99918500001301346499500004db8c8c26505cb1328000003e972c4c4db18262e00c1300006098980304c5c018260c202821f62201ab36304cf4016181e00c133d,0x466e0119d4e1a10e8a80008da46843a1200f2347005cea01e1a1054f230a8e34203563c711a38038107401e1a5a00f0d0f00511ba00288db8f0d081200b9338005c99b97263548b96264c5cb131f0000ea1172675399852c4c0069d0f2c34e8a961a742420226a8a1a1338,0xb961a1308b934e005c6ab00844da804226d308b93362e586818000251c00906d4000160100241a716120c5400906d25848309120c129002c34040161a0060b0d153058684802c3438b0d262ea1a134e3ea09a3801075000080a810d19d4e845d1a3802e74e800046d40002338,0x405065200403568a5c99b422e4d1e118268e20283031014119000015080002ec00001762000068080003400c131a2e013a34e2e4c6ae802e3568b931ac800ba34e8820111422e8d3804246d40212369406c6878000811069b082e5c98d5800011a700469538017269c5cb0d15,0x904b4004821f0024108000104d400082840004149002419b800001e000806d00138d01009c680004e344c0271a0c9c69317549c68714064da00000a920001f4b0000fb11f0a4d1ca0326d450193693e58a14271a4ca00182603104054700201b5080a0d38405062a2028309,0xb3206551a03d1d8d01e87407ac97e03d64b501e835680f590fc07ac84203d061301903307ac81ba3e7a5875f3d2c1d01e961d7ac81a3407a5839eb206d400016027ac818a00425808000001101903647ac8b0d3d64582c03d06740048226100c12c0806099000904be0048338,0x2117468d08ba33d006c2150a36105c51b080c00504560001294230808c000a082a8c2022a00289a900144c5c00000d4024961d0124b110000584e42242ad211213a9088b04804258d400042a400021360084b1416640c5e3a12c5001096248e84b00804258790b206a48590336,0x1121266c88b131700000164d42583804c427531096289884b074c2c4c5e6a12c17310935298589954a42580c04b42ac025a13a9684b07009658265212c1d1cb132a8e84b05c7424d4a3a1266d1cb131742589940000d12d51f28b40003409000052e1826285c017468c00ba33d,0x288906ac000005e010cb00001294784a5a43c241161fa2241a7002e4d90017708000bb83a00000320000e10a81f26bf40f934700dd1a7372c4c5c0502c3b3db934e6e5899400009d0800000ae000003b9c890ab4e4484ea7222c57390960e01389804e44582511626548909352,0x154a480005600ac5529251120c54009044e004d51da22418480010c000433800012d224862410f800095240004a9600025024610109a3080819184042e924935fa890b07080a089a20804b4000085c845c9a9422e582c0092c67444833d0000030d33230904822c4c0002552,0x433a9c0219c4e007020a803810240008680002025286101144308085c00004a40218228010c10d0086085c05a26d368b93640000bad00005d58043041602182220000022800025700002e920048219006c2038036105ed1726b000b935d016529200b05490057128e0002535,0x5c869c000284e010dc200000a11c027869d0cb021a865810bc32c082c00004c8000001e86e01180014094a18a042e00000760000039c30a0d1ada8083a021a83800001b50086a0de1a80444021a84e00021a7430808c2185069c000434b861419e8086150000404be0219d40,0xbad2000494900f0b073404105da020850d420217007c22f803e513805d4e6c00104520058e878004117c0343a9cd01041a3a1010b962a0868b15045000b0217002812c0000096000404b0002021a005410d0000086ad85868f6c2025f001c29687860888000b8ac0005c3a,0x34043401a021300d010b8068081803404500005e4e0002f35000179a4385045970b022888202a0002e9ce8016043401a8217702810300103890027389d746825a2c7010d1638085cb9304c828e02170000e270038086801c042e7cb04263e5820faa3e513a23404440005d6a,0xbe02c325f01610725c9a3b92e4d7c000c0b800060420001a270000008c038142e00035170000b0b8001258003c2eb4f0b962c785cb0cbc2e58400172c32e4b934e017c10300007d080003eb800f9756007cb9d1f2c504cf96280c5c9b44e005da14802ed074017682a00bb409,0x662c2e00000164484b1600ca4da802242b401121404484b0c808e58425212c3400013148e84b0d008e8548047426c023961701930a900c984db2612c2e032160300031b500018da40632c1d8a4934e0184b0d00c2582c0612c50000004f00000328050d11c028689c00b962e,0x5e6400033b500019da406642a40332136]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kc:Slice E A (0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff) 13:=mappedSlice (f:=identifyRow 0 0 7 5) (R:=ao) (G:=ac) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) fk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kd:Slice E A (0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff) 13:=mappedSlice (f:=identifyRow 0 0 6 5) (R:=ao) (G:=ac) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) fk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ke:Slice E A (0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff) 11:=mappedSlice (f:=identifyRow 0 0 7 4) (R:=cG) (G:=cH) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kf:Slice E A (0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff) 11:=mappedSlice (f:=identifyRow 0 0 6 4) (R:=oz) (G:=oA) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) FN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kg:Slice E A (0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff) 11:=mappedSlice (f:=identifyRow 0 0 5 4) (R:=fV) (G:=fW) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) oB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kh:Slice E A (0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff) 13:=mappedSlice (f:=identifyRow 0 0 5 3) (R:=gf) (G:=gg) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) oO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ki:Slice E A (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f) 11:=mappedSlice (f:=identifyRow 0 0 7 2) (R:=oP) (G:=oQ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Gn
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kj:Slice E A (0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f) 11:=mappedSlice (f:=identifyRow 0 0 6 2) (R:=oR) (G:=oS) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Go
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kk:Slice E A (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f) 11:=mappedSlice (f:=identifyRow 0 0 4 2) (R:=dI) (G:=dJ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) gr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kl:Slice E A (0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333) 13:=mappedSlice (f:=identifyRow 0 0 5 1) (R:=pE) (G:=pF) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Hr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Km:Slice E A (0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333) 12:=mappedSlice (f:=identifyRow 0 0 4 1) (R:=pG) (G:=pH) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Hs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kn:Slice E A (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555) 11:=mappedSlice (f:=identifyRow 0 0 7 0) (R:=pI) (G:=pJ) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Ht
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ko:Slice E A (0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555) 11:=mappedSlice (f:=identifyRow 0 0 5 0) (R:=pK) (G:=pL) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Hu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kp:Slice E A (0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555) 11:=mappedSlice (f:=identifyRow 0 0 4 0) (R:=pM) (G:=pN) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Hv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kq:Slice E A (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 11:=mappedSlice (f:=identifyRow 0 0 2 0) (R:=pO) (G:=pP) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) Hw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kr:Slice E A (subcubeFast 208 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=fl) (qGoal:=fm) (by decide +kernel) nv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ks:Slice E A (subcubeFast 208 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=fn) (qGoal:=fo) (by decide +kernel) nw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kt:Slice E A (subcubeFast 204 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=gt) (qGoal:=gu) (by decide +kernel) pQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ku:Slice E A (subcubeFast 201 2) 4:=slice_fast_direct (zDead:=0) (qRoots:=gv) (qGoal:=gw) (by decide +kernel) pR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kv:Slice E A (subcubeFast 200 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=gx) (qGoal:=gy) (by decide +kernel) dK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kw:Slice E A (subcubeFast 198 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=gt) (qGoal:=gu) (by decide +kernel) pQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kx:Slice E A (subcubeFast 196 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=pS) (qGoal:=pT) (by decide +kernel) Hx
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ky:Slice E A (subcubeFast 196 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=pU) (qGoal:=pV) (by decide +kernel) Hy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Kz:Slice E A (subcubeFast 196 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=pW) (qGoal:=pX) (by decide +kernel) Hz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KA:Slice E A (subcubeFast 195 8) 4:=slice_fast_direct (zDead:=0) (qRoots:=gv) (qGoal:=gw) (by decide +kernel) pR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KB:Slice E A (subcubeFast 194 8) 7:=slice_fast_direct (zDead:=0) (qRoots:=gx) (qGoal:=gy) (by decide +kernel) dK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KC:Slice E A (subcubeFast 193 8) 5:=slice_fast_direct (zDead:=0) (qRoots:=pY) (qGoal:=pZ) (by decide +kernel) HA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KD:Slice E A (subcubeFast 193 2) 5:=slice_fast_direct (zDead:=0) (qRoots:=qa) (qGoal:=qb) (by decide +kernel) HB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KE:Slice E A (subcubeFast 193 0) 6:=slice_fast_direct (zDead:=0) (qRoots:=qc) (qGoal:=qd) (by decide +kernel) HC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KF:Slice E A (subcubeFast 192 8) 8:=slice_fast_direct (zDead:=0) (qRoots:=qe) (qGoal:=qf) (by decide +kernel) HD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KG:Slice E A (subcubeFast 192 2) 8:=slice_fast_direct (zDead:=0) (qRoots:=qg) (qGoal:=qh) (by decide +kernel) HE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KH:Slice E A (subcubeFast 192 0) 9:=slice_fast_direct (zDead:=0) (qRoots:=qi) (qGoal:=qj) (by decide +kernel) HF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KI:Slice E A (subcubeFast 176 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=aJ) (qGoal:=ap) (by decide +kernel) bK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KJ:Slice E A (subcubeFast 164 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dt) (qGoal:=du) (by decide +kernel) ew
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KK:Slice E A (subcubeFast 161 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dv) (qGoal:=dw) (by decide +kernel) ex
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KL:Slice E A (subcubeFast 160 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=aq) (qGoal:=B) (by decide +kernel) dy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KM:Slice E A (subcubeFast 149 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=cf) (qGoal:=cg) (by decide +kernel) ch
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KN:Slice E A (subcubeFast 148 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=aN) (qGoal:=az) (by decide +kernel) cj
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KO:Slice E A (subcubeFast 146 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fO) (qGoal:=fP) (by decide +kernel) ob
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KP:Slice E A (subcubeFast 145 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=fQ) (qGoal:=fR) (by decide +kernel) oe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KQ:Slice E A (subcubeFast 144 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aA) (qGoal:=af) (by decide +kernel) cp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KR:Slice E A (subcubeFast 138 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=qk) (qGoal:=ql) (by decide +kernel) HG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KS:Slice E A (subcubeFast 136 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bM) (qGoal:=bg) (by decide +kernel) dL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KT:Slice E A (subcubeFast 133 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=qt) (qGoal:=qu) (by decide +kernel) HY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KU:Slice E A (subcubeFast 132 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=qv) (qGoal:=qw) (by decide +kernel) HZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KV:Slice E A (subcubeFast 132 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qx) (qGoal:=qy) (by decide +kernel) Ia
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KW:Slice E A (subcubeFast 130 8) 8:=slice_fast_direct (zDead:=0) (qRoots:=qz) (qGoal:=qA) (by decide +kernel) Ib
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KX:Slice E A (subcubeFast 130 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qB) (qGoal:=qC) (by decide +kernel) Ic
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KY:Slice E A (subcubeFast 129 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=qD) (qGoal:=qE) (by decide +kernel) Id
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma KZ:Slice E A (subcubeFast 129 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qF) (qGoal:=qG) (by decide +kernel) Ie
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma La:Slice E A (subcubeFast 128 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=qH) (qGoal:=qI) (by decide +kernel) If
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lb:Slice E A (subcubeFast 128 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=cb) (qGoal:=cc) (by decide +kernel) cr
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lc:Slice E A (subcubeFast 128 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=qJ) (qGoal:=qK) (by decide +kernel) Ig
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ld:Slice E A (subcubeFast 128 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=gE) (qGoal:=gF) (by decide +kernel) qM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Le:Slice E A (subcubeFast 112 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dB) (qGoal:=dC) (by decide +kernel) eF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lf:Slice E A (subcubeFast 100 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eG) (qGoal:=eH) (by decide +kernel) mv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lg:Slice E A (subcubeFast 97 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eI) (qGoal:=eJ) (by decide +kernel) my
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lh:Slice E A (subcubeFast 96 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=eK) (qGoal:=eL) (by decide +kernel) mB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Li:Slice E A (subcubeFast 85 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=dz) (qGoal:=dA) (by decide +kernel) eE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lj:Slice E A (subcubeFast 84 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=qN) (qGoal:=qO) (by decide +kernel) Ih
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lk:Slice E A (subcubeFast 84 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=gh) (qGoal:=gi) (by decide +kernel) pd
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ll:Slice E A (subcubeFast 82 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=qP) (qGoal:=qQ) (by decide +kernel) Ii
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lm:Slice E A (subcubeFast 81 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=qR) (qGoal:=qS) (by decide +kernel) Ij
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ln:Slice E A (subcubeFast 80 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=qT) (qGoal:=qU) (by decide +kernel) Ik
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lo:Slice E A (subcubeFast 80 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gG) (qGoal:=gH) (by decide +kernel) qV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lp:Slice E A (subcubeFast 72 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=qW) (qGoal:=qX) (by decide +kernel) Il
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lq:Slice E A (subcubeFast 71 0) 4:=slice_fast_direct (zDead:=0) (qRoots:=qY) (qGoal:=qZ) (by decide +kernel) Im
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lr:Slice E A (subcubeFast 70 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=ra) (qGoal:=rb) (by decide +kernel) In
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ls:Slice E A (subcubeFast 69 32) 5:=slice_fast_direct (zDead:=0) (qRoots:=rc) (qGoal:=rd) (by decide +kernel) Io
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lt:Slice E A (subcubeFast 69 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=re) (qGoal:=rf) (by decide +kernel) Ip
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lu:Slice E A (subcubeFast 68 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=rg) (qGoal:=rh) (by decide +kernel) Iq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lv:Slice E A (subcubeFast 68 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=ri) (qGoal:=rj) (by decide +kernel) Ir
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lw:Slice E A (subcubeFast 67 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rk) (qGoal:=rl) (by decide +kernel) Is
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lx:Slice E A (subcubeFast 66 8) 8:=slice_fast_direct (zDead:=0) (qRoots:=rm) (qGoal:=ro) (by decide +kernel) It
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ly:Slice E A (subcubeFast 66 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rp) (qGoal:=rq) (by decide +kernel) Iu
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Lz:Slice E A (subcubeFast 65 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=rr) (qGoal:=rt) (by decide +kernel) Iv
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LA:Slice E A (subcubeFast 65 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=ru) (qGoal:=rv) (by decide +kernel) Iw
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LB:Slice E A (subcubeFast 65 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=rx) (qGoal:=ry) (by decide +kernel) Ix
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LC:Slice E A (subcubeFast 64 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=rz) (qGoal:=rA) (by decide +kernel) Iy
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LD:Slice E A (subcubeFast 64 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=rB) (qGoal:=rC) (by decide +kernel) Iz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LE:Slice E A (subcubeFast 64 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=rD) (qGoal:=rE) (by decide +kernel) IA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LF:Slice E A (subcubeFast 64 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=rF) (qGoal:=rG) (by decide +kernel) IB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LG:Slice E A (subcubeFast 53 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=cO) (qGoal:=cP) (by decide +kernel) cC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LH:Slice E A (subcubeFast 52 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=cQ) (qGoal:=cR) (by decide +kernel) dD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LI:Slice E A (subcubeFast 49 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=dE) (qGoal:=dF) (by decide +kernel) eM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LJ:Slice E A (subcubeFast 48 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bo) (qGoal:=aK) (by decide +kernel) cD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LK:Slice E A (subcubeFast 44 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=rH) (qGoal:=rI) (by decide +kernel) IC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LL:Slice E A (subcubeFast 42 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aD) (qGoal:=Z) (by decide +kernel) bF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LM:Slice E A (subcubeFast 40 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=dG) (qGoal:=dH) (by decide +kernel) eS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LN:Slice E A (subcubeFast 38 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eV) (qGoal:=eW) (by decide +kernel) mM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LO:Slice E A (subcubeFast 37 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=eX) (qGoal:=eY) (by decide +kernel) mN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LP:Slice E A (subcubeFast 36 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=eZ) (qGoal:=fa) (by decide +kernel) mO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LQ:Slice E A (subcubeFast 35 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=fb) (qGoal:=fc) (by decide +kernel) mP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LR:Slice E A (subcubeFast 34 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=fd) (qGoal:=ff) (by decide +kernel) mQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LS:Slice E A (subcubeFast 33 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=fg) (qGoal:=fh) (by decide +kernel) mR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LT:Slice E A (subcubeFast 32 0) 13:=slice_fast_direct (zDead:=0) (qRoots:=ao) (qGoal:=ac) (by decide +kernel) fk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LU:Slice E A (subcubeFast 26 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=rJ) (qGoal:=rK) (by decide +kernel) ID
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LV:Slice E A (subcubeFast 24 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=bC) (qGoal:=aO) (by decide +kernel) cz
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LW:Slice E A (subcubeFast 23 32) 4:=slice_fast_direct (zDead:=0) (qRoots:=gj) (qGoal:=gk) (by decide +kernel) pi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LX:Slice E A (subcubeFast 21 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=cO) (qGoal:=cP) (by decide +kernel) cC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LY:Slice E A (subcubeFast 20 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=bZ) (qGoal:=ca) (by decide +kernel) cq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma LZ:Slice E A (subcubeFast 20 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=aH) (qGoal:=ag) (by decide +kernel) cX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ma:Slice E A (subcubeFast 19 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=rQ) (qGoal:=rR) (by decide +kernel) IV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mb:Slice E A (subcubeFast 18 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=rS) (qGoal:=rT) (by decide +kernel) IW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mc:Slice E A (subcubeFast 18 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gN) (qGoal:=gO) (by decide +kernel) rU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Md:Slice E A (subcubeFast 17 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=rV) (qGoal:=rW) (by decide +kernel) IX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Me:Slice E A (subcubeFast 17 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=gP) (qGoal:=gQ) (by decide +kernel) rX
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mf:Slice E A (subcubeFast 16 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=rY) (qGoal:=rZ) (by decide +kernel) IY
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mg:Slice E A (subcubeFast 16 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=sa) (qGoal:=sb) (by decide +kernel) IZ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mh:Slice E A (subcubeFast 16 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=aY) (qGoal:=aI) (by decide +kernel) gW
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mi:Slice E A (subcubeFast 12 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=so) (qGoal:=sp) (by decide +kernel) JA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mj:Slice E A (subcubeFast 11 0) 8:=slice_fast_direct (zDead:=0) (qRoots:=sq) (qGoal:=sr) (by decide +kernel) JB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mk:Slice E A (subcubeFast 10 0) 11:=slice_fast_direct (zDead:=0) (qRoots:=st) (qGoal:=su) (by decide +kernel) JC
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ml:Slice E A (subcubeFast 9 2) 6:=slice_fast_direct (zDead:=0) (qRoots:=sv) (qGoal:=sx) (by decide +kernel) JD
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mm:Slice E A (subcubeFast 9 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sy) (qGoal:=sz) (by decide +kernel) JE
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mn:Slice E A (subcubeFast 8 2) 9:=slice_fast_direct (zDead:=0) (qRoots:=gX) (qGoal:=gY) (by decide +kernel) sA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mo:Slice E A (subcubeFast 8 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=gZ) (qGoal:=hA) (by decide +kernel) sB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mp:Slice E A (subcubeFast 7 0) 7:=slice_fast_direct (zDead:=0) (qRoots:=sC) (qGoal:=sD) (by decide +kernel) JF
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mq:Slice E A (subcubeFast 6 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=sE) (qGoal:=sF) (by decide +kernel) JG
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mr:Slice E A (subcubeFast 6 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sG) (qGoal:=sH) (by decide +kernel) JH
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ms:Slice E A (subcubeFast 5 32) 8:=slice_fast_direct (zDead:=0) (qRoots:=sI) (qGoal:=sJ) (by decide +kernel) JI
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mt:Slice E A (subcubeFast 5 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sK) (qGoal:=sL) (by decide +kernel) JJ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mu:Slice E A (subcubeFast 4 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=sM) (qGoal:=sN) (by decide +kernel) JK
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mv:Slice E A (subcubeFast 4 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=sO) (qGoal:=sP) (by decide +kernel) JL
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mw:Slice E A (subcubeFast 4 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=sQ) (qGoal:=sR) (by decide +kernel) JM
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mx:Slice E A (subcubeFast 3 32) 6:=slice_fast_direct (zDead:=0) (qRoots:=sS) (qGoal:=sT) (by decide +kernel) JN
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma My:Slice E A (subcubeFast 3 0) 10:=slice_fast_direct (zDead:=0) (qRoots:=sU) (qGoal:=sV) (by decide +kernel) JO
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Mz:Slice E A (subcubeFast 2 32) 7:=slice_fast_direct (zDead:=0) (qRoots:=sW) (qGoal:=sX) (by decide +kernel) JP
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MA:Slice E A (subcubeFast 2 8) 9:=slice_fast_direct (zDead:=0) (qRoots:=gX) (qGoal:=gY) (by decide +kernel) sA
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MB:Slice E A (subcubeFast 2 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=sY) (qGoal:=sZ) (by decide +kernel) JQ
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MC:Slice E A (subcubeFast 1 32) 9:=slice_fast_direct (zDead:=0) (qRoots:=ta) (qGoal:=tb) (by decide +kernel) JR
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MD:Slice E A (subcubeFast 1 2) 7:=slice_fast_direct (zDead:=0) (qRoots:=tc) (qGoal:=td) (by decide +kernel) JS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ME:Slice E A (subcubeFast 1 0) 12:=slice_fast_direct (zDead:=0) (qRoots:=te) (qGoal:=tf) (by decide +kernel) JT
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MF:Slice E A (subcubeFast 0 32) 10:=slice_fast_direct (zDead:=0) (qRoots:=dM) (qGoal:=dN) (by decide +kernel) hB
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MG:Slice E A (subcubeFast 0 8) 10:=slice_fast_direct (zDead:=0) (qRoots:=tg) (qGoal:=th) (by decide +kernel) JU
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MH:Slice E A (subcubeFast 0 2) 10:=slice_fast_direct (zDead:=0) (qRoots:=ti) (qGoal:=tj) (by decide +kernel) JV
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma K:btAll (fun o => ∀ p, o = some p → Slice E A p.1 p.2) Kb:=btAll_ofList (P:=fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice E A p.1 p.2) (forall_cons (someSlice MH) (forall_cons (someSlice MG) (forall_cons (someSlice MF) (forall_cons (someSlice ME) (forall_cons (someSlice MD) (forall_cons (someSlice MC) (forall_cons (someSlice MB) (forall_cons (someSlice MA) (forall_cons (someSlice Mz) (forall_cons (someSlice My) (forall_cons (someSlice Mx) (forall_cons (someSlice Mw) (forall_cons (someSlice Mv) (forall_cons (someSlice Mu) (forall_cons (someSlice Mt) (forall_cons (someSlice Ms) (forall_cons (someSlice Mr) (forall_cons (someSlice Mq) (forall_cons (someSlice Mp) (forall_cons (someSlice Mo) (forall_cons (someSlice Mn) (forall_cons (someSlice Mm) (forall_cons (someSlice Ml) (forall_cons (someSlice Mk) (forall_cons (someSlice Mj) (forall_cons (someSlice Mi) (forall_cons (someSlice Mh) (forall_cons (someSlice Mg) (forall_cons (someSlice Mf) (forall_cons (someSlice Me) (forall_cons (someSlice Md) (forall_cons (someSlice Mc) (forall_cons (someSlice Mb) (forall_cons (someSlice Ma) (forall_cons (someSlice LZ) (forall_cons (someSlice LY) (forall_cons (someSlice LX) (forall_cons (someSlice LW) (forall_cons (someSlice LV) (forall_cons (someSlice LU) (forall_cons (someSlice LT) (forall_cons (someSlice LS) (forall_cons (someSlice LR) (forall_cons (someSlice LQ) (forall_cons (someSlice LP) (forall_cons (someSlice LO) (forall_cons (someSlice LN) (forall_cons (someSlice LM) (forall_cons (someSlice LL) (forall_cons (someSlice LK) (forall_cons (someSlice LJ) (forall_cons (someSlice LI) (forall_cons (someSlice LH) (forall_cons (someSlice LG) (forall_cons (someSlice LF) (forall_cons (someSlice LE) (forall_cons (someSlice LD) (forall_cons (someSlice LC) (forall_cons (someSlice LB) (forall_cons (someSlice LA) (forall_cons (someSlice Lz) (forall_cons (someSlice Ly) (forall_cons (someSlice Lx) (forall_cons (someSlice Lw) (forall_cons (someSlice Lv) (forall_cons (someSlice Lu) (forall_cons (someSlice Lt) (forall_cons (someSlice Ls) (forall_cons (someSlice Lr) (forall_cons (someSlice Lq) (forall_cons (someSlice Lp) (forall_cons (someSlice Lo) (forall_cons (someSlice Ln) (forall_cons (someSlice Lm) (forall_cons (someSlice Ll) (forall_cons (someSlice Lk) (forall_cons (someSlice Lj) (forall_cons (someSlice Li) (forall_cons (someSlice Lh) (forall_cons (someSlice Lg) (forall_cons (someSlice Lf) (forall_cons (someSlice Le) (forall_cons (someSlice Ld) (forall_cons (someSlice Lc) (forall_cons (someSlice Lb) (forall_cons (someSlice La) (forall_cons (someSlice KZ) (forall_cons (someSlice KY) (forall_cons (someSlice KX) (forall_cons (someSlice KW) (forall_cons (someSlice KV) (forall_cons (someSlice KU) (forall_cons (someSlice KT) (forall_cons (someSlice KS) (forall_cons (someSlice KR) (forall_cons (someSlice KQ) (forall_cons (someSlice KP) (forall_cons (someSlice KO) (forall_cons (someSlice KN) (forall_cons (someSlice KM) (forall_cons (someSlice KL) (forall_cons (someSlice KK) (forall_cons (someSlice KJ) (forall_cons (someSlice KI) (forall_cons (someSlice KH) (forall_cons (someSlice KG) (forall_cons (someSlice KF) (forall_cons (someSlice KE) (forall_cons (someSlice KD) (forall_cons (someSlice KC) (forall_cons (someSlice KB) (forall_cons (someSlice KA) (forall_cons (someSlice Kz) (forall_cons (someSlice Ky) (forall_cons (someSlice Kx) (forall_cons (someSlice Kw) (forall_cons (someSlice Kv) (forall_cons (someSlice Ku) (forall_cons (someSlice Kt) (forall_cons (someSlice Ks) (forall_cons (someSlice Kr) (forall_cons (someSlice Kq) (forall_cons (someSlice Kp) (forall_cons (someSlice Ko) (forall_cons (someSlice Kn) (forall_cons (someSlice Km) (forall_cons (someSlice Kl) (forall_cons (someSlice Kk) (forall_cons (someSlice Kj) (forall_cons (someSlice Ki) (forall_cons (someSlice Kh) (forall_cons (someSlice Kg) (forall_cons (someSlice Kf) (forall_cons (someSlice Ke) (forall_cons (someSlice Kd) (forall_cons (someSlice Kc) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def MI:BT (List (List Nat)):=BT.empty
lemma MJ:btAll (fun bk => ∀ xs ∈ bk, Impossible A (6 - 1) xs.toFinset) MI:=trivial
def tm:List NodeSpec:=readDeltaNodes 2 (unpackWords 7 [(20,0xd8087161204200001f30248240820400007)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MK:∀ ns ∈ tm, Impossible A 6 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I MJ (by decide +kernel)
def ML:BT (List (List Nat)):=refBuckets C [tm] #[0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
set_option maxRecDepth 20000 in
lemma hE:btAll (fun bk => ∀ xs ∈ bk, Impossible A 6 xs.toFinset) ML:=refBuckets_all (forall_cons MK (fun _ h => (List.not_mem_nil h).elim))
def tn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa3be4376379709401501ba944a441515fd486d44e353054),(64,0x4880a1b7e3d4c7b37a44151dab299f33244051786ca52240),(31,0xed5e1ea19922028d6a7a866)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MM:∀ ns ∈ tn, Impossible A 7 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I hE (by decide +kernel)
def tp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x14369e7288d3b244250c34fa7f4910143cf3cf50cc91054),(64,0x5394482a033ebd2c762a148951636424a4005153e9e74491),(34,0x1f972b12ca728905433ef94e96)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MN:∀ ns ∈ tp, Impossible A 7 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I hE (by decide +kernel)
def tq:List NodeSpec:=readDeltaNodes 1 (varNats 2 (unpackWords 3 [(24,0x6c92278dc4f24c254)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MO:∀ ns ∈ tq, Impossible A 7 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I hE (by decide +kernel)
def MP:BT (List (List Nat)):=refBuckets C [tn,tp,tq] #[0,0,0,6,0,16,0,36865,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,13,0,0,0,0,2,0,0,12,0,0,0,0,0,0,0,4,8,0,0,10,0,0,0,61447,0,0,0,0,5,17,0,0,0,0,14,0,11]
set_option maxRecDepth 20000 in
lemma aF:btAll (fun bk => ∀ xs ∈ bk, Impossible A 7 xs.toFinset) MP:=refBuckets_all (forall_cons MM (forall_cons MN (forall_cons MO (fun _ h => (List.not_mem_nil h).elim))))
def tr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86f271a4944aad024924956736a2713136aa8ae651249015),(64,0x20aa15fd486d6734912552e1b55fd5c6d671a91062817914),(58,0xa49cf8cb55289308354327673252202ab48ed673252)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MQ:∀ ns ∈ tr, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def ts:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x771b0f64944055fd95a6c3d92510555bc52986c3cc251055),(64,0x29105572d3a433d54a252212a4924aff9d219eaac9488514),(64,0xb2f76aac94882a1262ae67f557aae3c91071e6691d324559),(1,1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MR:∀ ns ∈ ts, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tt:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9a3b4d31929109533dae470d3c94882a9b3e365591291054),(64,0xcbaac94882a99ed7215dc25220aaafe64c698c94882aab23),(58,0x1124a37da6d56ac6a441e7af22d0cc718d2441555fd6)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MS:∀ ns ∈ tt, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x35cb8db8dd8da65362c6a441ea124967f37daee2df48850f),(64,0x20a85f3a636c7f7323b5749220d50cf2996ae912882a12e6),(64,0x2882a9dff76ae912882a19e536d58a49105433ca65ab1492),(16,64711973462993)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MT:∀ ns ∈ tu, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5318ea2510553e786ce71a912882a998efabb4e352251095),(64,0x4883154a786cfcc94c5d24886a2de3eae5d22510553ada6c),(64,0x49220c555b9c8feeb3dd749221a8b73a636c7f732394c5d2),(23,0x74cac723fbac73b57)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MU:∀ ns ∈ tv, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a8074a5124a24aa75d4e90f3752894884a8375289251055),(64,0xa6f875851289212ae6a6f8f1b7325124254cd79b73249248),(56,0x254b7987656325221aa7fc6b932c7656325221aae6)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MV:∀ ns ∈ tw, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x36b25220c54dba9ae4cac7cdac94886aaf21b9fcc9449055),(64,0x3ceaac67188944155452e87e7cdac94884aba6dd4d72658d),(64,0x5424b9e2b719b77f18d731220e50935c8acbcec637d220d),(17,557740802679953)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MW:∀ ns ∈ tx, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def ty:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x1184b2da28b4db41d439622104181bac43b22222101181aa94c634211210119),(64,0x3197c3cd7e6e91f3f2222210418126df58d5c1b41e422104186dd61f3925121),(40,0x7ae1f4db2291c2422103181a16ce1f182f222221)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MX:∀ ns ∈ ty, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x44150fdf194de932882a12b6ca7374524861d0cc62488394),(64,0x263bb5366379709409aa1dbd369cb43c924150fdf2a7f499),(64,0x38de5724a00c55dfe28f95c92802aab273e72a944a00aa11),(14,657358301630)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MY:∀ ns ∈ tz, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20154925192bbbf37e3a3849201ea38f598e329eba248095),(64,0x4543e654a249002a1ef79bb1d1564920955df31bf1d15649),(64,0xf21faaa512480550eef8cf5c85124825521eff298d94a448),(2,29)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma MZ:∀ ns ∈ tA, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xde3cb9b4ca7ce76e6ef95463c62443ca39f3b4f849448055),(64,0xf29fe9ae4cff533e664492628bfb4e95f33224805424924d),(64,0xcf99912402a2fed3ad7de311241517f69d2bef188920a80e),(44,0x4495e7c6bf9fd56a8d50cc910a286cd54)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Na:∀ ns ∈ tB, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tC:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x7182a2111131801fff2c74a7182a21111219017ff3ae4ba63b59732d22211618),(64,0x1ec52d83a1e61182a21111719028a538a7f4a7182a2111131944cf18de38f1c9),(64,0x195c8112ff18886b192c22221051841f969d3a397182822111131903e19b91dc),(20,0x159a6d1a4a3f2112112)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nb:∀ ns ∈ tC, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x201541fbc769a6d50fe9124a54f3fd72f7f9d943fa4490d5),(64,0xbaa879d122486a826cd9dabc3ce88944a555db9b94c7f489),(64,0xb2736a879d122492a876d52c72f3943ce89124b54a93b979),(34,0x1c9799b77f990cc7f489212a0c)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nc:∀ ns ∈ tD, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x55db54b1cbdeaa450fe912435493f99b77698b43fa2512d5),(64,0x554d23e6557928920aaa691f332b89251055333a75249440),(64,0x8894884aabec5ef33e8647d4a894886a9fbf3fa87544a441),(15,7529059469077)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nd:∀ ns ∈ tE, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20254d87ce5124801553486658f8492882a9cbabc9449015),(64,0x33c2892402ab9f993bbbd5352892406a397bdee7299e1449),(46,0x1df21fb944920150dc7ce512480157758fd)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nf:∀ ns ∈ tF, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x241554d89249200549fb9bb12492404abdef27ec51248055),(64,0x42a66b71be2f8924920aa6cca124940054cd7c721bb1249),(38,0x17d5ff31e8dec92404a85b390924a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ng:∀ ns ∈ tG, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xeed5ba8746510d453487750e8c924150c9b9ea9bd9248055),(64,0x2882aa9a43a287464920a8e5eed594aa1d194415548758e5),(57,0x3da4335a4dd5124a212a14d5124a20154cb4c52d449)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nh:∀ ns ∈ tH, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a7eee53752492482a9fb93af2512402a8536449288055),(64,0x20155dfaac6f6a925005504cfb44b1d95249252aac849249),(45,0x3358fcdda594e4924a54cfb633aca7249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ni:∀ ns ∈ tI, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tJ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2802aa86ce66b71fd2ca724921aa604fcb95cb2951448495),(64,0x4490157f9dd5c492880a9b56c64a492880abbf552ac6f709),(46,0x15332b8925101554caaf25124054e362bc9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nj:∀ ns ∈ tJ, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a4186bf092514153f73bf57928920154ef95e49448015),(64,0xca12512953f7325579289201556caf24a2400a9f22bc9289),(44,0x261b24a8fa635094803150f6fcdb3278d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nk:∀ ns ∈ tK, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x90dd9e3a124a20aa66dcda6ce74249441557c77a49448015),(64,0xa0ef3974dbf3931cb1a7524a24d554d21b1f3a128920aaa6),(64,0x2510540a6915561d0925125579db54d5c98e7d4329449062),(15,7480539534670)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nl:∀ ns ∈ tL, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd3e26f86cd973cd331c4a24c54a7f686cd9770cc71288314),(64,0x94eaab28944154fdf154fe792482a1fbe265379e4920a86b),(64,0xbcf7512886a9b377b2aed7512882ab97e361d553112882a9),(19,0xe7fddd0d9baf4d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nm:∀ ns ∈ tM, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x212a6cf4d9f998f70a251095337c61b3737f331eea2510d5),(64,0x3192482a1b3c8ed36198f7512884a9b3f367e6ce663dd44a),(64,0x3192482a1dbd3757cea792482a1d8e87c3192482a1d8ee7c),(10,349322932)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nn:∀ ns ∈ tN, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def tO:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x153619cd84a2480a9bb198d8492880aa9a4716863249054),(55,0x7ee7deaf2512402a9f72bc9289002af7339b09449)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma No:∀ ns ∈ tO, Impossible A 8 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I aF (by decide +kernel)
def Np:BT (List (List Nat)):=refBuckets C [tr,ts,tt,tu,tv,tw,tx,ty,tz,tA,tB,tC,tD,tE,tF,tG,tH,tI,tJ,tK,tL,tM,tN,tO] #[0,2617770105,17,0xb50b20a606c041,872562691,0,655510,8,0xa70a1061058050,0,696438,2399645779,85,651297,0xb60b107704e02a,5636322553869,2198249520,0xac0a209709203d,0xbd0b308d07f05f018,0x7505d05b043025004,634885,0xbe08806801f01e01d,1661087745,0x9e07c02701b,0,109,0xba06605e04403e,0x8907a05704c037017,188444,2483576850,294919,344096,553017,0xae09a022006,749626,766008,1912823858,2768482330,573569,19,0x6405904d04a015,0,0x9007006f031019009,602242,2869497998,286780,9554322821186,716816,0xb00a807302f,0xb80a90a309d06704b,0xb40ad099016,258086,9072581586946,14,9141704147054,0x7e05c05102800a,86,438343,0xa4071033029,0x9804502c014,0xb906906502b,2500206645,0xbc07d05a04002d00c,0]
set_option maxRecDepth 20000 in
lemma ad:btAll (fun bk => ∀ xs ∈ bk, Impossible A 8 xs.toFinset) Np:=refBuckets_all (forall_cons MQ (forall_cons MR (forall_cons MS (forall_cons MT (forall_cons MU (forall_cons MV (forall_cons MW (forall_cons MX (forall_cons MY (forall_cons MZ (forall_cons Na (forall_cons Nb (forall_cons Nc (forall_cons Nd (forall_cons Nf (forall_cons Ng (forall_cons Nh (forall_cons Ni (forall_cons Nj (forall_cons Nk (forall_cons Nl (forall_cons Nm (forall_cons Nn (forall_cons No (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))
def tP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24924158cea4651249055339bd944924154cea2aca251055),(64,0xd0924924031633aca38524402a83b1b992492492b1d8dac9),(31,0x64c5de49249202595c64889)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nq:∀ ns ∈ tP, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x67aa812664ba9e1bc9c4c24a472a1f2592a7a89c512993d5),(64,0x24f5414bf7e1b3bdd9cc9489355681249f9456736b38a491),(64,0xae9e7165220f55e9d754a25220aa0c44a9cceb4eac54a252),(51,0x6825ecea8b5861b0e26128a39565b98ca6de67)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nr:∀ ns ∈ tQ, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb4d317915c7438d24924f541509ee62bd8b7361ec92893d5),(64,0x6492492560bcaf4399249249582f2290e87344924958124c),(64,0x5d5326c6d85128920aa0973a76533e28928926aa1794cb8e),(36,0x681249251961b97bcc91528948b)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ns:∀ ns ∈ tR, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa498a62afeed5592912f28d90c9249d6397aae2ad244c514),(64,0xb0d53157f521b5564a44aaa993f76aa5129105504c24927e),(64,0x655865d0dae1a6325228e54c064fdeca944a45154131c7ce),(64,0xae471c25225450c05653ab1587e3ad3a62baac948a515302),(20,0xa9d0e26bbddd14)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nt:∀ ns ∈ tS, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x99564a449aa0349869b8e9d18a73b6521b56ae2ac9489715),(64,0xcd244aaa20533615b57f9de998e30a4914a2a12bb939c90c),(64,0x24ccac5253eade2a6729244aea028d4b4ca1994fd4ab4332),(64,0xf8cdf294b5d2489514259bbbf8c956f0cad6262441ea2249),(28,0x3b4ef2c5129105538944b)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nu:∀ ns ∈ tT, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5e4571b163494528a0262b8d865e7feb7865362c524893d5),(64,0x26d3b9bbb9119eade2bcd8b984a25551505f866ebc76a866),(64,0xeed58a44a24aa0924a8b7779f9dc67eb78ed5d22512e2869),(64,0xb962912892ab596eef3148e433f5bc529b17489442aa8336),(43,0xb4ee3e9d19b6e30e3522512a2a0cf2b)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nv:∀ ns ∈ tU, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7a752bb8c75128955404927a77bfdef4e994c62e91289595),(64,0x44a25654e249517ce1ab1d2c35f48944aca02bad552a43e5),(64,0xf13fcd9f9b3ae912893d40562a198eaa6e67e7deed7298ba),(64,0xeef56390cfd6f0e76ae912895953e4ced5d124a20aa0933b),(31,0xf931972e89251255091516)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nw:∀ ns ∈ tV, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7eac512743245329eabb9a672894885d53b5a74289251055),(64,0x28ac68249366c66c7487485124a28f54d3b5aa4289251255),(64,0x24958124f7642645ec3a436e6492492aaa8197c3a4289249),(41,0x3ffae99ab2492492b032d86dc51249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nx:∀ ns ∈ tW, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7babf2de1f0ce512912aaa4dd4b375366c71a67289488396),(64,0x24a21554e3d5e965fae69d3e5cd7d22512a2a69867e55c61),(64,0x25650e9e2957362249441599e64ceaddee6753c5bc5e1b11),(64,0x672a6cd0cd1924924154124dd09b4eb4cae67f557aa76249),(30,0xc409acfdcd72659fcc9251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ny:∀ ns ∈ tX, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x20aa64fccd0a249441542f71d8e32c87af8ecac64a249395),(64,0x28925125546bb2196e3d7c7638fcc9449072ca6915851289),(64,0x24924aa0d9ebf9924924954c534e77a5128924aa6193f3b7),(13,14625992329)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Nz:∀ ns ∈ tY, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def tZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9798c924924ac1791ec632492492b0527ee4329e49249256),(64,0x58293f7213792492495813faf21b777f9b5928924c542f21),(64,0xac925166ac62523f73b5ce6d64928a6a85e45b1b19249249),(25,0x18813f9d61ae4cb2d4d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NA:∀ ns ∈ tZ, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ua:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x32dc7af8ecf9b5928924c5818eca65b8f5f3e6d64a249355),(64,0x2495892add1d379c71249062a11aac914ace3112896a876d),(64,0x389452aa180924fca7bd4a7e6a989228f502b7f579c61249),(64,0xae28bdca73a6e798d7309452ca180925f51cf9dddc99ded5),(8,3277386)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NB:∀ ns ∈ ua, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ub:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd6e52b54c44a20aa112f6eb6ef55a53d137ab153112895d4),(64,0x994a7331128931507ed1ccd748944954fbb3b554912882aa),(64,0x872a79442a782774a753feeb8763dd44a24f503fcdef7e6d),(64,0xf5fa7dcb4aa9379b958a9889443ca9257ea2f71bcdfea95d),(15,9428418657358)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NC:∀ ns ∈ ub, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9d4f16f17c7ae91289595289d4fb32d2a94cbd53112883d4),(64,0xe91289315063b72fe99b732d5d225126281c9ca87f71de61),(64,0x25550924ddcea6eb8c7b44eb88c48855404eb619ac3dfc7a),(64,0x4495579fa37a48944155c249ba28bece75667bc369d5184a),(16,0xbdb0c37a489)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ND:∀ ns ∈ uc, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ud:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86530ea8c2512a2ae024df14e6632ee66ddd30ea7128a3d4),(64,0x509249f719f533ccbd3aa3094428a0329376517d94b9fef7),(64,0x5a2f3b932d1f70e4492ba81c3b550d9219b75cc3aa34a24d),(64,0x275c6f50eaafa76f8f5cc78c4496b28612a732d32a8bf866),(64,0xdbbd56954a6e331dcc48921d557fb199f70c48920aa72c09),(19,0xd19f124ce63dba)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NE:∀ ns ∈ ud, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ue:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3d78b999225127aa612a78a2fe390aa6fb4dabe389249554),(64,0x20aa5ea96a8d93290cd61ee75ccc922495150493bea719fe),(64,0x25505eecdf94b9eeb137fa5686f37a48944aeaad0de92249),(64,0xca18815a6471dbaf71b365ce71184a2cf54c5eca7e491249),(43,0x549997b73f7723d56d0ec643e9c49242)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NF:∀ ns ∈ ue, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x44a2492a97ff3fccbe5324492883155fec6432b871249055),(64,0x8892482aa316d54e643345248eae663112893950e69cc99e),(64,0xf11f5244a24d5499fac4df0d9b1c6999244a20e597a643e9),(64,0x81c9543b5467ebc7b9b363e199244a294541be9d7732c8f1),(1,1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NG:∀ ns ∈ uf, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ug:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa6cd8ca71bd244a20e58133c3ef50edd4921b8cc93289394),(64,0x33be778a2fe3d8cd8cdb9b4ca7d38924a5155319a77eac6f),(64,0x2490a28bebcfb1244924154c25cdd4576e7d89225126a860),(64,0xe4924e501dbd39689324925524e94efd47ee36d8a5664e71),(32,0x6fa7dea1e67d4cdb9dd73e9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NH:∀ ns ∈ ug, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x241ea2949dbb26730cbe3ddf5f97ab931b8c87d389248795),(64,0x8aa91fb8f5f2a64889251062aade893a4e76ae4ce73e9c49),(64,0x31677556687af8cc6644928831538cb21ebe36f332249441),(64,0xca904f6eeb0ed4aa512823154e7e65b8f5f1f0cc66449289),(31,0x1a265b8e56e8e9bcae49409)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NI:∀ ns ∈ uh, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ui:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xea43795c92812abd2d3f1bcae4940155dff198aa49250056),(64,0x32194f5c9248056251324e4eb21925321d172492028a8576),(64,0x24920159ed3394f58924900ac15dba90ca7ae492412b3d7c),(13,264786386609)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NJ:∀ ns ∈ ui, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xbb53663a2ac92413955f9fd52492480565f9915249248056),(64,0x3219abbac327721449213543bb73ec54a24904aa0932530b),(64,0x55124900acf6d0f3e72892402a87547b687dca944920b548),(11,4139042932)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NK:∀ ns ∈ uj, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uk:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x25621b5fd84dd0fb94ebe24a2423950eff14322a89248256),(64,0xb8c8745c92480aacfcf8db57c492490550fcf0d87c249248),(64,0x58cb9ef0ede93248e73a2e4924035524996127fea5b8c929),(60,0x52ee74ea92492402b0327361956f33979c7455124904d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NL:∀ ns ∈ uk, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ul:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24a2402a976dee99399e2a4924900c594bb9f95249248056),(64,0x54e581dabab28755a77cdb4d9ba5cc78c4496aaafef4ccff),(64,0xaa4ca19e2fb2bf1ae4ca67ccc89212ca3d7d3227ccc89201),(64,0xa4fe66dd489f3322480a2a60336ea67de3112422a980a327),(14,675372199900)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NM:∀ ns ∈ ul, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def um:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xfceb0d7f3ba2956a7a86448925654c0bfb55efbc62248455),(64,0xbf1ae4ca63d43322484baa6eb54cf99122480550953fdece),(64,0x91224847ac0c92e5fbe6448920954c0abc5193d52650c972),(64,0x2d454c9a439532128920158c07a9267773f553d3b9d8e2a1),(43,0x4c06cb0c9d43b757a9f1366caa33244a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NN:∀ ns ∈ um, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def un:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7ab931b8c894a892038aaa0bd2af399ac3dca8fa9224a355),(64,0x449251ca832794e94fe892482553ae7e444ce63db9de3ee4),(64,0x3b134993f769d943fa449094556057da9c7fa6b933fd4c7f),(64,0x7a67dfb9da723fa44908e541935874a7d4892492a980ada6),(43,0x9db4996d769d8e47f489201ab1c4a937)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NO:∀ ns ∈ un, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uo:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3a1e8924805606cd54c7f4492412a8326b0eb4fa91249255),(64,0xdb2365cf58f43ce8912413d5576ebf3a1e89248056576ea6),(64,0xb8cb6bb4e94f3a224928c542bb753286f4492412b02ac30f),(47,0xb05ecea4e6b933fd4c79d11249462cb02bf)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NP:∀ ns ∈ uo, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def up:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xaed3b2879d122484d63013ffaeca4cb6bb543ce891242395),(64,0xaa6024cb09b7c337e64cf99b732198fe9124255530132d),(64,0xfccdbbd5687f449251ca996c87524924805552eea1fc9449),(64,0x248462ca907f3ac35c99ea7298fe8924b316549f4adef731),(28,0x303b6932daed38eca1fd2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NQ:∀ ns ∈ up, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uq:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf8fe7524924a31532d91e84924900aa65b3bb8fe4a248055),(64,0x3d7cf9fcea49249262c729ec5348fbd0924921aa823f6e7a),(64,0x2aa96e33d3fa24920154c08fdbbb548f1d4944909ac11fb7),(17,0x397e562249440)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NR:∀ ns ∈ uq, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ur:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86f3aa249451eb180924abe439de7ea67d15e7544928a595),(64,0x472a0d91cb8f5f191c5622494498b18092b790fd4cb22d0c),(64,0xe643239112892cd58d30cbfa9cd96af4eb8d9ba91c889449),(64,0xebe38ea752492496b196c8ef44928805534c0f9d3186c8fe),(40,0x2acf49df1dbd5d5e4a24806aa0dfa9)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NS:∀ ns ∈ ur, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def us:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24920e55cd2a9712492402a9811fb73d7cbbc75251242316),(64,0x3e12492418abbfc70ea4924900ac49939bebd77739d79f09),(64,0xf0a249061caa08fdb9ebe3e33a92492518b29e647eddda7c),(64,0x24935c9d19abbbe37c52b24909450b21d91132635dd62bcc),(2,14)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NT:∀ ns ∈ us, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ut:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24827aa0973431bdee3f72892413940eedcdf14a51248255),(64,0xe512482553349143e72892402a82639a2265cef90dd94a51),(64,0xf723f72892415150495dcb9ef7b3f6289241395066922a7c),(44,0x5d98c7bea7fc5124826280935cd8c29e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NU:∀ ns ∈ ut, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uu:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x86eabe24924839550d53d3f2539994de9d4e88d84928a3d5),(64,0xf1c87c249248056065b0dd57c4924904ac4cf62b3f26eabe),(64,0x335b978be249248656260249c64d213ed37624924867aafc),(64,0x325a79b0ec6f50ea4924906ac0e335b9e33c249248296260),(4,1966)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NV:∀ ns ∈ uu, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xdddea1d19248055336e6febe2492482aa9a4597c49249055),(64,0xf97f71fceb1cbce9143a324926a815dba95537b24904aa6d),(64,0x90f27464921154130fb8b9343ac72f7fa9543a324927aa0e),(29,0x53487a87464920954c0a6)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NW:∀ ns ∈ uv, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x33e8bc46644928839652ee7a90a24900aabf3cea51248055),(64,0x249441eb107fb095ff3a1fb47e1b1124a28e5499bae75c67),(64,0xee4a75e6cd8de7999124a24e58bb8ad319be36c7f735d332),(55,0x66dd5cb64512482a99b7372d9144920aa629365fa)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NX:∀ ns ∈ uw, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def ux:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x777ef996e52e44924927aa607adcbfc75ebc3754492494d6),(64,0x24929ac68335e6ea4924908aa0cf2637544924904ac892b6),(64,0x44924908c59033c994f512492422b2c1eba2ff1d7ba6ea89),(54,0x3ded7ee3ebc6ec4924905ac60576ef1dfd3af374)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NY:∀ ns ∈ ux, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uy:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0xa0752153025c9a2018c1a27162c8fe6880010688cf8f2459303f9a2000c1a2009cd1962344020834),(64,0x841a013aa3344688021068240041c61900f172688063068a4891ac304ed33cd1004190642400bb),(10,0x9d48764e1a2)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma NZ:∀ ns ∈ uy, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9b3ebabc944901ac49266f4d96af719f4529c75449288516),(64,0x201aa99eee74a4924900aa8c2a5dd7394a4a248062cec84d),(64,0xf615bf874c4d9b2fdcc4a24807aa57ff93f99b73263f9289),(47,0x76f4e361d192480555348673a9449201549)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oa:∀ ns ∈ uz, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2423162c168ddebbf558ec7a249219ab29a4355e51248055),(64,0x4cd8d32faefd54ab295124908d58c0519a67e6e6aca5449),(64,0xf4f5f3fd687524924935664152735c99dab192924a2cc54c),(64,0x7b92492518ab20f3fd35c99fe765792492598b052daefe64),(21,0x1815d9c72586cd8e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ob:∀ ns ∈ uA, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xfb73d7ca9fcea49249462c602aec69e659f2af424924a355),(64,0xcf5fcc95290f2492480d6301fbd3d7c7678ea4a2484d6411),(64,0x5819a7a64e64eaf2492482960ae334f4c9cc995e4924905a),(64,0xf4df1d9b1939f55e4924904c59907ef0f5f1a6d57924925b),(4,100)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oc:∀ ns ∈ uB, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uC:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x529249241ab397e7aa2492482a8766cf3b55caf2492482d6),(64,0x24904c5839ae3a7a64eaabc924920b595d9c537894d22a6f),(64,0x24806ac4db4cbbd769dfa2492483150ecb9cb9e76ab55e49),(50,0x1dfe298f2492480563673673259cc95198f249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Od:∀ ns ∈ uC, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uD:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 4 (unpackWords 5 [(64,0x546c82d9a200041a00c9c5912212467244400901a2a181e03e688001068031eba16a84261cf11834),(64,0xe22446d9cd1000a0d151b11b22d9a200081a1e7e4488ce39a2000c1a00944d3c8b0ac5b344011834),(6,90528028)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oe:∀ ns ∈ uD, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x90de49249052c1dfe23792492412b0576e6e325249248256),(64,0xb4ecb9f0944901ac5c9bbf73b5fead3e124924b5839a1939),(64,0x5e9de92492404b03f996c7afe64e6c3bd249248262c8fdbb),(39,0x1db8cf21d94e742492496abd7f327)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Of:∀ ns ∈ uE, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uF:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x581ae4ced596a7424944a5990543f772f76b9ce84928b315),(64,0x961ae4c6eaf9d092492cc5829a63f6e7af8ebc9d0924924c),(64,0x8aa90e8492494d6302d729be5348729ce8492494d6643b6a),(64,0x25258c077b1d76d52c35c98e7ce849249472ccad729be534),(24,0x301fe65f1b5f3a1249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Og:∀ ns ∈ uF, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uG:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc712494faa0d9b6333ca9c4924954c0a5f1f50c84a248456),(64,0xd163f9c492498a1a1b64ab7c53aff944eb5ec67bcce6634c),(64,0x24920f58d35db4efcf962d9674cc71249462a69766abdc67),(64,0x7fd0cb22d9647d38924a6a99e4267eb137c366ce1c6998e),(59,0xd032153d5b484dafc3275619667a1a6f331c4925aeaa)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oh:∀ ns ∈ uG, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uH:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x551112cd1aef6ec285819a596111112181802c878f3bc7987812e2a711111518),(64,0x19421121025192dbb1f8194211111011961ab916c5e4b858d6f431f112101619),(64,0x16ac3ee6d196d1d211210141902dbd18a31d22111011193029c3cb5fc4c2939),(29,0x118a39c5fc6d1af71d2112101519)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oi:∀ ns ∈ uH, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uI:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xc1ca41a83fb18b5e71d211111451a6411a8d1c939c1ce59b1e971d2111112619),(64,0xd91ce4ae6d3c2a71d211210241a3028b11fc1df5fc6d2a71d211210261962201),(64,0x11261918c873c4311110011903a72d4311110111905c91c83c43111111181c01),(29,0x2801c11aad4bd28e4db1cc4396111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oj:∀ ns ∈ uI, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uJ:List NodeSpec:=readDeltaNodes 8 (unruns (varNats 5 (unpackWords 6 [(64,0x981e1634200019411c7e40bc06a0a620f08650472457c2ea682986442214001d03b8844249201ae8c781c8e1c2004092),(64,0x60b90882d05a02c08189088400060b8fb160b407407a2042c2212512a1280182e4220b413c0bc2042c22920aef04884),(3,1760)])) 0)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ok:∀ ns ∈ uJ, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9f4c6d8b431924805531df7133f58ed79bd7331889249356),(64,0xb8cc6324905507ef953f98c92412a83f7c653798c92412a9),(64,0x249241ca9a1cb8edf9b763658fe5f1b0924928c59cf69d71),(62,0xd0f6f8d963f8992924925258cda15be33ce6790ecaf361)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ol:∀ ns ∈ uK, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3d7c75e69b0924924c58c4e4abebcd9baf8ca64a492494d6),(64,0x24929ac618819e652c35c98dd4ce6c249249862c14f3b97d),(64,0x2882d670fb69366e4eeae2494416b1816b9732c9ce579b09),(64,0xab1316b9732c9d5561b0924929ac16b9c931b3c3b998d849),(38,0xc4eccbdeaeb0d7263399c9249251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Om:∀ ns ∈ uL, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x5f1b4ce6c24924b6b1883f39b3f35c98d98ce6c24924b316),(64,0xe4924905ac15bcc9ebdae79da6457924924135631036790f),(64,0x3612492518b3ba99e752772f5173612892018b06f3b4cf55),(64,0x24807aa9d98d9b2e6736128920a5887339ff774366ebd36f),(36,0x36396750cd213219f637e5e9b19)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma On:∀ ns ∈ uM, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def uN:List NodeSpec:=readDeltaNodes 7 (varNats 2 (unpackWords 3 [(64,0xd96e64851248055336eff5e144920155fdb1b57851248055),(64,0x8748a43af2492484965aee77d8cbeaf8db0cdd9248062867),(64,0x9219adca7c4924904c54f261b6da7488dd4924921a5964e5),(8,3271497)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oo:∀ ns ∈ uN, Impossible A 9 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ad (by decide +kernel)
def Op:BT (List (List Nat)):=refBuckets C [tP,tQ,tR,tS,tT,tU,tV,tW,tX,tY,tZ,ua,ub,uc,ud,ue,uf,ug,uh,ui,uj,uk,ul,um,un,uo,up,uq,ur,us,ut,uu,uv,uw,ux,uy,uz,uA,uB,uC,uD,uE,uF,uG,uH,uI,uJ,uK,uL,uM,uN] #[0x18a1570d404102301b,0x18d11110e0b000b,0x14e1441430f90bf09208b06e01c,0x10a1040fc0e307e075022007,0x1421130df0d90c5081048030016,5251674187,27628065529927,0x18013a132118021,0x1731660fb0d70c30a308f06505d03d001,0x18114b12e0f30c609104d045025,25292895473673,0x18312612310f08d,0x18c1270c00b405904603f03901d,76578996154175539,0x19117a15011c0ed07a,99375857021927522,0x19316d15e14011e0cf0cb07d012,0x16c16816312b0da0d30b3097089013,0x17116711b0ff0f1086,0x17b16f1250f50e10a1098029018,0x1200e40ae08e068060,0x1971940ec07202c,0x13c10709d06d06a019,0x1581520fe0c809507f06f06b017,0x16a0ca07006c049027,0x18818517713f124,0x1300ef0e905c05102b,0x18417d1190fd0ce0b60ad01e015,0x14d1221060d20c40ab05e058,1167488,0x1381090b505f054014,14,0x1791761651150eb0ea0e2090043,0x1451361020e60d5066042,98258132802977798,0x1370db0c20ba08a024010004,0x17e14a13e0d60cc0bb084052026,0x18b13108c05b055020,0x19618718217215c1210e00aa09e08501f,5973159986,27012140240942,23023105298444,6796185869,716876,0x1170b704f03402800d,4161650746,0x16e12f11f0b80a708302d,0x17412809c07905601a,0x1480ee0e70d80a005a037,0x16b1601331290f40a406704a03b00a003,0x1551140f004003802f011,0x15111a0c70bc0a50a209f08807407102a008005,93468800125304951,823350,18833432584260,26324039721108,0x17c16913b12c10c1050fa0e80d10bd0b90b10a8093057053,0x18f15f12a0de078076,0x1861751350be099002,0x18e16214610809b08703e031,0x19015a1490b206400f,0x15b15615314713d10107b,25843691315354,1232976]
set_option maxRecDepth 20000 in
lemma ay:btAll (fun bk => ∀ xs ∈ bk, Impossible A 9 xs.toFinset) Op:=refBuckets_all (forall_cons Nq (forall_cons Nr (forall_cons Ns (forall_cons Nt (forall_cons Nu (forall_cons Nv (forall_cons Nw (forall_cons Nx (forall_cons Ny (forall_cons Nz (forall_cons NA (forall_cons NB (forall_cons NC (forall_cons ND (forall_cons NE (forall_cons NF (forall_cons NG (forall_cons NH (forall_cons NI (forall_cons NJ (forall_cons NK (forall_cons NL (forall_cons NM (forall_cons NN (forall_cons NO (forall_cons NP (forall_cons NQ (forall_cons NR (forall_cons NS (forall_cons NT (forall_cons NU (forall_cons NV (forall_cons NW (forall_cons NX (forall_cons NY (forall_cons NZ (forall_cons Oa (forall_cons Ob (forall_cons Oc (forall_cons Od (forall_cons Oe (forall_cons Of (forall_cons Og (forall_cons Oh (forall_cons Oi (forall_cons Oj (forall_cons Ok (forall_cons Ol (forall_cons Om (forall_cons On (forall_cons Oo (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))
def uO:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xac924924958124994c79e65124927aa0a253854651289395),(64,0x9ccc57292209aa99e38a12492802b070e8c92492495819cc),(50,0xdf968e12492402b033a8e12494412b028c919)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oq:∀ ns ∈ uO, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uP:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2b0339d892492412b1d3ad9c24924805633c597249248056),(64,0x594b89c5124944e591521d33b492492018a833a9c9249241),(64,0x94d9cd87144928a356683e697b1c67ace28948b39504e379),(12,14019774861)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Os:∀ ns ∈ uP, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uQ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x993353a53677f1cc924928e5902e1296d4e87148924a396),(64,0x489ea2a1e9cd851249249581bccc8d9d4bd7a51249249ab2),(64,0x5ae70dae2ac9489a7287128a0cec65ae1a7d3be5e9b55289),(64,0x29134d54d2418d2d21be19e294ccb1492261ea32885213b4),(27,0x5921abb192a9ba95ac51)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ot:∀ ns ∈ uQ, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uR:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd8f31748944c5144c90a63bb7e9d31f56f0d8b148944d3d5),(64,0xc0af9fcb78a1994fd4af659924a2d454c441c8bb0c94cdf1),(64,0x33944928b595648264e77537467aa6ea57bae89251314559),(64,0xbba3af454d14c66a512492528b1841274e93d0dd5687d5bc),(64,0x689249aaaa5920fd8c7a1baad0fab78b99ca24944d3d640b),(34,0x984824e989e7dc758e487aa6d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ou:∀ ns ∈ uR, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uS:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x7f1449249256310255f5788c3267b9a665e47f324924b5d5),(64,0x2492492b1882bfadc9fceb0d332f2290fcc92492d458193f),(64,0x8c924928f5902775e63ccbabd4ca6324924a396064fcc9ca),(64,0x9ceb4c9ddd14ae43a124925aaaa07e5e436656293af5da4d),(64,0x32957d5e1fd6af734cc7de63b56a6d6492496e2c48296c4c),(4,784)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ov:∀ ns ∈ uS, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uT:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd2e5e7672489459eaa04f5e632a57c37af219bb24924a515),(64,0x38c24924a3163d329198e972f39b4e49124947aca1057459),(64,0xe7230924b39547c70e972f39b8e49924835540d7cd5648ac),(64,0x6aa86024e7373a1375ca56aa4894528ab3812aac769d79cd),(36,0x2c19e188a9a451435c52aa62251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ow:∀ ns ∈ uT, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uU:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf21932d69f5eca9889452ea05e28e6c74914a72a93289354),(64,0x4936999c7545ee3b7c79eba44a29750c04fe6c514d09df1),(64,0xa7530925134e54e44846caa1bed59cdd4a8ea9225134f54c),(64,0xca13b450df6bb6a959d526510728aa242377539994d6a94c),(64,0xee249124c515643369b3287f33fa7531494f94c3aa30945a),(31,0x7240fb8aa755e65f1b6552b)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ox:∀ ns ∈ uU, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uV:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4892498baa902a6aa2fe3d8f94c996954ab43b988924b555),(64,0x72b86f997c92249262caa2412fbf9d8f287d5753b7c7ae66),(64,0xd21861d5798fb4cdb995c46124930f551c60257a76ea2fb2),(64,0x24a59558e056e7eea2f71d1ddd6954aef70d24925aaaa482),(64,0x2b05feca570c2492492b20a5cc9d6e7aab625cf3b2f4c249),(19,0xfbb3f92249249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oy:∀ ns ∈ uV, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uW:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x414e5194cba997f71d3e9889249a7aa1cd3b99e449249256),(64,0xbcf86324907286120ade253a9b752b87636124924c3d5509),(64,0xa14d5caa2f73f3ad2a95d8f9a89249ea2fb2879ba47a752a),(64,0xa7d49124967ac605fd50eb4ee6653f337c7c5ccc922514a2),(64,0x87de6dddef94c65c9224924f5520bf3b7517d9fe65e66dcc),(7,58478)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Oz:∀ ns ∈ uW, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uX:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd8d94f955c7d38924b5d407dca1867f0cdbae7d499249355),(64,0x87ecf556c4ba94dcbd30924925e59905599cea2f72d72ea3),(64,0x452ea857748fde2d2a94d90c249249395097e7ca499cc32f),(64,0x5f199124924c5d6211336275e7d73c3b654cfb9eef332249),(64,0xe66dcd911249259caa241a748648b4eb55bbbcc36433f5bc),(57,0x120993653633587bf8cc892492cd5890ed3a72f4abc)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OA:∀ ns ∈ uX, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uY:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa1e92bb4aa4925025621432b324aa5dcc9d5855249282396),(64,0x5f6329e79849241872c602ccb3a3e7ed2b79bc9e612504a2),(64,0x88225f5a7e745a3abd8ef3d62492435566a20919ae3a4ae4),(64,0xf5f14a7aa4924904ae12e495adab7c6ceb454924920a8b2),(33,0x7b23092eeb4ed952892413d5)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OB:∀ ns ∈ uY, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def uZ:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xc1d86754924920958c50852132dc72b7474e8aa24920c356),(64,0xa4c0fcf955692492432b10a9d4dd3292c3274be24924846a),(64,0x542baf3f1d154492412b132d5e7ee9d29b3bb16591248072),(64,0x521d154492412b181137c86ed8c911c6af62b8e8b9249095),(6,11191)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OC:∀ ns ∈ uZ, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vc:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x337549249209ab05167b9256b6adf1b39b968a9249241557),(64,0xd3732e549249209583d377a2a4924904ac0f5efeb7c64327),(64,0x2b07f7efb90924920958c057d69721ceca67e8928908e543),(64,0xdcc31e7b732f3ba91f913ef1889215595064d8db51249241),(14,1868466258548)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OD:∀ ns ∈ vc, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vd:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x25626a24184998eb31d39df399cc65dd4a7a86448920e5d5),(64,0xf9e8b28bf87586cb0f4b999224926a8b07afa667cc84a248),(64,0xad026cb9eae7517f1ec66c76ae4cae4a524920c59544d303),(64,0x4492402b188e289256931ba2b0eb1599da69f11249062ea9),(64,0x409396effcadaa19e1b7435c994c7f4492418baa64f2267c),(29,0x180cdba98fa9124908ac72)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OE:∀ ns ∈ vd, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def ve:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4492422b2881f2e50cf169dca4fe758e5ea447f449243556),(64,0x510561fbf5f43732f6877a7994f4492435163019358af3ea),(64,0x531e744492418b2ca20af727aac5275ebb4f26f449243396),(64,0x9e2bf397afcfe892486a2a72409f2c51ff4d5a634db5e8ed),(64,0x36e7643a72bc32398cfe1d8e889248317554412a7cd547b3),(64,0x467c899cc7b75b773d754a6e331fc9449097589e4af4d7a6),(3,96)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OF:∀ ns ∈ ve, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vf:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9e2d39b29d63979ca63fa24920d5160f4dd4c7f249248256),(64,0xfb73d7c752492486a2a1e9bb90fe4924904ac722413e58a1),(64,0x3d7cbe3a92492427560a5dce3a92492412b130125dd8dbe1),(64,0x24904ac14bfbbcfe4924904ac60489f21475e6dd92db9b24),(14,136066516041)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OG:∀ ns ∈ vf, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vg:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x589a6053934cffa9d65ba8bf36c33f5bc32391124924c716),(64,0xd4ea4924909658c0e5f8de89249211590525aa4e89249211),(64,0xacf0edb13ed7b124924231530179177636ec7da6fd0f5f1),(64,0x80df5793bb732e554f8492490ce58c0e5f9e88924921158c),(52,0x2603ea2adc6586df0fdb9a97ccea492490d6589)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OH:∀ ns ∈ vg, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vh:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x6eed4d994a512483145417f6725c4c90d8a55a92492413d5),(64,0x58c4438e484933e5f7e7f87fa5124831450c441349726337),(64,0x94fcbe24924830e58f66987d4a7536ea571d74d84924930e),(64,0x7ee3d7ca1d49249219cb0761a7c2492482562c84c933c8ee),(41,0x13029a4369d4924921958980bbe2b65)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OI:∀ ns ∈ vh, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vi:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xb32dfd31bd31f228653d9248072a4c066ddc8be249248656),(64,0x8e5ea550e8c92423d50adcb7dcfb949ce99426f649209aaa),(64,0xebf521449201543d3752a90a24904aa6027db0ed54364875),(64,0x67aec85a1b2c3a2dd43f9f3bd0db89b3646644928b5d57a6),(46,0xd303baad3ad4e98c3647f752ba66449249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OJ:∀ ns ∈ vi, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vj:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x3f199124924c55635905e956a7ee679cf729fd124924c396),(64,0x879975366e74332289259ca9a90369d2aca1d56951d61b37),(64,0x96a24924825648225eb3be8cb6296a24924b3d534c0778b2),(64,0xfc924921158d290451375abfbcebceb91249241a7ac0cbf2),(51,0x6024bdad24b961d21ba92492425553019bdeeb)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OK:∀ ns ∈ vj, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vk:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa7f4492496a2e1dbf3a6784924904ac0cb61b7a249248256),(64,0x7663299b732aa74449241aaac4d317aca95fa61b23fb990c),(64,0x3e6729bcec4d9b3ee62492486aac4f242b22f4d7a636e764),(64,0xf8caa1d49249209cb85778f9954a4924904aea20aeb5433c),(64,0xa91ff43bf50cd23dccb229fa24924b3950acd4f3be37e87a),(1,1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OL:∀ ns ∈ vk, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vl:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x98d76d3549b996452b98e88924847aa1cfea9fa249248256),(64,0x37f44924900ac61061bec323efdc7af8e949249219eaa85c),(64,0x3b7a72d9144921158137da647ccdb9bccd89249209ab19b7),(64,0x2892415155085ad521aefe67c77f8cdbaea9d1924867aa60),(35,0x17a7ec7cb9433484fe66dcdabc)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OM:∀ ns ∈ vl, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vm:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x30e8892486facaef0daba94a24900ac6c98dab6451248056),(64,0xbd652a24920d51547132c64990abe424dd0daf9d62b33b4d),(64,0x25aaab80d9ea9212492422aa311079f2997af6a9ff7ceb1c),(64,0xe7af968752492486e2cc8454bf973538ff4d7267f9929249),(64,0xc613b5ae7327579249241a7aa4c0899f13f9bb994dbb23f6),(15,7295028610020)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ON:∀ ns ∈ vm, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vn:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249549443df1569f26357b8ec4cb69ebe3b2bc924920d5d6),(64,0x3d7ca450ea492490cd5c29a456a249248256064fcff91249),(64,0x33c3ad30dbe97a57dfb8f5f1ca524924835c58980f7e47ee),(64,0x2492a964235d90996d3d7c76394a49249061eba48836e3e6),(40,0x3029a73be44924908ac0c9fa932249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OO:∀ ns ∈ vn, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vo:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x8653c9249202cb8729b4f249248256343fb6325249248455),(64,0xb6993f327561e492490d458986ceed30db0ff33b699a5729),(64,0xbb732f3c9249209583d2f7b1e4924904ac5834ea4fd559bb),(64,0xa6f2492484a2c4c0b4569f2d25cfcdbbbfce8492490cf582),(32,0x342be99abd53915d699ae769)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OP:∀ ns ∈ vo, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vp:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xea6d16efbf71ae4569f0924920c7560aedd6c6f249248256),(64,0xf4f96236da6cae73273bd2492486a2a590b4879d693fad1c),(64,0x2492d559904ef0953af6752772f3b43a124925a8aa616bce),(64,0x3d7cb4274249248662ec827e889b97b3a939ae4cff5a9d09),(64,0x4c77c2ef3e5ceca4cb69ebe7ce84924906aeb3214d61fb7),(45,0x320c765265b4f5f1d9f3a1249243397251)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OQ:∀ ns ∈ vp, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vq:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x2ad78a2db2db2fe782828196112141a18011b2ab911882c491ea111111101719),(64,0x93a619711111618346011291eb1c8a13959f783d319611111419196442111288),(64,0x11105744201d2881af91287833a59c782f2a61111141a18029b188b3ff5d92f4),(64,0x84420129d1b9a7831ac7b3af3c3c1c1b2a61111141a19119aa28d7eb1e915871),(32,0x420112ca1eac3af2e4a3c59611111371)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OR:∀ ns ∈ vq, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vr:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe492418b2a6120cf9fc77d94b4cfabf3bd0ae7d3c924c3d4),(64,0xc0fbb3b5531124904accc3815ec52e889ee786d3768f431b),(64,0x5672a9ba997733ee7bbcf75128847aa0db7d73375124904a),(64,0x6aaa8e3035b4a93b9cb513b630ce67d17c7ba8924831c590),(64,0x7f1eea24920d51650c04aab5f4bba2b1598cf2996ba89248),(32,0x39240f5afe4e98fb95877f0f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OS:∀ ns ∈ vr, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vs:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x19772039e7ad184ad41ea3c94a782943961111104191a05c9493c43111101119),(64,0x11191906fb1c6e93eb781b43971111025191906fd216e93fa785d39611111026),(64,0x113619281204ac38e3de2a3aa4ad7491d4b4111111104191a05c91fc41111111),(63,0x204e8119f1a11bc59a652a42111110271b182048c7a93f4b81e3c1bf3d42111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OT:∀ ns ∈ vs, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vt:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x4ea1a941cb4aa783c2a421111105181a71c01bd6bb4a81e3c23d42111110351a),(64,0x5f928581eb42111110471905dc14ee2ee4aa782e2a43111101619712202bf5df),(64,0xc2c111111141b1920111aa949e2b958a1ce1b3d431111261953203ae7a93ce7b),(64,0x18bf13981621fb538a7f5d2c111111141b1a44201111da3cc13c97e92e159a1d),(64,0x20111111ec2ee281cb21bb5e82c28b7b62b92dc11891111111052a1a44205a91),(3,1810)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OU:∀ ns ∈ vt, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vu:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xac3ee75e2918911111110351a32011f838e79c3ed18959b15d2c11111110371b),(64,0xaa4ad75e2b2c1111111061c1a14018ec189d4a875e5852c11111110351b42016),(64,0x21a1941122039f14ad75e3a2b2c11111110651b61212022984ac29c5a149b43),(64,0x110361a416ac4db4819b11111110131a221115f189c12ac15fa58d1db1111111),(26,0x310118a39c5fc75e1af2c11111)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OV:∀ ns ∈ vu, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vv:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249248672e7930a3ee72e5e4a6ccf99b72a4529249243517),(64,0x9949cd72639d3612492418a2ed05a75beae5271b2c7cfc6c),(64,0x3b550cd213f99b7369d0d8512480a2c7ac829bbba99f999d),(64,0x249248672c41735ea19a426433ec5786c2892423d65e9f6f),(64,0xb63f71ebe33652924924339635226db8e9713ad866dceae6),(51,0x69814d393ad866dcfebc28924331534c0ada4e)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OW:∀ ns ∈ vv, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def vw:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xd61d71d0d85124839520ad74277d8ca67d97324289242395),(64,0x8f55e931d79fccba19df37f24924806ac54da19a2954b55),(64,0x85cb0e917c6ea492490d659a24c9a3b6f73e27ee77e49249),(64,0xc8124bf2676473537c3ae2492484a2aa209eb5e8b5d0aaec),(52,0xe7b4eb8dc6e2892412b1fe4335371b8a24900a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OX:∀ ns ∈ vw, Impossible A 10 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I ay (by decide +kernel)
def OY:BT (List (List Nat)):=refBuckets C [uO,uP,uQ,uR,uS,uT,uU,uV,uW,uX,uY,uZ,vc,vd,ve,vf,vg,vh,vi,vj,vk,vl,vm,vn,vo,vp,vq,vr,vs,vt,vu,vv,vw] #[0xbf0a3087039032029,3020582972,3489955871,0xf00cb0a60a1,0xf10ee0c20a907a077073028,0xf20b7056009,4077666488,0xf405f04100e,0xae060037017007,7353873350683,1040595,2902843483,73762044008046597,639102,0xb009a05d04904200f004,4228677748,72629684755693598,210,100,0xd60b5054034020003,0xba06e052006,405592,249,0xbb0b30a4097,0xea0e40bc09408906f06904c025,0xfd0f70bd0ab04d,1028159,0x1080f60d80cc0c5068,4161548308,0xd40ce09f09d09609003b,207,0xb108e04b031,0xe9095059008,0xdc0b209108607f07c04e019,0xec04f02d027,0xc1050026016,213,0,0xe70d90c9012,182,17596196139076,0xaa0a207006705103d013,0xdb0b90ac06c062,18077585461361,0x9b092076057043021,528397,4278747268,0xc605c02e01d015,0xe10ca0c70a508007504702c01c,0xfa06103800c,72355358215557251,0xe50dd03e00a,0xc00a809808f06a,0xaf09907b07204a002,0xeb0e608a07d06603a033,3893194899,856185,0xda078046010,0xe202b02a01800b001,0xde065055036,3741966405,0xe00be082022,368657,0x1051030cd08c08b06d023]
set_option maxRecDepth 20000 in
lemma bD:btAll (fun bk => ∀ xs ∈ bk, Impossible A 10 xs.toFinset) OY:=refBuckets_all (forall_cons Oq (forall_cons Os (forall_cons Ot (forall_cons Ou (forall_cons Ov (forall_cons Ow (forall_cons Ox (forall_cons Oy (forall_cons Oz (forall_cons OA (forall_cons OB (forall_cons OC (forall_cons OD (forall_cons OE (forall_cons OF (forall_cons OG (forall_cons OH (forall_cons OI (forall_cons OJ (forall_cons OK (forall_cons OL (forall_cons OM (forall_cons ON (forall_cons OO (forall_cons OP (forall_cons OQ (forall_cons OR (forall_cons OS (forall_cons OT (forall_cons OU (forall_cons OV (forall_cons OW (forall_cons OX (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))
def vx:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x64920d5012558b9eab2892493954115cf31451924924a396),(64,0x3315c924a2098b06c95e38666a12492813d6269bcec79f19),(64,0x263e66329249248272c83269957a4fc5724924847ac1dcf1),(39,0x1cc8ca6746633385124904e581929)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma OZ:∀ ns ∈ vx, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vy:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x24139524b733f8c7e92492403d5771bdf3319dc2c9240315),(64,0x45439440d3f1ae738cf4e28924928e581fcb476326761249),(64,0x8412afab68a558a24944c35538944906d26c3bc30faa944a),(64,0xe6d64924938f54b281dcc90f86fa695bc3f144924934f591),(28,0x2c920ea76eeeca7c743b1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pa:∀ ns ∈ vy, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vz:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2a6909b598aa48944d554670562269d255e739224924b396),(64,0x35454d641b22871d4db73ba9f4ea9124a261eaaa4b079f97),(64,0xc6ffd4ae244924938e59450b07d65ddcdb29d99877491249),(64,0x251ea141cbc9914d39b0b8b63092492cf55a44857f50eabc),(64,0xa14fd7aa2f71d6c52be9144928e5583cd2ac90eccc3e24c9),(1,2)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pb:∀ ns ∈ vz, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vA:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x9398492496aaa4a0b4aa24bccb5cafc76c79f5244924c555),(64,0x8bdc76f8f3322492498a2ac83ebfcff145ee5e53265ad3e9),(64,0x3973029937bc3e5e6e3ad5b93d12494128b224136e3765ba),(64,0x32756aa49249061cb327920c2b6b5dc74a6ce79e8924920e),(64,0x256508464abdf0e94d9d63d1449219ab18a1089925526e64),(19,8606133415875144)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pc:∀ ns ∈ vA, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vB:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xf952492484aac6b20db8cb7a3b5eb9abd8743d224920c3d6),(64,0x8afdcd572f62f912492423d6301cb1962d3f76aee9d799eb),(64,0x72f52673f2a47de44a248597583d39b512492412b180a9e9),(64,0x3165be7e99799b747d48924851459b2c9448275a65dc98ef),(64,0xa6f5690d5a637633c34da79e74449242aaaa52289077914),(64,0xa5120ddb1de28bf8f65e75a552ad0fe492490728b1852449),(1,1)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pd:∀ ns ∈ vB, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vC:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249072ea930a242c7ed545f64e571499f91c88924920f556),(64,0x67c2492482563118883b452ec6e8a686cae778b32294f849),(64,0xaa52492483cf58c4422ff262fb73fc3e728924187a80c9e4),(64,0x36f33f34da7a87464920d5143122586fec7e34d865d4cdbb),(64,0x8b180f9a19639d43d593a955ea42892423d5462219de3bec),(49,0x1a8906d86f5ba8bdc76c6cb0f74cc8924926a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pe:∀ ns ∈ vC, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vD:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xe8924920f5173019e7571ba727bbfbf3298cd91249242516),(64,0xf94c6688924920c596261448576517d9fe65e77523f2194f),(64,0x30e582baf3f294924920958d6437b75643e1e6ea7dc6df1e),(64,0xb69b4f54e88924835c54d641bac50c667d4cdbae7f451248),(64,0xc5a931ae4c64a492490d755364290d577a4f3e45319a1b71),(45,0x180c9fbfd12492422b320df89865b1432f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pf:∀ ns ∈ vD, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vE:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x2492422b320dfccba28669097b19a1ae4ca4529249243596),(64,0x4a2c605663f7ee7cca32ecf5329e4924909458c064fccb11),(64,0x87424924835758c074eadeb7d8d9d587e3ad3a626f249248),(64,0x956e492490628aa3110afe8dbc9bbf324e6e8a68acc6c529),(64,0x9b192aba9ae4cb53a12492435564710d9f343f4e6cae7532),(64,0x302d8dbe196d50c972bf39799f12492423d56413ef3e5ca3)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pg:∀ ns ∈ vE, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vF:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0xae18ff18cd72f3a71d3c43111147184420211fd1c8a5d9697481942111114719),(64,0x9c1fc6b43642111110561a13110111f29c1bde5fd6971c3d6111115181841102),(64,0x1fb782f66111110571941101bdb496aa1ee7942e643111104619344201bd94f6),(64,0x1111027196362205c28e18ea3a95d82f4931942111110671a741101121bd86ed),(25,0x402fb188a13ff5d92f4961943)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Ph:∀ ns ∈ vF, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vG:List NodeSpec:=readDeltaNodes 8 (varNats 3 (unpackWords 4 [(64,0x78f7ce2fe2f493394311110361962201542eb7dd4895fd69771d211111041919),(64,0x97d411111110211a43313201339819af5ae28d79784396111110718191810399),(64,0x1ac7b3af3c3c1b2a421111103191a06f22af6fa19f879785843111101718505c),(64,0x81b3d43111102619206a2cb1eac3af2e4a18d42111110261918202c91abd5d7b),(15,0x207e6fa6fe3dc77)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pi:∀ ns ∈ vG, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vH:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x71531240936aff650fef6e6e54fdcd7265e9b0924920d716),(64,0x6aab129027da759dcb89ba43b373abab9cc9ccdc924920d),(64,0xd0de5724a0d4512242b393a65b43e46e732687bbcd849249),(64,0x5da0515f7849d21f71b2925121a8a3414bb98bdd093343e3),(64,0x20e5563d288272caa1fcc92950fdcd726523a6c249248356),(64,0x849249072eb1ecd482f3e264d8db8ecdce64d0f5b2949249),(47,0xcd2902ffc7ef4ed8e94ccf436e26599e88d)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pj:∀ ns ∈ vH, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vI:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x85124839454dd7536d5292492402b1baea6d8a5249248056),(64,0x3be24924830f54f66a40df15d8efb1de1d4cba99677a1d0d),(64,0x5552499afe4c9e2be1449201ca1e96064b53b6f51ceedef4),(64,0x7b7531ba1449201aa34092fdaac77cc7bbb993a979249243),(52,0x409f0b9ff33ec4cda99aaea52892423d624cde4)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pk:∀ ns ∈ vI, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def vJ:List NodeSpec:=readDeltaNodes 1 (varNats 2 (unpackWords 3 [(44,0x2419712f5fd5d4d931d72ea5289243396)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pl:∀ ns ∈ vJ, Impossible A 11 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I bD (by decide +kernel)
def Pm:BT (List (List Nat)):=refBuckets C [vx,vy,vz,vA,vB,vC,vD,vE,vF,vG,vH,vI,vJ] #[1510187048,27,1610936371,0,72,69633,0,49,0,0,54,106508,1577230375,327703,1040404525,59,87,8,0,311332,48,92,0,1493516309,155680,0,60,299030,218148866,167970,1308700675,68,1241657360,282667,0,922927129,331837,81938,10,0,47,29,348184,91,266255,307230,6529524965390,0,50,290853,97,0,229422,135175,57,1443102726,93,213001,315397,274495,360479,82,1392623620,0]
set_option maxRecDepth 20000 in
lemma db:btAll (fun bk => ∀ xs ∈ bk, Impossible A 11 xs.toFinset) Pm:=refBuckets_all (forall_cons OZ (forall_cons Pa (forall_cons Pb (forall_cons Pc (forall_cons Pd (forall_cons Pe (forall_cons Pf (forall_cons Pg (forall_cons Ph (forall_cons Pi (forall_cons Pj (forall_cons Pk (forall_cons Pl (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def vK:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x249409ea984dcaf48c249250072a83aa524a35924924a3d5),(64,0x4e58c242c79ea66565175c92492418aac0e351a6f5aa509),(64,0x8d541371d11bd5e61f89249209ea8371dc957199c249249),(57,0x204d27c37a9955c9249211eaa064871bcfccfe4a249)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pn:∀ ns ∈ vK, Impossible A 12 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I db (by decide +kernel)
def vL:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0xa4a96f373312249249ca2a59242b9b3ad30fa5124924e395),(64,0x21551630b2127bc3f4efd59f879e8924920d516514250739),(64,0xca55f124924287aa6148a2413a5a7bf69b653b330fa89249),(64,0x9ee3d5971d9987e45124834f54c48944398dc64b8fd739d4),(64,0xda1f73915f8f94fe8924920d5560a799fe4924904aa9b20a),(17,674564017887410)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Po:∀ ns ∈ vL, Impossible A 12 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I db (by decide +kernel)
def vM:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x35454d48944296e52c77636573ac7c2a3a79d092492145d5),(64,0xbcd30e30924920d3d62c9049a7d8bef8dfeb94f5a9849249),(64,0x24a0bc33e9d43b9b4f54c449242872a798486e5b4e969f3b),(64,0x79aa1ec94482bc57656de6db97f9e8753092492143d664d),(64,0x9d5da1bd4af985124834e5542792819fee8f8763cf863249),(64,0x414ee73fc3e4eb694f729e7d3112490728aac7921deaeca4),(5,7753)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pp:∀ ns ∈ vM, Impossible A 12 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I db (by decide +kernel)
def vN:List NodeSpec:=readDeltaNodes 8 (varNats 2 (unpackWords 3 [(64,0x4552492835152c9093bb1faf325e6ff5ca79b0924920d515),(64,0x6483bfa4e45e9e9932ca944920e3d5681bd6fe126ca65325),(64,0x2492433d530c6483edcbfd893bf3e3d0e8aa24920e3d530c),(64,0xe6eefe32799cc7bd1785124839451a0d7db1276ae6327721),(64,0x41fb8ebb1dbbda9db1967729ee9b0924920f51630c2c826e),(52,0x3d985204992632eddca79fa9249241e72a7b30a)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pq:∀ ns ∈ vN, Impossible A 12 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I db (by decide +kernel)
def vO:List NodeSpec:=readDeltaNodes 2 (varNats 2 (unpackWords 3 [(64,0x7a2ea5289241e7aa520fec4bbf729dd0c9ccf0924920c515),(31,0x6185121fc6ddcca67cb6d8f)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pr:∀ ns ∈ vO, Impossible A 12 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I db (by decide +kernel)
def Ps:BT (List (List Nat)):=refBuckets C [vK,vL,vM,vN,vO] #[25,1,11,21,19,0,0,0,0,0,20,0,22,14,0,29,0,18,0,31,0,0,0,17,0,9,0,0,5,0,7,0,0,0,24,16,28,49156,15,0,0,23,30,27,0,26,0,0,131082,0,0,8,0,6,33,0,0,0,12290,13,0,34,0,0]
set_option maxRecDepth 20000 in
lemma Pt:btAll (fun bk => ∀ xs ∈ bk, Impossible A 12 xs.toFinset) Ps:=refBuckets_all (forall_cons Pn (forall_cons Po (forall_cons Pp (forall_cons Pq (forall_cons Pr (fun _ h => (List.not_mem_nil h).elim))))))
def vP:List NodeSpec:=readDeltaNodes 6 (varNats 2 (unpackWords 3 [(64,0x3b6c76e7d08924920f3d530906d32b8eab5944924920c515),(64,0xaa1389282f57de1fec7723cc24924850e54d48961da6698d),(64,0x6fc52144921739430c2890b5f4de7dee132d4a9249241e7a),(64,0x44941f99dd3a2e48fe3de8a524924851454a49124904bee4),(3,98)]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Pu:∀ ns ∈ vP, Impossible A 13 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I Pt (by decide +kernel)
def Pv:BT (List (List Nat)):=refBuckets C [vP] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,4,0,0,0,0,0,0,0,0,0,0,5,0,0,0]
set_option maxRecDepth 20000 in
lemma Pw:btAll (fun bk => ∀ xs ∈ bk, Impossible A 13 xs.toFinset) Pv:=refBuckets_all (forall_cons Pu (fun _ h => (List.not_mem_nil h).elim))
def vQ:List NodeSpec:=readDeltaNodes 1 (unpackWords 6 [(25,0x108208508009f5cae420010410410410071c8)])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma Px:∀ ns ∈ vQ, Impossible A 14 (nodeValsBT C ns).toFinset:=blockOk J 12 (by decide) F H K I Pw (by decide +kernel)
def Py:BT (List (List Nat)):=refBuckets C [vQ] #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]
set_option maxRecDepth 20000 in
lemma Pz:btAll (fun bk => ∀ xs ∈ bk, Impossible A 14 xs.toFinset) Py:=refBuckets_all (forall_cons Px (fun _ h => (List.not_mem_nil h).elim))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma PG:Lower E A 15:=lower_of_forestBT (essPairs:=[(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65),(VAR 7,1,129)]) (by decide +kernel) Pz (by decide +kernel)


def edgeFn (x : Fin 8 → Bool) : Bool:=(x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
def edgeList:List Nat:=[0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7]
def graphFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)
def witness:List Gate:=[⟨.or,[1,3]⟩,⟨.or,[2,4]⟩,⟨.or,[3,6]⟩,⟨.or,[1,7]⟩,⟨.or,[6,7]⟩,⟨.or,[0,9]⟩,⟨.or,[5,12]⟩,⟨.and,[10,11]⟩,⟨.and,[13,14]⟩,⟨.and,[0,9]⟩,⟨.and,[2,4]⟩,⟨.and,[8,12]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩]
theorem witnessBasis:∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2:=by
  simp [witness]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem graphCorrect:∀ x : Fin 8 → Bool, edgeFn x = graphFn x:=by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tableCorrect:∀ r : Row, edgeFn (evalInput r) = A.testBit r.val:=by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect:∀ r : Row, Circuit.eval ⟨witness,23⟩ (List.ofFn (evalInput r)) = A.testBit r.val:=by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem conclude (gates : List Gate) (o : Nat) (legal : (∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2))
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = graphFn x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length ≤ gates.length ∧
    ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = graphFn x:=by
  have eq : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeFn x :=
    fun x => (spec x).trans (graphCorrect x).symm
  obtain ⟨gs,out,legal',size,compute⟩:=replace_of_lower A (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 15 PG witness 23 (by decide) witnessBasis edgeFn tableCorrect
    witnessCorrect gates o legal eq
  exact ⟨gs,out,legal',size,fun x => (compute x).trans (graphCorrect x)⟩

end PEqualNP.Outside.L_meta_52830

theorem PEqualNP.Outside.L_meta_52830 :
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true):=by
  intro gates o legal _ spec
  exact PEqualNP.Outside.L_meta_52830.conclude gates o legal spec

