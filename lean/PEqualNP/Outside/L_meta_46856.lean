import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_46856
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
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
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
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
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
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
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
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
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
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
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
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
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
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
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
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
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
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
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
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
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
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
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
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
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
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
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
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
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
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
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
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
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
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
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
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
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
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
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
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
  have hltc : ∀ x ∈ child, x < 2^128 := by
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
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
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
      have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
        intro x hx
        have h1 := permWord_eq_renameW sw hsv x hx
        have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
        rw [h2, h1]
        apply Nat.eq_of_testBit_eq; intro r
        by_cases hrr : r < 128
        · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
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
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 63) % 128, Nat.mod_lt _ (by decide)⟩

lemma map_available (f : Row → Row) {b c : List Wire}
    (cover : ∀ w ∈ b, Avail c (restrictW f w)) {w : Wire} (hw : Avail b w) :
    Avail c (restrictW f w) := by
  rcases hw with hb | ⟨bit,rfl⟩ | hi
  · exact cover _ hb
  · exact Or.inr (Or.inl ⟨bit,rfl⟩)
  · have h : Avail c (invW (restrictW f w)) := cover _ hi
    simpa only [invW_inv] using avail_inv h

lemma map_reach (f : Row → Row) {R S : List Wire}
    (cover : ∀ w ∈ R, Avail S (restrictW f w)) {p b} (hr : Reach R p b) :
    ∃ c, Reach S p c ∧ ∀ w ∈ b, Avail c (restrictW f w) := by
  induction p generalizing b with
  | zero =>
    have hb : b = R := hr
    exact ⟨S,rfl,hb.symm ▸ cover⟩
  | succ p ih =>
    obtain ⟨op,b,a,d,prev,ha,hd,rfl⟩ := hr
    obtain ⟨c,hc,hmap⟩ := ih prev
    let w := comb2 op (restrictW f a) (restrictW f d)
    have eq : restrictW f (comb2 op a d) = w := by cases op <;> rfl
    refine ⟨w :: c,⟨op,c,_,_,hc,map_available f hmap ha,map_available f hmap hd,rfl⟩,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hold
    · rw [eq]
      exact Or.inl List.mem_cons_self
    · exact avail_cons w (hmap t hold)

lemma dualLower {roots : List Nat} {T G L : Nat}
    (hvars : ∀ r : Row, roots.all (fun a => decide (obs a (dualRow r) = !(obs a r))) = true)
    (hgoal : ∀ r : Row, (!(obs T (dualRow r))) = obs G r)
    (prior : Lower roots G L) : Lower roots T L := by
  intro p bank hr hav
  have maps (w : Wire) (hw : w ∈ roots.map obs) : Avail (roots.map obs) (restrictW dualRow w) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have eq : restrictW dualRow (obs a) = invW (obs a) :=
      funext fun r => of_decide_eq_true (List.all_eq_true.mp (hvars r) a ha)
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨c,hc,hmap⟩ := map_reach dualRow maps hr
  have eq : invW (restrictW dualRow (obs T)) = obs G := funext hgoal
  exact prior p c hc (eq ▸ avail_inv (map_available dualRow hmap hav))

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
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

def cert0 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def cert22 : List Nat := varsOf 14
def cert191 : List Nat := [6,6,10,10,12,12,6,10,12]
def cert174 : List Nat := [4,2,8,2,8,4,8,4,2]
def cert128 : Nat := fullMask 9
def cert47 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def cert227 : List (Nat × Nat × Nat) := []
def cert32 : Array Decor := buildWires cert47 cert227
def cert40 : Array (List (Nat × Nat)) := #[]
def cert219 : List (Nat × Nat) := []
def cert221 : Array (Nat × Nat) := cert219.toArray
def cert195 : List PoolSpec := []
def cert14 : Array (Option BoundPool) := buildPools cert32 cert22 cert221 cert195
lemma cert140 : goodPairs cert0 cert191 cert174 := goodPairs_of (by decide +kernel)
lemma cert48 : ∀ x ∈ cert47, faithful cert191 cert174 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert33 : ∀ x ∈ cert32.toList, faithful cert191 cert174 x ∧ x.1 < 2^128 := buildWires_faithful cert48
lemma cert41 : ∀ sw ∈ cert40.toList, swapsValid sw = true ∧ permWord sw cert0 = cert0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert222 : ∀ i (hi : i < cert221.size), Slice cert22 cert0 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert22 cert0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert15 : ∀ i (hi : i < cert14.size), ∀ c, cert14[i] = some c → ValidPool cert22 cert0 c := buildPools_sound cert222
def cert61 : Array (List (List Nat)) := #[]
lemma cert62 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert0 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
def cert178 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert99 : checkNodes cert32 cert0 cert128 cert14 cert40 cert61 0 cert178 = true := by decide +kernel
def cert55 : Array (List (List Nat)) := buildBuckets 1 cert32 cert178
lemma cert56 : ∀ i (hi : i < cert55.size), ∀ xs ∈ cert55[i], Impossible cert0 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert140 cert33 cert15 cert41 cert62 cert99
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert100 : checkNodes cert32 cert0 cert128 cert14 cert40 cert55 1 cert178 = true := by decide +kernel
lemma cert57 : ∀ i (hi : i < cert55.size), ∀ xs ∈ cert55[i], Impossible cert0 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert140 cert33 cert15 cert41 cert56 cert100
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert101 : checkNodes cert32 cert0 cert128 cert14 cert40 cert55 2 cert178 = true := by decide +kernel
lemma cert58 : ∀ i (hi : i < cert55.size), ∀ xs ∈ cert55[i], Impossible cert0 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert140 cert33 cert15 cert41 cert57 cert101
def cert179 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert102 : checkNodes cert32 cert0 cert128 cert14 cert40 cert55 3 cert179 = true := by decide +kernel
def cert59 : Array (List (List Nat)) := buildBuckets 1 cert32 cert179
lemma cert60 : ∀ i (hi : i < cert59.size), ∀ xs ∈ cert59[i], Impossible cert0 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert140 cert33 cert15 cert41 cert58 cert102
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert133 : forestRootCheck cert22 cert0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert132 : bucketContains cert59 cert22 = true := by decide +kernel
lemma cert144 : Lower cert22 cert0 4 := lower_of_forest cert133 cert60 cert132
def cert11 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def cert29 : List Nat := varsOf 22
lemma cert163 : carryOK [(3,4)] cert29 cert11 cert22 cert0 = true := by decide +kernel
lemma cert162 : Lower cert29 cert11 4 := carry_of cert163 cert144
def cert12 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def cert30 : List Nat := varsOf 42
lemma cert165 : carryOK [(3,5),(2,3),(2,4)] cert30 cert12 cert22 cert0 = true := by decide +kernel
lemma cert164 : Lower cert30 cert12 4 := carry_of cert165 cert144
def cert13 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def cert31 : List Nat := varsOf 44
lemma cert167 : carryOK [(3,5),(2,3),(1,2),(1,4)] cert31 cert13 cert22 cert0 = true := by decide +kernel
lemma cert166 : Lower cert31 cert13 4 := carry_of cert167 cert144
def cert1 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def cert23 : List Nat := varsOf 30
lemma cert146 : liftCheck 0 16 cert23 cert1 cert22 cert0 [(VAR 4,22,6)] = true := by decide +kernel
lemma cert145 : Lower cert23 cert1 5 := lift_of cert146 cert144
def cert2 : Nat := 0xffc0ffc0c000c000ffc0ffc0c000c000
def cert24 : List Nat := varsOf 46
lemma cert148 : liftCheck 0 2 cert24 cert2 cert31 cert13 [(VAR 1,14,12)] = true := by decide +kernel
lemma cert147 : Lower cert24 cert2 5 := lift_of cert148 cert166
def cert3 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def cert25 : List Nat := varsOf 60
def cert192 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def cert175 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def cert129 : Nat := fullMask 21
def cert49 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def cert34 : Array Decor := buildWires cert49 cert227
def cert16 : Array (Option BoundPool) := buildPools cert34 cert25 cert221 cert195
lemma cert141 : goodPairs cert3 cert192 cert175 := goodPairs_of (by decide +kernel)
lemma cert50 : ∀ x ∈ cert49, faithful cert192 cert175 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert35 : ∀ x ∈ cert34.toList, faithful cert192 cert175 x ∧ x.1 < 2^128 := buildWires_faithful cert50
lemma cert42 : ∀ sw ∈ cert40.toList, swapsValid sw = true ∧ permWord sw cert3 = cert3 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert223 : ∀ i (hi : i < cert221.size), Slice cert25 cert3 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert25 cert3 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert17 : ∀ i (hi : i < cert16.size), ∀ c, cert16[i] = some c → ValidPool cert25 cert3 c := buildPools_sound cert223
lemma cert69 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert3 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert103 : checkNodes cert34 cert3 cert129 cert16 cert40 cert61 0 cert178 = true := by decide +kernel
def cert63 : Array (List (List Nat)) := buildBuckets 1 cert34 cert178
lemma cert64 : ∀ i (hi : i < cert63.size), ∀ xs ∈ cert63[i], Impossible cert3 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert141 cert35 cert17 cert42 cert69 cert103
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert104 : checkNodes cert34 cert3 cert129 cert16 cert40 cert63 1 cert178 = true := by decide +kernel
lemma cert65 : ∀ i (hi : i < cert63.size), ∀ xs ∈ cert63[i], Impossible cert3 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert141 cert35 cert17 cert42 cert64 cert104
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert105 : checkNodes cert34 cert3 cert129 cert16 cert40 cert63 2 cert178 = true := by decide +kernel
lemma cert66 : ∀ i (hi : i < cert63.size), ∀ xs ∈ cert63[i], Impossible cert3 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert141 cert35 cert17 cert42 cert65 cert105
def cert180 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert106 : checkNodes cert34 cert3 cert129 cert16 cert40 cert63 3 cert180 = true := by decide +kernel
def cert67 : Array (List (List Nat)) := buildBuckets 1 cert34 cert180
lemma cert68 : ∀ i (hi : i < cert67.size), ∀ xs ∈ cert67[i], Impossible cert3 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert141 cert35 cert17 cert42 cert66 cert106
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert135 : forestRootCheck cert25 cert3 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert134 : bucketContains cert67 cert25 = true := by decide +kernel
lemma cert149 : Lower cert25 cert3 4 := lower_of_forest cert135 cert68 cert134
def cert4 : Nat := 0xfffcc000fffcc000fffcc000fffcc000
def cert193 : List Nat := [14,14,14,18,18,20,20,22,24,24,26,28,14,18,18,18,20,20,20,24,24,24]
def cert176 : List Nat := [12,10,6,16,2,16,4,6,16,8,10,12,16,6,10,12,6,10,12,6,10,12]
def cert130 : Nat := fullMask 22
def cert51 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf49f,0x1b6496),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x718e7,0x2da8c5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def cert228 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(0,0,3),(2,0,1),(1,0,1),(1,0,3),(0,0,1),(3,1,9),(0,1,9),(1,6,1),(3,0,1),(3,7,2),(1,7,2),(3,6,1),(3,10,8)]
def cert36 : Array Decor := buildWires cert51 cert228
def cert43 : Array (List (Nat × Nat)) := #[[],[(2,3)],[(1,2)],[(1,3),(1,2)],[(1,2),(1,3)],[(1,3)]]
def cert18 : Array (Option BoundPool) := buildPools cert36 cert23 cert221 cert195
lemma cert142 : goodPairs cert4 cert193 cert176 := goodPairs_of (by decide +kernel)
lemma cert52 : ∀ x ∈ cert51, faithful cert193 cert176 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert37 : ∀ x ∈ cert36.toList, faithful cert193 cert176 x ∧ x.1 < 2^128 := buildWires_faithful cert52
lemma cert44 : ∀ sw ∈ cert43.toList, swapsValid sw = true ∧ permWord sw cert4 = cert4 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert224 : ∀ i (hi : i < cert221.size), Slice cert23 cert4 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert23 cert4 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert19 : ∀ i (hi : i < cert18.size), ∀ c, cert18[i] = some c → ValidPool cert23 cert4 c := buildPools_sound cert224
lemma cert81 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert4 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert107 : checkNodes cert36 cert4 cert130 cert18 cert43 cert61 0 cert178 = true := by decide +kernel
def cert70 : Array (List (List Nat)) := buildBuckets 1 cert36 cert178
lemma cert71 : ∀ i (hi : i < cert70.size), ∀ xs ∈ cert70[i], Impossible cert4 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert81 cert107
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert108 : checkNodes cert36 cert4 cert130 cert18 cert43 cert70 1 cert178 = true := by decide +kernel
lemma cert72 : ∀ i (hi : i < cert70.size), ∀ xs ∈ cert70[i], Impossible cert4 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert71 cert108
def cert181 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert109 : checkNodes cert36 cert4 cert130 cert18 cert43 cert70 2 cert181 = true := by decide +kernel
def cert73 : Array (List (List Nat)) := buildBuckets 1 cert36 cert181
lemma cert74 : ∀ i (hi : i < cert73.size), ∀ xs ∈ cert73[i], Impossible cert4 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert72 cert109
def cert182 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([7,14,2,3],[],[0]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert110 : checkNodes cert36 cert4 cert130 cert18 cert43 cert73 3 cert182 = true := by decide +kernel
def cert75 : Array (List (List Nat)) := buildBuckets 4 cert36 cert182
lemma cert76 : ∀ i (hi : i < cert75.size), ∀ xs ∈ cert75[i], Impossible cert4 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert74 cert110
def cert183 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0,1]),([7,0,1,2,3],[],[0]),([0,1,8,2,3],[],[0]),([0,1,2,3,9],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert111 : checkNodes cert36 cert4 cert130 cert18 cert43 cert75 4 cert183 = true := by decide +kernel
def cert77 : Array (List (List Nat)) := buildBuckets 3 cert36 cert183
lemma cert78 : ∀ i (hi : i < cert77.size), ∀ xs ∈ cert77[i], Impossible cert4 4 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert76 cert111
def cert184 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert112 : checkNodes cert36 cert4 cert130 cert18 cert43 cert77 5 cert184 = true := by decide +kernel
def cert79 : Array (List (List Nat)) := buildBuckets 1 cert36 cert184
lemma cert80 : ∀ i (hi : i < cert79.size), ∀ xs ∈ cert79[i], Impossible cert4 5 xs.toFinset :=
  buildBuckets_sound (by decide) cert142 cert37 cert19 cert44 cert78 cert112
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert137 : forestRootCheck cert23 cert4 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert136 : bucketContains cert79 cert23 = true := by decide +kernel
lemma cert150 : Lower cert23 cert4 6 := lower_of_forest cert137 cert80 cert136
def cert5 : Nat := 0xfffffff0fffff000fffffff0fffff000
lemma cert152 : liftCheck 16 0 cert25 cert5 cert31 cert13 [(VAR 4,16,0)] = true := by decide +kernel
lemma cert151 : Lower cert25 cert5 5 := lift_of cert152 cert166
def cert6 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def cert26 : List Nat := varsOf 54
lemma cert154 : carryOK [(3,4),(3,5)] cert26 cert6 cert23 cert1 = true := by decide +kernel
lemma cert153 : Lower cert26 cert6 5 := carry_of cert154 cert145
def cert7 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000
def cert27 : List Nat := varsOf 58
lemma cert156 : carryOK [(1,2)] cert27 cert7 cert25 cert3 = true := by decide +kernel
lemma cert155 : Lower cert27 cert7 4 := carry_of cert156 cert149
def cert8 : Nat := 0xfffcffc0fffcffc0fffcffc0fffcffc0
lemma cert158 : carryOK [(1,5),(1,4),(1,3),(1,2)] cert23 cert8 cert25 cert5 = true := by decide +kernel
lemma cert157 : Lower cert23 cert8 5 := carry_of cert158 cert151
def cert9 : Nat := 0xffffffccffffcc00ffffffccffffcc00
lemma cert160 : carryOK [(1,2)] cert27 cert9 cert25 cert5 = true := by decide +kernel
lemma cert159 : Lower cert27 cert9 5 := carry_of cert160 cert151
def cert10 : Nat := 0xfffcffc0fffcc000fffcffc0fffcc000
def cert28 : List Nat := varsOf 62
def cert194 : List Nat := [14,14,14,18,18,20,20,22,24,24,26,28,38,38,38,40,40,42,42,44,44,50,50,52,52,56,14,14,14,18,18,18,18,18,18,20,20,20,20,20,20,24,24,24,24,24,24,38,38,38,40,40,40,40,40,40]
def cert177 : List Nat := [12,10,6,16,2,16,4,6,16,8,10,12,36,34,6,32,8,34,10,36,12,48,34,48,36,48,34,36,48,6,10,12,34,36,48,6,10,12,34,36,48,6,10,12,34,36,48,10,12,48,6,10,12,34,36,48]
def cert131 : Nat := fullMask 56
def cert53 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x38007fc66749f,0x2c965964466496),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f81d9878e7,0x552aaaa91858c5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7e001e1f8f07,0x198c30c0150e03),(0xffff0000ffff0000ffff0000ffff0000,0x7fffe3e00ff8,0x82410412a00128),(0xffffffff00000000ffffffff00000000,0xff800003fff000,0xe271c71feab000)]
def cert229 : List (Nat × Nat × Nat) := [(1,2,3),(2,0,4),(3,0,3),(0,2,3),(1,0,4),(1,0,3),(0,0,3),(1,3,4),(3,0,2),(3,3,4),(2,2,3),(0,0,2),(2,0,2),(1,2,4),(1,0,2),(2,3,4),(2,2,4),(0,0,1),(1,0,1),(3,2,3),(2,0,3),(2,0,1),(1,21,3),(3,21,0),(3,3,18),(1,1,2),(3,15,0),(2,1,2),(2,0,5),(0,0,5),(1,0,8),(0,1,9),(0,0,12),(2,0,8),(1,7,4),(1,7,2),(1,26,2),(2,22,2),(3,16,1),(3,13,1),(3,2,10),(2,1,4),(1,11,2),(3,11,1),(2,22,3),(1,11,1),(0,0,18),(0,1,19),(1,13,1),(1,1,3),(2,23,2),(1,17,1),(1,11,4),(2,19,4),(3,11,2),(2,1,3),(1,22,2),(3,22,2),(1,8,4),(3,6,1),(1,22,3),(0,1,10),(1,17,3),(3,17,1),(1,24,4),(3,1,10),(3,0,1),(1,22,4),(1,6,3),(1,16,3),(1,28,3),(1,51,3),(1,21,7),(3,7,18),(3,21,10),(0,10,18),(3,46,10),(3,11,18),(2,47,4),(1,66,4),(1,47,4),(3,37,1),(2,61,4),(1,66,2),(1,17,13),(3,17,54),(3,17,10),(1,21,26),(3,22,23),(3,16,54),(3,32,0),(3,46,0),(0,0,30),(1,64,3),(1,68,3),(1,43,3),(3,21,1),(1,21,11),(3,26,18),(1,32,26),(3,21,23),(3,22,12),(1,21,22),(0,23,18),(3,66,2),(3,22,5),(3,22,19),(3,2,65),(0,22,12),(1,42,3),(3,22,18),(1,49,2),(1,61,3),(2,61,3),(0,61,4),(1,15,22),(2,88,4),(1,113,2),(1,93,2),(2,93,4),(3,93,2),(1,119,3),(1,93,4),(3,14,61),(2,23,61),(0,93,2),(0,61,12),(3,62,23),(3,124,2),(1,129,4),(1,124,2)]
def cert38 : Array Decor := buildWires cert53 cert229
def cert45 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def cert220 : List (Nat × Nat) := [(subcube 0 2,5),(subcube 32 0,6),(subcube 16 4,4),(subcube 0 32,5),(subcube 4 0,4),(subcube 0 4,5),(subcube 8 0,5),(subcube 2 0,4),(subcube 16 2,4),(subcube 8 32,4),(subcube 16 0,5)]
def cert225 : Array (Nat × Nat) := cert220.toArray
def cert196 : List PoolSpec := [(0,[]),(1,[(0,0,1),(1,0,1),(3,22,23)]),(2,[]),(1,[]),(3,[]),(4,[]),(5,[]),(1,[(2,0,3),(3,0,3)]),(6,[]),(7,[]),(8,[]),(1,[(0,0,3),(1,11,2)]),(1,[(1,0,3),(0,1,10)]),(9,[]),(1,[(0,0,3),(1,11,1)]),(1,[(0,0,3),(3,11,1)]),(1,[(2,1,2),(3,32,0)]),(10,[]),(1,[(0,0,3),(1,21,11)]),(1,[(1,0,3),(3,1,10)]),(1,[(0,0,1),(1,0,1)]),(1,[(1,21,3)]),(1,[(3,21,0)]),(1,[(3,3,18)]),(1,[(2,2,3)]),(1,[(1,1,2)]),(1,[(1,0,2)]),(1,[(1,2,3)]),(1,[(1,0,1)]),(1,[(2,0,1),(1,26,2)]),(1,[(1,0,3)]),(1,[(1,0,3),(3,2,10)]),(1,[(0,0,3)]),(1,[(2,1,2)]),(1,[(0,0,18)]),(1,[(2,0,2)]),(1,[(0,0,1)]),(1,[(0,0,2)]),(1,[(2,0,1)]),(1,[(2,0,3)]),(1,[(3,6,1)]),(1,[(2,0,2),(3,17,1)]),(1,[(3,0,3)]),(1,[(2,0,1),(3,0,1)])]
def cert20 : Array (Option BoundPool) := buildPools cert38 cert28 cert225 cert196
lemma cert143 : goodPairs cert10 cert194 cert177 := goodPairs_of (by decide +kernel)
lemma cert54 : ∀ x ∈ cert53, faithful cert194 cert177 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert39 : ∀ x ∈ cert38.toList, faithful cert194 cert177 x ∧ x.1 < 2^128 := buildWires_faithful cert54
lemma cert46 : ∀ sw ∈ cert45.toList, swapsValid sw = true ∧ permWord sw cert10 = cert10 := autos_of (by decide +kernel)
lemma cert198 : sliceDirectCheck 0 2 0 cert28 cert10 cert25 cert5 = true := by decide +kernel
lemma cert197 : Slice cert28 cert10 (subcube 0 2) 5 := slice_direct cert198 cert151
lemma cert202 : sliceDirectCheck 32 0 0 cert28 cert10 cert23 cert4 = true := by decide +kernel
lemma cert199 : Slice cert28 cert10 (subcube 32 0) 6 := slice_direct cert202 cert150
lemma cert204 : sliceDirectCheck 16 4 0 cert28 cert10 cert30 cert12 = true := by decide +kernel
lemma cert203 : Slice cert28 cert10 (subcube 16 4) 4 := slice_direct cert204 cert164
lemma cert206 : sliceDirectCheck 0 32 0 cert28 cert10 cert23 cert8 = true := by decide +kernel
lemma cert205 : Slice cert28 cert10 (subcube 0 32) 5 := slice_direct cert206 cert157
lemma cert208 : sliceDirectCheck 4 0 0 cert28 cert10 cert27 cert7 = true := by decide +kernel
lemma cert207 : Slice cert28 cert10 (subcube 4 0) 4 := slice_direct cert208 cert155
lemma cert210 : sliceDirectCheck 0 4 0 cert28 cert10 cert27 cert9 = true := by decide +kernel
lemma cert209 : Slice cert28 cert10 (subcube 0 4) 5 := slice_direct cert210 cert159
lemma cert212 : sliceDirectCheck 8 0 0 cert28 cert10 cert26 cert6 = true := by decide +kernel
lemma cert211 : Slice cert28 cert10 (subcube 8 0) 5 := slice_direct cert212 cert153
lemma cert214 : sliceDirectCheck 2 0 0 cert28 cert10 cert25 cert3 = true := by decide +kernel
lemma cert213 : Slice cert28 cert10 (subcube 2 0) 4 := slice_direct cert214 cert149
lemma cert216 : sliceDirectCheck 16 2 0 cert28 cert10 cert31 cert13 = true := by decide +kernel
lemma cert215 : Slice cert28 cert10 (subcube 16 2) 4 := slice_direct cert216 cert166
lemma cert218 : sliceDirectCheck 8 32 0 cert28 cert10 cert29 cert11 = true := by decide +kernel
lemma cert217 : Slice cert28 cert10 (subcube 8 32) 4 := slice_direct cert218 cert162
lemma cert201 : sliceDirectCheck 16 0 0 cert28 cert10 cert24 cert2 = true := by decide +kernel
lemma cert200 : Slice cert28 cert10 (subcube 16 0) 5 := slice_direct cert201 cert147
set_option maxRecDepth 200000 in
lemma cert226 : ∀ i (hi : i < cert225.size), Slice cert28 cert10 cert225[i].1 cert225[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert28 cert10 p.1 p.2) (forall_cons cert197 (forall_cons cert199 (forall_cons cert203 (forall_cons cert205 (forall_cons cert207 (forall_cons cert209 (forall_cons cert211 (forall_cons cert213 (forall_cons cert215 (forall_cons cert217 (forall_cons cert200 (fun _ h => (List.not_mem_nil h).elim))))))))))))
lemma cert21 : ∀ i (hi : i < cert20.size), ∀ c, cert20[i] = some c → ValidPool cert28 cert10 c := buildPools_sound cert226
lemma cert98 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert10 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert113 : checkNodes cert38 cert10 cert131 cert20 cert45 cert61 0 cert178 = true := by decide +kernel
def cert82 : Array (List (List Nat)) := buildBuckets 1 cert38 cert178
lemma cert83 : ∀ i (hi : i < cert82.size), ∀ xs ∈ cert82[i], Impossible cert10 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert98 cert113
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert114 : checkNodes cert38 cert10 cert131 cert20 cert45 cert82 1 cert178 = true := by decide +kernel
lemma cert84 : ∀ i (hi : i < cert82.size), ∀ xs ∈ cert82[i], Impossible cert10 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert83 cert114
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert115 : checkNodes cert38 cert10 cert131 cert20 cert45 cert82 2 cert178 = true := by decide +kernel
lemma cert85 : ∀ i (hi : i < cert82.size), ∀ xs ∈ cert82[i], Impossible cert10 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert84 cert115
def cert185 : List NodeSpec := [([93,133,3,4],[],[]),([93,2,3,134],[],[]),([93,135,3,4],[],[]),([129,125,3,4],[],[]),([62,123,3,4],[],[]),([87,93,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert116 : checkNodes cert38 cert10 cert131 cert20 cert45 cert82 3 cert185 = true := by decide +kernel
def cert86 : Array (List (List Nat)) := buildBuckets 3 cert38 cert185
lemma cert87 : ∀ i (hi : i < cert86.size), ∀ xs ∈ cert86[i], Impossible cert10 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert85 cert116
def cert186 : List NodeSpec := [([121,0,66,2,3],[],[]),([17,66,88,3,4],[],[]),([89,1,56,3,4],[],[]),([0,1,122,3,12],[],[]),([110,0,1,2,12],[],[]),([22,105,2,3,4],[],[]),([115,23,2,3,4],[],[]),([22,2,123,3,4],[0],[0]),([21,93,2,3,4],[],[]),([93,2,3,4,18],[],[]),([124,93,2,3,4],[1],[0]),([28,66,2,3,4],[],[]),([93,125,2,3,4],[],[0]),([93,2,123,3,4],[],[]),([0,1,2,61,126],[],[]),([93,2,3,4,72],[],[]),([112,0,1,2,12],[],[]),([93,2,3,4,127],[],[]),([17,1,2,65,12],[2],[]),([17,109,66,3,4],[],[]),([0,1,2,128,3],[],[]),([93,2,61,3,4],[1],[0]),([55,62,22,3,4],[],[]),([37,1,2,65,12],[2],[]),([0,1,2,117,12],[3],[]),([129,22,2,3,4],[],[]),([93,62,2,3,4],[0],[0]),([55,22,61,3,4],[],[]),([129,93,2,3,4],[1],[0]),([87,22,23,2,3],[],[0]),([0,1,2,114,12],[],[]),([130,93,2,3,4],[],[]),([0,1,2,131,3],[3],[]),([22,132,2,3,4],[],[]),([0,1,61,5,12],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert117 : checkNodes cert38 cert10 cert131 cert20 cert45 cert86 4 cert186 = true := by decide +kernel
def cert88 : Array (List (List Nat)) := buildBuckets 12 cert38 cert186
lemma cert89 : ∀ i (hi : i < cert88.size), ∀ xs ∈ cert88[i], Impossible cert10 4 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert87 cert117
def cert168 : List NodeSpec := [([0,1,2,3,75,4],[],[]),([0,1,2,3,76,4],[4,5,6],[]),([77,0,1,2,3,4],[3],[]),([7,51,1,2,3,4],[4],[]),([0,78,1,2,3,4],[3],[]),([0,1,2,3,79,4],[],[]),([0,1,2,3,80,4],[],[]),([0,1,2,3,81,4],[0],[]),([21,25,7,1,2,4],[7],[]),([0,1,2,67,5,4],[3],[]),([82,0,1,2,3,4],[8,3],[]),([21,0,1,47,3,4],[3],[]),([0,1,47,3,4,18],[9,10],[]),([32,22,2,19,3,4],[0,8],[]),([83,0,1,47,3,4],[11],[]),([0,66,2,3,4,84],[],[]),([0,1,47,3,4,85],[9,10],[]),([86,0,1,2,3,12],[],[]),([14,42,0,1,2,3],[],[]),([28,1,2,3,10,4],[],[0]),([87,0,1,2,61,3],[3],[]),([22,23,2,3,4,72],[5],[0]),([0,1,2,88,3,4],[5,3,4],[]),([48,0,2,3,4,18],[],[]),([0,50,2,3,4,18],[9,10],[]),([26,71,2,3,4,18],[],[0]),([0,66,2,88,3,4],[0,2,5,12],[0]),([17,89,1,3,4],[0,9,10,13],[0]),([0,1,2,90,3,4],[0],[]),([17,1,2,91,3,4],[],[]),([21,0,50,2,3,4],[14],[]),([21,48,0,2,3,4],[15],[]),([14,0,68,1,2,3],[],[]),([0,68,2,3,54,4],[9],[]),([92,0,1,2,3,4],[],[]),([93,22,2,3,4],[0,2,5,1],[0]),([94,0,1,2,3,4],[0],[]),([17,13,1,56,3,4],[9],[0]),([95,1,2,19,3,4],[16],[]),([33,0,1,2,5,12],[10],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert119 : checkNodes cert38 cert10 cert131 cert20 cert45 cert88 5 cert168 = true := by decide +kernel
def cert169 : List NodeSpec := [([96,1,2,3,10,4],[5],[]),([97,1,2,19,3,4],[],[]),([25,7,1,2,4,18],[],[]),([0,1,2,3,98,4],[0],[]),([0,1,2,74,54,4],[8],[]),([0,68,1,2,3,12],[],[]),([0,1,2,3,99,4],[0],[]),([14,43,0,1,2,3],[],[]),([43,0,2,3,54,4],[9],[]),([17,66,2,3,4],[2,0,10],[0]),([0,1,2,3,100,4],[0],[]),([26,0,101,2,3,4],[],[]),([102,0,1,2,3,4],[17,18],[]),([0,1,103,2,3,4],[],[]),([32,104,0,2,3,4],[6],[]),([0,1,105,2,3,4],[],[0]),([106,0,1,2,3,4],[4],[]),([22,0,1,2,5,12],[13,2,10],[0]),([107,0,1,2,3,4],[4],[]),([0,1,108,2,3,4],[],[]),([17,66,1,2,3,4],[2,8],[]),([109,0,66,2,3,4],[0,2,5],[0]),([110,0,1,2,3,4],[],[0]),([14,17,22,1,2,3],[13,2],[]),([51,1,23,2,3,4],[5],[]),([21,70,0,2,3,4],[19],[]),([17,22,1,2,3,12],[13,2],[0]),([22,23,2,61,3,4],[5,0,20],[0]),([17,32,22,2,3,4],[0,6,8],[]),([22,23,2,3,4,18],[5],[0]),([111,22,1,2,3,4],[0],[]),([55,22,2,3,4],[0,2],[0]),([34,0,1,2,5,12],[17,13,10],[]),([22,0,1,2,65,12],[2,10],[]),([0,1,2,65,5,4],[2,10,8],[]),([112,0,1,2,3,4],[],[0]),([113,0,1,2,3,12],[13,3,17],[0]),([0,1,2,65,4,12],[2,3],[]),([17,1,2,3,65,4],[2,0],[0]),([0,1,2,3,114,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert120 : checkNodes cert38 cert10 cert131 cert20 cert45 cert88 5 cert169 = true := by decide +kernel
def cert170 : List NodeSpec := [([21,26,71,2,3,4],[],[0]),([0,1,2,65,12],[2,10,3],[0,1]),([115,0,1,2,3,4],[],[0]),([21,22,23,2,3,4],[0,20],[0]),([87,22,0,1,2,3],[],[0]),([15,0,1,61,3,4],[],[]),([0,1,2,116,3,4],[3,4],[]),([17,13,68,1,3,4],[9],[]),([62,22,23,2,3,4],[0,5],[0]),([42,0,1,2,3,12],[17],[0]),([0,66,2,3,4,18],[],[]),([21,0,66,2,3,4],[0,12],[0]),([14,0,1,2,61,3],[3],[0]),([0,1,2,61,3,12],[17,4],[0]),([0,1,2,3,117,4],[6,0,3,4],[0]),([22,37,1,2,3,12],[4,2],[0]),([0,1,2,61,3,4],[3,4],[]),([93,2,3,4],[2,1],[0]),([70,0,2,3,4,18],[],[]),([106,0,1,2,3,12],[17,3],[]),([118,0,1,2,3,4],[3,4],[]),([0,1,2,119,61,3],[4],[0]),([120,0,1,2,3,4],[3,4],[]),([0,1,61,3,5,4],[9,5],[0]),([22,2,19,30,3,4],[8,0],[]),([21,0,1,61,3,4],[3],[]),([0,1,61,3,4,18],[3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert121 : checkNodes cert38 cert10 cert131 cert20 cert45 cert88 5 cert170 = true := by decide +kernel
def cert187 : List NodeSpec := cert168 ++ cert169 ++ cert170
lemma cert118 : checkNodes cert38 cert10 cert131 cert20 cert45 cert88 5 cert187 = true := by
  unfold cert187 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨cert119, cert120⟩, cert121⟩
def cert90 : Array (List (List Nat)) := buildBuckets 36 cert38 cert187
lemma cert91 : ∀ i (hi : i < cert90.size), ∀ xs ∈ cert90[i], Impossible cert10 5 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert89 cert118
def cert171 : List NodeSpec := [([0,1,2,3,27,4],[9,0,21,4,5,6,8],[]),([28,0,1,2,3,4],[4,5,6,3,0,17,9,8,22],[0,1]),([29,0,1,2,3,4],[9,0,5,6,8,3,4,23,13],[]),([15,14,0,1,2,3],[3,24,13,10,2],[]),([22,0,1,2,3,5,4],[8,17,5,2,10,9],[0]),([0,1,2,19,30,3,4],[8,0,6,25,13,26],[0,1]),([15,24,0,1,4],[8,17,2,13],[]),([31,0,1,2,3,4],[8,5,6,9,10,4,3],[]),([14,0,1,2,3,5],[27,13,10,2],[]),([17,32,0,1,2,3,4],[5,0,6,9,8],[0]),([0,1,2,5,12],[2,10,13],[0,1]),([33,0,1,2,3,5,4],[10,9],[0]),([34,0,1,2,3,4],[9,6,5,17,0,8,4,3,10],[]),([32,26,0,2,3,4],[6,0,2,5,8,13],[0]),([0,1,2,3,5,4],[10,2,8,13],[]),([1,2,35,3,4],[8,0,17,13],[]),([21,0,1,23,2,3,4],[4,0,3,28],[0]),([0,36,1,2,3,4],[0,13,17,10],[]),([37,0,1,2,3,4],[4,5,6,8,13,0,3,9,10],[]),([15,22,0,1,2,3,4],[8,5,0,9,6,2,10],[0]),([38,1,2,3,4],[9,2,8,13],[]),([7,0,1,2,3,4,18],[4,3,0],[0]),([0,1,2,3,39],[0,13,17],[]),([0,1,2,40,3,4],[2,0,3,4],[]),([25,0,1,2,3,4,18],[9,4,10],[0]),([25,7,1,2,4],[10,2,7],[0]),([0,1,2,41,3,4],[6,9,0,2,29,4],[]),([21,0,1,2,3,10,4],[0,4,30],[0]),([42,0,1,2,3,4],[5,9,17,4,3],[0]),([0,1,2,3,10,4,18],[0,4],[0]),([43,0,1,2,3,4],[5,0,9,6,17,4,3,8,13],[0]),([44,0,1,2,3,4],[0,8,17,10,3,4,5,13],[]),([45,0,1,2,3,4],[0,5,6,8,10,3,4,31],[]),([46,0,1,2,3,10,4],[0,4,5,6,2],[0]),([21,11,0,1,2,3,4],[4,17,8,3,32],[0]),([24,0,1,2,12],[17,13,2],[]),([11,0,1,2,3,4,18],[8,4,3,17,9,0],[0]),([0,1,2,47,3,4],[2,9,10,11,4],[0]),([32,0,1,2,19,3,4],[0,5,6,8,33,13],[0]),([0,1,47,3,4],[2,9,10,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert123 : checkNodes cert38 cert10 cert131 cert20 cert45 cert90 6 cert171 = true := by decide +kernel
def cert172 : List NodeSpec := [([46,25,0,1,2,3,4],[4,10,9,2],[]),([25,17,1,2,3,4],[8,17,9,10,2],[]),([48,0,2,3,4],[5,2,9,10,15],[0]),([49,0,1,2,3,4],[5,9,8,2,4,3,10],[0]),([0,50,2,3,4],[6,9,10,14],[0]),([51,0,1,2,3,4],[4,5,6,0,3,17,9,13,34],[0]),([0,52,1,2,3,4],[0,6,5,10,4,3],[0,1]),([0,53,2,3,4],[0,6,8,2],[]),([14,17,0,1,2,3],[3,35,13,2,10],[0]),([0,1,2,3,12],[2,13],[]),([17,0,1,2,3,12],[13,2,10],[0]),([17,0,1,2,3,5,4],[10,9,13],[0]),([16,0,1,2,3,54,4],[6,17,8,9,0],[0]),([55,0,1,2,3,4],[0,6,17,2,3,4],[0]),([17,0,1,56,2,3,4],[9,5,0],[0]),([0,1,2,3,57],[9,2,13],[]),([58,0,1,2,3],[0,4,10,13],[]),([22,0,1,2,3,12],[2,10,13,36],[0,1]),([17,0,1,2,3,54,4],[6,9,10],[0]),([14,16,0,1,2,3],[3,37,13,10,2],[0]),([17,0,1,2,3,4],[8,5,6,0,17,10,3,4,9],[]),([59,0,1,3,4],[8,9,2,13],[]),([21,26,0,1,2,3,4],[4,6,3,38],[0]),([21,22,0,1,2,3,4],[4,5,0,9,6,8,3,36],[0]),([60,17,0,1,2,3,4],[5,2,9,0,10],[]),([26,0,1,2,3,4,18],[6,4,9,0],[0]),([17,13,1,3,4],[0,9,10,13],[0]),([21,25,0,1,2,3,4],[4,10,9,3,39],[0]),([0,1,2,61,3,4],[9,0,5,6,17,3,4],[0]),([0,1,23,2,3,4,18],[0,6,4],[0,1]),([62,22,0,1,2,3,4],[0,6,8,5,9],[0]),([0,1,2,3,63],[2,8,4],[]),([17,1,2,3,10,4],[2,0,8,9,10,13],[0]),([22,0,1,2,3,4,12],[17,3,4,5,2,9,0,36],[0]),([0,64,1,2,3,4],[3,0,5,9,13,17,40],[0,1]),([22,0,1,2,3,65,4],[2,10,5],[0]),([0,66,1,2,3,4],[0,5,2,8,4,3],[0]),([33,0,1,2,3,4],[9,6,5,10,4,3],[]),([22,0,1,2,3,4],[6,0,8,5,2,4,3,9],[0]),([22,0,1,2,61,3,4],[5,8,9,0,6,36],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert124 : checkNodes cert38 cert10 cert131 cert20 cert45 cert90 6 cert172 = true := by decide +kernel
def cert173 : List NodeSpec := [([0,1,2,3,67,4],[10,5,6,9,3,4],[0]),([17,0,68,1,2,3,4],[6,5,9,0],[0]),([0,1,2,3,69],[2,13],[]),([22,0,1,2,3,4,18],[8,4,3,5],[0]),([60,16,0,1,2,3,4],[8,2,5,10],[]),([14,22,0,1,2,3],[3,36,2,10,13],[0,1]),([22,23,2,3,4],[0,5,2,20],[0]),([0,68,1,2,3,4],[8,0,5,9,17,4,3,41],[0,1]),([0,1,2,3,5,12],[10,2,13],[]),([21,7,0,1,2,3,4],[0,4,3,42],[0]),([22,1,2,19,3,4],[0,8,10,13,6,9],[0]),([70,0,2,3,4],[0,6,2,19],[0]),([0,66,2,3,4],[0,2,5,10,12],[0]),([26,71,2,3,4],[6,0,2,43],[0]),([0,1,2,3,65,4],[2,10,8,5,3,4],[0,1]),([34,0,1,2,3,5,4],[17,8,0,10,9],[0]),([17,0,1,2,3,67,4],[10,9],[]),([44,0,2,3,4],[0,8,5,10,13],[]),([22,0,1,2,3,4,72],[5,3],[0]),([37,0,1,2,3,12],[4,2,13,3,10],[0]),([0,1,2,3,73,4],[13,9,0,10,5,6],[]),([0,1,2,3,74,4],[10,8,5,6,13],[0]),([17,22,1,2,3,4],[6,8,9,0,2,13,10],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert125 : checkNodes cert38 cert10 cert131 cert20 cert45 cert90 6 cert173 = true := by decide +kernel
def cert188 : List NodeSpec := cert171 ++ cert172 ++ cert173
lemma cert122 : checkNodes cert38 cert10 cert131 cert20 cert45 cert90 6 cert188 = true := by
  unfold cert188 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨cert123, cert124⟩, cert125⟩
def cert92 : Array (List (List Nat)) := buildBuckets 35 cert38 cert188
lemma cert93 : ∀ i (hi : i < cert92.size), ∀ xs ∈ cert92[i], Impossible cert10 6 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert91 cert122
def cert189 : List NodeSpec := [([0,1,2,3,5,4],[2,10,8,27,13],[0,1]),([6,0,1,2,3,4],[3,4,6,13,17,9,0,10],[0,1]),([7,0,1,2,3,4],[0,6,2,8,4,3,42],[0]),([0,1,8,2,3,4],[2,0,10,8,4,3],[0,1]),([0,1,2,3,4,9],[0,13,10,6],[0]),([0,1,2,3,10,4],[0,2,30,10,8,4],[0,1]),([11,0,1,2,3,4],[17,10,6,2,8,4,3,32],[0]),([0,1,2,3,4,12],[2,10,13,3],[0,1]),([13,0,1,2,3,4],[0,6,8,10,4,3,13],[0]),([14,0,1,2,3],[3,2,10],[0,1]),([15,0,1,2,3,4],[8,0,6,4,3,2,10,13],[0,1]),([16,0,1,2,3,4],[8,6,17,4,3,9,0,10,13],[0]),([17,0,1,2,3,4],[8,9,6,0,17,10,3,4,13,35],[0,1]),([0,1,2,3,4,18],[8,13,0,6,3,17],[0,1]),([0,1,2,19,3,4],[0,8,10,13,6,26,3],[0]),([20,0,1,2,3,4],[4,0,10,6,2,13,3],[0]),([0,1,2,3,12],[2,10,13,3],[0,1]),([21,0,1,2,3,4],[4,0,6,3,17,8],[0,1]),([22,0,1,2,3,4],[6,0,8,5,17,2,3,4,36,9,10],[0,1]),([0,1,23,2,3,4],[0,6,2,8,3,4,28],[0]),([24,0,1,2,3,4],[17,0,10,6,2,4,3,8,13],[0]),([25,0,1,2,3,4],[17,9,6,2,10,8,3,4,39],[0,1]),([26,0,1,2,3,4],[6,8,2,4,3,0,9,38],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert126 : checkNodes cert38 cert10 cert131 cert20 cert45 cert92 7 cert189 = true := by decide +kernel
def cert94 : Array (List (List Nat)) := buildBuckets 8 cert38 cert189
lemma cert95 : ∀ i (hi : i < cert94.size), ∀ xs ∈ cert94[i], Impossible cert10 7 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert93 cert126
def cert190 : List NodeSpec := [([0,1,2,3,4],[3],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert127 : checkNodes cert38 cert10 cert131 cert20 cert45 cert94 8 cert190 = true := by decide +kernel
def cert96 : Array (List (List Nat)) := buildBuckets 1 cert38 cert190
lemma cert97 : ∀ i (hi : i < cert96.size), ∀ xs ∈ cert96[i], Impossible cert10 8 xs.toFinset :=
  buildBuckets_sound (by decide) cert143 cert39 cert21 cert46 cert95 cert127
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert139 : forestRootCheck cert28 cert10 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,18,2),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert138 : bucketContains cert96 cert28 = true := by decide +kernel
lemma cert161 : Lower cert28 cert10 9 := lower_of_forest cert139 cert97 cert138
def cert293 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def cert306 : List Nat := varsOf 38
def cert421 : List Nat := [6,6,34,34,36,36,6,34,36]
def cert408 : List Nat := [4,2,32,2,32,4,32,4,2]
def cert318 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def cert307 : Array Decor := buildWires cert318 cert227
def cert300 : Array (Option BoundPool) := buildPools cert307 cert306 cert221 cert195
lemma cert388 : goodPairs cert293 cert421 cert408 := goodPairs_of (by decide +kernel)
lemma cert319 : ∀ x ∈ cert318, faithful cert421 cert408 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert308 : ∀ x ∈ cert307.toList, faithful cert421 cert408 x ∧ x.1 < 2^128 := buildWires_faithful cert319
lemma cert313 : ∀ sw ∈ cert40.toList, swapsValid sw = true ∧ permWord sw cert293 = cert293 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert442 : ∀ i (hi : i < cert221.size), Slice cert306 cert293 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert306 cert293 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert301 : ∀ i (hi : i < cert300.size), ∀ c, cert300[i] = some c → ValidPool cert306 cert293 c := buildPools_sound cert442
lemma cert330 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert293 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert360 : checkNodes cert307 cert293 cert128 cert300 cert40 cert61 0 cert178 = true := by decide +kernel
def cert324 : Array (List (List Nat)) := buildBuckets 1 cert307 cert178
lemma cert325 : ∀ i (hi : i < cert324.size), ∀ xs ∈ cert324[i], Impossible cert293 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert388 cert308 cert301 cert313 cert330 cert360
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert361 : checkNodes cert307 cert293 cert128 cert300 cert40 cert324 1 cert178 = true := by decide +kernel
lemma cert326 : ∀ i (hi : i < cert324.size), ∀ xs ∈ cert324[i], Impossible cert293 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert388 cert308 cert301 cert313 cert325 cert361
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert362 : checkNodes cert307 cert293 cert128 cert300 cert40 cert324 2 cert178 = true := by decide +kernel
lemma cert327 : ∀ i (hi : i < cert324.size), ∀ xs ∈ cert324[i], Impossible cert293 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert388 cert308 cert301 cert313 cert326 cert362
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert363 : checkNodes cert307 cert293 cert128 cert300 cert40 cert324 3 cert179 = true := by decide +kernel
def cert328 : Array (List (List Nat)) := buildBuckets 1 cert307 cert179
lemma cert329 : ∀ i (hi : i < cert328.size), ∀ xs ∈ cert328[i], Impossible cert293 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert388 cert308 cert301 cert313 cert327 cert363
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert383 : forestRootCheck cert306 cert293 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert382 : bucketContains cert328 cert306 = true := by decide +kernel
lemma cert391 : Lower cert306 cert293 4 := lower_of_forest cert383 cert329 cert382
lemma cert400 : carryOK [(3,4),(3,5)] cert22 cert0 cert306 cert293 = true := by decide +kernel
lemma cert399 : Lower cert22 cert0 4 := carry_of cert400 cert391
lemma cert402 : carryOK [(4,5)] cert29 cert11 cert306 cert293 = true := by decide +kernel
lemma cert401 : Lower cert29 cert11 4 := carry_of cert402 cert391
def cert298 : Nat := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
lemma cert404 : liftCheck 0 16 cert26 cert298 cert306 cert293 [(VAR 4,50,34)] = true := by decide +kernel
lemma cert403 : Lower cert26 cert298 5 := lift_of cert404 cert391
def cert299 : Nat := 0xfff0f0f0f0f0f000fff0f0f0f0f0f000
def cert423 : List Nat := [12,12,20,20,28,36,36,44,52,56,56,56,12,12,12,20,20,20,36,36,36,56]
def cert410 : List Nat := [8,4,16,4,24,32,4,40,48,48,40,24,24,40,48,24,40,48,24,40,48,4]
def cert322 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0x20004a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x207e93,0xdbc91),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16db14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b67a0)]
def cert447 : List (Nat × Nat × Nat) := [(1,1,2),(0,0,1),(0,1,2),(3,0,1),(2,0,1),(2,1,2),(1,0,1),(3,1,2),(2,10,2),(3,9,3),(0,10,2),(3,5,2),(1,9,3),(1,5,2),(3,6,4)]
def cert311 : Array Decor := buildWires cert322 cert447
def cert316 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(3,4)],[(3,5),(3,4)],[(3,4),(3,5)],[(3,5)]]
def cert304 : Array (Option BoundPool) := buildPools cert311 cert25 cert221 cert195
lemma cert390 : goodPairs cert299 cert423 cert410 := goodPairs_of (by decide +kernel)
lemma cert323 : ∀ x ∈ cert322, faithful cert423 cert410 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert312 : ∀ x ∈ cert311.toList, faithful cert423 cert410 x ∧ x.1 < 2^128 := buildWires_faithful cert323
lemma cert317 : ∀ sw ∈ cert316.toList, swapsValid sw = true ∧ permWord sw cert299 = cert299 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert445 : ∀ i (hi : i < cert221.size), Slice cert25 cert299 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert25 cert299 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert305 : ∀ i (hi : i < cert304.size), ∀ c, cert304[i] = some c → ValidPool cert25 cert299 c := buildPools_sound cert445
lemma cert359 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert299 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert375 : checkNodes cert311 cert299 cert130 cert304 cert316 cert61 0 cert178 = true := by decide +kernel
def cert348 : Array (List (List Nat)) := buildBuckets 1 cert311 cert178
lemma cert349 : ∀ i (hi : i < cert348.size), ∀ xs ∈ cert348[i], Impossible cert299 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert359 cert375
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert376 : checkNodes cert311 cert299 cert130 cert304 cert316 cert348 1 cert178 = true := by decide +kernel
lemma cert350 : ∀ i (hi : i < cert348.size), ∀ xs ∈ cert348[i], Impossible cert299 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert349 cert376
def cert417 : List NodeSpec := [([18,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert377 : checkNodes cert311 cert299 cert130 cert304 cert316 cert348 2 cert417 = true := by decide +kernel
def cert351 : Array (List (List Nat)) := buildBuckets 1 cert311 cert417
lemma cert352 : ∀ i (hi : i < cert351.size), ∀ xs ∈ cert351[i], Impossible cert299 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert350 cert377
def cert418 : List NodeSpec := [([9,11,0,3],[],[0]),([0,6,4,3],[],[0]),([12,0,1,3],[],[]),([0,1,2,13],[],[]),([0,1,14,3],[],[]),([15,0,1,3],[],[]),([8,7,2,3],[],[]),([0,1,2,16],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert378 : checkNodes cert311 cert299 cert130 cert304 cert316 cert351 3 cert418 = true := by decide +kernel
def cert353 : Array (List (List Nat)) := buildBuckets 4 cert311 cert418
lemma cert354 : ∀ i (hi : i < cert353.size), ∀ xs ∈ cert353[i], Impossible cert299 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert352 cert378
def cert419 : List NodeSpec := [([0,1,2,4,3],[],[0]),([5,0,1,2,3],[],[0,1]),([0,6,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([9,0,1,2,3],[],[0]),([0,1,10,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert379 : checkNodes cert311 cert299 cert130 cert304 cert316 cert353 4 cert419 = true := by decide +kernel
def cert355 : Array (List (List Nat)) := buildBuckets 3 cert311 cert419
lemma cert356 : ∀ i (hi : i < cert355.size), ∀ xs ∈ cert355[i], Impossible cert299 4 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert354 cert379
def cert420 : List NodeSpec := [([0,1,2,3],[],[0,2,3,1,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert380 : checkNodes cert311 cert299 cert130 cert304 cert316 cert355 5 cert420 = true := by decide +kernel
def cert357 : Array (List (List Nat)) := buildBuckets 1 cert311 cert420
lemma cert358 : ∀ i (hi : i < cert357.size), ∀ xs ∈ cert357[i], Impossible cert299 5 xs.toFinset :=
  buildBuckets_sound (by decide) cert390 cert312 cert305 cert317 cert356 cert380
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert387 : forestRootCheck cert25 cert299 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert386 : bucketContains cert357 cert25 = true := by decide +kernel
lemma cert405 : Lower cert25 cert299 6 := lower_of_forest cert387 cert358 cert386
def cert294 : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
lemma cert393 : carryOK [(3,5),(3,4)] cert23 cert294 cert26 cert298 = true := by decide +kernel
lemma cert392 : Lower cert23 cert294 5 := carry_of cert393 cert403
def cert295 : Nat := 0xfcc0fcc0c0c0c0c0fcc0fcc0c0c0c0c0
lemma cert395 : carryOK [(3,4)] cert24 cert295 cert26 cert298 = true := by decide +kernel
lemma cert394 : Lower cert24 cert295 5 := carry_of cert395 cert403
def cert296 : Nat := 0xffcccccccccccc00ffcccccccccccc00
lemma cert397 : carryOK [(1,2)] cert27 cert296 cert25 cert299 = true := by decide +kernel
lemma cert396 : Lower cert27 cert296 6 := carry_of cert397 cert405
def cert297 : Nat := 0xfcc0c0c0c0c0c000fcc0c0c0c0c0c000
def cert422 : List Nat := [14,14,14,22,22,22,30,30,38,38,38,46,46,54,54,58,58,58,58,60,60,60,60,14,14,14,14,14,14,14,22,22,22,22,22,22,22,38,38,38,38,38,38,38,58,58,58,58,60,60,60,60]
def cert409 : List Nat := [12,10,6,20,18,6,28,26,36,34,6,44,42,52,50,56,50,42,26,56,52,44,28,26,28,42,44,50,52,56,26,28,42,44,50,52,56,26,28,42,44,50,52,56,6,28,44,52,6,26,42,50]
def cert381 : Nat := fullMask 52
def cert320 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff87ffff,0xf12a54a8756b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0ffffff87fff,0x1f54a95702d6d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0003fff98c7,0x669f3e7ee98c3),(0xffff0000ffff0000ffff0000ffff0000,0xff01fc07fe0f8,0xaae7cf9dde0d8),(0xffffffff00000000ffffffff00000000,0xfffe0007fff00,0xccf9f3e3bfb00)]
def cert446 : List (Nat × Nat × Nat) := [(2,0,2),(2,2,3),(0,0,2),(1,2,3),(0,2,3),(0,0,1),(3,2,3),(3,6,4),(1,6,4),(0,0,8),(0,7,3),(0,1,3),(2,1,2),(0,1,2),(3,7,3),(0,10,2),(3,7,1),(3,10,2),(0,9,4),(0,3,4),(3,6,0),(2,10,2),(3,5,1),(1,10,2),(3,25,1),(3,11,1),(1,11,7),(3,9,8),(1,7,16),(1,17,7),(0,19,4),(3,15,2),(3,15,4),(3,19,1),(0,15,4),(3,14,1),(3,15,1),(3,21,3),(0,21,3),(3,20,3),(3,6,10),(3,20,0),(3,26,0),(0,22,3),(3,19,4),(0,28,3),(2,28,3),(1,20,3),(3,22,3),(3,10,8),(3,11,4),(1,6,10),(0,20,3),(0,10,8),(2,0,23),(3,39,1),(3,58,4),(3,20,28),(3,57,2),(3,20,4),(3,57,4),(3,53,4),(1,11,20),(3,48,8)]
def cert309 : Array Decor := buildWires cert320 cert446
def cert314 : Array (List (Nat × Nat)) := #[[],[(3,4)],[(3,4),(1,2)],[(4,5)],[(1,2)],[(4,5),(1,2)],[(3,5),(3,4)],[(3,5),(3,4),(1,2)],[(3,4),(3,5)],[(3,5)]]
def cert441 : List (Nat × Nat) := [(subcube 0 2,6),(subcube 0 24,4),(subcube 0 48,4),(subcube 0 4,6),(subcube 0 40,4),(subcube 0 8,5),(subcube 0 16,5),(subcube 0 32,5)]
def cert443 : Array (Nat × Nat) := cert441.toArray
def cert424 : List PoolSpec := [(0,[(0,2,3),(1,2,3),(3,9,8)]),(1,[]),(2,[]),(0,[]),(3,[]),(4,[]),(5,[]),(3,[(0,2,3),(1,2,3),(3,9,8)]),(6,[]),(3,[(0,0,2),(3,7,3)]),(7,[]),(0,[(2,2,3),(3,6,4)]),(0,[(2,2,3),(1,6,4)]),(0,[(0,2,3),(1,2,3)]),(0,[(2,2,3),(3,2,3)]),(0,[(1,10,2),(0,28,3)]),(0,[(1,10,2),(2,28,3)]),(0,[(0,10,2),(1,20,3)]),(0,[(2,10,2),(3,10,2)]),(0,[(3,2,3),(3,11,4)]),(0,[(0,10,2),(3,20,3)]),(3,[(2,2,3),(3,2,3)]),(3,[(2,2,3),(3,6,4)]),(3,[(2,2,3),(1,6,4)]),(0,[(1,2,3)]),(3,[(0,2,3),(1,2,3)]),(3,[(0,0,2)]),(0,[(0,7,3)]),(0,[(3,2,3)]),(0,[(0,1,2)]),(0,[(3,7,3)]),(0,[(0,10,2)]),(0,[(3,7,1)]),(0,[(3,10,2)]),(3,[(3,10,2)]),(0,[(0,2,3)]),(0,[(2,2,3)]),(0,[(2,10,2)]),(0,[(3,5,1)]),(0,[(1,10,2)]),(3,[(0,10,2)]),(3,[(2,2,3)]),(3,[(1,2,3)]),(3,[(0,2,3)])]
def cert302 : Array (Option BoundPool) := buildPools cert309 cert28 cert443 cert424
lemma cert389 : goodPairs cert297 cert422 cert409 := goodPairs_of (by decide +kernel)
lemma cert321 : ∀ x ∈ cert320, faithful cert422 cert409 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert310 : ∀ x ∈ cert309.toList, faithful cert422 cert409 x ∧ x.1 < 2^128 := buildWires_faithful cert321
lemma cert315 : ∀ sw ∈ cert314.toList, swapsValid sw = true ∧ permWord sw cert297 = cert297 := autos_of (by decide +kernel)
lemma cert426 : sliceDirectCheck 0 2 0 cert28 cert297 cert25 cert299 = true := by decide +kernel
lemma cert425 : Slice cert28 cert297 (subcube 0 2) 6 := slice_direct cert426 cert405
lemma cert428 : sliceDirectCheck 0 24 0 cert28 cert297 cert306 cert293 = true := by decide +kernel
lemma cert427 : Slice cert28 cert297 (subcube 0 24) 4 := slice_direct cert428 cert391
lemma cert430 : sliceDirectCheck 0 48 0 cert28 cert297 cert22 cert0 = true := by decide +kernel
lemma cert429 : Slice cert28 cert297 (subcube 0 48) 4 := slice_direct cert430 cert399
lemma cert432 : sliceDirectCheck 0 4 0 cert28 cert297 cert27 cert296 = true := by decide +kernel
lemma cert431 : Slice cert28 cert297 (subcube 0 4) 6 := slice_direct cert432 cert396
lemma cert434 : sliceDirectCheck 0 40 0 cert28 cert297 cert29 cert11 = true := by decide +kernel
lemma cert433 : Slice cert28 cert297 (subcube 0 40) 4 := slice_direct cert434 cert401
lemma cert436 : sliceDirectCheck 0 8 0 cert28 cert297 cert26 cert298 = true := by decide +kernel
lemma cert435 : Slice cert28 cert297 (subcube 0 8) 5 := slice_direct cert436 cert403
lemma cert438 : sliceDirectCheck 0 16 0 cert28 cert297 cert24 cert295 = true := by decide +kernel
lemma cert437 : Slice cert28 cert297 (subcube 0 16) 5 := slice_direct cert438 cert394
lemma cert440 : sliceDirectCheck 0 32 0 cert28 cert297 cert23 cert294 = true := by decide +kernel
lemma cert439 : Slice cert28 cert297 (subcube 0 32) 5 := slice_direct cert440 cert392
set_option maxRecDepth 200000 in
lemma cert444 : ∀ i (hi : i < cert443.size), Slice cert28 cert297 cert443[i].1 cert443[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert28 cert297 p.1 p.2) (forall_cons cert425 (forall_cons cert427 (forall_cons cert429 (forall_cons cert431 (forall_cons cert433 (forall_cons cert435 (forall_cons cert437 (forall_cons cert439 (fun _ h => (List.not_mem_nil h).elim)))))))))
lemma cert303 : ∀ i (hi : i < cert302.size), ∀ c, cert302[i] = some c → ValidPool cert28 cert297 c := buildPools_sound cert444
lemma cert347 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert297 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert364 : checkNodes cert309 cert297 cert381 cert302 cert314 cert61 0 cert178 = true := by decide +kernel
def cert331 : Array (List (List Nat)) := buildBuckets 1 cert309 cert178
lemma cert332 : ∀ i (hi : i < cert331.size), ∀ xs ∈ cert331[i], Impossible cert297 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert347 cert364
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert365 : checkNodes cert309 cert297 cert381 cert302 cert314 cert331 1 cert178 = true := by decide +kernel
lemma cert333 : ∀ i (hi : i < cert331.size), ∀ xs ∈ cert331[i], Impossible cert297 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert332 cert365
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert366 : checkNodes cert309 cert297 cert381 cert302 cert314 cert331 2 cert178 = true := by decide +kernel
lemma cert334 : ∀ i (hi : i < cert331.size), ∀ xs ∈ cert331[i], Impossible cert297 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert333 cert366
def cert411 : List NodeSpec := [([10,33,9,4],[],[]),([68,0,1,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert367 : checkNodes cert309 cert297 cert381 cert302 cert314 cert331 3 cert411 = true := by decide +kernel
def cert335 : Array (List (List Nat)) := buildBuckets 1 cert309 cert411
lemma cert336 : ∀ i (hi : i < cert335.size), ∀ xs ∈ cert335[i], Impossible cert297 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert334 cert367
def cert412 : List NodeSpec := [([40,0,1,9,4],[],[]),([0,1,33,9,4],[],[0]),([60,0,2,3,4],[],[]),([36,19,0,1,4],[],[]),([61,0,1,2,3],[],[]),([32,10,0,1,4],[0],[]),([58,0,1,9,4],[1,2],[]),([10,7,16,9,4],[],[0]),([10,33,2,3,4],[3,4],[0]),([19,10,18,3,4],[],[]),([20,0,1,55,3],[2],[]),([10,15,18,3,4],[4],[]),([22,0,1,3,13],[],[]),([6,53,0,1,4],[],[0]),([48,0,1,8,4],[],[0]),([10,7,1,50,4],[],[]),([21,0,1,55,3],[],[]),([10,7,1,55,3],[],[]),([62,0,1,3,4],[],[]),([10,14,1,9,4],[1],[]),([63,0,1,3,4],[],[]),([44,64,0,1,2],[],[]),([10,7,30,3,4],[],[]),([64,0,1,2,52],[],[]),([22,25,1,3,4],[],[]),([65,0,1,2,3],[],[]),([66,0,1,2,3],[],[]),([46,22,1,3,4],[],[]),([67,0,1,3,4],[],[]),([22,0,1,52,4],[],[]),([20,0,1,50,4],[1,5],[]),([46,21,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert368 : checkNodes cert309 cert297 cert381 cert302 cert314 cert335 4 cert412 = true := by decide +kernel
def cert337 : Array (List (List Nat)) := buildBuckets 11 cert309 cert412
lemma cert338 : ∀ i (hi : i < cert337.size), ∀ xs ∈ cert337[i], Impossible cert297 4 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert336 cert368
def cert406 : List NodeSpec := [([29,0,1,2,3,4],[],[]),([7,0,30,1,3,4],[],[0]),([7,0,31,1,3,4],[6],[]),([32,0,1,4],[1,0,7,2],[0]),([0,1,33,2,3,4],[3,4],[0]),([7,0,34,1,3,4],[6],[]),([19,7,0,1,9,4],[8],[]),([35,0,1,2,3,4],[],[]),([19,0,18,1,3,4],[],[0]),([36,7,0,1,3,4],[3],[0]),([15,0,18,1,3,4],[4],[0]),([37,0,1,2,3,4],[],[]),([38,0,1,2,3,4],[9],[1]),([39,0,1,2,3,4],[4],[0]),([21,7,0,18,3,4],[6],[]),([11,21,0,1,3,4],[],[0]),([21,0,1,9,3,4],[8],[]),([40,0,1,2,3,4],[],[0]),([41,0,1,2,3,4],[],[]),([0,42,1,2,3,4],[],[]),([19,0,1,2,24,4],[10],[]),([10,0,1,2,3,12],[8,11],[1,2]),([43,0,1,2,3,4],[],[]),([44,7,0,1,2,4],[],[]),([10,14,1,2,3,4],[4],[0]),([10,0,1,2,3,13],[5,12],[0]),([10,25,1,2,3,4],[4],[0,2]),([10,7,1,28,3,4],[3],[0,3]),([10,15,1,2,3,4],[4],[0,1]),([45,0,1,2,3,4],[],[0]),([44,0,1,2,3,4],[],[]),([10,0,1,9,8,4],[1,13],[0,4]),([11,10,7,1,3,4],[],[0]),([44,20,0,1,2,4],[8],[3]),([10,7,1,9,3,4],[],[4,0]),([46,10,1,2,3,4],[3],[0]),([10,7,18,3,4],[4,6,3],[0,3,4,5]),([6,11,10,0,1,4],[14],[0]),([7,0,1,23,3,4],[3,2,5],[]),([36,15,0,1,3,4],[3,1],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert370 : checkNodes cert309 cert297 cert381 cert302 cert314 cert337 5 cert406 = true := by decide +kernel
def cert407 : List NodeSpec := [([19,10,1,2,3,4],[4,9],[0]),([22,20,0,1,3,4],[3],[0,4,3]),([22,10,7,1,3,4],[3],[]),([6,22,0,1,3,4],[],[0,4]),([10,47,1,2,3,4],[3],[]),([46,7,1,2,3,4],[3],[0]),([48,0,1,2,3,4],[],[0]),([49,0,1,2,3,4],[6],[]),([10,7,16,2,3,4],[],[0,1,4]),([22,0,1,3,8,4],[],[0]),([11,20,0,1,3,4],[8,2],[0]),([10,0,1,2,50,4],[6,15],[0,4]),([7,0,16,1,9,4],[],[0]),([22,7,0,1,3,4],[3],[4]),([51,10,0,1,2,4],[16],[]),([14,0,1,9,4],[6,1,2,13],[0]),([20,0,1,9,3,4],[8,2],[]),([10,7,18,2,3,4],[4,3,6],[]),([10,0,1,2,52,4],[1,17],[0]),([26,22,0,1,3,4],[18],[0]),([20,0,1,28,3,4],[1,5],[0,3]),([21,10,7,2,3,4],[4,3],[]),([53,0,1,2,3,4],[10],[0]),([46,20,1,2,3,4],[3],[0]),([54,0,1,2,3,4],[],[]),([20,0,1,2,52,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([7,0,1,55,3],[6,2,19],[0]),([56,0,1,2,3,4],[6],[]),([57,0,1,2,3,4],[10],[0,1]),([58,0,1,2,3,4],[6,8,10],[0]),([20,0,1,2,3,4],[8,10],[1,6]),([59,0,1,2,3,4],[],[]),([44,10,0,1,2,4],[20],[]),([44,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert371 : checkNodes cert309 cert297 cert381 cert302 cert314 cert337 5 cert407 = true := by decide +kernel
def cert413 : List NodeSpec := cert406 ++ cert407
lemma cert369 : checkNodes cert309 cert297 cert381 cert302 cert314 cert337 5 cert413 = true := by
  unfold cert413 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨cert370, cert371⟩
def cert339 : Array (List (List Nat)) := buildBuckets 26 cert309 cert413
lemma cert340 : ∀ i (hi : i < cert339.size), ∀ xs ∈ cert339[i], Impossible cert297 5 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert338 cert369
def cert414 : List NodeSpec := [([6,11,0,1,4],[8,6,14,21,2],[0]),([0,1,2,3,12],[11,22,1,2],[0,1,2]),([0,1,2,3,13],[12,23,5,8],[0]),([14,0,1,2,3,4],[6,4,3,8,2,24],[0]),([0,1,9,8,4],[13,25,1,2],[0,4]),([10,7,1,2,3,4],[4,6,3,26],[0,3]),([15,0,1,2,3,4],[1,4,10,27],[0,1]),([11,7,0,1,3,4],[6,3,1,5,28],[0]),([7,0,16,1,2,3,4],[8,6],[0,2,1,4]),([17,7,0,1,3,4],[6,3,26,1,5],[0]),([7,0,18,1,3,4],[6,3,4,26,29],[0,3,4,5]),([19,0,1,2,3,4],[6,3,4,1,10,30,9],[0,1]),([20,10,0,1,2,3,4],[6,31],[0,4,3]),([21,7,0,1,2,3,4],[4,6,3,26],[4,0]),([21,0,1,2,3,4],[6,3,8,10,32,26],[4,0,3]),([20,7,0,1,2,3,4],[4,1,5,26],[0,3,4]),([22,0,1,2,3,4],[4,3,8,10,33,34],[0,3]),([10,0,1,2,3,8,4],[6,8,24,4],[0,1,4]),([19,7,0,1,2,3,4],[8,3,6,1],[1,0]),([0,1,23,2,3,4],[3,5,2,4,1],[0,1,6,4,2,7]),([10,0,1,9,2,3,4],[1,35,4],[0,1,4,2]),([7,0,1,2,24,3,4],[2,6,5,1],[0,3]),([6,10,0,1,2,3,4],[8,3,4,6,36],[0,4,1,2]),([25,0,1,2,3,4],[8,4,1,2,36],[0,2]),([7,0,18,1,2,3,4],[3,4,6],[0,4]),([15,7,0,1,2,3,4],[8,1],[0,1]),([7,0,1,9,3,4],[6,3,8,1,2,35,5],[0,4]),([22,10,0,1,2,3,4],[6,4,3,33],[0,4]),([26,10,0,1,2,3,4],[6,37],[0,4]),([0,27,1,2,3,4],[3,38,6,1,5],[0]),([10,0,1,2,28,3,4],[6,39,4],[0,4,3]),([20,0,1,2,3,4],[31,40,8,10],[0,4,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert372 : checkNodes cert309 cert297 cert381 cert302 cert314 cert339 6 cert414 = true := by decide +kernel
def cert341 : Array (List (List Nat)) := buildBuckets 11 cert309 cert414
lemma cert342 : ∀ i (hi : i < cert341.size), ∀ xs ∈ cert341[i], Impossible cert297 6 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert340 cert372
def cert415 : List NodeSpec := [([5,0,1,2,3,4],[6,3,4,8,1,10,5],[0,4]),([6,0,1,2,3,4],[8,3,4,1,10,2,36,41],[0,4,1,2]),([7,0,1,2,3,4],[6,4,26,3,8,1,10,5],[0,3]),([0,1,2,3,8,4],[24,42,6,8,2],[0,4]),([0,1,9,2,3,4],[35,43,1,2,5],[0,1,6,4,2,7]),([10,0,1,2,3,4],[4,3,6,8,10],[0,1,6,4,2,7,3,8,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert373 : checkNodes cert309 cert297 cert381 cert302 cert314 cert341 7 cert415 = true := by decide +kernel
def cert343 : Array (List (List Nat)) := buildBuckets 3 cert309 cert415
lemma cert344 : ∀ i (hi : i < cert343.size), ∀ xs ∈ cert343[i], Impossible cert297 7 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert342 cert373
def cert416 : List NodeSpec := [([0,1,2,3,4],[3,4],[0,1,6,4,2,7,3,8,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert374 : checkNodes cert309 cert297 cert381 cert302 cert314 cert343 8 cert416 = true := by decide +kernel
def cert345 : Array (List (List Nat)) := buildBuckets 1 cert309 cert416
lemma cert346 : ∀ i (hi : i < cert345.size), ∀ xs ∈ cert345[i], Impossible cert297 8 xs.toFinset :=
  buildBuckets_sound (by decide) cert389 cert310 cert303 cert315 cert344 cert374
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert385 : forestRootCheck cert28 cert297 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert384 : bucketContains cert345 cert28 = true := by decide +kernel
lemma cert398 : Lower cert28 cert297 9 := lower_of_forest cert385 cert346 cert384
def cert623 (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

def cert478 : List Nat := varsOf 15
def cert468 : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def cert477 : List Nat := [5,14,5,9,3,5,14,9,14,3,3,7,7]
def cert470 : List Nat := [4,12,6,8,2,1,10,1,6,1,0,6,1]
def cert469 : Nat := fullMask 13
def cert451 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6503,2311),(0xff00ff00ff00ff00ff00ff00ff00ff00,458,74)]
def cert482 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def cert486 : BT Decor := buildWiresBT 5 cert451 cert482
def cert448 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3)],[(2,3),(1,2)],[(2,3),(1,3)]]
def cert449 : BT (List (Nat × Nat)) := btOfList 3 cert448
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert474 : goodPairs cert468 cert477 cert470 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert452 : ∀ x ∈ cert451, faithful cert477 cert470 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert487 : btAll (fun x => faithful cert477 cert470 x ∧ x.1 < 2^128) cert486 := buildWiresBT_faithful cert452
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert450 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert468 = cert468) cert449 := btAll_ofList (autos_of (by decide +kernel))
def cert479 : List (Option (Nat × Nat)) := []
def cert480 : BT (Option (Nat × Nat)) := btOfList 1 cert479
def cert475 : BT (Option BoundPool) := buildPoolsBT 1 cert486 cert478 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert481 : btAll (fun o => ∀ p, o = some p → Slice cert478 cert468 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert478 cert468 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert476 : btAll (fun o => ∀ c, o = some c → ValidPool cert478 cert468 c) cert475 := buildPoolsBT_sound cert481
def cert466 : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert467 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert468 (3 - 1) xs.toFinset) cert466 := trivial
def cert453 : List NodeSpec := cert623 [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert483 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert466 3 cert453 = true := by decide +kernel
def cert471 : List NodeSpec := cert453
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert463 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert466 3 cert471 = true := cert483
def cert457 : BT (List (List Nat)) := buildBucketsBT cert486 cert471
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert458 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert468 3 xs.toFinset) cert457 := buildBucketsBT_sound (by decide) cert474 cert487 cert476 cert450 cert467 cert463
def cert454 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert484 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert457 4 cert454 = true := by decide +kernel
def cert472 : List NodeSpec := cert454
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert464 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert457 4 cert472 = true := cert484
def cert459 : BT (List (List Nat)) := buildBucketsBT cert486 cert472
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert460 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert468 4 xs.toFinset) cert459 := buildBucketsBT_sound (by decide) cert474 cert487 cert476 cert450 cert458 cert464
def cert455 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert485 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert459 5 cert455 = true := by decide +kernel
def cert473 : List NodeSpec := cert455
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert465 : checkNodesBT cert486 cert468 cert469 cert475 cert449 cert459 5 cert473 = true := cert485
def cert461 : BT (List (List Nat)) := buildBucketsBT cert486 cert473
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert462 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert468 5 xs.toFinset) cert461 := buildBucketsBT_sound (by decide) cert474 cert487 cert476 cert450 cert460 cert465
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert456 : Lower cert478 cert468 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) cert462 (by decide +kernel)
def cert490 : List Nat := varsOf 23
def cert489 : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert488 : Lower cert490 cert489 6 := carry_of (swaps := [(3,4)]) (roots2 := cert478) (T2 := cert468) (by decide +kernel) cert456
def cert493 : List Nat := varsOf 27
def cert492 : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert491 : Lower cert493 cert492 6 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := cert478) (T2 := cert468) (by decide +kernel) cert456
def cert513 : List Nat := varsOf 28
def cert505 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def cert512 : List Nat := [20,24,12,12,24,20]
def cert507 : List Nat := [16,16,4,8,8,4]
def cert506 : Nat := fullMask 6
def cert497 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def cert516 : BT Decor := buildWiresBT 2 cert497 cert227
def cert494 : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(3,4),(2,3)],[(3,4),(2,4)]]
def cert495 : BT (List (Nat × Nat)) := btOfList 3 cert494
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert509 : goodPairs cert505 cert512 cert507 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert498 : ∀ x ∈ cert497, faithful cert512 cert507 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert517 : btAll (fun x => faithful cert512 cert507 x ∧ x.1 < 2^128) cert516 := buildWiresBT_faithful cert498
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert496 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert505 = cert505) cert495 := btAll_ofList (autos_of (by decide +kernel))
def cert510 : BT (Option BoundPool) := buildPoolsBT 1 cert516 cert513 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert514 : btAll (fun o => ∀ p, o = some p → Slice cert513 cert505 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert513 cert505 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert511 : btAll (fun o => ∀ c, o = some c → ValidPool cert513 cert505 c) cert510 := buildPoolsBT_sound cert514
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert504 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert505 (3 - 1) xs.toFinset) cert466 := trivial
def cert499 : List NodeSpec := cert623 [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert515 : checkNodesBT cert516 cert505 cert506 cert510 cert495 cert466 3 cert499 = true := by decide +kernel
def cert508 : List NodeSpec := cert499
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert503 : checkNodesBT cert516 cert505 cert506 cert510 cert495 cert466 3 cert508 = true := cert515
def cert501 : BT (List (List Nat)) := buildBucketsBT cert516 cert508
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert502 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert505 3 xs.toFinset) cert501 := buildBucketsBT_sound (by decide) cert509 cert517 cert511 cert496 cert504 cert503
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert500 : Lower cert513 cert505 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) cert502 (by decide +kernel)
def cert520 : List Nat := varsOf 29
def cert519 : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert518 : Lower cert520 cert519 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) cert500
def cert622 : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert621 : Lower cert23 cert622 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) cert500
def cert582 : List Nat := varsOf 31
def cert569 : Nat := 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8
def cert581 : List Nat := [5,14,5,9,14,5,14,9,22,17,17,3,26,22,3,26,22,7,26,13,11,19,26,3,7,22,9,7,3,13,9,5,17,14,21,11,22,9,25,13,21,14,14,14,25,21,14]
def cert571 : List Nat := [4,12,6,8,10,1,6,1,6,1,16,2,24,20,1,10,18,6,18,1,10,18,28,0,1,16,10,2,6,12,12,12,28,2,20,1,28,0,1,8,1,8,4,0,24,4,28]
def cert570 : Nat := fullMask 47
def cert522 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x31edfdba4ead,0x148010842a0),(0xcccccccccccccccccccccccccccccccc,0x4e1a1bf7f952,0x21c378954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6f96ab0b2177,0x6415f0422147),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5eea645c90da,0x5291e450901a),(0xffff0000ffff0000ffff0000ffff0000,0x31550265b700,0x501502653400)]
def cert593 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(1,0,3),(1,1,2),(2,1,2),(0,1,3),(2,1,3),(0,2,3),(1,2,3),(0,0,17),(1,0,17),(2,0,17),(3,0,17),(0,1,17),(1,0,22),(3,0,22),(2,2,3),(1,2,4),(2,2,4),(1,2,5),(1,3,4),(2,3,4),(1,3,28),(3,3,28),(1,4,22),(1,4,5),(1,5,22),(1,3,35),(3,3,35),(1,1,17),(2,1,17),(3,1,17),(0,1,28),(2,1,28),(1,4,17),(3,4,17),(2,1,31),(3,5,17),(2,1,46),(2,1,32),(1,0,13),(1,3,13),(3,4,6),(1,4,13),(3,4,13),(2,6,13),(0,6,17),(1,13,55),(2,6,17),(3,2,6),(3,0,50),(3,2,50),(1,4,50),(3,4,50),(1,0,39),(1,2,39),(1,4,39),(2,4,39),(3,4,39),(2,6,39),(1,2,54),(1,3,58),(1,3,69),(3,3,69),(3,1,71),(3,4,71),(1,0,74),(2,1,74),(3,7,17),(3,3,49),(1,8,39),(1,3,42),(1,4,45),(1,4,9),(3,4,9),(0,9,11),(3,2,11),(0,3,9),(3,3,9),(1,3,85),(0,4,19),(1,4,19),(3,4,19),(3,3,91),(1,9,15),(2,9,15),(3,3,64),(1,2,87),(1,4,87),(1,4,18),(1,4,21),(0,1,29),(0,1,82),(0,29,82),(0,9,29),(3,9,29),(3,0,43),(0,1,43),(3,3,43),(3,2,29),(0,1,90),(0,1,108),(1,4,88),(3,4,88),(0,1,111),(3,10,29),(2,12,108),(1,4,95),(3,4,95),(0,12,29),(1,4,40),(3,13,29),(3,18,19),(1,4,16),(1,4,47),(3,4,23),(3,22,38)]
def cert619 : BT Decor := buildWiresBT 7 cert522 cert593
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert578 : goodPairs cert569 cert581 cert571 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert523 : ∀ x ∈ cert522, faithful cert581 cert571 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert620 : btAll (fun x => faithful cert581 cert571 x ∧ x.1 < 2^128) cert619 := buildWiresBT_faithful cert523
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert521 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert569 = cert569) cert495 := btAll_ofList (autos_of (by decide +kernel))
def cert589 : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6)]
def cert590 : BT (Option (Nat × Nat)) := btOfList 3 cert589
def cert592 : List PoolSpec := [(1,[]),(0,[]),(3,[(0,0,1)]),(4,[(0,0,1)]),(5,[(0,0,1)]),(2,[]),(0,[(1,2,5)]),(4,[]),(3,[]),(0,[(1,4,5)]),(3,[(0,0,1),(1,4,5)]),(5,[(1,2,3)]),(3,[(0,0,1),(1,3,28)]),(3,[(0,0,1),(3,5,17)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(5,[]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[(1,0,1)]),(1,[(2,1,2)]),(3,[(1,0,1),(3,4,6)]),(3,[(1,0,1),(0,6,17)]),(3,[(1,0,1),(2,6,17)]),(1,[(3,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(2,6,17)]),(3,[(2,0,1)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(3,[(3,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(0,[(1,0,13)]),(1,[(2,1,28)]),(4,[(1,0,2)]),(5,[(1,0,2)]),(1,[(0,1,28)]),(0,[(1,0,2)]),(4,[(1,0,2),(3,4,9)]),(4,[(1,0,2),(0,9,29)]),(4,[(1,0,17),(3,4,19)]),(3,[(1,0,17)]),(5,[(1,0,3),(3,2,11)]),(4,[(1,0,17)]),(3,[(3,3,9)]),(5,[(1,0,2),(3,3,9)]),(4,[(2,0,2)]),(5,[(2,0,2)]),(3,[(1,0,3)]),(4,[(3,2,11)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(3,[(2,1,17)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(3,[(1,0,13)]),(4,[(2,1,2),(1,4,13)]),(4,[(2,1,2),(1,4,50)]),(4,[(2,1,2),(3,13,29)]),(3,[(1,3,13)]),(5,[(2,1,2),(1,3,13)]),(4,[(2,1,17)]),(3,[(0,1,17)]),(3,[(0,0,17)]),(3,[(0,0,17),(1,4,18)]),(3,[(1,0,17),(3,4,19)]),(3,[(2,0,17)]),(3,[(3,0,17)]),(4,[(3,0,17)]),(4,[(0,1,17)]),(3,[(0,1,17),(1,1,17)]),(3,[(1,1,17)]),(3,[(2,1,17),(1,4,39)]),(3,[(3,1,17)]),(3,[(3,1,17),(1,4,40)]),(4,[(1,2,4)]),(3,[(1,3,4)]),(3,[(1,4,17)]),(4,[(1,4,17)]),(3,[(3,4,17)]),(4,[(3,4,17)])]
def cert579 : BT (Option BoundPool) := buildPoolsBT 7 cert619 cert582 cert590 cert592
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert588 : Slice cert582 cert569 (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) cert456
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert587 : Slice cert582 cert569 (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) cert488
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert586 : Slice cert582 cert569 (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) cert491
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert585 : Slice cert582 cert569 (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert500
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert584 : Slice cert582 cert569 (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert621
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert583 : Slice cert582 cert569 (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert518
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert591 : btAll (fun o => ∀ p, o = some p → Slice cert582 cert569 p.1 p.2) cert590 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert582 cert569 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert583) (forall_cons (fun _ h => by cases h; exact cert584) (forall_cons (fun _ h => by cases h; exact cert585) (forall_cons (fun _ h => by cases h; exact cert586) (forall_cons (fun _ h => by cases h; exact cert587) (forall_cons (fun _ h => by cases h; exact cert588) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert580 : btAll (fun o => ∀ c, o = some c → ValidPool cert582 cert569 c) cert579 := buildPoolsBT_sound cert591
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert568 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 (3 - 1) xs.toFinset) cert466 := trivial
def cert524 : List NodeSpec := cert623 [([0,17,29,101],[]),([0,2,35,102],[]),([4,17,56,84],[]),([0,17,56,122],[]),([0,17,79,122],[]),([0,17,35,122],[]),([0,17,73,122],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert594 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert466 3 cert524 = true := by decide +kernel
def cert572 : List NodeSpec := cert524
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert562 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert466 3 cert572 = true := cert594
def cert550 : BT (List (List Nat)) := buildBucketsBT cert619 cert572
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert551 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 3 xs.toFinset) cert550 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert568 cert562
def cert525 : List NodeSpec := cert623 [([0,3,4,22,28],[]),([0,2,3,22,34],[]),([0,2,3,4,35],[]),([0,3,4,28,35],[]),([0,3,4,13,55],[]),([0,2,3,6,65],[]),([0,2,3,4,68],[]),([0,1,2,3,74],[]),([0,2,3,8,65],[]),([0,1,2,3,81],[]),([0,1,2,3,91],[]),([0,1,4,17,94],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert595 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert550 4 cert525 = true := by decide +kernel
def cert526 : List NodeSpec := cert623 [([0,4,14,17,41],[]),([0,1,17,29,82],[7]),([0,1,4,17,103],[7]),([0,3,4,17,101],[]),([0,2,3,4,109],[]),([0,3,4,27,35],[]),([0,3,4,35,85],[]),([0,2,3,35,89],[]),([0,2,3,35,91],[]),([0,2,3,73,89],[]),([0,2,3,73,91],[]),([0,1,3,85,89],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert596 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert550 4 cert526 = true := by decide +kernel
def cert527 : List NodeSpec := cert623 [([0,2,4,35,86],[]),([0,2,3,4,113],[]),([0,1,3,4,115],[]),([0,4,13,17,100],[]),([0,1,17,29,53],[7]),([0,1,4,17,120],[7]),([0,2,4,22,50],[]),([0,2,3,22,65],[]),([0,1,3,64,66],[]),([1,2,3,4,121],[]),([0,4,16,17,56],[]),([0,4,16,17,79],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert597 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert550 4 cert527 = true := by decide +kernel
def cert528 : List NodeSpec := cert623 [([0,4,16,17,35],[]),([0,4,16,17,73],[]),([0,1,2,3,123],[]),([0,1,21,26,29],[]),([0,1,2,3,124],[]),([0,1,22,26,29],[]),([0,2,3,4,125],[]),([0,2,3,40,65],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert598 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert550 4 cert528 = true := by decide +kernel
def cert573 : List NodeSpec := cert525 ++ cert526 ++ cert527 ++ cert528
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert563 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert550 4 cert573 = true := by
  unfold cert573 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨cert595,cert596⟩,cert597⟩,cert598⟩
def cert552 : BT (List (List Nat)) := buildBucketsBT cert619 cert573
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert553 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 4 xs.toFinset) cert552 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert551 cert563
def cert529 : List NodeSpec := [([0,2,3,4,5,22],[],[0,2]),([0,1,3,4,17,28],[6,7],[0]),([0,1,2,3,17,34],[9,10],[0]),([0,1,2,3,4,31],[12],[0]),([0,1,2,3,4,46],[7,8,13],[0]),([0,1,3,4,28,31],[6,14],[0]),([0,1,3,4,28,32],[],[0]),([0,1,2,3,4,32],[0],[0]),([0,3,4,6,13,17],[],[0]),([0,2,3,4,6,50],[],[0]),([0,2,3,4,6,39],[],[0]),([0,2,3,4,13,54],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert599 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert529 = true := by decide +kernel
def cert530 : List NodeSpec := [([0,1,3,4,17,58],[7],[0]),([0,1,2,3,17,51],[21],[0]),([0,1,2,3,4,55],[0,7,8,22],[0,2]),([0,1,2,3,4,57],[23],[0]),([0,1,3,4,58,70],[],[0]),([0,1,3,4,57,58],[27],[0]),([0,1,2,3,4,70],[1],[0]),([0,2,3,4,7,22],[],[0]),([0,1,3,4,17,69],[7],[0]),([0,1,2,3,4,71],[1,16],[0]),([0,1,2,3,4,77],[],[0]),([0,1,3,4,25,69],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert600 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert530 = true := by decide +kernel
def cert534 : List NodeSpec := cert623 [([0,1,2,3,4,72],[]),([2,3,4,8,13,49],[34]),([0,3,4,8,13,17],[]),([0,2,3,4,8,50],[]),([0,2,3,4,8,39],[0]),([0,1,3,4,17,42],[7]),([0,1,2,3,4,24],[]),([0,1,2,3,4,45],[16]),([1,2,3,4,42,49],[8]),([0,2,3,4,41,42],[8]),([0,1,3,4,25,42],[]),([0,1,2,3,4,80],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert604 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert534 = true := by decide +kernel
def cert535 : List NodeSpec := cert623 [([0,1,4,9,11,17],[7,8]),([0,1,3,4,9,85],[8]),([0,1,2,3,4,19],[1,16]),([0,1,4,9,15,17],[7,8]),([0,1,3,4,9,64],[0]),([0,1,2,4,15,87],[1]),([0,1,2,3,4,37],[0]),([0,1,2,3,4,93],[1]),([0,1,2,3,4,94],[]),([0,2,3,4,14,41],[]),([0,1,3,4,17,41],[6,7]),([0,1,2,3,4,36],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert605 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert535 = true := by decide +kernel
def cert536 : List NodeSpec := [([1,2,3,4,9,49],[8],[0]),([1,3,4,9,17,18],[],[0]),([1,3,4,9,17,21],[],[0]),([0,1,4,9,17,29],[],[0]),([0,1,4,9,17,87],[7],[0]),([0,1,3,4,17,82],[7],[0]),([0,1,3,4,17,83],[7,40],[0]),([0,1,3,4,9,43],[0],[0]),([0,1,3,4,9,44],[],[0]),([0,1,2,3,4,103],[0,7,16,41],[0,1]),([0,1,2,3,4,90],[1],[0,1,3]),([0,1,2,3,4,92],[42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert606 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert536 = true := by decide +kernel
def cert537 : List NodeSpec := [([0,1,2,3,4,104],[],[0]),([0,1,2,3,4,21],[],[0]),([1,2,3,4,19,21],[8],[0]),([0,2,3,4,35],[],[0,1,2,4]),([0,1,2,3,4,35],[],[0]),([0,2,3,4,19,35],[1],[0,2]),([0,2,3,4,19,73],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,3,4,19,85],[8,44],[0]),([0,1,2,3,19,89],[],[0,2]),([0,1,2,3,91],[],[0]),([0,1,2,3,4,91],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert607 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert537 = true := by decide +kernel
def cert538 : List NodeSpec := [([0,1,2,3,19,91],[16],[0]),([1,2,3,4,9,21],[8],[0]),([0,2,3,4,9,35],[],[0,2]),([0,1,2,3,9,91],[],[0]),([0,1,2,3,4,48],[],[0]),([0,1,2,3,4,97],[],[0,1]),([0,1,3,4,10,108],[],[0,3]),([0,1,2,4,29,88],[16],[0]),([0,1,2,3,4,111],[1],[0,3]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,112],[],[0]),([0,2,3,4,12,100],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert608 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert538 = true := by decide +kernel
def cert539 : List NodeSpec := [([0,1,3,4,12,108],[],[0]),([0,1,2,4,29,95],[16],[0]),([0,1,2,3,4,118],[],[0]),([0,1,2,3,4,117],[8],[0]),([0,1,2,3,4,64],[],[0]),([0,1,2,3,4,39],[16],[0,3]),([0,1,2,4,30,95],[],[0]),([0,1,2,3,4,116],[],[0]),([0,1,3,4,17,49],[7],[0]),([0,1,2,3,4,78],[],[0]),([0,2,3,4,13,41],[8],[0]),([0,1,4,13,15,17],[7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert609 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert539 = true := by decide +kernel
def cert540 : List NodeSpec := [([0,1,3,4,13,64],[8],[0]),([0,3,4,13,17,22],[],[0]),([0,3,4,13,17,40],[],[0]),([0,1,4,13,17,29],[],[0]),([0,1,4,13,17,50],[7],[0]),([0,1,3,4,17,52],[7,58],[0]),([0,1,3,4,17,53],[7],[0]),([0,1,3,4,13,43],[1],[0]),([0,1,3,4,13,44],[],[0]),([0,2,3,4,13,100],[8],[0,1]),([0,1,2,3,4,110],[],[0]),([0,1,2,3,4,61],[8,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert610 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert540 = true := by decide +kernel
def cert541 : List NodeSpec := [([0,1,2,3,4,67],[],[0,2,3]),([0,1,2,3,4,120],[1,7,16,60],[0,1]),([0,1,2,3,4,59],[],[0]),([0,1,2,4,39,50],[8,62],[0]),([0,1,2,3,4,62],[],[0,2]),([0,1,2,3,4,63],[],[0]),([0,1,2,3,4,22],[],[0]),([0,2,3,4,22,39],[8],[0,2]),([0,1,2,3,65],[],[0]),([0,1,2,3,4,65],[],[0]),([0,1,2,3,39,65],[16],[0]),([0,1,2,3,39,66],[],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert611 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert541 = true := by decide +kernel
def cert531 : List NodeSpec := cert623 [([0,2,3,4,13,22],[8,64]),([0,1,2,3,13,65],[]),([1,2,3,4,18,19],[]),([0,2,3,4,17,56],[]),([0,2,3,4,17,79],[]),([0,1,2,3,17,98],[66]),([0,2,3,4,17,35],[]),([0,2,3,4,17,73],[]),([0,1,3,4,17,85],[8]),([0,1,2,3,17,91],[67]),([1,2,3,4,20,21],[]),([0,1,3,4,17,96],[8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert601 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert531 = true := by decide +kernel
def cert532 : List NodeSpec := [([0,1,2,3,4,47],[7,8,16],[0]),([0,1,3,4,21,26],[16],[0]),([0,1,2,3,4,99],[],[0]),([0,1,2,3,4,23],[7,8,16],[0]),([0,1,3,4,22,26],[16],[0,5]),([0,1,2,3,4,33],[],[0]),([0,2,3,4,22,38],[72],[0]),([0,1,3,4,17,60],[8],[0]),([0,2,3,4,39,40],[],[0]),([0,1,3,4,17,64],[8],[0,2]),([0,1,2,3,17,65],[74],[0]),([0,1,2,3,17,119],[76],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert602 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert532 = true := by decide +kernel
def cert533 : List NodeSpec := [([0,1,17,26,29],[7,8,16,77,78],[0,1,2,3]),([0,1,4,17,26,107],[7,8],[0]),([0,1,2,3,4,105],[],[0]),([0,1,2,3,4,106],[],[0]),([0,1,2,3,4,108],[],[0]),([0,1,3,4,43,108],[8],[0]),([0,1,3,4,17,108],[8],[0]),([0,1,2,3,4,75],[],[0]),([0,1,2,3,4,76],[],[0,3]),([0,1,2,3,4,43],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert603 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert533 = true := by decide +kernel
def cert574 : List NodeSpec := cert529 ++ cert530 ++ cert534 ++ cert535 ++ cert536 ++ cert537 ++ cert538 ++ cert539 ++ cert540 ++ cert541 ++ cert531 ++ cert532 ++ cert533
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert564 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert552 5 cert574 = true := by
  unfold cert574 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cert599,cert600⟩,cert604⟩,cert605⟩,cert606⟩,cert607⟩,cert608⟩,cert609⟩,cert610⟩,cert611⟩,cert601⟩,cert602⟩,cert603⟩
def cert554 : BT (List (List Nat)) := buildBucketsBT cert619 cert574
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert555 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 5 xs.toFinset) cert554 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert553 cert564
def cert542 : List NodeSpec := [([0,1,2,3,4,5,17],[0,1,2,7,8,11],[0,2]),([0,1,3,4,28],[0,2,5,6,14,15],[0,1,3]),([0,1,2,3,4,28],[0,2,5,6,7,8,14,15,16],[0,1]),([0,2,3,4,6,13],[0,1,5,8,17,20],[0,1]),([0,1,2,3,4,6,17],[1,7,8,11,17],[0,2]),([0,1,3,4,58],[1,5,17,24,25,26],[0,1,3]),([0,1,2,3,4,58],[0,1,5,7,8,16,17,24,25,26],[0,1]),([0,1,2,3,4,7,17],[0,1,7,8,28],[0,2]),([0,1,2,3,4,69],[0,1,7,8,16],[0,1]),([0,2,3,4,8,13],[0,1,5,8,20,31],[0,1]),([0,1,2,3,4,8,17],[1,5,7,8,31],[0,2]),([0,1,2,3,4,42],[5,6,7,16,35],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert612 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert542 = true := by decide +kernel
def cert543 : List NodeSpec := [([0,1,2,3,4,9,11],[7,8],[0,2]),([0,1,2,3,4,9,15],[7,8],[0]),([0,1,2,3,4,41],[0,2,5,6,7,8,16,38],[0,1]),([0,1,2,3,4,9,41],[0,1,5,8,38],[0]),([0,1,2,3,4,9,42],[1,5,35],[0]),([0,1,3,4,9,17],[0,7,8,36,39],[0]),([0,1,2,3,4,9,29],[7,8,16,36],[0,1,3,4]),([0,1,2,3,4,19],[1,16,43,45],[0,1,2,4]),([0,1,2,3,4,9,19],[5,7,37,45],[0,2]),([0,1,2,3,4,87],[0,1,7,8,16,36,46,47],[0,1,2]),([0,1,2,3,4,9,87],[0,7,8,36],[0,2]),([0,1,2,3,4,10,29],[0,7,8,16,48],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert613 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert543 = true := by decide +kernel
def cert544 : List NodeSpec := [([0,1,2,3,4,88],[0,1,5,7,8,16,50,51],[0]),([0,1,2,3,4,12,29],[1,7,8,16,52],[0,1]),([0,1,2,3,4,95],[0,1,5,7,8,16,54],[0]),([0,1,2,3,4,49],[0,1,5,7,8,16,20,34,57],[0,1,2,5]),([0,1,2,3,4,13,49],[0,1,5,8,34],[0]),([0,1,2,3,4,13,42],[0,5,6],[0]),([0,1,2,3,4,13,15],[7,8],[0,2]),([0,1,3,4,13,17],[1,7,8,20,55],[0,2]),([0,1,2,3,4,13,29],[1,7,8,16,55],[0,1,3,4]),([0,1,2,3,4,50],[0,1,7,8,16,55,61,62],[0,1,2]),([0,1,2,3,4,13,50],[1,7,8,55],[0]),([0,1,2,3,4,39],[0,16,54,63],[0,1,2,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert614 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert544 = true := by decide +kernel
def cert545 : List NodeSpec := [([0,1,2,3,4,13,39],[7,56,63],[0]),([0,1,2,3,4,17,18],[0,7,8,11,65],[0,2]),([0,1,2,3,4,17,19],[0,11,43],[0,2]),([0,1,2,3,4,17,20],[0,68],[0,2]),([0,1,2,3,4,21],[1,7,8,16,69,70],[0,2,3]),([0,1,2,3,4,17,21],[0,7,8,69],[0,2]),([0,1,2,3,4,22],[0,7,8,16,64,71],[0,2,3]),([0,1,2,3,4,17,22],[1,7,8,64],[0,2]),([0,1,2,3,4,17,38],[1,73],[0,2]),([0,1,2,3,4,17,39],[1,11,54],[0,2]),([0,1,2,3,4,17,40],[1,7,8,11,75],[0,2]),([0,1,3,4,17,26],[7,8,11,16,77],[0,1,2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert615 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert545 = true := by decide +kernel
def cert546 : List NodeSpec := [([0,1,2,3,4,43],[0,1,11,79,80],[0,2,3]),([0,1,2,3,4,17,43],[11,16,79],[0,2,3]),([0,1,2,3,4,44],[0,1,7,8,11,81,82],[0,2,3]),([0,1,2,3,4,17,44],[7,8,11,16,81],[0,1,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert616 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert546 = true := by decide +kernel
def cert575 : List NodeSpec := cert542 ++ cert543 ++ cert544 ++ cert545 ++ cert546
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert565 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert554 6 cert575 = true := by
  unfold cert575 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨cert612,cert613⟩,cert614⟩,cert615⟩,cert616⟩
def cert556 : BT (List (List Nat)) := buildBucketsBT cert619 cert575
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert557 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 6 xs.toFinset) cert556 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert555 cert565
def cert547 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,16],[0,1,2,3]),([0,1,2,3,4,6],[0,1,5,7,8,16,17,18,19],[0,1,2,3]),([0,1,2,3,4,7],[0,1,7,8,16,28,29,30],[0,1,2,3]),([0,1,2,3,4,8],[0,1,5,7,8,16,31,32,33],[0,1,2,3]),([0,1,2,3,4,9],[0,1,5,7,8,16,36,37],[0,1]),([0,1,2,3,4,10],[0,1,5,7,8,16,48,49],[0,1]),([0,1,2,3,4,12],[0,1,5,7,8,16,52,53],[0,1]),([0,1,2,3,4,13],[0,1,5,7,8,16,55,56],[0,1,2,5]),([0,1,2,3,4,17],[0,1,7,8,11,16],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert617 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert556 7 cert547 = true := by decide +kernel
def cert576 : List NodeSpec := cert547
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert566 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert556 7 cert576 = true := cert617
def cert558 : BT (List (List Nat)) := buildBucketsBT cert619 cert576
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert559 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 7 xs.toFinset) cert558 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert557 cert566
def cert548 : List NodeSpec := [([0,1,2,3,4],[7,8,16],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert618 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert558 8 cert548 = true := by decide +kernel
def cert577 : List NodeSpec := cert548
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert567 : checkNodesBT cert619 cert569 cert570 cert579 cert495 cert558 8 cert577 = true := cert618
def cert560 : BT (List (List Nat)) := buildBucketsBT cert619 cert577
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert561 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert569 8 xs.toFinset) cert560 := buildBucketsBT_sound (by decide) cert578 cert620 cert580 cert521 cert559 cert567
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert549 : Lower cert582 cert569 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) cert561 (by decide +kernel)
def cert811 : List Nat := varsOf 7
def cert805 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def cert810 : List Nat := [5,6,3,3,6,5]
def cert806 : List Nat := [4,4,1,2,2,1]
def cert798 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def cert814 : BT Decor := buildWiresBT 2 cert798 cert227
def cert795 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2)],[(1,2),(0,1)],[(1,2),(0,2)]]
def cert796 : BT (List (Nat × Nat)) := btOfList 3 cert795
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert807 : goodPairs cert805 cert810 cert806 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert799 : ∀ x ∈ cert798, faithful cert810 cert806 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert815 : btAll (fun x => faithful cert810 cert806 x ∧ x.1 < 2^128) cert814 := buildWiresBT_faithful cert799
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert797 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert805 = cert805) cert796 := btAll_ofList (autos_of (by decide +kernel))
def cert808 : BT (Option BoundPool) := buildPoolsBT 1 cert814 cert811 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert812 : btAll (fun o => ∀ p, o = some p → Slice cert811 cert805 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert811 cert805 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert809 : btAll (fun o => ∀ c, o = some c → ValidPool cert811 cert805 c) cert808 := buildPoolsBT_sound cert812
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert804 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert805 (3 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert813 : checkNodesBT cert814 cert805 cert506 cert808 cert796 cert466 3 cert499 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert803 : checkNodesBT cert814 cert805 cert506 cert808 cert796 cert466 3 cert508 = true := cert813
def cert801 : BT (List (List Nat)) := buildBucketsBT cert814 cert508
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert802 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert805 3 xs.toFinset) cert801 := buildBucketsBT_sound (by decide) cert807 cert815 cert809 cert797 cert804 cert803
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert800 : Lower cert811 cert805 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) cert802 (by decide +kernel)
def cert835 : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert834 : Lower cert478 cert835 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,6,14)]) (by decide +kernel) cert800
def cert847 : Nat := 0xeeaaee00eeaaee00eeaaee00eeaaee00
def cert854 : List Nat := [9,19,9,10,10,19,17,26]
def cert849 : List Nat := [8,18,1,2,8,3,1,18]
def cert848 : Nat := fullMask 8
def cert839 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,103,100),(0xcccccccccccccccccccccccccccccccc,186,170),(0xff00ff00ff00ff00ff00ff00ff00ff00,157,17),(0xffff0000ffff0000ffff0000ffff0000,226,130)]
def cert857 : BT Decor := buildWiresBT 2 cert839 cert227
def cert836 : List (List (Nat × Nat)) := [[],[(1,4),(0,3)]]
def cert837 : BT (List (Nat × Nat)) := btOfList 1 cert836
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert851 : goodPairs cert847 cert854 cert849 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert840 : ∀ x ∈ cert839, faithful cert854 cert849 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert858 : btAll (fun x => faithful cert854 cert849 x ∧ x.1 < 2^128) cert857 := buildWiresBT_faithful cert840
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert838 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert847 = cert847) cert837 := btAll_ofList (autos_of (by decide +kernel))
def cert852 : BT (Option BoundPool) := buildPoolsBT 1 cert857 cert493 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert855 : btAll (fun o => ∀ p, o = some p → Slice cert493 cert847 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert493 cert847 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert853 : btAll (fun o => ∀ c, o = some c → ValidPool cert493 cert847 c) cert852 := buildPoolsBT_sound cert855
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert846 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert847 (3 - 1) xs.toFinset) cert466 := trivial
def cert841 : List NodeSpec := cert623 [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert856 : checkNodesBT cert857 cert847 cert848 cert852 cert837 cert466 3 cert841 = true := by decide +kernel
def cert850 : List NodeSpec := cert841
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert845 : checkNodesBT cert857 cert847 cert848 cert852 cert837 cert466 3 cert850 = true := cert856
def cert843 : BT (List (List Nat)) := buildBucketsBT cert857 cert850
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert844 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert847 3 xs.toFinset) cert843 := buildBucketsBT_sound (by decide) cert851 cert858 cert853 cert838 cert846 cert845
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert842 : Lower cert493 cert847 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,8,10),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) cert844 (by decide +kernel)
def cert691 : List Nat := [12,12,36,36,40,40,12,36,40]
def cert685 : List Nat := [8,4,32,4,32,8,32,8,4]
def cert639 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def cert629 : BT Decor := buildWiresBT 2 cert639 cert227
def cert633 : List (List (Nat × Nat)) := []
def cert635 : BT (List (Nat × Nat)) := btOfList 1 cert633
def cert625 : BT (Option BoundPool) := buildPoolsBT 1 cert629 cert31 cert480 cert195
lemma cert675 : goodPairs cert13 cert691 cert685 := goodPairs_of (by decide +kernel)
lemma cert640 : ∀ x ∈ cert639, faithful cert691 cert685 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma cert630 : btAll (fun x => faithful cert691 cert685 x ∧ x.1 < 2^128) cert629 := buildWiresBT_faithful cert640
set_option maxRecDepth 500000 in
lemma cert636 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert13 = cert13) cert635 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma cert703 : btAll (fun o => ∀ p, o = some p → Slice cert31 cert13 p.1 p.2) cert480 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert31 cert13 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma cert626 : btAll (fun o => ∀ c, o = some c → ValidPool cert31 cert13 c) cert625 := buildPoolsBT_sound cert703
lemma cert649 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert13 (0 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert663 : checkNodesBT cert629 cert13 cert128 cert625 cert635 cert466 0 cert178 = true := by decide +kernel
def cert643 : BT (List (List Nat)) := buildBucketsBT cert629 cert178
set_option maxRecDepth 500000 in
lemma cert644 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert13 0 xs.toFinset) cert643 :=
  buildBucketsBT_sound (by decide) cert675 cert630 cert626 cert636 cert649 cert663
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert664 : checkNodesBT cert629 cert13 cert128 cert625 cert635 cert643 1 cert178 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert645 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert13 1 xs.toFinset) cert643 :=
  buildBucketsBT_sound (by decide) cert675 cert630 cert626 cert636 cert644 cert664
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert665 : checkNodesBT cert629 cert13 cert128 cert625 cert635 cert643 2 cert178 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert646 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert13 2 xs.toFinset) cert643 :=
  buildBucketsBT_sound (by decide) cert675 cert630 cert626 cert636 cert645 cert665
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert666 : checkNodesBT cert629 cert13 cert128 cert625 cert635 cert643 3 cert179 = true := by decide +kernel
def cert647 : BT (List (List Nat)) := buildBucketsBT cert629 cert179
set_option maxRecDepth 500000 in
lemma cert648 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert13 3 xs.toFinset) cert647 :=
  buildBucketsBT_sound (by decide) cert675 cert630 cert626 cert636 cert646 cert666
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert708 : forestRootCheck cert31 cert13 [(VAR 2,12,8),(VAR 3,12,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert707 : bucketContainsBT cert647 cert31 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert677 : Lower cert31 cert13 4 := lower_of_forestBT cert708 cert648 cert707

lemma cert684 : carryOK [(1,4),(1,5),(1,3),(1,2)] cert22 cert0 cert31 cert13 = true := by decide +kernel
lemma cert683 : Lower cert22 cert0 4 := carry_of cert684 cert677

lemma cert679 : carryOK [(1,3),(1,2)] cert306 cert293 cert31 cert13 = true := by decide +kernel
lemma cert678 : Lower cert306 cert293 4 := carry_of cert679 cert677

lemma cert681 : carryOK [(1,2)] cert30 cert12 cert31 cert13 = true := by decide +kernel
lemma cert680 : Lower cert30 cert12 4 := carry_of cert681 cert677

def cert861 : List Nat := varsOf 49
def cert860 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert859 : Lower cert861 cert860 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4)]) (roots2 := cert811) (T2 := cert805) (by decide +kernel) cert800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert712 : Lower cert306 cert293 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := cert811) (T2 := cert805) (by decide +kernel) cert800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert711 : Lower cert26 cert298 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,34,50)]) (by decide +kernel) cert712
def cert624 : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
def cert692 : List Nat := [6,6,10,10,12,12,34,34,36,36,40,40,6,6,10,10,12,12,34,34,36,36,40,40]
def cert686 : List Nat := [4,2,8,2,8,4,32,2,32,4,32,8,8,32,4,32,2,32,4,8,2,8,2,4]
def cert674 : Nat := fullMask 24
def cert641 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def cert706 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def cert631 : BT Decor := buildWiresBT 4 cert641 cert706
def cert634 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def cert637 : BT (List (Nat × Nat)) := btOfList 4 cert634
def cert702 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 8 0,4)]
def cert704 : BT (Option (Nat × Nat)) := btOfList 2 cert702
def cert693 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def cert627 : BT (Option BoundPool) := buildPoolsBT 2 cert631 cert24 cert704 cert693
lemma cert676 : goodPairs cert624 cert692 cert686 := goodPairs_of (by decide +kernel)
lemma cert642 : ∀ x ∈ cert641, faithful cert692 cert686 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma cert632 : btAll (fun x => faithful cert692 cert686 x ∧ x.1 < 2^128) cert631 := buildWiresBT_faithful cert642
set_option maxRecDepth 500000 in
lemma cert638 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert624 = cert624) cert637 := btAll_ofList (autos_of (by decide +kernel))
lemma cert695 : sliceDirectCheck 4 0 0 cert24 cert624 cert30 cert12 = true := by decide +kernel
lemma cert694 : Slice cert24 cert624 (subcubeFast 4 0) 4 := slice_fast_direct cert695 cert680
lemma cert697 : sliceDirectCheck 2 0 0 cert24 cert624 cert31 cert13 = true := by decide +kernel
lemma cert696 : Slice cert24 cert624 (subcubeFast 2 0) 4 := slice_fast_direct cert697 cert677
lemma cert699 : sliceDirectCheck 32 0 0 cert24 cert624 cert22 cert0 = true := by decide +kernel
lemma cert698 : Slice cert24 cert624 (subcubeFast 32 0) 4 := slice_fast_direct cert699 cert683
lemma cert701 : sliceDirectCheck 8 0 0 cert24 cert624 cert306 cert293 = true := by decide +kernel
lemma cert700 : Slice cert24 cert624 (subcubeFast 8 0) 4 := slice_fast_direct cert701 cert678
set_option maxRecDepth 500000 in
lemma cert705 : btAll (fun o => ∀ p, o = some p → Slice cert24 cert624 p.1 p.2) cert704 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert24 cert624 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert694) (forall_cons (fun _ h => by cases h; exact cert696) (forall_cons (fun _ h => by cases h; exact cert698) (forall_cons (fun _ h => by cases h; exact cert700) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma cert628 : btAll (fun o => ∀ c, o = some c → ValidPool cert24 cert624 c) cert627 := buildPoolsBT_sound cert705
lemma cert662 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 (0 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert667 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert466 0 cert178 = true := by decide +kernel
def cert650 : BT (List (List Nat)) := buildBucketsBT cert631 cert178
set_option maxRecDepth 500000 in
lemma cert651 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 0 xs.toFinset) cert650 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert662 cert667
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert668 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert650 1 cert178 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert652 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 1 xs.toFinset) cert650 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert651 cert668
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert669 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert650 2 cert178 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert653 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 2 xs.toFinset) cert650 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert652 cert669
def cert687 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert670 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert650 3 cert687 = true := by decide +kernel
def cert654 : BT (List (List Nat)) := buildBucketsBT cert631 cert687
set_option maxRecDepth 500000 in
lemma cert655 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 3 xs.toFinset) cert654 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert653 cert670
def cert688 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert671 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert654 4 cert688 = true := by decide +kernel
def cert656 : BT (List (List Nat)) := buildBucketsBT cert631 cert688
set_option maxRecDepth 500000 in
lemma cert657 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 4 xs.toFinset) cert656 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert655 cert671
def cert689 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert672 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert656 5 cert689 = true := by decide +kernel
def cert658 : BT (List (List Nat)) := buildBucketsBT cert631 cert689
set_option maxRecDepth 500000 in
lemma cert659 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 5 xs.toFinset) cert658 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert657 cert672
def cert690 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert673 : checkNodesBT cert631 cert624 cert674 cert627 cert637 cert658 6 cert690 = true := by decide +kernel
def cert660 : BT (List (List Nat)) := buildBucketsBT cert631 cert690
set_option maxRecDepth 500000 in
lemma cert661 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert624 6 xs.toFinset) cert660 :=
  buildBucketsBT_sound (by decide) cert676 cert632 cert628 cert638 cert659 cert673
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert710 : forestRootCheck cert24 cert624 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert709 : bucketContainsBT cert660 cert24 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert682 : Lower cert24 cert624 7 := lower_of_forestBT cert710 cert661 cert709

def cert714 : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert713 : Lower cert23 cert714 7 := carry_of (swaps := [(4,5)]) (roots2 := cert24) (T2 := cert624) (by decide +kernel) cert682
def cert717 : List Nat := varsOf 57
def cert716 : Nat := 0xffffffaaffaaff00ffffffaaffaaff00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert715 : Lower cert717 cert716 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) cert859
def cert794 : List Nat := varsOf 43
def cert793 : Nat := 0xee88ee88ee00ee00ee88ee88ee00ee00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert792 : Lower cert794 cert793 5 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3)]) (roots2 := cert478) (T2 := cert835) (by decide +kernel) cert834
def cert818 : List Nat := varsOf 51
def cert817 : Nat := 0xeeee8888aaaa0000eeee8888aaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert816 : Lower cert818 cert817 5 := carry_of (swaps := [(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := cert26) (T2 := cert298) (by decide +kernel) cert711
def cert821 : List Nat := varsOf 25
def cert820 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert819 : Lower cert821 cert820 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := cert811) (T2 := cert805) (by decide +kernel) cert800
def cert823 : Nat := 0xffaaaa00aaaaaa00ffaaaa00aaaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert822 : Lower cert717 cert823 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (roots2 := cert478) (T2 := cert835) (by decide +kernel) cert834
def cert826 : List Nat := varsOf 26
def cert825 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert824 : Lower cert826 cert825 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := cert811) (T2 := cert805) (by decide +kernel) cert800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert827 : Lower cert30 cert12 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(0,1)]) (roots2 := cert811) (T2 := cert805) (by decide +kernel) cert800
def cert829 : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert828 : Lower cert27 cert829 5 := carry_of (swaps := [(2,3)]) (roots2 := cert26) (T2 := cert298) (by decide +kernel) cert711
def cert831 : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert830 : Lower cert493 cert831 7 := carry_of (swaps := [(0,1),(1,2)]) (roots2 := cert23) (T2 := cert714) (by decide +kernel) cert713
def cert833 : Nat := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert832 : Lower cert794 cert833 5 := carry_of (swaps := [(2,3),(3,4),(1,2),(0,1)]) (roots2 := cert717) (T2 := cert716) (by decide +kernel) cert715
def cert761 : List Nat := varsOf 59
def cert749 : Nat := 0xffeeee88eeaaee00ffeeee88eeaaee00
def cert760 : List Nat := [9,10,17,10,17,9,50,17,50,35,41,19,50,56,35,26,56,41,11,19,35,56,26,11,17,42,42,25,25,10,9,9,9,49,10,11,49,35,9,41,17,19]
def cert751 : List Nat := [8,8,18,2,16,1,34,1,18,3,40,18,48,24,33,18,40,33,3,3,34,48,24,8,24,34,40,1,24,24,0,24,3,48,0,1,33,1,33,1,0,1]
def cert750 : Nat := fullMask 42
def cert719 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fbd99e4eb5,0x2f9080e42a0),(0xcccccccccccccccccccccccccccccccc,0x22c26dcdb4a,0x1021c8b4c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcdfee7a42b,0xb5c12403),(0xffff0000ffff0000ffff0000ffff0000,0x3121969b9d4,0x2b160b914),(0xffffffff00000000ffffffff00000000,0xb206337740,0x5206335440)]
def cert778 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,2,3),(1,2,5),(0,1,24),(2,1,24),(0,4,6),(2,4,7),(1,2,8),(3,0,29),(0,4,10),(2,4,10),(0,4,17),(1,8,23),(1,1,9),(2,1,9),(2,4,9),(1,0,20),(1,2,38),(3,2,38),(2,10,20),(1,0,25),(1,1,12),(2,1,12),(1,2,12),(0,1,45),(1,1,45),(2,1,45),(3,1,45),(2,2,12),(2,4,12),(1,12,16),(1,12,33),(3,12,17),(1,12,19),(2,4,46),(0,4,47),(3,2,13),(0,4,13),(1,1,59),(2,1,59),(1,2,59),(2,2,59),(2,17,59),(0,13,17),(2,13,19),(0,1,62),(3,1,62),(1,2,14),(1,14,19),(0,4,21),(1,2,22)]
def cert790 : BT Decor := buildWiresBT 7 cert719 cert778
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert757 : goodPairs cert749 cert760 cert751 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert720 : ∀ x ∈ cert719, faithful cert760 cert751 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert791 : btAll (fun x => faithful cert760 cert751 x ∧ x.1 < 2^128) cert790 := buildWiresBT_faithful cert720
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert718 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert749 = cert749) cert837 := btAll_ofList (autos_of (by decide +kernel))
def cert774 : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 2,4),some (subcubeFast 16 0,5),some (subcubeFast 32 0,4)]
def cert775 : BT (Option (Nat × Nat)) := btOfList 4 cert774
def cert777 : List PoolSpec := [(3,[]),(6,[]),(2,[(0,0,1)]),(4,[]),(2,[(0,0,1),(1,2,5)]),(10,[]),(1,[]),(11,[]),(2,[]),(8,[]),(5,[]),(9,[]),(2,[(1,0,1)]),(0,[]),(2,[(2,0,1)]),(6,[(2,4,7)]),(0,[(1,0,2)]),(2,[(3,0,1)]),(1,[(3,0,1)]),(6,[(0,4,17)]),(8,[(0,4,17)]),(7,[]),(2,[(3,0,1),(1,1,2)]),(2,[(0,0,2)]),(2,[(0,0,2),(1,1,9)]),(2,[(0,0,2),(2,1,9)]),(2,[(1,0,2)]),(2,[(2,0,2)]),(2,[(0,0,3)]),(0,[(1,2,5)]),(2,[(0,1,2)]),(1,[(2,4,12)]),(1,[(1,2,12)]),(2,[(0,0,3),(1,2,12)]),(2,[(1,1,2)]),(2,[(2,1,2)]),(2,[(3,1,2)]),(2,[(0,0,3),(1,1,12)]),(2,[(0,0,3),(2,1,12)]),(2,[(0,0,3),(2,2,12)]),(2,[(1,0,3)]),(10,[(0,4,13)]),(3,[(0,4,13)]),(2,[(2,0,3)]),(2,[(2,0,3),(1,2,14)]),(2,[(3,0,3)]),(2,[(0,1,3)]),(2,[(0,1,3),(1,0,20)]),(2,[(1,1,3)]),(6,[(0,4,21)]),(10,[(0,4,21)]),(2,[(2,1,3)])]
def cert758 : BT (Option BoundPool) := buildPoolsBT 6 cert790 cert761 cert775 cert777
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert765 : Slice cert761 cert749 (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert842
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert764 : Slice cert761 cert749 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert792
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert773 : Slice cert761 cert749 (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert859
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert772 : Slice cert761 cert749 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert816
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert771 : Slice cert761 cert749 (subcubeFast 2 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert819
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert770 : Slice cert761 cert749 (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert822
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert769 : Slice cert761 cert749 (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert824
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert768 : Slice cert761 cert749 (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert827
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert767 : Slice cert761 cert749 (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert828
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert766 : Slice cert761 cert749 (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) cert830
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert763 : Slice cert761 cert749 (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert832
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert762 : Slice cert761 cert749 (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert715
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert776 : btAll (fun o => ∀ p, o = some p → Slice cert761 cert749 p.1 p.2) cert775 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert761 cert749 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert762) (forall_cons (fun _ h => by cases h; exact cert763) (forall_cons (fun _ h => by cases h; exact cert766) (forall_cons (fun _ h => by cases h; exact cert767) (forall_cons (fun _ h => by cases h; exact cert768) (forall_cons (fun _ h => by cases h; exact cert769) (forall_cons (fun _ h => by cases h; exact cert770) (forall_cons (fun _ h => by cases h; exact cert771) (forall_cons (fun _ h => by cases h; exact cert772) (forall_cons (fun _ h => by cases h; exact cert773) (forall_cons (fun _ h => by cases h; exact cert764) (forall_cons (fun _ h => by cases h; exact cert765) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert759 : btAll (fun o => ∀ c, o = some c → ValidPool cert761 cert749 c) cert758 := buildPoolsBT_sound cert776
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert748 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 (4 - 1) xs.toFinset) cert466 := trivial
def cert721 : List NodeSpec := cert623 [([1,3,4,42,45],[]),([1,2,3,42,51],[]),([1,3,4,30,45],[]),([0,1,3,33,45],[]),([0,1,2,3,53],[]),([0,1,3,45,56],[]),([0,1,3,45,57],[]),([0,1,2,3,64],[]),([0,2,3,59,67],[]),([0,2,3,59,68],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert779 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert466 4 cert721 = true := by decide +kernel
def cert752 : List NodeSpec := cert721
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert743 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert466 4 cert752 = true := cert779
def cert733 : BT (List (List Nat)) := buildBucketsBT cert790 cert752
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert734 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 4 xs.toFinset) cert733 := buildBucketsBT_sound (by decide) cert757 cert791 cert759 cert718 cert748 cert743
def cert722 : List NodeSpec := cert623 [([0,1,3,4,10,29],[1,8]),([0,2,3,8,33],[13,19,20]),([0,1,2,3,4,34],[]),([1,2,3,4,10,38],[1,5]),([0,1,2,3,4,39],[1,7,8,13]),([0,1,2,3,4,41],[]),([1,2,3,4,12,42],[1,9,21,29]),([0,1,2,3,16,51],[0,5,7,10,31]),([0,1,2,3,4,52],[0,1,7,8]),([1,2,3,4,12,30],[13]),([0,1,3,4,17,45],[0,5,32,33]),([0,1,2,3,17,51],[7,10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert780 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert733 5 cert722 = true := by decide +kernel
def cert723 : List NodeSpec := cert623 [([0,1,2,3,12,33],[7,13,19,20]),([0,1,2,3,4,54],[0,7,8]),([0,1,3,4,18,45],[0]),([0,1,2,3,18,51],[]),([0,1,3,4,19,45],[]),([0,1,2,3,19,51],[]),([0,1,2,3,4,55],[0]),([0,1,3,4,45,46],[0,5,32,33]),([0,1,3,4,45,47],[0,5,32,33]),([0,1,3,4,45,48],[]),([0,1,3,4,45,49],[]),([0,1,2,3,17,59],[7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert781 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert733 5 cert723 = true := by decide +kernel
def cert724 : List NodeSpec := cert623 [([0,1,2,3,4,65],[7,8]),([0,1,3,4,18,58],[13]),([0,1,2,3,18,59],[]),([0,1,2,3,19,59],[6,41]),([0,1,2,3,4,66],[]),([0,1,2,3,59,60],[7]),([0,1,2,3,59,61],[]),([0,1,2,3,59,62],[]),([0,1,2,3,59,63],[6,40]),([0,1,2,3,4,62],[1,6,13]),([0,1,2,3,4,70],[]),([0,1,2,3,4,40],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert782 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert733 5 cert724 = true := by decide +kernel
def cert753 : List NodeSpec := cert722 ++ cert723 ++ cert724
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert744 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert733 5 cert753 = true := by
  unfold cert753 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨cert780,cert781⟩,cert782⟩
def cert735 : BT (List (List Nat)) := buildBucketsBT cert790 cert753
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert736 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 5 xs.toFinset) cert735 := buildBucketsBT_sound (by decide) cert757 cert791 cert759 cert718 cert734 cert744
def cert725 : List NodeSpec := [([0,1,2,3,4,24],[0,1,3,4,5,6,7,8],[0]),([0,1,2,3,4,27],[0,1,5,6,7,8,9,11,12,13],[0]),([0,1,2,3,28],[0,3,7,10,13,14,15],[0]),([0,1,2,3,4,8,10],[1,9,13,16],[0]),([0,2,3,4,8,17],[0,1,9,13,18,21,22],[0]),([0,1,2,3,4,8,23],[1,3,5,6,13],[0]),([0,1,2,3,4,29],[0,1,5,6,7,8,11,13],[0]),([0,2,3,4,35],[0,9,13,24],[0]),([0,2,3,4,36],[0,1,9,25],[0]),([0,1,2,3,37],[0,3,7,9,10,23],[0]),([0,1,2,3,4,10,20],[0,1,5,6,9,13],[0,1]),([0,1,2,3,4,10,25],[0,1,9,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert783 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert735 6 cert725 = true := by decide +kernel
def cert726 : List NodeSpec := [([0,1,2,3,4,10,26],[1,11,13],[0]),([0,1,2,3,4,31],[0,1,5,6,7,8,9,13,26],[0]),([0,1,2,3,4,32],[1,5,6,7,10,13,26],[0]),([0,1,2,3,4,10],[0,1,5,6,7,8,13,26],[0]),([0,1,2,3,4,12,16],[0,1,5,6,9,13,28,30],[0,1]),([0,1,2,3,4,12,17],[0,1,5,6,9,13,28,34],[0]),([0,1,2,3,4,12,18],[0,1,9,11,13,35],[0]),([0,1,2,3,4,12,19],[0,1,9,13,36],[0]),([0,2,3,4,43],[0,5,13,37],[0]),([0,2,3,4,44],[0,1,5,38],[0]),([0,1,3,4,45],[0,5,33],[0]),([0,1,2,3,4,45],[0,1,5,7,8,9,13,33],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert784 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert735 6 cert726 = true := by decide +kernel
def cert727 : List NodeSpec := [([0,1,3,4,50],[0,5,9,39],[0]),([0,1,2,3,51],[0,5,7,10,28],[0]),([0,1,2,3,4,13,17],[6,13,34,40],[0,1]),([0,1,2,3,4,13,18],[1,6,9,11,35],[0]),([0,1,2,3,4,13,19],[1,5,6,13,36],[0]),([0,1,2,3,4,58],[0,1,3,5,6,7,8,9,13],[0,1]),([0,1,2,3,59],[3,6,7,40,41,42],[0,1]),([0,1,2,3,4,59],[0,1,5,6,7,8,9,13,40],[0]),([0,1,2,3,4,14,18],[0,1,11,13],[0]),([0,1,2,3,4,14,19],[0,13],[0]),([0,1,2,3,4,69],[0,1,6,7,8,9,13,44],[0]),([0,1,2,3,4,15,18],[1,3,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert785 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert735 6 cert727 = true := by decide +kernel
def cert728 : List NodeSpec := cert623 [([0,1,2,3,4,38],[0,1,3,5,7,8,9,13,47]),([0,1,2,3,71],[3,6,7,11,13,48,49,50]),([0,1,2,3,4,71],[0,1,3,7,8,9,11,13,48]),([0,1,2,3,4,72],[0,1,3,6,7,8,9,13])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert786 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert735 6 cert728 = true := by decide +kernel
def cert754 : List NodeSpec := cert725 ++ cert726 ++ cert727 ++ cert728
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert745 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert735 6 cert754 = true := by
  unfold cert754 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨cert783,cert784⟩,cert785⟩,cert786⟩
def cert737 : BT (List (List Nat)) := buildBucketsBT cert790 cert754
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert738 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 6 xs.toFinset) cert737 := buildBucketsBT_sound (by decide) cert757 cert791 cert759 cert718 cert736 cert745
def cert729 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,8,9,10],[0]),([0,1,2,3,4,6],[0,1,3,5,6,8,9,11,12,13],[0]),([0,1,2,3,4,7],[0,1,3,5,6,8,9,10,11,13,14],[0]),([0,1,2,3,4,8],[0,1,3,5,6,8,9,11,13,17,21],[0]),([0,1,2,3,4,9],[0,1,3,5,6,8,9,10,13,23],[0,1]),([0,1,2,3,4,10],[0,1,3,5,6,8,9,11,13,26],[0,1]),([0,1,2,3,4,11],[0,1,3,5,6,8,9,10,11,13,27],[0]),([0,1,2,3,4,12],[0,1,5,8,9,10,13,28],[0]),([0,1,2,3,4,13],[0,1,3,5,6,8,9,13,40],[0,1]),([0,1,2,3,4,14],[0,1,5,6,8,9,10,13,43],[0,1]),([0,1,2,3,4,15],[0,1,3,5,6,8,9,13,45],[0,1]),([0,1,2,3,4,20],[0,1,3,5,8,9,11,13,21,46],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert787 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert737 7 cert729 = true := by decide +kernel
def cert730 : List NodeSpec := cert623 [([0,1,2,3,4,21],[0,1,3,5,6,8,9,11,13,48]),([0,1,2,3,4,22],[0,1,3,5,6,8,9,13,21,51])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert788 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert737 7 cert730 = true := by decide +kernel
def cert755 : List NodeSpec := cert729 ++ cert730
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert746 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert737 7 cert755 = true := by
  unfold cert755 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨cert787,cert788⟩
def cert739 : BT (List (List Nat)) := buildBucketsBT cert790 cert755
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert740 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 7 xs.toFinset) cert739 := buildBucketsBT_sound (by decide) cert757 cert791 cert759 cert718 cert738 cert746
def cert731 : List NodeSpec := [([0,1,2,3,4],[8],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert789 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert739 8 cert731 = true := by decide +kernel
def cert756 : List NodeSpec := cert731
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert747 : checkNodesBT cert790 cert749 cert750 cert758 cert837 cert739 8 cert756 = true := cert789
def cert741 : BT (List (List Nat)) := buildBucketsBT cert790 cert756
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert742 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert749 8 xs.toFinset) cert741 := buildBucketsBT_sound (by decide) cert757 cert791 cert759 cert718 cert740 cert747
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert732 : Lower cert761 cert749 9 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,8,10),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,3,35)]) (by decide +kernel) cert742 (by decide +kernel)
def cert881 : List Nat := [18,24,10,10,24,18]
def cert877 : List Nat := [16,16,2,8,8,2]
def cert870 : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def cert884 : BT Decor := buildWiresBT 2 cert870 cert227
def cert867 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,3)],[(1,4)],[(3,4),(1,3)],[(3,4),(1,4)]]
def cert868 : BT (List (Nat × Nat)) := btOfList 3 cert867
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert878 : goodPairs cert825 cert881 cert877 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert871 : ∀ x ∈ cert870, faithful cert881 cert877 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert885 : btAll (fun x => faithful cert881 cert877 x ∧ x.1 < 2^128) cert884 := buildWiresBT_faithful cert871
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert869 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert825 = cert825) cert868 := btAll_ofList (autos_of (by decide +kernel))
def cert879 : BT (Option BoundPool) := buildPoolsBT 1 cert884 cert826 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert882 : btAll (fun o => ∀ p, o = some p → Slice cert826 cert825 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert826 cert825 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert880 : btAll (fun o => ∀ c, o = some c → ValidPool cert826 cert825 c) cert879 := buildPoolsBT_sound cert882
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert876 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert825 (3 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert883 : checkNodesBT cert884 cert825 cert506 cert879 cert868 cert466 3 cert499 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert875 : checkNodesBT cert884 cert825 cert506 cert879 cert868 cert466 3 cert508 = true := cert883
def cert873 : BT (List (List Nat)) := buildBucketsBT cert884 cert508
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert874 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert825 3 xs.toFinset) cert873 := buildBucketsBT_sound (by decide) cert878 cert885 cert880 cert869 cert876 cert875
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert872 : Lower cert826 cert825 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18)]) (by decide +kernel) cert874 (by decide +kernel)
def cert892 : Nat := 0xaa888800aa888800aa888800aa888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert891 : Lower cert493 cert892 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) cert872
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert894 : Lower cert513 cert505 4 := carry_of (swaps := [(1,2)]) (roots2 := cert826) (T2 := cert825) (by decide +kernel) cert872
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert940 : Lower cert821 cert820 4 := carry_of (swaps := [(0,1)]) (roots2 := cert826) (T2 := cert825) (by decide +kernel) cert872
def cert942 : Nat := 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert941 : Lower cert493 cert942 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,24,26)]) (by decide +kernel) cert940
def cert863 : Nat := 0xfffcfc00fffcfc00fffcfc00fffcfc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert862 : Lower cert23 cert863 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,8,10)]) (by decide +kernel) cert894
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert864 : Lower cert478 cert835 5 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := cert493) (T2 := cert942) (by decide +kernel) cert941
def cert866 : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert865 : Lower cert490 cert866 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2),(2,3)]) (roots2 := cert493) (T2 := cert942) (by decide +kernel) cert941
def cert888 : List Nat := varsOf 19
def cert887 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert886 : Lower cert888 cert887 4 := carry_of (swaps := [(2,3),(0,1),(1,2)]) (roots2 := cert826) (T2 := cert825) (by decide +kernel) cert872
def cert890 : Nat := 0xee888888ee888888ee888888ee888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert889 : Lower cert493 cert890 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) cert886
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert893 : Lower cert23 cert622 5 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := cert493) (T2 := cert892) (by decide +kernel) cert891
def cert896 : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert895 : Lower cert478 cert896 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := cert23) (T2 := cert863) (by decide +kernel) cert862
def cert898 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert897 : Lower cert490 cert898 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := cert23) (T2 := cert863) (by decide +kernel) cert862
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert899 : Lower cert520 cert519 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) cert894
def cert915 : Nat := 0xeee8e8a8eee8e8a8eee8e8a8eee8e8a8
def cert922 : List Nat := [5,14,3,3,14,5,7,3,14,13,25,22,21,25,19,26,13,21,26,26,7,22]
def cert916 : List Nat := [4,12,1,2,10,1,6,6,6,12,17,6,20,9,17,24,9,17,18,10,1,20]
def cert903 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1376ed,0x136424),(0xcccccccccccccccccccccccccccccccc,0x3cc9de,0xc09d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x331b73,0x201bc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xda712,0x9a212),(0xffff0000ffff0000ffff0000ffff0000,0x2efc00,0x26d400)]
def cert935 : List (Nat × Nat × Nat) := [(1,0,2),(2,1,2)]
def cert938 : BT Decor := buildWiresBT 3 cert903 cert935
def cert900 : List (List (Nat × Nat)) := [[],[(3,4)]]
def cert901 : BT (List (Nat × Nat)) := btOfList 1 cert900
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert919 : goodPairs cert915 cert922 cert916 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert904 : ∀ x ∈ cert903, faithful cert922 cert916 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert939 : btAll (fun x => faithful cert922 cert916 x ∧ x.1 < 2^128) cert938 := buildWiresBT_faithful cert904
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert902 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert915 = cert915) cert901 := btAll_ofList (autos_of (by decide +kernel))
def cert931 : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def cert932 : BT (Option (Nat × Nat)) := btOfList 3 cert931
def cert934 : List PoolSpec := [(3,[]),(0,[]),(4,[]),(5,[]),(0,[(1,0,2)]),(6,[]),(1,[]),(7,[]),(2,[]),(3,[(2,1,2)])]
def cert920 : BT (Option BoundPool) := buildPoolsBT 4 cert938 cert582 cert932 cert934
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert930 : Slice cert582 cert915 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert864
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert929 : Slice cert582 cert915 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert865
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert928 : Slice cert582 cert915 (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert889
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert927 : Slice cert582 cert915 (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) cert894
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert926 : Slice cert582 cert915 (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert893
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert925 : Slice cert582 cert915 (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert895
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert924 : Slice cert582 cert915 (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert897
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert923 : Slice cert582 cert915 (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert899
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert933 : btAll (fun o => ∀ p, o = some p → Slice cert582 cert915 p.1 p.2) cert932 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert582 cert915 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert923) (forall_cons (fun _ h => by cases h; exact cert924) (forall_cons (fun _ h => by cases h; exact cert925) (forall_cons (fun _ h => by cases h; exact cert926) (forall_cons (fun _ h => by cases h; exact cert927) (forall_cons (fun _ h => by cases h; exact cert928) (forall_cons (fun _ h => by cases h; exact cert929) (forall_cons (fun _ h => by cases h; exact cert930) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert921 : btAll (fun o => ∀ c, o = some c → ValidPool cert582 cert915 c) cert920 := buildPoolsBT_sound cert933
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert914 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert915 (6 - 1) xs.toFinset) cert466 := trivial
def cert905 : List NodeSpec := cert623 [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8]),([0,1,2,3,4,6],[0,1,2,3,5,6,7,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert936 : checkNodesBT cert938 cert915 cert130 cert920 cert901 cert466 6 cert905 = true := by decide +kernel
def cert917 : List NodeSpec := cert905
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert912 : checkNodesBT cert938 cert915 cert130 cert920 cert901 cert466 6 cert917 = true := cert936
def cert908 : BT (List (List Nat)) := buildBucketsBT cert938 cert917
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert909 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert915 6 xs.toFinset) cert908 := buildBucketsBT_sound (by decide) cert919 cert939 cert921 cert902 cert914 cert912
def cert906 : List NodeSpec := cert623 [([0,1,2,3,4],[0,1,2,3,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert937 : checkNodesBT cert938 cert915 cert130 cert920 cert901 cert908 7 cert906 = true := by decide +kernel
def cert918 : List NodeSpec := cert906
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert913 : checkNodesBT cert938 cert915 cert130 cert920 cert901 cert908 7 cert918 = true := cert937
def cert910 : BT (List (List Nat)) := buildBucketsBT cert938 cert918
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert911 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert915 7 xs.toFinset) cert910 := buildBucketsBT_sound (by decide) cert919 cert939 cert921 cert902 cert909 cert913
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert907 : Lower cert582 cert915 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,6,14),(VAR 4,6,22)]) (by decide +kernel) cert911 (by decide +kernel)
def cert998 : List Nat := [17,24,9,9,24,17]
def cert993 : List Nat := [16,16,1,8,8,1]
def cert985 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def cert1001 : BT Decor := buildWiresBT 2 cert985 cert227
def cert982 : List (List (Nat × Nat)) := [[]]
def cert983 : BT (List (Nat × Nat)) := btOfList 1 cert982
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert995 : goodPairs cert820 cert998 cert993 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert986 : ∀ x ∈ cert985, faithful cert998 cert993 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1002 : btAll (fun x => faithful cert998 cert993 x ∧ x.1 < 2^128) cert1001 := buildWiresBT_faithful cert986
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert984 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert820 = cert820) cert983 := btAll_ofList (autos_of (by decide +kernel))
def cert996 : BT (Option BoundPool) := buildPoolsBT 1 cert1001 cert821 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert999 : btAll (fun o => ∀ p, o = some p → Slice cert821 cert820 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert821 cert820 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert997 : btAll (fun o => ∀ c, o = some c → ValidPool cert821 cert820 c) cert996 := buildPoolsBT_sound cert999
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert992 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert820 (3 - 1) xs.toFinset) cert466 := trivial
def cert987 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1000 : checkNodesBT cert1001 cert820 cert506 cert996 cert983 cert466 3 cert987 = true := by decide +kernel
def cert994 : List NodeSpec := cert987
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert991 : checkNodesBT cert1001 cert820 cert506 cert996 cert983 cert466 3 cert994 = true := cert1000
def cert989 : BT (List (List Nat)) := buildBucketsBT cert1001 cert994
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert990 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert820 3 xs.toFinset) cert989 := buildBucketsBT_sound (by decide) cert995 cert1002 cert997 cert984 cert992 cert991
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert988 : Lower cert821 cert820 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) cert990 (by decide +kernel)
def cert981 : Nat := 0xcc888800cc888800cc888800cc888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert980 : Lower cert493 cert981 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,9,11)]) (by decide +kernel) cert988
def cert1015 : List Nat := [18,20,6,6,20,18]
def cert1011 : List Nat := [16,16,2,4,4,2]
def cert1004 : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def cert1018 : BT Decor := buildWiresBT 2 cert1004 cert227
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1012 : goodPairs cert11 cert1015 cert1011 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1005 : ∀ x ∈ cert1004, faithful cert1015 cert1011 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1019 : btAll (fun x => faithful cert1015 cert1011 x ∧ x.1 < 2^128) cert1018 := buildWiresBT_faithful cert1005
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1003 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert11 = cert11) cert983 := btAll_ofList (autos_of (by decide +kernel))
def cert1013 : BT (Option BoundPool) := buildPoolsBT 1 cert1018 cert29 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1016 : btAll (fun o => ∀ p, o = some p → Slice cert29 cert11 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert29 cert11 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1014 : btAll (fun o => ∀ c, o = some c → ValidPool cert29 cert11 c) cert1013 := buildPoolsBT_sound cert1016
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1010 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert11 (3 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1017 : checkNodesBT cert1018 cert11 cert506 cert1013 cert983 cert466 3 cert987 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1009 : checkNodesBT cert1018 cert11 cert506 cert1013 cert983 cert466 3 cert994 = true := cert1017
def cert1007 : BT (List (List Nat)) := buildBucketsBT cert1018 cert994
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1008 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert11 3 xs.toFinset) cert1007 := buildBucketsBT_sound (by decide) cert1012 cert1019 cert1014 cert1003 cert1010 cert1009
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1006 : Lower cert29 cert11 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) cert1008 (by decide +kernel)
def cert1021 : Nat := 0xfcfce8e8fcfce8e8fcfce8e8fcfce8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1020 : Lower cert490 cert1021 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) cert1006
def cert1023 : Nat := 0xffeeeeccffeeeeccffeeeeccffeeeecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1022 : Lower cert493 cert1023 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) cert988
def cert1025 : Nat := 0xfffafaf0fffafaf0fffafaf0fffafaf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1024 : Lower cert520 cert1025 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) cert988
def cert1027 : Nat := 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1026 : Lower cert23 cert1027 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) cert1006
def cert976 : Nat := 0xe8e8c0c0e8e8c0c0e8e8c0c0e8e8c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert975 : Lower cert490 cert976 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) cert1006
def cert978 : Nat := 0xf0a0a000f0a0a000f0a0a000f0a0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert977 : Lower cert520 cert978 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,9,13)]) (by decide +kernel) cert988
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert979 : Lower cert23 cert294 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,18,26)]) (by decide +kernel) cert1006
def cert952 : Nat := 0xfce8e8c0fce8e8c0fce8e8c0fce8e8c0
def cert959 : List Nat := [6,13,7,11,6,7,19,26,11,26,19,11,13,13,21,19,21]
def cert954 : List Nat := [4,12,5,10,2,3,18,18,3,10,3,9,9,5,5,17,17]
def cert953 : Nat := fullMask 17
def cert944 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1fd6e,0x1fd24),(0xcccccccccccccccccccccccccccccccc,0x8ffd,2040),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x17037,0x6007),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3b8a,6666),(0xffff0000ffff0000ffff0000ffff0000,0x1c6c0,0x180c0)]
def cert973 : BT Decor := buildWiresBT 3 cert944 cert227
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert956 : goodPairs cert952 cert959 cert954 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert945 : ∀ x ∈ cert944, faithful cert959 cert954 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert974 : btAll (fun x => faithful cert959 cert954 x ∧ x.1 < 2^128) cert973 := buildWiresBT_faithful cert945
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert943 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert952 = cert952) cert983 := btAll_ofList (autos_of (by decide +kernel))
def cert968 : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
def cert969 : BT (Option (Nat × Nat)) := btOfList 3 cert968
def cert971 : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[])]
def cert957 : BT (Option BoundPool) := buildPoolsBT 3 cert973 cert582 cert969 cert971
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert967 : Slice cert582 cert952 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert975
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert966 : Slice cert582 cert952 (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert980
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert965 : Slice cert582 cert952 (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert977
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert964 : Slice cert582 cert952 (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert979
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert963 : Slice cert582 cert952 (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1020
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert962 : Slice cert582 cert952 (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1022
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert961 : Slice cert582 cert952 (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1024
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert960 : Slice cert582 cert952 (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1026
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert970 : btAll (fun o => ∀ p, o = some p → Slice cert582 cert952 p.1 p.2) cert969 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert582 cert952 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert960) (forall_cons (fun _ h => by cases h; exact cert961) (forall_cons (fun _ h => by cases h; exact cert962) (forall_cons (fun _ h => by cases h; exact cert963) (forall_cons (fun _ h => by cases h; exact cert964) (forall_cons (fun _ h => by cases h; exact cert965) (forall_cons (fun _ h => by cases h; exact cert966) (forall_cons (fun _ h => by cases h; exact cert967) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert958 : btAll (fun o => ∀ c, o = some c → ValidPool cert582 cert952 c) cert957 := buildPoolsBT_sound cert970
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert951 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert952 (7 - 1) xs.toFinset) cert466 := trivial
def cert946 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert972 : checkNodesBT cert973 cert952 cert953 cert957 cert983 cert466 7 cert946 = true := by decide +kernel
def cert955 : List NodeSpec := cert946
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert950 : checkNodesBT cert973 cert952 cert953 cert957 cert983 cert466 7 cert955 = true := cert972
def cert948 : BT (List (List Nat)) := buildBucketsBT cert973 cert955
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert949 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert952 7 xs.toFinset) cert948 := buildBucketsBT_sound (by decide) cert956 cert974 cert958 cert943 cert951 cert950
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert947 : Lower cert582 cert952 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) cert949 (by decide +kernel)
def cert1103 : List Nat := [12,12,20,20,24,24,12,20,24]
def cert1097 : List Nat := [8,4,16,4,16,8,16,8,4]
def cert1049 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def cert1041 : BT Decor := buildWiresBT 2 cert1049 cert227
def cert1105 : BT (Option PoolSpec) := btOfList 1 []
lemma cert1075 : goodPairs cert505 cert1103 cert1097 := goodPairs_of (by decide +kernel)
lemma cert1050 : ∀ x ∈ cert1049, faithful cert1103 cert1097 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma cert1042 : btAll (fun x => faithful cert1103 cert1097 x ∧ x.1 < 2^128) cert1041 := buildWiresBT_faithful cert1050
set_option maxRecDepth 500000 in
lemma cert1046 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert505 = cert505) cert635 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma cert1126 : btAll (fun o => ∀ p, o = some p → Slice cert513 cert505 p.1 p.2) cert480 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert513 cert505 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert1053 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert505 2 xs.toFinset) cert466 := trivial
def cert1035 : BT (Option BoundPool) := buildPoolsSubBT 1 cert1041 cert513 cert480 cert1105 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1065 : checkNodesBT cert1041 cert505 cert128 cert1035 cert635 cert466 3 cert179 = true := by decide +kernel
def cert1054 : BT (List (List Nat)) := buildBucketsBT cert1041 cert179
set_option maxRecDepth 500000 in
lemma cert1055 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert505 3 xs.toFinset) cert1054 :=
  buildBucketsBT_sound (by decide) cert1075 cert1042 (buildPoolsSubBT_sound cert1126) cert1046 cert1053 cert1065
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert1072 : forestRootCheck cert513 cert505 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert1071 : bucketContainsBT cert1054 cert513 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert1077 : Lower cert513 cert505 4 := lower_of_forestBT cert1072 cert1055 cert1071
lemma cert1084 : carryOK [(1,3),(0,2)] cert888 cert887 cert513 cert505 = true := by decide +kernel
lemma cert1078 : Lower cert888 cert887 4 := carry_of cert1084 cert1077
def cert1031 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def cert1040 : List Nat := varsOf 13
lemma cert1086 : carryOK [(1,4),(1,3),(0,1),(0,2)] cert1040 cert1031 cert513 cert505 = true := by decide +kernel
lemma cert1085 : Lower cert1040 cert1031 4 := carry_of cert1086 cert1077
lemma cert1088 : carryOK [(1,2)] cert826 cert825 cert513 cert505 = true := by decide +kernel
lemma cert1087 : Lower cert826 cert825 4 := carry_of cert1088 cert1077
def cert1032 : Nat := 0xfaa0f000faa0f000faa0f000faa0f000
lemma cert1090 : liftCheck 0 1 cert520 cert1032 cert513 cert505 [(VAR 0,21,20)] = true := by decide +kernel
lemma cert1089 : Lower cert520 cert1032 5 := lift_of cert1090 cert1077
lemma cert1092 : liftCheck 2 0 cert23 cert863 cert513 cert505 [(VAR 1,10,8)] = true := by decide +kernel
lemma cert1091 : Lower cert23 cert863 5 := lift_of cert1092 cert1077
def cert1033 : Nat := 0xfffffffffff0f000fffffffffff0f000
lemma cert1094 : liftCheck 32 0 cert25 cert1033 cert513 cert505 [(VAR 5,32,0)] = true := by decide +kernel
lemma cert1093 : Lower cert25 cert1033 5 := lift_of cert1094 cert1077
def cert1034 : Nat := 0xeecc8800eecc8800eecc8800eecc8800
lemma cert1096 : carryOK [(3,4),(1,2)] cert493 cert1034 cert520 cert1032 = true := by decide +kernel
lemma cert1095 : Lower cert493 cert1034 5 := carry_of cert1096 cert1089
def cert1028 : Nat := 0xfeecfeecfeecfeecfeecfeecfeecfeec
lemma cert1080 : carryOK [(0,4),(0,3),(1,5),(0,2)] cert478 cert1028 cert25 cert1033 = true := by decide +kernel
lemma cert1079 : Lower cert478 cert1028 5 := carry_of cert1080 cert1093
def cert1029 : Nat := 0xfefef8f8fefef8f8fefef8f8fefef8f8
lemma cert1082 : carryOK [(0,1),(0,5),(1,3),(0,2)] cert490 cert1029 cert25 cert1033 = true := by decide +kernel
lemma cert1081 : Lower cert490 cert1029 5 := carry_of cert1082 cert1093
def cert1030 : Nat := 0xfeecf800feecf800feecf800feecf800
def cert1104 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,25,25,25,26,26,28,28,11,11,11,11,12,12,12,12,12,12,18,18,18,18,18,18,21,21,21,21,25,25,25]
def cert1098 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,24,17,9,24,10,24,20,7,17,20,24,7,9,10,17,20,24,7,9,10,17,20,24,7,9,10,24,7,10,20]
def cert1070 : Nat := fullMask 50
def cert1051 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f8007879f267,0x99659869b266),(0xcccccccccccccccccccccccccccccccc,0x7e0798e3f87,0x1a8a2890c2b85),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x781f860fc3f8,0x28a28ac0f4350),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3801ffff003ff,0x174d343d000ab),(0xffff0000ffff0000ffff0000ffff0000,0x3ffe007fffc00,0x2471c76b2d400)]
def cert1129 : List (Nat × Nat × Nat) := [(3,1,3),(1,1,2),(0,3,4),(0,0,3),(2,0,7),(0,0,4),(3,8,4),(0,8,4),(1,12,1)]
def cert1043 : BT Decor := buildWiresBT 4 cert1051 cert1129
def cert1045 : List (List (Nat × Nat)) := [[],[(3,4),(1,2)]]
def cert1047 : BT (List (Nat × Nat)) := btOfList 1 cert1045
def cert1125 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 8,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 2 1,4),some (subcubeFast 4 8,4),some (subcubeFast 2 16,4),some (subcubeFast 4 1,4),some (subcubeFast 0 1,5)]
def cert1127 : BT (Option (Nat × Nat)) := btOfList 4 cert1125
def cert1106 : BT (Option PoolSpec) := btOfList 4 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[]),some (6,[]),some (7,[]),some (8,[])]
lemma cert1076 : goodPairs cert1030 cert1104 cert1098 := goodPairs_of (by decide +kernel)
lemma cert1052 : ∀ x ∈ cert1051, faithful cert1104 cert1098 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma cert1044 : btAll (fun x => faithful cert1104 cert1098 x ∧ x.1 < 2^128) cert1043 := buildWiresBT_faithful cert1052
set_option maxRecDepth 500000 in
lemma cert1048 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert1030 = cert1030) cert1047 := btAll_ofList (autos_of (by decide +kernel))
lemma cert1108 : sliceDirectCheck 0 16 0 cert582 cert1030 cert478 cert1028 = true := by decide +kernel
lemma cert1107 : Slice cert582 cert1030 (subcubeFast 0 16) 5 := slice_fast_direct cert1108 cert1079
lemma cert1110 : sliceDirectCheck 0 8 0 cert582 cert1030 cert490 cert1029 = true := by decide +kernel
lemma cert1109 : Slice cert582 cert1030 (subcubeFast 0 8) 5 := slice_fast_direct cert1110 cert1081
lemma cert1112 : sliceDirectCheck 2 0 0 cert582 cert1030 cert520 cert1032 = true := by decide +kernel
lemma cert1111 : Slice cert582 cert1030 (subcubeFast 2 0) 5 := slice_fast_direct cert1112 cert1089
lemma cert1114 : sliceDirectCheck 4 0 0 cert582 cert1030 cert493 cert1034 = true := by decide +kernel
lemma cert1113 : Slice cert582 cert1030 (subcubeFast 4 0) 5 := slice_fast_direct cert1114 cert1095
lemma cert1116 : sliceDirectCheck 2 1 0 cert582 cert1030 cert513 cert505 = true := by decide +kernel
lemma cert1115 : Slice cert582 cert1030 (subcubeFast 2 1) 4 := slice_fast_direct cert1116 cert1077
lemma cert1118 : sliceDirectCheck 4 8 0 cert582 cert1030 cert888 cert887 = true := by decide +kernel
lemma cert1117 : Slice cert582 cert1030 (subcubeFast 4 8) 4 := slice_fast_direct cert1118 cert1078
lemma cert1120 : sliceDirectCheck 2 16 0 cert582 cert1030 cert1040 cert1031 = true := by decide +kernel
lemma cert1119 : Slice cert582 cert1030 (subcubeFast 2 16) 4 := slice_fast_direct cert1120 cert1085
lemma cert1122 : sliceDirectCheck 4 1 0 cert582 cert1030 cert826 cert825 = true := by decide +kernel
lemma cert1121 : Slice cert582 cert1030 (subcubeFast 4 1) 4 := slice_fast_direct cert1122 cert1087
lemma cert1124 : sliceDirectCheck 0 1 0 cert582 cert1030 cert23 cert863 = true := by decide +kernel
lemma cert1123 : Slice cert582 cert1030 (subcubeFast 0 1) 5 := slice_fast_direct cert1124 cert1091
set_option maxRecDepth 500000 in
lemma cert1128 : btAll (fun o => ∀ p, o = some p → Slice cert582 cert1030 p.1 p.2) cert1127 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert582 cert1030 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert1107) (forall_cons (fun _ h => by cases h; exact cert1109) (forall_cons (fun _ h => by cases h; exact cert1111) (forall_cons (fun _ h => by cases h; exact cert1113) (forall_cons (fun _ h => by cases h; exact cert1115) (forall_cons (fun _ h => by cases h; exact cert1117) (forall_cons (fun _ h => by cases h; exact cert1119) (forall_cons (fun _ h => by cases h; exact cert1121) (forall_cons (fun _ h => by cases h; exact cert1123) (fun _ h => (List.not_mem_nil h).elim))))))))))
lemma cert1056 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1030 3 xs.toFinset) cert466 := trivial
def cert1099 : List NodeSpec := [([0,13,2,3,4],[],[])]
def cert1036 : BT (Option BoundPool) := buildPoolsSubBT 4 cert1043 cert582 cert1127 cert1106 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1066 : checkNodesBT cert1043 cert1030 cert1070 cert1036 cert1047 cert466 4 cert1099 = true := by decide +kernel
def cert1057 : BT (List (List Nat)) := buildBucketsBT cert1043 cert1099
set_option maxRecDepth 500000 in
lemma cert1058 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1030 4 xs.toFinset) cert1057 :=
  buildBucketsBT_sound (by decide) cert1076 cert1044 (buildPoolsSubBT_sound cert1128) cert1048 cert1056 cert1066
def cert1100 : List NodeSpec := [([9,0,1,2,3,4],[],[]),([8,10,1,2,3,4],[0,1],[]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[2,3],[0,1])]
def cert1037 : BT (Option BoundPool) := buildPoolsSubBT 4 cert1043 cert582 cert1127 cert1106 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1067 : checkNodesBT cert1043 cert1030 cert1070 cert1037 cert1047 cert1057 5 cert1100 = true := by decide +kernel
def cert1059 : BT (List (List Nat)) := buildBucketsBT cert1043 cert1100
set_option maxRecDepth 500000 in
lemma cert1060 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1030 5 xs.toFinset) cert1059 :=
  buildBucketsBT_sound (by decide) cert1076 cert1044 (buildPoolsSubBT_sound cert1128) cert1048 cert1058 cert1067
def cert1101 : List NodeSpec := [([5,0,1,2,3,4],[6,5,4],[]),([0,1,2,6,3,4],[7,6,5],[]),([0,1,2,7,3,4],[6,5,8],[0]),([8,0,1,2,3,4],[7,4,1,0],[0])]
def cert1038 : BT (Option BoundPool) := buildPoolsSubBT 4 cert1043 cert582 cert1127 cert1106 [0,1,4,5,6,7,8]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1068 : checkNodesBT cert1043 cert1030 cert1070 cert1038 cert1047 cert1059 6 cert1101 = true := by decide +kernel
def cert1061 : BT (List (List Nat)) := buildBucketsBT cert1043 cert1101
set_option maxRecDepth 500000 in
lemma cert1062 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1030 6 xs.toFinset) cert1061 :=
  buildBucketsBT_sound (by decide) cert1076 cert1044 (buildPoolsSubBT_sound cert1128) cert1048 cert1060 cert1068
def cert1102 : List NodeSpec := [([0,1,2,3,4],[4,5,6,7],[0,1])]
def cert1039 : BT (Option BoundPool) := buildPoolsSubBT 4 cert1043 cert582 cert1127 cert1106 [4,5,6,7]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1069 : checkNodesBT cert1043 cert1030 cert1070 cert1039 cert1047 cert1061 7 cert1102 = true := by decide +kernel
def cert1063 : BT (List (List Nat)) := buildBucketsBT cert1043 cert1102
set_option maxRecDepth 500000 in
lemma cert1064 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1030 7 xs.toFinset) cert1063 :=
  buildBucketsBT_sound (by decide) cert1076 cert1044 (buildPoolsSubBT_sound cert1128) cert1048 cert1062 cert1069
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert1074 : forestRootCheck cert582 cert1030 [(VAR 0,11,10),(VAR 1,11,9),(VAR 2,12,8),(VAR 3,11,3),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert1073 : bucketContainsBT cert1063 cert582 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert1083 : Lower cert582 cert1030 8 := lower_of_forestBT cert1074 cert1064 cert1073
def cert1149 : List Nat := varsOf 21
def cert1143 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def cert1148 : List Nat := [17,20,5,5,20,17]
def cert1144 : List Nat := [16,16,1,4,4,1]
def cert1136 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def cert1152 : BT Decor := buildWiresBT 2 cert1136 cert227
def cert1133 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def cert1134 : BT (List (Nat × Nat)) := btOfList 3 cert1133
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1145 : goodPairs cert1143 cert1148 cert1144 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1137 : ∀ x ∈ cert1136, faithful cert1148 cert1144 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1153 : btAll (fun x => faithful cert1148 cert1144 x ∧ x.1 < 2^128) cert1152 := buildWiresBT_faithful cert1137
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1135 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert1143 = cert1143) cert1134 := btAll_ofList (autos_of (by decide +kernel))
def cert1146 : BT (Option BoundPool) := buildPoolsBT 1 cert1152 cert1149 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1150 : btAll (fun o => ∀ p, o = some p → Slice cert1149 cert1143 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert1149 cert1143 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1147 : btAll (fun o => ∀ c, o = some c → ValidPool cert1149 cert1143 c) cert1146 := buildPoolsBT_sound cert1150
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1142 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1143 (3 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1151 : checkNodesBT cert1152 cert1143 cert506 cert1146 cert1134 cert466 3 cert499 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1141 : checkNodesBT cert1152 cert1143 cert506 cert1146 cert1134 cert466 3 cert508 = true := cert1151
def cert1139 : BT (List (List Nat)) := buildBucketsBT cert1152 cert508
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1140 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1143 3 xs.toFinset) cert1139 := buildBucketsBT_sound (by decide) cert1145 cert1153 cert1147 cert1135 cert1142 cert1141
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1138 : Lower cert1149 cert1143 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) cert1140 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1130 : Lower cert1040 cert1031 4 := carry_of (swaps := [(3,4)]) (roots2 := cert1149) (T2 := cert1143) (by decide +kernel) cert1138
def cert1132 : Nat := 0xfae8fae8fae8fae8fae8fae8fae8fae8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1131 : Lower cert478 cert1132 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,1,3)]) (by decide +kernel) cert1130
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1154 : Lower cert888 cert887 4 := carry_of (swaps := [(1,2)]) (roots2 := cert1149) (T2 := cert1143) (by decide +kernel) cert1138
def cert1156 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1155 : Lower cert493 cert1156 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) cert1154
def cert1158 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1157 : Lower cert520 cert1158 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := cert493) (T2 := cert1156) (by decide +kernel) cert1155
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1185 : Lower cert490 cert898 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := cert478) (T2 := cert1132) (by decide +kernel) cert1131
def cert1168 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def cert1174 : List Nat := [5,6,3,3,6,5,12,9,9,18,17,17,26,12,28,26,28]
def cert1169 : List Nat := [4,4,1,2,2,1,4,1,8,2,1,16,24,8,24,10,20]
def cert1160 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3501,1188),(0xcccccccccccccccccccccccccccccccc,0x921e,0x8218),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16073,0x10043),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f1c0,0xf100),(0xffff0000ffff0000ffff0000ffff0000,0x1de00,0x15800)]
def cert1183 : BT Decor := buildWiresBT 3 cert1160 cert227
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1171 : goodPairs cert1168 cert1174 cert1169 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1161 : ∀ x ∈ cert1160, faithful cert1174 cert1169 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1184 : btAll (fun x => faithful cert1174 cert1169 x ∧ x.1 < 2^128) cert1183 := buildWiresBT_faithful cert1161
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1159 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert1168 = cert1168) cert1047 := btAll_ofList (autos_of (by decide +kernel))
def cert1179 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def cert1180 : BT (Option (Nat × Nat)) := btOfList 2 cert1179
def cert1172 : BT (Option BoundPool) := buildPoolsBT 2 cert1183 cert582 cert1180 cert693
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1178 : Slice cert582 cert1168 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1131
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1177 : Slice cert582 cert1168 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1185
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1176 : Slice cert582 cert1168 (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1155
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1175 : Slice cert582 cert1168 (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) cert1157
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1181 : btAll (fun o => ∀ p, o = some p → Slice cert582 cert1168 p.1 p.2) cert1180 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert582 cert1168 p.1 p.2) (forall_cons (fun _ h => by cases h; exact cert1175) (forall_cons (fun _ h => by cases h; exact cert1176) (forall_cons (fun _ h => by cases h; exact cert1177) (forall_cons (fun _ h => by cases h; exact cert1178) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1173 : btAll (fun o => ∀ c, o = some c → ValidPool cert582 cert1168 c) cert1172 := buildPoolsBT_sound cert1181
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1167 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1168 (6 - 1) xs.toFinset) cert466 := trivial
def cert1162 : List NodeSpec := cert623 [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1182 : checkNodesBT cert1183 cert1168 cert953 cert1172 cert1047 cert466 6 cert1162 = true := by decide +kernel
def cert1170 : List NodeSpec := cert1162
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1166 : checkNodesBT cert1183 cert1168 cert953 cert1172 cert1047 cert466 6 cert1170 = true := cert1182
def cert1164 : BT (List (List Nat)) := buildBucketsBT cert1183 cert1170
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1165 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert1168 6 xs.toFinset) cert1164 := buildBucketsBT_sound (by decide) cert1171 cert1184 cert1173 cert1159 cert1167 cert1166
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1163 : Lower cert582 cert1168 7 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) cert1165 (by decide +kernel)
def cert1186 : Nat := 0xffffff00ff000000ffffff00ff000000
def cert1194 : List Nat := varsOf 56
def cert1258 : List Nat := [24,24,40,40,48,48,24,40,48]
def cert1256 : List Nat := [16,8,32,8,32,16,32,16,8]
def cert1205 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def cert1198 : Array Decor := buildWires cert1205 cert227
def cert1190 : Array (Option BoundPool) := buildPools cert1198 cert1194 cert221 cert195
lemma cert1244 : goodPairs cert1186 cert1258 cert1256 := goodPairs_of (by decide +kernel)
lemma cert1206 : ∀ x ∈ cert1205, faithful cert1258 cert1256 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert1199 : ∀ x ∈ cert1198.toList, faithful cert1258 cert1256 x ∧ x.1 < 2^128 := buildWires_faithful cert1206
lemma cert1202 : ∀ sw ∈ cert40.toList, swapsValid sw = true ∧ permWord sw cert1186 = cert1186 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma cert1269 : ∀ i (hi : i < cert221.size), Slice cert1194 cert1186 cert221[i].1 cert221[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert1194 cert1186 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert1191 : ∀ i (hi : i < cert1190.size), ∀ c, cert1190[i] = some c → ValidPool cert1194 cert1186 c := buildPools_sound cert1269
lemma cert1215 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert1186 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1229 : checkNodes cert1198 cert1186 cert128 cert1190 cert40 cert61 0 cert178 = true := by decide +kernel
def cert1209 : Array (List (List Nat)) := buildBuckets 1 cert1198 cert178
lemma cert1210 : ∀ i (hi : i < cert1209.size), ∀ xs ∈ cert1209[i], Impossible cert1186 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert1244 cert1199 cert1191 cert1202 cert1215 cert1229
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1230 : checkNodes cert1198 cert1186 cert128 cert1190 cert40 cert1209 1 cert178 = true := by decide +kernel
lemma cert1211 : ∀ i (hi : i < cert1209.size), ∀ xs ∈ cert1209[i], Impossible cert1186 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert1244 cert1199 cert1191 cert1202 cert1210 cert1230
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1231 : checkNodes cert1198 cert1186 cert128 cert1190 cert40 cert1209 2 cert178 = true := by decide +kernel
lemma cert1212 : ∀ i (hi : i < cert1209.size), ∀ xs ∈ cert1209[i], Impossible cert1186 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert1244 cert1199 cert1191 cert1202 cert1211 cert1231
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1232 : checkNodes cert1198 cert1186 cert128 cert1190 cert40 cert1209 3 cert179 = true := by decide +kernel
def cert1213 : Array (List (List Nat)) := buildBuckets 1 cert1198 cert179
lemma cert1214 : ∀ i (hi : i < cert1213.size), ∀ xs ∈ cert1213[i], Impossible cert1186 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert1244 cert1199 cert1191 cert1202 cert1212 cert1232
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1241 : forestRootCheck cert1194 cert1186 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1240 : bucketContains cert1213 cert1194 = true := by decide +kernel
lemma cert1246 : Lower cert1194 cert1186 4 := lower_of_forest cert1241 cert1214 cert1240
lemma cert1248 : carryOK [(2,5),(1,4),(0,3)] cert811 cert805 cert1194 cert1186 = true := by decide +kernel
lemma cert1247 : Lower cert811 cert805 4 := carry_of cert1248 cert1246
def cert1188 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def cert1196 : List Nat := varsOf 35
lemma cert1251 : carryOK [(1,2),(0,2),(1,4),(0,3)] cert1196 cert1188 cert1194 cert1186 = true := by decide +kernel
lemma cert1250 : Lower cert1196 cert1188 4 := carry_of cert1251 cert1246
def cert1189 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def cert1197 : List Nat := varsOf 37
lemma cert1253 : carryOK [(2,4),(0,1),(0,3)] cert1197 cert1189 cert1194 cert1186 = true := by decide +kernel
lemma cert1252 : Lower cert1197 cert1189 4 := carry_of cert1253 cert1246
lemma cert1255 : carryOK [(2,4),(1,3)] cert306 cert293 cert1194 cert1186 = true := by decide +kernel
lemma cert1254 : Lower cert306 cert293 4 := carry_of cert1255 cert1246
def cert1187 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def cert1195 : List Nat := varsOf 39
def cert1259 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def cert1257 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def cert1207 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def cert1200 : Array Decor := buildWires cert1207 cert706
def cert1203 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def cert1268 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def cert1270 : Array (Nat × Nat) := cert1268.toArray
def cert1192 : Array (Option BoundPool) := buildPools cert1200 cert1195 cert1270 cert693
lemma cert1245 : goodPairs cert1187 cert1259 cert1257 := goodPairs_of (by decide +kernel)
lemma cert1208 : ∀ x ∈ cert1207, faithful cert1259 cert1257 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma cert1201 : ∀ x ∈ cert1200.toList, faithful cert1259 cert1257 x ∧ x.1 < 2^128 := buildWires_faithful cert1208
lemma cert1204 : ∀ sw ∈ cert1203.toList, swapsValid sw = true ∧ permWord sw cert1187 = cert1187 := autos_of (by decide +kernel)
lemma cert1261 : sliceDirectCheck 2 0 0 cert1195 cert1187 cert1197 cert1189 = true := by decide +kernel
lemma cert1260 : Slice cert1195 cert1187 (subcube 2 0) 4 := slice_direct cert1261 cert1252
lemma cert1263 : sliceDirectCheck 1 0 0 cert1195 cert1187 cert306 cert293 = true := by decide +kernel
lemma cert1262 : Slice cert1195 cert1187 (subcube 1 0) 4 := slice_direct cert1263 cert1254
lemma cert1265 : sliceDirectCheck 32 0 0 cert1195 cert1187 cert811 cert805 = true := by decide +kernel
lemma cert1264 : Slice cert1195 cert1187 (subcube 32 0) 4 := slice_direct cert1265 cert1247
lemma cert1267 : sliceDirectCheck 4 0 0 cert1195 cert1187 cert1196 cert1188 = true := by decide +kernel
lemma cert1266 : Slice cert1195 cert1187 (subcube 4 0) 4 := slice_direct cert1267 cert1250
set_option maxRecDepth 200000 in
lemma cert1271 : ∀ i (hi : i < cert1270.size), Slice cert1195 cert1187 cert1270[i].1 cert1270[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice cert1195 cert1187 p.1 p.2) (forall_cons cert1260 (forall_cons cert1262 (forall_cons cert1264 (forall_cons cert1266 (fun _ h => (List.not_mem_nil h).elim)))))
lemma cert1193 : ∀ i (hi : i < cert1192.size), ∀ c, cert1192[i] = some c → ValidPool cert1195 cert1187 c := buildPools_sound cert1271
lemma cert1228 : ∀ i (hi : i < cert61.size), ∀ xs ∈ cert61[i], Impossible cert1187 (0 - 1) xs.toFinset := by intro i hi; simp [cert61] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1233 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert61 0 cert178 = true := by decide +kernel
def cert1216 : Array (List (List Nat)) := buildBuckets 1 cert1200 cert178
lemma cert1217 : ∀ i (hi : i < cert1216.size), ∀ xs ∈ cert1216[i], Impossible cert1187 0 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1228 cert1233
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1234 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1216 1 cert178 = true := by decide +kernel
lemma cert1218 : ∀ i (hi : i < cert1216.size), ∀ xs ∈ cert1216[i], Impossible cert1187 1 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1217 cert1234
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1235 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1216 2 cert178 = true := by decide +kernel
lemma cert1219 : ∀ i (hi : i < cert1216.size), ∀ xs ∈ cert1216[i], Impossible cert1187 2 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1218 cert1235
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1236 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1216 3 cert687 = true := by decide +kernel
def cert1220 : Array (List (List Nat)) := buildBuckets 1 cert1200 cert687
lemma cert1221 : ∀ i (hi : i < cert1220.size), ∀ xs ∈ cert1220[i], Impossible cert1187 3 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1219 cert1236
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1237 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1220 4 cert688 = true := by decide +kernel
def cert1222 : Array (List (List Nat)) := buildBuckets 2 cert1200 cert688
lemma cert1223 : ∀ i (hi : i < cert1222.size), ∀ xs ∈ cert1222[i], Impossible cert1187 4 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1221 cert1237
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1238 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1222 5 cert689 = true := by decide +kernel
def cert1224 : Array (List (List Nat)) := buildBuckets 1 cert1200 cert689
lemma cert1225 : ∀ i (hi : i < cert1224.size), ∀ xs ∈ cert1224[i], Impossible cert1187 5 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1223 cert1238
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1239 : checkNodes cert1200 cert1187 cert674 cert1192 cert1203 cert1224 6 cert690 = true := by decide +kernel
def cert1226 : Array (List (List Nat)) := buildBuckets 1 cert1200 cert690
lemma cert1227 : ∀ i (hi : i < cert1226.size), ∀ xs ∈ cert1226[i], Impossible cert1187 6 xs.toFinset :=
  buildBuckets_sound (by decide) cert1245 cert1201 cert1193 cert1204 cert1225 cert1239
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1243 : forestRootCheck cert1195 cert1187 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert1242 : bucketContains cert1226 cert1195 = true := by decide +kernel
lemma cert1249 : Lower cert1195 cert1187 7 := lower_of_forest cert1243 cert1227 cert1242
def cert1274 : List Nat := varsOf 61
def cert1273 : Nat := 0xfffafafafffaaa00fffafafafffaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert1272 : Lower cert1274 cert1273 6 := lift_of (z := 36) (o := 0) (essPairs := [(VAR 2,16,20),(VAR 5,1,33)]) (by decide +kernel) cert988
def cert248 : List Nat := [10,10,34,34,40,40,10,34,40]
def cert247 : List Nat := [8,2,32,2,32,8,32,8,2]
def cert235 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def cert232 : BT Decor := buildWiresBT 2 cert235 cert227
lemma cert243 : goodPairs cert12 cert248 cert247 := goodPairs_of (by decide +kernel)
lemma cert236 : ∀ x ∈ cert235, faithful cert248 cert247 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma cert233 : btAll (fun x => faithful cert248 cert247 x ∧ x.1 < 2^128) cert232 := buildWiresBT_faithful cert236
set_option maxRecDepth 500000 in
lemma cert234 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert12 = cert12) cert635 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma cert249 : btAll (fun o => ∀ p, o = some p → Slice cert30 cert12 p.1 p.2) cert480 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert30 cert12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert237 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert12 2 xs.toFinset) cert466 := trivial
def cert231 : BT (Option BoundPool) := buildPoolsSubBT 1 cert232 cert30 cert480 cert1105 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert240 : checkNodesBT cert232 cert12 cert128 cert231 cert635 cert466 3 cert179 = true := by decide +kernel
def cert238 : BT (List (List Nat)) := buildBucketsBT cert232 cert179
set_option maxRecDepth 500000 in
lemma cert239 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert12 3 xs.toFinset) cert238 :=
  buildBucketsBT_sound (by decide) cert243 cert233 (buildPoolsSubBT_sound cert249) cert234 cert237 cert240
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert242 : forestRootCheck cert30 cert12 [(VAR 1,10,8),(VAR 3,10,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert241 : bucketContainsBT cert238 cert30 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert244 : Lower cert30 cert12 4 := lower_of_forestBT cert242 cert239 cert241
def cert230 : Nat := 0xffccffcccccccc00ffccffcccccccc00
lemma cert246 : liftCheck 16 0 cert27 cert230 cert30 cert12 [(VAR 4,18,2)] = true := by decide +kernel
lemma cert245 : Lower cert27 cert230 5 := lift_of cert246 cert244
def cert251 : Nat := 0xeaea8080eaea8080eaea8080eaea8080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert250 : Lower cert490 cert251 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,5,7)]) (by decide +kernel) cert1138
def cert254 : BT Decor := buildWiresBT 2 cert47 cert227
set_option maxRecDepth 500000 in
lemma cert255 : btAll (fun x => faithful cert191 cert174 x ∧ x.1 < 2^128) cert254 := buildWiresBT_faithful cert48
set_option maxRecDepth 500000 in
lemma cert256 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert0 = cert0) cert635 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma cert266 : btAll (fun o => ∀ p, o = some p → Slice cert22 cert0 p.1 p.2) cert480 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert22 cert0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma cert257 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert0 2 xs.toFinset) cert466 := trivial
def cert253 : BT (Option BoundPool) := buildPoolsSubBT 1 cert254 cert22 cert480 cert1105 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma cert260 : checkNodesBT cert254 cert0 cert128 cert253 cert635 cert466 3 cert179 = true := by decide +kernel
def cert258 : BT (List (List Nat)) := buildBucketsBT cert254 cert179
set_option maxRecDepth 500000 in
lemma cert259 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert0 3 xs.toFinset) cert258 :=
  buildBucketsBT_sound (by decide) cert140 cert255 (buildPoolsSubBT_sound cert266) cert256 cert257 cert260
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert262 : forestRootCheck cert22 cert0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma cert261 : bucketContainsBT cert258 cert22 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma cert263 : Lower cert22 cert0 4 := lower_of_forestBT cert262 cert259 cert261
def cert252 : Nat := 0xfce8fce8fce8fce8fce8fce8fce8fce8
lemma cert265 : liftCheck 1 0 cert478 cert252 cert22 cert0 [(VAR 0,3,2)] = true := by decide +kernel
lemma cert264 : Lower cert478 cert252 5 := lift_of cert265 cert263
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert267 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert805 = cert805) cert983 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert272 : checkNodesBT cert814 cert805 cert506 cert808 cert983 cert466 3 cert987 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert271 : checkNodesBT cert814 cert805 cert506 cert808 cert983 cert466 3 cert994 = true := cert272
def cert269 : BT (List (List Nat)) := buildBucketsBT cert814 cert994
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert270 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert805 3 xs.toFinset) cert269 := buildBucketsBT_sound (by decide) cert807 cert815 cert809 cert267 cert804 cert271
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert268 : Lower cert811 cert805 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) cert270 (by decide +kernel)
def cert283 : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0
def cert288 : List Nat := [5,7,9,5,7,9,10,14]
def cert284 : List Nat := [4,6,8,1,3,1,2,6]
def cert276 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccc,210,210),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,155,131),(0xff00ff00ff00ff00ff00ff00ff00ff00,228,4)]
def cert291 : BT Decor := buildWiresBT 2 cert276 cert227
def cert273 : List (List (Nat × Nat)) := [[],[(1,2),(0,3)]]
def cert274 : BT (List (Nat × Nat)) := btOfList 1 cert273
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert285 : goodPairs cert283 cert288 cert284 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert277 : ∀ x ∈ cert276, faithful cert288 cert284 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert292 : btAll (fun x => faithful cert288 cert284 x ∧ x.1 < 2^128) cert291 := buildWiresBT_faithful cert277
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert275 : btAll (fun sw => swapsValid sw = true ∧ permWord sw cert283 = cert283) cert274 := btAll_ofList (autos_of (by decide +kernel))
def cert286 : BT (Option BoundPool) := buildPoolsBT 1 cert291 cert478 cert480 cert195
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert289 : btAll (fun o => ∀ p, o = some p → Slice cert478 cert283 p.1 p.2) cert480 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice cert478 cert283 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert287 : btAll (fun o => ∀ c, o = some c → ValidPool cert478 cert283 c) cert286 := buildPoolsBT_sound cert289
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert282 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert283 (3 - 1) xs.toFinset) cert466 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert290 : checkNodesBT cert291 cert283 cert848 cert286 cert274 cert466 3 cert841 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert281 : checkNodesBT cert291 cert283 cert848 cert286 cert274 cert466 3 cert850 = true := cert290
def cert279 : BT (List (List Nat)) := buildBucketsBT cert291 cert850
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert280 : btAll (fun bk => ∀ xs ∈ bk, Impossible cert283 3 xs.toFinset) cert279 := buildBucketsBT_sound (by decide) cert285 cert292 cert287 cert275 cert282 cert281
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma cert278 : Lower cert478 cert283 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) cert280 (by decide +kernel)

def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeeeee8fac8e888feeeeee8fac8e888
def h0Pos : List Nat := [3,3,3,3,3,3,3,7,7,7,11,11,11,11,11,13,13,13,13,13,13,13,14,14,14,14,14,14,14,19,19,19,22,22,22,22,22,22,23,25,25,25,25,25,25,25,25,27,28,28,28,28,28,28,28,29,29,30,30,35,35,35,35,37,37,37,37,37,38,38,38,38,41,41,41,41,41,42,42,42,42,42,45,46,49,49,49,49,49,49,50,50,50,50,53,53,54,57,57,58,58,60,60,60]
def h0Neg : List Nat := [0,1,2,9,10,17,18,1,5,6,1,2,9,10,26,1,5,8,9,12,21,44,2,6,8,10,12,26,44,1,17,18,2,4,6,18,20,21,21,1,8,9,17,21,24,26,56,26,4,12,20,21,24,26,52,9,21,6,26,1,2,33,34,1,5,33,36,52,6,34,36,52,1,9,33,40,44,10,26,34,40,44,44,44,1,17,21,33,48,52,18,26,34,48,21,52,52,33,56,26,56,44,52,56]
def h0Mask : Nat := fullMask 104
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6c3f41f0ff980ffc0e03fffff,0x240f00703a9880ee0601595aa),(0xcccccccccccccccccccccccccccccccc,0x193c0be0f07e00807fffc07fff,0x81c00e0305620a00d8ac06a54),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe1c00c00ff87ff007f1fff8380,0x61c24e10dd034f087614b90300),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfe000fff0007ffff801ffffc00,0xbc080f7a0004b2f3001f2e7018),(0xffff0000ffff0000ffff0000ffff0000,0xfffff0000007ffffffe0000000,0xddef604088057cfc78c8104060),(0xffffffff00000000ffffffff00000000,0xfffffffffff800000000000000,0xf7b38f9cee6040400010200000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(0,6,2),(1,7,3),(2,8,4),(1,7,4),(0,6,5),(1,11,2),(1,11,4),(1,11,10),(3,11,10),(1,3,4),(0,6,16),(1,6,2),(3,7,18),(0,18,3),(0,18,4),(1,11,3),(1,7,11),(3,7,22),(3,7,16),(2,6,5),(3,2,16),(3,3,5),(1,28,7),(1,28,2),(3,4,5),(1,31,7),(1,31,2),(3,0,18),(3,1,18),(3,11,18),(2,18,3),(2,18,4),(3,26,18),(0,18,5),(2,6,2),(2,41,3),(1,42,4),(2,6,4),(2,41,4),(2,6,3),(3,6,2),(2,46,4),(1,47,0),(1,47,1),(3,47,5),(1,41,4),(0,2,3),(0,2,4),(0,6,3),(1,6,3),(3,6,3),(0,6,4),(1,58,2),(1,58,3),(1,6,4),(3,58,61),(0,2,61),(0,3,61),(1,2,3),(3,58,65),(0,6,65),(1,67,4),(2,65,4),(3,2,5),(1,70,58),(1,70,4),(3,0,61),(3,1,61),(3,11,61),(3,2,61),(3,3,61),(0,61,5),(3,6,4),(2,12,4),(0,44,65),(3,70,6),(1,79,0),(1,79,1),(3,79,5),(2,61,5),(2,2,4),(0,3,4),(2,3,4),(3,6,5),(0,80,6),(1,2,4),(0,6,92),(1,65,4),(3,26,94),(0,6,94),(3,69,6),(3,3,92),(3,98,6),(1,11,53),(1,100,4),(2,100,4),(1,53,4),(2,2,3),(3,2,3),(1,0,54),(3,2,4),(3,3,4),(1,0,53),(1,1,53),(1,6,53),(2,111,4),(2,6,53),(0,4,5),(2,113,114),(1,26,53),(3,53,5),(3,117,6),(2,6,114),(1,53,114),(1,2,114),(1,3,114),(1,31,53),(3,6,65),(0,65,4),(2,6,125),(2,96,5),(1,104,6),(3,104,6),(1,104,4),(0,3,5),(2,6,131),(1,2,131),(1,131,4),(1,6,54),(2,6,54),(2,136,131),(1,54,3),(1,54,131),(1,28,54),(3,6,92),(0,3,92),(2,6,142),(1,87,6),(3,87,6),(1,87,3),(1,89,2),(1,87,131),(1,87,28),(1,107,6),(3,107,6),(1,107,3),(0,2,5),(1,0,153),(1,1,153),(1,6,153),(2,6,153),(1,153,3),(2,158,4),(1,153,4),(1,82,4),(1,70,6),(1,70,3),(0,6,163),(2,163,4),(0,6,72),(1,0,114),(1,1,114),(1,6,114),(3,31,6),(1,31,6),(0,6,33),(1,31,3),(1,0,2),(1,1,2),(2,175,4),(3,1,2),(3,177,174),(1,177,4),(2,174,3),(0,174,5),(2,35,3),(3,182,174),(1,181,3),(1,35,4),(2,35,4),(3,1,5),(1,1,3),(2,183,4),(2,188,4),(0,188,5),(3,174,188),(1,183,4),(0,183,5),(3,183,5),(1,174,4),(0,188,196),(2,174,4),(3,181,188),(1,188,4),(3,1,3),(3,201,174),(1,1,4),(0,174,203),(3,1,4),(3,205,174),(1,187,3),(3,1,92),(1,87,1),(3,87,174),(0,174,3),(1,1,211),(1,174,3),(3,1,213),(2,213,4),(1,180,1),(1,180,4),(0,174,4),(3,1,196),(1,198,1),(1,1,181),(1,0,88),(2,174,88),(0,174,16),(1,89,1),(0,225,174),(3,89,174),(3,108,174),(1,1,131),(2,174,131),(1,28,1),(3,28,174),(2,174,114),(3,0,2),(1,50,4),(2,50,4),(1,234,3),(3,1,237),(2,237,4),(1,234,4),(3,1,240),(3,234,175),(1,175,4),(3,234,243),(1,201,234),(3,234,203),(3,234,5),(1,205,234),(1,205,2),(1,187,234),(3,234,92),(1,234,88),(1,2,88),(3,234,16),(3,1,16),(1,89,234),(1,108,234),(1,108,2),(1,234,131),(1,28,234),(1,234,114),(1,31,234),(1,0,3),(0,175,263),(3,177,263),(3,1,263),(1,266,4),(2,266,4),(1,263,4),(0,263,203),(3,205,263),(3,205,269),(1,187,2),(0,2,263),(3,2,263),(1,275,1),(1,275,4),(3,54,263),(0,263,92),(3,87,263),(3,107,263),(3,153,263),(3,70,263),(0,263,4),(3,284,263),(3,1,269),(1,285,1),(0,263,5),(1,2,288),(2,263,114),(3,0,3),(1,291,1),(1,292,4),(2,292,4),(1,291,2),(3,1,295),(2,295,4),(1,291,4),(3,1,298),(1,177,291),(3,291,203),(3,291,5),(1,205,291),(1,291,54),(3,291,92),(1,87,291),(1,107,291),(1,291,153),(1,70,291),(1,291,114),(1,31,291),(1,0,4),(3,2,203),(3,3,312),(3,205,312),(1,53,312),(3,53,312),(0,312,5),(1,53,318),(0,65,312),(2,65,312),(1,104,312),(3,104,312),(1,105,312),(3,105,312),(3,0,92),(1,87,0),(3,2,312),(0,2,312),(1,107,1),(3,107,312),(2,2,312),(1,332,318),(1,328,1),(1,153,312),(3,153,312),(3,70,312),(3,0,16),(1,89,0),(0,3,312),(2,3,312),(1,314,1),(1,131,312),(3,131,312),(3,28,312),(1,31,0),(1,2,318),(1,3,318),(3,312,5),(3,0,4),(1,350,2),(3,1,351),(1,350,3),(3,1,353),(1,350,53),(3,350,65),(1,104,350),(1,105,350),(3,350,92),(1,350,153),(1,70,350),(1,350,131),(1,28,350),(3,0,5),(1,364,1),(2,365,4),(1,364,2),(3,1,367),(2,367,4),(1,364,3),(3,1,370),(2,370,4),(1,364,4),(3,1,373),(1,105,1),(3,1,109),(2,109,4),(3,0,103),(1,1,103),(3,1,103),(3,0,65),(1,381,1),(1,381,4),(3,1,65),(1,1,65),(1,0,125),(1,1,125),(3,0,94),(3,1,94),(1,69,0),(1,69,1),(2,69,1),(0,65,5),(2,65,114),(1,104,0),(2,395,1),(2,395,4),(0,395,5),(1,104,1),(3,0,399),(1,399,4),(2,399,4),(3,0,130),(3,1,130),(1,104,114),(3,1,106),(1,1,54),(3,0,407),(3,0,138),(3,1,138),(1,326,1),(1,208,0),(1,0,142),(1,1,142),(1,98,0),(1,98,1),(3,131,92),(3,28,92),(0,92,5),(1,1,419),(2,327,1),(3,0,209),(3,0,146),(3,1,146),(1,107,0),(2,425,1),(3,0,330),(3,0,152),(3,1,152),(1,107,131),(1,28,107),(3,1,154),(2,154,4),(3,0,155),(1,155,4),(2,155,4),(3,0,158),(3,1,158),(3,0,160),(3,1,160),(1,70,0),(2,441,1),(2,441,4),(1,70,1),(3,0,444),(2,444,4),(3,0,163),(3,1,163),(3,0,72),(3,1,72),(3,1,167),(3,0,121),(3,1,121),(2,346,1),(1,31,1),(3,0,33),(3,1,33)]
def h0W : BT Decor := buildWiresBT 9 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(0,1),(2,3)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,9),some (subcubeFast 2 0,9),some (subcubeFast 0 32,9),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,9),some (0xaaaaaaaa55555555aaaaaaaa55555555,9),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,9),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,9),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 32 0,8),some (subcubeFast 0 4,7),some (subcubeFast 0 8,7),some (0xf00ff00f00000000f00ff00f00000000,7),some (0xf0f00f0f00000000f0f00f0f00000000,7),some (0xff0000ff00000000ff0000ff00000000,7),some (0xf0f000000000f0f0f0f000000000f0f0,7),some (0xff0000000000ff00ff0000000000ff00,7),some (subcubeFast 0 16,6),some (subcubeFast 1 32,6),some (subcubeFast 2 32,6),some (0xa5a50000a5a50000a5a50000a5a5,6),some (0xaa550000aa550000aa550000aa55,6),some (0xaa55aa5500000000aa55aa55,6),some (0xc3c3c3c300000000c3c3c3c3,6),some (0xc0c0c0c030303030c0c0c0c03030303,6),some (subcubeFast 4 1,5),some (subcubeFast 8 4,5),some (subcubeFast 16 1,5),some (subcubeFast 4 16,5),some (subcubeFast 20 0,5),some (0xf0f000000f0f0000f0f000000f0f0000,5),some (0xff00000000ff0000ff00000000ff0000,5),some (subcubeFast 6 1,4),some (subcubeFast 9 2,4),some (subcubeFast 1 16,4),some (subcubeFast 2 16,4),some (subcubeFast 17 2,4),some (subcubeFast 18 1,4),some (subcubeFast 12 16,4),some (subcubeFast 20 8,4),some (subcubeFast 24 4,4),some (subcubeFast 33 4,4),some (subcubeFast 34 8,4),some (subcubeFast 12 32,4),some (subcubeFast 20 32,4),some (subcubeFast 48 4,4),some (subcubeFast 24 32,4),some (subcubeFast 48 8,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput0Map : Lower (varsOf 62) 0xfffcfcf0fcccccc0fffcfcf0fcccccc0 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := cert28) (T2 := cert10) _ cert161
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput0Flip : Lower (varsOf 62) 0xfcccccc0f0c0c000fcccccc0f0c0c000 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput0Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfcccccc0f0c0c000fcccccc0f0c0c000) (by decide +kernel) sliceInput0Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput1Map : Lower (varsOf 61) 0xfffaffa0faaaaaa0fffaffa0faaaaaa0 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := cert28) (T2 := cert10) _ cert161
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput1Flip : Lower (varsOf 61) 0xfaaaaaa0fa00a000faaaaaa0fa00a000 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput1Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 2 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfaaaaaa0fa00a000faaaaaa0fa00a000) (by decide +kernel) sliceInput1Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Map : Lower (varsOf 31) 0xe8888880e8888880e8888880e8888880 9 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := cert28) (T2 := cert297) _ cert398
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Flip : Lower (varsOf 31) 0xfeeeeee8feeeeee8feeeeee8feeeeee8 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput2Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfeeeeee8feeeeee8feeeeee8feeeeee8) (by decide +kernel) sliceInput2Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput3Map : Lower (varsOf 55) 0xeeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8 9 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := cert582) (T2 := cert569) _ cert549
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G 0xaa55aa55aa55aa55aa55aa55aa55aa55 9 := mappedSlice (f := identifyRow 0 0 0 3) (R := varsOf 55) (G := 0xeeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput3Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput4Map : Lower (varsOf 31) 0xfaeaeaa8faeaeaa8faeaeaa8faeaeaa8 9 := by
  apply carry_of (swaps := [(1, 2)]) (roots2 := cert582) (T2 := cert569) _ cert549
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G 0xaaaaaaaa55555555aaaaaaaa55555555 9 := mappedSlice (f := identifyRow 0 0 0 5) (R := varsOf 31) (G := 0xfaeaeaa8faeaeaa8faeaeaa8faeaeaa8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput4Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput5Map : Lower (varsOf 59) 0xeeeeeecceecccc88eeeeeecceecccc88 9 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (0, 1)]) (roots2 := cert582) (T2 := cert569) _ cert549
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3 9 := mappedSlice (f := identifyRow 0 0 1 2) (R := varsOf 59) (G := 0xeeeeeecceecccc88eeeeeecceecccc88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput5Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput6Map : Lower (varsOf 47) 0xfee8fee8f8c8f8c8fee8fee8f8c8f8c8 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := cert761) (T2 := cert749) _ cert732
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G 0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f 9 := mappedSlice (f := identifyRow 0 0 2 4) (R := varsOf 47) (G := 0xfee8fee8f8c8f8c8fee8fee8f8c8f8c8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput6Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput7Map : Lower (varsOf 59) 0xeeeeeeaaee888888eeeeeeaaee888888 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := cert582) (T2 := cert915) _ cert907
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput7Flip : Lower (varsOf 59) 0xeeeeee88aa888888eeeeee88aa888888 8 := dualLower (by decide +kernel) (by decide +kernel) sliceInput7Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xeeeeee88aa888888eeeeee88aa888888) (by decide +kernel) sliceInput7Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput8Map : Lower (varsOf 55) 0xeeeeecece8e88888eeeeecece8e88888 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (0, 1)]) (roots2 := cert582) (T2 := cert915) _ cert907
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput8Flip : Lower (varsOf 55) 0xeeeee8e8c8c88888eeeee8e8c8c88888 8 := dualLower (by decide +kernel) (by decide +kernel) sliceInput8Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xeeeee8e8c8c88888eeeee8e8c8c88888) (by decide +kernel) sliceInput8Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput9Map : Lower (varsOf 47) 0xeee8eee8e888e888eee8eee8e888e888 8 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2)]) (roots2 := cert582) (T2 := cert952) _ cert947
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xeee8eee8e888e888eee8eee8e888e888) (by decide +kernel) sliceInput9Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput10Map : Lower (varsOf 31) 0xeee8eca0eee8eca0eee8eca0eee8eca0 8 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := cert582) (T2 := cert1030) _ cert1083
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput10Flip : Lower (varsOf 31) 0xfac8e888fac8e888fac8e888fac8e888 8 := dualLower (by decide +kernel) (by decide +kernel) sliceInput10Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfac8e888fac8e888fac8e888fac8e888) (by decide +kernel) sliceInput10Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput11Map : Lower (varsOf 59) 0xffeeeeeeffccee88ffeeeeeeffccee88 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (0, 1)]) (roots2 := cert582) (T2 := cert1168) _ cert1163
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 0 4) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeffccee88ffeeeeeeffccee88) (by decide +kernel) sliceInput11Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput12Map : Lower (varsOf 55) 0xfefeeeeefafae8e8fefeeeeefafae8e8 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := cert582) (T2 := cert1168) _ cert1163
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 0 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafae8e8fefeeeeefafae8e8) (by decide +kernel) sliceInput12Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput13Map : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8 7 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := cert1195) (T2 := cert1187) _ cert1249
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G 0xf00ff00f00000000f00ff00f00000000 7 := mappedSlice (f := identifyRow 0 32 2 3) (R := varsOf 23) (G := 0xfefee8e8fefee8e8fefee8e8fefee8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput13Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput14Map : Lower (varsOf 15) 0xfee8fee8fee8fee8fee8fee8fee8fee8 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := cert1195) (T2 := cert1187) _ cert1249
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G 0xf0f00f0f00000000f0f00f0f00000000 7 := mappedSlice (f := identifyRow 0 32 2 4) (R := varsOf 15) (G := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput14Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G 0xff0000ff00000000ff0000ff00000000 7 := mappedSlice (f := identifyRow 0 32 3 4) (R := varsOf 15) (G := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput14Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput15Map : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3)]) (roots2 := cert1195) (T2 := cert1187) _ cert1249
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G 0xf0f000000000f0f0f0f000000000f0f0 7 := mappedSlice (f := identifyRow 0 4 4 5) (R := varsOf 27) (G := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput15Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G 0xff0000000000ff00ff0000000000ff00 7 := mappedSlice (f := identifyRow 0 8 4 5) (R := varsOf 23) (G := 0xfefee8e8fefee8e8fefee8e8fefee8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput13Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput16Map : Lower (varsOf 47) 0xfeeefeeefac8fac8feeefeeefac8fac8 6 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := cert1274) (T2 := cert1273) _ cert1272
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefac8fac8feeefeeefac8fac8) (by decide +kernel) sliceInput16Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput17Map : Lower (varsOf 30) 0xfcccccc0fcccccc0fcccccc0fcccccc0 6 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 1 32) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcccccc0fcccccc0fcccccc0fcccccc0) (by decide +kernel) sliceInput17Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput18Map : Lower (varsOf 29) 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0 6 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 2 32) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0) (by decide +kernel) sliceInput18Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput19Map : Lower (varsOf 43) 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88 6 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G 0xa5a50000a5a50000a5a50000a5a5 6 := mappedSlice (f := identifyRow 16 0 0 2) (R := varsOf 43) (G := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput19Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput20Map : Lower (varsOf 39) 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8 6 := by
  apply carry_of (swaps := [(3, 4), (4, 5)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G 0xaa550000aa550000aa550000aa55 6 := mappedSlice (f := identifyRow 16 0 0 3) (R := varsOf 39) (G := 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput20Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput21Map : Lower (varsOf 23) 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8 6 := by
  apply carry_of (swaps := [(3, 4)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G 0xaa55aa5500000000aa55aa55 6 := mappedSlice (f := identifyRow 32 0 0 3) (R := varsOf 23) (G := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput21Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput22Map : Lower (varsOf 27) 0xeecccc88eecccc88eecccc88eecccc88 6 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (0, 1)]) (roots2 := cert478) (T2 := cert468) _ cert456
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G 0xc3c3c3c300000000c3c3c3c3 6 := mappedSlice (f := identifyRow 32 0 1 2) (R := varsOf 27) (G := 0xeecccc88eecccc88eecccc88eecccc88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput22Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G 0xc0c0c0c030303030c0c0c0c03030303 6 := mappedSlice (f := identifyRow 4 0 1 5) (R := varsOf 27) (G := 0xeecccc88eecccc88eecccc88eecccc88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput22Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput23Map : Lower (varsOf 58) 0xffffffccffccccccffffffccffcccccc 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (1, 2)]) (roots2 := cert25) (T2 := cert1033) _ cert1093
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffffccffccccccffffffccffcccccc) (by decide +kernel) sliceInput23Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput24Map : Lower (varsOf 51) 0xeeeeeeeecccc8888eeeeeeeecccc8888 5 := by
  apply carry_of (swaps := [(2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := cert27) (T2 := cert230) _ cert245
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeeeeecccc8888eeeeeeeecccc8888) (by decide +kernel) sliceInput24Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput25Map : Lower (varsOf 46) 0xfffcfffcfcccfcccfffcfffcfcccfccc 5 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := cert25) (T2 := cert1033) _ cert1093
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfffcfffcfcccfcccfffcfffcfcccfccc) (by decide +kernel) sliceInput25Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput26Map : Lower (varsOf 43) 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := cert27) (T2 := cert230) _ cert245
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88) (by decide +kernel) sliceInput26Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput27Map : Lower (varsOf 43) 0xee88ee8888888888ee88ee8888888888 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (1, 2)]) (roots2 := cert490) (T2 := cert251) _ cert250
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xee88ee8888888888ee88ee8888888888) (by decide +kernel) sliceInput27Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput28Map : Lower (varsOf 15) 0xfae8fae8fae8fae8fae8fae8fae8fae8 5 := by
  apply carry_of (swaps := [(0, 1)]) (roots2 := cert478) (T2 := cert252) _ cert264
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G 0xf0f000000f0f0000f0f000000f0f0000 5 := mappedSlice (f := identifyRow 0 16 2 5) (R := varsOf 15) (G := 0xfae8fae8fae8fae8fae8fae8fae8fae8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput28Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput29Map : Lower (varsOf 15) 0xfec8fec8fec8fec8fec8fec8fec8fec8 5 := by
  apply carry_of (swaps := [(2, 3)]) (roots2 := cert478) (T2 := cert252) _ cert264
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G 0xff00000000ff0000ff00000000ff0000 5 := mappedSlice (f := identifyRow 0 16 3 5) (R := varsOf 15) (G := 0xfec8fec8fec8fec8fec8fec8fec8fec8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput29Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput30Map : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 6 1) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 56) (qGoal := 0xffffff00ff000000ffffff00ff000000) (by decide +kernel) sliceInput30Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput31Map : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 9 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 52) (qGoal := 0xfffff0f0f0f00000fffff0f0f0f00000) (by decide +kernel) sliceInput31Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput32Map : Lower (varsOf 46) 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := cert478) (T2 := cert283) _ cert278
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0) (by decide +kernel) sliceInput32Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput33Map : Lower (varsOf 45) 0xfaaafaaafa00fa00faaafaaafa00fa00 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (2, 3), (1, 2)]) (roots2 := cert478) (T2 := cert283) _ cert278
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfaaafaaafa00fa00faaafaaafa00fa00) (by decide +kernel) sliceInput33Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput34Map : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 17 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 44) (qGoal := 0xfff0fff0f000f000fff0fff0f000f000) (by decide +kernel) sliceInput34Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 44) (qGoal := 0xfff0fff0f000f000fff0fff0f000f000) (by decide +kernel) sliceInput34Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput35Map : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) sliceInput35Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 20 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) sliceInput35Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 24 4) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) sliceInput35Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput36Map : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 33 4) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 26) (qGoal := 0xffcccc00ffcccc00ffcccc00ffcccc00) (by decide +kernel) sliceInput36Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput37Map : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 34 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) sliceInput37Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput38Map : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 12 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) sliceInput38Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput39Map : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88 4 := by
  apply carry_of (swaps := [(2, 3)]) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 20 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 11) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) sliceInput39Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 48 4) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 11) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) sliceInput39Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput40Map : Lower (varsOf 7) 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8 4 := by
  apply carry_of (swaps := []) (roots2 := cert811) (T2 := cert805) _ cert268
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 24 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput40Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 48 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput40Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))
def h0Empty : BT (List (List Nat)) := BT.empty
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def pool0 : PoolSpec := (33,[])
def pool1 : PoolSpec := (34,[])
def pool2 : PoolSpec := (42,[])
def pool3 : PoolSpec := (39,[])
def pool4 : PoolSpec := (37,[])
def pool5 : PoolSpec := (43,[])
def pool6 : PoolSpec := (40,[])
def pool7 : PoolSpec := (41,[])
def pool8 : PoolSpec := (46,[])
def pool9 : PoolSpec := (44,[])
def pool10 : PoolSpec := (45,[])
def pool11 : PoolSpec := (38,[])
def pool12 : PoolSpec := (28,[])
def pool13 : PoolSpec := (48,[])
def pool14 : PoolSpec := (26,[])
def pool15 : PoolSpec := (10,[(1,0,1)])
def pool16 : PoolSpec := (10,[(1,0,4)])
def pool17 : PoolSpec := (2,[(1,0,1)])
def pool18 : PoolSpec := (0,[(1,2,4)])
def pool19 : PoolSpec := (14,[(1,0,1)])
def pool20 : PoolSpec := (2,[(1,0,4)])
def pool21 : PoolSpec := (2,[(1,0,1),(2,6,4)])
def pool22 : PoolSpec := (2,[(1,0,1),(1,6,4)])
def pool23 : PoolSpec := (2,[(1,0,4),(3,1,312)])
def pool24 : PoolSpec := (2,[(1,0,2),(1,1,3),(0,174,188)])
def pool25 : PoolSpec := (10,[(1,0,4),(3,1,312)])
def h0Block6_0Specs : List PoolSpec := [pool14,pool2,(13,[]),(10,[])]
def h0Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 h0W h0R h0Slices h0Block6_0Specs
def h0Block6_0 : List NodeSpec := [([127,0,1,96,2,3,4],[3],[]),([26,44,69,0,1,2,3],[0],[]),([26,0,1,99,2,3,4],[],[]),([26,0,1,97,2,3,4],[],[]),([26,0,1,96,2,3,4],[1],[]),([26,0,1,2,3,4,43],[],[]),([115,0,1,2,3,4,5],[2],[]),([81,0,1,11,2,3,4],[],[]),([91,0,1,11,2,3,4],[],[]),([44,80,0,1,11,2,3],[0],[]),([44,69,0,1,11,2,3],[0],[]),([189,0,1,183,3,92,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_0Ok : checkNodesBT h0W h0G h0Mask h0Block6_0Pools h0Autos h0Empty 6 h0Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_0Mem : ∀ ns ∈ h0Block6_0, Impossible h0G 6 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0EmptyOk h0Block6_0Ok
def h0Block6_1Specs : List PoolSpec := [pool1,pool5,pool14,(24,[]),pool10,(23,[])]
def h0Block6_1Pools : BT (Option BoundPool) := buildPoolsBT 3 h0W h0R h0Slices h0Block6_1Specs
def h0Block6_1 : List NodeSpec := [([102,0,1,2,100,3,4],[],[]),([137,0,1,2,3,4,5],[],[]),([132,1,2,106,3,4,5],[],[]),([15,0,1,11,2,3,4],[],[]),([24,0,1,11,2,3,4],[],[]),([25,0,1,11,2,3,4],[],[]),([0,1,7,12,3,22,4],[1,2],[]),([0,1,58,2,3,68,5],[2],[]),([0,1,17,2,3,10,5],[0],[]),([0,1,11,2,3,4,68],[3,4,5],[]),([0,1,11,2,3,4,14],[0,1],[]),([0,1,11,2,3,10,13],[3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_1Ok : checkNodesBT h0W h0G h0Mask h0Block6_1Pools h0Autos h0Empty 6 h0Block6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_1Mem : ∀ ns ∈ h0Block6_1, Impossible h0G 6 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0EmptyOk h0Block6_1Ok
def h0Block6_2Specs : List PoolSpec := [pool1,pool14,(24,[]),pool2,pool8,(23,[])]
def h0Block6_2Pools : BT (Option BoundPool) := buildPoolsBT 3 h0W h0R h0Slices h0Block6_2Specs
def h0Block6_2 : List NodeSpec := [([0,1,11,2,3,10,16],[0,1],[]),([0,1,11,12,3,4,10],[2],[]),([0,1,23,2,3,22,4],[1],[]),([0,1,6,2,3,4,95],[3],[]),([0,1,2,212,184,4,5],[5],[]),([0,1,2,100,3,4,101],[1,4],[]),([0,1,2,3,4,95],[],[]),([1,6,2,106,3,134,5],[3],[]),([1,6,106,3,133,4,5],[3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_2Ok : checkNodesBT h0W h0G h0Mask h0Block6_2Pools h0Autos h0Empty 6 h0Block6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_2Mem : ∀ ns ∈ h0Block6_2, Impossible h0G 6 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0EmptyOk h0Block6_2Ok
def h0Nodes6 : List NodeSpec := h0Block6_0 ++ h0Block6_1 ++ h0Block6_2
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_of_mem (forall_append (forall_append h0Block6_0Mem h0Block6_1Mem) h0Block6_2Mem)
def h0Block7_0Specs : List PoolSpec := [pool9,pool1,pool5,pool14,pool12,pool3,(14,[]),pool0,pool2,pool10,pool15,(13,[]),(19,[])]
def h0Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_0Specs
def h0Block7_0 : List NodeSpec := [([26,45,0,1,2,3,4],[2,7,8,10,11],[]),([26,44,0,1,2,3,65,4],[0,4,8],[0]),([26,38,0,1,2,3],[1,4,7],[]),([26,69,0,1,6,2,3,4],[0,3,8,9],[0]),([26,42,0,1,2,3,4],[6,7,8,10],[0]),([26,37,0,1,2,4],[1,4,7],[]),([26,98,0,1,6,2,3,4],[0,2,3],[0]),([26,41,0,1,2,3,4,16],[3,8],[]),([26,76,0,1,3,4],[1,4,7],[]),([26,0,1,6,2,3,4,94],[3,8,12],[0]),([26,0,1,2,3,4,94],[0,2,8],[0]),([86,76,0,1,3,4],[5,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_0Ok : checkNodesBT h0W h0G h0Mask h0Block7_0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_0Mem : ∀ ns ∈ h0Block7_0, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_0Ok
def h0Block7_1Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool14,pool12,(30,[]),(31,[]),pool4,pool3,pool6,pool0,pool2,(11,[]),(10,[(1,0,1),(2,6,4)]),pool21,(14,[(1,0,1),(2,6,4)]),(2,[(1,0,1),(0,2,3),(2,6,114)])]
def h0Block7_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block7_1Specs
def h0Block7_1 : List NodeSpec := [([45,46,0,1,2,3,4,5],[2,10],[]),([81,0,1,6,2,3,4,5],[1,10],[0]),([44,69,0,1,6,2,3,5],[4,6],[0]),([44,42,0,1,2,3,4,5],[0,5],[]),([44,0,1,82,2,3,4,5],[0,5],[]),([44,0,1,11,2,12,3,4],[4,5,12,15],[0]),([44,0,1,11,2,3,65,4],[5,12],[0]),([44,0,1,11,2,3,13],[2,3,4,8,12],[]),([44,0,1,6,2,3,72,5],[4,6,14,16],[]),([44,0,1,63,3,5],[9,11],[]),([44,0,1,2,12,3,4,5],[5,7],[]),([119,0,1,53,2,3,4,5],[1,3,5,8,13,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_1Ok : checkNodesBT h0W h0G h0Mask h0Block7_1Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_1Mem : ∀ ns ∈ h0Block7_1, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_1Ok
def h0Block7_2Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,(24,[]),(31,[]),pool4,pool3,pool0,pool10,(47,[]),(27,[]),pool8,pool7,(2,[(1,0,1),(1,11,2),(2,12,4)])]
def h0Block7_2Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_2Specs
def h0Block7_2 : List NodeSpec := [([87,132,0,1,2,3,4,5],[1,10,14],[]),([87,0,1,6,2,3,134,5],[1,2,3,13],[]),([87,0,1,6,30,3,4,5],[6,10,13],[]),([87,0,1,183,3,4,5],[7,12],[]),([189,0,1,2,183,3,4,5],[1,7],[0,1]),([112,0,1,2,3,5],[8,9],[]),([80,0,1,11,6,2,3,4],[5,13,15],[0]),([80,0,1,6,2,3,4,5],[1,13,15],[]),([38,0,1,11,2,3],[9,13],[]),([89,98,0,1,6,2,4,5],[0,1,11],[]),([89,0,1,6,2,146,4,5],[0,2],[]),([165,0,1,6,2,3,4,5],[1,4,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_2Ok : checkNodesBT h0W h0G h0Mask h0Block7_2Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_2Mem : ∀ ns ∈ h0Block7_2, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_2Ok
def h0Block7_3Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,pool14,(29,[]),(30,[]),pool4,pool3,pool0,pool10,(11,[]),pool8,(10,[])]
def h0Block7_3Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_3Specs
def h0Block7_3 : List NodeSpec := [([190,0,1,174,3,92,5],[6,8],[]),([9,0,1,6,2,3,4,5],[0,1,2],[]),([159,0,1,6,2,3,4,5],[0,1,2,5],[]),([69,0,1,58,6,2,3,5],[1,5,11,13],[]),([69,0,1,11,6,2,3,4],[2,5,13],[0]),([69,0,1,6,2,3,4,5],[1,2,13],[]),([31,113,0,1,2,3,4,5],[11,14],[]),([126,0,1,2,3,65,4,5],[6,12],[]),([132,0,1,54,2,3,4,5],[1,3,11,12],[0]),([143,0,1,2,3,4,92,5],[7,12],[]),([37,0,1,11,2,4],[4,10],[]),([77,76,0,1,4,5],[9,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_3Ok : checkNodesBT h0W h0G h0Mask h0Block7_3Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_3Mem : ∀ ns ∈ h0Block7_3, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_3Ok
def h0Block7_4Specs : List PoolSpec := [pool9,pool1,pool14,pool4,pool3,(14,[]),pool0,pool2,(47,[]),(11,[]),pool8,(13,[]),(8,[]),(10,[]),(32,[]),pool24,(2,[(1,0,2),(1,1,3),(3,181,188)])]
def h0Block7_4Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block7_4Specs
def h0Block7_4 : List NodeSpec := [([77,0,1,63,4,5],[4,6],[]),([28,136,0,1,2,3,4,5],[0,13],[]),([28,0,315,1,2,3,312,5],[8],[]),([28,1,6,2,106,3,4,5],[10],[]),([149,0,1,6,2,3,4,5],[5,10,14],[]),([199,0,1,2,174,3,4,5],[9,16],[]),([195,0,1,2,183,3,4,5],[13,15],[]),([136,0,1,2,131,3,4,5],[3,6,12],[0]),([113,0,1,2,3,114,4,5],[1,6,11,13],[0]),([76,0,1,11,3,4],[6,10],[]),([27,0,1,7,6,3,4,5],[0,2,7],[]),([36,0,1,2,3,4],[0,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_4Ok : checkNodesBT h0W h0G h0Mask h0Block7_4Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_4Mem : ∀ ns ∈ h0Block7_4, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_4Ok
def h0Block7_5Specs : List PoolSpec := [pool9,pool1,pool14,pool12,(29,[]),(24,[]),pool0,pool10,(47,[]),(27,[]),(11,[]),pool8,pool7,(12,[])]
def h0Block7_5Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_5Specs
def h0Block7_5 : List NodeSpec := [([66,0,1,6,2,3,4,5],[0,11],[]),([75,0,1,11,2,3,4],[1,3,6],[]),([75,0,1,2,3,4],[6,7],[]),([62,0,1,2,3,5],[1,3,6],[]),([19,0,1,3,4,5],[1,2,3],[]),([25,0,1,6,2,3,4,5],[4,8],[0]),([35,0,1,2,3,184,4,5],[1,6,9,13],[]),([35,0,11,2,3,4],[6,11],[]),([74,0,1,2,30,3,4,5],[5,10],[]),([74,0,1,2,3,163,4,5],[9,13],[]),([250,0,1,2,3,4,16,5],[12,13],[]),([0,244,1,3,4,5],[1,4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_5Ok : checkNodesBT h0W h0G h0Mask h0Block7_5Pools h0Autos h0Bucket6 7 h0Block7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_5Mem : ∀ ns ∈ h0Block7_5, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_5Ok
def h0Block7_6Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,(24,[]),(30,[]),pool3,pool6,pool0,pool2,(10,[]),(2,[]),(36,[])]
def h0Block7_6Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_6Specs
def h0Block7_6 : List NodeSpec := [([0,226,1,2,3,4,5],[2,12,13,14],[]),([0,1,272,2,3,5],[9,10],[]),([0,1,118,2,3,4],[1,10],[]),([0,1,7,17,2,3,4,5],[4,5,11],[0]),([0,1,7,11,2,3,22,4],[2,3,4,11],[0]),([0,1,7,11,2,3,4,13],[0,4,5,11],[0]),([0,1,7,11,2,3,4,16],[0,4,11],[0]),([0,1,7,11,12,3,4],[2,3,5,10,11],[0]),([0,1,7,6,33,3,4,5],[1,6,11],[]),([0,1,7,6,30,3,4,5],[1,6,11],[]),([0,1,7,20,4,5],[2,8],[]),([0,1,7,21,3,5],[2,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_6Ok : checkNodesBT h0W h0G h0Mask h0Block7_6Pools h0Autos h0Bucket6 7 h0Block7_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_6Mem : ∀ ns ∈ h0Block7_6, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_6Ok
def h0Block7_7Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool14,pool12,pool19,(31,[]),pool6,pool0,pool2,(2,[(1,0,1),(0,6,2),(1,11,2)]),pool10,pool8,(13,[(1,0,1)])]
def h0Block7_7Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_7Specs
def h0Block7_7 : List NodeSpec := [([0,1,7,12,3,4,5],[2,3,5,7,9,10,11],[]),([0,1,172,6,2,3,4,5],[6,10],[]),([0,1,32,6,2,3,4,5],[1,10],[]),([0,1,29,6,2,3,4,5],[1,10],[]),([0,1,99,6,2,3,4,5],[3],[0]),([0,1,164,6,2,3,4,5],[3,14],[]),([0,1,67,58,2,3,4,5],[0,5,10],[0]),([0,1,67,11,2,3,4],[4,5,10],[0]),([0,1,58,6,2,3,72,5],[0,4,12,13],[]),([0,1,58,63,3,5],[8,9],[]),([0,1,97,6,2,3,4,5],[0,13],[0]),([0,1,166,6,2,3,4,5],[6,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_7Ok : checkNodesBT h0W h0G h0Mask h0Block7_7Pools h0Autos h0Bucket6 7 h0Block7_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_7Mem : ∀ ns ∈ h0Block7_7, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_7Ok
def h0Block7_8Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,(29,[]),(24,[]),pool19,(30,[]),(31,[]),pool4,pool0,pool2,pool10,(27,[]),pool8,(10,[(1,0,1),(0,6,4)]),(9,[]),(19,[])]
def h0Block7_8Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block7_8Specs
def h0Block7_8 : List NodeSpec := [([0,1,93,11,2,3,4],[2,3,4,13],[]),([0,1,96,6,2,3,4,5],[3,13,19],[0]),([0,1,96,2,3,4,5],[1,3,13,18],[0]),([0,1,11,63,3,4],[5,7,12],[]),([0,1,11,2,20,4],[12,16],[]),([0,1,11,2,100,3,4],[2,13,16],[]),([0,1,11,2,21,3],[12,16],[]),([0,1,11,2,3,4,10],[2,3,4,11],[0]),([0,1,11,2,3,4,10,5],[6,7,8,9,10],[]),([0,1,11,2,3,4,103],[0,12],[]),([0,1,6,71,2,3,4,5],[1,17],[]),([0,1,6,53,3,4,121,5],[3,5,11,14,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_8Ok : checkNodesBT h0W h0G h0Mask h0Block7_8Pools h0Autos h0Bucket6 7 h0Block7_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_8Mem : ∀ ns ∈ h0Block7_8, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_8Ok
def h0Block7_9Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool14,(29,[]),pool3,pool0,pool2,pool10,pool8,(17,[]),(2,[(1,0,1),(1,11,2)]),(19,[]),(10,[(1,0,1),(1,82,4)])]
def h0Block7_9Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_9Specs
def h0Block7_9 : List NodeSpec := [([0,1,6,123,2,3,4,5],[6,8,9,11,13],[]),([0,1,6,54,2,3,134,5],[1,2,5,10],[0]),([0,1,6,54,3,133,4,5],[1,2,6,10],[0]),([0,1,6,2,140,3,4,5],[1,6,10],[]),([0,1,6,2,12,3,22,4],[3,4,8,12],[0,1]),([0,1,6,2,3,148,4,5],[1,10],[]),([0,1,6,2,3,139,4,5],[1,4,8],[0]),([0,1,6,2,3,4,43,5],[0,10],[0]),([0,1,6,2,3,4,161,5],[0,4,9,14],[]),([0,1,6,2,3,4,68,5],[0,1,4,8,13],[0]),([0,1,6,2,3,4,120,5],[2,7,8,9],[0]),([0,1,6,2,3,10,16,5],[0,1,2,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_9Ok : checkNodesBT h0W h0G h0Mask h0Block7_9Pools h0Autos h0Bucket6 7 h0Block7_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_9Mem : ∀ ns ∈ h0Block7_9, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_9Ok
def h0Block7_10Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool4,pool3,pool6,pool0,pool2,(27,[]),pool8,(13,[]),pool11,(8,[]),(23,[]),(10,[]),pool24,(20,[(1,0,2)])]
def h0Block7_10Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block7_10Specs
def h0Block7_10 : List NodeSpec := [([0,1,116,2,3,4],[1,7],[]),([0,1,63,64,4,5],[5,7],[]),([0,1,63,3,4,78],[5,7],[]),([0,1,2,211,184,4,5],[6,7,8,9],[0]),([0,1,2,194,183,3,4,5],[7,9,15,16],[]),([0,1,2,183,3,191,4,5],[7,9,15,16],[]),([0,1,2,183,3,4,193,5],[0,4],[]),([0,1,2,183,3,4,5],[3,4,11],[]),([0,1,2,106,3,134,5],[2,5,8],[0]),([0,1,2,204,3,16,5],[5,12],[]),([0,1,2,181,212,3,4,5],[13,14,17],[0]),([0,1,2,100,3,4],[2,7,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_10Ok : checkNodesBT h0W h0G h0Mask h0Block7_10Pools h0Autos h0Bucket6 7 h0Block7_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_10Mem : ∀ ns ∈ h0Block7_10, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_10Ok
def h0Block7_11Specs : List PoolSpec := [pool13,pool1,pool12,(24,[]),pool4,pool3,pool0,pool2,(27,[]),pool8,(10,[]),(2,[])]
def h0Block7_11Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_11Specs
def h0Block7_11 : List NodeSpec := [([0,1,2,100,3,4,5],[0,6],[]),([0,1,2,39,3,4],[2,3,6],[]),([0,1,2,3,197,4,5],[4,8,10,11],[]),([0,1,2,3,4,319,5],[5,6],[]),([0,1,2,3,4,333,5],[4,5],[]),([0,1,183,3,4,92,5],[4,8],[0]),([0,1,106,3,133,4,5],[1,5,7],[0]),([1,11,2,106,3,4],[6,9],[]),([1,6,2,106,131,3,4,5],[4,6,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_11Ok : checkNodesBT h0W h0G h0Mask h0Block7_11Pools h0Autos h0Bucket6 7 h0Block7_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_11Mem : ∀ ns ∈ h0Block7_11, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_11Ok
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4 ++ h0Block7_5 ++ h0Block7_6 ++ h0Block7_7 ++ h0Block7_8 ++ h0Block7_9 ++ h0Block7_10 ++ h0Block7_11
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block7_0Mem h0Block7_1Mem) h0Block7_2Mem) h0Block7_3Mem) h0Block7_4Mem) h0Block7_5Mem) h0Block7_6Mem) h0Block7_7Mem) h0Block7_8Mem) h0Block7_9Mem) h0Block7_10Mem) h0Block7_11Mem)
def h0Block8_0Specs : List PoolSpec := [pool9,pool1,pool14,pool12,pool4,(14,[]),pool0,pool2,pool10,(47,[]),(13,[]),(2,[(1,0,1),(1,6,2)]),(2,[(1,0,1),(2,6,2)]),pool21,(2,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,2,4)])]
def h0Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_0Specs
def h0Block8_0 : List NodeSpec := [([26,44,0,1,2,3,4],[1,2,4,13],[0,1]),([26,41,0,1,2,3,4],[1,3,6,12],[0]),([26,47,0,1,2,3,4],[1,8],[0]),([26,79,0,1,2,3,4],[6,9],[0]),([26,0,1,7,2,3,4],[0,6,8],[]),([26,0,1,58,2,3,4],[4,8,9],[]),([26,0,1,6,2,3,65,4],[0,1,3,6,7,8,14],[0]),([26,0,1,6,2,3,4,92],[0,1,3,6,7,8,15],[0,1]),([26,0,1,53,2,3,4],[6,9,10],[0]),([26,0,1,54,2,3,4],[6,9],[]),([26,0,1,2,18,3,4],[1,2,3,5,10,11],[0]),([26,0,1,2,3,65,4],[0,1,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Ok : checkNodesBT h0W h0G h0Mask h0Block8_0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Mem : ∀ ns ∈ h0Block8_0, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_0Ok
def h0Block8_1Specs : List PoolSpec := [pool9,pool1,pool5,pool12,(29,[]),(30,[]),pool4,pool3,(14,[]),pool0,pool2,pool10,(27,[]),(13,[]),pool7,(16,[]),pool11,(4,[]),(15,[]),pool22,(0,[(1,2,4),(2,6,5)]),(1,[(1,2,4),(2,6,5)])]
def h0Block8_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_1Specs
def h0Block8_1 : List NodeSpec := [([26,0,1,2,3,4,61],[1,3,8,9,15,18,19],[0,1]),([26,0,1,2,3,4,92],[11,13,20,21],[0]),([86,0,1,2,3,4,61],[7,8,9,17,18,19],[0,1]),([45,0,1,6,2,3,4,5],[1,2,3,5,9,10,12],[0]),([186,0,1,2,3,4,5],[1,4,16],[]),([268,0,1,2,3,4,5],[1,4,16],[]),([332,0,1,2,3,4,318,5],[7,10,16],[0]),([321,0,1,2,3,4,5],[0,16],[]),([397,0,1,2,3,4,5],[7,16],[]),([443,0,1,2,3,4,5],[10,16],[]),([402,0,1,2,3,4,5],[9,14],[]),([446,0,1,2,3,4,5],[2,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_1Ok : checkNodesBT h0W h0G h0Mask h0Block8_1Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_1Mem : ∀ ns ∈ h0Block8_1, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_1Ok
def h0Block8_2Specs : List PoolSpec := [(18,[]),pool1,pool5,pool14,pool12,pool19,(30,[]),(31,[]),pool4,pool3,pool0,pool2,pool17,(11,[]),(2,[(1,0,1),(2,6,2),(2,6,4)]),(10,[(1,0,1),(2,6,4)]),pool21,(0,[(2,6,4),(3,2,5)]),(1,[(2,6,4),(3,2,5)])]
def h0Block8_2Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_2Specs
def h0Block8_2 : List NodeSpec := [([236,0,1,2,3,4,5],[8,9,10],[]),([294,0,1,2,3,4,5],[8,9,10],[]),([366,0,1,2,3,4,5],[0,2,10],[]),([44,87,0,1,2,3,5],[9,10,13],[]),([44,41,0,1,2,3,4,5],[1,4,7,10,11,14],[0,1]),([44,70,0,1,6,2,3,4,5],[3,4,5,6,15,16],[0]),([44,70,0,1,2,3,4,5],[4,9,15,17,18],[]),([44,79,0,1,2,3,5],[1,4,10],[0]),([44,0,1,11,2,3,4],[1,2,3,8,11,12,15],[0,1]),([44,0,1,11,2,3,4,5],[0,1,2,3,8,11,15,16],[0,1]),([44,0,1,6,2,3,65,4,5],[3,4,6,9,11],[0]),([44,0,1,54,2,3,5],[9,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_2Ok : checkNodesBT h0W h0G h0Mask h0Block8_2Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_2Mem : ∀ ns ∈ h0Block8_2, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_2Ok
def h0Block8_3Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool14,pool19,pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,pool8,pool7,(3,[]),(19,[]),(0,[]),(32,[]),(16,[(1,0,1)]),(2,[(1,0,1),(2,6,114)])]
def h0Block8_3Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_3Specs
def h0Block8_3 : List NodeSpec := [([44,0,1,2,3,4,5],[6,7],[]),([44,0,1,2,3,312,5],[7,10,17],[]),([44,0,1,2,3,61,5],[7,10,15],[0,1]),([119,0,1,2,3,4,5],[3,6,7,11,20],[0]),([87,89,0,1,6,2,3,4,5],[0,1,2,4,8,13],[0,1]),([87,31,0,1,6,2,3,4,5],[0,5,12,13,16,19],[]),([87,28,0,1,6,2,3,4,5],[1,4,11,14,16,18],[0]),([87,328,0,1,3,4,5],[7,10],[]),([87,0,1,11,2,3,4],[10,13],[]),([87,0,1,6,2,131,3,4,5],[2,6,7,9,10,13],[0]),([87,0,1,2,3,229,4,5],[1,6,14],[]),([87,0,1,2,3,298,5],[7,10,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_3Ok : checkNodesBT h0W h0G h0Mask h0Block8_3Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_3Mem : ∀ ns ∈ h0Block8_3, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_3Ok
def h0Block8_4Specs : List PoolSpec := [pool9,pool1,pool12,(29,[]),pool4,pool3,pool6,pool0,pool2,pool10,pool8,pool7,(16,[]),pool11,(8,[]),(36,[]),(35,[]),(1,[(2,2,4),(3,3,5),(1,28,2)])]
def h0Block8_4Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_4Specs
def h0Block8_4 : List NodeSpec := [([87,0,1,2,3,134,5],[5,10,14,15,16],[0]),([87,0,1,30,3,4,5],[0,6,8,17],[0]),([87,0,1,174,3,188,4,5],[0,4,7,8],[0]),([297,0,1,2,3,4,5],[7,11],[]),([369,0,1,2,3,4,5],[7,11],[]),([377,0,1,2,3,4,5],[1,2,3],[]),([433,0,1,2,3,4,5],[8,13],[]),([198,108,0,1,2,3,5],[5,13],[]),([198,0,1,2,3,188,4,5],[4,5,8,9,13],[1]),([198,0,1,2,3,114,5],[8,11,13],[]),([198,0,1,2,3,4,5],[5,13],[]),([198,0,1,2,3,312,5],[5,7,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_4Ok : checkNodesBT h0W h0G h0Mask h0Block8_4Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_4Mem : ∀ ns ∈ h0Block8_4, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_4Ok
def h0Block8_5Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool14,pool12,(29,[]),pool4,pool3,pool6,pool0,pool2,pool10,pool8,(2,[(1,0,1),(1,6,2),(2,18,4)]),pool7,(16,[]),pool11,(3,[]),(2,[(1,0,2),(2,174,4),(1,3,4)]),(36,[]),(35,[])]
def h0Block8_5Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_5Specs
def h0Block8_5 : List NodeSpec := [([198,0,1,2,3,16,5],[2,8,13,17,18,19],[1]),([233,0,1,2,3,4,5],[15,16,17],[]),([436,0,1,2,3,4,5],[0,3,10],[]),([176,234,0,1,3,4,5],[8,10],[]),([176,0,1,174,3,4,5],[10,15],[]),([38,0,1,6,2,3,5],[2,5,10,11,14],[0]),([38,0,1,2,3,4,5],[7,8],[]),([38,0,1,2,3,5],[2,10,13,14,15],[]),([89,180,0,1,2,4,5],[2,9,16,17],[]),([89,314,0,1,2,4,5],[6,7],[]),([89,98,0,1,2,4,5],[8,12,20,21],[0]),([89,0,1,6,2,3,4,92,5],[0,1,2,4,5,9,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_5Ok : checkNodesBT h0W h0G h0Mask h0Block8_5Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_5Mem : ∀ ns ∈ h0Block8_5, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_5Ok
def h0Block8_6Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool12,pool3,pool6,pool0,pool2,pool10,pool8,pool11,(6,[]),(19,[]),(0,[]),(2,[(1,0,1),(1,2,3),(2,65,4)]),(36,[]),(35,[])]
def h0Block8_6Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_6Specs
def h0Block8_6 : List NodeSpec := [([89,0,1,2,146,4,5],[5,10,16,17],[0]),([165,0,1,2,3,4,5],[5,9,16,17],[0]),([239,0,1,2,3,4,5],[1,6,11],[]),([372,0,1,2,3,4,5],[5,6,13],[]),([285,0,1,2,3,4,5],[2,6],[]),([285,0,1,2,3,312,5],[5,11,14],[]),([290,0,1,2,3,4,5],[2,6],[]),([159,0,1,2,3,4,5],[0,5,12,16,17],[0]),([69,0,1,6,2,3,65,4,5],[1,4,5,8,10],[]),([69,0,1,6,2,3,4,5],[0,1,2,3,5,7,8,15],[0]),([69,0,1,2,3,114,5],[3,10],[]),([69,0,1,2,3,4,5],[1,6,8,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_6Ok : checkNodesBT h0W h0G h0Mask h0Block8_6Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_6Mem : ∀ ns ∈ h0Block8_6, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_6Ok
def h0Block8_7Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,pool4,pool3,pool6,pool0,pool2,pool10,(27,[]),(2,[(1,0,1),(2,6,2),(2,6,3)]),pool11,(17,[]),(19,[]),(8,[(1,0,1),(3,4,5)]),(2,[(1,0,2),(3,1,174),(2,35,3)])]
def h0Block8_7Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_7Specs
def h0Block8_7 : List NodeSpec := [([394,0,1,2,3,4,5],[7,10],[]),([215,0,1,2,3,4,5],[7,14],[]),([31,74,0,1,2,3,4,5],[6,7,14],[]),([31,0,1,292,2,3,4,5],[6,7,14],[]),([31,0,1,7,6,2,3,4,5],[4,10,11],[0]),([31,0,1,6,53,2,3,4,5],[6,10,11,14,15,16,17],[0]),([31,0,1,2,109,3,4,5],[7,11,14],[]),([42,0,1,6,2,3,4,5],[3,5,7,8,9],[0]),([182,0,1,2,174,3,4,5],[3,6,10,12,18],[0]),([46,41,0,1,2,3,4,5],[2,3,5,9,10,13],[0,1]),([104,0,1,11,2,3,4],[0,3,4],[]),([180,177,0,1,174,3,4,5],[1,8,9,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_7Ok : checkNodesBT h0W h0G h0Mask h0Block8_7Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_7Mem : ∀ ns ∈ h0Block8_7, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_7Ok
def h0Block8_8Specs : List PoolSpec := [pool13,pool1,pool5,pool14,pool12,pool4,pool3,pool6,pool0,pool2,pool10,(27,[]),(11,[]),pool8,(2,[(1,0,1),(1,6,2),(2,18,3)]),pool7,pool11,(1,[]),(19,[(3,1,174)])]
def h0Block8_8Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_8Specs
def h0Block8_8 : List NodeSpec := [([180,35,0,1,2,3,4,5],[1,8,9,15,18],[]),([180,0,1,2,131,4,5],[8,9,15],[]),([180,0,1,2,3,4,203,5],[2,6,16],[]),([230,0,1,2,3,4,5],[1,9,15,17],[]),([223,0,1,2,3,4,5],[13,15,16],[]),([37,0,1,6,2,4,5],[1,4,8,9,14],[0]),([37,0,1,2,4,5],[0,1,8,12],[]),([314,205,0,1,2,3,5],[1,7],[]),([344,0,1,2,3,4,5],[5,6],[]),([77,0,1,2,4,312,5],[5,6,8],[]),([98,0,1,6,2,3,4,92,5],[1,7,9,10,11],[]),([98,0,1,6,2,3,4,5],[2,3,4,6,9,10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_8Ok : checkNodesBT h0W h0G h0Mask h0Block8_8Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_8Mem : ∀ ns ∈ h0Block8_8, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_8Ok
def h0Block8_9Specs : List PoolSpec := [pool13,pool9,pool1,pool14,pool4,pool3,pool6,pool0,pool2,pool17,(47,[]),pool8,pool7,pool11,(19,[]),(20,[]),(9,[(1,0,1),(3,3,5)]),(32,[]),(1,[(1,0,4),(3,3,5)]),pool23,pool25]
def h0Block8_9Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_9Specs
def h0Block8_9 : List NodeSpec := [([98,0,1,2,131,4,5],[0,8],[]),([417,0,1,2,3,4,5],[6,8],[]),([28,177,0,1,174,3,4,5],[1,6,8,15],[]),([28,35,0,1,2,3,4,5],[2,7,8,11],[]),([28,205,0,1,2,3,312,5],[2,6,10],[0]),([28,74,0,1,2,3,4,312,5],[4,7,17,18],[]),([28,74,0,1,2,3,4,5],[2,5,12,13,19,20],[0]),([28,0,1,330,2,3,4,5],[2,6,10],[]),([28,0,1,84,2,3,4,5],[2,6,10],[]),([28,0,1,7,6,2,3,4,5],[1,3,8,9],[0]),([28,0,1,6,54,2,3,4,5],[1,2,5,8,14,16],[0]),([28,0,1,2,106,3,4,5],[1,2,6,8,15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_9Ok : checkNodesBT h0W h0G h0Mask h0Block8_9Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_9Mem : ∀ ns ∈ h0Block8_9, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_9Ok
def h0Block8_10Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,pool14,pool12,(29,[]),pool3,pool6,pool0,pool2,pool8,(13,[]),pool7,(8,[]),(9,[]),(10,[]),(2,[(1,0,1),(0,2,3),(2,6,53)]),(2,[(1,0,1),(0,2,4),(2,6,54)]),(2,[(1,0,1),(2,6,153)]),(1,[(2,2,4),(3,3,5),(1,87,28)])]
def h0Block8_10Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_10Specs
def h0Block8_10 : List NodeSpec := [([28,0,1,2,407,3,4,5],[2,3,9],[]),([149,0,1,2,3,4,5],[2,9,11,21],[0]),([41,47,0,1,3,4,5],[3,6,10],[0]),([41,0,1,11,2,3,4],[10,12],[]),([41,0,1,6,2,3,4,16,5],[5,6,7,11,12,14],[0,1]),([41,0,1,53,3,4,5],[10,14],[]),([41,0,1,54,3,4,5],[10,14],[]),([157,0,1,2,3,4,5],[4,8,10,16,20],[1]),([136,0,1,2,3,4,5],[4,6,10,15,19],[0]),([113,0,1,2,3,4,5],[1,3,10,13,16,17,18],[0]),([282,0,1,2,3,4,5],[0,10],[]),([278,0,1,2,3,4,5],[0,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_10Ok : checkNodesBT h0W h0G h0Mask h0Block8_10Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_10Mem : ∀ ns ∈ h0Block8_10, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_10Ok
def h0Block8_11Specs : List PoolSpec := [pool13,pool9,pool1,pool12,(29,[]),pool4,pool3,pool6,pool0,pool2,pool10,(5,[]),pool8,pool7,(16,[]),(2,[(1,0,1),(1,6,4),(3,2,61)]),pool23,pool25]
def h0Block8_11Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_11Specs
def h0Block8_11 : List NodeSpec := [([107,0,1,11,2,3,4],[0,5,9],[]),([328,0,1,3,312,92,5],[6,8],[]),([336,0,1,2,3,4,5],[5,6,8],[]),([313,0,1,2,3,312,5],[6,8],[]),([76,0,1,6,3,4,5],[2,3,8,9,15],[0]),([76,0,1,3,4,312,5],[5,6,8],[]),([76,0,1,3,4,61,5],[2,4,11,14,15],[0,1]),([76,0,1,3,4,5],[2,8,12,13,15],[]),([70,205,0,1,2,3,312,5],[8,13],[]),([70,74,0,1,2,3,4,5],[5,6,7,8,16,17],[0]),([70,0,1,292,2,3,4,5],[1,8,13],[]),([70,0,1,84,2,3,4,5],[8,10,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_11Ok : checkNodesBT h0W h0G h0Mask h0Block8_11Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_11Mem : ∀ ns ∈ h0Block8_11, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_11Ok
def h0Block8_12Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,(29,[]),(24,[]),(30,[]),(31,[]),pool4,pool3,pool6,pool0,pool2,pool10,(47,[]),(11,[]),pool15,pool8,(13,[]),(16,[]),(4,[]),(10,[(1,0,1),(0,6,4)]),(10,[(1,0,1),(1,6,4)]),(19,[]),pool16]
def h0Block8_12Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_12Specs
def h0Block8_12 : List NodeSpec := [([70,0,1,58,6,2,3,4,5],[4,5,6,15,23],[0]),([70,0,1,2,3,4,61,5],[1,3,11,13,17,24],[]),([70,0,1,2,3,312,203,5],[9,11,13,25],[]),([431,0,1,2,3,4,5],[11,14,19],[]),([317,0,1,2,3,4,5],[10,11,13],[]),([117,350,0,1,2,3,4],[13,16],[]),([117,0,1,6,2,3,4],[2,6,8,13,18],[0]),([117,0,1,2,3,4,312],[11,13,26],[]),([47,0,1,11,2,3,4],[2,4,5,7],[0]),([124,0,1,2,3,4,5],[11,13,20,22],[]),([79,0,1,11,2,3,4],[0,13,21],[]),([141,0,1,2,3,4,5],[12,13,20,22],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_12Ok : checkNodesBT h0W h0G h0Mask h0Block8_12Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_12Mem : ∀ ns ∈ h0Block8_12, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_12Ok
def h0Block8_13Specs : List PoolSpec := [pool9,pool1,(29,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(27,[]),pool8,pool7,pool11,(19,[])]
def h0Block8_13Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_13Specs
def h0Block8_13 : List NodeSpec := [([421,0,1,2,3,4,5],[1,3,7],[]),([454,0,1,2,3,4,5],[8,13],[]),([396,0,1,2,3,4,5],[1,3,7],[]),([426,0,1,2,3,4,5],[8,13],[]),([442,0,1,2,3,4,5],[8,13],[]),([177,0,1,181,174,3,4,5],[5,7,10,11],[]),([177,0,1,174,3,4,16,5],[2,12,13],[]),([457,0,1,2,3,4,5],[1,4,6],[]),([296,0,1,2,3,4,5],[0,4,7],[]),([352,0,1,2,3,4,5],[5,7,9],[]),([368,0,1,2,3,4,5],[1,3,7,14],[]),([376,0,1,2,3,4,5],[1,3,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_13Ok : checkNodesBT h0W h0G h0Mask h0Block8_13Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_13Mem : ∀ ns ∈ h0Block8_13, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_13Ok
def h0Block8_14Specs : List PoolSpec := [pool1,pool5,pool12,pool4,pool3,pool0,pool2,(27,[]),(5,[]),pool8,pool7,(16,[]),pool11,(12,[]),(2,[]),(19,[(3,1,174)])]
def h0Block8_14Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_14Specs
def h0Block8_14 : List NodeSpec := [([406,0,1,2,3,4,5],[0,3,5],[]),([432,0,1,2,3,4,5],[6,12],[]),([35,187,0,2,3,4,5],[0,6,14],[]),([35,0,1,2,181,3,4,5],[0,1,5,7,9],[0]),([35,0,1,2,3,4,16,5],[0,10,11,12,13,15],[]),([35,0,6,2,3,4,5],[0,2,5,6,8],[0]),([424,0,1,2,3,4,5],[1,4],[]),([429,0,1,2,3,4,5],[1,10],[]),([448,0,1,2,3,4,5],[1,10],[]),([238,0,1,2,3,4,5],[0,1,4],[]),([354,0,1,2,3,4,5],[0,1,10],[]),([371,0,1,2,3,4,5],[0,1,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_14Ok : checkNodesBT h0W h0G h0Mask h0Block8_14Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_14Mem : ∀ ns ∈ h0Block8_14, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_14Ok
def h0Block8_15Specs : List PoolSpec := [pool13,pool1,pool5,pool4,pool3,pool6,(14,[]),pool0,pool10,(47,[]),(5,[]),pool8,pool7,pool11,(17,[]),(19,[(3,1,263)])]
def h0Block8_15Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_15Specs
def h0Block8_15 : List NodeSpec := [([266,0,1,2,3,4,92,5],[3,5,7,14,15],[]),([410,0,1,2,3,4,5],[2,4],[]),([438,0,1,2,3,4,5],[1,2,4],[]),([214,0,1,2,3,4,5],[1,2,7],[]),([205,0,1,2,3,65,312,5],[0,7],[]),([205,0,1,2,3,298,5],[1,12],[]),([205,0,1,2,3,269,5],[5,13],[0]),([404,0,1,2,3,4,5],[1,8,10],[]),([450,0,1,2,3,4,5],[1,6,12],[]),([241,0,1,2,3,4,5],[3,5,8],[]),([299,0,1,2,3,4,5],[3,9,12],[]),([374,0,1,2,3,4,5],[1,3,11],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_15Ok : checkNodesBT h0W h0G h0Mask h0Block8_15Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_15Mem : ∀ ns ∈ h0Block8_15, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_15Ok
def h0Block8_16Specs : List PoolSpec := [pool1,(24,[]),pool4,pool3,pool6,pool0,pool2,pool10,pool11,(9,[]),(19,[]),pool23,pool25]
def h0Block8_16Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_16Specs
def h0Block8_16 : List NodeSpec := [([451,0,1,2,3,4,5],[6,8],[]),([74,0,1,2,3,65,4,5],[0,3,5,11,12],[]),([74,0,1,2,3,4,92,5],[2,3,5,11,12],[]),([74,0,1,2,3,4,16,5],[2,3,8,9,11,12],[]),([453,0,1,2,3,4,5],[0,1,4],[]),([440,0,1,2,3,4,5],[2,4,7],[]),([208,234,0,1,3,4,5],[0,8],[]),([208,350,0,1,2,3,5],[0,5],[]),([208,364,0,1,2,3,4,5],[0,5,7,10],[]),([208,0,1,2,3,4,5],[2,4,7],[]),([208,0,1,2,3,312,92,5],[3,5,7],[]),([208,0,1,2,3,312,5],[0,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_16Ok : checkNodesBT h0W h0G h0Mask h0Block8_16Pools h0Autos h0Bucket7 8 h0Block8_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_16Mem : ∀ ns ∈ h0Block8_16, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_16Ok
def h0Block8_17Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool12,(29,[]),pool4,pool3,pool0,pool2,(47,[]),(27,[]),pool7,(16,[]),pool11,(2,[(3,0,2),(1,3,4),(3,1,16)])]
def h0Block8_17Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_17Specs
def h0Block8_17 : List NodeSpec := [([208,0,1,174,3,4,5],[2,14],[]),([219,0,1,2,3,4,5],[2,8,13],[]),([255,234,0,1,2,3,4,5],[2,3,7,9,15],[]),([286,0,1,2,3,4,5],[2,3,8],[]),([187,234,0,1,2,3,4,16,5],[2,5,8,9,12],[0]),([187,0,1,2,3,4,298,5],[0,2,8,9,10,11],[]),([422,0,1,2,3,4,5],[2,4,8],[]),([400,0,1,2,3,4,5],[3,6],[]),([427,0,1,2,3,4,5],[2,4,8],[]),([445,0,1,2,3,4,5],[3,6],[]),([234,0,1,2,3,229,4,5],[1,6,9],[]),([234,0,1,258,3,4,5],[9,14],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_17Ok : checkNodesBT h0W h0G h0Mask h0Block8_17Pools h0Autos h0Bucket7 8 h0Block8_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_17Mem : ∀ ns ∈ h0Block8_17, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_17Ok
def h0Block8_18Specs : List PoolSpec := [pool1,pool12,(29,[]),pool4,pool3,pool6,pool0,pool2,pool7,pool11]
def h0Block8_18Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_18Specs
def h0Block8_18 : List NodeSpec := [([234,0,1,249,3,4,5],[5,9],[]),([234,0,1,175,3,4,16,5],[2,3,8],[]),([234,0,1,3,253,4,5],[4,9],[]),([234,0,1,3,133,4,5],[4,7],[]),([234,0,1,3,4,121,5],[7,9],[]),([234,0,1,3,4,243,5],[3,4],[0]),([456,0,1,2,3,4,5],[4,7],[]),([256,0,1,2,3,4,5],[4,7],[]),([262,0,1,2,3,4,5],[4,7],[]),([257,0,1,2,3,4,5],[4,9],[]),([260,0,1,2,3,4,5],[5,7],[]),([408,0,1,2,3,4,5],[0,1,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_18Ok : checkNodesBT h0W h0G h0Mask h0Block8_18Pools h0Autos h0Bucket7 8 h0Block8_18 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_18Mem : ∀ ns ∈ h0Block8_18, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_18Ok
def h0Block8_19Specs : List PoolSpec := [pool9,pool1,pool5,pool12,pool4,pool3,pool0,pool2,pool10,(47,[]),(5,[]),(13,[]),pool7,pool11,(6,[]),(23,[]),(10,[])]
def h0Block8_19Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_19Specs
def h0Block8_19 : List NodeSpec := [([434,0,1,2,3,4,5],[2,4],[]),([34,1,6,2,3,4,5],[1,3,6,10],[]),([291,0,1,2,158,4,5],[5,6,16],[]),([291,0,1,2,4,122,5],[12,13,16],[]),([423,0,1,2,3,4,5],[0,5,6],[]),([306,0,1,2,3,4,5],[6,12],[]),([311,0,1,2,3,4,5],[5,8,13],[]),([428,0,1,2,3,4,5],[6,9,14],[]),([447,0,1,2,3,4,5],[6,11,12],[]),([409,0,1,2,3,4,5],[0,5,6],[]),([437,0,1,2,3,4,5],[5,6,15],[]),([381,0,1,2,3,4,5],[5,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_19Ok : checkNodesBT h0W h0G h0Mask h0Block8_19Pools h0Autos h0Bucket7 8 h0Block8_19 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_19Mem : ∀ ns ∈ h0Block8_19, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_19Ok
def h0Block8_20Specs : List PoolSpec := [pool13,(18,[]),pool1,pool14,pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,pool8,pool7,pool11,(3,[]),(0,[])]
def h0Block8_20Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_20Specs
def h0Block8_20 : List NodeSpec := [([350,0,1,2,3,130,5],[0,8],[]),([350,0,1,2,3,103,5],[6,8],[]),([350,0,1,2,3,160,5],[0,8],[]),([350,0,1,2,3,134,5],[1,2,11,12],[]),([403,0,1,2,3,4,5],[6,8,10],[]),([449,0,1,2,3,4,5],[7,8,12],[]),([73,1,6,2,3,4,5],[2,3,4,14],[]),([73,1,2,3,4,312,5],[4,5,15],[]),([73,1,2,3,4,61,5],[4,5,14],[]),([73,1,2,3,312,203,5],[4,5],[]),([378,0,1,2,3,4,5],[6,10,13],[]),([452,0,1,2,3,4,5],[6,8,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_20Ok : checkNodesBT h0W h0G h0Mask h0Block8_20Pools h0Autos h0Bucket7 8 h0Block8_20 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_20Mem : ∀ ns ∈ h0Block8_20, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_20Ok
def h0Block8_21Specs : List PoolSpec := [pool13,(18,[]),pool9,pool5,pool4,pool3,pool6,pool0,pool2,pool10,(47,[]),pool7,pool11,(12,[]),(19,[]),(0,[]),(2,[]),(0,[(3,3,5),(1,28,350)])]
def h0Block8_21Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_21Specs
def h0Block8_21 : List NodeSpec := [([439,0,1,2,3,4,5],[6,9,12],[]),([326,0,1,2,3,4,5],[6,8],[]),([326,1,2,3,4,312,5],[5,7,15],[]),([326,1,2,3,312,92,5],[5,7],[]),([338,1,2,3,4,312,5],[5,12,15],[]),([388,0,1,2,3,4,5],[7,8,13],[]),([364,0,1,375,2,3,4,5],[3,4,7,14],[]),([364,0,1,2,3,4,103,5],[1,7,10],[]),([364,1,2,106,3,4,5],[0,7,16],[]),([357,0,1,2,3,4,5],[7,11],[]),([363,0,1,2,3,4,5],[2,6,17],[]),([307,0,1,2,3,4,5],[5,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_21Ok : checkNodesBT h0W h0G h0Mask h0Block8_21Pools h0Autos h0Bucket7 8 h0Block8_21 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_21Mem : ∀ ns ∈ h0Block8_21, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_21Ok
def h0Block8_22Specs : List PoolSpec := [pool13,pool9,pool1,pool3,pool6,pool0,pool2,(47,[]),pool8,pool7,pool11,(2,[])]
def h0Block8_22Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_22Specs
def h0Block8_22 : List NodeSpec := [([309,0,1,2,3,4,5],[1,5,9],[]),([358,0,1,2,3,4,5],[2,4,8],[]),([361,0,1,2,3,4,5],[1,5,9],[]),([245,0,1,2,3,4,5],[3,6],[]),([248,0,1,2,3,4,5],[6,10],[]),([300,0,1,2,3,4,5],[1,3,5],[]),([303,0,1,2,3,4,5],[2,7,9],[]),([356,0,1,2,3,4,5],[3,5,8],[]),([0,359,1,2,3,92,5],[4,6],[]),([0,390,1,2,3,4,5],[4,5,8],[]),([0,398,395,1,2,3,4,5],[0,5,11],[]),([0,301,1,2,3,4,5],[2,3,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_22Ok : checkNodesBT h0W h0G h0Mask h0Block8_22Pools h0Autos h0Bucket7 8 h0Block8_22 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_22Mem : ∀ ns ∈ h0Block8_22, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_22Ok
def h0Block8_23Specs : List PoolSpec := [pool1,pool5,pool12,pool4,pool3,pool6,pool0,pool2,pool10,pool8,pool7,(16,[]),pool11,(4,[]),(0,[]),(2,[])]
def h0Block8_23Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_23Specs
def h0Block8_23 : List NodeSpec := [([0,305,1,2,3,4,5],[4,8,12],[]),([0,415,1,2,3,4,5],[4,6,13,15],[]),([0,302,1,2,3,4,203,5],[0,9,12],[]),([0,242,1,175,3,4,5],[0,6,11],[]),([0,246,1,2,3,4,5],[4,12,14],[]),([0,251,1,3,4,92,5],[3,4],[]),([0,254,1,2,3,4,5],[4,7],[]),([0,247,1,2,3,4,203,5],[4,12],[]),([0,412,1,2,3,4,92,5],[5,6,7],[]),([0,412,1,2,3,4,5],[0,2,6],[]),([0,206,1,2,3,4,5],[9,10,12],[]),([0,202,1,2,3,4,5],[1,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_23Ok : checkNodesBT h0W h0G h0Mask h0Block8_23Pools h0Autos h0Bucket7 8 h0Block8_23 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_23Mem : ∀ ns ∈ h0Block8_23, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_23Ok
def h0Block8_24Specs : List PoolSpec := [pool9,pool1,pool5,pool14,pool4,pool3,pool6,pool0,pool2,(11,[]),pool8,pool7,pool11,(12,[]),(17,[]),(10,[]),(1,[]),(2,[(1,0,2),(3,1,2),(3,177,174)]),(2,[(1,0,4),(3,1,4),(3,205,312)])]
def h0Block8_24Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_24Specs
def h0Block8_24 : List NodeSpec := [([0,178,1,174,3,4,5],[1,3,8,12,17],[]),([0,271,1,2,3,4,5],[1,6,16],[]),([0,315,1,2,3,312,5],[1,4,7,18],[0]),([0,1,209,174,3,4,5],[1,12],[]),([0,1,220,2,3,4,5],[1,9,10],[]),([0,1,225,2,174,3,4,5],[0,1,2,8,11],[0]),([0,1,287,2,3,4,5],[1,6,14,15],[]),([0,1,216,2,3,4,5],[1,2,9,11],[]),([0,1,342,2,3,4,5],[1,2,5,13],[]),([0,1,416,2,3,4,5],[2,5],[]),([0,1,231,2,174,3,4,5],[0,2,4,8],[]),([0,1,231,2,3,4,92,5],[6,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_24Ok : checkNodesBT h0W h0G h0Mask h0Block8_24Pools h0Autos h0Bucket7 8 h0Block8_24 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_24Mem : ∀ ns ∈ h0Block8_24, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_24Ok
def h0Block8_25Specs : List PoolSpec := [pool9,pool1,pool5,pool12,(29,[]),(24,[]),pool4,pool3,pool6,pool0,pool2,(2,[(1,0,1),(0,6,2)]),pool17,(11,[]),pool8,pool11,(23,[]),(10,[]),(2,[])]
def h0Block8_25Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_25Specs
def h0Block8_25 : List NodeSpec := [([0,1,265,2,3,4,5],[1,8,9],[]),([0,1,276,2,3,4,5],[8,9,13,17,18],[]),([0,1,330,2,3,312,5],[1,9],[]),([0,1,334,2,3,4,5],[7,9,13,17,18],[]),([0,1,50,2,3,4,16,5],[0,1,4,5,15],[]),([0,1,292,2,3,4,92,5],[0,6,7,9,13,16],[]),([0,1,382,2,3,4,5],[10,15],[]),([0,1,84,2,3,65,4,5],[1,8,9,14],[]),([0,1,411,2,3,4,5],[10,15],[]),([0,1,365,2,3,4,92,5],[1,2,6,9,10],[]),([0,1,7,11,2,3,4],[1,2,3,5,9,12],[0]),([0,1,7,11,2,3,4,5],[1,2,3,4,8,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_25Ok : checkNodesBT h0W h0G h0Mask h0Block8_25Pools h0Autos h0Bucket7 8 h0Block8_25 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_25Mem : ∀ ns ∈ h0Block8_25, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_25Ok
def h0Block8_26Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,(29,[]),pool19,pool4,pool3,pool0,pool2,pool10,(27,[]),pool15,pool8,(13,[]),pool7,(19,[]),(20,[]),(1,[(1,2,3),(0,6,65)]),(2,[(1,0,1),(3,70,6)]),(0,[(3,2,5),(3,70,6)])]
def h0Block8_26Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_26Specs
def h0Block8_26 : List NodeSpec := [([0,1,7,6,2,3,4,16,5],[1,3,4,5,6,13],[0]),([0,1,7,18,3,4,5],[2,4,5],[0]),([0,1,82,6,2,3,4,5],[1,2,3,5,7,10,12,14,21],[0]),([0,1,82,2,3,4,5],[1,12,19,22],[]),([0,1,151,2,3,4,5],[8,9],[]),([0,1,129,2,3,4,5],[10,17],[]),([0,1,67,6,2,3,65,4,5],[1,2,4,11],[]),([0,1,67,6,2,3,4,5],[1,2,3,5,9,10,18],[0]),([0,1,67,2,3,4,5],[9,11,16,20],[]),([0,1,58,11,2,3,4],[0,8,15],[]),([0,1,58,6,2,3,65,4,5],[4,5,6,11,12,15],[0]),([0,1,58,2,3,61,5],[2,5,10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_26Ok : checkNodesBT h0W h0G h0Mask h0Block8_26Pools h0Autos h0Bucket7 8 h0Block8_26 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_26Mem : ∀ ns ∈ h0Block8_26, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_26Ok
def h0Block8_27Specs : List PoolSpec := [pool13,pool1,pool5,pool14,pool12,pool4,pool6,(14,[]),pool0,pool2,pool17,pool10,(47,[]),pool15,pool8,(13,[]),pool7,(8,[]),(2,[(1,0,1),(1,11,2)]),(2,[(1,0,1),(1,11,4)]),(1,[]),(2,[(1,0,1),(1,2,4),(0,6,92)]),(0,[(1,2,4),(0,6,92)]),(0,[(3,4,5),(3,31,6)])]
def h0Block8_27Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_27Specs
def h0Block8_27 : List NodeSpec := [([0,1,170,6,2,3,4,5],[1,2,3,5,9,11,12,13],[]),([0,1,170,2,3,4,5],[2,11,15,17,23],[]),([0,1,145,2,3,4,5],[8,16],[]),([0,1,93,6,2,3,4,92,5],[3,4,9,11],[]),([0,1,93,6,2,3,4,5],[1,2,4,6,8,9,11,21],[0,1]),([0,1,93,2,3,4,5],[6,11,20,22],[]),([0,1,11,6,2,12,3,4],[1,2,4,8,9,10,14,18],[0,1]),([0,1,11,6,2,3,65,4],[1,4,9,14,15],[0]),([0,1,11,6,2,3,4],[1,4,8,10],[]),([0,1,11,6,2,3,4,13],[1,2,3,5,9,14,19],[0,1]),([0,1,11,6,2,3,4,92],[0,1,2,5,7,9],[0,1]),([0,1,11,53,2,3,4],[0,1,8,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_27Ok : checkNodesBT h0W h0G h0Mask h0Block8_27Pools h0Autos h0Bucket7 8 h0Block8_27 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_27Mem : ∀ ns ∈ h0Block8_27, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_27Ok
def h0Block8_28Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool12,(24,[]),pool4,pool3,(14,[]),pool0,pool2,pool17,pool10,pool15,pool8,(13,[]),pool11,(10,[(1,0,1),(1,6,4)]),(23,[]),(17,[]),(19,[]),(0,[(0,6,5)])]
def h0Block8_28Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_28Specs
def h0Block8_28 : List NodeSpec := [([0,1,11,53,2,3,4,5],[0,9,20],[0]),([0,1,11,54,2,3,4],[0,9,21],[0]),([0,1,11,2,18,3,4],[2,14],[0]),([0,1,11,2,3,65,4],[3,10,14],[]),([0,1,11,2,3,4,61],[2,4,9],[0,1]),([0,1,11,2,3,4,61,5],[2,3,4,5,9,10,11,12,17,18],[]),([0,1,11,2,3,4,92],[0,2,6,9,10],[]),([0,1,6,85,2,3,4],[2,4,9,13,15],[]),([0,1,6,51,2,3,4],[2,4,9,13,15],[]),([0,1,6,53,2,3,114,4,5],[1,2,6,9,10,16,19,20],[0,1]),([0,1,6,54,2,131,3,4,5],[2,6,7,8,9,14],[0]),([0,1,6,63,3,4,5],[2,4,5,8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_28Ok : checkNodesBT h0W h0G h0Mask h0Block8_28Pools h0Autos h0Bucket7 8 h0Block8_28 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_28Mem : ∀ ns ∈ h0Block8_28, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_28Ok
def h0Block8_29Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool12,(29,[]),pool19,pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(27,[]),(11,[]),pool15,pool8,(13,[]),pool7,(2,[(1,0,1),(1,11,2)]),(19,[]),(9,[(1,0,1),(1,87,3)]),(7,[(1,0,1),(1,107,3)]),(13,[(1,0,1)])]
def h0Block8_29Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_29Specs
def h0Block8_29 : List NodeSpec := [([0,1,6,2,33,3,4,5],[2,3,4,7,9,13,14,22],[0]),([0,1,6,2,20,4,5],[2,5,12,13,16,19],[0]),([0,1,6,2,21,3,5],[2,5,11,12,13,16],[0]),([0,1,6,2,59,3,4,5],[2,3,5,10,11,12,13,15],[]),([0,1,6,2,40,3,4],[2,5,12,17,19],[]),([0,1,6,2,12,3,4,5],[2,3,5,12,13,20,21],[0]),([0,1,6,2,142,3,4,92,5],[1,3,8,10,12,13,15],[0]),([0,1,6,2,3,146,4,5],[3,9,12,19,23],[0]),([0,1,6,2,3,152,4,5],[3,8,11,13,15,24],[]),([0,1,6,2,3,163,4,5],[3,4,5,9,13,20,25],[0,1]),([0,1,6,2,3,8,4,5],[0,1,2,3,4,5,6],[0]),([0,1,6,2,3,125,65,4,5],[1,4,9,13,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_29Ok : checkNodesBT h0W h0G h0Mask h0Block8_29Pools h0Autos h0Bucket7 8 h0Block8_29 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_29Mem : ∀ ns ∈ h0Block8_29, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_29Ok
def h0Block8_30Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,pool14,pool12,(29,[]),pool19,(30,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(27,[]),pool15,pool8,(13,[]),pool7,(2,[(1,0,1),(1,11,4)]),(19,[])]
def h0Block8_30Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_30Specs
def h0Block8_30 : List NodeSpec := [([0,1,6,2,3,138,4,5],[2,4,6,14],[]),([0,1,6,2,3,158,4,5],[4,6,9,11,14,20],[0,1]),([0,1,6,2,3,65,4,5],[4,6,9,11,14,20],[0]),([0,1,6,2,3,4,130,5],[0,4,6,8,11,14,16],[]),([0,1,6,2,3,4,72,5],[3,4,5,7,8,15,18,21],[0]),([0,1,6,2,3,4,10,5],[3,4,5,8,10,11,12,13],[0]),([0,1,6,2,3,4,78],[3,6,14,18,20],[]),([0,1,6,2,3,4,13,5],[3,4,5,10,11,15,19,22],[]),([0,1,6,2,3,4,103,5],[1,3,14,15,16,19,23],[0]),([0,1,6,2,3,4,121,5],[3,4,10,12,13,15,17],[0]),([0,1,6,2,3,4,160,5],[3,4,11,12,13,14,18],[1]),([0,1,6,2,3,4,92,16,5],[1,3,4,5,15,16,19,21],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_30Ok : checkNodesBT h0W h0G h0Mask h0Block8_30Pools h0Autos h0Bucket7 8 h0Block8_30 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_30Mem : ∀ ns ∈ h0Block8_30, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_30Ok
def h0Block8_31Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,pool14,pool12,(30,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(11,[]),pool15,(13,[]),pool7,(16,[]),(4,[]),(19,[]),(2,[]),(10,[(0,2,3)])]
def h0Block8_31Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_31Specs
def h0Block8_31 : List NodeSpec := [([0,1,6,2,3,4,92,5],[3,4,9,10,11,12,13],[]),([0,1,6,2,3,4,94,5],[1,4,5,7,13,16,21],[0]),([0,1,144,2,3,4,5],[12,18,19,20],[]),([0,1,171,2,3,4,5],[3,14,17,20],[]),([0,1,128,2,3,4,5],[12,15,17,18,20],[]),([0,1,150,2,3,4,5],[9,12,15,17,20],[]),([0,1,162,2,3,4,5],[2,8,17,20],[]),([0,1,53,2,3,4,318,5],[0,12,21],[0]),([0,1,53,2,353,4,5],[10,12],[]),([0,1,53,3,4,121,5],[4,6,8,10,13,23],[0]),([0,1,123,2,3,4,5],[4,9,13,14,22],[0]),([0,1,283,2,3,4,5],[3,14],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_31Ok : checkNodesBT h0W h0G h0Mask h0Block8_31Pools h0Autos h0Bucket7 8 h0Block8_31 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_31Mem : ∀ ns ∈ h0Block8_31, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_31Ok
def h0Block8_32Specs : List PoolSpec := [pool9,pool1,(29,[]),(24,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,(11,[]),(21,[]),(1,[(0,2,4),(0,3,5),(1,2,131)]),(1,[(0,2,4),(0,3,5),(1,131,4)]),(1,[(0,2,4),(3,3,5),(1,28,54)])]
def h0Block8_32Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_32Specs
def h0Block8_32 : List NodeSpec := [([0,1,281,2,3,4,5],[1,6],[]),([0,1,54,2,3,298,5],[5,8],[]),([0,1,54,2,3,134,5],[0,1,5,9,13],[0]),([0,1,54,3,133,4,5],[0,1,5,9,12],[0]),([0,1,329,3,4,196,5],[5,8,11],[]),([0,1,329,3,312,92,5],[4,5],[]),([0,1,337,2,3,4,5],[0,4],[]),([0,1,331,2,3,312,5],[4,5,8],[]),([0,1,63,3,4,312,5],[4,5,8],[]),([0,1,63,3,4,61,5],[1,2,3,7,10],[0]),([0,1,2,140,3,4,5],[0,6,9,14],[0]),([0,1,2,325,3,4,5],[4,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_32Ok : checkNodesBT h0W h0G h0Mask h0Block8_32Pools h0Autos h0Bucket7 8 h0Block8_32 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_32Mem : ∀ ns ∈ h0Block8_32, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_32Ok
def h0Block8_33Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool4,pool3,pool6,pool0,pool2,(47,[]),pool8,(13,[]),pool7,pool11,(19,[])]
def h0Block8_33Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_33Specs
def h0Block8_33 : List NodeSpec := [([0,1,2,30,3,4,312,5],[3,5,6,8],[0]),([0,1,2,249,3,312,5],[7,8],[]),([0,1,2,273,3,263,4,5],[0,2],[]),([0,1,2,273,3,4,312,5],[4,7,12],[]),([0,1,2,355,3,4,5],[7,9],[]),([0,1,2,304,3,4,5],[7,9],[]),([0,1,2,308,3,4,5],[5,7,11],[]),([0,1,2,360,3,4,5],[0,7],[]),([0,1,2,211,181,3,4,5],[2,7,8,12,14],[0]),([0,1,2,232,3,4,5],[1,8,10],[]),([0,1,2,228,3,4,5],[5,13],[]),([0,1,2,183,174,3,188,4,5],[2,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_33Ok : checkNodesBT h0W h0G h0Mask h0Block8_33Pools h0Autos h0Bucket7 8 h0Block8_33 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_33Mem : ∀ ns ∈ h0Block8_33, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_33Ok
def h0Block8_34Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool4,pool3,pool6,pool0,pool2,(47,[]),(27,[]),pool8,pool7,pool11,(12,[]),(19,[]),(20,[]),(10,[]),pool24,(17,[(1,0,2)]),(2,[(1,0,2),(1,1,3)]),(2,[(1,0,2),(1,1,4),(0,174,203)]),(1,[(1,0,2),(0,174,3)])]
def h0Block8_34Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_34Specs
def h0Block8_34 : List NodeSpec := [([0,1,2,183,3,188,4,5],[3,4,6,7,18],[0]),([0,1,2,183,3,4,5],[0,4,7,12,17,18,19],[0,1]),([0,1,2,227,3,4,5],[2,6,10,13],[]),([0,1,2,106,131,3,4,5],[2,4,5,7,8,16],[0]),([0,1,2,204,3,4,5],[5,11,13,14,15,21],[0]),([0,1,2,224,3,4,5],[2,9,12,13],[]),([0,1,2,181,174,3,188,4,5],[3,6,8,10,20],[0,1]),([0,1,2,181,3,4,203,5],[0,3,11,13],[]),([0,1,2,174,212,3,4,5],[1,2,8,13,22],[0]),([0,1,2,174,221,3,4,5],[2,3,8,13],[]),([0,1,2,174,3,207,4,5],[2,11,14],[]),([0,1,2,174,3,229,4,5],[3,4,8,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_34Ok : checkNodesBT h0W h0G h0Mask h0Block8_34Pools h0Autos h0Bucket7 8 h0Block8_34 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_34Mem : ∀ ns ∈ h0Block8_34, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_34Ok
def h0Block8_35Specs : List PoolSpec := [(18,[]),pool9,pool1,pool5,pool12,pool4,pool3,pool6,(14,[]),pool0,pool2,(47,[]),(27,[]),pool15,pool8,(13,[]),pool7,pool11,(3,[]),(4,[]),(12,[]),(9,[]),(9,[(1,0,1)]),(19,[]),(8,[(1,0,1)]),(2,[(1,0,3),(1,1,2),(0,175,263)]),(22,[]),(1,[(2,2,4),(0,3,5),(1,87,131)])]
def h0Block8_35Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_35Specs
def h0Block8_35 : List NodeSpec := [([0,1,2,174,3,184,4,5],[2,3,7,9,12,14,23],[0]),([0,1,2,174,3,203,16,5],[3,6,11,17],[0]),([0,1,2,264,3,4,5],[0,2,5,9,10,25],[]),([0,1,2,111,3,4,5],[4,9,15,19,21,24],[0]),([0,1,2,135,3,4,5],[2,8,9,18,19,20,22],[]),([0,1,2,156,3,4,5],[4,9,13,15,20],[]),([0,1,2,340,4,269,5],[5,9,26],[]),([0,1,2,345,3,4,5],[1,5],[]),([0,1,2,64,4,312,5],[5,6,9],[]),([0,1,2,418,3,4,5],[7,10],[]),([0,1,2,3,148,4,5],[6,10,14,27],[0]),([0,1,2,3,323,4,5],[9,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_35Ok : checkNodesBT h0W h0G h0Mask h0Block8_35Pools h0Autos h0Bucket7 8 h0Block8_35 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_35Mem : ∀ ns ∈ h0Block8_35, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_35Ok
def h0Block8_36Specs : List PoolSpec := [pool13,(18,[]),pool1,pool5,pool4,pool3,pool6,pool0,pool2,pool10,(27,[]),pool7,pool11,(9,[]),(15,[]),(20,[]),(2,[(1,0,3),(1,1,4),(0,263,203)])]
def h0Block8_36Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_36Specs
def h0Block8_36 : List NodeSpec := [([0,1,2,3,430,4,5],[5,8],[]),([0,1,2,3,163,4,312,5],[3,5,9,11,13],[0]),([0,1,2,3,207,4,312,5],[0,2,4,6],[]),([0,1,2,3,252,4,5],[5,8],[]),([0,1,2,3,259,4,5],[5,8],[]),([0,1,2,3,362,4,5],[2,7,11,14],[]),([0,1,2,3,280,4,5],[7,11],[]),([0,1,2,3,270,4,5],[2,3,7,8,12,15,16],[]),([0,1,2,3,279,4,5],[2,9],[]),([0,1,2,3,413,4,92,5],[6,7,8],[]),([0,1,2,3,263,289,4,5],[0,2],[]),([0,1,2,3,414,4,92,5],[1,4,6,9,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_36Ok : checkNodesBT h0W h0G h0Mask h0Block8_36Pools h0Autos h0Bucket7 8 h0Block8_36 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_36Mem : ∀ ns ∈ h0Block8_36, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_36Ok
def h0Block8_37Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,(30,[]),pool4,pool3,pool6,pool0,pool2,(27,[]),(11,[]),(13,[]),pool7,pool11,(17,[]),(2,[(1,0,2),(1,1,3),(1,174,4)]),(1,[(0,2,4),(0,3,5),(1,54,131)])]
def h0Block8_37Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_37Specs
def h0Block8_37 : List NodeSpec := [([0,1,2,3,229,4,92,5],[5,6,10,11],[]),([0,1,2,3,188,4,196,5],[8,10,15,16,17],[0]),([0,1,2,3,320,4,5],[2,6,7],[]),([0,1,2,3,139,4,5],[3,7,9,10,13,18],[0]),([0,1,2,3,65,386,4,5],[7,9,10],[]),([0,1,2,3,4,405,5],[4,14],[]),([0,1,2,3,4,217,5],[0,7,15],[]),([0,1,2,3,4,52,5],[9,12,14],[]),([0,1,2,3,4,277,5],[9,14],[]),([0,1,2,3,4,185,5],[6,7,9],[]),([0,1,2,3,4,267,5],[1,4,9],[]),([0,1,2,3,4,261,5],[10,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_37Ok : checkNodesBT h0W h0G h0Mask h0Block8_37Pools h0Autos h0Bucket7 8 h0Block8_37 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_37Mem : ∀ ns ∈ h0Block8_37, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_37Ok
def h0Block8_38Specs : List PoolSpec := [(18,[]),pool1,pool5,(29,[]),(24,[]),(31,[]),pool4,pool3,pool0,pool2,pool7,(16,[]),pool11,(4,[]),(23,[]),(15,[]),pool22,(17,[]),(32,[]),(2,[(1,0,1),(1,6,114)]),(2,[])]
def h0Block8_38Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_38Specs
def h0Block8_38 : List NodeSpec := [([0,1,2,3,4,310,5],[10,12,15],[]),([0,1,2,3,4,383,5],[9,12],[]),([0,1,2,3,4,312,78],[6,7,8],[]),([0,1,2,3,4,312,347,5],[5,6,7],[]),([0,1,2,3,4,312,348,5],[6,7,18],[]),([0,1,2,3,4,322,5],[7,8,13,20],[]),([0,1,2,3,4,324,5],[7,8,13,20],[]),([0,1,2,3,4,235,5],[9,12],[]),([0,1,2,3,4,293,5],[1,3,12],[]),([0,1,2,3,4,78,61],[7,8,11,16,17],[0,1]),([0,1,2,3,4,78,61,5],[2,4,7,8,11,14,16],[]),([0,1,2,3,4,169,5],[0,1,8,13,19],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_38Ok : checkNodesBT h0W h0G h0Mask h0Block8_38Pools h0Autos h0Bucket7 8 h0Block8_38 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_38Mem : ∀ ns ∈ h0Block8_38, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_38Ok
def h0Block8_39Specs : List PoolSpec := [pool1,pool5,(29,[]),pool3,pool6,(14,[]),pool0,pool2,(13,[]),(16,[]),(3,[]),(4,[]),(12,[]),(10,[]),(0,[]),(1,[]),(2,[]),pool16]
def h0Block8_39Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_39Specs
def h0Block8_39 : List NodeSpec := [([0,1,2,3,4,61,5],[3,5,6,9,10,12],[]),([0,1,2,3,4,120,5],[0,1,4,5,6,7],[0]),([0,1,2,3,4,92,420,5],[4,7],[]),([0,1,2,3,4,316,5],[3,6,11,16],[]),([0,1,2,3,4,335,5],[3,6,17],[]),([0,1,2,3,4,343,5],[3,6,17],[]),([0,1,2,3,130,312,5],[3,6,8],[]),([0,1,2,3,240,312,5],[3,6,14],[]),([0,1,2,3,298,312,5],[3,6,10],[]),([0,1,2,3,298,203,5],[0,2,15],[]),([0,1,2,3,312,103,5],[3,6,14],[]),([0,1,2,3,312,160,5],[3,6,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_39Ok : checkNodesBT h0W h0G h0Mask h0Block8_39Pools h0Autos h0Bucket7 8 h0Block8_39 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_39Mem : ∀ ns ∈ h0Block8_39, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_39Ok
def h0Block8_40Specs : List PoolSpec := [pool1,pool12,pool4,pool3,pool6,pool0,pool2,pool10,(5,[]),pool15,pool7,pool11,(0,[]),(1,[]),pool16]
def h0Block8_40Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_40Specs
def h0Block8_40 : List NodeSpec := [([0,1,2,3,312,92,5],[3,5,12],[]),([0,1,2,3,312,134,5],[0,3,10,14],[]),([0,1,2,3,203,269,5],[3,11,13],[]),([0,1,210,174,3,4,5],[10,11],[]),([0,1,174,3,188,4,92,5],[2,6,7,10],[0]),([0,1,174,3,4,179,5],[0,2,4,11],[]),([0,50,6,2,3,4,5],[0,1,5,8],[]),([0,6,2,155,3,4,5],[0,5,9],[]),([327,1,2,3,4,312,5],[3,5,12],[]),([339,1,2,3,4,312,5],[3,11,12],[]),([346,1,2,3,4,312,5],[7,11,12],[]),([49,1,6,2,3,4,5],[0,1,5,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_40Ok : checkNodesBT h0W h0G h0Mask h0Block8_40Pools h0Autos h0Bucket7 8 h0Block8_40 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_40Mem : ∀ ns ∈ h0Block8_40, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_40Ok
def h0Block8_41Specs : List PoolSpec := [pool13,pool1,pool14,pool12,pool4,pool3,pool0,pool15,pool7,(3,[]),(9,[(1,0,1)]),(8,[(1,0,1)]),(2,[(1,0,1),(0,2,4),(1,0,54)])]
def h0Block8_41Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_41Specs
def h0Block8_41 : List NodeSpec := [([83,1,6,2,3,4,5],[1,2,4,9],[]),([1,6,2,109,3,4,5],[3,6,11],[]),([1,6,2,106,3,4,5],[0,6,10,12],[0]),([1,6,2,154,3,4,5],[3,6,7],[]),([1,6,2,3,4,167,5],[2,4,7],[]),([1,2,109,3,4,312,5],[5,6,9],[]),([1,2,106,3,263,4,5],[0,6,9],[]),([1,2,174,3,222,4,5],[6,8,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_41Ok : checkNodesBT h0W h0G h0Mask h0Block8_41Pools h0Autos h0Bucket7 8 h0Block8_41 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_41Mem : ∀ ns ∈ h0Block8_41, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_41Ok
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14 ++ h0Block8_15 ++ h0Block8_16 ++ h0Block8_17 ++ h0Block8_18 ++ h0Block8_19 ++ h0Block8_20 ++ h0Block8_21 ++ h0Block8_22 ++ h0Block8_23 ++ h0Block8_24 ++ h0Block8_25 ++ h0Block8_26 ++ h0Block8_27 ++ h0Block8_28 ++ h0Block8_29 ++ h0Block8_30 ++ h0Block8_31 ++ h0Block8_32 ++ h0Block8_33 ++ h0Block8_34 ++ h0Block8_35 ++ h0Block8_36 ++ h0Block8_37 ++ h0Block8_38 ++ h0Block8_39 ++ h0Block8_40 ++ h0Block8_41
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block8_0Mem h0Block8_1Mem) h0Block8_2Mem) h0Block8_3Mem) h0Block8_4Mem) h0Block8_5Mem) h0Block8_6Mem) h0Block8_7Mem) h0Block8_8Mem) h0Block8_9Mem) h0Block8_10Mem) h0Block8_11Mem) h0Block8_12Mem) h0Block8_13Mem) h0Block8_14Mem) h0Block8_15Mem) h0Block8_16Mem) h0Block8_17Mem) h0Block8_18Mem) h0Block8_19Mem) h0Block8_20Mem) h0Block8_21Mem) h0Block8_22Mem) h0Block8_23Mem) h0Block8_24Mem) h0Block8_25Mem) h0Block8_26Mem) h0Block8_27Mem) h0Block8_28Mem) h0Block8_29Mem) h0Block8_30Mem) h0Block8_31Mem) h0Block8_32Mem) h0Block8_33Mem) h0Block8_34Mem) h0Block8_35Mem) h0Block8_36Mem) h0Block8_37Mem) h0Block8_38Mem) h0Block8_39Mem) h0Block8_40Mem) h0Block8_41Mem)
def h0Block9_0Specs : List PoolSpec := [pool9,pool1,pool14,pool12,pool4,pool3,pool6,(14,[]),pool0,pool2,pool17,pool10,(11,[]),pool15,pool8,pool7,(16,[]),(3,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(23,[]),(15,[]),pool21,(9,[(1,0,1)]),(0,[(2,6,4)]),(1,[(2,6,4)]),(19,[]),(20,[]),(0,[(2,6,5)]),(10,[]),(2,[(1,0,1),(2,2,4)]),(7,[]),(2,[]),(36,[]),pool20,pool16,(21,[]),(22,[]),(35,[]),(1,[(2,2,4),(3,3,5)])]
def h0Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_0Specs
def h0Block9_0 : List NodeSpec := [([26,0,1,6,2,3,4],[1,3,8,10,18,30,31],[0,1]),([332,0,1,2,3,4,312,5],[5,7,8,12,29,38,39],[0]),([341,0,1,2,3,4,312,5],[5,8,20,23,24,29,38,40],[0]),([349,0,1,2,3,4,312,5],[5,8,18,29,37],[0]),([44,0,1,6,2,3,4,5],[1,2,4,5,13,22,25],[0,1]),([44,0,1,2,3,4,5],[4,5,13,16,19,20,21,25,27,28],[0,1]),([87,89,0,1,2,3,4,5],[0,6,15,19,21,36,41],[0,1]),([87,31,0,1,2,3,4,5],[5,7,11,14,16,35,36,41],[0]),([87,28,0,1,2,3,4,5],[0,6,9,14,32,34,35,42],[0]),([87,291,0,1,2,3,4,5],[0,7,8,15,17,22],[0]),([87,364,0,1,2,3,4,5],[5,6,8,14,18,29],[]),([87,0,1,6,2,3,4,5],[1,5,6,7,8,13,14,22,26,33],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Ok : checkNodesBT h0W h0G h0Mask h0Block9_0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Mem : ∀ ns ∈ h0Block9_0, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_0Ok
def h0Block9_1Specs : List PoolSpec := [pool13,pool9,pool1,(29,[]),pool4,pool3,pool6,(14,[]),pool0,(27,[]),(11,[]),pool8,pool7,(16,[]),pool11,(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(15,[]),(17,[]),(19,[]),(10,[]),(0,[]),(7,[]),(14,[(1,0,2)]),(0,[(2,2,4)]),(0,[(2,174,4)]),(1,[(1,0,2),(2,174,4)]),(2,[(1,0,2),(2,174,4)]),(36,[]),(0,[(2,3,4)]),(1,[(1,0,2),(2,3,4)]),(2,[(1,0,2),(2,3,4)]),(1,[(3,0,2),(2,3,4)]),pool16,(1,[(1,0,4),(2,3,4)]),(8,[(3,0,5)]),(1,[(3,0,5),(2,3,4)]),(35,[]),(0,[(2,2,4),(0,3,5)]),(1,[(2,2,4),(0,3,5)])]
def h0Block9_1Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_1Specs
def h0Block9_1 : List NodeSpec := [([87,0,1,2,131,3,4,5],[5,8,11,16,18,19,41,42],[0]),([87,0,1,2,3,263,4,5],[6,7,8,11,21,22],[0]),([87,0,1,2,3,4,312,5],[5,7,8,10,11,22,24,36],[0]),([87,0,1,174,3,4,5],[10,11,12,14,16,25,26,27],[0]),([198,0,1,2,174,3,4,5],[11,12,13,14,16,25],[]),([198,0,1,2,3,4,5],[5,11,13,14,16,17,18,23,28,29,30],[0]),([89,234,0,1,2,3,4,5],[1,2,5,6,18,25,32,35],[0]),([89,364,0,1,2,3,4,5],[0,2,3,9,15,20,22,32,38,39],[]),([89,0,1,2,174,3,4,5],[0,2,12,13,18,32,33,34],[0,1]),([89,0,1,2,3,4,312,5],[0,2,4,5,17,19,20,22,32,36,37],[0]),([89,0,1,2,3,4,92,5],[1,5,6,9,10,11,16,18,19,31,40],[0]),([285,0,1,2,3,263,4,5],[2,6,17,19],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Ok : checkNodesBT h0W h0G h0Mask h0Block9_1Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Mem : ∀ ns ∈ h0Block9_1, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_1Ok
def h0Block9_2Specs : List PoolSpec := [pool13,(18,[]),pool9,pool1,pool5,pool14,pool12,(29,[]),(30,[]),pool4,pool3,pool6,pool0,pool2,pool17,pool10,(47,[]),(11,[]),pool15,pool8,(13,[]),pool7,(3,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(17,[]),(19,[]),(20,[]),(10,[]),(8,[(1,0,1)]),(2,[(1,0,1),(2,2,3)]),(7,[]),(2,[]),(0,[(2,263,4)]),(1,[(1,0,3),(2,263,4)]),(2,[(1,0,3),(2,263,4)]),(0,[(3,4,5)]),pool20,(1,[(1,0,4),(3,4,5)]),(0,[(1,2,3),(2,65,4)]),(1,[(1,2,3),(2,65,4)]),(0,[(2,2,3)])]
def h0Block9_2Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_2Specs
def h0Block9_2 : List NodeSpec := [([285,0,1,2,3,4,5],[0,3,11,17,24,26,28,31,36,37,38],[0,1]),([69,0,1,2,3,65,4,5],[2,4,11,13,17,24],[0]),([69,0,1,2,3,4,5],[1,2,17,19,24,26,28,31,35,42,43],[0,1]),([31,234,0,1,2,3,4,5],[10,13,15,31,34,35],[0]),([31,291,0,1,2,3,4,5],[10,16,22,28,30,39],[0]),([31,0,1,6,2,3,4,5],[3,4,6,9,10,12,13,14,18,27],[0,1]),([31,0,1,53,2,3,4,5],[4,10,13,15,31,34,35],[0,1]),([31,0,1,2,3,4,312,5],[9,10,27,31,39,40,41],[0]),([104,350,0,1,2,3,4,5],[0,12,25,26,27],[0]),([104,364,0,1,2,3,4,5],[0,12,23,29],[]),([104,0,1,6,2,3,4,5],[4,6,7,8,12,18,20,25,26,32,33],[0]),([104,0,1,2,3,114,4,5],[4,5,11,21,25,26,27,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_2Ok : checkNodesBT h0W h0G h0Mask h0Block9_2Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_2Mem : ∀ ns ∈ h0Block9_2, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_2Ok
def h0Block9_3Specs : List PoolSpec := [pool9,pool5,pool4,pool3,pool6,pool0,pool2,pool10,(47,[]),(27,[]),(11,[]),pool8,(13,[]),pool7,(16,[]),pool11,(3,[]),(4,[]),(12,[]),(8,[]),(9,[]),(15,[]),(17,[]),(19,[]),(20,[]),(10,[]),(1,[]),(7,[]),(2,[]),(0,[(2,174,3)]),(1,[(1,0,2),(2,174,3)]),(2,[(1,0,2),(2,174,3)]),pool16,(22,[]),(0,[(3,3,312)]),(1,[(1,0,4),(3,3,312)]),(2,[(1,0,4),(3,3,312)]),(1,[(1,2,4),(3,3,92)]),(0,[(1,2,4),(3,3,92)])]
def h0Block9_3Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_3Specs
def h0Block9_3 : List NodeSpec := [([104,0,1,2,3,4,312,5],[3,5,12,20,22,23,32],[0]),([180,0,1,2,174,3,4,5],[1,6,10,13,16,29,30,31],[0]),([180,0,1,2,3,4,5],[1,4,10,20,22,24,25,27,29,30],[0]),([108,234,0,1,2,3,4,5],[1,3,15,21,27],[0]),([108,364,0,1,2,3,4,5],[1,11,15,17,23],[]),([108,0,1,2,174,3,4,5],[11,13,14,15,20,27],[0]),([314,0,1,2,3,4,312,5],[2,3,16,18,33],[]),([314,0,1,2,3,4,5],[1,2,3,10,19,22,24,25,27,34,35,36],[0,1]),([98,0,1,2,3,4,92,5],[3,6,7,9,10,19,37],[0]),([98,0,1,2,3,4,5],[1,3,7,10,19,22,23,25,26,27,38],[0]),([28,107,0,1,2,3,4,5],[6,8,14,20,24,25],[0]),([28,234,0,1,2,3,4,5],[0,4,6,25,27,28],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_3Ok : checkNodesBT h0W h0G h0Mask h0Block9_3Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_3Mem : ∀ ns ∈ h0Block9_3, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_3Ok
def h0Block9_4Specs : List PoolSpec := [pool9,pool1,pool12,pool4,pool3,pool6,pool0,pool2,(47,[]),(5,[]),(11,[]),pool15,pool8,(13,[]),(2,[(1,0,1),(2,6,2)]),pool7,(16,[]),(4,[]),(6,[]),(12,[]),(0,[(2,6,2)]),(1,[(2,6,2)]),(8,[]),(9,[]),(15,[]),(19,[]),(20,[]),(10,[]),(1,[(1,2,4)]),(7,[]),(2,[]),(8,[(1,0,2)]),(1,[(1,0,2),(3,3,5)]),(0,[(3,2,263)]),(1,[(1,0,3),(3,2,263)]),pool20,pool16,(1,[(1,0,4),(3,3,5)]),(0,[(3,2,3)]),(1,[(1,0,4),(3,2,3)]),(0,[(3,3,5)]),(1,[(3,0,4),(3,2,3)]),(8,[(3,0,5)]),(1,[(3,0,5),(3,2,3)]),(1,[(0,2,4),(3,3,5)])]
def h0Block9_4Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_4Specs
def h0Block9_4 : List NodeSpec := [([28,350,0,1,2,3,4,5],[5,8,23,26,27,40],[0,1]),([28,0,1,54,2,3,4,5],[0,5,7,27,29,30,44],[0]),([28,0,1,2,174,3,4,5],[5,7,10,12,19,22,25,31,32],[0]),([28,0,1,2,3,4,312,5],[3,4,5,7,22,24,35,36,37,40],[0,1]),([28,0,1,2,3,4,92,5],[5,7,16,19,22,23,28,29],[0]),([41,0,1,6,2,3,4,5],[1,2,6,7,9,10,11,14,15],[0]),([41,0,1,2,3,4,5],[7,11,14,15,16,18,19,20,21,22],[0]),([105,350,0,1,2,3,4,5],[1,4,5,12,22,23,41],[0]),([105,364,0,1,2,3,4,5],[1,7,12,17,25,42,43],[0]),([105,0,1,2,3,4,312,5],[1,3,4,13,16,25,36,38,39],[0]),([275,0,1,2,3,263,4,5],[1,5,19,29],[]),([275,0,1,2,3,4,5],[1,6,16,18,19,26,27,29,33,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_4Ok : checkNodesBT h0W h0G h0Mask h0Block9_4Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_4Mem : ∀ ns ∈ h0Block9_4, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_4Ok
def h0Block9_5Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool12,pool4,pool3,pool6,(14,[]),pool0,pool2,pool17,pool10,(27,[]),(11,[]),pool15,pool7,(7,[(1,0,1)]),(16,[]),pool11,(3,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(19,[]),(20,[]),(10,[]),(0,[]),(2,[(1,0,1),(3,2,4)]),(7,[]),(1,[(3,2,5)]),(2,[]),(0,[(3,2,5)]),(2,[(1,0,3)]),(14,[(1,0,4)]),(21,[]),(0,[(3,2,312)]),(1,[(1,0,4),(3,2,312)]),(2,[(1,0,4),(3,2,312)])]
def h0Block9_5Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_5Specs
def h0Block9_5 : List NodeSpec := [([107,291,0,1,2,3,4,5],[6,8,10,19,20],[0]),([107,364,0,1,2,3,4,5],[0,10,19,21,26],[]),([107,0,1,6,2,3,4,5],[2,5,7,8,10,13,14,15,17,30,31],[0]),([107,0,1,2,131,3,4,5],[5,6,10,14,19,24,31],[0]),([107,0,1,2,3,263,4,5],[0,7,19,22,23],[0]),([107,0,1,2,3,312,5],[5,9,10,22,25,29,36],[0]),([328,0,1,2,3,4,312,5],[5,6,14,22,37,38],[0]),([328,0,1,2,3,4,5],[5,6,9,10,18,22,23,24,27,28,38,39,40],[0]),([70,291,0,1,2,3,4,5],[1,16,20,27,28,33,34],[0,1]),([70,350,0,1,2,3,4,5],[12,16,25,27,28,33,34],[0,1]),([70,0,1,6,2,3,4,5],[2,3,4,9,10,11,15,16,31,32],[0,1]),([70,0,1,2,3,263,4,5],[0,3,14,23,31,34,35],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_5Ok : checkNodesBT h0W h0G h0Mask h0Block9_5Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_5Mem : ∀ ns ∈ h0Block9_5, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_5Ok
def h0Block9_6Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool12,(24,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,pool17,pool10,(27,[]),(5,[]),(11,[]),pool15,pool8,pool7,(7,[(1,0,1)]),(16,[]),pool11,(3,[]),(4,[]),(12,[]),(8,[]),(9,[]),(9,[(1,0,1)]),(19,[]),(20,[]),(10,[]),(0,[]),(7,[]),(1,[(1,0,2)]),(2,[(1,0,2),(3,1,2)]),(2,[(1,0,2),(3,1,174)]),(0,[(3,1,174)]),(0,[(3,1,3)]),(2,[(1,0,2),(3,1,3)]),(1,[(3,0,2)]),pool20,pool16,(0,[(0,2,3),(3,53,5)]),(1,[(0,2,3),(3,53,5)])]
def h0Block9_6Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_6Specs
def h0Block9_6 : List NodeSpec := [([70,0,1,2,3,4,312,5],[0,3,6,7,9,10,11,19,29,33,41,42],[0]),([117,0,1,2,3,4],[26,31,33,43,44],[0,1]),([47,0,1,6,2,3,4,5],[1,2,4,5,12,16,17,20],[0]),([79,0,1,6,2,3,4,5],[2,10,12,13,17,18,28],[0,1]),([90,0,1,6,2,3,4,5],[2,4,10,12,24,29,30],[0]),([177,291,0,1,2,3,4,5],[1,7,10,15,23],[0]),([177,0,1,2,3,263,4,5],[2,3,8,10,15,25,29],[0]),([177,0,1,174,3,4,5],[2,21,22,32,33,34,35],[0]),([35,0,1,2,174,3,4,5],[2,10,11,14,16,22,34,36],[0]),([35,0,1,2,3,4,5],[2,6,10,21,25,26,27,31,34,36,37],[0]),([201,234,0,1,2,3,4,5],[1,7,26,33,38,40],[0]),([201,0,1,2,174,3,4,5],[3,11,16,19,26,34,38,39],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_6Ok : checkNodesBT h0W h0G h0Mask h0Block9_6Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_6Mem : ∀ ns ∈ h0Block9_6, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_6Ok
def h0Block9_7Specs : List PoolSpec := [pool1,pool5,pool4,pool3,pool6,pool0,pool2,pool10,(47,[]),(5,[]),(11,[]),pool8,pool7,(16,[]),pool11,(3,[]),(12,[]),(8,[]),(9,[]),(17,[]),(20,[]),(10,[]),(0,[]),(1,[]),(1,[(1,2,4)]),(7,[]),(1,[(3,0,2)]),(7,[(3,1,5)]),(1,[(1,0,3)]),(0,[(3,1,263)]),(2,[(1,0,3),(3,1,263)]),(1,[(1,0,4)]),(2,[(1,0,4),(3,1,4)]),pool23,(9,[(3,1,312)]),(0,[(3,1,312)]),(2,[(1,2,4),(3,1,92)])]
def h0Block9_7Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_7Specs
def h0Block9_7 : List NodeSpec := [([266,0,1,2,3,263,4,5],[0,5,19,28],[]),([266,0,1,2,3,4,5],[0,1,2,5,9,10,18,19,21,23,29,30],[0]),([205,234,0,1,2,3,4,5],[4,7,14,18,25],[0]),([205,291,0,1,2,3,4,5],[0,8,12,15,18],[0]),([205,0,1,2,174,3,4,5],[11,12,13,14,18,25],[0]),([205,0,1,2,3,263,4,5],[0,1,4,18,19],[0]),([205,0,1,2,3,312,5],[0,2,5,18,22,31,32],[0]),([74,0,1,2,3,4,312,5],[0,2,5,22,31,33],[0,1]),([74,0,1,2,3,4,5],[0,5,9,10,16,17,21,31,33,34,35],[0,1]),([208,0,1,2,3,4,92,5],[4,6,7,10,24],[0]),([208,0,1,2,3,4,5],[0,2,4,7,9,13,16,17,21,22,24,36],[0,1]),([187,234,0,1,2,3,4,5],[0,3,4,6,14,20,21,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_7Ok : checkNodesBT h0W h0G h0Mask h0Block9_7Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_7Mem : ∀ ns ∈ h0Block9_7, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_7Ok
def h0Block9_8Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(27,[]),pool8,pool7,pool11,(12,[]),(8,[]),(9,[]),(15,[]),(20,[]),(10,[]),(1,[]),pool18,(7,[]),(0,[(1,1,2)]),(1,[(1,0,2)]),(0,[(1,3,4)]),(2,[(3,0,2),(1,1,2)]),(1,[(3,0,2),(1,3,4)]),(2,[(3,0,2),(1,3,4)]),(10,[(3,0,3)]),(25,[]),pool16]
def h0Block9_8Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_8Specs
def h0Block9_8 : List NodeSpec := [([187,291,0,1,2,3,4,5],[2,5,6,9,10,14,20,31,32],[0]),([187,350,0,1,2,3,4,5],[0,5,13,18,20,21],[]),([187,0,1,2,174,3,4,5],[2,3,10,12,13,20,21,26],[0]),([187,0,1,2,3,263,4,5],[0,2,4,20,21],[0]),([187,0,1,2,3,4,312,5],[3,5,6,8,9,10,19,20,33],[0]),([234,0,1,2,88,3,4,5],[1,15,17,24],[0]),([234,0,1,2,131,3,4,5],[6,9,10,17,24],[0]),([234,0,1,2,3,114,4,5],[7,10,15,18,24],[0]),([234,0,1,2,3,4,203,5],[6,15,20,24],[0]),([234,0,1,2,3,4,16,5],[3,6,7,10,16,24,27,29,30],[0]),([234,0,1,175,3,4,5],[2,9,10,15,22,24,25,28],[0]),([234,0,1,3,4,92,5],[6,7,10,11,15,18,23,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_8Ok : checkNodesBT h0W h0G h0Mask h0Block9_8Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_8Mem : ∀ ns ∈ h0Block9_8, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_8Ok
def h0Block9_9Specs : List PoolSpec := [pool13,pool9,pool1,pool4,pool3,pool6,pool0,pool2,pool10,(47,[]),(11,[]),pool8,pool7,pool11,(3,[]),(4,[]),(8,[]),(9,[]),(23,[]),(17,[]),(20,[]),(0,[]),pool18,(7,[]),(10,[(3,0,3)]),(1,[(3,0,3),(1,2,4)]),(2,[(3,0,3),(1,2,4)]),(0,[(1,2,3)]),(0,[(0,3,5)]),(2,[(3,0,4)]),(1,[(3,0,4),(1,2,3)]),(10,[(3,0,4)]),(1,[(3,0,4),(0,3,5)])]
def h0Block9_9Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_9Specs
def h0Block9_9 : List NodeSpec := [([291,0,1,54,2,3,4,5],[6,9,14,17],[0]),([291,0,1,153,2,3,4,5],[4,6,16,24],[0]),([291,0,1,2,3,114,4,5],[12,13,16,24],[0]),([291,0,1,2,3,4,203,5],[2,4,13,14,17,20],[0]),([291,0,1,2,3,4,92,5],[2,4,7,10,14,18,22,25,26],[0,1]),([381,0,1,2,3,65,4,5],[4,7,10,21],[]),([381,0,1,2,3,4,5],[1,4,7,10,13,15,17,19,20,27],[0]),([350,0,1,53,2,3,4,5],[6,9,16,17,29],[0]),([350,0,1,153,2,3,4,5],[0,6,17,23],[0]),([350,0,1,2,131,3,4,5],[2,3,12,17,28,31,32],[0]),([350,0,1,2,3,65,4,5],[3,5,10,11,17,27,30],[0,1]),([350,0,1,2,3,92,5],[5,6,7,8,12,17,22,23],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_9Ok : checkNodesBT h0W h0G h0Mask h0Block9_9Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_9Mem : ∀ ns ∈ h0Block9_9, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_9Ok
def h0Block9_10Specs : List PoolSpec := [pool13,pool5,pool14,pool12,(29,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,pool10,(47,[]),(27,[]),(11,[]),pool8,(13,[]),pool7,pool11,(3,[]),(4,[]),(6,[]),(12,[]),(9,[]),(17,[]),(19,[]),(10,[]),(1,[]),pool18,(7,[]),(0,[(2,2,4)]),(0,[(1,3,4)]),(0,[(3,4,5)]),(10,[(0,2,3)]),(8,[(3,0,5)]),(1,[(3,0,5),(1,2,4)]),(2,[(1,2,4)]),(0,[(2,2,3)]),(2,[(1,2,4),(3,0,92)]),(1,[(1,2,4),(3,0,92)]),(0,[(3,2,4)]),(1,[(3,2,4),(1,107,0)]),(1,[(3,4,5),(1,31,0)]),(2,[(1,31,0)])]
def h0Block9_10Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_10Specs
def h0Block9_10 : List NodeSpec := [([326,0,1,2,3,4,92,5],[7,10,14,21,28],[0]),([326,0,1,2,3,4,5],[7,10,14,18,19,20,21,22,28,38,39],[0,1]),([364,0,1,53,2,3,4,5],[3,4,9,12,25,33,34],[0]),([364,0,1,54,2,3,4,5],[0,9,20,25],[0]),([364,0,1,2,88,3,4,5],[15,18,25,26,34],[]),([364,0,1,2,3,65,4,5],[1,10,15,20,25],[]),([364,0,1,2,3,4,92,5],[0,7,10,13,15,20,25,34,35,36],[0,1]),([364,0,1,2,3,4,16,5],[0,1,2,4,10,17,20,25,31],[]),([0,327,1,2,3,4,5],[8,9,14,15,17,18,19,20,22,27,29,30],[0,1]),([0,346,1,2,3,4,5],[10,11,12,14,18,19,24,29,32,42,43],[0]),([0,395,1,2,3,4,5],[9,16,17,18,20,23,24,27,29,37],[0,1]),([0,425,1,2,3,4,5],[5,6,8,10,14,19,20,22,23,40,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_10Ok : checkNodesBT h0W h0G h0Mask h0Block9_10Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_10Mem : ∀ ns ∈ h0Block9_10, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_10Ok
def h0Block9_11Specs : List PoolSpec := [pool9,pool1,pool5,pool14,pool12,pool4,pool3,pool6,(14,[]),pool0,pool2,(2,[(1,0,1),(0,6,2)]),pool17,(5,[]),(11,[]),pool15,pool8,(13,[]),pool7,(16,[]),pool11,(3,[]),(12,[]),(8,[]),(2,[(1,0,1),(0,6,4)]),(9,[]),(17,[]),(19,[]),(0,[(0,6,5)]),(1,[(0,6,5)]),(10,[]),(0,[]),(1,[]),(7,[]),(1,[(3,2,5)]),(1,[(3,0,2)]),(2,[(3,0,2),(1,234,1)]),(0,[(1,234,1)]),(0,[(3,2,5)]),(0,[(1,291,1)]),(2,[(3,0,3),(1,291,1)]),(0,[(1,350,1)]),(2,[(3,0,4),(1,350,1)]),(1,[(3,0,5)]),(1,[(2,2,3)]),(0,[(2,2,3),(1,104,1)]),(1,[(2,2,4)]),(0,[(2,2,4),(1,87,1)]),(1,[(3,2,4)]),(0,[(3,2,4),(1,107,1)])]
def h0Block9_11Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_11Specs
def h0Block9_11 : List NodeSpec := [([0,441,1,2,3,4,5],[0,8,19,20,21,22,25,30,32,38],[0,1]),([0,1,209,2,3,4,5],[8,9,14,16,18,22,23,30,33,46,47],[0,1]),([0,1,399,2,3,4,5],[9,13,17,18,25,26,30,44,45],[0,1]),([0,1,330,2,3,4,5],[6,8,14,20,22,23,25,30,48,49],[0]),([0,1,444,2,3,4,5],[0,2,5,8,19,22,23,25,30,31,34],[0]),([0,1,50,2,3,4,5],[1,5,9,10,13,22,23,25,30,35,36,37],[0]),([0,1,292,2,3,4,5],[5,9,13,14,23,25,30,39,40],[0]),([0,1,84,2,3,4,5],[1,9,13,14,22,23,25,30,41,42],[0]),([0,1,365,2,3,4,5],[1,2,5,9,13,14,22,23,25,27,43],[0]),([0,1,7,6,2,3,4,5],[1,4,6,7,9,11,13,14,15],[0]),([0,1,58,6,2,3,4,5],[1,3,5,7,15,16,18,24,25],[0,1]),([0,1,11,6,2,3,4],[1,4,9,12,15,28,29],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_11Ok : checkNodesBT h0W h0G h0Mask h0Block9_11Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_11Mem : ∀ ns ∈ h0Block9_11, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_11Ok
def h0Block9_12Specs : List PoolSpec := [pool13,pool1,pool5,pool14,pool12,(29,[]),(24,[]),(30,[]),pool4,pool3,pool6,pool0,pool2,pool17,(5,[]),(11,[]),pool15,pool8,(13,[]),(2,[(1,0,1),(1,6,2)]),pool7,(7,[(1,0,1)]),(8,[]),(9,[]),(23,[]),pool22,(9,[(1,0,1)]),(0,[(0,6,5)]),(1,[(0,6,5)]),(2,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,2,4)]),(10,[]),(8,[(1,0,1)]),(2,[(1,0,1),(0,2,3)]),(0,[]),(1,[]),(2,[(1,0,1),(0,2,4)]),pool18,(1,[(1,2,4)]),(7,[]),(2,[]),pool20,pool16,(10,[(0,2,3)]),(0,[(0,2,3),(0,4,5)]),(1,[(0,2,3),(0,4,5)])]
def h0Block9_12Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_12Specs
def h0Block9_12 : List NodeSpec := [([0,1,11,6,2,3,4,5],[1,2,4,6,11,12,13,16,17,24],[0,1]),([0,1,11,2,3,4],[27,28,31],[0,1]),([0,1,6,53,2,3,4,5],[4,5,7,11,13,16,21,32,33,34,35],[0,1]),([0,1,6,54,2,3,4,5],[0,1,9,11,16,21,26,34,36],[0]),([0,1,6,153,2,3,4,5],[1,2,4,7,9,11,13,16,34,35],[0,1]),([0,1,6,2,18,3,4,5],[1,3,4,12,13,14,15,16,19],[0]),([0,1,6,2,3,65,4,5],[1,2,4,9,10,11,12,15,16,29],[0]),([0,1,6,2,3,114,4,5],[1,2,3,8,10,12,13,16,20,34,35],[0,1]),([0,1,6,2,3,4,61,5],[1,4,11,13,16,23,25],[0,1]),([0,1,6,2,3,4,92,5],[1,8,9,10,11,12,15,16,30,37,38],[0,1]),([0,1,53,2,3,114,4,5],[1,3,4,8,10,22,39,40,43,44,45],[0,1]),([0,1,53,2,3,4,312,5],[9,11,18,23,34,39,41,42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_12Ok : checkNodesBT h0W h0G h0Mask h0Block9_12Pools h0Autos h0Bucket8 9 h0Block9_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_12Mem : ∀ ns ∈ h0Block9_12, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_12Ok
def h0Block9_13Specs : List PoolSpec := [pool13,pool1,pool5,pool14,pool12,pool4,pool3,pool6,(14,[]),pool0,pool2,(27,[]),(11,[]),pool8,(13,[]),pool7,(16,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(17,[]),(19,[]),(20,[]),(10,[]),(0,[]),(1,[]),(7,[]),(2,[]),(1,[(1,0,2),(0,174,3)]),(0,[(0,174,3)]),(2,[(1,0,2),(0,174,3)]),(0,[(1,291,2)]),(1,[(3,0,3),(1,291,2)]),pool16,(6,[(1,0,4)]),(0,[(1,350,2)]),(1,[(3,0,4),(1,350,2)]),(0,[(0,2,3)]),(2,[(0,2,3),(1,0,53)]),(10,[(0,2,4)]),(0,[(0,2,4),(0,3,5)]),(1,[(0,2,4),(0,3,5)]),(0,[(3,4,5),(1,31,2)]),(1,[(3,4,5),(1,31,2)])]
def h0Block9_13Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_13Specs
def h0Block9_13 : List NodeSpec := [([0,1,274,2,3,263,4,5],[1,2,7,12,19,23],[]),([0,1,54,2,131,3,4,5],[1,3,5,6,21,28,41,42,43],[0]),([0,1,54,2,3,263,4,5],[0,9,19,26,28],[0]),([0,1,329,2,3,4,312,5],[5,6,12,23,26,35,36],[0]),([0,1,153,2,3,263,4,5],[0,9,19,20,28],[0]),([0,1,153,2,3,4,312,5],[6,9,21,35],[0]),([0,1,2,33,3,4,5],[6,8,15,18,20,22,29,44,45],[0]),([0,1,2,295,3,4,5],[6,13,14,16,18,20,25,33,34],[0]),([0,1,2,351,3,4,5],[7,8,10,11,16,19,20,21,25,37,38],[0]),([0,1,2,367,3,4,5],[9,15,17,18,19,20,23,27],[0,1]),([0,1,2,211,174,3,4,5],[1,10,12,15,19,30,31,32],[0]),([0,1,2,109,3,4,5],[1,4,9,17,20,21,24,28,39,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_13Ok : checkNodesBT h0W h0G h0Mask h0Block9_13Pools h0Autos h0Bucket8 9 h0Block9_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_13Mem : ∀ ns ∈ h0Block9_13, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_13Ok
def h0Block9_14Specs : List PoolSpec := [pool1,pool5,pool4,pool3,pool6,pool0,pool2,(27,[]),(11,[]),pool8,pool7,(16,[]),pool11,(3,[]),(4,[]),(12,[]),(8,[]),(9,[]),(19,[]),(20,[]),(10,[]),(0,[]),(1,[]),(7,[]),(2,[]),(17,[(1,0,2)]),(2,[(1,0,2),(1,1,3)]),(2,[(1,0,2),(1,1,4)]),(1,[(1,0,2),(0,174,5)]),(0,[(1,3,4)]),(1,[(1,0,2),(1,3,4)]),(2,[(1,0,2),(1,3,4)]),(1,[(1,0,2),(0,3,5)]),(10,[(1,0,2)]),(0,[(0,2,4)]),(2,[(0,2,4),(1,0,54)]),(1,[(0,2,4)]),(2,[(0,2,4),(1,1,54)]),(2,[(1,0,153)]),(0,[(0,2,5)]),(2,[(1,1,153)]),(1,[(0,2,5)])]
def h0Block9_14Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_14Specs
def h0Block9_14 : List NodeSpec := [([0,1,2,218,174,3,4,5],[9,10,11,12,23],[0]),([0,1,2,106,3,4,5],[2,5,13,14,15,17,19,23,34,35],[0]),([0,1,2,181,174,3,4,5],[1,6,7,8,9,24,28],[0]),([0,1,2,154,3,4,5],[5,6,12,13,15,17,22,23,38,39],[0,1]),([0,1,2,174,88,3,4,5],[7,9,11,12,16,21,23],[0]),([0,1,2,174,131,3,4,5],[0,6,8,10,16,23,32],[0]),([0,1,2,174,3,188,4,5],[1,2,4,5,6,8,10,15,16,25,26],[0,1]),([0,1,2,174,3,114,4,5],[8,10,12,17,23,33],[0]),([0,1,2,174,3,4,203,5],[0,3,9,10,11,12,23,27],[0,1]),([0,1,2,174,3,4,16,5],[1,9,10,11,15,16,17,29,30,31],[0,1]),([0,1,2,407,3,4,5],[0,5,15,16,17,18,20,23,36,37],[0,1]),([0,1,2,155,3,4,5],[0,1,5,15,16,17,21,23,40,41],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_14Ok : checkNodesBT h0W h0G h0Mask h0Block9_14Pools h0Autos h0Bucket8 9 h0Block9_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_14Mem : ∀ ns ∈ h0Block9_14, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_14Ok
def h0Block9_15Specs : List PoolSpec := [pool1,pool5,pool4,pool3,pool6,(14,[]),pool0,pool2,pool17,pool10,(27,[]),(11,[]),pool8,(13,[]),(2,[(1,0,1),(1,6,2)]),pool7,(16,[]),pool11,(3,[]),(4,[]),(6,[]),(12,[]),(0,[(1,6,2)]),(1,[(1,6,2)]),(8,[]),(9,[]),(15,[]),(17,[]),(19,[]),(20,[]),(10,[]),(1,[]),(7,[]),(2,[]),(0,[(1,234,3)]),(2,[(1,0,3),(1,1,2)]),pool16,(0,[(0,3,5)]),(1,[(1,0,4),(0,3,5)]),(0,[(1,350,3)]),(1,[(1,2,4),(0,3,92)]),(1,[(1,2,4),(0,3,5)]),(0,[(2,2,4),(1,87,3)]),(1,[(2,2,4),(1,87,3)]),(7,[(1,107,3)]),(0,[(3,2,4),(1,107,3)]),(0,[(3,2,5),(1,70,3)]),(1,[(3,2,5),(1,70,3)])]
def h0Block9_15Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_15Specs
def h0Block9_15 : List NodeSpec := [([0,1,2,175,3,263,4,5],[0,2,6,7,11,21,35],[0]),([0,1,2,18,3,4,5],[0,7,8,14,15,16,17,18,19,20,21,22,23],[0]),([0,1,2,340,3,4,312,5],[2,3,18,21,28,36],[0]),([0,1,2,142,3,4,92,5],[3,7,9,10,11,21,40],[0]),([0,1,2,131,3,4,312,5],[0,2,3,25,36,37,38],[0]),([0,1,2,131,3,4,92,5],[0,3,7,11,24,30,33,41],[0]),([0,1,2,3,146,4,5],[3,12,13,24,27,30,32,42,43],[0]),([0,1,2,3,152,4,5],[1,5,11,25,27,30,31,44,45],[0,1]),([0,1,2,3,163,4,5],[4,10,11,13,21,25,32,46,47],[0,1]),([0,1,2,3,237,4,5],[1,3,4,7,25,27,29,30,32,34],[0]),([0,1,2,3,353,4,5],[1,4,11,15,25,26,27,30,31,32,39],[0,1]),([0,1,2,3,370,4,5],[1,4,11,19,25,28,31,32],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_15Ok : checkNodesBT h0W h0G h0Mask h0Block9_15Pools h0Autos h0Bucket8 9 h0Block9_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_15Mem : ∀ ns ∈ h0Block9_15, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_15Ok
def h0Block9_16Specs : List PoolSpec := [pool13,pool9,pool1,pool5,pool14,pool4,pool3,pool6,pool0,pool2,(11,[]),(13,[]),(16,[]),pool11,(6,[]),(12,[]),(8,[]),(9,[]),(17,[]),(10,[]),(1,[]),pool18,(7,[]),(2,[]),(2,[(1,0,3),(1,1,4)]),(1,[(1,0,3),(1,2,4)]),(2,[(1,0,3),(1,2,4)]),(10,[(1,0,3)]),pool16,(0,[(1,2,3)]),(1,[(1,0,4),(1,2,3)]),(2,[(1,0,4),(1,2,3)]),(0,[(2,2,3),(1,104,3)]),(0,[(0,2,4),(1,54,3)]),(0,[(0,2,5),(1,153,3)]),(1,[(0,2,5),(1,153,3)])]
def h0Block9_16Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_16Specs
def h0Block9_16 : List NodeSpec := [([0,1,2,3,284,263,4,5],[2,7,18],[0]),([0,1,2,3,288,263,4,5],[0,2,4,15,23],[0]),([0,1,2,3,263,114,4,5],[7,13,15,16,27],[0]),([0,1,2,3,263,4,203,5],[2,3,8,13,15,17,24],[0]),([0,1,2,3,263,4,92,5],[2,7,9,10,18,21,25,26],[0,1]),([0,1,2,3,125,65,4,5],[1,3,7,9,10],[0,1]),([0,1,2,3,138,4,5],[3,11,17,18,19,20,22,33],[0,1]),([0,1,2,3,393,65,4,5],[3,6,9,10,23],[]),([0,1,2,3,158,4,5],[6,7,17,18,19,22,34,35],[0,1]),([0,1,2,3,65,114,4,5],[3,7,9,10,17,19,23],[0]),([0,1,2,3,65,4,312,5],[5,6,9,12,28,29,30,31],[0]),([0,1,2,3,65,4,5],[3,6,7,11,12,14,19,20,22,32],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_16Ok : checkNodesBT h0W h0G h0Mask h0Block9_16Pools h0Autos h0Bucket8 9 h0Block9_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_16Mem : ∀ ns ∈ h0Block9_16, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_16Ok
def h0Block9_17Specs : List PoolSpec := [pool13,pool5,(29,[]),pool4,pool3,pool6,(14,[]),pool0,pool2,(11,[]),pool7,(16,[]),pool11,(3,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),(23,[]),(15,[]),(17,[]),(19,[]),(20,[]),(10,[]),(1,[]),pool18,(7,[]),(2,[]),(0,[(1,174,3)]),(0,[(1,234,4)]),(0,[(1,291,4)]),(0,[(1,1,4)]),(1,[(1,0,4)]),pool20,pool16,(1,[(1,0,4),(1,2,4)]),(2,[(1,0,4),(1,2,4)]),(2,[(1,0,4),(1,2,312)]),(1,[(2,2,3),(1,104,4)]),(0,[(2,2,3),(1,104,4)]),(0,[(3,2,5),(1,70,4)]),(1,[(3,2,5),(1,70,4)]),(2,[(1,0,114)]),(0,[(0,4,5)])]
def h0Block9_17Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_17Specs
def h0Block9_17 : List NodeSpec := [([0,1,2,3,213,4,5],[1,8,11,12,14,15,16,23,29],[0]),([0,1,2,3,4,130,5],[0,4,6,17,21,24,27,39,40],[0,1]),([0,1,2,3,4,72,5],[4,6,10,15,17,21,28,41,42],[0]),([0,1,2,3,4,240,5],[4,5,6,8,12,17,21,24,25,27,30],[0]),([0,1,2,3,4,298,5],[2,10,11,12,15,17,20,24,25,31],[0,1]),([0,1,2,3,4,373,5],[0,4,11,15,16,17,22,25],[0]),([0,1,2,3,4,318,312,5],[3,4,8,11,19,21,34],[0]),([0,1,2,3,4,167,5],[3,7,8,9,13,16,18,25,27,43,44],[0]),([0,1,2,3,4,312,203,5],[3,4,12,18,25,32],[0,1]),([0,1,2,3,4,312,61,5],[3,4,7,33,34,35],[0,1]),([0,1,2,3,4,312,92,5],[3,4,11,15,18,26,35,36,37],[0]),([0,1,2,3,4,312,196,5],[4,7,11,15,35,38],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_17Ok : checkNodesBT h0W h0G h0Mask h0Block9_17Pools h0Autos h0Bucket8 9 h0Block9_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_17Mem : ∀ ns ∈ h0Block9_17, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_17Ok
def h0Block9_18Specs : List PoolSpec := [pool13,(18,[]),pool5,pool4,pool3,pool6,(14,[]),pool0,pool2,pool17,pool10,(27,[]),(5,[]),(11,[]),pool8,pool7,(16,[]),pool11,(3,[]),(4,[]),(6,[]),(12,[]),(8,[]),(9,[]),pool22,(17,[]),(0,[(1,6,4)]),(1,[(1,6,4)]),(20,[]),(10,[]),(0,[]),(1,[]),(1,[(1,2,4)]),(7,[]),(2,[]),(2,[(1,0,2),(1,174,4)]),(0,[(1,174,4)]),(0,[(1,3,4)]),(36,[]),(2,[(1,0,3),(1,263,4)]),(0,[(1,263,4)]),pool16,(2,[(1,0,4),(1,3,4)]),(1,[(1,0,4),(1,3,4)]),(2,[(1,0,4),(1,3,312)]),(0,[(0,2,3),(1,53,4)]),(1,[(0,2,3),(1,53,4)]),(35,[]),(1,[(2,2,4),(1,87,4)]),(2,[(1,153,4)]),(0,[(0,2,5),(1,153,4)]),(1,[(0,2,5),(1,153,4)]),(2,[(1,2,114)]),(0,[(0,4,5),(1,2,114)]),(1,[(0,4,5),(1,2,114)])]
def h0Block9_18Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_18Specs
def h0Block9_18 : List NodeSpec := [([0,1,2,3,4,312,16,5],[3,4,22,23,25,37,41,42,43],[0]),([0,1,2,3,4,312,269,5],[4,7,18,25,41,44],[0]),([0,1,2,3,4,61,5],[3,4,7,9,12,13,18,19,21,24,26,27],[0,1]),([0,1,2,3,4,103,5],[4,10,22,28,29,33,45,46],[0,1]),([0,1,2,3,4,419,92,5],[5,8,13,32,34],[0]),([0,1,2,3,4,121,5],[5,11,16,21,22,23,52,53,54],[0,1]),([0,1,2,3,4,160,5],[4,5,21,22,33,49,50,51],[0,1]),([0,1,2,3,4,92,16,5],[4,5,10,13,14,15,20,21,22,38,47],[0]),([0,1,2,3,4,92,5],[5,6,8,11,16,21,22,23,29,30,33,48],[0]),([0,1,2,3,4,196,5],[4,8,16,17,18,19,21,31,35,36],[0]),([0,1,2,3,4,269,5],[0,1,7,13,19,20,25,31,39,40],[0,1]),([0,1,2,3,4,94,5],[2,4,5,8,16,21,29,30,31,34],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_18Ok : checkNodesBT h0W h0G h0Mask h0Block9_18Pools h0Autos h0Bucket8 9 h0Block9_18 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_18Mem : ∀ ns ∈ h0Block9_18, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_18Ok
def h0Block9_19Specs : List PoolSpec := [pool1,pool4,pool3,pool0,pool2,pool7,(16,[]),pool11,(6,[]),(9,[]),pool18,(7,[]),(0,[(1,1,2)]),(1,[(1,0,2)]),(2,[(1,0,2),(1,1,2)]),(2,[(1,0,2),(1,2,4)]),(0,[(1,1,4)]),(1,[(1,0,4)]),(2,[(1,0,4),(1,1,4)]),(2,[(1,0,4),(1,2,4)]),(6,[(1,0,4)])]
def h0Block9_19Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block9_19Specs
def h0Block9_19 : List NodeSpec := [([0,1,2,3,312,203,5],[1,2,7,9,16,17,18],[0,1]),([0,1,2,3,312,92,5],[2,3,4,8,9,10,19,20],[0,1]),([0,1,174,175,3,4,5],[0,4,5,6,7,12,13,14],[0]),([0,1,174,3,4,92,5],[4,5,6,7,8,10,11,15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_19Ok : checkNodesBT h0W h0G h0Mask h0Block9_19Pools h0Autos h0Bucket8 9 h0Block9_19 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_19Mem : ∀ ns ∈ h0Block9_19, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_19Ok
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7 ++ h0Block9_8 ++ h0Block9_9 ++ h0Block9_10 ++ h0Block9_11 ++ h0Block9_12 ++ h0Block9_13 ++ h0Block9_14 ++ h0Block9_15 ++ h0Block9_16 ++ h0Block9_17 ++ h0Block9_18 ++ h0Block9_19
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block9_0Mem h0Block9_1Mem) h0Block9_2Mem) h0Block9_3Mem) h0Block9_4Mem) h0Block9_5Mem) h0Block9_6Mem) h0Block9_7Mem) h0Block9_8Mem) h0Block9_9Mem) h0Block9_10Mem) h0Block9_11Mem) h0Block9_12Mem) h0Block9_13Mem) h0Block9_14Mem) h0Block9_15Mem) h0Block9_16Mem) h0Block9_17Mem) h0Block9_18Mem) h0Block9_19Mem)
def h0Block10_0Specs : List PoolSpec := [pool17,(11,[]),(16,[]),(8,[]),(9,[]),(17,[]),(10,[]),(0,[]),(1,[]),(7,[]),(1,[(3,2,5)]),(2,[]),(0,[(2,2,4)]),(1,[(3,0,2)]),(2,[(3,0,2)]),(0,[(3,2,5)]),(0,[(3,4,5)]),(1,[(3,0,3)]),(2,[(3,0,3)]),(2,[(3,0,4)]),(1,[(3,0,4)]),(1,[(3,0,5)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(2,[(0,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(2,[(2,2,3)]),(0,[(0,2,4)]),(1,[(0,2,4)]),(2,[(0,2,4)]),(1,[(2,2,4)]),(2,[(2,2,4)]),(0,[(3,2,4)]),(1,[(3,2,4)]),(2,[(3,2,4)]),(1,[(3,4,5)])]
def h0Block10_0Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_0Specs
def h0Block10_0 : List NodeSpec := [([87,0,1,2,3,4,5],[3,4,6,9,12,31,32],[0,1]),([31,0,1,2,3,4,5],[2,3,4,5,6,9,11,16,36],[0,1]),([104,0,1,2,3,4,5],[3,4,5,6,9,25,26,27],[0,1]),([107,0,1,2,3,4,5],[1,3,4,6,9,33,34,35],[0,1]),([70,0,1,2,3,4,5],[1,3,4,6,9,10,11,15],[0,1]),([234,0,1,2,3,4,5],[3,4,6,7,9,13,14],[0,1]),([291,0,1,2,3,4,5],[3,4,6,7,9,17,18],[0,1]),([350,0,1,2,3,4,5],[3,4,6,7,9,19,20],[0,1]),([364,0,1,2,3,4,5],[3,4,6,7,9,11,21],[0,1]),([0,1,6,2,3,4,5],[0,3,4,6,7,8,9,11],[0,1]),([0,1,53,2,3,4,5],[3,4,6,9,11,22,23,24],[0,1]),([0,1,54,2,3,4,5],[3,4,6,9,28,29,30],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Ok : checkNodesBT h0W h0G h0Mask h0Block10_0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Mem : ∀ ns ∈ h0Block10_0, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_0Ok
def h0Block10_1Specs : List PoolSpec := [(16,[]),(12,[]),(8,[]),(9,[]),(17,[]),(10,[]),(0,[]),pool18,(1,[(1,2,4)]),(7,[]),(2,[]),(1,[(1,0,2)]),(2,[(1,0,2)]),(1,[(1,0,3)]),(2,[(1,0,3)]),(1,[(1,0,4)]),pool20,(0,[(1,2,3)]),(2,[(1,2,4)]),(1,[(1,2,3)]),(2,[(1,2,3)]),(0,[(0,2,5)]),(1,[(0,2,5)]),(0,[(0,4,5)]),(1,[(0,4,5)])]
def h0Block10_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block10_1Specs
def h0Block10_1 : List NodeSpec := [([0,1,153,2,3,4,5],[2,3,9,10,21,22],[0,1]),([0,1,2,174,3,4,5],[0,2,3,5,6,9,11,12],[0]),([0,1,2,3,263,4,5],[2,3,4,5,6,9,13,14],[0,1]),([0,1,2,3,65,4,5],[0,1,2,3,5,9,17,19,20],[0,1]),([0,1,2,3,114,4,5],[2,3,9,10,23,24],[0,1]),([0,1,2,3,4,312,5],[2,3,5,6,9,15,16],[0,1]),([0,1,2,3,4,92,5],[0,2,3,5,7,8,9,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Ok : checkNodesBT h0W h0G h0Mask h0Block10_1Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Mem : ∀ ns ∈ h0Block10_1, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_1Ok
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_of_mem (forall_append h0Block10_0Mem h0Block10_1Mem)
def h0Block11_0Specs : List PoolSpec := [(0,[]),(1,[]),(2,[])]
def h0Block11_0Pools : BT (Option BoundPool) := buildPoolsBT 2 h0W h0R h0Slices h0Block11_0Specs
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Ok : checkNodesBT h0W h0G h0Mask h0Block11_0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Mem : ∀ ns ∈ h0Block11_0, Impossible h0G 11 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket10Ok h0Block11_0Ok
def h0Nodes11 : List NodeSpec := h0Block11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_of_mem h0Block11_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lifted : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22),(VAR 5,5,37)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)) 12 := lifted
end PEqualNP.Outside.L_meta_46856
theorem PEqualNP.Outside.L_meta_46856 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_46856.table2_of_lower (4277071592 * 2 ^ 32 + 4207470728) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_46856.low_root
    PEqualNP.Outside.L_meta_46856.wit PEqualNP.Outside.L_meta_46856.wo (by decide)
    PEqualNP.Outside.L_meta_46856.wit_mono PEqualNP.Outside.L_meta_46856.wit_eval s hcs
