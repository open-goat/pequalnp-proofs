import PEqualNP.Defs

/-!
# Truth tables as numbers, monotone tables built from two halves, and a checker for relabelling

Helper of `L-meta-8613` (the five-input assembly). Everything here is general except the
checker `chk`, which is for five inputs.

* `idx x`: the position of `x` in a truth table, `∑ i, if x i then 2 ^ i else 0`.
* `tableNat n f`: the truth table of `f` as a number, built from the half with the last input
  `false` (low bits) and the half with it `true` (high bits). `testBit_table`: bit `idx x` of it
  is `f x`.
* `monoTables n`: the list of tables of monotone functions on `n` inputs, built as ordered pairs
  of monotone tables on `n - 1` inputs. `mono_mem`: the table of a monotone function is in it.
* `chk ts ws`: for each table `t` of `ts`, the matching entry `(c, d, T)` of `ws` names a
  permutation `σ` of five inputs (code `c`), its inverse (code `d`) and a table `T` of `reps`
  with `T` the table of `x ↦ f (x ∘ σ)`. `chk_sound` turns `chk ts ws = true` into `Good t`.
-/

namespace PEqualNP.MetaComplexity.Mono5

/-- The position of the input `x` in a truth table. -/
def idx {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0

theorem idx_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    idx x = 2 ^ n * (if x (Fin.last n) then 1 else 0) + idx (Fin.init x) := by
  unfold idx
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.init, Fin.val_last]
  split <;> simp [Nat.add_comm] <;> rfl

theorem idx_lt {n : ℕ} (x : Fin n → Bool) : idx x < 2 ^ n := by
  induction n with
  | zero => simp [idx]
  | succ n ih =>
    rw [idx_succ, Nat.pow_succ]
    have := ih (Fin.init x)
    split <;> omega

theorem testBit_idx {n : ℕ} (x : Fin n → Bool) (j : Fin n) : (idx x).testBit j = x j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [idx_succ, Nat.testBit_two_pow_mul_add _ (idx_lt _)]
    induction j using Fin.lastCases with
    | last => simp only [Fin.val_last, Nat.lt_irrefl, ite_false, Nat.sub_self]; split <;> simp_all
    | cast j =>
      simp only [Fin.val_castSucc, j.isLt, ite_true]
      rw [ih]
      rfl

/-- The truth table of `f` as a number: bit `idx x` is `f x`. -/
def tableNat : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ
  | 0, f => if f Fin.elim0 then 1 else 0
  | n + 1, f => 2 ^ (2 ^ n) * tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) +
      tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x false))

theorem tableNat_lt (n : ℕ) (f : (Fin n → Bool) → Bool) : tableNat n f < 2 ^ (2 ^ n) := by
  induction n with
  | zero => simp only [tableNat]; split <;> simp
  | succ n ih =>
    simp only [tableNat]
    have h1 := ih (fun x => f (Fin.snoc (α := fun _ => Bool) x true))
    have h2 := ih (fun x => f (Fin.snoc (α := fun _ => Bool) x false))
    have hK : 2 ^ (2 ^ (n + 1)) = 2 ^ (2 ^ n) * 2 ^ (2 ^ n) := by
      rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]
    rw [hK]
    calc 2 ^ 2 ^ n * tableNat n _ + tableNat n _
        < 2 ^ 2 ^ n * tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) + 2 ^ 2 ^ n :=
          by omega
      _ = 2 ^ 2 ^ n * (tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) + 1) := by
          ring
      _ ≤ 2 ^ 2 ^ n * 2 ^ 2 ^ n := Nat.mul_le_mul_left _ h1

theorem testBit_table (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (tableNat n f).testBit (idx x) = f x := by
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    subst hx
    simp only [tableNat, idx, Finset.univ_eq_empty, Finset.sum_empty]
    split <;> simp_all
  | succ n ih =>
    simp only [tableNat]
    rw [Nat.testBit_two_pow_mul_add _ (tableNat_lt _ _), idx_succ]
    have hx : x = Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last n)) :=
      (Fin.snoc_init_self x).symm
    have hl := idx_lt (Fin.init x)
    cases hb : x (Fin.last n) with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.zero_add, hl, ite_true]
      rw [ih]
      rw [hb] at hx
      exact congrArg f hx.symm
    | true =>
      simp only [ite_true, Nat.mul_one]
      split
      · omega
      · rw [Nat.add_sub_cancel_left, ih]
        rw [hb] at hx
        exact congrArg f hx.symm

theorem two_pow_mul_add_and (K a b c d : ℕ) (hb : b < 2 ^ K) (hd : d < 2 ^ K) :
    (2 ^ K * a + b) &&& (2 ^ K * c + d) = 2 ^ K * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hd)]
  split <;> simp

theorem table_and (n : ℕ) (f g : (Fin n → Bool) → Bool) :
    tableNat n (fun x => f x && g x) = tableNat n f &&& tableNat n g := by
  induction n with
  | zero =>
    simp only [tableNat]
    rcases Bool.eq_false_or_eq_true (f Fin.elim0) with h | h <;>
      rcases Bool.eq_false_or_eq_true (g Fin.elim0) with h' | h' <;> simp [h, h']
  | succ n ih =>
    simp only [tableNat]
    rw [two_pow_mul_add_and _ _ _ _ _ (tableNat_lt _ _) (tableNat_lt _ _), ih, ih]

/-- Monotone on `n` inputs, in the row's words. -/
def Mono (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true

/-- One level of the recursion: for each lower half `a` of `as`, each upper half `b` of `L`
with `a ≤ b` bitwise. -/
def step (K : ℕ) (L as : List ℕ) : List ℕ :=
  as.flatMap (fun a => (L.filter (fun b => a &&& b == a)).map (fun b => 2 ^ K * b + a))

theorem step_append (K : ℕ) (L as bs : List ℕ) :
    step K L (as ++ bs) = step K L as ++ step K L bs := List.flatMap_append

/-- The tables of the monotone functions on `n` inputs. -/
def monoTables : ℕ → List ℕ
  | 0 => [0, 1]
  | n + 1 => let L := monoTables n; step (2 ^ n) L L

theorem mono_mem (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : Mono n f) :
    tableNat n f ∈ monoTables n := by
  induction n with
  | zero => simp only [tableNat, monoTables]; split <;> simp
  | succ n ih =>
    set f1 : (Fin n → Bool) → Bool := fun x => f (Fin.snoc (α := fun _ => Bool) x true)
    set f0 : (Fin n → Bool) → Bool := fun x => f (Fin.snoc (α := fun _ => Bool) x false)
    have hm : ∀ b : Bool, Mono n (fun x => f (Fin.snoc (α := fun _ => Bool) x b)) := by
      intro b x y hxy hx
      refine hf _ _ ?_ hx
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hxy i
    have h0 := ih f0 (hm false)
    have h1 := ih f1 (hm true)
    have hle : (fun x => f0 x && f1 x) = f0 := by
      funext x
      cases h : f0 x with
      | false => simp
      | true =>
        have : f1 x = true := hf _ _ (by
          intro i
          induction i using Fin.lastCases with
          | last => simp
          | cast i => simp) h
        simp [this]
    have hand : tableNat n f0 &&& tableNat n f1 = tableNat n f0 := by
      rw [← table_and, hle]
    show 2 ^ (2 ^ n) * tableNat n f1 + tableNat n f0 ∈ step (2 ^ n) (monoTables n) (monoTables n)
    simp only [step, List.mem_flatMap, List.mem_map, List.mem_filter]
    exact ⟨tableNat n f0, h0, tableNat n f1, ⟨h1, by simp [hand]⟩, rfl⟩

/-! ## The checker, five inputs -/

/-- The map of five inputs with code `c`: input `i` goes to digit `i` of `c` in base five. -/
def dec (c : ℕ) (i : Fin 5) : Fin 5 := ⟨c / 5 ^ (i : ℕ) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The position `idx (x ∘ dec c)` for the input `x` at position `m`. -/
def pidx (c m : ℕ) : ℕ :=
  (if m.testBit (dec c 0) then 1 else 0) + (if m.testBit (dec c 1) then 2 else 0) +
  (if m.testBit (dec c 2) then 4 else 0) + (if m.testBit (dec c 3) then 8 else 0) +
  (if m.testBit (dec c 4) then 16 else 0)

theorem pidx_eq (c m : ℕ) :
    pidx c m = ∑ i : Fin 5, if m.testBit (dec c i) then 2 ^ (i : ℕ) else 0 := by
  simp only [pidx, Fin.sum_univ_five]
  rfl

/-- The entry `(c, d, T)` is right for the table `t`, with `T` in the list `R`. -/
def Ent (R : List ℕ) (t c d T : ℕ) : Prop :=
  (∀ i : Fin 5, dec d (dec c i) = i) ∧ T ∈ R ∧ ∀ m < 32, t.testBit (pidx c m) = T.testBit m

instance (R : List ℕ) (t c d T : ℕ) : Decidable (Ent R t c d T) := by
  unfold Ent; infer_instance

/-- Every table of `ts` has its right entry, in order, in `ws`. -/
def chk (R : List ℕ) : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | t :: ts, (c, d, T) :: ws => decide (Ent R t c d T) && chk R ts ws

/-- `t` is, after relabelling its inputs by a map with a left inverse, a table of `R`. -/
def Good (R : List ℕ) (t : ℕ) : Prop :=
  ∃ σ τ : Fin 5 → Fin 5, (∀ i, τ (σ i) = i) ∧ ∃ T ∈ R,
    ∀ m < 32, t.testBit (∑ i : Fin 5, if m.testBit (σ i) then 2 ^ (i : ℕ) else 0) = T.testBit m

theorem chk_sound (R : List ℕ) :
    ∀ (ts : List ℕ) (ws : List (ℕ × ℕ × ℕ)), chk R ts ws = true → ∀ t ∈ ts, Good R t
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [chk] at h
  | t :: ts, (c, d, T) :: ws, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · obtain ⟨h1, h2, h3⟩ := h.1
      exact ⟨dec c, dec d, h1, T, h2, fun m hm => by rw [← pidx_eq]; exact h3 m hm⟩
    · exact chk_sound R ts ws h.2 t' ht'

end PEqualNP.MetaComplexity.Mono5
