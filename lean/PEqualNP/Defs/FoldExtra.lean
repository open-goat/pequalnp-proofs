import PEqualNP.Defs.SyntacticFold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Readers, EXTRA and folded circuits, beside the syntactic fold (seat-gct-2, for Lemma M of seat-ralg-1)

Vocabulary for statements about `PEqualNP.SyntacticFold.fold` on the root's circuits, on `N` inputs (wires `0 .. N - 1`;
gate `j` is wire `N + j`).

* `readers gs out w`: the number of gates of the list `gs` whose input list contains `w`, plus one when `w` is the output
  `out` (`out = some w`). A gate that lists `w` twice counts once.
* `extra N gs out`: the sum, over the wires `w < N + gs.length`, of `readers gs out w - 1`. An unread wire adds `0`
  (subtraction on the naturals), so this is the sum of (readers - 1) over the wires with at least one reader.
* `circuitExtra N C`: `extra` of `C`, with its output `C.output` as the one output.
* `foldedOut F`: the output of a folded circuit `F`, its first output value, as a wire (`some u`) or none when it is a
  constant. `foldedExtra N F`: `extra` of `F` with that output.
* `IsFolded N C`: every gate is an AND or an OR gate, reads exactly two distinct wires, both earlier than itself; the
  output is an existing wire (an input or a gate); every gate is read by some gate or is the output. (A gate read by a
  later gate, recursively, is in the output's cone, so this says that no gate is dead.)
* `zeroing Z`: the partial assignment fixing every input in the finite set `Z` to `false`, nothing else.
* `BecomesZero N Z C w`: the wire `w` is an input in `Z`, or a gate wire whose value in the pass of the fold under
  `zeroing Z` is the constant `false`.

Caveats a statement must respect:
* `readers` and `extra` count over a LIST of gates and one output; they read gate inputs as written, so a statement
  should assume what it needs (`IsFolded`) about which wires exist.
* `foldedOut` reads only the first output; with `fold N rho C [C.output]` that is the circuit's one output.
* `zeroing Z` fixes only inputs: an element of `Z` at or above `N` changes nothing in the fold, and `BecomesZero` asks
  `w < N` of a zeroed input.
* `BecomesZero` is SYNTACTIC: a gate counts only when the pass gives it the constant `false`. A gate that is `false`
  on every input but does not fold to the constant is not counted (red team, 2026-11-25 23:43 UTC).
* `extra` of a folded circuit equals its size minus the number of inputs read plus one (the counting identity
  `C.size = R - 1 + EXTRA`), but nothing here states that.
-/

namespace PEqualNP.FoldExtra

open PEqualNP.CircuitLowerBounds PEqualNP.SyntacticFold

/-- The gates of `gs` reading wire `w`, plus one if `w` is the output. -/
def readers (gs : List Gate) (out : Option ℕ) (w : ℕ) : ℕ :=
  (gs.filter fun g => decide (w ∈ g.inputs)).length + if out = some w then 1 else 0

/-- The sum of readers minus one over the wires below `N + gs.length`. -/
def extra (N : ℕ) (gs : List Gate) (out : Option ℕ) : ℕ :=
  ∑ w ∈ Finset.range (N + gs.length), (readers gs out w - 1)

/-- EXTRA of a circuit, read at its output. -/
def circuitExtra (N : ℕ) (C : Circuit) : ℕ :=
  extra N C.gates (some C.output)

/-- The first output of a folded circuit, as a wire, or none when it is a constant. -/
def foldedOut (F : Folded) : Option ℕ :=
  match F.outs.headD (Val.const false) with
  | Val.wire u => some u
  | Val.const _ => none

/-- EXTRA of a folded circuit, read at its first output. -/
def foldedExtra (N : ℕ) (F : Folded) : ℕ :=
  extra N F.gates (foldedOut F)

/-- A folded AND/OR circuit: two distinct earlier reads per gate, an existing output, no dead gate. -/
def IsFolded (N : ℕ) (C : Circuit) : Prop :=
  C.output < N + C.gates.length ∧
    ∀ j < C.gates.length,
      ((C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨ (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.or) ∧
      (C.gates.getD j ⟨GateOp.or, []⟩).inputs.length = 2 ∧ (C.gates.getD j ⟨GateOp.or, []⟩).inputs.Nodup ∧
      (∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + j) ∧
      1 ≤ readers C.gates (some C.output) (N + j)

/-- Fix every input in `Z` to `false`. -/
def zeroing (Z : Finset ℕ) : ℕ → Option Bool :=
  fun k => if k ∈ Z then some false else none

/-- Wire `w` becomes `0` under `zeroing Z`: an input in `Z`, or a gate whose pass value is the constant `false`. -/
def BecomesZero (N : ℕ) (Z : Finset ℕ) (C : Circuit) (w : ℕ) : Prop :=
  (w < N ∧ w ∈ Z) ∨ (N ≤ w ∧ (pass N (zeroing Z) C).2.getD w (Val.const true) = Val.const false)

instance (N : ℕ) (Z : Finset ℕ) (C : Circuit) (w : ℕ) : Decidable (BecomesZero N Z C w) := by
  unfold BecomesZero; infer_instance

end PEqualNP.FoldExtra
