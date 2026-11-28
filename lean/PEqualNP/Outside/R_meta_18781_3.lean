import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18781_3 (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    (∃ j g, C.gates[j]? = some g ∧ g.op = .and ∧
      (C.wires (List.ofFn fun i : Fin 42 => decide (i = 0 ∨ i = 22))).getD (42+j) false = true) →
    ∃ P S : PEqualNP.CircuitLowerBounds.Circuit, ∃ t : List ℕ,
      PEqualNP.MetaComplexity.Monotone2 P ∧ PEqualNP.MetaComplexity.Monotone2 S ∧ P.size + S.size + 1 = C.size ∧ t.length ≤ 2 ∧
      (∀ i ∈ t, i < 42 + P.size ∧ ∃ k ∈ ([0,22] : List (Fin 42)),
        (P.wires (List.ofFn fun j => decide (j = k))).getD i false = true) ∧
      ∀ x : Fin 42 → Bool, let w := P.wires (List.ofFn x);
        C.eval (List.ofFn x) = S.eval (w ++ [t.all fun i => w.getD i false]) ∧
        (S.eval (w ++ [false]) = true → S.eval (w ++ [true]) = true))
    (h2 : ∀ P S : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 P → PEqualNP.MetaComplexity.Monotone2 S → P.size + S.size ≤ 123 →
    let E := fun p l : Fin 42 => p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
    let row := fun p l : Fin 42 => fun i => decide (i = p ∨ i = l)
    let N := Maximal (fun x : Fin 42 → Bool => ¬∃ p l, E p l ∧ x p = true ∧ x l = true)
    let w := fun x : Fin 42 → Bool => P.wires (List.ofFn x)
    let f := fun x b => S.eval (w x ++ [b])
    (∀ p l, E p l → f (row p l) true = true) → (∀ x, N x → f x false = false) →
    ∀ t : List ℕ, t.length ≤ 2 →
      (∀ i ∈ t, i < 42 + P.size ∧
        (∃ k ∈ ([0,22] : List (Fin 42)), (w (fun j => decide (j = k))).getD i false = true) ∧
        ∀ p l, E p l → f (row p l) false = false → (w (row p l)).getD i false = true) →
      ∃ m, N m ∧ f m true = true ∧ ∀ i ∈ t, (w m).getD i false = true) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C _ hm hsize computes hot
  obtain ⟨P,S,t,hP,hS,hs,ht,valid,transfer⟩ := h1 C hm hot
  let E (p l : Fin 42) := p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20] : List ℕ)
  let row (p l : Fin 42) := fun i => decide (i = p ∨ i = l)
  let w (x : Fin 42 → Bool) := P.wires (List.ofFn x)
  let f (x : Fin 42 → Bool) (b : Bool) := S.eval (w x ++ [b])
  let v (x : Fin 42 → Bool) := t.all fun i => (w x).getD i false
  have he (x) : C.eval (List.ofFn x) = f x (v x) := (transfer x).1
  have good (p l : Fin 42) (hp : E p l) : f (row p l) (v (row p l)) = true := by
    rw [← he]
    exact (computes _).2 ⟨p,l,hp,by simp [row],by simp [row]⟩
  have high (p l : Fin 42) (hp : E p l) : f (row p l) true = true := by
    have hv := good p l hp
    cases hx : v (row p l) <;> rw [hx] at hv
    · exact (transfer _).2 hv
    · exact hv
  let N := Maximal (fun x : Fin 42 → Bool => ¬∃ p l, E p l ∧ x p = true ∧ x l = true)
  have low (m : Fin 42 → Bool) (h : N m) : f m false = false := by
    cases hx : f m false
    · rfl
    · exfalso
      apply h.1 ((computes _).1 ?_)
      rw [he]
      cases v m
      · exact hx
      · exact (transfer _).2 hx
  obtain ⟨m,hmn,hm1,hmt⟩ := h2 P S hP hS (by omega) high low t ht (by
    intro i hi
    refine ⟨(valid i hi).1,(valid i hi).2,?_⟩
    intro p l hp hf
    have hv := good p l hp
    change f (row p l) false = false at hf
    cases hx : v (row p l) with
    | true => exact List.all_eq_true.mp hx i hi
    | false => rw [hx,hf] at hv; contradiction)
  apply hmn.1 ((computes _).1 ?_)
  rw [he,show v m = true from List.all_eq_true.mpr hmt]
  exact hm1
