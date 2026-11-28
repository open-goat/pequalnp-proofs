import PEqualNP.Defs

-- L-meta-53175 (lane O1). The schedule-subset lemma (canP, key) is the staged L-meta-53174 of this lane;
-- the rank-realising construction R1297 is the staged L-lib-1297 proof of lane N5, copied inline.
-- Wire-fold lemmas follow the merged PEqualNP.Outside.L_meta_567; the signature lemmas are from L-lib-1279/1283 (same lane).

namespace PEqualNP.Outside.L_meta_53175
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq {α : Type} (L : List α) (a d : α) : (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (L : List α) (d : α) {j : ℕ} (h : L.length ≤ j) : L.getD j d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- The wire of gate `p` is that gate applied to the final wires it reads. -/
theorem wire_at : ∀ (gs : List Gate) (w : List Bool) (p : ℕ), p < gs.length →
    (∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < w.length + p) →
    (wiresFrom gs w).getD (w.length + p) false =
      (gs.getD p ⟨GateOp.or, []⟩).op.eval
        ((gs.getD p ⟨GateOp.or, []⟩).inputs.map fun i => (wiresFrom gs w).getD i false)
  | [], _, _, h, _ => by simp at h
  | g :: gs, w, 0, _, hrb => by
    have e : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    simp only [List.getD_cons_zero, Nat.add_zero] at hrb ⊢
    rw [e, getD_wiresFrom _ _ _ (by simp)]
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    simp only [List.getD_cons_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [getD_wiresFrom _ _ _ (by simp; have := hrb i hi; omega), List.getD_append _ _ _ _ (hrb i hi)]
  | g :: gs, w, p + 1, hp, hrb => by
    have e : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    simp only [List.getD_cons_succ] at hrb ⊢
    rw [e]
    have := wire_at gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) p (by simp at hp; omega)
      (by intro i hi; have := hrb i hi; simp; omega)
    simp only [List.length_append, List.length_singleton] at this
    rw [show w.length + (p + 1) = w.length + 1 + p by omega]
    exact this

def isNotB (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

/-- Input word of a mask. -/
noncomputable def inw (n : ℕ) (x : Finset (Fin n)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false, true]

theorem inw_len (n : ℕ) (x : Finset (Fin n)) : (inw n x).length = n + 2 := by simp [inw]

theorem inw_getD_lt (n : ℕ) (x : Finset (Fin n)) (i : ℕ) (h : i < n) :
    (inw n x).getD i false = true ↔ (⟨i, h⟩ : Fin n) ∈ x := by
  unfold inw
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; exact h)]
  simp [h]

theorem inw_getD_ge (n : ℕ) (x : Finset (Fin n)) (i : ℕ) (h : n ≤ i) :
    (inw n x).getD i false = decide (i = n + 1) := by
  unfold inw
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; exact h)]
  simp only [List.length_ofFn]
  rcases (show i = n ∨ i = n + 1 ∨ n + 2 ≤ i by omega) with h1 | h1 | h1
  · subst h1; simp
  · subst h1; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]
    symm; simp; omega

theorem inw_mono (n : ℕ) (x y : Finset (Fin n)) (hxy : x ⊆ y) (i : ℕ) :
    (inw n x).getD i false ≤ (inw n y).getD i false := by
  by_cases h : i < n
  · rw [Bool.le_iff_imp]
    intro hx
    rw [inw_getD_lt _ _ _ h] at hx ⊢
    exact hxy hx
  · rw [inw_getD_ge _ _ _ (by omega), inw_getD_ge _ _ _ (by omega)]

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.all_cons, id]
    revert ha hl
    cases f a <;> cases f' a <;> cases (l.map f).all id <;> cases (l.map f').all id <;> decide

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.any_cons, id]
    revert ha hl
    cases f a <;> cases f' a <;> cases (l.map f).any id <;> cases (l.map f').any id <;> decide

section mono
variable (n : ℕ) (C : Circuit)

noncomputable def Wv (x : Finset (Fin n)) (i : ℕ) : Bool := (wiresFrom C.gates (inw n x)).getD i false

theorem gate_ops (hfan : PEqualNP.MetaComplexity.FanInTwo C) (p : ℕ) (hp : p < C.gates.length) :
    (C.gates.getD p ⟨GateOp.or, []⟩).op = GateOp.and ∨ (C.gates.getD p ⟨GateOp.or, []⟩).op = GateOp.or ∨
      (C.gates.getD p ⟨GateOp.or, []⟩).op = GateOp.not := by
  have hmem : C.gates.getD p ⟨GateOp.or, []⟩ ∈ C.gates := by
    rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
  have := (hfan _ hmem).1
  simpa [Set.mem_insert_iff] using this

/-- A wire is monotone in the mask as long as every NOT gate up to it gives the same output. -/
theorem mono (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (x y : Finset (Fin n)) (hxy : x ⊆ y) : ∀ i,
    (∀ q, q < C.gates.length → n + 2 + q ≤ i → isNotB (C.gates.getD q ⟨GateOp.or, []⟩) = true →
      Wv n C x (n + 2 + q) = Wv n C y (n + 2 + q)) →
    Wv n C x i ≤ Wv n C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hagree
    by_cases hin : i < n + 2
    · unfold Wv
      rw [getD_wiresFrom _ _ _ (by rw [inw_len]; exact hin), getD_wiresFrom _ _ _ (by rw [inw_len]; exact hin)]
      exact inw_mono n x y hxy i
    · by_cases hg : i < n + 2 + C.gates.length
      · obtain ⟨p, rfl⟩ : ∃ p, i = n + 2 + p := ⟨i - (n + 2), by omega⟩
        have hp : p < C.gates.length := by omega
        have hrbp : ∀ k ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs, k < (inw n x).length + p := by
          intro k hk; rw [inw_len]; exact hrb p hp k hk
        have hrbp' : ∀ k ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs, k < (inw n y).length + p := by
          intro k hk; rw [inw_len]; exact hrb p hp k hk
        have ex := wire_at C.gates (inw n x) p hp hrbp
        have ey := wire_at C.gates (inw n y) p hp hrbp'
        rw [inw_len] at ex ey
        rcases gate_ops C hfan p hp with h | h | h
        · unfold Wv; rw [ex, ey, h]
          apply all_mono
          intro k hk
          have hk' := hrb p hp k hk
          exact ih k (by omega) (fun q hq hq2 hq3 => hagree q hq (by omega) hq3)
        · unfold Wv; rw [ex, ey, h]
          apply any_mono
          intro k hk
          have hk' := hrb p hp k hk
          exact ih k (by omega) (fun q hq hq2 hq3 => hagree q hq (by omega) hq3)
        · have := hagree p hp le_rfl (by unfold isNotB; rw [h])
          exact le_of_eq this
      · unfold Wv
        rw [getD_ge _ _ (by rw [length_wiresFrom, inw_len]; omega),
          getD_ge _ _ (by rw [length_wiresFrom, inw_len]; omega)]

/-- The first NOT whose output differs falls. -/
theorem not_falls (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (x y : Finset (Fin n)) (hxy : x ⊆ y) (p : ℕ) (hp : p < C.gates.length)
    (hnot : isNotB (C.gates.getD p ⟨GateOp.or, []⟩) = true)
    (hpre : ∀ q, q < p → isNotB (C.gates.getD q ⟨GateOp.or, []⟩) = true →
      Wv n C x (n + 2 + q) = Wv n C y (n + 2 + q)) :
    Wv n C y (n + 2 + p) ≤ Wv n C x (n + 2 + p) := by
  have hop : (C.gates.getD p ⟨GateOp.or, []⟩).op = GateOp.not := by
    revert hnot; unfold isNotB; split <;> simp_all
  have hrbp : ∀ k ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs, k < (inw n x).length + p := by
    intro k hk; rw [inw_len]; exact hrb p hp k hk
  have hrbp' : ∀ k ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs, k < (inw n y).length + p := by
    intro k hk; rw [inw_len]; exact hrb p hp k hk
  have ex := wire_at C.gates (inw n x) p hp hrbp
  have ey := wire_at C.gates (inw n y) p hp hrbp'
  rw [inw_len] at ex ey
  unfold Wv; rw [ex, ey, hop]
  simp only [GateOp.eval]
  cases hin : (C.gates.getD p ⟨GateOp.or, []⟩).inputs with
  | nil => simp
  | cons k ks =>
    have hk : k < n + 2 + p := hrb p hp k (by
      show k ∈ (C.gates.getD p ⟨GateOp.or, []⟩).inputs; rw [hin]; exact List.mem_cons_self)
    have hm := mono n C hfan hrb x y hxy k (fun q hq hq2 hq3 => hpre q (by omega) hq3)
    unfold Wv at hm
    simp only [List.map_cons, List.headD_cons]
    revert hm
    cases (wiresFrom C.gates (inw n x)).getD k false <;> cases (wiresFrom C.gates (inw n y)).getD k false <;> decide

end mono

/-- Binary value of a bit sequence, most significant first. -/
noncomputable def bval (G : List ℕ) (b : ℕ → Bool) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  G.foldl (fun s i => 2 * s + (if b i then 1 else 0)) 0

theorem foldl_acc (b : ℕ → Bool) : ∀ (G : List ℕ) (s : ℕ),
    G.foldl (fun s i => 2 * s + (@ite _ (b i = true) (Classical.propDecidable _) 1 0)) s = s * 2 ^ G.length + bval G b
  | [], s => by simp [bval]
  | a :: G, s => by
    simp only [List.foldl_cons, bval]
    rw [foldl_acc b G, foldl_acc b G (2 * 0 + _)]
    simp only [List.length_cons, pow_succ]; ring

theorem bval_cons (a : ℕ) (G : List ℕ) (b : ℕ → Bool) :
    bval (a :: G) b = (if b a then 1 else 0) * 2 ^ G.length + bval G b := by
  show List.foldl (fun s i => 2 * s + (@ite _ (b i = true) (Classical.propDecidable _) 1 0)) 0 (a :: G) = _
  rw [List.foldl_cons, foldl_acc]; simp

theorem bval_lt (b : ℕ → Bool) : ∀ G : List ℕ, bval G b < 2 ^ G.length
  | [] => by simp [bval]
  | a :: G => by
    rw [bval_cons, List.length_cons, pow_succ]
    have := bval_lt b G
    split_ifs <;> omega

/-- Lexicographic comparison: if each bit of `b2` is at most that of `b1` once all earlier bits agree,
then the binary value of `b2` is at most that of `b1`, with equality only when all bits agree. -/
theorem lex (b1 b2 : ℕ → Bool) : ∀ G : List ℕ, G.Pairwise (· < ·) →
    (∀ a ∈ G, (∀ c ∈ G, c < a → b1 c = b2 c) → b2 a ≤ b1 a) →
    bval G b2 ≤ bval G b1 ∧ (bval G b2 = bval G b1 → ∀ a ∈ G, b1 a = b2 a)
  | [], _, _ => by simp [bval]
  | a :: G, hs, H => by
    rw [List.pairwise_cons] at hs
    obtain ⟨hlt, hs'⟩ := hs
    rw [bval_cons, bval_cons]
    have h1 := bval_lt b1 G
    have h2 := bval_lt b2 G
    by_cases hab : b1 a = b2 a
    · have H' : ∀ a' ∈ G, (∀ c ∈ G, c < a' → b1 c = b2 c) → b2 a' ≤ b1 a' := by
        intro a' ha' hc
        apply H a' (List.mem_cons_of_mem _ ha')
        intro c hc' hca
        rcases List.mem_cons.1 hc' with rfl | hc''
        · exact hab
        · exact hc c hc'' hca
      obtain ⟨i1, i2⟩ := lex b1 b2 G hs' H'
      refine ⟨by rw [hab]; omega, fun he => ?_⟩
      intro a' ha'
      rcases List.mem_cons.1 ha' with rfl | ha''
      · exact hab
      · exact i2 (by rw [hab] at he; omega) a' ha''
    · have hle := H a List.mem_cons_self (fun c hc hca => by
        rcases List.mem_cons.1 hc with rfl | hc'
        · exact absurd hca (lt_irrefl _)
        · exact absurd (hlt c hc') (by omega))
      have hb1 : b1 a = true := by revert hle hab; cases b1 a <;> cases b2 a <;> decide
      have hb2 : b2 a = false := by revert hle hab; cases b1 a <;> cases b2 a <;> decide
      rw [hb1, hb2]
      simp only [ite_true, Bool.false_eq_true, ite_false, zero_mul, zero_add, one_mul]
      refine ⟨by omega, fun he => by omega⟩

theorem range_filter_len (p : Gate → Bool) (d : Gate) : ∀ L : List Gate,
    ((List.range L.length).filter (fun i => p (L.getD i d))).length = (L.filter p).length := by
  intro L
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, List.filter_append,
      List.length_append, List.length_append]
    have hc : (List.range L.length).filter (fun i => p ((L ++ [a]).getD i d)) =
        (List.range L.length).filter (fun i => p (L.getD i d)) := by
      apply List.filter_congr
      intro i hi
      rw [List.mem_range] at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [hc, ih]
    simp only [List.filter_cons, List.filter_nil, getD_snoc_eq]
    split_ifs <;> simp


/-- NOT gate indices in order, the signature, and wire falls. -/
def gatesF (C : Circuit) : List ℕ :=
  (List.range C.size).filter (fun i => isNotB (C.gates.getD i ⟨GateOp.or, []⟩))

noncomputable def sigF (n : ℕ) (C : Circuit) (x : Finset (Fin n)) : ℕ :=
  bval (gatesF C) (fun i => Wv n C x (n + 2 + i))

theorem gatesF_len (C : Circuit) : (gatesF C).length = PEqualNP.NotBracket.notCount C := by
  unfold gatesF PEqualNP.NotBracket.notCount
  rw [show C.size = C.gates.length from rfl, range_filter_len]
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotB]

theorem gatesF_sorted (C : Circuit) : (gatesF C).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem mem_gatesF (C : Circuit) (p : ℕ) :
    p ∈ gatesF C ↔ p < C.gates.length ∧ isNotB (C.gates.getD p ⟨GateOp.or, []⟩) = true := by
  unfold gatesF; rw [List.mem_filter, List.mem_range]; rfl

theorem coreF (n : ℕ) (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C) (x y : Finset (Fin n)) (hxy : x ⊆ y) :
    sigF n C y ≤ sigF n C x ∧
      ((∃ i, i < n + 2 + C.size ∧ Wv n C x i = true ∧ Wv n C y i = false) → sigF n C y < sigF n C x) := by
  have hL := lex (fun i => Wv n C x (n + 2 + i)) (fun i => Wv n C y (n + 2 + i)) (gatesF C) (gatesF_sorted C) (by
    intro a ha hpre
    obtain ⟨hap, han⟩ := (mem_gatesF C a).1 ha
    exact not_falls n C hfan hrb x y hxy a hap han (fun q hq hqn => hpre q ((mem_gatesF C q).2
      ⟨by omega, hqn⟩) hq))
  refine ⟨hL.1, fun hd => ?_⟩
  rcases Nat.lt_or_ge (sigF n C y) (sigF n C x) with h | h
  · exact h
  · exfalso
    have hall := hL.2 (le_antisymm hL.1 h)
    obtain ⟨i, _, hix, hiy⟩ := hd
    have hm := mono n C hfan hrb x y hxy i (fun q hq _ hqn => hall q ((mem_gatesF C q).2 ⟨hq, hqn⟩))
    rw [hix, hiy] at hm
    exact absurd hm (by decide)

theorem sigF_lt (n : ℕ) (C : Circuit) (x : Finset (Fin n)) :
    sigF n C x < 2 ^ PEqualNP.NotBracket.notCount C := by
  unfold sigF; rw [← gatesF_len]; exact bval_lt _ _

theorem bval_append (b : ℕ → Bool) (G H : List ℕ) : bval (G ++ H) b = bval G b * 2 ^ H.length + bval H b := by
  show List.foldl (fun s i => 2 * s + (@ite _ (b i = true) (Classical.propDecidable _) 1 0)) 0 (G ++ H) = _
  rw [List.foldl_append, foldl_acc]; rfl

theorem bval_inj (b1 b2 : ℕ → Bool) : ∀ H : List ℕ, bval H b1 = bval H b2 → ∀ a ∈ H, b1 a = b2 a
  | [], _ => by simp
  | a :: H, he => by
    rw [bval_cons, bval_cons] at he
    have h1 := bval_lt b1 H
    have h2 := bval_lt b2 H
    have hab : b1 a = b2 a := by
      rcases Bool.eq_false_or_eq_true (b1 a) with h | h <;> rcases Bool.eq_false_or_eq_true (b2 a) with h' | h' <;>
        simp [h, h'] at he ⊢ <;> omega
    rw [hab] at he
    have ht := bval_inj b1 b2 H (by omega)
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | h
    · exact hab
    · exact ht a' h

/-- Two signatures in the same aligned block of length `2^s` agree on their leading bits. -/
theorem lead_bits (b1 b2 : ℕ → Bool) (G : List ℕ) (s q : ℕ) (hs : s ≤ G.length)
    (h1 : q * 2 ^ s ≤ bval G b1) (h1' : bval G b1 < (q + 1) * 2 ^ s)
    (h2 : q * 2 ^ s ≤ bval G b2) (h2' : bval G b2 < (q + 1) * 2 ^ s) :
    ∀ a ∈ G.take (G.length - s), b1 a = b2 a := by
  have hsplit : ∀ b : ℕ → Bool, bval G b = bval (G.take (G.length - s)) b * 2 ^ s + bval (G.drop (G.length - s)) b := by
    intro b
    conv_lhs => rw [← List.take_append_drop (G.length - s) G]
    rw [bval_append, List.length_drop, show G.length - (G.length - s) = s by omega]
  have hq : ∀ b : ℕ → Bool, q * 2 ^ s ≤ bval G b → bval G b < (q + 1) * 2 ^ s →
      bval (G.take (G.length - s)) b = q := by
    intro b hl hu
    have e := hsplit b
    have hd : bval (G.drop (G.length - s)) b < 2 ^ s := by
      have := bval_lt b (G.drop (G.length - s)); rwa [List.length_drop, show G.length - (G.length - s) = s by omega] at this
    have hp : 0 < 2 ^ s := Nat.two_pow_pos s
    have k1 : bval (G.take (G.length - s)) b * 2 ^ s < (q + 1) * 2 ^ s := by omega
    have k2 : q * 2 ^ s < (bval (G.take (G.length - s)) b + 1) * 2 ^ s := by rw [add_mul]; omega
    have := Nat.lt_of_mul_lt_mul_right k1
    have := Nat.lt_of_mul_lt_mul_right k2
    omega
  exact bval_inj b1 b2 _ (by rw [hq b1 h1 h1', hq b2 h2 h2'])


theorem map_range_getD {β : Type} (f : ℕ → β) (d : β) (m k : ℕ) (hk : k < m) :
    ((List.range m).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_snoc_at {α : Type} (L : List α) (a d : α) (k : ℕ) (h : k = L.length) : (L ++ [a]).getD k d = a := by
  subst h; exact getD_snoc_eq L a d

theorem notCount_isNot (C : Circuit) : PEqualNP.NotBracket.notCount C = (C.gates.filter isNotB).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotB]

def canP {X : Type} [Preorder X] (n : ℕ) (cost : Fin (n + 1) → X → ℕ) (S : Finset (Fin (n + 1)))
    (k : ℕ) (x : X) (e : ℕ) : Prop :=
  ∃ f : Fin (n + 1) → X, Monotone f ∧ (∀ i, f i ≤ x) ∧
    (S.filter (fun i => i.val < k)).sum (fun i => cost i (f i)) ≤ e

theorem canP_sub {X : Type} [Preorder X] (n : ℕ) (cost : Fin (n + 1) → X → ℕ) (S T : Finset (Fin (n + 1)))
    (hST : S ⊆ T) (k : ℕ) (x : X) (e : ℕ) (h : canP n cost T k x e) : canP n cost S k x e := by
  obtain ⟨f, hm, hx, hs⟩ := h
  refine ⟨f, hm, hx, le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)) hs⟩
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hST hi.1, hi.2⟩

theorem canP_pred {X : Type} [Preorder X] (n : ℕ) (cost : Fin (n + 1) → X → ℕ) (S : Finset (Fin (n + 1)))
    (k : ℕ) (x : X) (e : ℕ) (h : canP n cost S (k + 1) x e) : canP n cost S k x e := by
  obtain ⟨f, hm, hx, hs⟩ := h
  refine ⟨f, hm, hx, le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)) hs⟩
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by omega⟩

theorem sum_succ (n : ℕ) (S : Finset (Fin (n + 1))) (k : ℕ) (F : Fin (n + 1) → ℕ) :
    (S.filter (fun i => i.val < k + 1)).sum F =
      (S.filter (fun i => i.val < k)).sum F + (S.filter (fun i => i.val = k)).sum F := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

theorem sum_eq_in (n : ℕ) (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) (hj : j ∈ S) (F : Fin (n + 1) → ℕ) :
    (S.filter (fun i => i.val = j.val)).sum F = F j := by
  have : S.filter (fun i => i.val = j.val) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact Fin.ext h
    · rintro rfl; exact ⟨hj, rfl⟩
  rw [this, Finset.sum_singleton]

theorem sum_eq_out (n : ℕ) (S : Finset (Fin (n + 1))) (k : ℕ)
    (hk : ∀ i ∈ S, i.val ≠ k) (F : Fin (n + 1) → ℕ) :
    (S.filter (fun i => i.val = k)).sum F = 0 := by
  have : S.filter (fun i => i.val = k) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact hk i
  rw [this, Finset.sum_empty]

theorem key (X : Type) [Preorder X] [Fintype X] (limit : X → ℕ) (hanti : Antitone limit) (n : ℕ)
    (cost : Fin (n + 1) → X → ℕ) :
    ∃ S : Finset (Fin (n + 1)), S.card ≤ Finset.univ.sum limit ∧
      ∀ (k : ℕ) (x : X) (e : ℕ), e < limit x →
        (canP n cost Finset.univ k x e ↔ canP n cost S k x e) := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => ∃ x : X, ∃ e : ℕ, e < limit x ∧
    canP n cost Finset.univ j.val x e ∧ ¬ canP n cost Finset.univ (j.val + 1) x e)
  refine ⟨S, ?_, ?_⟩
  · -- each kept level loses a valid pair, and a pair is lost at most once
    let P : Finset (Σ _ : X, ℕ) := Finset.univ.sigma (fun x => Finset.range (limit x))
    have hP : P.card = Finset.univ.sum limit := by
      simp [P, Finset.card_sigma]
    rw [← hP]
    let R : Fin (n + 1) → (Σ _ : X, ℕ) → Prop := fun j p => p.2 < limit p.1 ∧
      canP n cost Finset.univ j.val p.1 p.2 ∧ ¬ canP n cost Finset.univ (j.val + 1) p.1 p.2
    -- a pair is lost at most once
    have hdown : ∀ (x : X) (e : ℕ) (m k : ℕ), canP n cost Finset.univ (k + m) x e →
        canP n cost Finset.univ k x e := by
      intro x e m
      induction m with
      | zero => intro k h; simpa using h
      | succ m ih =>
        intro k h
        exact ih k (canP_pred n cost _ (k + m) _ _ (by rw [show k + m + 1 = k + (m + 1) by omega]; exact h))
    have honce : ∀ j1 j2 p, R j1 p → R j2 p → j1 = j2 := by
      intro j1 j2 p h1 h2
      obtain ⟨_, a1, b1⟩ := h1
      obtain ⟨_, a2, b2⟩ := h2
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : j1.val ≠ j2.val) with h | h
      · exact b1 (hdown p.1 p.2 (j2.val - (j1.val + 1)) (j1.val + 1)
          (by rw [show j1.val + 1 + (j2.val - (j1.val + 1)) = j2.val by omega]; exact a2))
      · exact b2 (hdown p.1 p.2 (j1.val - (j2.val + 1)) (j2.val + 1)
          (by rw [show j2.val + 1 + (j1.val - (j2.val + 1)) = j1.val by omega]; exact a1))
    have hex : ∀ j ∈ S, ∃ p : Σ _ : X, ℕ, R j p := by
      intro j hj
      obtain ⟨x, e, he, h1, h2⟩ := (Finset.mem_filter.1 hj).2
      exact ⟨⟨x, e⟩, he, h1, h2⟩
    rcases S.eq_empty_or_nonempty with h0 | ⟨j0, hj0⟩
    · rw [h0]; simp
    · obtain ⟨p0, _⟩ := hex j0 hj0
      let φ : Fin (n + 1) → Σ _ : X, ℕ := fun j => if h : ∃ p, R j p then h.choose else p0
      have hφ : ∀ j ∈ S, R j (φ j) := by
        intro j hj
        have h := hex j hj
        simp only [φ, dif_pos h]
        exact h.choose_spec
      apply Finset.card_le_card_of_injOn φ
      · intro j hj
        have := (hφ j (Finset.mem_coe.1 hj)).1
        simp only [P, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
          Finset.coe_range, Set.mem_Iio]
        exact this
      · intro j1 hj1 j2 hj2 he
        exact honce j1 j2 (φ j1) (hφ j1 (Finset.mem_coe.1 hj1)) (by rw [he]; exact hφ j2 (Finset.mem_coe.1 hj2))
  · intro k
    induction k with
    | zero =>
      intro x e _
      constructor
      · exact canP_sub n cost S Finset.univ (Finset.subset_univ _) 0 x e
      · rintro ⟨f, hm, hx, _⟩
        exact ⟨f, hm, hx, by simp⟩
    | succ k ih =>
      intro x e he
      constructor
      · exact canP_sub n cost S Finset.univ (Finset.subset_univ _) (k + 1) x e
      · intro h
        by_cases hk : k < n + 1
        · let j : Fin (n + 1) := ⟨k, hk⟩
          by_cases hjS : j ∈ S
          · obtain ⟨f, hm, hx, hs⟩ := h
            rw [sum_succ, sum_eq_in n S j hjS] at hs
            set y := f j with hy
            -- the schedule below level k, capped at y
            let f' : Fin (n + 1) → X := fun i => if i.val ≤ k then f i else y
            have hm' : Monotone f' := by
              intro a b hab
              have hab' : a.val ≤ b.val := hab
              simp only [f']
              split_ifs with h1 h2 h2
              · exact hm hab
              · exact hm (show a ≤ j from (show a.val ≤ k from h1))
              · omega
              · exact le_refl _
            have hx' : ∀ i, f' i ≤ y := by
              intro i
              simp only [f']
              split_ifs with h1
              · exact hm (show i ≤ j from (show i.val ≤ k from h1))
              · exact le_refl _
            have hs' : (S.filter (fun i => i.val < k)).sum (fun i => cost i (f' i)) =
                (S.filter (fun i => i.val < k)).sum (fun i => cost i (f i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have : i.val < k := (Finset.mem_filter.1 hi).2
              simp only [f', if_pos (le_of_lt this)]
            have hlim : limit x ≤ limit y := hanti (hx j)
            obtain ⟨g, hgm, hgx, hgs⟩ := (ih y (e - cost j y) (by omega)).2 ⟨f', hm', hx', by rw [hs']; omega⟩
            let g' : Fin (n + 1) → X := fun i => if i.val < k then g i else y
            have hgm' : Monotone g' := by
              intro a b hab
              have hab' : a.val ≤ b.val := hab
              simp only [g']
              split_ifs with h1 h2 h2
              · exact hgm hab
              · exact hgx a
              · omega
              · exact le_refl _
            refine ⟨g', hgm', ?_, ?_⟩
            · intro i
              simp only [g']
              split_ifs
              · exact le_trans (hgx i) (hx j)
              · exact hx j
            · rw [sum_succ, sum_eq_in n Finset.univ j (Finset.mem_univ _)]
              have e1 : (Finset.univ.filter (fun i : Fin (n + 1) => i.val < k)).sum (fun i => cost i (g' i)) =
                  (Finset.univ.filter (fun i : Fin (n + 1) => i.val < k)).sum (fun i => cost i (g i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                have : i.val < k := (Finset.mem_filter.1 hi).2
                simp only [g', if_pos this]
              have e2 : g' j = y := by simp [g', j]
              rw [e1, e2]
              omega
          · -- the level is dropped: no valid pair is lost there
            have hs0 : canP n cost S k x e := by
              obtain ⟨f, hm, hx, hs⟩ := h
              refine ⟨f, hm, hx, ?_⟩
              rw [sum_succ, sum_eq_out n S k (fun i hi hik => hjS (by rw [show j = i from Fin.ext hik.symm]; exact hi))] at hs
              simpa using hs
            have hu := (ih x e he).2 hs0
            by_contra hno
            exact hjS (Finset.mem_filter.2 ⟨Finset.mem_univ _, x, e, he, hu, hno⟩)
        · -- past the last level nothing changes
          have hsame : ∀ T : Finset (Fin (n + 1)), T.filter (fun i => i.val < k + 1) = T.filter (fun i => i.val < k) := by
            intro T
            ext i
            simp only [Finset.mem_filter]
            have := i.isLt
            constructor
            · rintro ⟨h1, _⟩; exact ⟨h1, by omega⟩
            · rintro ⟨h1, _⟩; exact ⟨h1, by omega⟩
          obtain ⟨f, hm, hx, hs⟩ := h
          rw [hsame] at hs
          obtain ⟨g, hgm, hgx, hgs⟩ := (ih x e he).2 ⟨f, hm, hx, hs⟩
          exact ⟨g, hgm, hgx, by rw [hsame]; exact hgs⟩



namespace R1297

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitBasics

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_eq_of_lt {α : Type*} (l : List α) (i : ℕ) (d1 d2 : α) (hi : i < l.length) :
    l.getD i d1 = l.getD i d2 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma getD_mem {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def Extends (base : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra : List Gate, gs2 = gs1 ++ extra ∧ FanInTwo ⟨extra, 0⟩ ∧
    ReadsBack (base + gs1.length) ⟨extra, 0⟩

lemma Extends.refl (base : ℕ) (gs : List Gate) : Extends base gs gs :=
  ⟨[], by simp, fanInTwo_nil 0, readsBack_nil _ 0⟩

lemma Extends.trans {base : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends base gs1 gs2) (h2 : Extends base gs2 gs3) :
    Extends base gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hf1, hr1⟩
  rcases h2 with ⟨e2, rfl, hf2, hr2⟩
  refine ⟨e1 ++ e2, by rw [List.append_assoc], fanInTwo_append hf1 hf2, ?_⟩
  have hr2' : ReadsBack ((base + gs1.length) + e1.length) ⟨e2, 0⟩ := by
    simpa [List.length_append, Nat.add_assoc] using hr2
  exact readsBack_append hr1 hr2'

lemma Extends.length_le {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _, _⟩; simp

lemma Extends.wire_eq {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2)
    (w : List Bool) (hw : w.length = base) (i : ℕ) (hi : i < base + gs1.length) :
    (wiresFrom gs2 w).getD i false = (wiresFrom gs1 w).getD i false := by
  rcases h with ⟨e, rfl, _, _⟩
  rw [wiresFrom_append]
  exact wiresFrom_getD_lt e (wiresFrom gs1 w) i (by rw [wiresFrom_length, hw]; exact hi)

def emitAnd (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], base + gs.length)

def emitOr (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], base + gs.length)

def emitNot (base : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], base + gs.length)

lemma emitAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitAnd base gs a b
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

def emitOrList (base : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitOr base gs acc w
    emitOrList base r.1 r.2 ws

lemma emitOrList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate) (acc : ℕ),
      acc < base + gs.length →
      (∀ w ∈ ws, w < base + gs.length) →
      let r := emitOrList base gs acc ws
      Extends base gs r.1 ∧
      r.1.length = gs.length + ws.length ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD r.2 false =
          ((wiresFrom gs v).getD acc false || ws.any (fun w => (wiresFrom gs v).getD w false)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs acc hacc _
    dsimp only [emitOrList]
    refine ⟨Extends.refl base gs, by simp, hacc, rfl, fun v _ => by simp⟩
  | cons w rest ih =>
    intro gs acc hacc hws
    dsimp only [emitOrList]
    have hw_lt : w < base + gs.length := hws w (List.mem_cons_self ..)
    set r1 := emitOr base gs acc w with hr1
    have h1 := emitOr_spec base gs acc w hacc hw_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hrest_lt : ∀ u ∈ rest, u < base + r1.1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem w hu); omega
    have h2 := ih r1.1 r1.2 hlt1 hrest_lt
    dsimp only at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2, hlen1]; omega, hlt2, by omega, ?_⟩
    intro v hv
    rw [hval2 v hv, hval1 v hv]
    have hany : rest.any (fun u => (wiresFrom r1.1 v).getD u false) =
        rest.any (fun u => (wiresFrom gs v).getD u false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, ht⟩
        refine ⟨u, hu, ?_⟩
        rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))] at ht
      · rintro ⟨u, hu, ht⟩
        refine ⟨u, hu, ?_⟩
        rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))]
    rw [hany, List.any_cons, Bool.or_assoc]

def emitAndList (base : ℕ) : List Gate → ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [] => (gs, acc)
  | gs, acc, w :: ws =>
    let r := emitAnd base gs acc w
    emitAndList base r.1 r.2 ws

lemma emitAndList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate) (acc : ℕ),
      acc < base + gs.length →
      (∀ w ∈ ws, w < base + gs.length) →
      let r := emitAndList base gs acc ws
      Extends base gs r.1 ∧
      r.1.length = gs.length + ws.length ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD r.2 false =
          ((wiresFrom gs v).getD acc false && ws.all (fun w => (wiresFrom gs v).getD w false)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs acc hacc _
    dsimp only [emitAndList]
    refine ⟨Extends.refl base gs, by simp, hacc, rfl, fun v _ => by simp⟩
  | cons w rest ih =>
    intro gs acc hacc hws
    dsimp only [emitAndList]
    have hw_lt : w < base + gs.length := hws w (List.mem_cons_self ..)
    set r1 := emitAnd base gs acc w with hr1
    have h1 := emitAnd_spec base gs acc w hacc hw_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hrest_lt : ∀ u ∈ rest, u < base + r1.1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem w hu); omega
    have h2 := ih r1.1 r1.2 hlt1 hrest_lt
    dsimp only at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2, hlen1]; omega, hlt2, by omega, ?_⟩
    intro v hv
    rw [hval2 v hv, hval1 v hv]
    have hall : rest.all (fun u => (wiresFrom r1.1 v).getD u false) =
        rest.all (fun u => (wiresFrom gs v).getD u false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro h u hu
        have := h u hu
        rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))] at this
      · intro h u hu
        have := h u hu
        rwa [hext1.wire_eq v hv u (hws u (List.mem_cons_of_mem w hu))]
    rw [hall, List.all_cons, Bool.and_assoc]

end CircuitBasics

section BitAndNotIndices

noncomputable def notIndices (gs : List Gate) : List ℕ :=
  (List.range gs.length).filter (fun g =>
    @decide ((gs.getD g ⟨GateOp.or, []⟩).op = GateOp.not) (Classical.propDecidable _))

lemma notIndices_nil : notIndices [] = [] := rfl

lemma notIndices_append (gs1 gs2 : List Gate) :
    notIndices (gs1 ++ gs2) = notIndices gs1 ++ (notIndices gs2).map (fun k => gs1.length + k) := by
  dsimp only [notIndices]
  rw [List.length_append, List.range_add, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro g hg
    rw [List.mem_range] at hg
    rw [getD_append_left gs1 gs2 g _ hg]
  · rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro k hk
    rw [List.mem_range] at hk
    simp only [Function.comp_def]
    rw [getD_append_right gs1 gs2 (gs1.length + k) _ (by omega)]
    have : gs1.length + k - gs1.length = k := by omega
    rw [this]

lemma notIndices_eq_nil_of_notCount_zero (gs : List Gate) (hnc : notCount ⟨gs, 0⟩ = 0) :
    notIndices gs = [] := by
  dsimp only [notIndices]
  rw [List.filter_eq_nil_iff]
  intro g hg
  rw [List.mem_range] at hg
  simp only [notCount, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hnc
  have hmem : gs.getD g ⟨GateOp.or, []⟩ ∈ gs := getD_mem gs g _ hg
  have hne : (gs.getD g ⟨GateOp.or, []⟩).op ≠ GateOp.not := by
    intro hEq
    exact hnc _ hmem (by rw [hEq]; simp)
  intro ht
  exact hne ((@decide_eq_true_eq _ (Classical.propDecidable _)).mp ht)

lemma notIndices_append_zero (gs1 gs2 : List Gate) (hnc : notCount ⟨gs2, 0⟩ = 0) :
    notIndices (gs1 ++ gs2) = notIndices gs1 := by
  rw [notIndices_append, notIndices_eq_nil_of_notCount_zero gs2 hnc]
  simp

lemma notIndices_append_not (gs : List Gate) (a : ℕ) :
    notIndices (gs ++ [⟨GateOp.not, [a]⟩]) = notIndices gs ++ [gs.length] := by
  rw [notIndices_append]
  have h1 : notIndices [⟨GateOp.not, [a]⟩] = [0] := by
    dsimp only [notIndices]
    simp only [List.length_singleton, List.range_one, List.filter_cons, List.filter_nil]
    have ht : @decide ((([⟨GateOp.not, [a]⟩] : List Gate).getD 0 ⟨GateOp.or, []⟩).op = GateOp.not)
        (Classical.propDecidable _) = true :=
      (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr rfl
    rw [ht]; rfl
  rw [h1]; simp

lemma list_filter_pairwise_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) (p : ℕ → Bool) :
    (l.filter p).Pairwise (· < ·) :=
  List.Pairwise.filter p hl

lemma notIndices_pairwise_lt (gs : List Gate) : (notIndices gs).Pairwise (· < ·) :=
  list_filter_pairwise_lt List.pairwise_lt_range _

lemma notIndices_strictMono (gs : List Gate) {i j : ℕ} (hi : i < j) (hj : j < (notIndices gs).length) :
    (notIndices gs).getD i gs.length < (notIndices gs).getD j gs.length := by
  have hi' : i < (notIndices gs).length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.pairwise_iff_getElem.mp (notIndices_pairwise_lt gs) i j hi' hj hi

lemma mem_notIndices_iff (gs : List Gate) (g : ℕ) :
    g ∈ notIndices gs ↔ g < gs.length ∧ (gs.getD g ⟨GateOp.or, []⟩).op = GateOp.not := by
  dsimp only [notIndices]
  rw [List.mem_filter, List.mem_range]
  exact and_congr_right fun _ => iff_of_eq (@decide_eq_true_eq _ (Classical.propDecidable _))

lemma nat_lt_of_high_bit {a b k0 : ℕ}
    (hhigh : ∀ k, k0 < k → a.testBit k = b.testBit k)
    (ha : a.testBit k0 = false) (hb : b.testBit k0 = true) : a < b := by
  have hdiv_eq : a / 2 ^ (k0 + 1) = b / 2 ^ (k0 + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact hhigh (i + (k0 + 1)) (by omega)
  have hda : a / 2 ^ k0 = 2 * (a / 2 ^ (k0 + 1)) := by
    have h1 : a / 2 ^ k0 / 2 = a / 2 ^ (k0 + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hmod : (a / 2 ^ k0) % 2 = 0 := by
      have ht : a.testBit k0 = decide (a / 2 ^ k0 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      rw [ha] at ht
      have hne : (a / 2 ^ k0) % 2 ≠ 1 := by
        intro h1'; rw [h1'] at ht; simp at ht
      omega
    omega
  have hdb : b / 2 ^ k0 = 2 * (b / 2 ^ (k0 + 1)) + 1 := by
    have h1 : b / 2 ^ k0 / 2 = b / 2 ^ (k0 + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hmod : (b / 2 ^ k0) % 2 = 1 := by
      have ht : b.testBit k0 = decide (b / 2 ^ k0 % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      rw [hb] at ht
      exact of_decide_eq_true ht.symm
    omega
  have hlt_div : a / 2 ^ k0 < b / 2 ^ k0 := by omega
  have hpos : 0 < 2 ^ k0 := Nat.pow_pos (by omega)
  have ha_lt : a < (a / 2 ^ k0 + 1) * 2 ^ k0 := by
    have hmod : a % 2 ^ k0 < 2 ^ k0 := Nat.mod_lt a hpos
    have hdm := Nat.div_add_mod a (2 ^ k0)
    have hmul : (a / 2 ^ k0 + 1) * 2 ^ k0 = 2 ^ k0 * (a / 2 ^ k0) + 2 ^ k0 := by ring
    omega
  have hb_ge : (a / 2 ^ k0 + 1) * 2 ^ k0 ≤ b := by
    have hle1 : (a / 2 ^ k0 + 1) * 2 ^ k0 ≤ (b / 2 ^ k0) * 2 ^ k0 :=
      Nat.mul_le_mul_right (2 ^ k0) hlt_div
    exact le_trans hle1 (Nat.div_mul_le_self b (2 ^ k0))
  omega

lemma eq_of_testBit_lt_pow {r a b : ℕ} (ha : a < 2 ^ r) (hb : b < 2 ^ r)
    (heq : ∀ k < r, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < r
  · exact heq k hk
  · have hge : r ≤ k := Nat.le_of_not_lt hk
    have ha' : a < 2 ^ k := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge)
    have hb' : b < 2 ^ k := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hge)
    rw [Nat.testBit_lt_two_pow ha', Nat.testBit_lt_two_pow hb']

end BitAndNotIndices

section ForwardProof

def VecLe (w1 w2 : List Bool) : Prop :=
  w1.length = w2.length ∧ ∀ k, w1.getD k false = true → w2.getD k false = true

lemma gateOp_mono {op : GateOp}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    {w1 w2 : List Bool} (hle : VecLe w1 w2) (inputs : List ℕ)
    (ht : op.eval (inputs.map fun i => w1.getD i false) = true) :
    op.eval (inputs.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact hle.2 i (ht _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
    rcases ht with ⟨_, ⟨i, hi, rfl⟩, hti⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle.2 i hti⟩

lemma gateOp_not_antitone {w1 w2 : List Bool} (hle : VecLe w1 w2) (inputs : List ℕ)
    (ht : GateOp.not.eval (inputs.map fun i => w2.getD i false) = true) :
    GateOp.not.eval (inputs.map fun i => w1.getD i false) = true := by
  cases inputs with
  | nil => simp [GateOp.eval]
  | cons u rest =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true'] at ht ⊢
    cases h1 : w1.getD u false
    · rfl
    · have h2 := hle.2 u h1
      rw [h2] at ht; cases ht

lemma vecLe_snoc {w1 w2 : List Bool} (hle : VecLe w1 w2) {b1 b2 : Bool}
    (hb : b1 = true → b2 = true) : VecLe (w1 ++ [b1]) (w2 ++ [b2]) := by
  refine ⟨by simp [hle.1], ?_⟩
  intro k hk
  have hlen12 := hle.1
  by_cases hkl : k < w1.length
  · have hkl2 : k < w2.length := by omega
    rw [getD_append_left _ _ k false hkl] at hk
    rw [getD_append_left _ _ k false hkl2]
    exact hle.2 k hk
  · have hle1 : w1.length ≤ k := Nat.le_of_not_lt hkl
    have hle2 : w2.length ≤ k := by omega
    rw [getD_append_right _ _ k false hle1] at hk
    rw [getD_append_right _ _ k false hle2, ← hle.1]
    by_cases hkeq : k - w1.length = 0
    · rw [hkeq] at hk ⊢
      simp only [List.getD_cons_zero] at hk ⊢
      exact hb hk
    · have hge : 1 ≤ k - w1.length := by omega
      have : ([b1]).getD (k - w1.length) false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
      rw [this] at hk; cases hk

lemma take_succ_eq_append {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]; simp

lemma wires_gate_val (C : Circuit) (w : List Bool) (g : ℕ) (hg : g < C.gates.length) :
    (C.wires w).getD (w.length + g) false =
      (C.gates[g]).op.eval ((C.gates[g]).inputs.map fun i => (wiresFrom (C.gates.take g) w).getD i false) := by
  have hw : wiresFrom C.gates w = wiresFrom (C.gates.drop (g + 1)) (wiresFrom (C.gates.take (g + 1)) w) := by
    rw [← wiresFrom_append, List.take_append_drop]
  change (wiresFrom C.gates w).getD (w.length + g) false = _
  rw [hw]
  have hlen_take : (wiresFrom (C.gates.take (g + 1)) w).length = w.length + (g + 1) := by
    rw [wiresFrom_length, List.length_take]; omega
  rw [wiresFrom_getD_lt _ _ (w.length + g) (by omega)]
  rw [take_succ_eq_append C.gates g hg, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen_g : (wiresFrom (C.gates.take g) w).length = w.length + g := by
    rw [wiresFrom_length, List.length_take]; omega
  rw [getD_append_right _ _ (w.length + g) false (by omega), hlen_g]
  simp

lemma prefix_mono_of_not_le (C : Circuit) (hfit : FanInTwo C)
    {w1 w2 : List Bool} (hle : VecLe w1 w2) :
    ∀ L ≤ C.gates.length,
      (∀ g < L, (C.gates.getD g ⟨GateOp.or, []⟩).op = GateOp.not →
        (C.wires w1).getD (w1.length + g) false = true →
        (C.wires w2).getD (w2.length + g) false = true) →
      VecLe (wiresFrom (C.gates.take L) w1) (wiresFrom (C.gates.take L) w2) := by
  intro L
  induction L with
  | zero => intro _ _; exact hle
  | succ k ih =>
    intro hk hnot
    have hk_lt : k < C.gates.length := by omega
    have hpre : VecLe (wiresFrom (C.gates.take k) w1) (wiresFrom (C.gates.take k) w2) :=
      ih (by omega) (fun g hg => hnot g (by omega))
    rw [take_succ_eq_append C.gates k hk_lt, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
        wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    apply vecLe_snoc hpre
    intro h1
    have hg_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk_lt
    have hop := (hfit C.gates[k] hg_mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor | hnt
    · exact gateOp_mono (Or.inl hand) hpre _ h1
    · exact gateOp_mono (Or.inr hor) hpre _ h1
    · have hget : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
      have h1' : (C.wires w1).getD (w1.length + k) false = true := by
        rw [wires_gate_val C w1 k hk_lt]; exact h1
      have h2' := hnot k (by omega) (by rw [hget]; exact hnt) h1'
      rwa [wires_gate_val C w2 k hk_lt] at h2'

noncomputable def inVec {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun a : Fin n => @decide (a ∈ s) (Classical.propDecidable _)) ++ [false, true]

lemma inVec_len {n : ℕ} (s : Finset (Fin n)) : (inVec s).length = n + 2 := by
  simp [inVec]

lemma inVec_getD_lt {n : ℕ} (s : Finset (Fin n)) (a : Fin n) :
    (inVec s).getD a.val false = @decide (a ∈ s) (Classical.propDecidable _) := by
  dsimp only [inVec]
  rw [getD_append_left _ _ a.val false (by simp)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt]

lemma inVec_getD_z {n : ℕ} (s : Finset (Fin n)) : (inVec s).getD n false = false := by
  dsimp only [inVec]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inVec_getD_o {n : ℕ} (s : Finset (Fin n)) : (inVec s).getD (n + 1) false = true := by
  dsimp only [inVec]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  have : n + 1 - n = 1 := by omega
  simp [this]

lemma vecLe_inVec {n : ℕ} {s1 s2 : Finset (Fin n)} (hsub : s1 ⊆ s2) :
    VecLe (inVec s1) (inVec s2) := by
  refine ⟨by rw [inVec_len, inVec_len], ?_⟩
  intro k hk
  by_cases hkn : k < n
  · rw [inVec_getD_lt s1 ⟨k, hkn⟩] at hk
    rw [inVec_getD_lt s2 ⟨k, hkn⟩]
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr
      (hsub ((@decide_eq_true_eq _ (Classical.propDecidable _)).mp hk))
  · by_cases hk0 : k = n
    · rw [hk0, inVec_getD_z] at hk; cases hk
    · by_cases hk1 : k = n + 1
      · rw [hk1, inVec_getD_o]
      · have hge : (inVec s1).length ≤ k := by rw [inVec_len]; omega
        have : (inVec s1).getD k false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
        rw [this] at hk; cases hk

lemma orderOK_of_fit {n m t r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)} {w : Fin m → Fin t → Bool}
    (C : Circuit) (tap : Fin t → ℕ)
    (hfit : FanInTwo C)
    (hns_len : (notIndices C.gates).length = r)
    (htap : ∀ i a, (C.wires (inVec (x i))).getD (tap a) false = w i a)
    (hnotW : ∀ i (b : Fin r),
      (C.wires (inVec (x i))).getD (n + 2 + (notIndices C.gates).getD b.val C.size) false =
        !((level i).val.testBit (r - 1 - b.val))) :
    ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
      (level i = level j → ∀ a, w i a = true → w j a = true) := by
  intro i j hsub
  have hle_in : VecLe (inVec (x i)) (inVec (x j)) := vecLe_inVec hsub
  by_cases hall : ∀ b : Fin r, (level i).val.testBit (r - 1 - b.val) = (level j).val.testBit (r - 1 - b.val)
  · have hlv_eq : level i = level j := by
      apply Fin.ext
      apply eq_of_testBit_lt_pow (level i).isLt (level j).isLt
      intro k hk
      have hb : r - 1 - k < r := by omega
      have h1 := hall ⟨r - 1 - k, hb⟩
      have h2 : r - 1 - (r - 1 - k) = k := by omega
      rwa [h2] at h1
    refine ⟨by rw [hlv_eq], ?_⟩
    intro _ a hia
    have hpre := prefix_mono_of_not_le C hfit hle_in C.gates.length (le_refl _) (by
      intro g hg hgn h1
      have hmem : g ∈ notIndices C.gates := (mem_notIndices_iff C.gates g).mpr ⟨hg, hgn⟩
      rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      have hidx_r : idx < r := by omega
      have hge : (notIndices C.gates).getD idx C.size = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; exact hget
      rw [inVec_len] at h1 ⊢
      rw [← hge] at h1 ⊢
      rw [hnotW i ⟨idx, hidx_r⟩] at h1
      rw [hnotW j ⟨idx, hidx_r⟩, ← hall ⟨idx, hidx_r⟩]
      exact h1)
    rw [List.take_length] at hpre
    rw [← htap j a]
    exact hpre.2 (tap a) (by change (C.wires (inVec (x i))).getD (tap a) false = true; rw [htap i a]; exact hia)
  · push_neg at hall
    have hex : ∃ b : ℕ, ∃ hb : b < r,
        (level i).val.testBit (r - 1 - b) ≠ (level j).val.testBit (r - 1 - b) := by
      rcases hall with ⟨b, hb⟩; exact ⟨b.val, b.isLt, hb⟩
    let b0 := Nat.find hex
    have hb0_spec := Nat.find_spec hex
    rcases hb0_spec with ⟨hb0_lt, hb0_ne⟩
    have hb0_min : ∀ b < b0, (level i).val.testBit (r - 1 - b) = (level j).val.testBit (r - 1 - b) := by
      intro b hb
      by_contra hne
      exact Nat.find_min hex hb ⟨by omega, hne⟩
    have hb0_ns : b0 < (notIndices C.gates).length := by omega
    set g0 := (notIndices C.gates).getD b0 C.size with hg0
    have hg0_mem : g0 ∈ notIndices C.gates := getD_mem _ b0 C.size hb0_ns
    have hg0_spec := (mem_notIndices_iff C.gates g0).mp hg0_mem
    have hg0_lt : g0 < C.gates.length := hg0_spec.1
    have hg0_op : (C.gates[g0]).op = GateOp.not := by
      have h1 := hg0_spec.2
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg0_lt] at h1
    have hpre : VecLe (wiresFrom (C.gates.take g0) (inVec (x i)))
        (wiresFrom (C.gates.take g0) (inVec (x j))) := by
      apply prefix_mono_of_not_le C hfit hle_in g0 (le_of_lt hg0_lt)
      intro g hg hgn h1
      have hmem : g ∈ notIndices C.gates := (mem_notIndices_iff C.gates g).mpr ⟨by omega, hgn⟩
      rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      have hidx_r : idx < r := by omega
      have hge : (notIndices C.gates).getD idx C.size = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; exact hget
      have hidx_lt : idx < b0 := by
        by_contra hnot_lt
        have hle_b : b0 ≤ idx := Nat.le_of_not_lt hnot_lt
        rcases eq_or_lt_of_le hle_b with rfl | hlt_b
        · rw [← hg0] at hge; omega
        · have := notIndices_strictMono C.gates hlt_b hidx
          change (notIndices C.gates).getD b0 C.size < (notIndices C.gates).getD idx C.size at this
          rw [← hg0, hge] at this; omega
      rw [inVec_len] at h1 ⊢
      rw [← hge] at h1 ⊢
      rw [hnotW i ⟨idx, hidx_r⟩] at h1
      rw [hnotW j ⟨idx, hidx_r⟩, ← hb0_min idx hidx_lt]
      exact h1
    have hanti : (C.wires (inVec (x j))).getD (n + 2 + g0) false = true →
        (C.wires (inVec (x i))).getD (n + 2 + g0) false = true := by
      intro h2
      have hi_val := wires_gate_val C (inVec (x i)) g0 hg0_lt
      have hj_val := wires_gate_val C (inVec (x j)) g0 hg0_lt
      rw [inVec_len] at hi_val hj_val
      rw [hj_val, hg0_op] at h2
      rw [hi_val, hg0_op]
      exact gateOp_not_antitone hpre (C.gates[g0]).inputs h2
    have hwi := hnotW i ⟨b0, hb0_lt⟩
    have hwj := hnotW j ⟨b0, hb0_lt⟩
    rw [← hg0] at hwi hwj
    have hbi : (level i).val.testBit (r - 1 - b0) = false := by
      cases hc1 : (level i).val.testBit (r - 1 - b0)
      · rfl
      · cases hc2 : (level j).val.testBit (r - 1 - b0)
        · have hj1 : (C.wires (inVec (x j))).getD (n + 2 + g0) false = true := by rw [hwj, hc2]; rfl
          have hi1 := hanti hj1
          rw [hwi, hc1] at hi1; cases hi1
        · exact absurd (hc1.trans hc2.symm) hb0_ne
    have hbj : (level j).val.testBit (r - 1 - b0) = true := by
      cases hc2 : (level j).val.testBit (r - 1 - b0)
      · exact absurd (hbi.trans hc2.symm) hb0_ne
      · rfl
    have hlt : (level i).val < (level j).val := by
      apply nat_lt_of_high_bit (k0 := r - 1 - b0) _ hbi hbj
      intro k hk
      by_cases hkr : k < r
      · have hb : r - 1 - k < b0 := by omega
        have h1 := hb0_min (r - 1 - k) hb
        have h2 : r - 1 - (r - 1 - k) = k := by omega
        rwa [h2] at h1
      · have hge : r ≤ k := Nat.le_of_not_lt hkr
        have hi_lt : (level i).val < 2 ^ k := lt_of_lt_of_le (level i).isLt (Nat.pow_le_pow_right (by omega) hge)
        have hj_lt : (level j).val < 2 ^ k := lt_of_lt_of_le (level j).isLt (Nat.pow_le_pow_right (by omega) hge)
        rw [Nat.testBit_lt_two_pow hi_lt, Nat.testBit_lt_two_pow hj_lt]
    refine ⟨le_of_lt hlt, fun heq => by rw [heq] at hlt; omega⟩

end ForwardProof

section Construction

def prefEq {m r : ℕ} (level : Fin m → Fin (2 ^ r)) (k : ℕ) (i j : Fin m) : Prop :=
  ∀ b < k, (level i).val.testBit (r - 1 - b) = (level j).val.testBit (r - 1 - b)

lemma nextBit_of_orderOK {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    {k : ℕ} (hk : k < r) {i j : Fin m}
    (hsub : x i ⊆ x j) (hpref : prefEq level k i j)
    (hi : (level i).val.testBit (r - 1 - k) = true) :
    (level j).val.testBit (r - 1 - k) = true := by
  cases hj : (level j).val.testBit (r - 1 - k)
  · exfalso
    have hlt : (level j).val < (level i).val := by
      apply nat_lt_of_high_bit (k0 := r - 1 - k) _ hj hi
      intro pos hpos
      by_cases hpr : pos < r
      · have hb : r - 1 - pos < k := by omega
        have h1 := (hpref (r - 1 - pos) hb).symm
        have h2 : r - 1 - (r - 1 - pos) = pos := by omega
        rwa [h2] at h1
      · have hge : r ≤ pos := Nat.le_of_not_lt hpr
        have hi_lt : (level i).val < 2 ^ pos := lt_of_lt_of_le (level i).isLt (Nat.pow_le_pow_right (by omega) hge)
        have hj_lt : (level j).val < 2 ^ pos := lt_of_lt_of_le (level j).isLt (Nat.pow_le_pow_right (by omega) hge)
        rw [Nat.testBit_lt_two_pow hj_lt, Nat.testBit_lt_two_pow hi_lt]
    have hle := hord i j hsub
    omega
  · rfl

noncomputable def maskWires {n : ℕ} (s : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (fun a => @decide (a ∈ s) (Classical.propDecidable _))).map (fun a => a.val)

lemma maskWires_len_le {n : ℕ} (s : Finset (Fin n)) : (maskWires s).length ≤ n := by
  dsimp only [maskWires]
  rw [List.length_map]
  exact le_trans (List.length_filter_le _ _) (by simp)

lemma maskWires_lt {n : ℕ} (s : Finset (Fin n)) : ∀ w ∈ maskWires s, w < n + 2 := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨a, _, rfl⟩
  omega

lemma maskWires_all_inVec {n : ℕ} (s t : Finset (Fin n)) :
    (maskWires s).all (fun w => (inVec t).getD w false) = decide (s ⊆ t) := by
  apply Bool.eq_iff_iff.mpr
  dsimp only [maskWires]
  simp only [List.all_map, List.all_eq_true, List.mem_filter, List.mem_finRange, true_and,
    Function.comp_def, decide_eq_true_eq]
  constructor
  · intro h a ha
    have h1 := h a ha
    rw [inVec_getD_lt] at h1
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mp h1
  · intro hsub a ha
    rw [inVec_getD_lt]
    exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr (hsub ha)

noncomputable def buildInitAux (n : ℕ) : List (Finset (Fin n)) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | s :: rest, gs =>
    let r1 := emitAndList (n + 2) gs (n + 1) (maskWires s)
    let r2 := buildInitAux n rest r1.1
    (r2.1, r1.2 :: r2.2)

lemma buildInitAux_spec (n : ℕ) :
    ∀ (ss : List (Finset (Fin n))) (gs : List Gate),
      let r := buildInitAux n ss gs
      Extends (n + 2) gs r.1 ∧
      r.1.length ≤ gs.length + ss.length * n ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = ss.length ∧
      (∀ w ∈ r.2, w < (n + 2) + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < ss.length) (t : Finset (Fin n)),
        (wiresFrom r.1 (inVec t)).getD (r.2.getD idx 0) false = decide (ss[idx] ⊆ t) := by
  intro ss
  induction ss with
  | nil =>
    intro gs
    dsimp only [buildInitAux]
    refine ⟨Extends.refl _ _, by simp, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons s rest ih =>
    intro gs
    dsimp only [buildInitAux]
    set r1 := emitAndList (n + 2) gs (n + 1) (maskWires s) with hr1
    have h1 := emitAndList_spec (n + 2) (maskWires s) gs (n + 1) (by omega)
      (fun w hw => by have := maskWires_lt s w hw; omega)
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    set r2 := buildInitAux n rest r1.1 with hr2
    have h2 := ih r1.1
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨hext2, hlen2, hnc2, hlen_w2, hlt2, hval2⟩
    have hgl2 := hext2.length_le
    have hmw_len := maskWires_len_le s
    refine ⟨hext1.trans hext2, ?_, by omega, by simp [hlen_w2], ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, one_mul]; omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hlt2 w hw'
    · intro idx hidx t
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hext2.wire_eq (inVec t) (inVec_len t) r1.2 hlt1,
            hval1 (inVec t) (inVec_len t),
            wiresFrom_getD_lt gs (inVec t) (n + 1) (by rw [inVec_len]; omega),
            inVec_getD_o, Bool.true_and]
        have hall : (maskWires s).all (fun w => (wiresFrom gs (inVec t)).getD w false) =
            (maskWires s).all (fun w => (inVec t).getD w false) := by
          apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
          constructor <;> intro h w hw
          · have := h w hw; rwa [wiresFrom_getD_lt gs (inVec t) w (by rw [inVec_len]; exact maskWires_lt s w hw)] at this
          · have := h w hw; rwa [wiresFrom_getD_lt gs (inVec t) w (by rw [inVec_len]; exact maskWires_lt s w hw)]
        rw [hall, maskWires_all_inVec]
      | succ idx' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact hval2 idx' (by simp at hidx; omega) t

def updateIndsAux (base notW : ℕ) : List (ℕ × Bool) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | (w, reqBit) :: rest, gs =>
    if reqBit then
      let r2 := updateIndsAux base notW rest gs
      (r2.1, w :: r2.2)
    else
      let r1 := emitAnd base gs w notW
      let r2 := updateIndsAux base notW rest r1.1
      (r2.1, r1.2 :: r2.2)

lemma updateIndsAux_spec (base notW : ℕ) :
    ∀ (items : List (ℕ × Bool)) (gs : List Gate),
      notW < base + gs.length →
      (∀ p ∈ items, p.1 < base + gs.length) →
      let r := updateIndsAux base notW items gs
      Extends base gs r.1 ∧
      r.1.length ≤ gs.length + items.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = items.length ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < items.length) (v : List Bool), v.length = base →
        (wiresFrom r.1 v).getD (r.2.getD idx 0) false =
          if (items[idx]).2 then (wiresFrom gs v).getD (items[idx]).1 false
          else ((wiresFrom gs v).getD (items[idx]).1 false && (wiresFrom gs v).getD notW false) := by
  intro items
  induction items with
  | nil =>
    intro gs _ _
    dsimp only [updateIndsAux]
    refine ⟨Extends.refl _ _, by simp, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons p rest ih =>
    intro gs hnotW hitems
    rcases p with ⟨w, reqBit⟩
    dsimp only [updateIndsAux]
    have hw_lt : w < base + gs.length := hitems (w, reqBit) (List.mem_cons_self ..)
    have hrest_lt : ∀ q ∈ rest, q.1 < base + gs.length := fun q hq => hitems q (List.mem_cons_of_mem _ hq)
    cases reqBit
    · simp only [Bool.false_eq_true, ↓reduceIte]
      set r1 := emitAnd base gs w notW with hr1
      have h1 := emitAnd_spec base gs w notW hw_lt hnotW
      dsimp only at h1; rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
      set r2 := updateIndsAux base notW rest r1.1 with hr2
      have h2 := ih r1.1 (by omega) (fun q hq => by have := hrest_lt q hq; omega)
      dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlen2, hnc2, hlen_w2, hlt2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext1.trans hext2, by simp only [List.length_cons]; omega, by omega, by simp [hlen_w2], ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · exact hlt2 u hu'
      · intro idx hidx v hv
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte]
          rw [hext2.wire_eq v hv r1.2 hlt1, hval1 v hv]
        | succ idx' =>
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          have hidx' : idx' < rest.length := by simp at hidx; omega
          rw [hval2 idx' hidx' v hv]
          have hq := hrest_lt rest[idx'] (List.getElem_mem hidx')
          rw [hext1.wire_eq v hv (rest[idx']).1 hq, hext1.wire_eq v hv notW hnotW]
    · simp only [↓reduceIte]
      set r2 := updateIndsAux base notW rest gs with hr2
      have h2 := ih gs hnotW hrest_lt
      dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlen2, hnc2, hlen_w2, hlt2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext2, by simp only [List.length_cons]; omega, hnc2, by simp [hlen_w2], ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · exact hlt2 u hu'
      · intro idx hidx v hv
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero, ↓reduceIte]
          exact hext2.wire_eq v hv w hw_lt
        | succ idx' =>
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact hval2 idx' (by simp at hidx; omega) v hv

def roundStep (n m r : ℕ) (level : Fin m → Fin (2 ^ r)) (k : ℕ) (st : List Gate × List ℕ) :
    List Gate × List ℕ :=
  let gs := st.1
  let inds := st.2
  let reqs := ((List.finRange m).filter (fun i => (level i).val.testBit (r - 1 - k))).map
    (fun i => inds.getD i.val 0)
  let rU := emitOrList (n + 2) gs n reqs
  let rNot := emitNot (n + 2) rU.1 rU.2
  let items := (List.finRange m).map (fun i => (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)))
  updateIndsAux (n + 2) rNot.2 items rNot.1

def roundLoop (n m r : ℕ) (level : Fin m → Fin (2 ^ r)) :
    ℕ → List Gate × List ℕ → List Gate × List ℕ
  | 0, st => st
  | k + 1, st => roundStep n m r level k (roundLoop n m r level k st)

lemma roundStep_spec {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    (k : ℕ) (hk : k < r) (gs : List Gate) (inds : List ℕ)
    (hnc : notCount ⟨gs, 0⟩ = k)
    (hns_len : (notIndices gs).length = k)
    (hnot_prev : ∀ (j : Fin m) (b : ℕ), b < k →
      (wiresFrom gs (inVec (x j))).getD (n + 2 + (notIndices gs).getD b 0) false =
        !((level j).val.testBit (r - 1 - b)))
    (hinds_len : inds.length = m)
    (hinds_lt : ∀ w ∈ inds, w < (n + 2) + gs.length)
    (hinds_self : ∀ i : Fin m, (wiresFrom gs (inVec (x i))).getD (inds.getD i.val 0) false = true)
    (hinds_sound : ∀ i j : Fin m,
      (wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false = true →
      x i ⊆ x j ∧ prefEq level k i j) :
    let res := roundStep n m r level k (gs, inds)
    Extends (n + 2) gs res.1 ∧
    res.1.length ≤ gs.length + 2 * m + 1 ∧
    notCount ⟨res.1, 0⟩ = k + 1 ∧
    (notIndices res.1).length = k + 1 ∧
    (∀ (j : Fin m) (b : ℕ), b < k + 1 →
      (wiresFrom res.1 (inVec (x j))).getD (n + 2 + (notIndices res.1).getD b 0) false =
        !((level j).val.testBit (r - 1 - b))) ∧
    res.2.length = m ∧
    (∀ w ∈ res.2, w < (n + 2) + res.1.length) ∧
    (∀ i : Fin m, (wiresFrom res.1 (inVec (x i))).getD (res.2.getD i.val 0) false = true) ∧
    (∀ i j : Fin m,
      (wiresFrom res.1 (inVec (x j))).getD (res.2.getD i.val 0) false = true →
      x i ⊆ x j ∧ prefEq level (k + 1) i j) := by
  let reqs := ((List.finRange m).filter (fun i => (level i).val.testBit (r - 1 - k))).map
    (fun i => inds.getD i.val 0)
  have hreqs_len : reqs.length ≤ m := by
    dsimp only [reqs]; rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hreqs_lt : ∀ w ∈ reqs, w < (n + 2) + gs.length := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
    exact hinds_lt _ (getD_mem inds i.val 0 (by omega))
  set rU := emitOrList (n + 2) gs n reqs with hrU
  have hUs := emitOrList_spec (n + 2) reqs gs n (by omega) hreqs_lt
  dsimp only at hUs; rw [← hrU] at hUs
  rcases hUs with ⟨hextU, hlenU, hltU, hncU, hvalU⟩
  set rNot := emitNot (n + 2) rU.1 rU.2 with hrNot
  have hNots := emitNot_spec (n + 2) rU.1 rU.2 hltU
  dsimp only at hNots; rw [← hrNot] at hNots
  rcases hNots with ⟨hextNot, hlenNot, hltNot, hncNot, hvalNot⟩
  let items := (List.finRange m).map (fun i => (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)))
  have hitems_len : items.length = m := by simp [items]
  have hglUN := (hextU.trans hextNot).length_le
  have hitems_lt : ∀ p ∈ items, p.1 < (n + 2) + rNot.1.length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    have := hinds_lt _ (getD_mem inds i.val 0 (by omega))
    omega
  set rUp := updateIndsAux (n + 2) rNot.2 items rNot.1 with hrUp
  have hUps := updateIndsAux_spec (n + 2) rNot.2 items rNot.1 hltNot hitems_lt
  dsimp only at hUps; rw [← hrUp] at hUps
  rcases hUps with ⟨hextUp, hlenUp, hncUp, hlen_wUp, hltUp, hvalUp⟩
  have hstep_eq : roundStep n m r level k (gs, inds) = rUp := rfl
  dsimp only; rw [hstep_eq]
  have hU_eval : ∀ j : Fin m, (wiresFrom rU.1 (inVec (x j))).getD rU.2 false = (level j).val.testBit (r - 1 - k) := by
    intro j
    rw [hvalU (inVec (x j)) (inVec_len _),
        wiresFrom_getD_lt gs (inVec (x j)) n (by rw [inVec_len]; omega),
        inVec_getD_z, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    dsimp only [reqs]
    simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, Function.comp_def]
    constructor
    · rintro ⟨i, hbi, hfi⟩
      rcases hinds_sound i j hfi with ⟨hsub, hpref⟩
      exact nextBit_of_orderOK hord hk hsub hpref hbi
    · intro hbj
      exact ⟨j, hbj, hinds_self j⟩
  have hNot_eval : ∀ j : Fin m,
      (wiresFrom rNot.1 (inVec (x j))).getD rNot.2 false = !((level j).val.testBit (r - 1 - k)) := by
    intro j
    rw [hvalNot (inVec (x j)) (inVec_len _), hU_eval j]
  have hns_U : notIndices rU.1 = notIndices gs := by
    rcases hextU with ⟨eU, heqU, _, _⟩
    have hnc_eU : notCount ⟨eU, 0⟩ = 0 := by
      rw [heqU, notCount_append] at hncU; omega
    rw [heqU]; exact notIndices_append_zero gs eU hnc_eU
  have hns_Not : notIndices rNot.1 = notIndices gs ++ [rU.1.length] := by
    rw [hrNot]; dsimp only [emitNot]
    rw [notIndices_append_not, hns_U]
  have hns_Up : notIndices rUp.1 = notIndices gs ++ [rU.1.length] := by
    rcases hextUp with ⟨eUp, heqUp, _, _⟩
    have hnc_eUp : notCount ⟨eUp, 0⟩ = 0 := by
      rw [heqUp, notCount_append] at hncUp; omega
    rw [heqUp, notIndices_append_zero _ _ hnc_eUp, hns_Not]
  have hextAll : Extends (n + 2) gs rUp.1 := (hextU.trans hextNot).trans hextUp
  have hitem_get : ∀ i : Fin m,
      items[i.val]'(by rw [hitems_len]; exact i.isLt) = (inds.getD i.val 0, (level i).val.testBit (r - 1 - k)) := by
    intro i; simp [items]
  have hUp_eval : ∀ (i j : Fin m),
      (wiresFrom rUp.1 (inVec (x j))).getD (rUp.2.getD i.val 0) false =
        if (level i).val.testBit (r - 1 - k) then
          (wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false
        else
          ((wiresFrom gs (inVec (x j))).getD (inds.getD i.val 0) false &&
            !((level j).val.testBit (r - 1 - k))) := by
    intro i j
    have h1 := hvalUp i.val (by rw [hitems_len]; exact i.isLt) (inVec (x j)) (inVec_len _)
    rw [hitem_get i] at h1
    rw [h1, hNot_eval j, (hextU.trans hextNot).wire_eq (inVec (x j)) (inVec_len _)
      (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))]
  refine ⟨hextAll, by omega, by omega, by rw [hns_Up, List.length_append, hns_len]; simp, ?_,
    by omega, hltUp, ?_, ?_⟩
  · intro j b hb
    rw [hns_Up]
    by_cases hbk : b < k
    · rw [getD_append_left _ _ b 0 (by omega)]
      have hmem : (notIndices gs).getD b 0 ∈ notIndices gs := getD_mem _ b 0 (by omega)
      have hlt_gs : (notIndices gs).getD b 0 < gs.length := ((mem_notIndices_iff gs _).mp hmem).1
      rw [hextAll.wire_eq (inVec (x j)) (inVec_len _) _ (by omega)]
      exact hnot_prev j b hbk
    · have hbeq : b = k := by omega
      rw [hbeq]
      rw [getD_append_right _ _ k 0 (by omega), hns_len, Nat.sub_self, List.getD_cons_zero]
      have hrNot2 : (n + 2) + rU.1.length = rNot.2 := by rw [hrNot]; rfl
      rw [hrNot2, hextUp.wire_eq (inVec (x j)) (inVec_len _) rNot.2 hltNot, hNot_eval j]
  · intro i
    rw [hUp_eval i i, hinds_self i]
    cases (level i).val.testBit (r - 1 - k) <;> rfl
  · intro i j hfire
    rw [hUp_eval i j] at hfire
    cases hbi : (level i).val.testBit (r - 1 - k)
    · simp only [hbi, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hfire
      rcases hinds_sound i j hfire.1 with ⟨hsub, hpref⟩
      refine ⟨hsub, fun b hb => ?_⟩
      by_cases hbk : b < k
      · exact hpref b hbk
      · have hbeq : b = k := by omega
        subst hbeq; rw [hbi, hfire.2]
    · simp only [hbi, ↓reduceIte] at hfire
      rcases hinds_sound i j hfire with ⟨hsub, hpref⟩
      have hbj := nextBit_of_orderOK hord hk hsub hpref hbi
      refine ⟨hsub, fun b hb => ?_⟩
      by_cases hbk : b < k
      · exact hpref b hbk
      · have hbeq : b = k := by omega
        subst hbeq; rw [hbi, hbj]

lemma roundLoop_spec {n m r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val)
    (gs0 : List Gate) (inds0 : List ℕ)
    (hnc0 : notCount ⟨gs0, 0⟩ = 0)
    (hinds0_len : inds0.length = m)
    (hinds0_lt : ∀ w ∈ inds0, w < (n + 2) + gs0.length)
    (hinds0_self : ∀ i : Fin m, (wiresFrom gs0 (inVec (x i))).getD (inds0.getD i.val 0) false = true)
    (hinds0_sound : ∀ i j : Fin m,
      (wiresFrom gs0 (inVec (x j))).getD (inds0.getD i.val 0) false = true → x i ⊆ x j) :
    ∀ k ≤ r,
      let res := roundLoop n m r level k (gs0, inds0)
      Extends (n + 2) gs0 res.1 ∧
      res.1.length ≤ gs0.length + k * (2 * m + 1) ∧
      notCount ⟨res.1, 0⟩ = k ∧
      (notIndices res.1).length = k ∧
      (∀ (j : Fin m) (b : ℕ), b < k →
        (wiresFrom res.1 (inVec (x j))).getD (n + 2 + (notIndices res.1).getD b 0) false =
          !((level j).val.testBit (r - 1 - b))) ∧
      res.2.length = m ∧
      (∀ w ∈ res.2, w < (n + 2) + res.1.length) ∧
      (∀ i : Fin m, (wiresFrom res.1 (inVec (x i))).getD (res.2.getD i.val 0) false = true) ∧
      (∀ i j : Fin m,
        (wiresFrom res.1 (inVec (x j))).getD (res.2.getD i.val 0) false = true →
        x i ⊆ x j ∧ prefEq level k i j) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [roundLoop]
    have hns0 : notIndices gs0 = [] := notIndices_eq_nil_of_notCount_zero gs0 hnc0
    refine ⟨Extends.refl _ _, by simp, hnc0, by rw [hns0]; rfl,
      (fun _ _ h => by cases h), hinds0_len, hinds0_lt, hinds0_self,
      (fun i j h => ⟨hinds0_sound i j h, fun _ hb => by cases hb⟩)⟩
  | succ k ih =>
    intro hkr
    dsimp only [roundLoop]
    set prev := roundLoop n m r level k (gs0, inds0) with hprev
    have hp := ih (by omega)
    dsimp only at hp
    rcases hp with ⟨hextP, hlenP, hncP, hnsP, hnotP, hlen_wP, hltP, hselfP, hsoundP⟩
    have hs := roundStep_spec hord k (by omega) prev.1 prev.2 hncP hnsP hnotP hlen_wP hltP hselfP hsoundP
    dsimp only at hs
    rcases hs with ⟨hextS, hlenS, hncS, hnsS, hnotS, hlen_wS, hltS, hselfS, hsoundS⟩
    refine ⟨hextP.trans hextS, ?_, hncS, hnsS, hnotS, hlen_wS, hltS, hselfS, hsoundS⟩
    have hmul : (k + 1) * (2 * m + 1) = k * (2 * m + 1) + (2 * m + 1) := by ring
    change (roundStep n m r level k (prev.1, prev.2)).1.length ≤ gs0.length + (k + 1) * (2 * m + 1)
    omega

def buildTapsAux (n m : ℕ) (inds : List ℕ) : List (Fin m → Bool) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | f :: rest, gs =>
    let ws := ((List.finRange m).filter f).map (fun i => inds.getD i.val 0)
    let r1 := emitOrList (n + 2) gs n ws
    let r2 := buildTapsAux n m inds rest r1.1
    (r2.1, r1.2 :: r2.2)

lemma buildTapsAux_spec (n m : ℕ) (inds : List ℕ) (hinds_len : inds.length = m) :
    ∀ (fs : List (Fin m → Bool)) (gs : List Gate),
      (∀ w ∈ inds, w < (n + 2) + gs.length) →
      let r := buildTapsAux n m inds fs gs
      Extends (n + 2) gs r.1 ∧
      r.1.length ≤ gs.length + fs.length * m ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      r.2.length = fs.length ∧
      (∀ w ∈ r.2, w < (n + 2) + r.1.length) ∧
      ∀ (idx : ℕ) (hidx : idx < fs.length) (v : List Bool),
        v.length = n + 2 → v.getD n false = false →
        (wiresFrom r.1 v).getD (r.2.getD idx 0) false =
          (List.finRange m).any (fun i => fs[idx] i && (wiresFrom gs v).getD (inds.getD i.val 0) false) := by
  intro fs
  induction fs with
  | nil =>
    intro gs _
    dsimp only [buildTapsAux]
    refine ⟨Extends.refl _ _, by simp, rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons f rest ih =>
    intro gs hinds_lt
    dsimp only [buildTapsAux]
    let ws := ((List.finRange m).filter f).map (fun i => inds.getD i.val 0)
    have hws_len : ws.length ≤ m := by
      dsimp only [ws]; rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    have hws_lt : ∀ w ∈ ws, w < (n + 2) + gs.length := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
      exact hinds_lt _ (getD_mem inds i.val 0 (by omega))
    set r1 := emitOrList (n + 2) gs n ws with hr1
    have h1 := emitOrList_spec (n + 2) ws gs n (by omega) hws_lt
    dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    set r2 := buildTapsAux n m inds rest r1.1 with hr2
    have h2 := ih r1.1 (fun w hw => by have := hinds_lt w hw; omega)
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨hext2, hlen2, hnc2, hlen_w2, hlt2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, ?_, by omega, by simp [hlen_w2], ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, one_mul]; omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · exact hlt2 w hw'
    · intro idx hidx v hv hvz
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hext2.wire_eq v hv r1.2 hlt1, hval1 v hv,
            wiresFrom_getD_lt gs v n (by rw [hv]; omega), hvz, Bool.false_or]
        apply Bool.eq_iff_iff.mpr
        dsimp only [ws]
        simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
          Function.comp_def, Bool.and_eq_true]
      | succ idx' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hidx' : idx' < rest.length := by simp at hidx; omega
        rw [hval2 idx' hidx' v hv hvz]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
        constructor <;> rintro ⟨i, hf, hw⟩ <;> refine ⟨i, hf, ?_⟩
        · rwa [hext1.wire_eq v hv (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))] at hw
        · rwa [hext1.wire_eq v hv (inds.getD i.val 0) (hinds_lt _ (getD_mem inds i.val 0 (by omega)))]

lemma build_of_orderOK {n m t r : ℕ} {x : Fin m → Finset (Fin n)}
    {level : Fin m → Fin (2 ^ r)} {w : Fin m → Fin t → Bool}
    (hord : ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
      (level i = level j → ∀ a, w i a = true → w j a = true)) :
    ∃ (C : Circuit) (tap : Fin t → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      notCount C = r ∧ (notIndices C.gates).length = r ∧
      (∀ a, tap a < n + 2 + C.size) ∧
      (∀ i a, (C.wires (inVec (x i))).getD (tap a) false = w i a) ∧
      (∀ i (b : Fin r), (C.wires (inVec (x i))).getD (n + 2 + (notIndices C.gates).getD b.val C.size) false =
        !((level i).val.testBit (r - 1 - b.val))) ∧
      C.size ≤ m * (n + 2 * r + t) + r := by
  let ss : List (Finset (Fin n)) := (List.finRange m).map x
  have hss_len : ss.length = m := by simp [ss]
  have hss_get : ∀ i : Fin m, ss[i.val]'(by rw [hss_len]; exact i.isLt) = x i := fun i => by simp [ss]
  set r0 := buildInitAux n ss [] with hr0
  have h0 := buildInitAux_spec n ss []
  dsimp only at h0; rw [← hr0] at h0
  rcases h0 with ⟨hext0, hlen0, hnc0, hlen_w0, hlt0, hval0⟩
  simp only [List.length_nil, zero_add, notCount_nil] at hlen0 hnc0
  have h0_self : ∀ i : Fin m, (wiresFrom r0.1 (inVec (x i))).getD (r0.2.getD i.val 0) false = true := by
    intro i
    have h1 := hval0 i.val (by rw [hss_len]; exact i.isLt) (x i)
    rw [hss_get i] at h1; rw [h1]; exact decide_eq_true (Finset.Subset.refl _)
  have h0_sound : ∀ i j : Fin m,
      (wiresFrom r0.1 (inVec (x j))).getD (r0.2.getD i.val 0) false = true → x i ⊆ x j := by
    intro i j hf
    have h1 := hval0 i.val (by rw [hss_len]; exact i.isLt) (x j)
    rw [hss_get i] at h1; rw [h1] at hf
    exact of_decide_eq_true hf
  set rL := roundLoop n m r level r (r0.1, r0.2) with hrL
  have hL := roundLoop_spec (fun i j hs => (hord i j hs).1) r0.1 r0.2 hnc0 (by omega) hlt0 h0_self h0_sound r (le_refl r)
  dsimp only at hL; rw [← hrL] at hL
  rcases hL with ⟨hextL, hlenL, hncL, hnsL, hnotL, hlen_wL, hltL, hselfL, hsoundL⟩
  let fs : List (Fin m → Bool) := (List.finRange t).map (fun a i => w i a)
  have hfs_len : fs.length = t := by simp [fs]
  have hfs_get : ∀ a : Fin t, fs[a.val]'(by rw [hfs_len]; exact a.isLt) = (fun i => w i a) := fun a => by simp [fs]
  set rT := buildTapsAux n m rL.2 fs rL.1 with hrT
  have hT := buildTapsAux_spec n m rL.2 hlen_wL fs rL.1 hltL
  dsimp only at hT; rw [← hrT] at hT
  rcases hT with ⟨hextT, hlenT, hncT, hlen_wT, hltT, hvalT⟩
  have hextAll : Extends (n + 2) [] rT.1 := (hext0.trans hextL).trans hextT
  rcases hextAll with ⟨e, heq, hfitC, hrbC⟩
  simp only [List.nil_append, List.length_nil, add_zero] at heq hfitC hrbC
  subst heq
  let C : Circuit := ⟨rT.1, 0⟩
  let tap : Fin t → ℕ := fun a => rT.2.getD a.val 0
  have hns_T : notIndices rT.1 = notIndices rL.1 := by
    rcases hextT with ⟨eT, heqT, _, _⟩
    have hnc_eT : notCount ⟨eT, 0⟩ = 0 := by
      rw [heqT, notCount_append] at hncT; omega
    rw [heqT]; exact notIndices_append_zero rL.1 eT hnc_eT
  refine ⟨C, tap, hfitC, hrbC, by dsimp only [C]; omega, by change notCount ⟨rT.1, 0⟩ = r; omega,
    by change (notIndices rT.1).length = r; rw [hns_T]; exact hnsL, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hltT _ (getD_mem rT.2 a.val 0 (by omega))
  · intro j a
    change (wiresFrom rT.1 (inVec (x j))).getD (rT.2.getD a.val 0) false = w j a
    have h1 := hvalT a.val (by rw [hfs_len]; exact a.isLt) (inVec (x j)) (inVec_len _) (inVec_getD_z _)
    rw [hfs_get a] at h1
    rw [h1]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
    constructor
    · rintro ⟨i, hwia, hfi⟩
      rcases hsoundL i j hfi with ⟨hsub, hpref⟩
      have hlv : level i = level j := by
        apply Fin.ext
        apply eq_of_testBit_lt_pow (level i).isLt (level j).isLt
        intro pos hpos
        have h1' := hpref (r - 1 - pos) (by omega)
        have h2' : r - 1 - (r - 1 - pos) = pos := by omega
        rwa [h2'] at h1'
      exact (hord i j hsub).2 hlv a hwia
    · intro hwja
      exact ⟨j, hwja, hselfL j⟩
  · intro j b
    change (wiresFrom rT.1 (inVec (x j))).getD (n + 2 + (notIndices rT.1).getD b.val rT.1.length) false = _
    rw [hns_T, getD_eq_of_lt (notIndices rL.1) b.val rT.1.length 0 (by omega)]
    have hmem : (notIndices rL.1).getD b.val 0 ∈ notIndices rL.1 := getD_mem _ b.val 0 (by omega)
    have hlt_g : (notIndices rL.1).getD b.val 0 < rL.1.length := ((mem_notIndices_iff rL.1 _).mp hmem).1
    rw [hextT.wire_eq (inVec (x j)) (inVec_len _) _ (by omega)]
    exact hnotL j b.val b.isLt
  · change rT.1.length ≤ m * (n + 2 * r + t) + r
    rw [hss_len] at hlen0
    rw [hfs_len] at hlenT
    have hmul : m * n + r * (2 * m + 1) + t * m = m * (n + 2 * r + t) + r := by ring
    omega

lemma main_bridge :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m t r : Nat) (x : Fin m → Finset (Fin n)) (level : Fin m → Fin (2^r))
      (w : Fin m → Fin t → Bool),
      let orderOK := ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
        (level i = level j → ∀ a, w i a = true → w j a = true)
      let fit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
        let ns := (List.range C.size).filter (fun g =>
          decide ((C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
            PEqualNP.CircuitLowerBounds.GateOp.not))
        let atWire := fun (i : Fin m) (p : Nat) =>
          (C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true])).getD p false
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C = r ∧ ns.length = r ∧
        (∀ a, tap a < n+2+C.size) ∧ (∀ i a, atWire i (tap a) = w i a) ∧
        ∀ i (b : Fin r), atWire i (n+2+ns.getD b.val C.size) =
          !((level i).val.testBit (r-1-b.val))
      ((∃ C tap, fit C tap) ↔ orderOK) ∧
        (orderOK → ∃ C tap, fit C tap ∧ C.size ≤ m*(n+2*r+t)+r) := by
  intro n m t r x level w
  dsimp only
  have hbuild : (∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
      (level i = level j → ∀ a, w i a = true → w j a = true)) →
      ∃ (C : Circuit) (tap : Fin t → ℕ),
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
          notCount C = r ∧ (notIndices C.gates).length = r ∧
          (∀ a, tap a < n + 2 + C.size) ∧
          (∀ i a, (C.wires (inVec (x i))).getD (tap a) false = w i a) ∧
          ∀ i (b : Fin r), (C.wires (inVec (x i))).getD (n + 2 + (notIndices C.gates).getD b.val C.size) false =
            !((level i).val.testBit (r - 1 - b.val))) ∧
        C.size ≤ m * (n + 2 * r + t) + r := by
    intro hord
    rcases build_of_orderOK hord with ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8, hsz⟩
    exact ⟨C, tap, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hsz⟩
  refine ⟨⟨?_, ?_⟩, hbuild⟩
  · rintro ⟨C, tap, h1, _, _, _, h5, _, h7, h8⟩
    exact orderOK_of_fit C tap h1 h5 h7 h8
  · intro hord
    rcases hbuild hord with ⟨C, tap, hfit, _⟩
    exact ⟨C, tap, hfit⟩

end Construction

end R1297

theorem r1297 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t r : Nat) (x : Fin m → Finset (Fin n)) (level : Fin m → Fin (2^r))
  (w : Fin m → Fin t → Bool),
  let orderOK := ∀ i j, x i ⊆ x j → (level i).val ≤ (level j).val ∧
    (level i = level j → ∀ a, w i a = true → w j a = true)
  let fit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
    let ns := (List.range C.size).filter (fun g =>
      decide ((C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
        PEqualNP.CircuitLowerBounds.GateOp.not))
    let atWire := fun (i : Fin m) (p : Nat) =>
      (C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true])).getD p false
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C = r ∧ ns.length = r ∧
    (∀ a, tap a < n+2+C.size) ∧ (∀ i a, atWire i (tap a) = w i a) ∧
    ∀ i (b : Fin r), atWire i (n+2+ns.getD b.val C.size) =
      !((level i).val.testBit (r-1-b.val))
  ((∃ C tap, fit C tap) ↔ orderOK) ∧
    (orderOK → ∃ C tap, fit C tap ∧ C.size ≤ m*(n+2*r+t)+r) :=
  PEqualNP.Outside.L_meta_53175.R1297.main_bridge



/-! Prefix masks, ranked states and the link between fitting circuits and monotone schedules. -/

noncomputable def mask (n t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < t)

theorem pre_eq (n t : ℕ) :
    (List.ofFn (fun j : Fin n => decide (j.val < t)) ++ [false, true]) = inw n (mask n t) := by
  unfold inw mask
  congr 1
  congr 1
  funext j
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mask_mono (n : ℕ) {t t' : ℕ} (h : t ≤ t') : mask n t ⊆ mask n t' := by
  intro j hj
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  omega

theorem mask_le (n t t' : ℕ) (ht : t ≤ n) (h : mask n t ⊆ mask n t') : t ≤ t' := by
  by_contra hc
  push_neg at hc
  have hm : (⟨t', by omega⟩ : Fin n) ∈ mask n t := by
    simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
  have := h hm
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and] at this
  omega

abbrev LX (B a : ℕ) : Type := Fin (2 ^ B) × (Fin a → Bool)

/-- Ranked copies of the output cube: first the rank, then the output word. -/
def lxPre (B a : ℕ) : Preorder (LX B a) where
  le p q := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)
  lt p q := (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) ∧ ¬ (q.1 < p.1 ∨ (q.1 = p.1 ∧ q.2 ≤ p.2))
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl p := Or.inr ⟨rfl, le_refl _⟩
  le_trans p q r h1 h2 := by
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (e2 ▸ h1)
    · exact Or.inl (e1 ▸ h2)
    · exact Or.inr ⟨e1.trans e2, le_trans h1 h2⟩

theorem lx_le_iff (B a : ℕ) (p q : LX B a) :
    @LE.le _ (lxPre B a).toLE p q ↔ (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) := Iff.rfl

def fitP (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S : Finset (Fin (n + 1))) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → ℕ),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false, true])).getD (tap i) false)) ≤ e

theorem fitP_sub (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S T : Finset (Fin (n + 1)))
    (hST : S ⊆ T) (h : fitP a n b e cost T) : fitP a n b e cost S := by
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, tap, h1, h2, h3, h4, h5, le_trans (Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)) h6⟩

theorem fitP_e (a n b e e' : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S : Finset (Fin (n + 1)))
    (he : e ≤ e') (h : fitP a n b e cost S) : fitP a n b e' cost S := by
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, tap, h1, h2, h3, h4, h5, le_trans h6 he⟩

theorem fitP_b (a n b b' e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S : Finset (Fin (n + 1)))
    (hb : b ≤ b') (h : fitP a n b e cost S) : fitP a n b' e cost S := by
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, tap, h1, h2, le_trans h3 hb, h4, h5, h6⟩

theorem bval_comp (b : ℕ → Bool) : ∀ G : List ℕ, bval G (fun j => !b j) + bval G b = 2 ^ G.length - 1
  | [] => by simp [bval]
  | a :: G => by
    have ih := bval_comp b G
    rw [bval_cons, bval_cons]
    have hp : 1 ≤ 2 ^ G.length := Nat.one_le_two_pow
    simp only [List.length_cons, pow_succ]
    cases b a <;> simp <;> omega

theorem link (n a B b : ℕ) (hb : b ≤ B) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) (e : ℕ) :
    fitP a n b e cost T ↔ ∃ f : Fin (n + 1) → LX B a, @Monotone _ _ _ (lxPre B a) f ∧
      (∀ i, (f i).1.val < 2 ^ b) ∧ T.sum (fun t => cost t (f t).2) ≤ e := by
  constructor
  · rintro ⟨C, tap, hfan, hrb, hnc, _, _, hs⟩
    have hgl : (gatesF C).length = PEqualNP.NotBracket.notCount C := gatesF_len C
    let rk : ℕ → ℕ := fun t => bval (gatesF C) (fun j => !Wv n C (mask n t) (n + 2 + j))
    have hrk_lt : ∀ t, rk t < 2 ^ PEqualNP.NotBracket.notCount C := by
      intro t; have := bval_lt (fun j => !Wv n C (mask n t) (n + 2 + j)) (gatesF C); rwa [hgl] at this
    have hrB : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (le_trans hnc hb)
    have hrb' : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hnc
    have hsig : ∀ t, rk t + sigF n C (mask n t) = 2 ^ (gatesF C).length - 1 := fun t =>
      bval_comp (fun j => Wv n C (mask n t) (n + 2 + j)) (gatesF C)
    have hrk_mono : ∀ t t', t ≤ t' → rk t ≤ rk t' := by
      intro t t' h
      have h1 := (coreF n C hfan hrb (mask n t) (mask n t') (mask_mono n h)).1
      have e1 := hsig t; have e2 := hsig t'
      omega
    let f : Fin (n + 1) → LX B a := fun t =>
      (⟨rk t.val, lt_of_lt_of_le (hrk_lt _) hrB⟩, fun i => Wv n C (mask n t.val) (tap i))
    refine ⟨f, ?_, fun i => lt_of_lt_of_le (hrk_lt _) hrb', ?_⟩
    · intro t t' htt
      have htt' : t.val ≤ t'.val := htt
      rw [lx_le_iff]
      rcases lt_or_eq_of_le (hrk_mono _ _ htt') with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Fin.ext h, fun i => ?_⟩
        have hs1 : sigF n C (mask n t.val) = sigF n C (mask n t'.val) := by
          have e1 := hsig t.val; have e2 := hsig t'.val; omega
        exact mono n C hfan hrb (mask n t.val) (mask n t'.val) (mask_mono n htt') (tap i)
          (fun q hq _ hn => bval_inj _ _ (gatesF C) hs1 q ((mem_gatesF C q).2 ⟨hq, hn⟩))
    · refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) hs
      congr 1
      funext i
      rw [pre_eq]
      rfl
  · rintro ⟨f, hfm, hfb, hs⟩
    have h97 := r1297 n (n + 1) a b (fun t => mask n t.val) (fun t => ⟨(f t).1.val, hfb t⟩) (fun t => (f t).2)
    obtain ⟨C, tap, hfit⟩ := h97.1.2 (by
      intro t t' hsub
      have htt : t ≤ t' := (mask_le n t.val t'.val (by omega) hsub : t.val ≤ t'.val)
      have hle := (lx_le_iff B a _ _).1 (hfm htt)
      rcases hle with hl | ⟨he, hw⟩
      · refine ⟨le_of_lt hl, fun heq => ?_⟩
        exfalso
        have : (f t).1.val = (f t').1.val := Fin.mk.inj_iff.1 heq
        exact absurd this (ne_of_lt hl)
      · refine ⟨by show (f t).1.val ≤ (f t').1.val; rw [he], fun _ i hi => ?_⟩
        have := hw i
        revert this hi
        cases (f t).2 i <;> cases (f t').2 i <;> simp)
    obtain ⟨hfan, hrb, hout, hnc, _, htap, hw, _⟩ := hfit
    refine ⟨C, tap, hfan, hrb, le_of_eq hnc, hout, htap, ?_⟩
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) hs
    congr 1
    funext i
    rw [pre_eq]
    exact hw t i

theorem link0 (n b : ℕ) (cost : Fin (n + 1) → (Fin 0 → Bool) → ℕ) (T : Finset (Fin (n + 1))) (e : ℕ) :
    fitP 0 n b e cost T ↔ T.sum (fun t => cost t (fun i => i.elim0)) ≤ e := by
  have hw : ∀ w : Fin 0 → Bool, w = (fun i => i.elim0) := fun w => funext (fun i => i.elim0)
  constructor
  · rintro ⟨C, tap, _, _, _, _, _, hs⟩
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) hs
    congr 1; funext i; exact i.elim0
  · intro hs
    refine ⟨⟨[], 0⟩, fun i => i.elim0, ?_, ?_, ?_, ?_, fun i => i.elim0, ?_⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · show (List.filter _ []).length ≤ b; simp
    · show 0 < n + 2 + 0; omega
    · refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) hs
      congr 1; funext i; exact i.elim0

/-- The least budget-`b` loss, capped at `E+1`. -/
noncomputable def qf (n a E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨E + 1, Or.inr rfl⟩ : ∃ e, fitP a n b e cost Finset.univ ∨ e = E + 1)

theorem qf_le (n a E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b : ℕ) : qf n a E cost b ≤ E + 1 := by
  classical
  unfold qf
  exact Nat.find_min' _ (Or.inr rfl)

theorem qf_iff (n a E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b e : ℕ) (he : e ≤ E) :
    fitP a n b e cost Finset.univ ↔ qf n a E cost b ≤ e := by
  classical
  constructor
  · intro h; unfold qf; exact Nat.find_min' _ (Or.inl h)
  · intro h
    have hs := Nat.find_spec (⟨E + 1, Or.inr rfl⟩ : ∃ e, fitP a n b e cost Finset.univ ∨ e = E + 1)
    have hq : qf n a E cost b = Nat.find (⟨E + 1, Or.inr rfl⟩ : ∃ e, fitP a n b e cost Finset.univ ∨ e = E + 1) := rfl
    rcases hs with hs | hs
    · rw [← hq] at hs; exact fitP_e a n b _ e cost _ h hs
    · rw [← hq] at hs; omega

theorem qf_anti (n a E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (b b' : ℕ) (hb : b ≤ b') :
    qf n a E cost b' ≤ qf n a E cost b := by
  classical
  have hs := Nat.find_spec (⟨E + 1, Or.inr rfl⟩ : ∃ e, fitP a n b e cost Finset.univ ∨ e = E + 1)
  have hq : qf n a E cost b = Nat.find (⟨E + 1, Or.inr rfl⟩ : ∃ e, fitP a n b e cost Finset.univ ∨ e = E + 1) := rfl
  rw [← hq] at hs
  unfold qf
  rcases hs with hs | hs
  · exact Nat.find_min' _ (Or.inl (fitP_b a n b b' _ cost _ hb hs))
  · exact Nat.find_min' _ (Or.inr hs)

theorem size_band (B l : ℕ) (h1 : 2 ^ B ≤ l) (h2 : l < 2 ^ (B + 1)) : Nat.size l = B + 1 := by
  apply le_antisymm
  · exact Nat.size_le.2 h2
  · exact Nat.lt_size.2 h1

theorem size_top (b : ℕ) : Nat.size (2 ^ b - 1) = b := by
  rcases b with _ | b
  · simp
  · apply size_band b
    · have : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
      have := Nat.one_le_two_pow (n := b); omega
    · have := Nat.one_le_two_pow (n := b + 1); omega

theorem band_sum (g : ℕ → ℕ) : ∀ B : ℕ,
    (Finset.range (2 ^ B)).sum (fun l => g (Nat.size l)) = g 0 + (Finset.range B).sum (fun j => 2 ^ j * g (j + 1))
  | 0 => by simp
  | B + 1 => by
    have ih := band_sum g B
    have hle : 2 ^ B ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih, Finset.sum_range_succ]
    have hI : (Finset.Ico (2 ^ B) (2 ^ (B + 1))).sum (fun l => g (Nat.size l)) = 2 ^ B * g (B + 1) := by
      have hc : ∀ l ∈ Finset.Ico (2 ^ B) (2 ^ (B + 1)), g (Nat.size l) = g (B + 1) := by
        intro l hl
        rw [Finset.mem_Ico] at hl
        rw [size_band B l hl.1 hl.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      congr 1
      rw [pow_succ]; omega
    rw [hI]; ring

end PEqualNP.Outside.L_meta_53175

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_53175 in
theorem PEqualNP.Outside.L_meta_53175 :
let fit := fun (a n b e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
    (S : Finset (Fin (n+1))) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
∀ (n a B E : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat),
  ∃ (q : Nat → Nat) (S : Finset (Fin (n+1))),
    S.card ≤ (if a = 0 then q 0 else 2^a *
      (q 0 + (Finset.range B).sum (fun j => 2^j * q (j+1)))) ∧
    ∀ b ≤ B, q b ≤ E+1 ∧ ∀ e ≤ E,
      (fit a n b e cost Finset.univ ↔ q b ≤ e) ∧
      ∀ k : Nat, fit a n b e cost (Finset.univ.filter (fun t => t.val < k)) ↔
        fit a n b e cost (S.filter (fun t => t.val < k)) := by
  intro fit n a B E cost
  classical
  by_cases ha : a = 0
  · subst ha
    have hqb : ∀ b, qf n 0 E cost b = qf n 0 E cost 0 := by
      intro b
      apply le_antisymm
      · by_cases h0 : qf n 0 E cost 0 ≤ E
        · have hf := (qf_iff n 0 E cost 0 _ h0).2 le_rfl
          exact (qf_iff n 0 E cost b _ h0).1 ((link0 n b cost _ _).2 ((link0 n 0 cost _ _).1 hf))
        · have := qf_le n 0 E cost b; have := qf_le n 0 E cost 0; omega
      · by_cases h0 : qf n 0 E cost b ≤ E
        · have hf := (qf_iff n 0 E cost b _ h0).2 le_rfl
          exact (qf_iff n 0 E cost 0 _ h0).1 ((link0 n 0 cost _ _).2 ((link0 n b cost _ _).1 hf))
        · have := qf_le n 0 E cost b; have := qf_le n 0 E cost 0; omega
    obtain ⟨S, hS, hkey⟩ := key Unit (fun _ => qf n 0 E cost 0) (fun _ _ _ => le_rfl) n
      (fun t _ => cost t (fun i => i.elim0))
    refine ⟨qf n 0 E cost, S, ?_, fun b _ => ⟨qf_le n 0 E cost b, fun e he => ⟨qf_iff n 0 E cost b e he, fun k => ?_⟩⟩⟩
    · rw [if_pos rfl]; simpa using hS
    · by_cases hqe : qf n 0 E cost b ≤ e
      · have hu := (qf_iff n 0 E cost b e he).2 hqe
        exact ⟨fun _ => fitP_sub _ _ _ _ _ _ _ (Finset.subset_univ _) hu,
          fun _ => fitP_sub _ _ _ _ _ _ _ (Finset.subset_univ _) hu⟩
      · have hlt : e < qf n 0 E cost 0 := by rw [← hqb b]; omega
        have h1 := hkey k () e hlt
        have tr : ∀ T : Finset (Fin (n + 1)), fit 0 n b e cost (T.filter (fun t => t.val < k)) ↔
            canP n (fun t _ => cost t (fun i => i.elim0)) T k () e := by
          intro T
          show fitP 0 n b e cost (T.filter (fun t => t.val < k)) ↔ _
          rw [link0]
          constructor
          · intro h; exact ⟨fun _ => (), fun _ _ _ => le_rfl, fun _ => le_rfl, h⟩
          · rintro ⟨f, _, _, h⟩; exact h
        rw [tr, tr]; exact h1
  · let limit : LX B a → ℕ := fun p => qf n a E cost (Nat.size p.1.val)
    have hanti : @Antitone _ _ (lxPre B a) _ limit := by
      intro p p' hpp
      have : p.1.val ≤ p'.1.val := by
        rcases (lx_le_iff B a p p').1 hpp with h | ⟨h, _⟩
        · exact le_of_lt h
        · rw [h]
      exact qf_anti n a E cost _ _ (Nat.size_le_size this)
    obtain ⟨S, hS, hkey⟩ := @key (LX B a) (lxPre B a) _ limit hanti n (fun t p => cost t p.2)
    have hsum : Finset.univ.sum limit =
        2 ^ a * (qf n a E cost 0 + (Finset.range B).sum (fun j => 2 ^ j * qf n a E cost (j + 1))) := by
      rw [Fintype.sum_prod_type]
      simp only [limit, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun l => qf n a E cost (Nat.size l)) (2 ^ B), band_sum]
    refine ⟨qf n a E cost, S, ?_, fun b hb => ⟨qf_le n a E cost b, fun e he => ⟨qf_iff n a E cost b e he, fun k => ?_⟩⟩⟩
    · rw [if_neg ha, ← hsum]; exact hS
    · by_cases hqe : qf n a E cost b ≤ e
      · have hu := (qf_iff n a E cost b e he).2 hqe
        exact ⟨fun _ => fitP_sub _ _ _ _ _ _ _ (Finset.subset_univ _) hu,
          fun _ => fitP_sub _ _ _ _ _ _ _ (Finset.subset_univ _) hu⟩
      · have hpb : 2 ^ b ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hb
        have h1b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        let top : LX B a := (⟨2 ^ b - 1, by omega⟩, fun _ => true)
        have hlim : limit top = qf n a E cost b := by
          show qf n a E cost (Nat.size (2 ^ b - 1)) = _; rw [size_top]
        have h1 := hkey k top e (by rw [hlim]; omega)
        have htop : ∀ p : LX B a, @LE.le _ (lxPre B a).toLE p top ↔ p.1.val < 2 ^ b := by
          intro p
          rw [lx_le_iff]
          constructor
          · rintro (h | ⟨h, _⟩)
            · have : p.1.val < 2 ^ b - 1 := h; omega
            · have : p.1.val = 2 ^ b - 1 := congrArg Fin.val h; omega
          · intro h
            by_cases h' : p.1.val < 2 ^ b - 1
            · exact Or.inl h'
            · exact Or.inr ⟨Fin.ext (by show p.1.val = 2 ^ b - 1; omega), fun i => Bool.le_true _⟩
        have tr : ∀ T : Finset (Fin (n + 1)), fit a n b e cost (T.filter (fun t => t.val < k)) ↔
            @canP (LX B a) (lxPre B a) n (fun t p => cost t p.2) T k top e := by
          intro T
          show fitP a n b e cost (T.filter (fun t => t.val < k)) ↔ _
          rw [link n a B b hb]
          constructor
          · rintro ⟨f, hm, hb', hs⟩; exact ⟨f, hm, fun i => (htop (f i)).2 (hb' i), hs⟩
          · rintro ⟨f, hm, hb', hs⟩; exact ⟨f, hm, fun i => (htop (f i)).1 (hb' i), hs⟩
        rw [tr, tr]; exact h1
