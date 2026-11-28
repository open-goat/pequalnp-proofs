import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_694_aux

private abbrev W (k : ℕ) := Fin k → Bool
private abbrev Lit (k : ℕ) := Fin k × Bool
private abbrev F (k : ℕ) := Finset (Lit k × Lit k)

private def mass (n : ℕ) (A : F n) : ℕ :=
  (Finset.univ.filter (fun z : W n => ∀ e ∈ A,
    z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2)).card

private abbrev Ty (c : ℕ) := Finset (Lit c × Bool)

private def choices {c : ℕ} (t : Ty c) (w : W c) : ℕ :=
  (Finset.univ.filter (fun b : Bool => ∀ edge ∈ t,
    w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2)).card

private def width {c : ℕ} (h : Ty c → ℕ) : ℕ :=
  c + ∑ t, h t

private def fiber {c : ℕ} (D : F c) (h : Ty c → ℕ) (w : W c) : ℕ :=
  if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then
    ∏ t, (choices t w) ^ (h t)
  else 0

private def score {c : ℕ} (D : F c) (h : Ty c → ℕ) : ℕ :=
  ∑ w : W c, fiber D h w

private def vars {m : ℕ} (e : Lit m × Lit m) : Finset (Fin m) :=
  {e.1.1, e.2.1}

private def nonVac {m : ℕ} (e : Lit m × Lit m) : Prop :=
  ¬(e.1.1 = e.2.1 ∧ e.1.2 ≠ e.2.2)

private lemma mass_pad {n m : ℕ} (hnm : n ≤ m) (A : F n) :
    let emb : Lit n × Lit n → Lit m × Lit m :=
      fun e => ((Fin.castLE hnm e.1.1, e.1.2), (Fin.castLE hnm e.2.1, e.2.2))
    mass m (A.image emb) = mass n A * 2 ^ (m - n) := by
  intro emb
  classical
  let eW : W m ≃ W n × (Fin (m - n) → Bool) :=
    { toFun := fun z => (fun i => z (Fin.castLE hnm i), fun j => z ⟨n + j.val, by omega⟩)
      invFun := fun p k => if hk : k.val < n then p.1 ⟨k.val, hk⟩ else p.2 ⟨k.val - n, by omega⟩
      left_inv := by
        intro z; funext k; dsimp only
        split_ifs with hk
        · rfl
        · congr 1; ext; dsimp only; omega
      right_inv := by
        rintro ⟨z1, z2⟩
        refine Prod.ext ?_ ?_
        · funext i; dsimp only; simp [i.isLt]
        · funext j; dsimp only
          have hnot : ¬(n + j.val < n) := by omega
          simp only [hnot, ↓reduceDIte]
          congr 1; ext; dsimp only; omega }
  have hiff : ∀ z : W m,
      (∀ e ∈ A.image emb, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2) ↔
      (∀ e ∈ A, (eW z).1 e.1.1 ≠ e.1.2 ∨ (eW z).1 e.2.1 ≠ e.2.2) := by
    intro z
    constructor
    · intro hz e he
      exact hz (emb e) (Finset.mem_image_of_mem emb he)
    · intro hz e' he'
      rcases Finset.mem_image.mp he' with ⟨e, he, rfl⟩
      exact hz e he
  let eSub : {z : W m // ∀ e ∈ A.image emb, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} ≃
      {z : W n // ∀ e ∈ A, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} × (Fin (m - n) → Bool) :=
    { toFun := fun z => (⟨(eW z.val).1, (hiff z.val).mp z.property⟩, (eW z.val).2)
      invFun := fun p => ⟨eW.symm (p.1.val, p.2), (hiff _).mpr (by simpa using p.1.property)⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by rintro ⟨⟨z1, hz1⟩, z2⟩; apply Prod.ext <;> simp }
  have hcard := Fintype.card_congr eSub
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have hL : Fintype.card {z : W m // ∀ e ∈ A.image emb, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} =
      mass m (A.image emb) := by
    rw [Fintype.card_subtype]; rfl
  have hR : Fintype.card {z : W n // ∀ e ∈ A, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} =
      mass n A := by
    rw [Fintype.card_subtype]; rfl
  rw [hL, hR] at hcard
  exact hcard

private lemma mass_eq_score_of_cover {c m : ℕ}
    (C : Finset (Fin m)) (eC : Fin c ≃ {v : Fin m // v ∈ C})
    (A : F m) (D : F c) (τ : {v : Fin m // v ∉ C} → Ty c) (h : Ty c → ℕ)
    (hcnt : ∀ t : Ty c, (Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t)).card = h t)
    (hsat : ∀ z : W m,
      (∀ e ∈ A, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2) ↔
      ((∀ e ∈ D, z (eC e.1.1).val ≠ e.1.2 ∨ z (eC e.2.1).val ≠ e.2.2) ∧
        ∀ v : {v : Fin m // v ∉ C}, ∀ edge ∈ τ v,
          z (eC edge.1.1).val ≠ edge.1.2 ∨ z v.val ≠ edge.2)) :
    mass m A = score D h := by
  classical
  let eSplit : W m ≃ W c × ({v : Fin m // v ∉ C} → Bool) :=
    { toFun := fun z => (fun i => z (eC i).val, fun v => z v.val)
      invFun := fun p u => if hu : u ∈ C then p.1 (eC.symm ⟨u, hu⟩) else p.2 ⟨u, hu⟩
      left_inv := by
        intro z; funext u; dsimp only
        split_ifs with hu
        · have : (eC (eC.symm ⟨u, hu⟩)).val = u := by simp
          rw [this]
        · rfl
      right_inv := by
        rintro ⟨w, y⟩
        refine Prod.ext ?_ ?_
        · funext i; dsimp only
          have hi : (eC i).val ∈ C := (eC i).property
          simp only [hi, ↓reduceDIte]
          have : eC.symm ⟨(eC i).val, hi⟩ = i := by simp
          rw [this]
        · funext v; dsimp only
          have hv : v.val ∉ C := v.property
          simp only [hv, ↓reduceDIte] }
  let P (w : W c) : Prop := ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2
  let Q (w : W c) (y : {v : Fin m // v ∉ C} → Bool) : Prop :=
    ∀ v : {v : Fin m // v ∉ C}, ∀ edge ∈ τ v, w edge.1.1 ≠ edge.1.2 ∨ y v ≠ edge.2
  let eSig : {z : W m // ∀ e ∈ A, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} ≃
      Σ w : W c, {y : {v : Fin m // v ∉ C} → Bool // P w ∧ Q w y} :=
    { toFun := fun z =>
        ⟨(eSplit z.val).1, ⟨(eSplit z.val).2, (hsat z.val).mp z.property⟩⟩
      invFun := fun s =>
        ⟨eSplit.symm (s.1, s.2.val), (hsat _).mpr (by
          have h1 : ∀ i : Fin c, eSplit.symm (s.1, s.2.val) (eC i).val = s.1 i := by
            intro i
            have := congrFun (congrArg Prod.fst (eSplit.apply_symm_apply (s.1, s.2.val))) i
            exact this
          have h2 : ∀ v : {v : Fin m // v ∉ C}, eSplit.symm (s.1, s.2.val) v.val = s.2.val v := by
            intro v
            have := congrFun (congrArg Prod.snd (eSplit.apply_symm_apply (s.1, s.2.val))) v
            exact this
          refine ⟨?_, ?_⟩
          · intro e he; rw [h1, h1]; exact s.2.property.1 e he
          · intro v edge hedge; rw [h1, h2]; exact s.2.property.2 v edge hedge)⟩
      left_inv := by intro z; apply Subtype.ext; exact eSplit.symm_apply_apply z.val
      right_inv := by
        rintro ⟨w, ⟨y, hy⟩⟩
        have hfn : ∀ (p q : W c × ({v : Fin m // v ∉ C} → Bool))
            (hp : P p.1 ∧ Q p.1 p.2) (hq : P q.1 ∧ Q q.1 q.2),
            p = q → (⟨p.1, ⟨p.2, hp⟩⟩ : Σ w : W c, {y // P w ∧ Q w y}) = ⟨q.1, ⟨q.2, hq⟩⟩ := by
          rintro p _ hp hq rfl; rfl
        exact hfn _ (w, y) _ hy (eSplit.apply_symm_apply (w, y)) }
  have hcard : mass m A = ∑ w : W c, Fintype.card {y : {v : Fin m // v ∉ C} → Bool // P w ∧ Q w y} := by
    have hL : Fintype.card {z : W m // ∀ e ∈ A, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2} = mass m A := by
      rw [Fintype.card_subtype]; rfl
    rw [← hL, Fintype.card_congr eSig, Fintype.card_sigma]
  rw [hcard]
  unfold score
  refine Finset.sum_congr rfl ?_
  intro w _
  unfold fiber
  by_cases hPw : ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2
  · have hite : (if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then ∏ t, (choices t w) ^ (h t) else 0) =
        ∏ t, (choices t w) ^ (h t) := by split_ifs; rfl
    rw [hite]
    let ePi : {y : {v : Fin m // v ∉ C} → Bool // P w ∧ Q w y} ≃
        ∀ v : {v : Fin m // v ∉ C}, {b : Bool // ∀ edge ∈ τ v, w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2} :=
      { toFun := fun y v => ⟨y.val v, y.property.2 v⟩
        invFun := fun f => ⟨fun v => (f v).val, ⟨hPw, fun v => (f v).property⟩⟩
        left_inv := by intro y; apply Subtype.ext; rfl
        right_inv := by intro f; funext v; apply Subtype.ext; rfl }
    rw [Fintype.card_congr ePi, Fintype.card_pi]
    have hch : ∀ v : {v : Fin m // v ∉ C},
        Fintype.card {b : Bool // ∀ edge ∈ τ v, w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2} =
        choices (τ v) w := by
      intro v; rw [Fintype.card_subtype]; rfl
    simp_rw [hch]
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := (Finset.univ : Finset (Ty c)))
      (g := τ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.prod_congr rfl ?_
    intro t _
    have heq : ∏ v ∈ Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t), choices (τ v) w =
        ∏ _v ∈ Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t), choices t w := by
      refine Finset.prod_congr rfl ?_
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    rw [heq, Finset.prod_const, hcnt t]
  · have hite : (if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then ∏ t, (choices t w) ^ (h t) else 0) = 0 := by
      split_ifs; rfl
    rw [hite]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun y => hPw y.property.1⟩

private lemma four_pow_gt (a p : ℕ) (hp : 3 * (a + 1) ≤ p) : 3 ^ p * 2 ^ a < 4 ^ p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  induction k with
  | zero =>
    simp only [Nat.add_zero]
    have h1 : 3 ^ (3 * (a + 1)) * 2 ^ a = 27 * 54 ^ a := by
      have ha : 3 ^ (3 * (a + 1)) = 27 * 27 ^ a := by
        rw [Nat.mul_add, Nat.pow_add, Nat.pow_mul]; norm_num; ring
      have hb : 27 ^ a * 2 ^ a = 54 ^ a := by
        rw [← Nat.mul_pow]
      calc 3 ^ (3 * (a + 1)) * 2 ^ a = 27 * (27 ^ a * 2 ^ a) := by rw [ha]; ring
        _ = 27 * 54 ^ a := by rw [hb]
    have h2 : 4 ^ (3 * (a + 1)) = 64 * 64 ^ a := by
      rw [Nat.mul_add, Nat.pow_add, Nat.pow_mul]; norm_num; ring
    rw [h1, h2]
    have h54 : 54 ^ a ≤ 64 ^ a := Nat.pow_le_pow_left (by omega) a
    have hpos : 0 < 64 ^ a := Nat.pos_of_ne_zero (by positivity)
    nlinarith
  | succ k ih =>
    have hih := ih (by omega)
    have hstep : 3 * (a + 1) + (k + 1) = (3 * (a + 1) + k) + 1 := by omega
    rw [hstep, Nat.pow_succ, Nat.pow_succ]
    calc 3 ^ (3 * (a + 1) + k) * 3 * 2 ^ a
        = 3 * (3 ^ (3 * (a + 1) + k) * 2 ^ a) := by ring
      _ < 3 * 4 ^ (3 * (a + 1) + k) := Nat.mul_lt_mul_of_pos_left hih (by omega)
      _ ≤ 4 ^ (3 * (a + 1) + k) * 4 := by omega

private lemma mass_mono {m : ℕ} {P Q : F m} (hPQ : P ⊆ Q) : mass m Q ≤ mass m P := by
  unfold mass
  refine Finset.card_le_card ?_
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact fun e he => hz e (hPQ he)

private lemma four_mul_mass_insert_le {m : ℕ} (P : F m) (e : Lit m × Lit m)
    (hnv : nonVac e) (hdisj : Disjoint (vars e) (P.biUnion vars)) :
    4 * mass m (insert e P) ≤ 3 * mass m P := by
  classical
  let S : Finset (W m) := Finset.univ.filter (fun z : W m => ∀ cl ∈ P, z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2)
  have hS_card : S.card = mass m P := rfl
  have hnotP : ∀ cl ∈ P, cl.1.1 ≠ e.1.1 ∧ cl.2.1 ≠ e.1.1 ∧ cl.1.1 ≠ e.2.1 ∧ cl.2.1 ≠ e.2.1 := by
    intro cl hcl
    have h1 : e.1.1 ∉ P.biUnion vars := Finset.disjoint_left.mp hdisj (by simp [vars])
    have h2 : e.2.1 ∉ P.biUnion vars := Finset.disjoint_left.mp hdisj (by simp [vars])
    have hc1 : cl.1.1 ∈ P.biUnion vars := Finset.mem_biUnion.mpr ⟨cl, hcl, by simp [vars]⟩
    have hc2 : cl.2.1 ∈ P.biUnion vars := Finset.mem_biUnion.mpr ⟨cl, hcl, by simp [vars]⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq; rw [heq] at hc1; exact h1 hc1
    · intro heq; rw [heq] at hc2; exact h1 hc2
    · intro heq; rw [heq] at hc1; exact h2 hc1
    · intro heq; rw [heq] at hc2; exact h2 hc2
  by_cases huv : e.1.1 = e.2.1
  · have hb : e.1.2 = e.2.2 := by
      by_contra hne; exact hnv ⟨huv, hne⟩
    let u := e.1.1
    let b := e.1.2
    let S0 := S.filter (fun z => z u = !b)
    let S1 := S.filter (fun z => z u = b)
    have hIns : Finset.univ.filter (fun z : W m => ∀ cl ∈ insert e P, z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2) = S0 := by
      ext z
      simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
      constructor
      · rintro ⟨he, hP⟩
        refine ⟨hP, ?_⟩
        have hne : z u ≠ b := by
          rcases he with h1 | h2
          · exact h1
          · rwa [← huv, ← hb] at h2
        cases hzu : z u <;> cases hb' : b <;> simp_all
      · rintro ⟨hP, hzu⟩
        refine ⟨Or.inl ?_, hP⟩
        change z u ≠ b
        rw [hzu]; cases hb' : b <;> simp
    have hpart : S0.card + S1.card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext z; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h; cases z u <;> cases b <;> simp [h]
      · rw [Finset.disjoint_left]
        intro z hz0 hz1
        have h0 := (Finset.mem_filter.mp hz0).2
        have h1 := (Finset.mem_filter.mp hz1).2
        rw [h0] at h1; cases hb' : b <;> simp [hb'] at h1
    have hbij : S0.card = S1.card := by
      refine Finset.card_bij (fun z _ => Function.update z u b) ?_ ?_ ?_
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, _⟩
        refine Finset.mem_filter.mpr ⟨?_, by simp⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS ⊢
        intro cl hcl
        have hn := hnotP cl hcl
        rw [Function.update_of_ne hn.1, Function.update_of_ne hn.2.1]
        exact hzS cl hcl
      · intro z1 hz1 z2 hz2 heq
        have h1 := (Finset.mem_filter.mp hz1).2
        have h2 := (Finset.mem_filter.mp hz2).2
        funext i
        by_cases hi : i = u
        · subst hi; rw [h1, h2]
        · have := congrFun heq i
          rwa [Function.update_of_ne hi, Function.update_of_ne hi] at this
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, hzu⟩
        refine ⟨Function.update z u (!b), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨?_, by simp⟩
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS ⊢
          intro cl hcl
          have hn := hnotP cl hcl
          rw [Function.update_of_ne hn.1, Function.update_of_ne hn.2.1]
          exact hzS cl hcl
        · funext i
          by_cases hi : i = u
          · subst hi; simp [hzu]
          · simp [Function.update_of_ne hi]
    have hmc : mass m (insert e P) = S0.card := by
      unfold mass; rw [hIns]
    omega
  · let u := e.1.1
    let v := e.2.1
    let b1 := e.1.2
    let b2 := e.2.2
    let piece (x y : Bool) : Finset (W m) := S.filter (fun z => z u = x ∧ z v = y)
    have hpeq : ∀ x y : Bool, (piece x y).card = (piece b1 b2).card := by
      intro x y
      refine Finset.card_bij (fun z _ => Function.update (Function.update z u b1) v b2) ?_ ?_ ?_
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, _⟩
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS ⊢
          intro cl hcl
          have hn := hnotP cl hcl
          rw [Function.update_of_ne hn.2.2.1, Function.update_of_ne hn.1,
              Function.update_of_ne hn.2.2.2, Function.update_of_ne hn.2.1]
          exact hzS cl hcl
        · exact ⟨by rw [Function.update_of_ne huv, Function.update_self], by rw [Function.update_self]⟩
      · intro z1 hz1 z2 hz2 heq
        rcases (Finset.mem_filter.mp hz1).2 with ⟨h1u, h1v⟩
        rcases (Finset.mem_filter.mp hz2).2 with ⟨h2u, h2v⟩
        funext i
        by_cases hiv : i = v
        · subst hiv; rw [h1v, h2v]
        · by_cases hiu : i = u
          · subst hiu; rw [h1u, h2u]
          · have := congrFun heq i
            rwa [Function.update_of_ne hiv, Function.update_of_ne hiu,
                 Function.update_of_ne hiv, Function.update_of_ne hiu] at this
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, hzu, hzv⟩
        refine ⟨Function.update (Function.update z u x) v y, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS ⊢
            intro cl hcl
            have hn := hnotP cl hcl
            rw [Function.update_of_ne hn.2.2.1, Function.update_of_ne hn.1,
                Function.update_of_ne hn.2.2.2, Function.update_of_ne hn.2.1]
            exact hzS cl hcl
          · exact ⟨by rw [Function.update_of_ne huv, Function.update_self], by rw [Function.update_self]⟩
        · funext i
          by_cases hiv : i = v
          · subst hiv; simp [hzv]
          · by_cases hiu : i = u
            · subst hiu; rw [Function.update_of_ne huv, Function.update_self, hzu]
            · simp [Function.update_of_ne hiv, Function.update_of_ne hiu]
    have hsum : S.card = ∑ p : Bool × Bool, (piece p.1 p.2).card := by
      have hbi : S = (Finset.univ : Finset (Bool × Bool)).biUnion (fun p => piece p.1 p.2) := by
        ext z
        simp only [piece, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun hz => ⟨(z u, z v), hz, rfl, rfl⟩, fun ⟨_, hz, _, _⟩ => hz⟩
      conv_lhs => rw [hbi]
      rw [Finset.card_biUnion]
      intro p1 _ p2 _ hne
      change Disjoint (piece p1.1 p1.2) (piece p2.1 p2.2)
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rcases (Finset.mem_filter.mp hz1).2 with ⟨h1u, h1v⟩
      rcases (Finset.mem_filter.mp hz2).2 with ⟨h2u, h2v⟩
      exact hne (Prod.ext (h1u.symm.trans h2u) (h1v.symm.trans h2v))
    have h4 : S.card = 4 * (piece b1 b2).card := by
      rw [hsum]
      have : ∀ p : Bool × Bool, (piece p.1 p.2).card = (piece b1 b2).card := fun p => hpeq p.1 p.2
      simp_rw [this]
      simp
    have hIns : Finset.univ.filter (fun z : W m => ∀ cl ∈ insert e P, z cl.1.1 ≠ cl.1.2 ∨ z cl.2.1 ≠ cl.2.2) =
        S \ piece b1 b2 := by
      ext z
      simp only [piece, S, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, forall_eq_or_imp, not_and]
      constructor
      · rintro ⟨he, hP⟩
        refine ⟨hP, fun _ hzu hzv => ?_⟩
        rcases he with h1 | h2
        · exact h1 hzu
        · exact h2 hzv
      · rintro ⟨hP, hnot⟩
        refine ⟨?_, hP⟩
        by_cases hzu : z u = b1
        · right; exact fun hzv => hnot hP hzu hzv
        · left; exact hzu
    have hsub : piece b1 b2 ⊆ S := Finset.filter_subset _ _
    have hmc : mass m (insert e P) = S.card - (piece b1 b2).card := by
      unfold mass; rw [hIns, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    omega

private lemma packing_bound {m : ℕ} (P : F m)
    (hnv : ∀ e ∈ P, nonVac e)
    (hdisj : ∀ e1 ∈ P, ∀ e2 ∈ P, e1 ≠ e2 → Disjoint (vars e1) (vars e2)) :
    4 ^ P.card * mass m P ≤ 3 ^ P.card * 2 ^ m := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, pow_zero, one_mul]
    have : mass m ∅ = 2 ^ m := by
      unfold mass
      simp [Fintype.card_bool, Fintype.card_fin]
    omega
  | @insert e P heP ih =>
    have hnvP : ∀ cl ∈ P, nonVac cl := fun cl hcl => hnv cl (Finset.mem_insert_of_mem hcl)
    have hdisjP : ∀ e1 ∈ P, ∀ e2 ∈ P, e1 ≠ e2 → Disjoint (vars e1) (vars e2) :=
      fun e1 h1 e2 h2 hne => hdisj e1 (Finset.mem_insert_of_mem h1) e2 (Finset.mem_insert_of_mem h2) hne
    have hih := ih hnvP hdisjP
    have hde : Disjoint (vars e) (P.biUnion vars) := by
      rw [Finset.disjoint_biUnion_right]
      intro cl hcl
      refine hdisj e (Finset.mem_insert_self e P) cl (Finset.mem_insert_of_mem hcl) ?_
      intro heq; subst heq; exact heP hcl
    have hstep := four_mul_mass_insert_le P e (hnv e (Finset.mem_insert_self e P)) hde
    rw [Finset.card_insert_of_notMem heP, Nat.pow_succ, Nat.pow_succ]
    calc 4 ^ P.card * 4 * mass m (insert e P)
        = 4 ^ P.card * (4 * mass m (insert e P)) := by ring
      _ ≤ 4 ^ P.card * (3 * mass m P) := Nat.mul_le_mul_left _ hstep
      _ = 3 * (4 ^ P.card * mass m P) := by ring
      _ ≤ 3 * (3 ^ P.card * 2 ^ m) := Nat.mul_le_mul_left _ hih
      _ = 3 ^ P.card * 3 * 2 ^ m := by ring

private lemma count_flatMap_replicate {α : Type*} [DecidableEq α]
    (l : List α) (h : α → ℕ) (hnd : l.Nodup) (t : α) :
    (l.flatMap (fun x => List.replicate (h x) x)).count t = if t ∈ l then h t else 0 := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.count_append, ih hnd.2, List.count_replicate]
    by_cases hta : t = a
    · subst hta
      simp [hnd.1]
    · have hat : a ≠ t := Ne.symm hta
      simp [hta, hat]

private lemma card_fin_getElem_eq {α : Type*} [DecidableEq α] (L : List α) (t : α) :
    (Finset.univ.filter (fun i : Fin L.length => L[i] = t)).card = L.count t := by
  classical
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.count_cons]
    let e : Fin (a :: tl).length ≃ Option (Fin tl.length) :=
      finSuccEquiv tl.length
    have hcard : (Finset.univ.filter (fun i : Fin (a :: tl).length => (a :: tl)[i] = t)).card =
        (Finset.univ.filter (fun o : Option (Fin tl.length) =>
          match o with | none => a = t | some j => tl[j] = t)).card := by
      refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
      · intro i hi
        have hval := (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        induction i using Fin.cases with
        | zero => simp [e, finSuccEquiv]; exact hval
        | succ j => simp [e, finSuccEquiv]; exact hval
      · intro i1 _ i2 _ heq; exact e.injective heq
      · intro o ho
        have hval := (Finset.mem_filter.mp ho).2
        refine ⟨e.symm o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply o⟩
        cases o with
        | none => simp [e, finSuccEquiv]; exact hval
        | some j => simp [e, finSuccEquiv]; exact hval
    rw [hcard]
    have hsplit : (Finset.univ.filter (fun o : Option (Fin tl.length) =>
        match o with | none => a = t | some j => tl[j] = t)).card =
        (if a = t then 1 else 0) + (Finset.univ.filter (fun j : Fin tl.length => tl[j] = t)).card := by
      let S1 := Finset.univ.filter (fun o : Option (Fin tl.length) =>
        match o with | none => a = t | some j => tl[j] = t)
      let Snone := S1.filter (fun o => o.isNone)
      let Ssome := S1.filter (fun o => o.isSome)
      have hdisj : Disjoint Snone Ssome := by
        rw [Finset.disjoint_left]; intro o h1 h2
        have a1 := (Finset.mem_filter.mp h1).2
        have a2 := (Finset.mem_filter.mp h2).2
        cases o <;> simp at a1 a2
      have hunion : S1 = Snone ∪ Ssome := by
        ext o; simp only [Snone, Ssome, Finset.mem_union, Finset.mem_filter]
        cases o <;> simp
      change S1.card = _
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      congr 1
      · by_cases hat : a = t
        · have : Snone = {none} := by
            ext o; simp only [Snone, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            cases o <;> simp [hat]
          rw [this, Finset.card_singleton]; simp only [hat, ↓reduceIte]
        · have : Snone = ∅ := by
            ext o; simp only [Snone, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            cases o <;> simp [hat]
          rw [this, Finset.card_empty]; simp only [hat, ↓reduceIte]
      · refine Finset.card_bij (fun o ho => match o, ho with | some j, _ => j | none, ho => absurd (Finset.mem_filter.mp ho).2 (by simp)) ?_ ?_ ?_
        · intro o ho
          rcases Finset.mem_filter.mp ho with ⟨h1, h2⟩
          cases o with
          | none => simp at h2
          | some j =>
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h1).2⟩
        · intro o1 ho1 o2 ho2 heq
          have h1 := (Finset.mem_filter.mp ho1).2
          have h2 := (Finset.mem_filter.mp ho2).2
          cases o1 <;> cases o2 <;> simp at h1 h2 heq ⊢
          exact heq
        · intro j hj
          refine ⟨some j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, rfl⟩, rfl⟩
    rw [hsplit, ih]
    by_cases hat : a = t <;> simp [hat, Nat.add_comm]

private lemma part1 (a : ℕ) :
    let c := 6 * (a + 1)
    ∀ (n : ℕ) (A : F n), 2 ^ n ≤ 2 ^ a * mass n A →
      ∃ (D : F c) (h : Ty c → ℕ),
        width h = max c n ∧
        mass n A * 2 ^ (width h) = score D h * 2 ^ n := by
  classical
  intro c n A hdens
  let m := max c n
  have hnm : n ≤ m := le_max_right c n
  have hcm : c ≤ m := le_max_left c n
  let emb : Lit n × Lit n → Lit m × Lit m :=
    fun e => ((Fin.castLE hnm e.1.1, e.1.2), (Fin.castLE hnm e.2.1, e.2.2))
  let A' : F m := A.image emb
  have hmass_pad : mass m A' = mass n A * 2 ^ (m - n) := mass_pad hnm A
  have hdens' : 2 ^ m ≤ 2 ^ a * mass m A' := by
    have hm_eq : m = n + (m - n) := by omega
    conv_lhs => rw [hm_eq, Nat.pow_add]
    rw [hmass_pad]
    calc 2 ^ n * 2 ^ (m - n) ≤ (2 ^ a * mass n A) * 2 ^ (m - n) :=
          Nat.mul_le_mul_right _ hdens
      _ = 2 ^ a * (mass n A * 2 ^ (m - n)) := by ring
  let Aeff : F m := A'.filter (fun e => nonVac e)
  have hmass_eff : mass m Aeff = mass m A' := by
    unfold mass
    congr 1; ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz e he
      by_cases hnv : nonVac e
      · exact hz e (Finset.mem_filter.mpr ⟨he, hnv⟩)
      · unfold nonVac at hnv; push Not at hnv
        rcases hnv with ⟨h1, h2⟩
        rw [← h1]
        by_cases hze : z e.1.1 = e.1.2
        · right; intro hze2; exact h2 (hze.symm.trans hze2)
        · left; exact hze
    · intro hz e he
      exact hz e (Finset.mem_filter.mp he).1
  let valid (Q : F m) : Prop :=
    Q ⊆ Aeff ∧ ∀ e1 ∈ Q, ∀ e2 ∈ Q, e1 ≠ e2 → Disjoint (vars e1) (vars e2)
  let cands : Finset (F m) := Aeff.powerset.filter valid
  have hne : cands.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
    ⟨Finset.empty_subset _, by simp⟩⟩⟩
  obtain ⟨P, hPmem, hPmax⟩ := Finset.exists_max_image cands Finset.card hne
  have hPval : valid P := (Finset.mem_filter.mp hPmem).2
  let U : Finset (Fin m) := P.biUnion vars
  have hcover : ∀ e ∈ Aeff, e.1.1 ∈ U ∨ e.2.1 ∈ U := by
    intro e he
    by_contra hnot
    push Not at hnot
    have heP : e ∉ P := by
      intro hmem
      exact hnot.1 (Finset.mem_biUnion.mpr ⟨e, hmem, by simp [vars]⟩)
    have hdisj_e : ∀ cl ∈ P, Disjoint (vars e) (vars cl) := by
      intro cl hcl
      rw [Finset.disjoint_left]
      intro x hx hxcl
      have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨cl, hcl, hxcl⟩
      simp only [vars, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hnot.1 hxU
      · exact hnot.2 hxU
    have hins : insert e P ∈ cands := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨he, hPval.1⟩),
        ⟨Finset.insert_subset_iff.mpr ⟨he, hPval.1⟩, ?_⟩⟩
      intro e1 h1 e2 h2 hne12
      rcases Finset.mem_insert.mp h1 with rfl | h1' <;> rcases Finset.mem_insert.mp h2 with rfl | h2'
      · exact absurd rfl hne12
      · exact hdisj_e e2 h2'
      · exact (hdisj_e e1 h1').symm
      · exact hPval.2 e1 h1' e2 h2' hne12
    have hle := hPmax (insert e P) hins
    rw [Finset.card_insert_of_notMem heP] at hle
    omega
  have hPcard_lt : P.card < 3 * (a + 1) := by
    by_contra hge
    push Not at hge
    have hnvP : ∀ e ∈ P, nonVac e := fun e he => (Finset.mem_filter.mp (hPval.1 he)).2
    have hpb := packing_bound P hnvP hPval.2
    have hle_m : mass m Aeff ≤ mass m P := mass_mono hPval.1
    have hpos : 0 < mass m Aeff := by
      by_contra h0
      have hz : mass m Aeff = 0 := by omega
      rw [← hmass_eff, hz, Nat.mul_zero] at hdens'
      have : 0 < 2 ^ m := Nat.pos_of_ne_zero (by positivity)
      omega
    have h1 : 4 ^ P.card * mass m Aeff ≤ 3 ^ P.card * 2 ^ a * mass m Aeff := by
      calc 4 ^ P.card * mass m Aeff
          ≤ 4 ^ P.card * mass m P := Nat.mul_le_mul_left _ hle_m
        _ ≤ 3 ^ P.card * 2 ^ m := hpb
        _ ≤ 3 ^ P.card * (2 ^ a * mass m Aeff) := by
            rw [hmass_eff]; exact Nat.mul_le_mul_left _ hdens'
        _ = 3 ^ P.card * 2 ^ a * mass m Aeff := by ring
    have h2 : 4 ^ P.card ≤ 3 ^ P.card * 2 ^ a := Nat.le_of_mul_le_mul_right h1 hpos
    have h3 : 3 ^ P.card * 2 ^ a < 4 ^ P.card := four_pow_gt a P.card hge
    omega
  have hU_le : U.card ≤ c := by
    have h1 : U.card ≤ ∑ e ∈ P, (vars e).card := Finset.card_biUnion_le
    have h2 : ∑ e ∈ P, (vars e).card ≤ ∑ _e ∈ P, 2 := by
      refine Finset.sum_le_sum ?_
      intro e _
      exact Finset.card_le_two
    rw [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hexC : ∃ C : Finset (Fin m), U ⊆ C ∧ C.card = c := by
    have hrem : c - U.card ≤ (Finset.univ \ U).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hrem
    refine ⟨U ∪ B, Finset.subset_union_left, ?_⟩
    have hdisjUB : Disjoint U B := by
      rw [Finset.disjoint_left]
      intro x hxU hxB
      exact (Finset.mem_sdiff.mp (hBsub hxB)).2 hxU
    rw [Finset.card_union_of_disjoint hdisjUB, hBcard]
    omega
  obtain ⟨C, hUC, hCcard⟩ := hexC
  have hcard_sub : Fintype.card {v : Fin m // v ∈ C} = c := by
    rw [Fintype.card_coe]; exact hCcard
  let eC : Fin c ≃ {v : Fin m // v ∈ C} :=
    (Fintype.equivFinOfCardEq hcard_sub).symm
  let D : F c := Finset.univ.filter (fun e : Lit c × Lit c =>
    (( (eC e.1.1).val, e.1.2 ), ( (eC e.2.1).val, e.2.2 )) ∈ Aeff)
  let τ : {v : Fin m // v ∉ C} → Ty c := fun v =>
    Finset.univ.filter (fun edge : Lit c × Bool =>
      (( (eC edge.1.1).val, edge.1.2 ), (v.val, edge.2)) ∈ Aeff ∨
      ((v.val, edge.2), ( (eC edge.1.1).val, edge.1.2 )) ∈ Aeff)
  let h : Ty c → ℕ := fun t =>
    (Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t)).card
  have hwidth : width h = m := by
    unfold width
    have hsum : ∑ t : Ty c, h t = Fintype.card {v : Fin m // v ∉ C} := by
      have := Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset {v : Fin m // v ∉ C}))
        (t := (Finset.univ : Finset (Ty c))) (g := τ)
      simpa [h] using this
    have hcard_out : Fintype.card {v : Fin m // v ∉ C} = m - c := by
      have : Fintype.card {v : Fin m // v ∉ C} = (Finset.univ \ C).card := by
        rw [Fintype.card_subtype]; congr 1; ext v; simp
      rw [this, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hCcard]
    omega
  have hsat : ∀ z : W m,
      (∀ e ∈ Aeff, z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2) ↔
      ((∀ e ∈ D, z (eC e.1.1).val ≠ e.1.2 ∨ z (eC e.2.1).val ≠ e.2.2) ∧
        ∀ v : {v : Fin m // v ∉ C}, ∀ edge ∈ τ v,
          z (eC edge.1.1).val ≠ edge.1.2 ∨ z v.val ≠ edge.2) := by
    intro z
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro e he
        exact hz _ (Finset.mem_filter.mp he).2
      · intro v edge hedge
        rcases (Finset.mem_filter.mp hedge).2 with h1 | h2
        · exact hz _ h1
        · exact (hz _ h2).symm
    · rintro ⟨hD, hT⟩ e he
      by_cases h1 : e.1.1 ∈ C
      · by_cases h2 : e.2.1 ∈ C
        · let i1 := eC.symm ⟨e.1.1, h1⟩
          let i2 := eC.symm ⟨e.2.1, h2⟩
          have hi1 : (eC i1).val = e.1.1 := by simp [i1]
          have hi2 : (eC i2).val = e.2.1 := by simp [i2]
          have hmemD : ((i1, e.1.2), (i2, e.2.2)) ∈ D := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            simpa [hi1, hi2] using he
          have res := hD ((i1, e.1.2), (i2, e.2.2)) hmemD
          simpa [hi1, hi2] using res
        · let i1 := eC.symm ⟨e.1.1, h1⟩
          have hi1 : (eC i1).val = e.1.1 := by simp [i1]
          let v : {v : Fin m // v ∉ C} := ⟨e.2.1, h2⟩
          have hmemT : ((i1, e.1.2), e.2.2) ∈ τ v := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
            simpa [hi1, v] using he
          have res := hT v ((i1, e.1.2), e.2.2) hmemT
          simpa [hi1, v] using res
      · have h2 : e.2.1 ∈ C := by
          rcases hcover e he with hc1 | hc2
          · exact absurd (hUC hc1) h1
          · exact hUC hc2
        let i2 := eC.symm ⟨e.2.1, h2⟩
        have hi2 : (eC i2).val = e.2.1 := by simp [i2]
        let v : {v : Fin m // v ∉ C} := ⟨e.1.1, h1⟩
        have hmemT : ((i2, e.2.2), e.1.2) ∈ τ v := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
          simpa [hi2, v] using he
        have res := hT v ((i2, e.2.2), e.1.2) hmemT
        simpa [hi2, v] using res.symm
  have hms : mass m Aeff = score D h :=
    mass_eq_score_of_cover C eC Aeff D τ h (fun _ => rfl) hsat
  refine ⟨D, h, hwidth, ?_⟩
  rw [hwidth, ← hms, hmass_eff, hmass_pad]
  have hm_eq : m = n + (m - n) := by omega
  conv_lhs => rw [hm_eq, Nat.pow_add]
  ring

private lemma part2 (a : ℕ) :
    let c := 6 * (a + 1)
    ∀ (D : F c) (h : Ty c → ℕ), ∃ A : F (width h), mass (width h) A = score D h := by
  classical
  intro c D h
  let m := width h
  have hcm : c ≤ m := by unfold m width; omega
  let C : Finset (Fin m) := Finset.univ.filter (fun v : Fin m => v.val < c)
  let eC : Fin c ≃ {v : Fin m // v ∈ C} :=
    { toFun := fun i => ⟨⟨i.val, by omega⟩, by simp [C, i.isLt]⟩
      invFun := fun v => ⟨v.val.val, (Finset.mem_filter.mp v.property).2⟩
      left_inv := by intro i; ext; rfl
      right_inv := by intro v; apply Subtype.ext; ext; rfl }
  let L : List (Ty c) := (Finset.univ : Finset (Ty c)).toList.flatMap (fun t => List.replicate (h t) t)
  have hLlen : L.length = ∑ t : Ty c, h t := by
    simp only [L, List.length_flatMap, List.length_replicate]
    simp
  have hLcnt : ∀ t : Ty c, L.count t = h t := by
    intro t
    have h1 := count_flatMap_replicate (Finset.univ : Finset (Ty c)).toList h (Finset.nodup_toList _) t
    have hmem : t ∈ (Finset.univ : Finset (Ty c)).toList := Finset.mem_toList.mpr (Finset.mem_univ t)
    simpa [L, hmem] using h1
  let eOut : {v : Fin m // v ∉ C} ≃ Fin L.length :=
    { toFun := fun v =>
        ⟨v.val.val - c, by
          have hv := v.property
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
          have : v.val.val < m := v.val.isLt
          unfold m width at this
          omega⟩
      invFun := fun i =>
        ⟨⟨c + i.val, by unfold m width; omega⟩, by
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          omega⟩
      left_inv := by
        intro v
        have hv := v.property
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
        apply Subtype.ext; ext; dsimp only; omega
      right_inv := by
        intro i; ext; dsimp only; omega }
  let τ : {v : Fin m // v ∉ C} → Ty c := fun v => L[eOut v]
  have hcnt : ∀ t : Ty c, (Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t)).card = h t := by
    intro t
    have hbij : (Finset.univ.filter (fun v : {v : Fin m // v ∉ C} => τ v = t)).card =
        (Finset.univ.filter (fun i : Fin L.length => L[i] = t)).card := by
      refine Finset.card_bij (fun v _ => eOut v) ?_ ?_ ?_
      · intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      · intro v1 _ v2 _ heq; exact eOut.injective heq
      · intro i hi
        refine ⟨eOut.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eOut.apply_symm_apply i⟩
        dsimp only [τ]
        have hfn : ∀ j1 j2 : Fin L.length, j1 = j2 → L[j1] = L[j2] := by rintro j1 _ rfl; rfl
        rw [hfn _ _ (eOut.apply_symm_apply i)]
        exact (Finset.mem_filter.mp hi).2
    rw [hbij, card_fin_getElem_eq, hLcnt]
  let AD : F m := D.image (fun e => (((eC e.1.1).val, e.1.2), ((eC e.2.1).val, e.2.2)))
  let AT : F m := Finset.univ.biUnion (fun v : {v : Fin m // v ∉ C} =>
    (τ v).image (fun edge => (((eC edge.1.1).val, edge.1.2), (v.val, edge.2))))
  let A : F m := AD ∪ AT
  refine ⟨A, ?_⟩
  refine mass_eq_score_of_cover C eC A D τ h hcnt ?_
  intro z
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro e he
      exact hz _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))
    · intro v edge hedge
      exact hz _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_image_of_mem _ hedge⟩))
  · rintro ⟨hD, hT⟩ e he
    rcases Finset.mem_union.mp he with hAD | hAT
    · rcases Finset.mem_image.mp hAD with ⟨e0, he0, rfl⟩
      exact hD e0 he0
    · rcases Finset.mem_biUnion.mp hAT with ⟨v, _, hv⟩
      rcases Finset.mem_image.mp hv with ⟨edge, hedge, rfl⟩
      exact hT v edge hedge

end PEqualNP.Outside.L_lib_694_aux

theorem PEqualNP.Outside.L_lib_694 : let W := fun k : ℕ => Fin k → Bool
let Lit := fun k : ℕ => Fin k × Bool
let F := fun k : ℕ => Finset (Lit k × Lit k)
let mass := fun (n : ℕ) (A : F n) =>
  (Finset.univ.filter (fun z : W n => ∀ e ∈ A,
    z e.1.1 ≠ e.1.2 ∨ z e.2.1 ≠ e.2.2)).card
∀ a : ℕ,
  let c := 6 * (a + 1)
  let T := Finset (Lit c × Bool)
  let choices := fun (t : T) (w : W c) =>
    (Finset.univ.filter (fun b : Bool => ∀ edge ∈ t,
      w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2)).card
  let width := fun h : T → ℕ => c + ∑ t, h t
  let fiber := fun (D : F c) (h : T → ℕ) (w : W c) =>
    if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then
      ∏ t, (choices t w) ^ (h t)
    else 0
  let score := fun (D : F c) (h : T → ℕ) => ∑ w, fiber D h w
  (∀ (n : ℕ) (A : F n), 2 ^ n ≤ 2 ^ a * mass n A →
    ∃ (D : F c) (h : T → ℕ),
      width h = max c n ∧
      mass n A * 2 ^ (width h) = score D h * 2 ^ n) ∧
  (∀ (D : F c) (h : T → ℕ), ∃ A : F (width h), mass (width h) A = score D h) := by
  intro W Lit F mass a c T choices width fiber score
  exact ⟨PEqualNP.Outside.L_lib_694_aux.part1 a, PEqualNP.Outside.L_lib_694_aux.part2 a⟩
