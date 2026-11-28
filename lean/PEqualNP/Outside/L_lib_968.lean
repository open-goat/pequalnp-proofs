import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_968_aux

open Classical

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> rfl

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  rcases zmod2_cases x with rfl | rfl
  · exact absurd rfl h
  · rfl

private lemma msingle_apply {ι : Type*} [DecidableEq ι] (a b i j : ι) :
    Matrix.single a b (1 : ZMod 2) i j = if i = a ∧ j = b then 1 else 0 := by
  simp only [Matrix.single_apply, eq_comm]

private lemma zmod2_quad_alt_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) (ZMod 2))
    (hH : H.transpose = H ∧ ∀ i, H i i = 0) (v : Fin n → ZMod 2) :
    (∑ a : Fin n, ∑ b : Fin n, v a * H a b * v b) = 0 := by
  have hsym : ∀ a b : Fin n, H b a = H a b := fun a b => congrFun (congrFun hH.1 a) b
  have hsplit : (∑ a : Fin n, ∑ b : Fin n, v a * H a b * v b) =
      (∑ p : Fin n × Fin n, if p.1 < p.2 then v p.1 * H p.1 p.2 * v p.2 else 0) +
      (∑ p : Fin n × Fin n, if p.2 < p.1 then v p.1 * H p.1 p.2 * v p.2 else 0) := by
    rw [← Fintype.sum_prod_type', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, not_lt.mpr (le_of_lt hlt)]
    · rw [heq]; simp [hH.2]
    · simp [hgt, not_lt.mpr (le_of_lt hgt)]
  have hswap : (∑ p : Fin n × Fin n, if p.2 < p.1 then v p.1 * H p.1 p.2 * v p.2 else 0) =
      (∑ p : Fin n × Fin n, if p.1 < p.2 then v p.1 * H p.1 p.2 * v p.2 else 0) := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun p => ?_
    dsimp only [Equiv.prodComm_apply, Prod.swap]
    by_cases h : p.2 < p.1
    · rw [if_pos h, if_pos h, hsym p.2 p.1]; ring
    · rw [if_neg h, if_neg h]
  rw [hsplit, hswap, zmod2_add_self]

private lemma exists_ann_ne_zero {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    {v : Fin n → ZMod 2} (hv : v ∉ U) :
    ∃ φ : Fin n → ZMod 2, (∀ u ∈ U, dotProduct φ u = 0) ∧ dotProduct φ v = 1 := by
  let U1 : Submodule (ZMod 2) (Fin n → ZMod 2) := U ⊔ Submodule.span (ZMod 2) {v}
  rcases Submodule.exists_isCompl U1 with ⟨C, hC⟩
  have hdisj : U ⊓ Submodule.span (ZMod 2) {v} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hwU, hwS⟩
    rcases Submodule.mem_span_singleton.mp hwS with ⟨c, rfl⟩
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simp only [one_smul] at hwU; exact absurd hwU hv
  have hsplit : ∀ w : Fin n → ZMod 2, ∃ u ∈ U, ∃ a : ZMod 2, ∃ c ∈ C, u + a • v + c = w := by
    intro w
    have htop : w ∈ U1 ⊔ C := by rw [hC.sup_eq_top]; trivial
    rcases Submodule.mem_sup.mp htop with ⟨x, hxU1, c, hcC, rfl⟩
    rcases Submodule.mem_sup.mp hxU1 with ⟨u, huU, s, hsS, rfl⟩
    rcases Submodule.mem_span_singleton.mp hsS with ⟨a, rfl⟩
    exact ⟨u, huU, a, c, hcC, rfl⟩
  have huniq : ∀ u ∈ U, ∀ (a : ZMod 2), ∀ c ∈ C, u + a • v + c = 0 → a = 0 := by
    intro u hu a c hc h0
    have hmem : u + a • v ∈ U1 ⊓ C := by
      refine ⟨Submodule.add_mem_sup hu (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))), ?_⟩
      rw [eq_neg_of_add_eq_zero_left h0]; exact C.neg_mem hc
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hmem
    have hS : a • v ∈ U ⊓ Submodule.span (ZMod 2) {v} := by
      refine ⟨?_, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))⟩
      rw [eq_neg_of_add_eq_zero_right hmem]; exact U.neg_mem hu
    rw [hdisj, Submodule.mem_bot] at hS
    rcases zmod2_cases a with rfl | rfl
    · rfl
    · simp only [one_smul] at hS; exact absurd (hS ▸ U.zero_mem) hv
  let getA : (Fin n → ZMod 2) → ZMod 2 := fun w => Classical.choose (Classical.choose_spec (hsplit w)).2
  have hgetA : ∀ w u, u ∈ U → ∀ (a : ZMod 2) c, c ∈ C → u + a • v + c = w → getA w = a := by
    intro w u hu a c hc hw
    have h1 := Classical.choose_spec (hsplit w)
    let u1 := Classical.choose (hsplit w)
    let a1 := Classical.choose h1.2
    have ha1 := Classical.choose_spec h1.2
    let c1 := Classical.choose ha1
    have hc1 := Classical.choose_spec ha1
    change a1 = a
    have h0 : (u1 - u) + (a1 - a) • v + (c1 - c) = 0 := by
      have heq := hc1.2.trans hw.symm
      funext i; have hi := congrFun heq i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      linear_combination hi
    exact sub_eq_zero.mp (huniq (u1 - u) (U.sub_mem h1.1 hu) (a1 - a) (c1 - c) (C.sub_mem hc1.1 hc) h0)
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := getA,
      map_add' := fun w1 w2 => by
        have h1 := Classical.choose_spec (hsplit w1)
        let u1 := Classical.choose (hsplit w1); let a1 := Classical.choose h1.2
        have ha1 := Classical.choose_spec h1.2; let c1 := Classical.choose ha1; have hc1 := Classical.choose_spec ha1
        have h2 := Classical.choose_spec (hsplit w2)
        let u2 := Classical.choose (hsplit w2); let a2 := Classical.choose h2.2
        have ha2 := Classical.choose_spec h2.2; let c2 := Classical.choose ha2; have hc2 := Classical.choose_spec ha2
        refine hgetA (w1 + w2) (u1 + u2) (U.add_mem h1.1 h2.1) (a1 + a2) (c1 + c2) (C.add_mem hc1.1 hc2.1) ?_
        funext i; have hi1 := congrFun hc1.2 i; have hi2 := congrFun hc2.2 i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi1 hi2 ⊢
        rw [← hi1, ← hi2]; ring
      map_smul' := fun s w => by
        rcases zmod2_cases s with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply]
          exact hgetA 0 0 U.zero_mem 0 0 C.zero_mem (by simp)
        · simp }
  let φ : Fin n → ZMod 2 := fun j => ψ (Pi.single j 1)
  have hdot : ∀ w : Fin n → ZMod 2, dotProduct φ w = ψ w := by
    intro w
    have hw : w = ∑ j : Fin n, w j • Pi.single j (1 : ZMod 2) := by
      funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro h; exact absurd (Finset.mem_univ i) h
    conv_rhs => rw [hw, map_sum]
    simp only [dotProduct, φ, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨φ, fun u hu => ?_, ?_⟩
  · rw [hdot]; exact hgetA u u hu 0 0 C.zero_mem (by simp)
  · rw [hdot]; exact hgetA v 0 U.zero_mem 1 0 C.zero_mem (by simp)

private lemma alt_rank_mod_bound {n : ℕ} (A B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (K : Matrix (Fin n) (Fin n) (ZMod 2)) (hK : K.transpose = K ∧ ∀ i, K i i = 0)
    (lam mu : Fin n → ZMod 2)
    (hlam : ∀ u ∈ A ⊔ B, dotProduct lam u = 0)
    (hmu : ∀ u ∈ A ⊓ B, dotProduct mu u = 0)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp K.mulVecLin)) +
      Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp K.mulVecLin)) ≤ 2) :
    dotProduct lam (K.mulVec mu) = 0 := by
  let V := LinearMap.range K.mulVecLin
  have hmod : ∀ S : Submodule (ZMod 2) (Fin n → ZMod 2),
      Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ S).comp K.mulVecLin)) +
      Module.finrank (ZMod 2) ↥(V ⊓ S) = Module.finrank (ZMod 2) V := by
    intro S
    let fS : V →ₗ[ZMod 2] ((Fin n → ZMod 2) ⧸ S) := (Submodule.mkQ S).comp V.subtype
    have hrg : LinearMap.range fS = LinearMap.range ((Submodule.mkQ S).comp K.mulVecLin) := by
      ext q; simp only [fS, LinearMap.mem_range, LinearMap.comp_apply, Submodule.coe_subtype, Subtype.exists]
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨K.mulVec x, ⟨x, rfl⟩, rfl⟩
    have hker : (LinearMap.ker fS).map V.subtype = V ⊓ S := by
      ext w; simp only [Submodule.mem_map, LinearMap.mem_ker, fS, LinearMap.comp_apply,
        Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_inf]
      constructor
      · rintro ⟨⟨y, hyV⟩, hyS, rfl⟩; exact ⟨hyV, hyS⟩
      · rintro ⟨hwV, hwS⟩; exact ⟨⟨w, hwV⟩, hwS, rfl⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker fS
    rw [hrg, ← Submodule.finrank_map_subtype_eq V (LinearMap.ker fS), hker] at hrn
    exact hrn
  by_cases hVA : V ≤ A ⊔ B
  · exact hlam (K.mulVec mu) (hVA ⟨mu, rfl⟩)
  · have hA0 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp K.mulVecLin)) ≠ 0 := by
      intro hz
      have h1 := hmod A; rw [hz, zero_add] at h1
      have hVA_eq : V ⊓ A = V := Submodule.eq_of_le_of_finrank_eq inf_le_left h1
      apply hVA
      intro w hw; rw [← hVA_eq] at hw; exact Submodule.mem_sup_left hw.2
    have hB0 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp K.mulVecLin)) ≠ 0 := by
      intro hz
      have h1 := hmod B; rw [hz, zero_add] at h1
      have hVB_eq : V ⊓ B = V := Submodule.eq_of_le_of_finrank_eq inf_le_left h1
      apply hVA
      intro w hw; rw [← hVB_eq] at hw; exact Submodule.mem_sup_right hw.2
    have hA1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp K.mulVecLin)) = 1 := by omega
    have hB1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp K.mulVecLin)) = 1 := by omega
    have hfrA := hmod A; rw [hA1] at hfrA
    have hfrB := hmod B; rw [hB1] at hfrB
    have hVA_eq_VB : V ⊓ A = V ⊓ B := by
      by_contra hne
      have hsup_le : (V ⊓ A) ⊔ (V ⊓ B) ≤ V := sup_le inf_le_left inf_le_left
      have hlt : V ⊓ A < (V ⊓ A) ⊔ (V ⊓ B) := by
        refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
        have hle_BA : V ⊓ B ≤ V ⊓ A := le_sup_right.trans (le_of_eq heq.symm)
        exact (Submodule.eq_of_le_of_finrank_eq hle_BA (by omega)).symm
      have hfr_gt := Submodule.finrank_lt_finrank_of_lt hlt
      have hfr_le := Submodule.finrank_mono hsup_le
      have hsup_eq : (V ⊓ A) ⊔ (V ⊓ B) = V := Submodule.eq_of_le_of_finrank_eq hsup_le (by omega)
      apply hVA
      intro w hw
      rw [← hsup_eq] at hw
      rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
      exact Submodule.add_mem_sup hu.2 hv.2
    have hVAB : V ⊓ (A ⊓ B) = V ⊓ A := by
      apply le_antisymm
      · exact inf_le_inf_left V inf_le_left
      · intro w hw; exact ⟨hw.1, hw.2, (hVA_eq_VB ▸ hw).2⟩
    have hfrAB := hmod (A ⊓ B)
    rw [hVAB] at hfrAB
    have hQ1 : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp K.mulVecLin)) = 1 := by omega
    have hne_bot : LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp K.mulVecLin) ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hQ1; omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hne_bot with ⟨q0, hq0_mem, hq0_ne⟩
    rcases hq0_mem with ⟨x0, rfl⟩
    let v0 := K.mulVec x0
    have hspan_q0 : LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp K.mulVecLin) =
        Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} := by
      have hle : Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} ≤
          LinearMap.range ((Submodule.mkQ (A ⊓ B)).comp K.mulVecLin) := by
        rw [Submodule.span_singleton_le_iff_mem]; exact ⟨x0, rfl⟩
      have hfr1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0}) = 1 :=
        finrank_span_singleton hq0_ne
      exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
    have hdecomp : ∀ x : Fin n → ZMod 2, ∃ c : ZMod 2, K.mulVec x - c • v0 ∈ A ⊓ B := by
      intro x
      have hmem : Submodule.mkQ (A ⊓ B) (K.mulVec x) ∈ Submodule.span (ZMod 2) {Submodule.mkQ (A ⊓ B) v0} := by
        rw [← hspan_q0]; exact ⟨x, rfl⟩
      rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hc, sub_self]
    have hlam_AB : ∀ u ∈ A ⊓ B, dotProduct lam u = 0 := fun u hu => hlam u (Submodule.mem_sup_left hu.1)
    have hdot_formula : ∀ x : Fin n → ZMod 2, ∃ c : ZMod 2,
        dotProduct lam (K.mulVec x) = c * dotProduct lam v0 ∧
        dotProduct mu (K.mulVec x) = c * dotProduct mu v0 := by
      intro x
      rcases hdecomp x with ⟨c, hcab⟩
      have h1 := hlam_AB _ hcab
      have h2 := hmu _ hcab
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h1 h2
      exact ⟨c, h1, h2⟩
    rcases zmod2_cases (dotProduct lam v0) with hlv0 | hlv1
    · rcases hdot_formula mu with ⟨c, h1, _⟩
      rw [h1, hlv0, mul_zero]
    · have hquad : dotProduct lam (K.mulVec lam) = 0 := by
        simp only [dotProduct, Matrix.mulVec]
        have hexp : ∑ a : Fin n, lam a * ∑ b : Fin n, K a b * lam b =
            ∑ a : Fin n, ∑ b : Fin n, lam a * K a b * lam b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => (mul_assoc _ _ _).symm
        rw [hexp]; exact zmod2_quad_alt_zero K hK lam
      rcases hdot_formula lam with ⟨c, h1, h2⟩
      rw [hlv1, mul_one, hquad] at h1
      have hc0 : c = 0 := h1.symm
      rw [hc0, zero_mul] at h2
      have hsym_dot : dotProduct lam (K.mulVec mu) = dotProduct mu (K.mulVec lam) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hKab : K b a = K a b := congrFun (congrFun hK.1 a) b
        rw [hKab]; ring
      rw [hsym_dot, h2]

private lemma alt_rank_le_two_wedge {n : ℕ} (K : Matrix (Fin n) (Fin n) (ZMod 2))
    (hK : K.transpose = K ∧ ∀ i, K i i = 0) (hrk : K.rank ≤ 2) :
    ∃ u v : Fin n → ZMod 2, ∀ a b : Fin n, K a b = u a * v b + v a * u b := by
  by_cases h0 : K = 0
  · refine ⟨0, 0, fun a b => by simp [h0]⟩
  · have hex : ∃ i j : Fin n, K i j ≠ 0 := by
      by_contra hall; push Not at hall; apply h0; ext i j; exact hall i j
    rcases hex with ⟨i0, j0, hij⟩
    have hij1 : K i0 j0 = 1 := zmod2_eq_one_of_ne_zero hij
    have hKsym : ∀ a b : Fin n, K b a = K a b := fun a b => congrFun (congrFun hK.1 a) b
    let u : Fin n → ZMod 2 := fun a => K a j0
    let v : Fin n → ZMod 2 := fun a => K a i0
    have hui : u i0 = 1 := hij1
    have huj : u j0 = 0 := hK.2 j0
    have hvi : v i0 = 0 := hK.2 i0
    have hvj : v j0 = 1 := by dsimp only [v]; rw [hKsym i0 j0]; exact hij1
    have hu_mem : u ∈ LinearMap.range K.mulVecLin := by
      refine ⟨Pi.single j0 1, ?_⟩
      funext a; simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, u]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ j0) h
    have hv_mem : v ∈ LinearMap.range K.mulVecLin := by
      refine ⟨Pi.single i0 1, ?_⟩
      funext a; simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply, v]
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ i0) h
    have hli : LinearIndependent (ZMod 2) (fun b : Fin 2 => if b = 0 then u else v) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : c 0 • u + c 1 • v = 0 := by
        simpa only [Fin.sum_univ_two, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff] using hc
      have hi_eq := congrFun hc' i0
      have hj_eq := congrFun hc' j0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hui, hvi, huj, hvj,
        mul_one, mul_zero, add_zero, zero_add] at hi_eq hj_eq
      intro b; fin_cases b <;> assumption
    let U2 := Submodule.span (ZMod 2) (Set.range (fun b : Fin 2 => if b = 0 then u else v))
    have hU2_le : U2 ≤ LinearMap.range K.mulVecLin := by
      rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; fin_cases b
      · exact hu_mem
      · exact hv_mem
    have hfrU2 : Module.finrank (ZMod 2) U2 = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hfr_eq : Module.finrank (ZMod 2) U2 = Module.finrank (ZMod 2) (LinearMap.range K.mulVecLin) := by
      have hle := Submodule.finrank_mono hU2_le; change Module.finrank (ZMod 2) (LinearMap.range K.mulVecLin) ≤ 2 at hrk; omega
    have hrg_eq : U2 = LinearMap.range K.mulVecLin := Submodule.eq_of_le_of_finrank_eq hU2_le hfr_eq
    refine ⟨u, v, fun a b => ?_⟩
    have hcol_mem : (fun r => K r b) ∈ U2 := by
      rw [hrg_eq]
      refine ⟨Pi.single b 1, ?_⟩
      funext r; simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Finset.sum_eq_single b]
      · simp
      · intro k _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ b) h
    have hU2_set : U2 = Submodule.span (ZMod 2) ({u, v} : Set (Fin n → ZMod 2)) := by
      dsimp only [U2]; congr 1; ext w; simp [Fin.exists_fin_two, eq_comm]
    rw [hU2_set, Submodule.mem_span_pair] at hcol_mem
    rcases hcol_mem with ⟨α, β, hcomb⟩
    have hα : α = v b := by
      have hi := congrFun hcomb i0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hui, hvi, mul_one, mul_zero, add_zero] at hi
      rw [hi, hKsym b i0]
    have hβ : β = u b := by
      have hj := congrFun hcomb j0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, huj, hvj, mul_one, mul_zero, zero_add] at hj
      rw [hj, hKsym b j0]
    have ha := congrFun hcomb a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hα, hβ] at ha
    rw [← ha]; ring

private lemma rank_le_two_of_two_vecs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2)) (v1 v2 : ι → ZMod 2)
    (hmem : ∀ x : ι → ZMod 2, ∃ c1 c2 : ZMod 2, M.mulVec x = c1 • v1 + c2 • v2) :
    M.rank ≤ 2 := by
  have hle : LinearMap.range M.mulVecLin ≤
      Submodule.span (ZMod 2) (({v1, v2} : Finset (ι → ZMod 2)) : Set (ι → ZMod 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    rcases hmem x with ⟨c1, c2, hx⟩
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  calc M.rank ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({v1, v2} : Finset (ι → ZMod 2)) : Set (ι → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ ({v1, v2} : Finset (ι → ZMod 2)).card := finrank_span_finset_le_card _
    _ ≤ 2 := Finset.card_le_two

private lemma rank_le_one_of_col_vec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ZMod 2) (j0 : ι) :
    (Matrix.of fun i j => if j = j0 then v i else 0).rank ≤ 1 := by
  have hle : LinearMap.range (Matrix.of fun i j => if j = j0 then v i else 0).mulVecLin ≤
      Submodule.span (ZMod 2) (({v} : Finset (ι → ZMod 2)) : Set (ι → ZMod 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply]
    have hx : (Matrix.of fun i j => if j = j0 then v i else 0).mulVec x = x j0 • v := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j0]
      · simp [mul_comm]
      · intro j _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ j0) h
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  calc (Matrix.of fun i j => if j = j0 then v i else 0).rank
      ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({v} : Finset (ι → ZMod 2)) : Set (ι → ZMod 2))) :=
        Submodule.finrank_mono hle
    _ ≤ ({v} : Finset (ι → ZMod 2)).card := finrank_span_finset_le_card _
    _ = 1 := Finset.card_singleton _

private lemma dir_forward {n b : ℕ} (P : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (hP_alt : ∀ K ∈ P, K.transpose = K ∧ ∀ i, K i i = 0)
    (E : Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) (hEb : Module.finrank (ZMod 2) E ≤ b)
    (hL_eq :
      let W := Submodule.span (ZMod 2) {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) |
        ∃ A K : Matrix (Fin n) (Fin n) (ZMod 2), (A.transpose = A ∧ ∀ i, A i i = 0) ∧ K ∈ P ∧
          X = Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) (ZMod 2))}
      let free := Submodule.span (ZMod 2) {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) |
        ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span (ZMod 2) {X | X ∈ L ∧ X.rank ≤ 2}) :
    ∃ I S : Submodule (ZMod 2) (Fin n → ZMod 2), I ≤ S ∧
      Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) S ≤ b ∧
      ∀ K ∈ P, ∀ x, (∀ y ∈ S, (∑ i, y i * x i) = 0) → K.mulVec x ∈ I := by
  let J := Fin n ⊕ Fin n
  let Big := Matrix J J (ZMod 2)
  let W := Submodule.span (ZMod 2) {X : Big | ∃ A K : Matrix (Fin n) (Fin n) (ZMod 2),
    (A.transpose = A ∧ ∀ i, A i i = 0) ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K 0}
  let free := Submodule.span (ZMod 2) {X : Big | ∀ j, (fun i => X i j) ∈ E}
  let L := W ⊔ free
  have hL : L = Submodule.span (ZMod 2) {X : Big | X ∈ L ∧ X.rank ≤ 2} := hL_eq
  let projL : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun w i => w (Sum.inl i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let projR : (J → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun w i => w (Sum.inr i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let toPair : (J → ZMod 2) ≃ₗ[ZMod 2] ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
    { toFun := fun w => (projL w, projR w),
      invFun := fun p => Sum.elim p.1 p.2,
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl,
      left_inv := fun w => funext fun j => by cases j <;> rfl,
      right_inv := fun ⟨u, v⟩ => rfl }
  let E' := E.map toPair.toLinearMap
  have hfrE' : Module.finrank (ZMod 2) E' = Module.finrank (ZMod 2) E :=
    LinearEquiv.finrank_map_eq toPair E
  let A : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := { u | (u, 0) ∈ E' },
      zero_mem' := E'.zero_mem, add_mem' := fun {u1 u2} h1 h2 => by
        change (u1 + u2, 0) ∈ E'
        have h := E'.add_mem h1 h2; simpa only [Prod.mk_add_mk, add_zero] using h,
      smul_mem' := fun c u hu => by
        change (c • u, 0) ∈ E'
        have h := E'.smul_mem c hu; simpa only [Prod.smul_mk, smul_zero] using h }
  let B : Submodule (ZMod 2) (Fin n → ZMod 2) := E'.map (LinearMap.snd (ZMod 2) _ _)
  have hfrAB : Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) E' := by
    let f := (LinearMap.snd (ZMod 2) (Fin n → ZMod 2) (Fin n → ZMod 2)).comp E'.subtype
    have hrg : LinearMap.range f = B := by ext v; simp [f, B, Submodule.mem_map]
    let eA : A ≃ₗ[ZMod 2] LinearMap.ker f :=
      { toFun := fun u => ⟨⟨(u.val, 0), u.property⟩, rfl⟩,
        invFun := fun k => ⟨k.val.val.1, by
          change (k.val.val.1, (0 : Fin n → ZMod 2)) ∈ E'
          have hk2 : k.val.val.2 = 0 := k.property
          have hpair : (k.val.val.1, (0 : Fin n → ZMod 2)) = k.val.val := Prod.ext rfl hk2.symm
          rw [hpair]; exact k.val.property⟩,
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl,
        left_inv := fun _ => rfl,
        right_inv := fun k => Subtype.ext (Subtype.ext (Prod.ext rfl k.property.symm)) }
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hrg, ← eA.finrank_eq] at hrn; omega
  -- Build shear sh : (Fin n → ZMod 2) →ₗ (Fin n → ZMod 2)
  rcases Submodule.exists_isCompl B with ⟨BC, hBC⟩
  let bB := Module.finBasis (ZMod 2) B
  let liftB : Fin (Module.finrank (ZMod 2) B) → (Fin n → ZMod 2) := fun k =>
    (Classical.choose (Submodule.mem_map.mp (bB k).property)).1
  have hliftB_mem : ∀ k, (liftB k, (bB k).val) ∈ E' := by
    intro k
    have hspec := Classical.choose_spec (Submodule.mem_map.mp (bB k).property)
    have hpair : (liftB k, (bB k).val) = Classical.choose (Submodule.mem_map.mp (bB k).property) :=
      Prod.ext rfl hspec.2.symm
    rw [hpair]; exact hspec.1
  let sh_B : B →ₗ[ZMod 2] (Fin n → ZMod 2) := bB.constr (ZMod 2) liftB
  have hsh_B_mem : ∀ v : B, (sh_B v, v.val) ∈ E' := by
    intro v
    have hv := bB.sum_repr v
    rw [← hv, map_sum]
    simp only [Submodule.coe_sum, map_smul, SetLike.val_smul]
    have hpair : (∑ k, bB.repr v k • sh_B (bB k), ∑ k, bB.repr v k • (bB k).val) =
        ∑ k, bB.repr v k • (sh_B (bB k), (bB k).val) := by
      apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd]
    rw [hpair]
    refine Submodule.sum_mem E' fun k _ => Submodule.smul_mem E' _ ?_
    have hk : sh_B (bB k) = liftB k := bB.constr_basis (ZMod 2) liftB k
    rw [hk]; exact hliftB_mem k
  have hsplitB : ∀ x : Fin n → ZMod 2, ∃ b ∈ B, ∃ c ∈ BC, b + c = x := by
    intro x; exact Submodule.mem_sup.mp (by rw [hBC.sup_eq_top]; trivial)
  have huniqB : ∀ b ∈ B, ∀ c ∈ BC, b + c = 0 → b = 0 := by
    intro b hb c hc h0
    have hmem : b ∈ B ⊓ BC := ⟨hb, by rw [eq_neg_of_add_eq_zero_left h0]; exact BC.neg_mem hc⟩
    rwa [hBC.inf_eq_bot, Submodule.mem_bot] at hmem
  let getB : (Fin n → ZMod 2) → B := fun x => ⟨Classical.choose (hsplitB x), (Classical.choose_spec (hsplitB x)).1⟩
  have hgetB_eq : ∀ x b (hb : b ∈ B) c, c ∈ BC → b + c = x → getB x = ⟨b, hb⟩ := by
    intro x b hb c hc hx
    have h1 := Classical.choose_spec (hsplitB x)
    let b1 := Classical.choose (hsplitB x); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
    apply Subtype.ext; change b1 = b
    have h0 : (b1 - b) + (c1 - c) = 0 := by
      have heq := hc1.2.trans hx.symm
      funext i; have hi := congrFun heq i; simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢; linear_combination hi
    exact sub_eq_zero.mp (huniqB _ (B.sub_mem h1.1 hb) _ (BC.sub_mem hc1.1 hc) h0)
  let sh : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    { toFun := fun x => sh_B (getB x),
      map_add' := fun x1 x2 => by
        have h1 := Classical.choose_spec (hsplitB x1)
        let b1 := Classical.choose (hsplitB x1); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
        have h2 := Classical.choose_spec (hsplitB x2)
        let b2 := Classical.choose (hsplitB x2); let c2 := Classical.choose h2.2; have hc2 := Classical.choose_spec h2.2
        have hsum : (b1 + b2) + (c1 + c2) = x1 + x2 := by
          calc (b1 + b2) + (c1 + c2) = (b1 + c1) + (b2 + c2) := by abel
            _ = x1 + x2 := by rw [hc1.2, hc2.2]
        rw [hgetB_eq (x1 + x2) (b1 + b2) (B.add_mem h1.1 h2.1) (c1 + c2) (BC.add_mem hc1.1 hc2.1) hsum]
        exact map_add sh_B (getB x1) (getB x2)
      map_smul' := fun s x => by
        have h1 := Classical.choose_spec (hsplitB x)
        let b1 := Classical.choose (hsplitB x); let c1 := Classical.choose h1.2; have hc1 := Classical.choose_spec h1.2
        have hsm : s • b1 + s • c1 = s • x := by rw [← smul_add, hc1.2]
        rw [hgetB_eq (s • x) (s • b1) (B.smul_mem s h1.1) (s • c1) (BC.smul_mem s hc1.1) hsm]
        exact map_smul sh_B s (getB x) }
  have hsh_kills_E : ∀ w ∈ E, projL w + sh (projR w) ∈ A ∧ projR w ∈ B := by
    intro w hwE
    have hwE' : (projL w, projR w) ∈ E' := Submodule.mem_map.mpr ⟨w, hwE, rfl⟩
    have hwB : projR w ∈ B := Submodule.mem_map.mpr ⟨(projL w, projR w), hwE', rfl⟩
    have hSw : (sh (projR w), projR w) ∈ E' := by
      change (sh_B (getB (projR w)), projR w) ∈ E'
      rw [hgetB_eq (projR w) (projR w) hwB 0 BC.zero_mem (by simp)]
      exact hsh_B_mem ⟨projR w, hwB⟩
    refine ⟨?_, hwB⟩
    change (projL w + sh (projR w), 0) ∈ E'
    have hadd := E'.add_mem hwE' hSw
    have hzero : projR w + projR w = 0 := funext fun i => zmod2_add_self _
    simpa only [Prod.mk_add_mk, hzero] using hadd
  -- Also note every X ∈ W has form fromBlocks A0 K0 K0 0 with alt A0 and K0 ∈ P
  have hW_form : ∀ X ∈ W, ∃ A0 K0 : Matrix (Fin n) (Fin n) (ZMod 2),
      (A0.transpose = A0 ∧ ∀ i, A0 i i = 0) ∧ K0 ∈ P ∧ X = Matrix.fromBlocks A0 K0 K0 0 := by
    intro X hX
    refine Submodule.span_induction (fun Y hY => hY)
      ⟨0, 0, ⟨Matrix.transpose_zero, fun _ => rfl⟩, P.zero_mem, by ext i j; cases i <;> cases j <;> rfl⟩
      (fun X1 X2 _ _ ⟨A1, K1, hA1, hK1, hX1⟩ ⟨A2, K2, hA2, hK2, hX2⟩ =>
        ⟨A1 + A2, K1 + K2, ⟨by rw [Matrix.transpose_add, hA1.1, hA2.1], fun i => by simp [hA1.2 i, hA2.2 i]⟩,
          P.add_mem hK1 hK2, by
            rw [hX1, hX2]; ext i j
            change (Matrix.fromBlocks A1 K1 K1 0) i j + (Matrix.fromBlocks A2 K2 K2 0) i j =
              (Matrix.fromBlocks (A1 + A2) (K1 + K2) (K1 + K2) 0) i j
            cases i <;> cases j <;> simp⟩)
      (fun c X1 _ ⟨A1, K1, hA1, hK1, hX1⟩ =>
        ⟨c • A1, c • K1, ⟨by rw [Matrix.transpose_smul, hA1.1], fun i => by simp [hA1.2 i]⟩,
          P.smul_mem c hK1, by
            rw [hX1]; ext i j
            change c * (Matrix.fromBlocks A1 K1 K1 0) i j =
              (Matrix.fromBlocks (c • A1) (c • K1) (c • K1) 0) i j
            cases i <;> cases j <;> simp⟩) hX
  let I := A ⊓ B
  let S := A ⊔ B
  have hIS : I ≤ S := inf_le_left.trans le_sup_left
  have hfrIS : Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) S ≤ b := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq A B
    change Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) I =
      Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B at hsup
    omega
  refine ⟨I, S, hIS, hfrIS, fun K hKP x hx_perp => ?_⟩
  by_contra hnotI
  rcases exists_ann_ne_zero I hnotI with ⟨mu, hmu_I, hmu_ne0⟩
  have hx_S : ∀ u ∈ A ⊔ B, dotProduct x u = 0 := by
    intro u hu
    rw [dotProduct_comm]
    exact hx_perp u hu
  let f_bad : Big →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun Y => dotProduct (Sum.elim 0 x) (Y.mulVec (Sum.elim mu 0)),
      map_add' := fun Y1 Y2 => by rw [Matrix.add_mulVec, dotProduct_add],
      map_smul' := fun c Y => by rw [Matrix.smul_mulVec, dotProduct_smul]; rfl }
  have hf_free : ∀ Z ∈ free, f_bad Z = 0 := by
    intro Z hZ
    refine Submodule.span_induction (fun Y hY => ?_) (map_zero f_bad)
      (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c _ _ ha => by rw [map_smul, ha, smul_zero]) hZ
    change dotProduct (Sum.elim 0 x) (Y.mulVec (Sum.elim mu 0)) = 0
    simp only [dotProduct, Matrix.mulVec]
    rw [Fintype.sum_sum_type (f := fun i => Sum.elim (0 : Fin n → ZMod 2) x i * ∑ j : Fin n ⊕ Fin n, Y i j * Sum.elim mu 0 j)]
    simp_rw [Fintype.sum_sum_type (f := fun j => Y _ j * Sum.elim mu 0 j)]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hcolB : projR (fun i => Y i (Sum.inl j)) ∈ B := (hsh_kills_E _ (hY (Sum.inl j))).2
    have h0 : dotProduct x (projR (fun i => Y i (Sum.inl j))) = 0 := hx_S _ (Submodule.mem_sup_right hcolB)
    have hsum : ∑ i : Fin n, x i * (Y (Sum.inr i) (Sum.inl j) * mu j) =
        dotProduct x (projR (fun i => Y i (Sum.inl j))) * mu j := by
      simp only [dotProduct, projR, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, h0, zero_mul]
  have hf_block : ∀ A0 K0 : Matrix (Fin n) (Fin n) (ZMod 2),
      f_bad (Matrix.fromBlocks A0 K0 K0 0) = dotProduct x (K0.mulVec mu) := by
    intro A0 K0
    change dotProduct (Sum.elim 0 x) ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim mu 0)) = dotProduct x (K0.mulVec mu)
    simp only [dotProduct, Matrix.mulVec]
    rw [Fintype.sum_sum_type (f := fun i => Sum.elim (0 : Fin n → ZMod 2) x i * ∑ j : Fin n ⊕ Fin n, (Matrix.fromBlocks A0 K0 K0 0) i j * Sum.elim mu 0 j)]
    simp_rw [Fintype.sum_sum_type (f := fun j => (Matrix.fromBlocks A0 K0 K0 0) _ j * Sum.elim mu 0 j)]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  have hf_rk2 : ∀ Y ∈ L, Y.rank ≤ 2 → f_bad Y = 0 := by
    intro Y hYL hYrk
    rcases Submodule.mem_sup.mp hYL with ⟨X, hXW, Z, hZfree, rfl⟩
    rcases hW_form X hXW with ⟨A0, K0, _, hK0P, rfl⟩
    let Ψ : (J → ZMod 2) →ₗ[ZMod 2] (((Fin n → ZMod 2) ⧸ A) × ((Fin n → ZMod 2) ⧸ B)) :=
      ((Submodule.mkQ A).comp (projL + sh.comp projR)).prod ((Submodule.mkQ B).comp projR)
    have hΨ_Z : ∀ w : J → ZMod 2, Ψ (Z.mulVec w) = 0 := by
      have hZ_E : ∀ Z' ∈ free, ∀ w : J → ZMod 2, Ψ (Z'.mulVec w) = 0 := by
        intro Z' hZ'
        refine Submodule.span_induction (fun M hM w => ?_) (fun w => by simp)
          (fun _ _ _ _ h1 h2 w => by rw [Matrix.add_mulVec, map_add, h1 w, h2 w, add_zero])
          (fun c _ _ h1 w => by rw [Matrix.smul_mulVec, map_smul, h1 w, smul_zero]) hZ'
        have hcol_sum : M.mulVec w = ∑ j : J, w j • (fun i => M i j) := by
          funext i; simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hcol_sum, map_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [map_smul]
        have hkill := hsh_kills_E (fun i => M i j) (hM j)
        have h0 : Ψ (fun i => M i j) = 0 := by
          apply Prod.ext
          · change Submodule.mkQ A (projL (fun i => M i j) + sh (projR (fun i => M i j))) = 0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact hkill.1
          · change Submodule.mkQ B (projR (fun i => M i j)) = 0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact hkill.2
        rw [h0, smul_zero]
      exact hZ_E Z hZfree
    let Q := LinearMap.range (Ψ.comp (Matrix.fromBlocks A0 K0 K0 0 + Z).mulVecLin)
    have hQ_le2 : Module.finrank (ZMod 2) Q ≤ 2 := by
      have h1 : Module.finrank (ZMod 2) Q ≤ (Matrix.fromBlocks A0 K0 K0 0 + Z).rank := by
        have hQeq : Q = (LinearMap.range (Matrix.fromBlocks A0 K0 K0 0 + Z).mulVecLin).map Ψ := LinearMap.range_comp _ _
        exact hQeq ▸ Submodule.finrank_map_le Ψ (LinearMap.range (Matrix.fromBlocks A0 K0 K0 0 + Z).mulVecLin)
      omega
    have hΨ_eq : ∀ w, Ψ ((Matrix.fromBlocks A0 K0 K0 0 + Z).mulVec w) = Ψ ((Matrix.fromBlocks A0 K0 K0 0).mulVec w) :=
      fun w => by rw [Matrix.add_mulVec, map_add, hΨ_Z w, add_zero]
    let p2 : Q →ₗ[ZMod 2] ((Fin n → ZMod 2) ⧸ B) := (LinearMap.snd (ZMod 2) _ _).comp Q.subtype
    have hrg_B : LinearMap.range ((Submodule.mkQ B).comp K0.mulVecLin) ≤ LinearMap.range p2 := by
      rintro _ ⟨v, rfl⟩
      refine ⟨⟨Ψ ((Matrix.fromBlocks A0 K0 K0 0 + Z).mulVec (Sum.elim v 0)), ⟨Sum.elim v 0, rfl⟩⟩, ?_⟩
      change (Ψ ((Matrix.fromBlocks A0 K0 K0 0 + Z).mulVec (Sum.elim v 0))).2 = Submodule.mkQ B (K0.mulVec v)
      rw [hΨ_eq]
      have hR : projR ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim v 0)) = K0.mulVec v := by
        funext i
        change ∑ j : Fin n ⊕ Fin n, (Matrix.fromBlocks A0 K0 K0 0) (Sum.inr i) j * Sum.elim v 0 j = K0.mulVec v i
        rw [Fintype.sum_sum_type]
        simp only [Matrix.mulVec, dotProduct, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, mul_zero, Finset.sum_const_zero, add_zero]
      change Submodule.mkQ B (projR ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim v 0))) = Submodule.mkQ B (K0.mulVec v)
      rw [hR]
    have hker_A : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp K0.mulVecLin)) ≤
        Module.finrank (ZMod 2) (LinearMap.ker p2) := by
      let emb : LinearMap.range ((Submodule.mkQ A).comp K0.mulVecLin) →ₗ[ZMod 2] LinearMap.ker p2 :=
        { toFun := fun q => ⟨⟨(q.val, 0), by
            rcases q.property with ⟨y, hy⟩
            refine ⟨Sum.elim 0 y, ?_⟩
            change Ψ ((Matrix.fromBlocks A0 K0 K0 0 + Z).mulVec (Sum.elim 0 y)) = (q.val, 0)
            rw [hΨ_eq]
            have hR0 : projR ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim 0 y)) = 0 := by
              funext i
              change ∑ j : Fin n ⊕ Fin n, (Matrix.fromBlocks A0 K0 K0 0) (Sum.inr i) j * Sum.elim (0 : Fin n → ZMod 2) y j = 0
              rw [Fintype.sum_sum_type]
              simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Matrix.fromBlocks_apply₂₁,
                Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
            have hL_y : projL ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim 0 y)) = K0.mulVec y := by
              funext i
              change ∑ j : Fin n ⊕ Fin n, (Matrix.fromBlocks A0 K0 K0 0) (Sum.inl i) j * Sum.elim (0 : Fin n → ZMod 2) y j = K0.mulVec y i
              rw [Fintype.sum_sum_type]
              simp only [Matrix.mulVec, dotProduct, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
                Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, mul_zero, Finset.sum_const_zero, zero_add]
            apply Prod.ext
            · change Submodule.mkQ A (projL ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim 0 y)) +
                sh (projR ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim 0 y)))) = q.val
              rw [hR0, map_zero, add_zero, hL_y]
              exact hy
            · change Submodule.mkQ B (projR ((Matrix.fromBlocks A0 K0 K0 0).mulVec (Sum.elim 0 y))) = 0
              rw [hR0, map_zero]⟩, rfl⟩,
          map_add' := fun _ _ => rfl,
          map_smul' := fun _ _ => rfl }
      have hemb_inj : Function.Injective emb := by
        intro q1 q2 h; exact Subtype.ext (congrArg Prod.fst (congrArg Subtype.val (congrArg Subtype.val h)))
      rw [← LinearMap.finrank_range_of_inj hemb_inj]
      exact Submodule.finrank_le _
    have hrn := LinearMap.finrank_range_add_finrank_ker p2
    have hrg_le := Submodule.finrank_mono hrg_B
    have hrk_sum : Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ A).comp K0.mulVecLin)) +
        Module.finrank (ZMod 2) (LinearMap.range ((Submodule.mkQ B).comp K0.mulVecLin)) ≤ 2 := by omega
    rw [map_add, hf_free Z hZfree, add_zero, hf_block]
    exact alt_rank_mod_bound A B K0 (hP_alt K0 hK0P) x mu hx_S hmu_I hrk_sum
  have hf_L : ∀ Y ∈ L, f_bad Y = 0 := by
    intro Y hYL
    rw [hL] at hYL
    refine Submodule.span_induction (fun M hM => hf_rk2 M hM.1 hM.2) (map_zero f_bad)
      (fun _ _ _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c _ _ ha => by rw [map_smul, ha, smul_zero]) hYL
  have hY_mem : Matrix.fromBlocks 0 K K 0 ∈ L :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨0, K, ⟨Matrix.transpose_zero, fun _ => rfl⟩, hKP, rfl⟩)
  have hf0 := hf_L _ hY_mem
  rw [hf_block] at hf0
  have hsym_dot : dotProduct mu (K.mulVec x) = dotProduct x (K.mulVec mu) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hKab : K b a = K a b := congrFun (congrFun (hP_alt K hKP).1 a) b
    rw [hKab]; ring
  rw [hsym_dot, hf0] at hmu_ne0
  exact zero_ne_one hmu_ne0

private lemma dir_backward {n b : ℕ} (P : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (hP_alt : ∀ K ∈ P, K.transpose = K ∧ ∀ i, K i i = 0)
    (hP_rk2 : P = Submodule.span (ZMod 2) {K | K ∈ P ∧ K.rank ≤ 2})
    (I S : Submodule (ZMod 2) (Fin n → ZMod 2)) (hIS : I ≤ S)
    (hfr : Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) S ≤ b)
    (hmap : ∀ K ∈ P, ∀ x, (∀ y ∈ S, (∑ i, y i * x i) = 0) → K.mulVec x ∈ I) :
    let J := Fin n ⊕ Fin n
    let Big := Matrix J J (ZMod 2)
    let W := Submodule.span (ZMod 2) {X : Big | ∃ A K : Matrix (Fin n) (Fin n) (ZMod 2),
      (A.transpose = A ∧ ∀ i, A i i = 0) ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K 0}
    ∃ E : Submodule (ZMod 2) (J → ZMod 2), Module.finrank (ZMod 2) E ≤ b ∧
      let free := Submodule.span (ZMod 2) {X : Big | ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span (ZMod 2) {X : Big | X ∈ L ∧ X.rank ≤ 2} := by
  intro J Big W
  let E : Submodule (ZMod 2) (J → ZMod 2) :=
    { carrier := { w | (fun i => w (Sum.inl i)) ∈ S ∧ (fun i => w (Sum.inr i)) ∈ I },
      zero_mem' := ⟨S.zero_mem, I.zero_mem⟩, add_mem' := fun {w1 w2} h1 h2 => ⟨S.add_mem h1.1 h2.1, I.add_mem h1.2 h2.2⟩,
      smul_mem' := fun c w hw => ⟨S.smul_mem c hw.1, I.smul_mem c hw.2⟩ }
  have hfrE : Module.finrank (ZMod 2) E ≤ b := by
    let eE : E ≃ₗ[ZMod 2] (S × I) :=
      { toFun := fun w => (⟨fun i => w.val (Sum.inl i), w.property.1⟩, ⟨fun i => w.val (Sum.inr i), w.property.2⟩),
        invFun := fun p => ⟨Sum.elim p.1.val p.2.val, ⟨p.1.property, p.2.property⟩⟩,
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl,
        left_inv := fun w => Subtype.ext (funext fun j => by cases j <;> rfl),
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [eE.finrank_eq, Module.finrank_prod]; omega
  refine ⟨E, hfrE, ?_⟩
  let free := Submodule.span (ZMod 2) {X : Big | ∀ j, (fun i => X i j) ∈ E}
  let L := W ⊔ free
  let R2 := Submodule.span (ZMod 2) {X : Big | X ∈ L ∧ X.rank ≤ 2}
  have hfree_le : free ≤ R2 := by
    rw [Submodule.span_le]
    intro Z hZ
    have hexp : Z = ∑ j0 : J, Matrix.of (fun i j => if j = j0 then Z i j0 else 0) := by
      ext i j; simp only [Matrix.sum_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro j0 _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hexp]
    refine Submodule.sum_mem R2 fun j0 _ => Submodule.subset_span ⟨?_, le_trans (rank_le_one_of_col_vec (fun i => Z i j0) j0) (by omega)⟩
    apply Submodule.mem_sup_right
    apply Submodule.subset_span
    intro j
    by_cases hj : j = j0
    · subst hj; simpa only [Matrix.of_apply, ↓reduceIte] using hZ j
    · simp only [Matrix.of_apply, if_neg hj]; exact E.zero_mem
  apply le_antisymm
  · refine sup_le ?_ hfree_le
    rw [Submodule.span_le]
    rintro _ ⟨A0, K, hA0, hKP, rfl⟩
    have hsplit_AK : Matrix.fromBlocks A0 K K 0 = Matrix.fromBlocks A0 0 0 0 + Matrix.fromBlocks 0 K K 0 := by
      ext i j; cases i <;> cases j <;> simp
    rw [hsplit_AK]
    refine Submodule.add_mem R2 ?_ ?_
    · -- A0 block: sum of rank-2 elementary alternating matrices
      have hA_exp : (Matrix.fromBlocks A0 0 0 0 : Big) =
          ∑ p : Fin n × Fin n, if p.1 < p.2 then
            A0 p.1 p.2 • (Matrix.fromBlocks (Matrix.single p.1 p.2 (1 : ZMod 2) + Matrix.single p.2 p.1 (1 : ZMod 2)) 0 0 0 : Big)
          else 0 := by
        have hAsym : ∀ a b : Fin n, A0 b a = A0 a b := fun a b => congrFun (congrFun hA0.1 a) b
        ext i j
        cases i with
        | inl a =>
          cases j with
          | inl b =>
            simp only [Matrix.fromBlocks_apply₁₁, Matrix.sum_apply]
            rcases lt_trichotomy a b with hlt | rfl | hgt
            · rw [Finset.sum_eq_single (a, b)]
              · rw [if_pos hlt]; simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, msingle_apply, smul_eq_mul]
                have hne : a ≠ b := ne_of_lt hlt
                simp [hne, hne.symm]
              · intro p _ hne
                split_ifs with hp
                · simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, msingle_apply]
                  have h1 : ¬ (a = p.1 ∧ b = p.2) := by rintro ⟨rfl, rfl⟩; exact hne rfl
                  have h2 : ¬ (a = p.2 ∧ b = p.1) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hlt hp
                  simp [h1, h2]
                · rfl
              · intro h; exact absurd (Finset.mem_univ _) h
            · rw [hA0.2 a]
              refine (Finset.sum_eq_zero fun p _ => ?_).symm
              split_ifs with hp
              · simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, msingle_apply]
                have h1 : ¬ (a = p.1 ∧ a = p.2) := by rintro ⟨h1, h2⟩; rw [← h1, ← h2] at hp; exact lt_irrefl _ hp
                have h2 : ¬ (a = p.2 ∧ a = p.1) := by rintro ⟨h1, h2⟩; rw [← h1, ← h2] at hp; exact lt_irrefl _ hp
                simp [h1, h2]
              · rfl
            · rw [Finset.sum_eq_single (b, a)]
              · rw [if_pos hgt]; simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, msingle_apply, smul_eq_mul]
                have hne : a ≠ b := ne_of_gt hgt
                simp [hne, hne.symm, hAsym b a]
              · intro p _ hne
                split_ifs with hp
                · simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, msingle_apply]
                  have h1 : ¬ (a = p.1 ∧ b = p.2) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hgt hp
                  have h2 : ¬ (a = p.2 ∧ b = p.1) := by rintro ⟨rfl, rfl⟩; exact hne rfl
                  simp [h1, h2]
                · rfl
              · intro h; exact absurd (Finset.mem_univ _) h
          | inr b =>
            simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.sum_apply]
            refine (Finset.sum_eq_zero fun p _ => ?_).symm
            split_ifs <;> simp
        | inr a =>
          cases j with
          | inl b =>
            simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.sum_apply]
            refine (Finset.sum_eq_zero fun p _ => ?_).symm
            split_ifs <;> simp
          | inr b =>
            simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.sum_apply]
            refine (Finset.sum_eq_zero fun p _ => ?_).symm
            split_ifs <;> simp
      rw [hA_exp]
      refine Submodule.sum_mem R2 fun p _ => ?_
      split_ifs with hlt
      · refine Submodule.smul_mem R2 _ (Submodule.subset_span ⟨?_, ?_⟩)
        · apply Submodule.mem_sup_left
          apply Submodule.subset_span
          refine ⟨Matrix.single p.1 p.2 (1 : ZMod 2) + Matrix.single p.2 p.1 (1 : ZMod 2), 0, ⟨?_, ?_⟩, P.zero_mem, rfl⟩
          · ext a b; simp only [Matrix.transpose_apply, Matrix.add_apply, msingle_apply]
            have ha1 : (b = p.1 ∧ a = p.2) ↔ (a = p.2 ∧ b = p.1) := and_comm
            have ha2 : (b = p.2 ∧ a = p.1) ↔ (a = p.1 ∧ b = p.2) := and_comm
            simp only [ha1, ha2, add_comm]
          · intro a; simp only [Matrix.add_apply, msingle_apply]
            have h1 : ¬ (a = p.1 ∧ a = p.2) := by rintro ⟨h1, h2⟩; rw [← h1, ← h2] at hlt; exact lt_irrefl _ hlt
            have h2 : ¬ (a = p.2 ∧ a = p.1) := by rintro ⟨h1, h2⟩; rw [← h1, ← h2] at hlt; exact lt_irrefl _ hlt
            simp [h1, h2]
        · refine rank_le_two_of_two_vecs _ (Pi.single (Sum.inl p.1) 1) (Pi.single (Sum.inl p.2) 1) fun x => ?_
          refine ⟨x (Sum.inl p.2), x (Sum.inl p.1), ?_⟩
          funext i
          cases i with
          | inl a =>
            change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks (Matrix.single p.1 p.2 (1 : ZMod 2) + Matrix.single p.2 p.1 (1 : ZMod 2)) 0 0 0 : Big) (Sum.inl a) b * x b = _
            rw [Fintype.sum_sum_type]
            simp only [Matrix.fromBlocks_apply₁₁,
              Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
              Matrix.add_apply, msingle_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
              Sum.inl.injEq]
            have hne : p.1 ≠ p.2 := ne_of_lt hlt
            have hneJ : (Sum.inl p.1 : J) ≠ Sum.inl p.2 := fun h => hne (Sum.inl.inj h)
            by_cases ha1 : a = p.1
            · subst ha1
              rw [Finset.sum_eq_single p.2]
              · simp [hne, hne.symm, hneJ, hneJ.symm]
              · intro b _ hne2; simp [hne, hne.symm, hne2]
              · intro h; exact absurd (Finset.mem_univ p.2) h
            · by_cases ha2 : a = p.2
              · subst ha2
                rw [Finset.sum_eq_single p.1]
                · simp [hne, hne.symm, hneJ, hneJ.symm]
                · intro b _ hne1; simp [hne, hne.symm, hne1]
                · intro h; exact absurd (Finset.mem_univ p.1) h
              · have ha1J : (Sum.inl a : J) ≠ Sum.inl p.1 := fun h => ha1 (Sum.inl.inj h)
                have ha2J : (Sum.inl a : J) ≠ Sum.inl p.2 := fun h => ha2 (Sum.inl.inj h)
                simp [ha1, ha2, ha1J, ha2J]
          | inr a =>
            change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks (Matrix.single p.1 p.2 (1 : ZMod 2) + Matrix.single p.2 p.1 (1 : ZMod 2)) 0 0 0 : Big) (Sum.inr a) b * x b = _
            rw [Fintype.sum_sum_type]
            simp only [Matrix.fromBlocks_apply₂₁,
              Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
              Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, reduceCtorEq, ↓reduceIte, mul_zero]
      · exact R2.zero_mem
    · -- K block: reduce via hP_rk2 to K ∈ P with K.rank ≤ 2
      rw [hP_rk2] at hKP
      refine Submodule.span_induction (fun K0 ⟨hK0P, hK0rk⟩ => ?_)
        (by convert R2.zero_mem using 1; ext i j; cases i <;> cases j <;> rfl)
        (fun K1 K2 _ _ ih1 ih2 => by
          have hadd : Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (ZMod 2)) (K1 + K2) (K1 + K2) 0 =
              Matrix.fromBlocks 0 K1 K1 0 + Matrix.fromBlocks 0 K2 K2 0 := by
            ext i j; cases i <;> cases j <;> simp
          rw [hadd]; exact R2.add_mem ih1 ih2)
        (fun c K1 _ ih1 => by
          have hsm : Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (ZMod 2)) (c • K1) (c • K1) 0 =
              c • Matrix.fromBlocks 0 K1 K1 0 := by
            ext i j; cases i <;> cases j <;> simp
          rw [hsm]; exact R2.smul_mem c ih1) hKP
      rcases alt_rank_le_two_wedge K0 (hP_alt K0 hK0P) hK0rk with ⟨u, v, hK0_eq⟩
      have hK0_mv : ∀ x : Fin n → ZMod 2, K0.mulVec x = (dotProduct v x) • u + (dotProduct u x) • v := by
        intro x; funext a
        simp only [Matrix.mulVec, dotProduct, hK0_eq, add_mul, Finset.sum_add_distrib,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        congr 1 <;> (refine Finset.sum_congr rfl fun b _ => by ring)
      by_cases huS : u ∈ S
      · by_cases hvS : v ∈ S
        · -- Both u, v ∈ S: subtract fromBlocks 0 K0 0 0 ∈ free, leaving fromBlocks 0 0 K0 0 of rank ≤ 2
          let Z : Big := Matrix.fromBlocks 0 K0 0 0
          let Y : Big := Matrix.fromBlocks 0 0 K0 0
          have hZ_free : Z ∈ free := by
            apply Submodule.subset_span
            intro j
            cases j with
            | inl a =>
              refine ⟨?_, ?_⟩
              · change (0 : Fin n → ZMod 2) ∈ S; exact S.zero_mem
              · change (0 : Fin n → ZMod 2) ∈ I; exact I.zero_mem
            | inr b =>
              refine ⟨?_, ?_⟩
              · change (fun a => K0 a b) ∈ S
                have hcol : (fun a => K0 a b) = v b • u + u b • v := by
                  funext a; simp only [hK0_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
                rw [hcol]; exact S.add_mem (S.smul_mem _ huS) (S.smul_mem _ hvS)
              · change (0 : Fin n → ZMod 2) ∈ I; exact I.zero_mem
          have hYZ : Matrix.fromBlocks 0 K0 K0 0 = Y + Z := by
            ext i j; change (Matrix.fromBlocks 0 K0 K0 0) i j = Y i j + Z i j
            cases i <;> cases j <;> simp [Y, Z]
          have hY_L : Y ∈ L := by
            have h1 : Y = Matrix.fromBlocks 0 K0 K0 0 + Z := by
              ext i j; change Y i j = (Matrix.fromBlocks 0 K0 K0 0) i j + Z i j
              cases i <;> cases j <;> simp [Y, Z, zmod2_add_self]
            rw [h1]
            exact Submodule.add_mem_sup
              (Submodule.subset_span ⟨0, K0, ⟨Matrix.transpose_zero, fun _ => rfl⟩, hK0P, rfl⟩) hZ_free
          have hY_rk : Y.rank ≤ 2 := by
            refine rank_le_two_of_two_vecs Y (Sum.elim 0 u) (Sum.elim 0 v) fun x => ?_
            refine ⟨dotProduct v (fun a => x (Sum.inl a)), dotProduct u (fun a => x (Sum.inl a)), ?_⟩
            funext i
            cases i with
            | inl a =>
              change ∑ b : Fin n ⊕ Fin n, Y (Sum.inl a) b * x b = _
              rw [Fintype.sum_sum_type]
              simp only [Y, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
                zero_mul, Finset.sum_const_zero, add_zero, Pi.add_apply, Pi.smul_apply, Sum.elim_inl,
                Pi.zero_apply, smul_zero]
            | inr a =>
              change ∑ b : Fin n ⊕ Fin n, Y (Sum.inr a) b * x b = _
              rw [Fintype.sum_sum_type]
              have h1 := congrFun (hK0_mv (fun b => x (Sum.inl b))) a
              simpa only [Y, Matrix.mulVec, dotProduct, Matrix.fromBlocks_apply₂₁,
                Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
                Pi.add_apply, Pi.smul_apply, Sum.elim_inr] using h1
          rw [hYZ]
          exact R2.add_mem (Submodule.subset_span ⟨hY_L, hY_rk⟩) (hfree_le hZ_free)
        · -- v ∉ S: pick x killing S with dotProduct x v = 1, so w = K0.mulVec x = u + c • v ∈ I
          rcases exists_ann_ne_zero S hvS with ⟨x, hxS, hxv⟩
          have hperp : ∀ y ∈ S, (∑ i, y i * x i) = 0 := fun y hy => by rw [← dotProduct, dotProduct_comm]; exact hxS y hy
          have hwI : K0.mulVec x ∈ I := hmap K0 hK0P x hperp
          let w := K0.mulVec x
          have hw_eq : w = u + dotProduct u x • v := by
            dsimp only [w]; rw [hK0_mv x, dotProduct_comm v x, hxv, one_smul]
          have hK0_vw : ∀ a b : Fin n, K0 a b = v a * w b + w a * v b := by
            intro a b
            rw [hK0_eq a b, hw_eq]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have z := zmod2_add_self (dotProduct u x * (v a * v b))
            calc u a * v b + v a * u b = (u a * v b + v a * u b) + (dotProduct u x * (v a * v b) + dotProduct u x * (v a * v b)) := by rw [z, add_zero]
              _ = v a * (u b + dotProduct u x * v b) + (u a + dotProduct u x * v a) * v b := by ring
          let M1 : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => v a * w b
          let M2 : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => w a * v b
          let Z : Big := Matrix.fromBlocks 0 M2 M2 0
          let Y : Big := Matrix.fromBlocks 0 M1 M1 0
          have hZ_free : Z ∈ free := by
            apply Submodule.subset_span
            intro j
            cases j with
            | inl b =>
              refine ⟨by change (0 : Fin n → ZMod 2) ∈ S; exact S.zero_mem, ?_⟩
              change (fun a => w a * v b) ∈ I
              have hcol : (fun a => w a * v b) = v b • w := by funext a; simp [mul_comm]
              rw [hcol]; exact I.smul_mem _ hwI
            | inr b =>
              refine ⟨?_, by change (0 : Fin n → ZMod 2) ∈ I; exact I.zero_mem⟩
              change (fun a => w a * v b) ∈ S
              have hcol : (fun a => w a * v b) = v b • w := by funext a; simp [mul_comm]
              rw [hcol]; exact S.smul_mem _ (hIS hwI)
          have hYZ : Matrix.fromBlocks 0 K0 K0 0 = Y + Z := by
            ext i j; change (Matrix.fromBlocks 0 K0 K0 0) i j = (Matrix.fromBlocks 0 M1 M1 0) i j + (Matrix.fromBlocks 0 M2 M2 0) i j
            cases i <;> cases j
            · simp only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, add_zero]
            · simp only [Matrix.fromBlocks_apply₁₂]; exact hK0_vw _ _
            · simp only [Matrix.fromBlocks_apply₂₁]; exact hK0_vw _ _
            · simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, add_zero]
          have hY_L : Y ∈ L := by
            have h1 : Y = Matrix.fromBlocks 0 K0 K0 0 + Z := by
              rw [hYZ]; ext i j; change Y i j = (Y i j + Z i j) + Z i j; rw [add_assoc, zmod2_add_self, add_zero]
            rw [h1]
            exact Submodule.add_mem_sup
              (Submodule.subset_span ⟨0, K0, ⟨Matrix.transpose_zero, fun _ => rfl⟩, hK0P, rfl⟩) hZ_free
          have hY_rk : Y.rank ≤ 2 := by
            refine rank_le_two_of_two_vecs Y (Sum.elim v 0) (Sum.elim 0 v) fun z => ?_
            refine ⟨dotProduct w (fun b => z (Sum.inr b)), dotProduct w (fun b => z (Sum.inl b)), ?_⟩
            funext i
            cases i with
            | inl a =>
              change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks 0 M1 M1 0) (Sum.inl a) b * z b = _
              rw [Fintype.sum_sum_type]
              simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
                zero_mul, Finset.sum_const_zero, zero_add, Pi.add_apply, Pi.smul_apply, Sum.elim_inl,
                Pi.zero_apply, smul_zero, add_zero, smul_eq_mul, dotProduct, Finset.sum_mul, mul_zero]
              dsimp only [M1]
              refine Finset.sum_congr rfl fun b _ => by ring
            | inr a =>
              change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks 0 M1 M1 0) (Sum.inr a) b * z b = _
              rw [Fintype.sum_sum_type]
              simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
                zero_mul, Finset.sum_const_zero, add_zero, Pi.add_apply, Pi.smul_apply, Sum.elim_inr,
                Pi.zero_apply, smul_zero, zero_add, smul_eq_mul, dotProduct, Finset.sum_mul, mul_zero]
              dsimp only [M1]
              refine Finset.sum_congr rfl fun b _ => by ring
          rw [hYZ]
          exact R2.add_mem (Submodule.subset_span ⟨hY_L, hY_rk⟩) (hfree_le hZ_free)
      · -- u ∉ S: pick x killing S with dotProduct x u = 1, so w = K0.mulVec x = c • u + v ∈ I
        rcases exists_ann_ne_zero S huS with ⟨x, hxS, hxu⟩
        have hperp : ∀ y ∈ S, (∑ i, y i * x i) = 0 := fun y hy => by rw [← dotProduct, dotProduct_comm]; exact hxS y hy
        have hwI : K0.mulVec x ∈ I := hmap K0 hK0P x hperp
        let w := K0.mulVec x
        have hw_eq : w = dotProduct v x • u + v := by
          dsimp only [w]; rw [hK0_mv x, dotProduct_comm u x, hxu, one_smul]
        have hK0_uw : ∀ a b : Fin n, K0 a b = u a * w b + w a * u b := by
          intro a b
          rw [hK0_eq a b, hw_eq]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have z := zmod2_add_self (dotProduct v x * (u a * u b))
          calc u a * v b + v a * u b = (u a * v b + v a * u b) + (dotProduct v x * (u a * u b) + dotProduct v x * (u a * u b)) := by rw [z, add_zero]
            _ = u a * (dotProduct v x * u b + v b) + (dotProduct v x * u a + v a) * u b := by ring
        let M1 : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => u a * w b
        let M2 : Matrix (Fin n) (Fin n) (ZMod 2) := fun a b => w a * u b
        let Z : Big := Matrix.fromBlocks 0 M2 M2 0
        let Y : Big := Matrix.fromBlocks 0 M1 M1 0
        have hZ_free : Z ∈ free := by
          apply Submodule.subset_span
          intro j
          cases j with
          | inl b =>
            refine ⟨by change (0 : Fin n → ZMod 2) ∈ S; exact S.zero_mem, ?_⟩
            change (fun a => w a * u b) ∈ I
            have hcol : (fun a => w a * u b) = u b • w := by funext a; simp [mul_comm]
            rw [hcol]; exact I.smul_mem _ hwI
          | inr b =>
            refine ⟨?_, by change (0 : Fin n → ZMod 2) ∈ I; exact I.zero_mem⟩
            change (fun a => w a * u b) ∈ S
            have hcol : (fun a => w a * u b) = u b • w := by funext a; simp [mul_comm]
            rw [hcol]; exact S.smul_mem _ (hIS hwI)
        have hYZ : Matrix.fromBlocks 0 K0 K0 0 = Y + Z := by
          ext i j; change (Matrix.fromBlocks 0 K0 K0 0) i j = (Matrix.fromBlocks 0 M1 M1 0) i j + (Matrix.fromBlocks 0 M2 M2 0) i j
          cases i <;> cases j
          · simp only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, add_zero]
          · simp only [Matrix.fromBlocks_apply₁₂]; exact hK0_uw _ _
          · simp only [Matrix.fromBlocks_apply₂₁]; exact hK0_uw _ _
          · simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, add_zero]
        have hY_L : Y ∈ L := by
          have h1 : Y = Matrix.fromBlocks 0 K0 K0 0 + Z := by
            rw [hYZ]; ext i j; change Y i j = (Y i j + Z i j) + Z i j; rw [add_assoc, zmod2_add_self, add_zero]
          rw [h1]
          exact Submodule.add_mem_sup
            (Submodule.subset_span ⟨0, K0, ⟨Matrix.transpose_zero, fun _ => rfl⟩, hK0P, rfl⟩) hZ_free
        have hY_rk : Y.rank ≤ 2 := by
          refine rank_le_two_of_two_vecs Y (Sum.elim u 0) (Sum.elim 0 u) fun z => ?_
          refine ⟨dotProduct w (fun b => z (Sum.inr b)), dotProduct w (fun b => z (Sum.inl b)), ?_⟩
          funext i
          cases i with
          | inl a =>
            change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks 0 M1 M1 0) (Sum.inl a) b * z b = _
            rw [Fintype.sum_sum_type]
            simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
              zero_mul, Finset.sum_const_zero, zero_add, Pi.add_apply, Pi.smul_apply, Sum.elim_inl,
              Pi.zero_apply, smul_zero, add_zero, smul_eq_mul, dotProduct, Finset.sum_mul, mul_zero]
            dsimp only [M1]
            refine Finset.sum_congr rfl fun b _ => by ring
          | inr a =>
            change ∑ b : Fin n ⊕ Fin n, (Matrix.fromBlocks 0 M1 M1 0) (Sum.inr a) b * z b = _
            rw [Fintype.sum_sum_type]
            simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
              zero_mul, Finset.sum_const_zero, add_zero, Pi.add_apply, Pi.smul_apply, Sum.elim_inr,
              Pi.zero_apply, smul_zero, zero_add, smul_eq_mul, dotProduct, Finset.sum_mul, mul_zero]
            dsimp only [M1]
            refine Finset.sum_congr rfl fun b _ => by ring
        rw [hYZ]
        exact R2.add_mem (Submodule.subset_span ⟨hY_L, hY_rk⟩) (hfree_le hZ_free)
  · rw [Submodule.span_le]; rintro X ⟨hX, _⟩; exact hX

private lemma main_proof :
let F := ZMod 2
∀ (n : ℕ) (P : Submodule F (Matrix (Fin n) (Fin n) F)),
  let M := Matrix (Fin n) (Fin n) F
  let J := Fin n ⊕ Fin n
  let Big := Matrix J J F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let perp := fun (S : Submodule F (Fin n → F)) (x : Fin n → F) =>
    ∀ y ∈ S, (∑ i, y i * x i) = 0
  (∀ K ∈ P, alt K) →
  P = Submodule.span F {K : M | K ∈ P ∧ K.rank ≤ 2} →
  let W := Submodule.span F {X : Big | ∃ A K : M,
    alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : M)}
  ∀ b : ℕ,
    (∃ E : Submodule F (J → F), Module.finrank F E ≤ b ∧
      let free := Submodule.span F {X : Big | ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span F {X : Big | X ∈ L ∧ X.rank ≤ 2}) ↔
    ∃ I S : Submodule F (Fin n → F), I ≤ S ∧
      Module.finrank F I + Module.finrank F S ≤ b ∧
      ∀ K ∈ P, ∀ x, perp S x → K.mulVec x ∈ I := by
  intro F n P M J Big alt perp hP_alt hP_rk2 W b
  constructor
  · rintro ⟨E, hEb, hLeq⟩
    exact dir_forward P hP_alt E hEb hLeq
  · rintro ⟨I, S, hIS, hfr, hmap⟩
    exact dir_backward P hP_alt hP_rk2 I S hIS hfr hmap

end PEqualNP.Outside.L_lib_968_aux

open PEqualNP.Outside.L_lib_968_aux in
theorem PEqualNP.Outside.L_lib_968 :
let F := ZMod 2
∀ (n : ℕ) (P : Submodule F (Matrix (Fin n) (Fin n) F)),
  let M := Matrix (Fin n) (Fin n) F
  let J := Fin n ⊕ Fin n
  let Big := Matrix J J F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let perp := fun (S : Submodule F (Fin n → F)) (x : Fin n → F) =>
    ∀ y ∈ S, (∑ i, y i * x i) = 0
  (∀ K ∈ P, alt K) →
  P = Submodule.span F {K : M | K ∈ P ∧ K.rank ≤ 2} →
  let W := Submodule.span F {X : Big | ∃ A K : M,
    alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : M)}
  ∀ b : ℕ,
    (∃ E : Submodule F (J → F), Module.finrank F E ≤ b ∧
      let free := Submodule.span F {X : Big | ∀ j, (fun i => X i j) ∈ E}
      let L := W ⊔ free
      L = Submodule.span F {X : Big | X ∈ L ∧ X.rank ≤ 2}) ↔
    ∃ I S : Submodule F (Fin n → F), I ≤ S ∧
      Module.finrank F I + Module.finrank F S ≤ b ∧
      ∀ K ∈ P, ∀ x, perp S x → K.mulVec x ∈ I :=
  main_proof
