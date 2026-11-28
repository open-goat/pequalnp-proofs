import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_lib_895_aux

def localPartner (c : Fin 3) : Fin 8 → Fin 8 :=
  ![![2, 3, 0, 1, 5, 4, 7, 6],
    ![4, 5, 3, 2, 0, 1, 7, 6],
    ![6, 7, 3, 2, 5, 4, 0, 1]] c

lemma localPartner_involutive (c : Fin 3) :
    Function.Involutive (localPartner c) := by
  fin_cases c <;> intro r <;> fin_cases r <;> decide

lemma localPartner_ne (c : Fin 3) (r : Fin 8) : localPartner c r ≠ r := by
  fin_cases c <;> fin_cases r <;> decide

def localPerm (c : Fin 3) : Equiv.Perm (Fin 8) where
  toFun := localPartner c
  invFun := localPartner c
  left_inv := localPartner_involutive c
  right_inv := localPartner_involutive c

lemma localPartner_zero (c : Fin 3) :
    (localPartner c 0).val = 2 + 2*c.val := by
  fin_cases c <;> decide

lemma localPartner_one (c : Fin 3) :
    (localPartner c 1).val = 3 + 2*c.val := by
  fin_cases c <;> decide

lemma localPartner_other (c d : Fin 3) (h : c ≠ d) :
    (localPartner c ⟨2+2*d.val, by omega⟩).val = 3+2*d.val := by
  fin_cases c <;> fin_cases d <;> first | contradiction | decide

lemma local_orientation (c : Fin 3) :
    ∃ u : Fin 8, u.val ∈ ([0,2,4,6] : List Nat) ∧
      (localPartner c u).val ∈ ([0,2,4,6] : List Nat) ∧ localPartner c u ≠ u := by
  refine ⟨0, by decide, ?_, localPartner_ne c 0⟩
  fin_cases c <;> decide

lemma local_triangle (c d : Fin 3) (b : Fin 2) :
    ∃ u : Fin 8, u.val ∈ ([b.val,2+2*d.val,3+2*d.val] : List Nat) ∧
      (localPartner c u).val ∈ ([b.val,2+2*d.val,3+2*d.val] : List Nat) ∧
      localPartner c u ≠ u := by
  fin_cases c <;> fin_cases d <;> fin_cases b <;> decide

def blockPerm {n : Nat} (a : Fin n → Fin 3) : Equiv.Perm (Fin n × Fin 8) where
  toFun p := (p.1, localPartner (a p.1) p.2)
  invFun p := (p.1, localPartner (a p.1) p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact localPartner_involutive (a p.1) p.2
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact localPartner_involutive (a p.1) p.2

def coordinates (n : Nat) : Fin (n*8+1) ≃ (Fin n × Fin 8) ⊕ Fin 1 :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl (Fin 1)))

def globalPerm {n : Nat} (a : Fin n → Fin 3) : Equiv.Perm (Fin (n*8+1)) :=
  (coordinates n).trans
    ((Equiv.sumCongr (blockPerm a) (Equiv.refl (Fin 1))).trans (coordinates n).symm)

lemma globalPerm_involutive {n : Nat} (a : Fin n → Fin 3) :
    Function.Involutive (globalPerm a) := by
  intro x
  apply (coordinates n).injective
  simp only [globalPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases h : coordinates n x with
  | inl p =>
    rcases p with ⟨i,r⟩
    simp [Equiv.sumCongr_apply, blockPerm]
    exact localPartner_involutive (a i) r
  | inr p => rfl

lemma globalPerm_block {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (r : Fin 8) :
    globalPerm a (Fin.castSucc (finProdFinEquiv (i,r))) =
      Fin.castSucc (finProdFinEquiv (i,localPartner (a i) r)) := by
  simp [globalPerm, coordinates, finSumFinEquiv_symm_apply_castSucc, blockPerm]
  rfl

lemma globalPerm_injective {n : Nat} :
    Function.Injective (fun a : Fin n → Fin 3 => globalPerm a) := by
  intro a b h
  funext i
  have hh := congrArg (fun P : Equiv.Perm (Fin (n*8+1)) =>
    P (Fin.castSucc (finProdFinEquiv (i,(0 : Fin 8))))) h
  rw [globalPerm_block,globalPerm_block] at hh
  have hv := congrArg Fin.val hh
  change (localPartner (a i) 0).val + 8*i.val =
    (localPartner (b i) 0).val + 8*i.val at hv
  rw [localPartner_zero,localPartner_zero] at hv
  apply Fin.ext
  omega

lemma globalPerm_last {n : Nat} (a : Fin n → Fin 3) :
    globalPerm a (Fin.last (n*8)) = Fin.last (n*8) := by
  apply (coordinates n).injective
  simp [globalPerm,coordinates,finSumFinEquiv_symm_last]

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux.Comb

abbrev Ban := (Nat × Nat) × (Nat × Nat)
def bits (w v : Nat) := (List.range w).map (fun j => v.testBit j)
def header (n : Nat) := List.replicate n true ++ [false]
def width (n : Nat) := n.log2+1
def legal (n : Nat) (B : List Ban) := 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
def pack (k : Nat) (rows : List (List Nat)) :=
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
def well (k : Nat) (rows : List (List Nat)) := ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k

def flag (i c : Nat) := [8*i+2+2*c,8*i+3+2*c]
def block (n i : Nat) :=
  [[8*i,8*i+2,8*i+4,8*i+6]] ++ (List.range 3).flatMap (fun c =>
    (List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
      [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j])))
def emit (n : Nat) (B : List Ban) :=
  (List.range n).flatMap (block n) ++ B.map (fun e => flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2)

lemma bits_length (w v : Nat) : (bits w v).length = w := by simp [bits]
lemma header_length (n : Nat) : (header n).length = n+1 := by simp [header]
lemma flag_length (i c : Nat) : (flag i c).length = 2 := rfl

lemma flatMap_length_constant {α β : Type*} (L : List α) (F : α → List β) (r : Nat)
    (h : ∀ a ∈ L, (F a).length = r) : (L.flatMap F).length = L.length*r := by
  revert h
  induction L with
  | nil => simp
  | cons a L ih =>
    intro h
    rw [List.flatMap_cons,List.length_append,h a (by simp),ih (fun b hb => h b (by simp [hb]))]
    simp [List.length_cons,Nat.add_mul]
    omega

lemma block_length (n i : Nat) : (block n i).length = 25 := by
  have inner (c : Nat) : ((List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
      [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]))).length = 8 := by
    rw [flatMap_length_constant (List.range 2) _ 4 (by intro b hb; simp)]
    norm_num
  unfold block
  rw [List.length_append,flatMap_length_constant (List.range 3) _ 8 (by intro c hc; exact inner c)]
  norm_num

lemma emit_length (n : Nat) (B : List Ban) : (emit n B).length = 25*n+B.length := by
  unfold emit
  rw [List.length_append,List.length_map,
    flatMap_length_constant (List.range n) (block n) 25 (by intro i hi; exact block_length n i)]
  simp only [List.length_range]
  omega

lemma block_disjoint {i j a b : Nat} (ha : a < 8) (hb : b < 8) (hij : i ≠ j) :
    8*i+a ≠ 8*j+b := by omega

lemma succ_mod_ne (n i : Nat) (hn : 2 ≤ n) (hi : i < n) : i ≠ (i+1) % n := by
  by_cases h : i+1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have eq : i+1 = n := by omega
    rw [eq,Nat.mod_self]
    omega

lemma orientation_well {n i : Nat} (hi : i < n) :
    ([8*i,8*i+2,8*i+4,8*i+6] : List Nat).length = 4 ∧
    ([8*i,8*i+2,8*i+4,8*i+6] : List Nat).Nodup ∧
    ∀ v ∈ ([8*i,8*i+2,8*i+4,8*i+6] : List Nat), v < 8*n+1 := by
  refine ⟨rfl,?_,?_⟩
  · simp [List.nodup_cons] <;> omega
  · intro v hv
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega

lemma triangle_well {n i c b j : Nat} (hn : 2 ≤ n) (hi : i < n)
    (hc : c < 3) (hb : b < 2) (hj : j < 4) :
    ([8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]).length = 4 ∧
    ([8*i+b] ++ flag i c ++ [8*((i+1) % n)+j]).Nodup ∧
    ∀ v ∈ [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j], v < 8*n+1 := by
  have hs : (i+1) % n < n := Nat.mod_lt _ (by omega)
  have hne := succ_mod_ne n i hn hi
  have h0 := block_disjoint (i := i) (j := (i+1) % n) (a := b) (b := j) (by omega) (by omega) hne
  have h1 := block_disjoint (i := i) (j := (i+1) % n) (a := 2+2*c) (b := j) (by omega) (by omega) hne
  have h2 := block_disjoint (i := i) (j := (i+1) % n) (a := 3+2*c) (b := j) (by omega) (by omega) hne
  refine ⟨by simp [flag],?_,?_⟩
  · simp [flag,List.nodup_cons] <;> omega
  · intro v hv
    simp only [flag,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with (rfl | (rfl | rfl)) | rfl <;> omega

lemma ban_well {n i j c d : Nat} (hij : i < j) (hjn : j < n) (hc : c < 3) (hd : d < 3) :
    (flag i c ++ flag j d).length = 4 ∧ (flag i c ++ flag j d).Nodup ∧
    ∀ v ∈ flag i c ++ flag j d, v < 8*n+1 := by
  refine ⟨by simp [flag],?_,?_⟩
  · simp [flag,List.nodup_cons] <;> omega
  · intro v hv
    simp only [flag,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
    rcases hv with (rfl | rfl) | (rfl | rfl) <;> omega

lemma emit_well (n : Nat) (B : List Ban) (h : legal n B) : well (8*n+1) (emit n B) := by
  intro row hrow
  simp only [emit,List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · obtain ⟨i,hi,hrow⟩ := List.mem_flatMap.mp hrow
    have hin := List.mem_range.mp hi
    simp only [block,List.mem_append,List.mem_singleton] at hrow
    rcases hrow with rfl | hrow
    · exact orientation_well hin
    · obtain ⟨c,hc,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨b,hb,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hrow
      exact triangle_well h.1 hin (List.mem_range.mp hc) (List.mem_range.mp hb) (List.mem_range.mp hj)
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hrow
    obtain ⟨hij,hjn,hc,hd⟩ := h.2 e he
    exact ban_well hij hjn hc hd

lemma pack_length_of_well (k : Nat) (rows : List (List Nat)) (h : well k rows) :
    (pack k rows).length = k+1+4*rows.length*width k := by
  unfold pack
  rw [List.length_append,header_length,
    flatMap_length_constant rows (fun row => row.flatMap (bits (width k))) (4*width k) ?_]
  · ring
  · intro row hrow
    rw [flatMap_length_constant row (bits (width k)) (width k) (by intro v hv; exact bits_length _ _)]
    rw [(h row hrow).1]

lemma emit_pack_length (n : Nat) (B : List Ban) (h : legal n B) :
    (pack (8*n+1) (emit n B)).length =
      (8*n+1)+1+4*(25*n+B.length)*width (8*n+1) := by
  rw [pack_length_of_well _ _ (emit_well n B h),emit_length]
end PEqualNP.Outside.L_lib_895_aux.Comb

namespace PEqualNP.Outside.L_lib_895_aux.Comb
open PEqualNP.Outside.L_lib_895_aux

def valid (n : Nat) (B : List Ban) (a : Fin n → Fin 3) :=
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2

def wins (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) :=
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k,
    u.val ∈ row ∧ (P u).val ∈ row ∧ P u ≠ u

def coord {n : Nat} (i : Fin n) (r : Fin 8) : Fin (n*8+1) :=
  Fin.castSucc (finProdFinEquiv (i,r))
lemma coord_val {n : Nat} (i : Fin n) (r : Fin 8) :
    (coord i r).val = r.val+8*i.val := rfl
lemma globalPerm_coord {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (r : Fin 8) :
    globalPerm a (coord i r) = coord i (localPartner (a i) r) := globalPerm_block a i r

def hit {n : Nat} (a : Fin n → Fin 3) (row : List Nat) :=
  ∃ u : Fin (n*8+1), u.val ∈ row ∧ (globalPerm a u).val ∈ row ∧ globalPerm a u ≠ u

lemma hit_mono {n : Nat} {a : Fin n → Fin 3} {row row' : List Nat}
    (h : hit a row) (hs : row ⊆ row') : hit a row' := by
  obtain ⟨u,hu,hpu,hne⟩ := h
  exact ⟨u,hs hu,hs hpu,hne⟩

lemma lift_local {n : Nat} (a : Fin n → Fin 3) (i : Fin n) (L row : List Nat)
    (hl : ∃ r : Fin 8, r.val ∈ L ∧ (localPartner (a i) r).val ∈ L ∧ localPartner (a i) r ≠ r)
    (hm : ∀ x ∈ L, 8*i.val+x ∈ row) : hit a row := by
  obtain ⟨r,hr,hpr,hne⟩ := hl
  refine ⟨coord i r,?_,?_,?_⟩
  · simpa only [coord_val,Nat.add_comm] using hm r.val hr
  · rw [globalPerm_coord,coord_val]
    simpa only [Nat.add_comm] using hm (localPartner (a i) r).val hpr
  · rw [globalPerm_coord]
    intro eq
    have hv := congrArg Fin.val eq
    rw [coord_val,coord_val] at hv
    exact hne (Fin.ext (by omega))

lemma orientation_hit {n i : Nat} (a : Fin n → Fin 3) (hi : i < n) :
    hit a [8*i,8*i+2,8*i+4,8*i+6] := by
  apply lift_local a ⟨i,hi⟩ [0,2,4,6] _ (local_orientation _)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

lemma triangle_hit {n i c b : Nat} (a : Fin n → Fin 3) (hi : i < n)
    (hc : c < 3) (hb : b < 2) (pad : Nat) :
    hit a ([8*i+b] ++ flag i c ++ [pad]) := by
  apply lift_local a ⟨i,hi⟩ [b,2+2*c,3+2*c] _
    (local_triangle (a ⟨i,hi⟩) ⟨c,hc⟩ ⟨b,hb⟩)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [flag,Nat.add_assoc]

lemma assignment_lookup {n : Nat} (a : Fin n → Fin 3) (i : Fin n) :
    (List.ofFn (fun j => (a j).val)).getD i.val 3 = (a i).val := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma flag_hit {n i c : Nat} (a : Fin n → Fin 3) (hi : i < n) (hc : c < 3)
    (hne : (a ⟨i,hi⟩).val ≠ c) : hit a (flag i c) := by
  let ii : Fin n := ⟨i,hi⟩
  let cc : Fin 3 := ⟨c,hc⟩
  have hn : a ii ≠ cc := by
    intro h
    exact hne (congrArg Fin.val h)
  let r : Fin 8 := ⟨2+2*c,by omega⟩
  have hr : (localPartner (a ii) r).val = 3+2*c := localPartner_other (a ii) cc hn
  apply lift_local a ii [2+2*c,3+2*c] _
    ⟨r,by simp [r],by simp [hr],localPartner_ne _ _⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> simp [flag,ii,Nat.add_assoc]

lemma ban_hit {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) (e : Ban) (he : e ∈ B) :
    hit a (flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2) := by
  obtain ⟨hij,hjn,hc,hd⟩ := hlegal.2 e he
  have hin : e.1.1 < n := by omega
  have hv := hvalid e he
  rw [assignment_lookup a ⟨e.1.1,hin⟩,assignment_lookup a ⟨e.2.1,hjn⟩] at hv
  rcases hv with hv | hv
  · apply hit_mono (flag_hit a hin hc hv)
    intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  · apply hit_mono (flag_hit a hjn hd hv)
    intro x hx
    exact List.mem_append.mpr (Or.inr hx)

lemma globalPerm_wins {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) : wins (n*8+1) (emit n B) (globalPerm a) := by
  refine ⟨globalPerm_involutive a,?_⟩
  intro row hrow
  change hit a row
  simp only [emit,List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · obtain ⟨i,hi,hrow⟩ := List.mem_flatMap.mp hrow
    have hin := List.mem_range.mp hi
    simp only [block,List.mem_append,List.mem_singleton] at hrow
    rcases hrow with rfl | hrow
    · exact orientation_hit a hin
    · obtain ⟨c,hc,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨b,hb,hrow⟩ := List.mem_flatMap.mp hrow
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hrow
      exact triangle_hit a hin (List.mem_range.mp hc) (List.mem_range.mp hb) _
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hrow
    exact ban_hit B hlegal a hvalid e he

lemma forward_solution {n : Nat} (B : List Ban) (hlegal : legal n B) (a : Fin n → Fin 3)
    (hvalid : valid n B a) : ∃ P : Equiv.Perm (Fin (8*n+1)), wins (8*n+1) (emit n B) P := by
  have hh : ∃ P : Equiv.Perm (Fin (n*8+1)), wins (n*8+1) (emit n B) P :=
    ⟨globalPerm a,globalPerm_wins B hlegal a hvalid⟩
  have heq : n*8+1 = 8*n+1 := by omega
  exact heq ▸ hh
end PEqualNP.Outside.L_lib_895_aux.Comb

namespace PEqualNP.Outside.L_lib_895_aux.Comb
open PEqualNP.Outside.L_lib_895_aux

lemma ports_miss_ban {i j c d b : Nat} (hij : i < j) (hc : c < 3) (hd : d < 3) (hb : b < 2) :
    8*i+b ∉ flag i c ++ flag j d ∧ 8*j+b ∉ flag i c ++ flag j d := by
  constructor <;> simp [flag] <;> omega

lemma not_hit_selected_flags {n : Nat} (a : Fin n → Fin 3) (i j : Fin n)
    (hij : i.val < j.val) (c d : Nat) (hc : c < 3) (hd : d < 3)
    (hci : (a i).val = c) (hdj : (a j).val = d) :
    ¬ hit a (flag i.val c ++ flag j.val d) := by
  intro ⟨u,hu,hpu,hne⟩
  simp only [flag,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with (he | ho) | (he | ho)
  · have eq : u = coord i (localPartner (a i) 0) := by
      apply Fin.ext
      rw [coord_val,localPartner_zero,hci]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 0) (by omega)).1 (by simpa using hpu)
  · have eq : u = coord i (localPartner (a i) 1) := by
      apply Fin.ext
      rw [coord_val,localPartner_one,hci]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 1) (by omega)).1 (by simpa [Nat.add_comm] using hpu)
  · have eq : u = coord j (localPartner (a j) 0) := by
      apply Fin.ext
      rw [coord_val,localPartner_zero,hdj]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 0) (by omega)).2 (by simpa using hpu)
  · have eq : u = coord j (localPartner (a j) 1) := by
      apply Fin.ext
      rw [coord_val,localPartner_one,hdj]
      omega
    rw [eq,globalPerm_coord,localPartner_involutive,coord_val] at hpu
    exact (ports_miss_ban hij hc hd (b := 1) (by omega)).2 (by simpa [Nat.add_comm] using hpu)

lemma globalPerm_valid_of_wins {n : Nat} (B : List Ban) (hlegal : legal n B)
    (a : Fin n → Fin 3) (hwins : wins (n*8+1) (emit n B) (globalPerm a)) : valid n B a := by
  intro e he
  obtain ⟨hij,hjn,hc,hd⟩ := hlegal.2 e he
  have hin : e.1.1 < n := by omega
  let i : Fin n := ⟨e.1.1,hin⟩
  let j : Fin n := ⟨e.2.1,hjn⟩
  rw [assignment_lookup a i,assignment_lookup a j]
  by_cases hci : (a i).val = e.1.2
  · by_cases hdj : (a j).val = e.2.2
    · have hr : flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2 ∈ emit n B := by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨e,he,rfl⟩)
      exact False.elim (not_hit_selected_flags a i j hij _ _ hc hd hci hdj (hwins.2 _ hr))
    · exact Or.inr hdj
  · exact Or.inl hci

lemma valid_iff_globalPerm_wins {n : Nat} (B : List Ban) (hlegal : legal n B)
    (a : Fin n → Fin 3) : valid n B a ↔ wins (n*8+1) (emit n B) (globalPerm a) :=
  ⟨globalPerm_wins B hlegal a,globalPerm_valid_of_wins B hlegal a⟩

def solutionMap {n : Nat} (B : List Ban) (hlegal : legal n B) :
    {a : Fin n → Fin 3 // valid n B a} →
    {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P} :=
  fun a => ⟨globalPerm a.val,globalPerm_wins B hlegal a.val a.property⟩

lemma solutionMap_injective {n : Nat} (B : List Ban) (hlegal : legal n B) :
    Function.Injective (solutionMap B hlegal) := by
  intro a b h
  apply Subtype.ext
  apply globalPerm_injective
  exact congrArg Subtype.val h

def CanonicalConverse (n : Nat) (B : List Ban) : Prop :=
  ∀ P : Equiv.Perm (Fin (n*8+1)), wins (n*8+1) (emit n B) P →
    ∃ a : Fin n → Fin 3, globalPerm a = P

lemma solutionMap_surjective_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    Function.Surjective (solutionMap B hlegal) := by
  intro P
  obtain ⟨a,ha⟩ := remaining_canonical_converse P.val P.property
  have hw : wins (n*8+1) (emit n B) (globalPerm a) := by rw [ha]; exact P.property
  refine ⟨⟨a,globalPerm_valid_of_wins B hlegal a hw⟩,?_⟩
  apply Subtype.ext
  exact ha

noncomputable def solutionsEquiv_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    {a : Fin n → Fin 3 // valid n B a} ≃
    {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P} :=
  Equiv.ofBijective (solutionMap B hlegal)
    ⟨solutionMap_injective B hlegal,solutionMap_surjective_of_canonical_converse B hlegal remaining_canonical_converse⟩

lemma bijection_of_canonical_converse {n : Nat} (B : List Ban) (hlegal : legal n B)
    (remaining_canonical_converse : CanonicalConverse n B) :
    Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (8*n+1)) // wins (8*n+1) (emit n B) P}) := by
  have hh : Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (n*8+1)) // wins (n*8+1) (emit n B) P}) :=
    ⟨solutionsEquiv_of_canonical_converse B hlegal remaining_canonical_converse⟩
  have heq : n*8+1 = 8*n+1 := by omega
  exact heq ▸ hh
end PEqualNP.Outside.L_lib_895_aux.Comb

namespace PEqualNP.Outside.L_lib_895_aux

theorem padded_set_forcing {α : Type*} [DecidableEq α] (P : α → α)
    (hP : Function.Involutive P) (T D : Finset α) (hcard : T.card < D.card)
    (hwin : ∀ x ∈ D, ∃ u ∈ insert x T, P u ∈ insert x T ∧ P u ≠ u) :
    ∃ u ∈ T, P u ∈ T ∧ P u ≠ u := by
  classical
  by_contra hnone
  have hno : ∀ u ∈ T, P u ∈ T → P u = u := by
    intro u hu hpu
    by_contra hneq
    exact hnone ⟨u,hu,hpu,hneq⟩
  have hmap : ∀ x ∈ D, P x ∈ T := by
    intro x hx
    obtain ⟨u,hu,hpu,hneq⟩ := hwin x hx
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases Finset.mem_insert.mp hpu with hfix | hpT
      · exact False.elim (hneq hfix)
      · exact hpT
    · rcases Finset.mem_insert.mp hpu with heq | hpT
      · rw [← heq,hP u]
        exact hu
      · exact False.elim (hneq (hno u hu hpT))
  have hle : D.card ≤ T.card := Finset.card_le_card_of_injOn P
    (fun x hx => hmap x hx) (fun a _ b _ hab => hP.injective hab)
  omega

theorem padded_triangle_forcing {α : Type*} [DecidableEq α] (P : α → α)
    (hP : Function.Involutive P) (T D : Finset α) (hT : T.card ≤ 3) (hD : 4 ≤ D.card)
    (hwin : ∀ x ∈ D, ∃ u ∈ insert x T, P u ∈ insert x T ∧ P u ≠ u) :
    ∃ u ∈ T, P u ∈ T ∧ P u ≠ u :=
  padded_set_forcing P hP T D (by omega) hwin

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
lemma involution_reverse {α : Type*} {P : α → α} (hP : Function.Involutive P)
    {a b : α} (h : P a = b) : P b = a := by rw [← h,hP a]
lemma triple_pair_cases {α : Type*} [DecidableEq α] {P : α → α} (hP : Function.Involutive P)
    (a b c : α)
    (hw : ∃ u ∈ ({a,b,c} : Finset α), P u ∈ ({a,b,c} : Finset α) ∧ P u ≠ u) :
    P a = b ∨ P a = c ∨ P b = c := by
  obtain ⟨u,hu,hpu,hneq⟩ := hw
  simp only[Finset.mem_insert,Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl | rfl
  · rcases hpu with h | h | h
    · exact False.elim (hneq h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hpu with h | h | h
    · exact Or.inl (involution_reverse hP h)
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (h))
  · rcases hpu with h | h | h
    · exact Or.inr (Or.inl (involution_reverse hP h))
    · exact Or.inr (Or.inr ((involution_reverse hP h)))
    · exact False.elim (hneq h)
lemma quad_pair_cases {α : Type*} [DecidableEq α] {P : α → α} (hP : Function.Involutive P)
    (a b c d : α)
    (hw : ∃ u ∈ ({a,b,c,d} : Finset α), P u ∈ ({a,b,c,d} : Finset α) ∧ P u ≠ u) :
    P a = b ∨ P a = c ∨ P a = d ∨ P b = c ∨ P b = d ∨ P c = d := by
  obtain ⟨u,hu,hpu,hneq⟩ := hw
  simp only[Finset.mem_insert,Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl | rfl | rfl
  · rcases hpu with h | h | h | h
    · exact False.elim (hneq h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases hpu with h | h | h | h
    · exact Or.inl (involution_reverse hP h)
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hpu with h | h | h | h
    · exact Or.inr (Or.inl (involution_reverse hP h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (involution_reverse hP h))))
    · exact False.elim (hneq h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
  · rcases hpu with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (involution_reverse hP h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (involution_reverse hP h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((involution_reverse hP h))))))
    · exact False.elim (hneq h)
end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

lemma ambient_classification {α : Type*} (P : α → α) (v : Fin 8 → α)
    (hv : Function.Injective v) (hP : Function.Involutive P)
    (h00 : P (v 0) = v 2 ∨ P (v 0) = v 3 ∨ P (v 2) = v 3)
    (h01 : P (v 1) = v 2 ∨ P (v 1) = v 3 ∨ P (v 2) = v 3)
    (h10 : P (v 0) = v 4 ∨ P (v 0) = v 5 ∨ P (v 4) = v 5)
    (h11 : P (v 1) = v 4 ∨ P (v 1) = v 5 ∨ P (v 4) = v 5)
    (h20 : P (v 0) = v 6 ∨ P (v 0) = v 7 ∨ P (v 6) = v 7)
    (h21 : P (v 1) = v 6 ∨ P (v 1) = v 7 ∨ P (v 6) = v 7)
    (ho : P (v 0) = v 2 ∨ P (v 0) = v 4 ∨ P (v 0) = v 6 ∨
      P (v 2) = v 4 ∨ P (v 2) = v 6 ∨ P (v 4) = v 6) :
    ∃ c : Fin 3, ∀ r : Fin 8, P (v r) = v (localPartner c r) := by
  have hi0 := hP (v 0)
  have hi1 := hP (v 1)
  have hi2 := hP (v 2)
  have hi3 := hP (v 3)
  have hi4 := hP (v 4)
  have hi5 := hP (v 5)
  have hi6 := hP (v 6)
  have hi7 := hP (v 7)
  rcases ho with h|h|h|h|h|h
  · refine ⟨0,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  · refine ⟨1,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  · refine ⟨2,?_⟩
    intro r
    fin_cases r <;> simp_all [localPartner,hv.eq_iff] <;> aesop (add simp hv.eq_iff)
  all_goals exfalso
  all_goals simp_all [hv.eq_iff]
  all_goals aesop (add simp hv.eq_iff)

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
open PEqualNP.Outside.L_lib_895_aux.Comb

lemma coordinate_cover {n : Nat} (x : Fin (n*8+1)) (hx : x ≠ Fin.last (n*8)) :
    ∃ i : Fin n, ∃ r : Fin 8, x = coord i r := by
  have hv : x.val ≠ n*8 := fun h => hx (Fin.ext h)
  let y : Fin (n*8) := ⟨x.val,by omega⟩
  obtain ⟨⟨i,r⟩,hh⟩ := (finProdFinEquiv : Fin n × Fin 8 ≃ Fin (n*8)).surjective y
  refine ⟨i,r,?_⟩
  apply Fin.ext
  exact (congrArg Fin.val hh).symm

lemma reconstruct_global {n : Nat} (P : Equiv.Perm (Fin (n*8+1)))
    (hP : Function.Involutive P) (a : Fin n → Fin 3)
    (hblock : ∀ i r, P (coord i r) = coord i (localPartner (a i) r)) :
    globalPerm a = P := by
  have hlast : P (Fin.last (n*8)) = Fin.last (n*8) := by
    by_contra hneq
    obtain ⟨i,r,he⟩ := coordinate_cover (P (Fin.last (n*8))) hneq
    have hh := hP (Fin.last (n*8))
    rw [he,hblock i r] at hh
    have hlt : (coord i (localPartner (a i) r)).val < n*8 :=
      (finProdFinEquiv (i,localPartner (a i) r)).isLt
    have hv := congrArg Fin.val hh
    change (coord i (localPartner (a i) r)).val = n*8 at hv
    omega
  apply Equiv.ext
  intro x
  by_cases hx : x = Fin.last (n*8)
  · subst x
    rw [globalPerm_last,hlast]
  · obtain ⟨i,r,rfl⟩ := coordinate_cover x hx
    exact (globalPerm_coord a i r).trans (hblock i r).symm

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
open PEqualNP.Outside.L_lib_895_aux.Comb

def basePort (b : Fin 2) : Fin 8 := ⟨b.val,by have := b.isLt; omega⟩
def evenPort (c : Fin 3) : Fin 8 := ⟨2+2*c.val,by have := c.isLt; omega⟩
def oddPort (c : Fin 3) : Fin 8 := ⟨3+2*c.val,by have := c.isLt; omega⟩
def padPort (j : Fin 4) : Fin 8 := ⟨j.val,by have := j.isLt; omega⟩
def nextIndex {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val+1) % n,Nat.mod_lt _ (by have := i.isLt; omega)⟩
def padCoord {n : Nat} (i : Fin n) (j : Fin 4) : Fin (n*8+1) :=
  coord (nextIndex i) (padPort j)

lemma coord_injective {n : Nat} (i : Fin n) : Function.Injective (coord i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  rw [coord_val,coord_val] at hh
  omega
lemma padCoord_injective {n : Nat} (i : Fin n) : Function.Injective (padCoord i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change r.val+8*((i.val+1) % n) = s.val+8*((i.val+1) % n) at hh
  omega

lemma orientation_mem_emit {n : Nat} (B : List Ban) (i : Fin n) :
    [8*i.val,8*i.val+2,8*i.val+4,8*i.val+6] ∈ emit n B := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
lemma triangle_mem_emit {n : Nat} (B : List Ban) (i : Fin n)
    (c : Fin 3) (b : Fin 2) (j : Fin 4) :
    [8*i.val+b.val] ++ flag i.val c.val ++ [8*((i.val+1) % n)+j.val] ∈ emit n B := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨c.val,List.mem_range.mpr c.isLt,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b.val,List.mem_range.mpr b.isLt,?_⟩
  exact List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩

lemma fin_mem_of_val_mem {k : Nat} (u : Fin k) (L : List (Fin k))
    (h : u.val ∈ L.map Fin.val) : u ∈ L := by
  obtain ⟨v,hv,heq⟩ := List.mem_map.mp h
  have hvu : v = u := Fin.ext heq
  simpa [hvu] using hv
lemma pair_from_list {k : Nat} (P : Equiv.Perm (Fin k)) (L : List (Fin k))
    (h : ∃ u : Fin k, u.val ∈ L.map Fin.val ∧ (P u).val ∈ L.map Fin.val ∧ P u ≠ u) :
    ∃ u ∈ L.toFinset, P u ∈ L.toFinset ∧ P u ≠ u := by
  obtain ⟨u,hu,hpu,hneq⟩ := h
  exact ⟨u,List.mem_toFinset.mpr (fin_mem_of_val_mem u L hu),
    List.mem_toFinset.mpr (fin_mem_of_val_mem (P u) L hpu),hneq⟩

lemma orientation_core_pair {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P) (i : Fin n) :
    ∃ u ∈ ({coord i 0,coord i 2,coord i 4,coord i 6} : Finset (Fin (n*8+1))),
      P u ∈ ({coord i 0,coord i 2,coord i 4,coord i 6} : Finset (Fin (n*8+1))) ∧ P u ≠ u := by
  let L : List (Fin (n*8+1)) := [coord i 0,coord i 2,coord i 4,coord i 6]
  have heq : L.map Fin.val = [8*i.val,8*i.val+2,8*i.val+4,8*i.val+6] := by
    simp [L,coord_val,Nat.add_comm]
  have hh := hw.2 _ (orientation_mem_emit B i)
  rw [← heq] at hh
  have hp := pair_from_list P L hh
  simpa [L] using hp

lemma triangle_core_pair {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P)
    (i : Fin n) (c : Fin 3) (b : Fin 2) :
    ∃ u ∈ ({coord i (basePort b),coord i (evenPort c),coord i (oddPort c)} : Finset (Fin (n*8+1))),
      P u ∈ ({coord i (basePort b),coord i (evenPort c),coord i (oddPort c)} : Finset (Fin (n*8+1))) ∧ P u ≠ u := by
  let T : Finset (Fin (n*8+1)) := {coord i (basePort b),coord i (evenPort c),coord i (oddPort c)}
  let D : Finset (Fin (n*8+1)) := Finset.univ.image (padCoord i)
  have hD : 4 ≤ D.card := by
    dsimp [D]
    rw [Finset.card_image_of_injective _ (padCoord_injective i)]
    simp
  apply padded_triangle_forcing P hw.1 T D Finset.card_le_three hD
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  let L : List (Fin (n*8+1)) :=
    [coord i (basePort b),coord i (evenPort c),coord i (oddPort c),padCoord i j]
  have heq : L.map Fin.val =
      [8*i.val+b.val] ++ flag i.val c.val ++ [8*((i.val+1) % n)+j.val] := by
    simp [L,coord_val,basePort,evenPort,oddPort,padCoord,padPort,nextIndex,flag,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hh := hw.2 _ (triangle_mem_emit B i c b j)
  rw [← heq] at hh
  have hp := pair_from_list P L hh
  have hs : L.toFinset = insert (padCoord i j) T := by
    ext y
    simp [L,T,or_assoc,or_left_comm,or_comm]
  simpa only [hs] using hp

lemma block_selected {n : Nat} (B : List Ban)
    (P : Equiv.Perm (Fin (n*8+1))) (hw : wins (n*8+1) (emit n B) P) (i : Fin n) :
    ∃ c : Fin 3, ∀ r : Fin 8, P (coord i r) = coord i (localPartner c r) := by
  have ht (c : Fin 3) (b : Fin 2) := triple_pair_cases hw.1
    (coord i (basePort b)) (coord i (evenPort c)) (coord i (oddPort c))
    (triangle_core_pair B P hw i c b)
  apply ambient_classification P (coord i) (coord_injective i) hw.1
  · simpa [basePort,evenPort,oddPort] using ht 0 0
  · simpa [basePort,evenPort,oddPort] using ht 0 1
  · simpa [basePort,evenPort,oddPort] using ht 1 0
  · simpa [basePort,evenPort,oddPort] using ht 1 1
  · simpa [basePort,evenPort,oddPort] using ht 2 0
  · simpa [basePort,evenPort,oddPort] using ht 2 1
  · exact quad_pair_cases hw.1 _ _ _ _ (orientation_core_pair B P hw i)

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
open PEqualNP.Outside.L_lib_895_aux.Comb

lemma canonical_converse (n : Nat) (B : List Ban) : CanonicalConverse n B := by
  classical
  intro P hw
  let a : Fin n → Fin 3 := fun i => Classical.choose (block_selected B P hw i)
  have ha : ∀ i r, P (coord i r) = coord i (localPartner (a i) r) :=
    fun i => Classical.choose_spec (block_selected B P hw i)
  exact ⟨a,reconstruct_global P hw.1 a ha⟩

theorem emitted_bijection {n : Nat} (B : List Ban) (hlegal : legal n B) :
    Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
      {P : Equiv.Perm (Fin (8*n+1)) // wins (8*n+1) (emit n B) P}) :=
  bijection_of_canonical_converse B hlegal (canonical_converse n B)

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

def bits (w v : Nat) : List Bool := (List.range w).map (fun j => v.testBit j)

lemma bits_shift_tag (w i tag : Nat) (ht : tag < 8) :
    bits (w+3) (8*i+tag) = bits 3 tag ++ bits w i := by
  simp only [bits]
  rw [show w+3=3+w by omega,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' : j < 3 := List.mem_range.mp hj
    simpa only [show (2:Nat)^3=8 from rfl,if_pos hj'] using
      (Nat.testBit_two_pow_mul_add i (b:=tag) (i:=3) ht j)
  · apply List.map_congr_left
    intro j hj
    have hb : ¬3+j < 3 := by omega
    simpa only [show (2:Nat)^3=8 from rfl,if_neg hb,Nat.add_sub_cancel_left,Function.comp_def] using
      (Nat.testBit_two_pow_mul_add i (b:=tag) (i:=3) ht (3+j))

lemma flag_even_tag_lt (c : Nat) (hc : c<3) : 2+2*c < 8 := by omega
lemma flag_odd_tag_lt (c : Nat) (hc : c<3) : 3+2*c < 8 := by omega

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

abbrev Ban := (Nat × Nat) × (Nat × Nat)
def width (n : Nat) := n.log2+1
def header (n : Nat) := List.replicate n true ++ [false]
def legalRecord (n : Nat) (e : Ban) : Prop :=
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3

def recordBits (n : Nat) (e : Ban) :=
  bits (width n) e.1.1 ++ bits 2 e.1.2 ++ bits (width n) e.2.1 ++ bits 2 e.2.2

def enc (n : Nat) (B : List Ban) := header n ++ B.flatMap (recordBits n)
def legal (n : Nat) (B : List Ban) := 2≤n ∧ ∀ e∈B, legalRecord n e

lemma bits_length (w v : Nat) : (bits w v).length = w := by simp [bits]
lemma recordBits_length (n : Nat) (e : Ban) : (recordBits n e).length = 2*width n+4 := by
  simp only [recordBits,List.length_append,bits_length]; omega

lemma bits_injective (w a b : Nat) (ha : a < 2^w) (hb : b < 2^w)
    (h : bits w a = bits w b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<w
  · have hh := congrArg (fun l : List Bool => l.getD j false) h
    simpa [bits,List.getD_eq_getElem?_getD,hj] using hh
  · have hp : 2^w ≤ 2^j := by gcongr; omega
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp),Nat.testBit_lt_two_pow (hb.trans_le hp)]

lemma header_unique (n m : Nat) (a b : List Bool)
    (h : List.replicate n true ++ false::a = List.replicate m true ++ false::b) : n=m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    cases m with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      apply congrArg Nat.succ
      apply ih m
      simpa using (List.cons.inj h).2

lemma recordBits_injective (n : Nat) (a b : Ban) (ha : legalRecord n a) (hb : legalRecord n b)
    (h : recordBits n a = recordBits n b) : a=b := by
  dsimp only [legalRecord] at ha hb
  simp only [recordBits,List.append_assoc] at h
  obtain ⟨hi,h⟩ := List.append_inj h (by simp [bits_length])
  obtain ⟨hc,h⟩ := List.append_inj h (by simp [bits_length])
  obtain ⟨hj,hd⟩ := List.append_inj h (by simp [bits_length])
  have hn : n < 2^(width n) := Nat.lt_log2_self
  have hi' := bits_injective (width n) a.1.1 b.1.1 (lt_trans (lt_trans ha.1 ha.2.1) hn)
    (lt_trans (lt_trans hb.1 hb.2.1) hn) hi
  have hj' := bits_injective (width n) a.2.1 b.2.1 (lt_trans ha.2.1 hn) (lt_trans hb.2.1 hn) hj
  have hc' := bits_injective 2 a.1.2 b.1.2 (by omega) (by omega) hc
  have hd' := bits_injective 2 a.2.2 b.2.2 (by omega) (by omega) hd
  exact Prod.ext (Prod.ext hi' hc') (Prod.ext hj' hd')

lemma payload_injective (n : Nat) (B : List Ban) : ∀ B' : List Ban,
    (∀ e∈B, legalRecord n e) → (∀ e∈B', legalRecord n e) →
    B.flatMap (recordBits n) = B'.flatMap (recordBits n) → B=B' := by
  induction B with
  | nil =>
    intro B' hB hB' h
    cases B' with
    | nil => rfl
    | cons e es =>
      have hh := congrArg List.length h
      simp only [List.flatMap_nil,List.length_nil,List.flatMap_cons,List.length_append,recordBits_length] at hh
      omega
  | cons e es ih =>
    intro B' hB hB' h
    cases B' with
    | nil =>
      have hh := congrArg List.length h
      simp only [List.flatMap_nil,List.length_nil,List.flatMap_cons,List.length_append,recordBits_length] at hh
      omega
    | cons e' es' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨hh,ht⟩ := List.append_inj h (by rw [recordBits_length,recordBits_length])
      have he := recordBits_injective n e e' (hB e List.mem_cons_self) (hB' e' List.mem_cons_self) hh
      have hs := ih es' (fun a ha => hB a (List.mem_cons_of_mem e ha))
        (fun a ha => hB' a (List.mem_cons_of_mem e' ha)) ht
      rw [he,hs]

theorem enc_legal_injective (n m : Nat) (B B' : List Ban)
    (hn : legal n B) (hm : legal m B') (h : enc n B = enc m B') : n=m ∧ B=B' := by
  have he : n=m := header_unique n m (B.flatMap (recordBits n)) (B'.flatMap (recordBits m))
    (by simpa only [enc,header,List.append_assoc,List.singleton_append] using h)
  subst m
  refine ⟨rfl,?_⟩
  have hp : B.flatMap (recordBits n) = B'.flatMap (recordBits n) := List.append_cancel_left h
  exact payload_injective n B B' hn.2 hm.2 hp

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
open PEqualNP.Outside.L_lib_895_aux.Comb

def inputEncoding (n : Nat) (B : List Comb.Ban) :=
  Comb.header n ++ B.flatMap (fun e => Comb.bits (Comb.width n) e.1.1 ++ Comb.bits 2 e.1.2 ++
    Comb.bits (Comb.width n) e.2.1 ++ Comb.bits 2 e.2.2)

lemma inputEncoding_length (n : Nat) (B : List Comb.Ban) :
    (inputEncoding n B).length = n+1+B.length*(2*Comb.width n+4) := by
  unfold inputEncoding
  rw [List.length_append, Comb.header_length]
  congr 1
  apply Comb.flatMap_length_constant
  intro e he
  simp only [List.length_append,Comb.bits_length]
  omega

lemma inputEncoding_size (n : Nat) (B : List Comb.Ban) :
    n+B.length+1 ≤ (inputEncoding n B).length := by
  rw [inputEncoding_length]
  have h := Nat.mul_le_mul_left B.length (show 1 ≤ 2*Comb.width n+4 by omega)
  omega

lemma output_quadratic_bound (n b : Nat) :
    8*n+2+4*(25*n+b)*Comb.width (8*n+1) ≤ 1000*(n+b+1)^2 := by
  have hw : Comb.width (8*n+1) ≤ 8*n+2 := by
    unfold Comb.width
    have := Nat.log2_le_self (8*n+1)
    omega
  have hm := Nat.mul_le_mul_left (4*(25*n+b)) hw
  nlinarith

lemma exact_output_quadratic (n : Nat) (B : List Comb.Ban) (h : Comb.legal n B) :
    (Comb.pack (8*n+1) (Comb.emit n B)).length ≤
      1000*((inputEncoding n B).length+1)^2 := by
  rw [Comb.emit_pack_length n B h]
  have h1 := output_quadratic_bound n B.length
  have h2 := inputEncoding_size n B
  nlinarith

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

abbrev LegalDatum := Nat × List Ban

def hasLegalEncoding (x : List Bool) : Prop :=
  ∃ p : LegalDatum, legal p.1 p.2 ∧ enc p.1 p.2 = x

def outputData (p : LegalDatum) : List Bool :=
  PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*p.1+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit p.1 p.2)

noncomputable def totalOutput (x : List Bool) : List Bool := by
  classical
  exact if h : hasLegalEncoding x then outputData (Classical.choose h) else []

lemma hasLegalEncoding_iff (x : List Bool) : hasLegalEncoding x ↔
    ∃ n B, legal n B ∧ enc n B = x := by
  constructor
  · rintro ⟨⟨n,B⟩,hl,he⟩; exact ⟨n,B,hl,he⟩
  · rintro ⟨n,B,hl,he⟩; exact ⟨(n,B),hl,he⟩

lemma totalOutput_malformed (x : List Bool)
    (h : ¬∃ n B, legal n B ∧ enc n B = x) : totalOutput x = [] := by
  have hx : ¬hasLegalEncoding x := fun hh => h ((hasLegalEncoding_iff x).mp hh)
  simp only [totalOutput,dif_neg hx]

lemma totalOutput_on_legal (n : Nat) (B : List Ban) (hl : legal n B) :
    totalOutput (enc n B) = PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) := by
  have hx : hasLegalEncoding (enc n B) := ⟨(n,B),hl,rfl⟩
  unfold totalOutput
  rw [dif_pos hx]
  obtain ⟨hp,he⟩ := Classical.choose_spec hx
  obtain ⟨hn,hB⟩ := enc_legal_injective _ _ _ _ hp hl he
  have hd : Classical.choose hx = (n,B) := Prod.ext hn hB
  rw [hd]
  rfl

lemma enc_eq_inputEncoding (n : Nat) (B : List Ban) : enc n B = inputEncoding n B := rfl
lemma legal_iff_comb (n : Nat) (B : List Ban) :
    legal n B ↔ PEqualNP.Outside.L_lib_895_aux.Comb.legal n B := Iff.rfl

theorem totalOutput_length (x : List Bool) :
    (totalOutput x).length ≤ 1000*(x.length+1)^2 := by
  by_cases hx : hasLegalEncoding x
  · obtain ⟨⟨n,B⟩,hl,he⟩ := hx
    rw [←he,totalOutput_on_legal n B hl]
    have h := exact_output_quadratic n B ((legal_iff_comb n B).mp hl)
    rw [←enc_eq_inputEncoding n B] at h
    exact h
  · have hm : ¬∃ n B, legal n B ∧ enc n B = x := fun h => hx ((hasLegalEncoding_iff x).mpr h)
    rw [totalOutput_malformed x hm]
    simp

theorem totalOutput_legal_spec (n : Nat) (B : List Ban) (hl : legal n B) :
    totalOutput (enc n B) = PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) ∧
    PEqualNP.Outside.L_lib_895_aux.Comb.well (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) ∧
    (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B).length = 25*n+B.length ∧
    (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B)).length =
      (8*n+1)+1+4*(25*n+B.length)*PEqualNP.Outside.L_lib_895_aux.Comb.width (8*n+1) := by
  refine ⟨totalOutput_on_legal n B hl,?_,?_,?_⟩
  · exact PEqualNP.Outside.L_lib_895_aux.Comb.emit_well n B ((legal_iff_comb n B).mp hl)
  · exact PEqualNP.Outside.L_lib_895_aux.Comb.emit_length n B
  · exact PEqualNP.Outside.L_lib_895_aux.Comb.emit_pack_length n B ((legal_iff_comb n B).mp hl)

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

lemma exact_of_machine_and_equiv
    (hMachine : ∃ C : Nat,
      (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput,
        (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^2))
    (hEquiv : ∀ n B, legal n B → Nonempty
      ({a : Fin n → Fin 3 // PEqualNP.Outside.L_lib_895_aux.Comb.valid n B a} ≃
       {P : Equiv.Perm (Fin (8*n+1)) // PEqualNP.Outside.L_lib_895_aux.Comb.wins (8*n+1)
         (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) P})) :
let bits := fun (w v : Nat) => (List.range w).map (fun j => v.testBit j)
let header := fun n : Nat => List.replicate n true ++ [false]
let width := fun n : Nat => n.log2+1
let Ban := (Nat × Nat) × (Nat × Nat)
let legal := fun (n : Nat) (B : List Ban) => 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
let enc := fun (n : Nat) (B : List Ban) =>
  header n ++ B.flatMap (fun e => bits (width n) e.1.1 ++ bits 2 e.1.2 ++
    bits (width n) e.2.1 ++ bits 2 e.2.2)
let valid := fun (n : Nat) (B : List Ban) (a : Fin n → Fin 3) =>
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2
let pack := fun (k : Nat) (rows : List (List Nat)) =>
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
let well := fun (k : Nat) (rows : List (List Nat)) => ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k
let wins := fun (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) =>
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k, u.val ∈ row ∧
    (P u).val ∈ row ∧ P u ≠ u
let emit := fun (n : Nat) (B : List Ban) =>
  let flag := fun (i c : Nat) => [8*i+2+2*c,8*i+3+2*c]
  let block := fun (i : Nat) =>
    [[8*i,8*i+2,8*i+4,8*i+6]] ++ (List.range 3).flatMap (fun c =>
      (List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
        [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j])))
  (List.range n).flatMap block ++ B.map (fun e => flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2)
∃ (f : List Bool → List Bool) (C : Nat),
  (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^2) ∧
  (∀ x : List Bool, (¬ ∃ n B, legal n B ∧ enc n B = x) → f x = []) ∧
  ∀ n B, legal n B →
    let k := 8*n+1
    let rows := emit n B
    f (enc n B) = pack k rows ∧ well k rows ∧ rows.length = 25*n+B.length ∧
      (pack k rows).length = k+1+4*(25*n+B.length)*width k ∧
      Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
        {P : Equiv.Perm (Fin k) // wins k rows P}) := by
  dsimp only
  obtain ⟨C,hC⟩ := hMachine
  refine ⟨totalOutput,C,hC,?_,?_⟩
  · intro x hx
    exact totalOutput_malformed x hx
  · intro n B hl
    have hs := totalOutput_legal_spec n B hl
    exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hEquiv n B hl⟩

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

theorem target_of_quadratic_machine
    (hMachine : ∃ C : Nat,
      (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput,
        (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^2)) :
let bits := fun (w v : Nat) => (List.range w).map (fun j => v.testBit j)
let header := fun n : Nat => List.replicate n true ++ [false]
let width := fun n : Nat => n.log2+1
let Ban := (Nat × Nat) × (Nat × Nat)
let legal := fun (n : Nat) (B : List Ban) => 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
let enc := fun (n : Nat) (B : List Ban) =>
  header n ++ B.flatMap (fun e => bits (width n) e.1.1 ++ bits 2 e.1.2 ++
    bits (width n) e.2.1 ++ bits 2 e.2.2)
let valid := fun (n : Nat) (B : List Ban) (a : Fin n → Fin 3) =>
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2
let pack := fun (k : Nat) (rows : List (List Nat)) =>
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
let well := fun (k : Nat) (rows : List (List Nat)) => ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k
let wins := fun (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) =>
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k, u.val ∈ row ∧
    (P u).val ∈ row ∧ P u ≠ u
let emit := fun (n : Nat) (B : List Ban) =>
  let flag := fun (i c : Nat) => [8*i+2+2*c,8*i+3+2*c]
  let block := fun (i : Nat) =>
    [[8*i,8*i+2,8*i+4,8*i+6]] ++ (List.range 3).flatMap (fun c =>
      (List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
        [8*i+b] ++ flag i c ++ [8*((i+1) % n)+j])))
  (List.range n).flatMap block ++ B.map (fun e => flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2)
∃ (f : List Bool → List Bool) (C : Nat),
  (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^2) ∧
  (∀ x : List Bool, (¬ ∃ n B, legal n B ∧ enc n B = x) → f x = []) ∧
  ∀ n B, legal n B →
    let k := 8*n+1
    let rows := emit n B
    f (enc n B) = pack k rows ∧ well k rows ∧ rows.length = 25*n+B.length ∧
      (pack k rows).length = k+1+4*(25*n+B.length)*width k ∧
      Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
        {P : Equiv.Perm (Fin k) // wins k rows P}) := by
  apply exact_of_machine_and_equiv hMachine
  intro n B hl
  exact emitted_bijection B ((legal_iff_comb n B).mp hl)
end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux.CallLayout

def forward {J K : Type*} (decode : J → Option K) (j : J) :
    K ⊕ {j : J // decode j = none} :=
  match h : decode j with
  | some k => Sum.inl k
  | none => Sum.inr ⟨j,h⟩

lemma forward_some {J K : Type*} (decode : J → Option K) (j : J) (k : K)
    (h : decode j = some k) : forward decode j = Sum.inl k := by
  unfold forward
  split <;> simp_all

lemma forward_none {J K : Type*} (decode : J → Option K) (j : J)
    (h : decode j = none) : forward decode j = Sum.inr ⟨j,h⟩ := by
  unfold forward
  split <;> simp_all

def optionSplit {J K : Type*} (encode : K → J) (decode : J → Option K)
    (henc : ∀ k, decode (encode k) = some k)
    (hdec : ∀ j k, decode j = some k → encode k = j) :
    J ≃ K ⊕ {j : J // decode j = none} where
  toFun := forward decode
  invFun
    | Sum.inl k => encode k
    | Sum.inr j => j.val
  left_inv j := by
    cases h : decode j with
    | none => rw [forward_none decode j h]
    | some k => rw [forward_some decode j k h]; exact hdec j k h
  right_inv s := by
    rcases s with k | ⟨j,hj⟩
    · exact forward_some decode (encode k) k (henc k)
    · exact forward_none decode j hj

lemma optionSplit_symm_inl {J K : Type*} (encode : K → J) (decode : J → Option K)
    (henc : ∀ k, decode (encode k) = some k)
    (hdec : ∀ j k, decode j = some k → encode k = j) (k : K) :
    (optionSplit encode decode henc hdec).symm (Sum.inl k) = encode k := rfl

lemma optionSplit_encode {J K : Type*} (encode : K → J) (decode : J → Option K)
    (henc : ∀ k, decode (encode k) = some k)
    (hdec : ∀ j k, decode j = some k → encode k = j) (k : K) :
    optionSplit encode decode henc hdec (encode k) = Sum.inl k := by
  exact forward_some decode (encode k) k (henc k)

lemma optionSplit_frame_finite {J K : Type*} [Finite J] (decode : J → Option K) :
    Finite {j : J // decode j = none} := by infer_instance

end PEqualNP.Outside.L_lib_895_aux.CallLayout

namespace PEqualNP.Outside.L_lib_895_aux.BoolCall
open Turing
variable {K Λ σ E L S J H τ : Type} [DecidableEq K] [DecidableEq J]
variable (ks : J ≃ K ⊕ E) (ls : H ≃ Λ ⊕ L) (ss : τ ≃ σ × S)

def trStmt (ret : L) : TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : J => Bool) H τ
  | .push k f q => .push (ks.symm (.inl k)) (fun s => f (ss s).1) (trStmt ret q)
  | .peek k f q => .peek (ks.symm (.inl k))
      (fun s o => ss.symm (f (ss s).1 o,(ss s).2)) (trStmt ret q)
  | .pop k f q => .pop (ks.symm (.inl k))
      (fun s o => ss.symm (f (ss s).1 o,(ss s).2)) (trStmt ret q)
  | .load f q => .load (fun s => ss.symm (f (ss s).1,(ss s).2)) (trStmt ret q)
  | .branch f q₁ q₂ => .branch (fun s => f (ss s).1)
      (trStmt ret q₁) (trStmt ret q₂)
  | .goto f => .goto (fun s => ls.symm (.inl (f (ss s).1)))
  | .halt => .goto (fun _ => ls.symm (.inr ret))

def liftStacks (stk : K → List Bool) (extra : E → List Bool) : J → List Bool :=
  fun j => (ks j).elim stk extra

lemma liftStacks_update (stk : K → List Bool) (extra : E → List Bool)
    (k : K) (w : List Bool) :
    liftStacks ks (Function.update stk k w) extra =
      Function.update (liftStacks ks stk extra) (ks.symm (.inl k)) w := by
  funext j
  by_cases h : j = ks.symm (.inl k)
  · subst j; simp [liftStacks]
  · rw [Function.update_of_ne h]
    have hk : ks j ≠ .inl k := by
      intro e
      apply h
      exact ks.injective (e.trans (ks.apply_symm_apply _).symm)
    cases e : ks j with
    | inl a =>
      have ha : a ≠ k := by intro h'; subst a; exact hk e
      simp [liftStacks,e,Function.update_of_ne ha]
    | inr a => simp [liftStacks,e]

def liftCfg (ret : L) (s : S) (extra : E → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : J => Bool) H τ :=
  ⟨some (ls.symm (c.l.elim (.inr ret) Sum.inl)),ss.symm (c.var,s),liftStacks ks c.stk extra⟩

lemma stepAux_sim (ret : L) (s : S) (extra : E → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (stk : K → List Bool) :
    TM2.stepAux (trStmt ks ls ss ret q) (ss.symm (v,s)) (liftStacks ks stk extra) =
      liftCfg ks ls ss ret s extra (TM2.stepAux q v stk) := by
  induction q generalizing v stk with
  | push k f q ih =>
    simp only [trStmt, TM2.stepAux, Equiv.apply_symm_apply]
    have h := ih v (Function.update stk k (f v :: stk k))
    rw [liftStacks_update] at h
    simpa only [liftStacks,Equiv.apply_symm_apply,Sum.elim_inl] using h
  | peek k f q ih =>
    simp only [trStmt,TM2.stepAux,Equiv.apply_symm_apply]
    simpa only [liftStacks,Equiv.apply_symm_apply,Sum.elim_inl] using ih (f v (stk k).head?) stk
  | pop k f q ih =>
    simp only [trStmt,TM2.stepAux,Equiv.apply_symm_apply]
    have h := ih (f v (stk k).head?) (Function.update stk k (stk k).tail)
    rw [liftStacks_update] at h
    simpa only [liftStacks,Equiv.apply_symm_apply,Sum.elim_inl] using h
  | load f q ih =>
    simp only [trStmt,TM2.stepAux,Equiv.apply_symm_apply]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trStmt,TM2.stepAux,Equiv.apply_symm_apply]
    cases f v
    · exact ih₂ v stk
    · exact ih₁ v stk
  | goto f => simp [trStmt,TM2.stepAux,liftCfg]
  | halt => rfl

lemma step_sim (ret : L) (s : S) (extra : E → List Bool)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (host : H → TM2.Stmt (fun _ : J => Bool) H τ)
    (hp : ∀ l, host (ls.symm (.inl l)) = trStmt ks ls ss ret (p l))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step p c = some d) :
    TM2.step host (liftCfg ks ls ss ret s extra c) =
      some (liftCfg ks ls ss ret s extra d) := by
  obtain ⟨l,v,stk⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step,Option.some.injEq] at h
    subst h
    change some (TM2.stepAux (host (ls.symm (.inl l))) _ _) = _
    rw [hp]
    exact congrArg some (stepAux_sim ks ls ss ret s extra (p l) v stk)

private lemma iterate_none {α : Type} (f : α → Option α) (n : Nat) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem run_lift (ret : L) (s : S) (extra : E → List Bool)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (host : H → TM2.Stmt (fun _ : J => Bool) H τ)
    (hp : ∀ l, host (ls.symm (.inl l)) = trStmt ks ls ss ret (p l)) :
    ∀ t (c d : TM2.Cfg (fun _ : K => Bool) Λ σ),
      (flip bind (TM2.step p))^[t] (some c) = some d →
      (flip bind (TM2.step host))^[t] (some (liftCfg ks ls ss ret s extra c)) =
        some (liftCfg ks ls ss ret s extra d) := by
  intro t
  induction t with
  | zero =>
    intro c d h
    have e : c = d := Option.some.inj h
    rw [e]; rfl
  | succ t ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h ⊢
    cases hc : TM2.step p c with
    | none =>
      have e : flip bind (TM2.step p) (some c) = none := hc
      rw [e,iterate_none] at h
      cases h
    | some c' =>
      have e : flip bind (TM2.step p) (some c) = some c' := hc
      have e' : flip bind (TM2.step host) (some (liftCfg ks ls ss ret s extra c)) =
          some (liftCfg ks ls ss ret s extra c') := step_sim ks ls ss ret s extra p host hp c c' hc
      rw [e] at h
      rw [e']
      exact ih c' d h

theorem frame_preserved (ret : L) (s : S) (extra : E → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    (ss (liftCfg ks ls ss ret s extra c).var).2 = s ∧
      ∀ e, (liftCfg ks ls ss ret s extra c).stk (ks.symm (.inr e)) = extra e := by
  simp [liftCfg,liftStacks]

theorem component_stacks (ret : L) (s : S) (extra : E → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (k : K) :
    (liftCfg ks ls ss ret s extra c).stk (ks.symm (.inl k)) = c.stk k := by
  simp [liftCfg,liftStacks]

theorem halt_is_return (ret : L) (s : S) (extra : E → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : c.l = none) :
    (liftCfg ks ls ss ret s extra c).l = some (ls.symm (.inr ret)) := by simp [liftCfg,h]

end PEqualNP.Outside.L_lib_895_aux.BoolCall

namespace PEqualNP.Outside.L_lib_895_aux.BoolCall
open Turing
variable {K Λ σ E L S J H τ : Type} [DecidableEq K] [DecidableEq J]
variable (ks : J ≃ K ⊕ E) (ls : H ≃ Λ ⊕ L) (ss : τ ≃ σ × S)

lemma liftStacks_reconstruct (hostStk : J → List Bool) :
    liftStacks ks (fun k => hostStk (ks.symm (.inl k)))
      (fun e => hostStk (ks.symm (.inr e))) = hostStk := by
  funext j
  obtain ⟨x,rfl⟩ := ks.symm.surjective j
  cases x <;> simp [liftStacks]

lemma stackMap_injective : Function.Injective (fun k : K => ks.symm (.inl k)) := by
  intro a b h
  exact Sum.inl.inj (ks.symm.injective h)

lemma labelMap_injective : Function.Injective (fun l : Λ => ls.symm (.inl l)) := by
  intro a b h
  exact Sum.inl.inj (ls.symm.injective h)

lemma return_outside (ret : L) (l : Λ) : ls.symm (.inr ret) ≠ ls.symm (.inl l) := by
  intro h
  have := ls.symm.injective h
  cases this

def evals_lift (ret : L) (s : S) (extra : E → List Bool)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (host : H → TM2.Stmt (fun _ : J => Bool) H τ)
    (hp : ∀ l, host (ls.symm (.inl l)) = trStmt ks ls ss ret (p l))
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (bound : Nat)
    (h : StateTransition.EvalsToInTime (TM2.step p) c (some d) bound) :
    StateTransition.EvalsToInTime (TM2.step host)
      (liftCfg ks ls ss ret s extra c) (some (liftCfg ks ls ss ret s extra d)) bound where
  steps := h.steps
  evals_in_steps := run_lift ks ls ss ret s extra p host hp h.steps c d h.evals_in_steps
  steps_le_m := h.steps_le_m

include ks in
lemma finite_host_stacks [Finite K] [Finite E] : Finite J :=
  Finite.of_equiv (K ⊕ E) ks.symm
include ls in
lemma finite_host_labels [Finite Λ] [Finite L] : Finite H :=
  Finite.of_equiv (Λ ⊕ L) ls.symm
include ss in
lemma finite_host_state [Finite σ] [Finite S] : Finite τ :=
  Finite.of_equiv (σ × S) ss.symm

end PEqualNP.Outside.L_lib_895_aux.BoolCall

namespace PEqualNP.Outside.L_lib_895_aux.Header
open Turing

def hstk (I C T N : List Bool) : Fin 4 → List Bool := ![I,C,T,N]

lemma hstk_set0 (I C T N X : List Bool) :
    Function.update (hstk I C T N) 0 X = hstk X C T N := by
  funext k; fin_cases k <;> rfl
lemma hstk_set1 (I C T N X : List Bool) :
    Function.update (hstk I C T N) 1 X = hstk I X T N := by
  funext k; fin_cases k <;> rfl
lemma hstk_set2 (I C T N X : List Bool) :
    Function.update (hstk I C T N) 2 X = hstk I C X N := by
  funext k; fin_cases k <;> rfl
lemma hstk_set3 (I C T N X : List Bool) :
    Function.update (hstk I C T N) 3 X = hstk I C T X := by
  funext k; fin_cases k <;> rfl

lemma hstk_get0 (I C T N : List Bool) : hstk I C T N 0 = I := rfl
lemma hstk_get1 (I C T N : List Bool) : hstk I C T N 1 = C := rfl
lemma hstk_get2 (I C T N : List Bool) : hstk I C T N 2 = T := rfl
lemma hstk_get3 (I C T N : List Bool) : hstk I C T N 3 = N := rfl

def program : Fin 3 → TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)
  | 0 => .pop 0 (fun _ x => x)
      (.branch Option.isSome
        (.branch (fun s => s.getD false)
          (.push 3 (fun _ => true) (.load (fun _ => none) (.goto fun _ => 1)))
          .halt)
        .halt)
  | 1 => .pop 1 (fun _ x => x)
      (.branch (fun s => s == some true)
        (.push 2 (fun _ => false) (.load (fun _ => none) (.goto fun _ => 1)))
        (.push 1 (fun _ => true) (.load (fun _ => none) (.goto fun _ => 2))))
  | _ => .pop 2 (fun _ x => x)
      (.branch Option.isSome
        (.push 1 (fun s => s.getD false) (.load (fun _ => none) (.goto fun _ => 2)))
        (.load (fun _ => none) (.goto fun _ => 0)))

def machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Option (Fin 3)) (s : Option Bool) (I C T N : List Bool) :
    (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :=
  ⟨l,s,hstk I C T N⟩

lemma read_true (I C T N : List Bool) :
    (TM2.step program) (cfg (some 0) none (true::I) C T N) =
      some (cfg (some 1) none I C T (true::N)) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set0,hstk_set3]

lemma read_false (I C T N : List Bool) :
    (TM2.step program) (cfg (some 0) none (false::I) C T N) =
      some (cfg none (some false) I C T N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set0]

lemma read_empty (C T N : List Bool) :
    (TM2.step program) (cfg (some 0) none [] C T N) =
      some (cfg none none [] C T N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set0]

lemma carry_true (I C T N : List Bool) :
    (TM2.step program) (cfg (some 1) none I (true::C) T N) =
      some (cfg (some 1) none I C (false::T) N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set1,hstk_set2]

lemma carry_false (I C T N : List Bool) :
    (TM2.step program) (cfg (some 1) none I (false::C) T N) =
      some (cfg (some 2) none I (true::C) T N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set1]

lemma carry_empty (I T N : List Bool) :
    (TM2.step program) (cfg (some 1) none I [] T N) =
      some (cfg (some 2) none I [true] T N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set1]

lemma restore_cons (I C N : List Bool) (b : Bool) (T : List Bool) :
    (TM2.step program) (cfg (some 2) none I C (b::T) N) =
      some (cfg (some 2) none I (b::C) T N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set1,hstk_set2]

lemma restore_empty (I C N : List Bool) :
    (TM2.step program) (cfg (some 2) none I C [] N) =
      some (cfg (some 0) none I C [] N) := by
  simp [FinTM2.step,TM2.step,program,machine,cfg,TM2.stepAux,hstk_get0,hstk_get1,hstk_get2,hstk_get3,hstk_set2]

def run (t : Nat) (c : (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool))) : Option (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) :=
  (fun s : Option (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool)) => s.bind (TM2.step program))^[t] (some c)

lemma run_one (c d : (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool))) (h : (TM2.step program) c = some d) :
    run 1 c = some d := by simpa only [run,Function.iterate_one,Option.bind_some] using h

lemma run_comp {s t : Nat} {a b c : (TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 3) (Option Bool))}
    (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
  unfold run at *
  rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]

lemma restore_run (I C T N : List Bool) :
    run (T.length+1) (cfg (some 2) none I C T N) =
      some (cfg (some 0) none I (T.reverse++C) [] N) := by
  induction T generalizing C with
  | nil => simpa using run_one _ _ (restore_empty I C N)
  | cons b T ih =>
    have hh := run_comp (run_one _ _ (restore_cons I C N b T)) (ih (b::C))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

def increment : List Bool → List Bool
  | [] => [true]
  | false::C => true::C
  | true::C => false::increment C

lemma increment_length (C : List Bool) : (increment C).length ≤ C.length+1 := by
  induction C with
  | nil => simp [increment]
  | cons b C ih => cases b <;> simp_all [increment]

lemma carry_run (I C T N : List Bool) :
    ∃ t ≤ 2*C.length+T.length+2,
      run t (cfg (some 1) none I C T N) =
        some (cfg (some 0) none I (T.reverse++increment C) [] N) := by
  induction C generalizing T with
  | nil =>
    refine ⟨1+(T.length+1),by simp; omega,?_⟩
    simpa [increment] using run_comp (run_one _ _ (carry_empty I T N)) (restore_run I [true] T N)
  | cons b C ih =>
    cases b with
    | false =>
      refine ⟨1+(T.length+1),by simp; omega,?_⟩
      simpa [increment] using run_comp (run_one _ _ (carry_false I C T N)) (restore_run I (true::C) T N)
    | true =>
      obtain ⟨t,ht,hr⟩ := ih (false::T)
      refine ⟨1+t,by simp_all; omega,?_⟩
      have hh := run_comp (run_one _ _ (carry_true I C T N)) hr
      simpa [increment,List.reverse_cons,List.append_assoc] using hh

end PEqualNP.Outside.L_lib_895_aux.Header

namespace PEqualNP.Outside.L_lib_895_aux.Mealy

open Turing

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq

instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

end PEqualNP.Outside.L_lib_895_aux.Mealy

namespace PEqualNP.Outside.L_lib_895_aux
open Turing

def incCarry (carry : Bool) : List Bool → List Bool
  | [] => []
  | b::xs => (if carry then !b else b) :: incCarry (carry && b) xs

def incWord (xs : List Bool) : List Bool := incCarry true xs

def wordValue : List Bool → Nat
  | [] => 0
  | b::xs => (if b then 1 else 0) + 2*wordValue xs

lemma incCarry_length (carry : Bool) (xs : List Bool) : (incCarry carry xs).length = xs.length := by
  induction xs generalizing carry with
  | nil => rfl
  | cons b xs ih => simp only [incCarry,List.length_cons,ih]

lemma incCarry_false (xs : List Bool) : incCarry false xs = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [incCarry,ih]

lemma wordValue_lt (xs : List Bool) : wordValue xs < 2^xs.length := by
  induction xs with
  | nil => simp [wordValue]
  | cons b xs ih => cases b <;> simp [wordValue,pow_succ] <;> omega

lemma incWord_value (xs : List Bool) : wordValue (incWord xs) = (wordValue xs+1)  %  2^xs.length := by
  change wordValue (incCarry true xs) = _
  induction xs with
  | nil => simp [incCarry,wordValue]
  | cons b xs ih =>
    cases b with
    | false =>
      change 1+2*wordValue (incCarry false xs) = (0+2*wordValue xs+1)  %  2^(xs.length+1)
      rw [incCarry_false,pow_succ,Nat.mod_eq_of_lt (by have h := wordValue_lt xs; omega)]
      omega
    | true =>
      change 0+2*wordValue (incCarry true xs) = (1+2*wordValue xs+1)  %  2^(xs.length+1)
      rw [ih,pow_succ]
      rw [show 1+2*wordValue xs+1=2*(wordValue xs+1) by omega,
        Nat.mul_comm (2^xs.length) 2,Nat.mul_mod_mul_left]
      omega

def carryTransition (carry b : Bool) : Bool × Option Bool × Option Bool :=
  (carry && b, some (if carry then !b else b), none)

lemma carry_run (carry : Bool) (xs : List Bool) :
    Mealy.fstRun2 carryTransition (fun _ => none) carry xs = incCarry carry xs := by
  induction xs generalizing carry with
  | nil => rfl
  | cons b xs ih => simp only [Mealy.fstRun2,carryTransition,incCarry,Option.toList_some,
      Option.toList_none,List.append_nil,List.cons_append,List.nil_append,ih]

def incrementMachine : FinTM2 := Mealy.trM carryTransition (fun _ => none) true (some false)

lemma increment_run (xs : List Bool) :
    (flip bind incrementMachine.step)^[2*xs.length+3] (some (initList incrementMachine xs)) =
      some (haltList incrementMachine (incWord xs)) := by
  have h := Mealy.trM_run carryTransition (fun _ => none) true (some false) (fun _ => by simp) xs
  have he : xs.length+1+1+(xs.length+1)=2*xs.length+3 := by omega
  rw [he] at h
  exact h.trans (congrArg (fun l : List Bool => some (haltList incrementMachine l)) (carry_run true xs))

noncomputable def incrementComputable :
    TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) incWord where
  tm := incrementMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time n := 2*n+3
  outputsFun xs :=
    { steps := 2*xs.length+3
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        exact (congrArg (fun l => (flip bind incrementMachine.step)^[2*xs.length+3]
          (some (initList incrementMachine l))) (hm xs)).trans
          ((increment_run xs).trans (congrArg (fun l => some (haltList incrementMachine l))
            (hm (incWord xs)).symm))
      steps_le_m := le_rfl }

lemma increment_finite_alphabets : ∀ j, Finite (incrementComputable.tm.Γ j) := by
  change ∀ j : Mealy.TrK, Finite (Mealy.TrΓ Bool Bool Bool j)
  intro j
  cases j <;> dsimp only [Mealy.TrΓ] <;> infer_instance

lemma increment_linear_bound (n : Nat) : incrementComputable.time n ≤ 3*(n+1) := by
  change 2*n+3 ≤ 3*(n+1)
  omega

lemma increment_length (xs : List Bool) : (incWord xs).length = xs.length := incCarry_length true xs

lemma increment_scratch_clean (xs : List Bool) :
    (haltList incrementMachine (incWord xs)).stk Mealy.TrK.inp = [] ∧
    (haltList incrementMachine (incWord xs)).stk Mealy.TrK.tmp = [] := by
  constructor <;> rfl

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux
open Turing

def growInc : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::growInc xs

lemma growInc_value (xs : List Bool) : wordValue (growInc xs) = wordValue xs+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [growInc,wordValue,ih] <;> omega

lemma growInc_length (xs : List Bool) :
    xs.length ≤ (growInc xs).length ∧ (growInc xs).length ≤ xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp [growInc] <;> omega

lemma growInc_expands (xs : List Bool) (h : xs.length < (growInc xs).length) :
    wordValue xs+1 = 2^xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp [growInc] at h
    | true =>
      have ht : xs.length < (growInc xs).length := by simpa [growInc] using h
      have hv := ih ht
      simp [wordValue,pow_succ]
      omega

def growFinish (carry : Bool) : Option Bool := if carry then some true else none

lemma grow_carry_run (carry : Bool) (xs : List Bool) :
    Mealy.fstRun2 carryTransition growFinish carry xs = (if carry then growInc xs else xs) := by
  induction xs generalizing carry with
  | nil => cases carry <;> rfl
  | cons b xs ih => cases carry <;> cases b <;> simp [Mealy.fstRun2,carryTransition,growFinish,growInc,ih]

def growMachine : FinTM2 := Mealy.trM carryTransition growFinish true (some false)

lemma grow_run (xs : List Bool) :
    (flip bind growMachine.step)^[2*xs.length+3] (some (initList growMachine xs)) =
      some (haltList growMachine (growInc xs)) := by
  have h := Mealy.trM_run carryTransition growFinish true (some false) (fun _ => by simp) xs
  have he : xs.length+1+1+(xs.length+1)=2*xs.length+3 := by omega
  rw [he] at h
  have hv : Mealy.fstRun2 carryTransition growFinish true xs = growInc xs := by simpa using grow_carry_run true xs
  exact h.trans (congrArg (fun l : List Bool => some (haltList growMachine l)) hv)

noncomputable def growComputable :
    TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) growInc where
  tm := growMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time n := 2*n+3
  outputsFun xs :=
    { steps := 2*xs.length+3
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        exact (congrArg (fun l => (flip bind growMachine.step)^[2*xs.length+3]
          (some (initList growMachine l))) (hm xs)).trans
          ((grow_run xs).trans (congrArg (fun l => some (haltList growMachine l))
            (hm (growInc xs)).symm))
      steps_le_m := le_rfl }

lemma grow_finite_alphabets : ∀ j, Finite (growComputable.tm.Γ j) := by
  change ∀ j : Mealy.TrK, Finite (Mealy.TrΓ Bool Bool Bool j)
  intro j; cases j <;> dsimp only [Mealy.TrΓ] <;> infer_instance

lemma grow_linear_bound (n : Nat) : growComputable.time n ≤ 3*(n+1) := by
  change 2*n+3 ≤ 3*(n+1); omega

lemma grow_scratch_clean (xs : List Bool) :
    (haltList growMachine (growInc xs)).stk Mealy.TrK.inp = [] ∧
    (haltList growMachine (growInc xs)).stk Mealy.TrK.tmp = [] := by
  constructor <;> rfl

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux

lemma bits_append_low (w t a b : Nat) (hb : b<2^t) :
    bits (w+t) (2^t*a+b) = bits t b ++ bits w a := by
  simp only [bits]
  rw [show w+t=t+w by omega,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' : j<t := List.mem_range.mp hj
    simpa only [if_pos hj'] using Nat.testBit_two_pow_mul_add a hb j
  · apply List.map_congr_left
    intro j hj
    have ht : ¬t+j<t := by omega
    simpa only [if_neg ht,Nat.add_sub_cancel_left,Function.comp_def] using
      Nat.testBit_two_pow_mul_add a hb (t+j)

lemma bits_cons_bit (w a : Nat) (b : Bool) :
    bits (w+1) (2*a+(if b then 1 else 0)) = b::bits w a := by
  have h := bits_append_low w 1 a (if b then 1 else 0) (by cases b <;> decide)
  cases b <;> simpa [bits] using h

lemma bits_wordValue (xs : List Bool) : bits xs.length (wordValue xs) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change bits (xs.length+1) ((if b then 1 else 0)+2*wordValue xs) = b::xs
    rw [Nat.add_comm (if b then 1 else 0) (2*wordValue xs),bits_cons_bit,ih]

lemma wordValue_bits (w n : Nat) (hn : n<2^w) : wordValue (bits w n) = n := by
  have hv := wordValue_lt (bits w n)
  rw [bits_length] at hv
  apply bits_injective w _ n hv hn
  simpa only [bits_length] using bits_wordValue (bits w n)

theorem growInc_bits_width (n : Nat) :
    growInc (bits (width n) n) = bits (width (n+1)) (n+1) := by
  by_cases hn : n=0
  · subst n; rfl
  let xs := bits (width n) n
  have hlen : xs.length = width n := bits_length _ _
  have hv : wordValue xs = n := wordValue_bits _ _ Nat.lt_log2_self
  have hout := growInc_length xs
  have hyval : wordValue (growInc xs) = n+1 := by rw [growInc_value,hv]
  have hylen : (growInc xs).length = width (n+1) := by
    by_cases hgrow : xs.length < (growInc xs).length
    · have hp := growInc_expands xs hgrow
      rw [hv,hlen] at hp
      have hw : width (n+1) = width n+1 := by rw [hp]; simp [width]
      omega
    · have heq : (growInc xs).length = width n := by omega
      have hupper : n+1 < 2^(width n) := by
        rw [←hyval,←heq]
        exact wordValue_lt _
      have hlogUpper := (Nat.log2_lt (show n+1≠0 by omega)).mpr hupper
      have hlogLower : n.log2 ≤ (n+1).log2 :=
        (Nat.le_log2 (show n+1≠0 by omega)).mpr ((Nat.log2_self_le hn).trans (by omega))
      unfold width at *
      omega
  change growInc xs = _
  have hrepr := bits_wordValue (growInc xs)
  rw [hylen,hyval] at hrepr
  exact hrepr.symm

theorem growInc_iterate_empty (n : Nat) :
    growInc^[n] [] = if n=0 then [] else bits (width n) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    by_cases hn : n=0
    · subst n; rfl
    · simp only [hn,if_false]
      rw [growInc_bits_width]
      simp

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux.Header

lemma increment_eq_growInc : increment = growInc := by
  funext C
  induction C with
  | nil => rfl
  | cons b C ih => cases b <;> simp_all [increment,growInc]

lemma increment_ready (I C N : List Bool) :
    ∃ t ≤ 2*C.length+2,
      run t (cfg (some 1) none I C [] N) =
        some (cfg (some 0) none I (increment C) [] N) := by
  obtain ⟨t,ht,hh⟩ := carry_run I C [] N
  exact ⟨t,by simpa using ht,by simpa using hh⟩

theorem header_run (n : Nat) (I C N : List Bool) :
    ∃ t ≤ n*(2*(C.length+n)+3)+1,
      run t (cfg (some 0) none (List.replicate n true ++ false::I) C [] N) =
        some (cfg none (some false) I (increment^[n] C) [] (List.replicate n true ++ N)) := by
  induction n generalizing C N with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa using run_one _ _ (read_false I C [] N)
  | succ n ih =>
    obtain ⟨u,hu,hru⟩ := increment_ready
      (List.replicate n true ++ false::I) C (true::N)
    obtain ⟨v,hv,hrv⟩ := ih (increment C) (true::N)
    have hread := run_one _ _
      (read_true (List.replicate n true ++ false::I) C [] N)
    have hrun := run_comp (run_comp hread hru) hrv
    have hlen := increment_length C
    have hmul := Nat.mul_le_mul_left n
      (show 2*((increment C).length+n)+3 ≤ 2*(C.length+1+n)+3 by omega)
    refine ⟨1+u+v,by nlinarith,?_⟩
    have hmarks : List.replicate n true ++ true::N = List.replicate (n+1) true ++ N := by
      rw [List.replicate_add]
      simp [List.append_assoc]
    simpa only [List.replicate_succ,List.cons_append,Function.iterate_succ_apply,hmarks] using hrun

theorem canonical_header_run (n : Nat) (I : List Bool) (hn : 2 ≤ n) :
    ∃ t ≤ 5*(n+1)^2,
      run t (cfg (some 0) none (List.replicate n true ++ false::I) [] [] []) =
        some (cfg none (some false) I (bits (width n) n) [] (List.replicate n true)) := by
  obtain ⟨t,ht,hh⟩ := header_run n I [] []
  refine ⟨t,by simp only [List.length_nil] at ht; nlinarith,?_⟩
  rw [increment_eq_growInc,growInc_iterate_empty] at hh
  simpa [show n ≠ 0 by omega] using hh

end PEqualNP.Outside.L_lib_895_aux.Header

namespace PEqualNP.Outside.L_lib_895_aux.Header

theorem unterminated_run (n : Nat) (C N : List Bool) :
 ∃ t ≤ n*(2*(C.length+n)+3)+1,
 run t (cfg (some 0) none (List.replicate n true) C [] N) =
 some (cfg none none [] (increment^[n] C) [] (List.replicate n true++N)) := by
 induction n generalizing C N with
 | zero =>
   refine ⟨1,by simp,?_⟩
   simpa using run_one _ _ (read_empty C [] N)
 | succ n ih =>
   obtain ⟨u,hu,hru⟩ := increment_ready (List.replicate n true) C (true::N)
   obtain ⟨v,hv,hrv⟩ := ih (increment C) (true::N)
   have hread := run_one _ _ (read_true (List.replicate n true) C [] N)
   have hrun := run_comp (run_comp hread hru) hrv
   have hlen := increment_length C
   have hmul := Nat.mul_le_mul_left n
     (show 2*((increment C).length+n)+3 ≤ 2*(C.length+1+n)+3 by omega)
   refine ⟨1+u+v,by nlinarith,?_⟩
   have hmarks : List.replicate n true ++ true::N = List.replicate (n+1) true ++ N := by
     rw [List.replicate_add]
     simp [List.append_assoc]
   simpa only [List.replicate_succ,Function.iterate_succ_apply,hmarks] using hrun

theorem canonical_unterminated_run (n : Nat) :
 ∃ t ≤ 5*(n+1)^2,
 run t (cfg (some 0) none (List.replicate n true) [] [] []) =
 some (cfg none none [] (growInc^[n] []) [] (List.replicate n true)) := by
 obtain ⟨t,ht,hh⟩ := unterminated_run n [] []
 refine ⟨t,by simp only [List.length_nil] at ht; nlinarith,?_⟩
 simpa [increment_eq_growInc] using hh

lemma input_decomposition (I : List Bool) :
 (∃ n, I = List.replicate n true) ∨
 (∃ n R, I = List.replicate n true ++ false::R) := by
 induction I with
 | nil => exact Or.inl ⟨0,rfl⟩
 | cons b I ih =>
   cases b with
   | false => exact Or.inr ⟨0,I,rfl⟩
   | true =>
     rcases ih with ⟨n,h⟩ | ⟨n,R,h⟩
     · exact Or.inl ⟨n+1,by simp [h,List.replicate_succ]⟩
     · exact Or.inr ⟨n+1,R,by simp [h,List.replicate_succ]⟩

theorem header_total (I : List Bool) :
 ∃ n ≤ I.length, ∃ ended : Bool, ∃ R t,
   I = List.replicate n true ++ (if ended then false::R else []) ∧
   (ended = false → R = []) ∧ t ≤ 5*(I.length+1)^2 ∧
   run t (cfg (some 0) none I [] [] []) =
   some (cfg none (if ended then some false else none) R (growInc^[n] []) [] (List.replicate n true)) := by
 rcases input_decomposition I with ⟨n,h⟩ | ⟨n,R,h⟩
 · subst I
   obtain ⟨t,ht,hh⟩ := canonical_unterminated_run n
   exact ⟨n,by simp,false,[],t,by simp,by simp,by simpa using ht,by simpa using hh⟩
 · have hn : n ≤ I.length := by simp [h]
   obtain ⟨t,ht,hh⟩ := header_run n R [] []
   refine ⟨n,hn,true,R,t,by simpa using h,by simp,?_,?_⟩
   · simp only [List.length_nil] at ht
     nlinarith
   · simpa [h,increment_eq_growInc] using hh

end PEqualNP.Outside.L_lib_895_aux.Header

namespace PEqualNP.Outside.L_lib_895_aux.MinTwo
open Turing
abbrev RC := TM2.Cfg (fun _ : Unit => Bool) Unit (Option Bool × Bool)
def program : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool × Bool) := fun _ =>
 .pop () (fun _ b => (b,false))
   (.peek () (fun s b => (s.1,s.1.isSome && b.isSome))
     (.branch (fun s => s.1.isSome)
       (.push () (fun s => s.1.getD false) (.load (fun s => (none,s.2)) .halt))
       (.load (fun s => (none,s.2)) .halt)))
def machine : FinTM2 where
 K := Unit
 k₀ := ()
 k₁ := ()
 Γ _ := Bool
 Λ := Unit
 main := ()
 σ := Option Bool × Bool
 initialState := (none,false)
 m := program
def cfg (l : Option Unit) (valid : Bool) (I : List Bool) : RC :=
 ⟨l,(none,valid),fun _ => I⟩

theorem check_run (I : List Bool) :
 TM2.step program (cfg (some ()) false I) =
 some (cfg none (decide (2 ≤ I.length)) I) := by
 cases I with
 | nil => simp [TM2.step,program,cfg,TM2.stepAux]
 | cons a I =>
   cases I with
   | nil => simp [TM2.step,program,cfg,TM2.stepAux,Function.update]
   | cons b I => simp [TM2.step,program,cfg,TM2.stepAux,Function.update]

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance

lemma width_min_two (n : Nat) (h : 2 ≤ n) : 2 ≤ width n := by
 unfold width
 have hlog : 1 ≤ n.log2 := by
   exact (Nat.le_log2 (by omega : n ≠ 0)).2 (by simpa using h)
 omega

theorem counter_valid_iff (n : Nat) :
 2 ≤ (growInc^[n] []).length ↔ 2 ≤ n := by
 rw [growInc_iterate_empty]
 by_cases h0 : n = 0
 · simp [h0]
 · simp only [h0,if_false]
   by_cases h1 : n = 1
   · subst n
     decide
   · have hn : 2 ≤ n := by omega
     simp [hn,PEqualNP.Outside.L_lib_895_aux.bits,width_min_two n hn]

end PEqualNP.Outside.L_lib_895_aux.MinTwo

namespace PEqualNP.Outside.L_lib_895_aux.Copy
open Turing

inductive Stack where | A | B | C deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.A,.B,.C] (by intro k; cases k <;> simp)
inductive Label where | duplicate | restore | copyBack deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.duplicate,.restore,.copyBack] (by intro l; cases l <;> simp)

abbrev State := Option Bool
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def copySt (a b c : List Bool) : Stack → List Bool
  | .A => a | .B => b | .C => c

def cfg (l : Option Label) (s : State) (a b c : List Bool) : Cfg := ⟨l,s,copySt a b c⟩
lemma setA (a a' b c : List Bool) : Function.update (copySt a b c) .A a' = copySt a' b c := by
  funext k; cases k <;> simp [copySt]
lemma setB (a b b' c : List Bool) : Function.update (copySt a b c) .B b' = copySt a b' c := by
  funext k; cases k <;> simp [copySt]
lemma setC (a b c c' : List Bool) : Function.update (copySt a b c) .C c' = copySt a b c' := by
  funext k; cases k <;> simp [copySt]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .duplicate =>
    .pop .A (fun _ o => o)
      (.branch Option.isSome
        (.push .B (fun s => s.getD false)
          (.push .C (fun s => s.getD false)
            (.load (fun _ => none) (.goto fun _ => .duplicate))))
        (.load (fun _ => none) (.goto fun _ => .restore)))
  | .restore =>
    .pop .B (fun _ o => o)
      (.branch Option.isSome
        (.push .A (fun s => s.getD false)
          (.load (fun _ => none) (.goto fun _ => .restore)))
        (.load (fun _ => none) (.goto fun _ => .copyBack)))
  | .copyBack =>
    .pop .C (fun _ o => o)
      (.branch Option.isSome
        (.push .B (fun s => s.getD false)
          (.load (fun _ => none) (.goto fun _ => .copyBack)))
        (.load (fun _ => none) .halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .A
  k₁ := .B
  Γ _ := Bool
  Λ := Label
  main := .duplicate
  σ := State
  initialState := none
  m := program

def startCfg (w : List Bool) : Cfg := cfg (some .duplicate) none w [] []
def endCfg (w : List Bool) : Cfg := cfg none none w w []

lemma duplicate_cons (s : State) (x : Bool) (w b c : List Bool) :
    TM2.step program (cfg (some .duplicate) s (x::w) b c) =
      some (cfg (some .duplicate) none w (x::b) (x::c)) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]
lemma duplicate_nil (s : State) (b c : List Bool) :
    TM2.step program (cfg (some .duplicate) s [] b c) =
      some (cfg (some .restore) none [] b c) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]
lemma restore_cons (s : State) (x : Bool) (w a c : List Bool) :
    TM2.step program (cfg (some .restore) s a (x::w) c) =
      some (cfg (some .restore) none (x::a) w c) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]
lemma restore_nil (s : State) (a c : List Bool) :
    TM2.step program (cfg (some .restore) s a [] c) =
      some (cfg (some .copyBack) none a [] c) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]
lemma copyBack_cons (s : State) (x : Bool) (w a b : List Bool) :
    TM2.step program (cfg (some .copyBack) s a b (x::w)) =
      some (cfg (some .copyBack) none a (x::b) w) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]
lemma copyBack_nil (s : State) (a b : List Bool) :
    TM2.step program (cfg (some .copyBack) s a b []) =
      some (cfg none none a b []) := by
  simp [TM2.step,program,TM2.stepAux,cfg,copySt,setA,setB,setC]

lemma pass_duplicate (w : List Bool) : ∀ (b c : List Bool) (s : State),
    (flip bind (TM2.step program))^[w.length+1] (some (cfg (some .duplicate) s w b c)) =
      some (cfg (some .restore) none [] (w.reverse++b) (w.reverse++c)) := by
  induction w with
  | nil => intro b c s; exact duplicate_nil s b c
  | cons x w ih =>
    intro b c s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .duplicate) s (x::w) b c)) =
        some (cfg (some .duplicate) none w (x::b) (x::c)) := duplicate_cons s x w b c
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

lemma pass_restore (w : List Bool) : ∀ (a c : List Bool) (s : State),
    (flip bind (TM2.step program))^[w.length+1] (some (cfg (some .restore) s a w c)) =
      some (cfg (some .copyBack) none (w.reverse++a) [] c) := by
  induction w with
  | nil => intro a c s; exact restore_nil s a c
  | cons x w ih =>
    intro a c s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .restore) s a (x::w) c)) =
        some (cfg (some .restore) none (x::a) w c) := restore_cons s x w a c
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

lemma pass_copyBack (w : List Bool) : ∀ (a b : List Bool) (s : State),
    (flip bind (TM2.step program))^[w.length+1] (some (cfg (some .copyBack) s a b w)) =
      some (cfg none none a (w.reverse++b) []) := by
  induction w with
  | nil => intro a b s; exact copyBack_nil s a b
  | cons x w ih =>
    intro a b s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .copyBack) s a b (x::w))) =
        some (cfg (some .copyBack) none a (x::b) w) := copyBack_cons s x w a b
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

theorem copy_run (w : List Bool) :
    (flip bind machine.step)^[3*w.length+3] (some (startCfg w)) = some (endCfg w) := by
  have hA := pass_duplicate w [] [] none
  simp only [List.append_nil] at hA
  have hB := pass_restore w.reverse [] w.reverse none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hB
  have hC := pass_copyBack w.reverse w [] none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hC
  change (flip bind (TM2.step program))^[3*w.length+3]
    (some (cfg (some .duplicate) none w [] [])) = some (cfg none none w w [])
  rw [show 3*w.length+3=(w.length+1)+(w.length+1)+(w.length+1) by omega,
    Function.iterate_add_apply,hA,Function.iterate_add_apply,hB,hC]

def copy_evals (w : List Bool) :
    StateTransition.EvalsToInTime machine.step (startCfg w) (some (endCfg w)) (3*w.length+3) where
  steps := 3*w.length+3
  evals_in_steps := copy_run w
  steps_le_m := le_rfl

lemma copy_finite_alphabets : ∀ j, Finite (machine.Γ j) := by
  intro j
  change Finite Bool
  infer_instance
lemma copy_finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma copy_finite_state : Finite machine.σ := by change Finite State; infer_instance
lemma copy_final_stacks (w : List Bool) :
    (endCfg w).stk .A = w ∧ (endCfg w).stk .B = w ∧ (endCfg w).stk .C = [] := by
  exact ⟨rfl,rfl,rfl⟩
lemma copy_final_control (w : List Bool) : (endCfg w).l = none ∧ (endCfg w).var = none := by
  exact ⟨rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.Copy

namespace PEqualNP.Outside.L_lib_895_aux.EmitHeader
open Turing
abbrev RC := TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool)
def stk (N O : List Bool) : Fin 2 → List Bool := ![N,O]
@[simp] lemma stk_get0 (N O : List Bool) : stk N O 0 = N := rfl
@[simp] lemma stk_get1 (N O : List Bool) : stk N O 1 = O := rfl
@[simp] lemma stk_set0 (N O X : List Bool) : Function.update (stk N O) 0 X = stk X O := by
 funext k; fin_cases k <;> rfl
@[simp] lemma stk_set1 (N O X : List Bool) : Function.update (stk N O) 1 X = stk N X := by
 funext k; fin_cases k <;> rfl

def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool) := fun _ =>
 .pop 0 (fun _ b => b) (.branch Option.isSome
  (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.push 1 (fun _ => true) (.load (fun _ => none) (.goto fun _ => ()))))))))))
  (.push 1 (fun _ => true) (.push 1 (fun _ => false) (.load (fun _ => none) .halt))))

def machine : FinTM2 where
 K := Fin 2
 k₀ := 0
 k₁ := 1
 Γ _ := Bool
 Λ := Unit
 main := ()
 σ := Option Bool
 initialState := none
 m := program
def cfg (l : Option Unit) (N O : List Bool) : RC := ⟨l,none,stk N O⟩
def run (t : Nat) (c : RC) : Option RC :=
 (fun s : Option RC => s.bind (TM2.step program))^[t] (some c)
lemma run_one (c d : RC) (h : TM2.step program c = some d) : run 1 c = some d := by
 simpa only [run,Function.iterate_one,Option.bind_some] using h
lemma run_comp {s t : Nat} {a b c : RC}
 (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]
lemma step_cons (b : Bool) (N O : List Bool) :
 TM2.step program (cfg (some ()) (b::N) O) =
 some (cfg (some ()) N (List.replicate 8 true++O)) := by
 simp [TM2.step,program,cfg,TM2.stepAux,List.replicate]
lemma step_nil (O : List Bool) :
 TM2.step program (cfg (some ()) [] O) = some (cfg none [] (false::true::O)) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

theorem emit_run_raw (N O : List Bool) :
 run (N.length+1) (cfg (some ()) N O) =
 some (cfg none [] (false::(List.replicate (8*N.length+1) true++O))) := by
 induction N generalizing O with
 | nil => simpa using run_one _ _ (step_nil O)
 | cons b N ih =>
   have h := run_comp (run_one _ _ (step_cons b N O)) (ih (List.replicate 8 true++O))
   have he : 8*(N.length+1)+1 = (8*N.length+1)+8 := by omega
   simp only [List.length_cons]
   rw [he,List.replicate_add,List.append_assoc]
   simpa only [show 1+(N.length+1)=(N.length+1)+1 by omega] using h

theorem emit_run (N O : List Bool) :
 run (N.length+1) (cfg (some ()) N O) =
 some (cfg none [] ((header (8*N.length+1)).reverse++O)) := by
 simpa [header,List.reverse_append,List.reverse_replicate] using emit_run_raw N O

theorem emit_unary (n : Nat) (O : List Bool) :
 run (n+1) (cfg (some ()) (List.replicate n true) O) =
 some (cfg none [] ((header (8*n+1)).reverse++O)) := by
 simpa using emit_run (List.replicate n true) O

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance
end PEqualNP.Outside.L_lib_895_aux.EmitHeader

namespace PEqualNP.Outside.L_lib_895_aux.ZeroCopy
open Turing
inductive Stack where | source | temp | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.source,.temp,.output] (by intro k; cases k <;> simp)
inductive Label where | duplicate | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.duplicate,.restore] (by intro l; cases l <;> simp)
abbrev State := Option Bool
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def stk (w t r : List Bool) : Stack → List Bool
  | .source => w | .temp => t | .output => r
def cfg (l : Option Label) (s : State) (w t r : List Bool) : Cfg := ⟨l,s,stk w t r⟩
lemma setSource (w w' t r : List Bool) : Function.update (stk w t r) .source w' = stk w' t r := by
  funext k; cases k <;> simp [stk]
lemma setTemp (w t t' r : List Bool) : Function.update (stk w t r) .temp t' = stk w t' r := by
  funext k; cases k <;> simp [stk]
lemma setOutput (w t r r' : List Bool) : Function.update (stk w t r) .output r' = stk w t r' := by
  funext k; cases k <;> simp [stk]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .duplicate => .pop .source (fun _ o => o)
      (.branch Option.isSome
        (.push .temp (fun s => s.getD false)
          (.push .output (fun _ => false)
            (.load (fun _ => none) (.goto fun _ => .duplicate))))
        (.load (fun _ => none) (.goto fun _ => .restore)))
  | .restore => .pop .temp (fun _ o => o)
      (.branch Option.isSome
        (.push .source (fun s => s.getD false)
          (.load (fun _ => none) (.goto fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .duplicate
  σ := State
  initialState := none
  m := program

def startCfg (w r : List Bool) : Cfg := cfg (some .duplicate) none w [] r
def endCfg (w r : List Bool) : Cfg := cfg none none w [] (List.replicate w.length false++r)

lemma duplicate_cons (s : State) (b : Bool) (w t r : List Bool) :
    TM2.step program (cfg (some .duplicate) s (b::w) t r) =
      some (cfg (some .duplicate) none w (b::t) (false::r)) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma duplicate_nil (s : State) (t r : List Bool) :
    TM2.step program (cfg (some .duplicate) s [] t r) =
      some (cfg (some .restore) none [] t r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma restore_cons (s : State) (b : Bool) (w t r : List Bool) :
    TM2.step program (cfg (some .restore) s w (b::t) r) =
      some (cfg (some .restore) none (b::w) t r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma restore_nil (s : State) (w r : List Bool) :
    TM2.step program (cfg (some .restore) s w [] r) = some (cfg none none w [] r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]

lemma replicate_push (n : Nat) (r : List Bool) :
    List.replicate n false ++ false::r = false::(List.replicate n false++r) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] using ih

lemma pass_duplicate (w : List Bool) : ∀ (t r : List Bool) (s : State),
    (flip bind (TM2.step program))^[w.length+1] (some (cfg (some .duplicate) s w t r)) =
      some (cfg (some .restore) none [] (w.reverse++t) (List.replicate w.length false++r)) := by
  induction w with
  | nil => intro t r s; exact duplicate_nil s t r
  | cons b w ih =>
    intro t r s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .duplicate) s (b::w) t r)) =
        some (cfg (some .duplicate) none w (b::t) (false::r)) := duplicate_cons s b w t r
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc,List.replicate_succ,replicate_push ]

lemma pass_restore (t : List Bool) : ∀ (w r : List Bool) (s : State),
    (flip bind (TM2.step program))^[t.length+1] (some (cfg (some .restore) s w t r)) =
      some (cfg none none (t.reverse++w) [] r) := by
  induction t with
  | nil => intro w r s; exact restore_nil s w r
  | cons b t ih =>
    intro w r s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .restore) s w (b::t) r)) =
        some (cfg (some .restore) none (b::w) t r) := restore_cons s b w t r
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc,List.replicate_succ,replicate_push ]

theorem emit_run (w r : List Bool) :
    (flip bind (TM2.step program))^[2*w.length+2] (some (startCfg w r)) = some (endCfg w r) := by
  have hA := pass_duplicate w [] r none
  simp only [List.append_nil] at hA
  have hB := pass_restore w.reverse [] (List.replicate w.length false++r) none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hB
  change (flip bind (TM2.step program))^[2*w.length+2]
    (some (cfg (some .duplicate) none w [] r)) = some (cfg none none w [] (List.replicate w.length false++r))
  rw [show 2*w.length+2=(w.length+1)+(w.length+1) by omega,
    Function.iterate_add_apply,hA,hB]

def emit_evals (w r : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (startCfg w r) (some (endCfg w r))
      (2*w.length+2) where
  steps := 2*w.length+2
  evals_in_steps := emit_run w r
  steps_le_m := le_rfl

lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by intro j; change Finite Bool; infer_instance
lemma finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma finite_state : Finite machine.σ := by change Finite State; infer_instance
lemma final_stacks (w r : List Bool) :
    (endCfg w r).stk .source = w ∧ (endCfg w r).stk .temp = [] ∧
      (endCfg w r).stk .output = List.replicate w.length false++r := ⟨rfl,rfl,rfl⟩
lemma final_control (w r : List Bool) : (endCfg w r).l = none ∧ (endCfg w r).var = none := ⟨rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.ZeroCopy

namespace PEqualNP.Outside.L_lib_895_aux.Clear
open Turing

def prog {α : Type} : Unit → TM2.Stmt (fun _ : Unit => α) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch id (.load (fun _ => false) (.goto fun _ => ())) .halt)

def cfg {α : Type} (l : Option Unit) (xs : List α) : TM2.Cfg (fun _ : Unit => α) Unit Bool :=
  ⟨l,false,fun _ => xs⟩

lemma update_unit {α : Type} (xs ys : List α) :
    Function.update (fun _ : Unit => xs) () ys = fun _ => ys := by
  funext k
  cases k
  rfl

lemma pop_cons {α : Type} (x : α) (xs : List α) :
    TM2.step prog (cfg (some ()) (x::xs)) = some (cfg (some ()) xs) := by
  simp [TM2.step,TM2.stepAux,prog,cfg,update_unit]

lemma pop_nil {α : Type} :
    TM2.step prog (cfg (some ()) ([] : List α)) = some (cfg none []) := by
  simp [TM2.step,TM2.stepAux,prog,cfg,update_unit]

theorem clear_run {α : Type} (xs : List α) :
    (fun s : Option (TM2.Cfg (fun _ : Unit => α) Unit Bool) => s.bind (TM2.step prog))^[xs.length+1]
      (some (cfg (some ()) xs)) = some (cfg none []) := by
  induction xs with
  | nil => simpa using pop_nil (α := α)
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [Option.bind_some,pop_cons]
    exact ih

def machine (α : Type) [Fintype α] : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := α
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := prog

lemma all_alphabets_finite (α : Type) [Fintype α] : ∀ j, Finite ((machine α).Γ j) := by
  intro j
  change Finite α
  infer_instance

def clear_evals {α : Type} (xs : List α) :
    StateTransition.EvalsToInTime (TM2.step prog) (cfg (some ()) xs)
      (some (cfg none [])) (xs.length+1) where
  steps := xs.length+1
  evals_in_steps := clear_run xs
  steps_le_m := le_rfl

lemma machine_run (α : Type) [Fintype α] (xs : List α) :
    (flip bind (machine α).step)^[xs.length+1]
      (some (initList (machine α) xs)) = some (haltList (machine α) []) := by
  have hi : initList (machine α) xs = cfg (some ()) xs := by
    congr 1
  have hf : haltList (machine α) [] = cfg none [] := by
    congr 1
  rw [hi,hf]
  exact clear_run xs

noncomputable def clearComputable (α : Type) [Fintype α] :
    TM2ComputableInTime (fun x : List α => x) (fun x : List α => x) (fun _ => []) where
  tm := machine α
  inputAlphabet := Equiv.refl α
  outputAlphabet := Equiv.refl α
  time n := n+1
  outputsFun xs :=
    { steps := xs.length+1
      evals_in_steps := by
        have hm : ∀ l : List α, List.map (Equiv.refl α).invFun l = l := fun l => by simp
        exact (congrArg (fun l : List α => (flip bind (machine α).step)^[xs.length+1]
          (some (initList (machine α) l))) (hm xs)).trans
          ((machine_run α xs).trans (congrArg (fun l : List α => some (haltList (machine α) l))
            (hm []).symm))
      steps_le_m := le_rfl }

end PEqualNP.Outside.L_lib_895_aux.Clear

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing
inductive Stack where | input | a | b | unary | headerCopy | output | tmp deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.a,.b,.unary,.headerCopy,.output,.tmp] (by intro k; cases k <;> simp)
inductive Label where
 | hdr (l : Fin 3) | min (l : Unit) | copy (l : Copy.Label)
 | emit (l : Unit) | zero (l : ZeroCopy.Label) | clearGood (l : Unit)
 | afterHeader | afterMin | afterCopy | afterEmit | afterZero | success | reject
 | badClear (k : Stack) | badDone
 deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.hdr 0,.hdr 1,.hdr 2,.min (),.copy .duplicate,.copy .restore,.copy .copyBack,.emit (),.zero .duplicate,.zero .restore,.clearGood (),.afterHeader,.afterMin,.afterCopy,.afterEmit,.afterZero,.success,.reject,.badClear .input,.badClear .a,.badClear .b,.badClear .unary,.badClear .headerCopy,.badClear .output,.badClear .tmp,.badDone] (by intro l; cases l with
 | hdr l => fin_cases l <;> simp
 | min l => cases l; simp
 | copy l => cases l <;> simp
 | emit l => cases l; simp
 | zero l => cases l <;> simp
 | clearGood l => cases l; simp
 | badClear k => cases k <;> simp
 | _ => simp)
abbrev State := Option Bool × Bool
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def stk (I A B N H O T : List Bool) : Stack → List Bool
 | .input => I | .a => A | .b => B | .unary => N | .headerCopy => H | .output => O | .tmp => T
def cfg (l : Option Label) (s : State) (I A B N H O T : List Bool) : Cfg :=
 ⟨l,s,stk I A B N H O T⟩
def unitState : State ≃ State × Unit where
 toFun s := (s,())
 invFun s := s.1
 left_inv _ := rfl
 right_inv := by rintro ⟨s,⟨⟩⟩; rfl

def hdrK : Fin 4 → Stack
 | 0 => .input
 | 1 => .b
 | 2 => .tmp
 | 3 => .unary
def hdrKD : Stack → Option (Fin 4)
 | .input => some 0
 | .b => some 1
 | .tmp => some 2
 | .unary => some 3
 | _ => none
def hdrKS := CallLayout.optionSplit hdrK hdrKD
 (by intro k; fin_cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [hdrKD,hdrK] <;> subst k <;> rfl)
def hdrLD : Label → Option (Fin 3)
 | .hdr l => some l
 | _ => none
def hdrLS := CallLayout.optionSplit Label.hdr hdrLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [hdrLD])
def hdrRet : {j : Label // hdrLD j = none} := ⟨.afterHeader,rfl⟩

def minK : Unit → Stack
 | () => .b
def minKD : Stack → Option (Unit)
 | .b => some ()
 | _ => none
def minKS := CallLayout.optionSplit minK minKD
 (by intro k; cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [minKD,minK] <;> subst k <;> rfl)
def minLD : Label → Option (Unit)
 | .min l => some l
 | _ => none
def minLS := CallLayout.optionSplit Label.min minLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [minLD])
def minRet : {j : Label // minLD j = none} := ⟨.afterMin,rfl⟩

def copyK : Copy.Stack → Stack
 | .A => .unary
 | .B => .headerCopy
 | .C => .tmp
def copyKD : Stack → Option (Copy.Stack)
 | .unary => some .A
 | .headerCopy => some .B
 | .tmp => some .C
 | _ => none
def copyKS := CallLayout.optionSplit copyK copyKD
 (by intro k; cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [copyKD,copyK] <;> subst k <;> rfl)
def copyLD : Label → Option (Copy.Label)
 | .copy l => some l
 | _ => none
def copyLS := CallLayout.optionSplit Label.copy copyLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [copyLD])
def copyRet : {j : Label // copyLD j = none} := ⟨.afterCopy,rfl⟩

def emitK : Fin 2 → Stack
 | 0 => .headerCopy
 | 1 => .output
def emitKD : Stack → Option (Fin 2)
 | .headerCopy => some 0
 | .output => some 1
 | _ => none
def emitKS := CallLayout.optionSplit emitK emitKD
 (by intro k; fin_cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [emitKD,emitK] <;> subst k <;> rfl)
def emitLD : Label → Option (Unit)
 | .emit l => some l
 | _ => none
def emitLS := CallLayout.optionSplit Label.emit emitLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [emitLD])
def emitRet : {j : Label // emitLD j = none} := ⟨.afterEmit,rfl⟩

def zeroK : ZeroCopy.Stack → Stack
 | .source => .b
 | .temp => .tmp
 | .output => .a
def zeroKD : Stack → Option (ZeroCopy.Stack)
 | .b => some .source
 | .tmp => some .temp
 | .a => some .output
 | _ => none
def zeroKS := CallLayout.optionSplit zeroK zeroKD
 (by intro k; cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [zeroKD,zeroK] <;> subst k <;> rfl)
def zeroLD : Label → Option (ZeroCopy.Label)
 | .zero l => some l
 | _ => none
def zeroLS := CallLayout.optionSplit Label.zero zeroLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [zeroLD])
def zeroRet : {j : Label // zeroLD j = none} := ⟨.afterZero,rfl⟩

def clearGoodK : Unit → Stack
 | () => .b
def clearGoodKD : Stack → Option (Unit)
 | .b => some ()
 | _ => none
def clearGoodKS := CallLayout.optionSplit clearGoodK clearGoodKD
 (by intro k; cases k <;> rfl)
 (by intro j k h; cases j <;> simp_all [clearGoodKD,clearGoodK] <;> subst k <;> rfl)
def clearGoodLD : Label → Option (Unit)
 | .clearGood l => some l
 | _ => none
def clearGoodLS := CallLayout.optionSplit Label.clearGood clearGoodLD
 (by intro k; rfl)
 (by intro j k h; cases j <;> simp_all [clearGoodLD])
def clearGoodRet : {j : Label // clearGoodLD j = none} := ⟨.success,rfl⟩

def badKD (k j : Stack) : Option Unit := if j=k then some () else none
def badKS (k : Stack) := CallLayout.optionSplit (fun _ : Unit => k) (badKD k)
 (by intro u; cases u; simp [badKD])
 (by intro j u h; cases u; by_cases hj : j=k; subst j; rfl; simp [badKD,hj] at h)
def badLD (k : Stack) (l : Label) : Option Unit := if l=.badClear k then some () else none
def badLS (k : Stack) := CallLayout.optionSplit (fun _ : Unit => Label.badClear k) (badLD k)
 (by intro u; cases u; simp [badLD])
 (by intro j u h; cases u; by_cases hj : j=.badClear k; subst j; rfl; simp [badLD,hj] at h)
def badNext : Stack → Label
 | .input => .badClear .a | .a => .badClear .b | .b => .badClear .unary
 | .unary => .badClear .headerCopy | .headerCopy => .badClear .output
 | .output => .badClear .tmp | .tmp => .badDone
def badRet (k : Stack) : {j : Label // badLD k j = none} :=
 ⟨badNext k,by cases k <;> decide⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
 | .hdr l => BoolCall.trStmt hdrKS hdrLS (Equiv.refl State) hdrRet (Header.program l)
 | .min l => BoolCall.trStmt minKS minLS unitState minRet (MinTwo.program l)
 | .copy l => BoolCall.trStmt copyKS copyLS (Equiv.refl State) copyRet (Copy.program l)
 | .emit l => BoolCall.trStmt emitKS emitLS (Equiv.refl State) emitRet (EmitHeader.program l)
 | .zero l => BoolCall.trStmt zeroKS zeroLS (Equiv.refl State) zeroRet (ZeroCopy.program l)
 | .clearGood l => BoolCall.trStmt clearGoodKS clearGoodLS (Equiv.prodComm (Option Bool) Bool) clearGoodRet (Clear.prog l)
 | .afterHeader => .branch (fun s => s.1 == some false)
     (.load (fun _ => (none,false)) (.goto fun _ => .min ()))
     (.load (fun _ => (none,false)) (.goto fun _ => .reject))
 | .afterMin => .branch (fun s => s.2)
     (.goto fun _ => .copy .duplicate)
     (.load (fun _ => (none,false)) (.goto fun _ => .reject))
 | .afterCopy => .goto fun _ => .emit ()
 | .afterEmit => .goto fun _ => .zero .duplicate
 | .afterZero => .load (fun _ => (none,false)) (.goto fun _ => .clearGood ())
 | .success => .load (fun _ => (none,true)) .halt
 | .reject => .load (fun _ => (none,false)) (.goto fun _ => .badClear .input)
 | .badClear k => BoolCall.trStmt (badKS k) (badLS k) (Equiv.prodComm (Option Bool) Bool) (badRet k) (Clear.prog ())
 | .badDone => .load (fun _ => (none,false)) .halt

def machine : FinTM2 where
 K := Stack
 k₀ := .input
 k₁ := .output
 Γ _ := Bool
 Λ := Label
 main := .hdr 0
 σ := State
 initialState := (none,false)
 m := program

def run (t : Nat) (c : Cfg) : Option Cfg :=
 (fun s : Option Cfg => s.bind (TM2.step program))^[t] (some c)
lemma run_one (c d : Cfg) (h : TM2.step program c = some d) : run 1 c = some d := by
 simpa only [run,Function.iterate_one,Option.bind_some] using h
lemma run_comp {s t : Nat} {a b c : Cfg}
 (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing
lemma cfg_ext (c d : Cfg) (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
 cases c; cases d; cases hl; cases hv; cases hs; rfl

lemma hdr_lift (l : Option (Fin 3)) (v : Option Bool) (I A B N H O T : List Bool) :
 BoolCall.liftCfg hdrKS hdrLS (Equiv.refl State) hdrRet false
   (fun e => stk [] A [] [] H O [] e.val) (Header.cfg l v I B T N) =
 cfg (some (l.elim .afterHeader Label.hdr)) (v,false) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

lemma min_lift (l : Option Unit) (v : Bool) (I A B N H O T : List Bool) :
 BoolCall.liftCfg minKS minLS unitState minRet ()
   (fun e => stk I A [] N H O T e.val) (MinTwo.cfg l v B) =
 cfg (some (l.elim .afterMin Label.min)) (none,v) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

lemma copy_lift (l : Option (Copy.Label)) (s : Option Bool) (v : Bool) (I A B N H O T : List Bool) :
 BoolCall.liftCfg copyKS copyLS (Equiv.refl State) copyRet v
   (fun e => stk I A B [] [] O [] e.val) (Copy.cfg l s N H T) =
 cfg (some (l.elim .afterCopy Label.copy)) (s,v) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

lemma emit_lift (l : Option (Unit)) (v : Bool) (I A B N H O T : List Bool) :
 BoolCall.liftCfg emitKS emitLS (Equiv.refl State) emitRet v
   (fun e => stk I A B N [] [] T e.val) (EmitHeader.cfg l H O) =
 cfg (some (l.elim .afterEmit Label.emit)) (none,v) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

lemma zero_lift (l : Option (ZeroCopy.Label)) (s : Option Bool) (v : Bool) (I A B N H O T : List Bool) :
 BoolCall.liftCfg zeroKS zeroLS (Equiv.refl State) zeroRet v
   (fun e => stk I [] [] N H O [] e.val) (ZeroCopy.cfg l s B T A) =
 cfg (some (l.elim .afterZero Label.zero)) (s,v) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

lemma clearGood_lift (l : Option (Unit))  (I A B N H O T : List Bool) :
 BoolCall.liftCfg clearGoodKS clearGoodLS (Equiv.prodComm (Option Bool) Bool) clearGoodRet none
   (fun e => stk I A [] N H O T e.val) (Clear.cfg l B) =
 cfg (some (l.elim .success Label.clearGood)) (none,false) I A B N H O T := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext k
   cases k <;> rfl

end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing

lemma call_header (n : Nat) (I : List Bool) (hn : 2 ≤ n) :
 ∃ t ≤ 5*(n+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (header n++I) [] [] [] [] [] []) =
 some (cfg (some .afterHeader) (some false,false) I [] (bits (width n) n) (List.replicate n true) [] [] []) := by
 obtain ⟨t,ht,hr⟩ := Header.canonical_header_run n I hn
 have h := BoolCall.run_lift hdrKS hdrLS (Equiv.refl State) hdrRet false
   (fun e => stk [] [] [] [] [] [] [] e.val) Header.program program (by intro l; rfl)
   t _ _ hr
 rw [hdr_lift,hdr_lift] at h
 refine ⟨t,ht,?_⟩
 simp only [header,List.append_assoc,List.singleton_append]
 exact h

lemma call_min (I A B N H O T : List Bool) :
 run 1 (cfg (some (.min ())) (none,false) I A B N H O T) =
 some (cfg (some .afterMin) (none,decide (2≤B.length)) I A B N H O T) := by
 have h := BoolCall.step_sim minKS minLS unitState minRet ()
   (fun e => stk I A [] N H O T e.val) MinTwo.program program (by intro l; rfl)
   _ _ (MinTwo.check_run B)
 rw [min_lift,min_lift] at h
 exact run_one _ _ h

lemma call_copy (I A B N O : List Bool) (v : Bool) :
 run (3*N.length+3) (cfg (some (.copy .duplicate)) (none,v) I A B N [] O []) =
 some (cfg (some .afterCopy) (none,v) I A B N N O []) := by
 have h := BoolCall.run_lift copyKS copyLS (Equiv.refl State) copyRet v
   (fun e => stk I A B [] [] O [] e.val) Copy.program program (by intro l; rfl)
   _ _ _ (Copy.copy_run N)
 change (flip bind (TM2.step program))^[3*N.length+3]
   (some (BoolCall.liftCfg copyKS copyLS (Equiv.refl State) copyRet v
     (fun e => stk I A B [] [] O [] e.val) (Copy.cfg (some .duplicate) none N [] []))) =
   some (BoolCall.liftCfg copyKS copyLS (Equiv.refl State) copyRet v
     (fun e => stk I A B [] [] O [] e.val) (Copy.cfg none none N N [])) at h
 rw [copy_lift,copy_lift] at h
 exact h

lemma call_emit (I A B N H O T : List Bool) (v : Bool) :
 run (H.length+1) (cfg (some (.emit ())) (none,v) I A B N H O T) =
 some (cfg (some .afterEmit) (none,v) I A B N [] ((header (8*H.length+1)).reverse++O) T) := by
 have h := BoolCall.run_lift emitKS emitLS (Equiv.refl State) emitRet v
   (fun e => stk I A B N [] [] T e.val) EmitHeader.program program (by intro l; rfl)
   _ _ _ (EmitHeader.emit_run H O)
 rw [emit_lift,emit_lift] at h
 exact h

lemma call_zero (I B N H O : List Bool) (v : Bool) :
 run (2*B.length+2) (cfg (some (.zero .duplicate)) (none,v) I [] B N H O []) =
 some (cfg (some .afterZero) (none,v) I (List.replicate B.length false) B N H O []) := by
 have h := BoolCall.run_lift zeroKS zeroLS (Equiv.refl State) zeroRet v
   (fun e => stk I [] [] N H O [] e.val) ZeroCopy.program program (by intro l; rfl)
   _ _ _ (ZeroCopy.emit_run B [])
 change (flip bind (TM2.step program))^[2*B.length+2]
   (some (BoolCall.liftCfg zeroKS zeroLS (Equiv.refl State) zeroRet v
     (fun e => stk I [] [] N H O [] e.val) (ZeroCopy.cfg (some .duplicate) none B [] []))) =
   some (BoolCall.liftCfg zeroKS zeroLS (Equiv.refl State) zeroRet v
     (fun e => stk I [] [] N H O [] e.val) (ZeroCopy.cfg none none B [] (List.replicate B.length false++[]))) at h
 rw [zero_lift,zero_lift] at h
 rw [List.append_nil] at h
 exact h

lemma call_clear (I A B N H O T : List Bool) :
 run (B.length+1) (cfg (some (.clearGood ())) (none,false) I A B N H O T) =
 some (cfg (some .success) (none,false) I A [] N H O T) := by
 have h := BoolCall.run_lift clearGoodKS clearGoodLS (Equiv.prodComm (Option Bool) Bool) clearGoodRet none
   (fun e => stk I A [] N H O T e.val) Clear.prog program (by intro l; rfl)
   _ _ _ (Clear.clear_run B)
 rw [clearGood_lift,clearGood_lift] at h
 exact h
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing
lemma after_header (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterHeader) (some false,false) I A B N H O T) =
 some (cfg (some (.min ())) (none,false) I A B N H O T) := rfl
lemma after_min (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterMin) (none,true) I A B N H O T) =
 some (cfg (some (.copy .duplicate)) (none,true) I A B N H O T) := rfl
lemma after_copy (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterCopy) (none,true) I A B N H O T) =
 some (cfg (some (.emit ())) (none,true) I A B N H O T) := rfl
lemma after_emit (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterEmit) (none,true) I A B N H O T) =
 some (cfg (some (.zero .duplicate)) (none,true) I A B N H O T) := rfl
lemma after_zero (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterZero) (none,true) I A B N H O T) =
 some (cfg (some (.clearGood ())) (none,false) I A B N H O T) := rfl
lemma finish (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .success) (none,false) I A B N H O T) =
 some (cfg none (none,true) I A B N H O T) := rfl
lemma bits_zero (w : Nat) : bits w 0 = List.replicate w false := by
 simp [bits,List.map_const]

theorem valid_prefix (n : Nat) (I : List Bool) (hn : 2 ≤ n) :
 ∃ t ≤ 30*((header n++I).length+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (header n++I) [] [] [] [] [] []) =
 some (cfg none (none,true) I (bits (width n) 0) [] (List.replicate n true) []
   (header (8*n+1)).reverse []) := by
 let B := bits (width n) n
 let N := List.replicate n true
 let O := (header (8*n+1)).reverse
 have hBl : B.length = width n := bits_length _ _
 have hNl : N.length = n := List.length_replicate
 have hacc : decide (2≤B.length) = true := by
   simp only [hBl]
   exact decide_eq_true (MinTwo.width_min_two n hn)
 obtain ⟨t,ht,hh⟩ := call_header n I hn
 have h := run_comp hh (run_one _ _ (after_header I [] B N [] [] []))
 have hm := call_min I [] B N [] [] []
 rw [hacc] at hm
 have h := run_comp h hm
 have h := run_comp h (run_one _ _ (after_min I [] B N [] [] []))
 have h := run_comp h (call_copy I [] B N [] true)
 have h := run_comp h (run_one _ _ (after_copy I [] B N N [] []))
 have he := call_emit I [] B N N [] [] true
 rw [hNl,List.append_nil] at he
 have h := run_comp h he
 have h := run_comp h (run_one _ _ (after_emit I [] B N [] O []))
 have h := run_comp h (call_zero I B N [] O true)
 have h := run_comp h (run_one _ _ (after_zero I (List.replicate B.length false) B N [] O []))
 have h := run_comp h (call_clear I (List.replicate B.length false) B N [] O [])
 have h := run_comp h (run_one _ _ (finish I (List.replicate B.length false) [] N [] O []))
 refine ⟨t+1+1+1+(3*N.length+3)+1+(n+1)+1+(2*B.length+2)+1+(B.length+1)+1,?_,?_⟩
 · have hw : width n ≤ n+1 := by
     unfold width
     have := Nat.log2_le_self n
     omega
   have hlen : n ≤ (header n++I).length := by simp [header]
   rw [hNl,hBl]
   nlinarith
 · have hz : List.replicate B.length false = bits (width n) 0 := by rw [hBl,bits_zero]
   rw [hz] at h
   exact h
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Carry
open Turing
abbrev RC := TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)
def stk (C T : List Bool) : Fin 2 → List Bool := ![C,T]
@[simp] lemma stk_get0 (C T : List Bool) : stk C T 0 = C := rfl
@[simp] lemma stk_get1 (C T : List Bool) : stk C T 1 = T := rfl
@[simp] lemma stk_set0 (C T X : List Bool) : Function.update (stk C T) 0 X = stk X T := by
 funext k; fin_cases k <;> rfl
@[simp] lemma stk_set1 (C T X : List Bool) : Function.update (stk C T) 1 X = stk C X := by
 funext k; fin_cases k <;> rfl

def program : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)
 | 0 => .pop 0 (fun _ x => x) (.branch (fun s => s == some true)
     (.push 1 (fun _ => false) (.load (fun _ => none) (.goto fun _ => 0)))
     (.push 0 (fun _ => true) (.load (fun _ => none) (.goto fun _ => 1))))
 | _ => .pop 1 (fun _ x => x) (.branch Option.isSome
     (.push 0 (fun s => s.getD false) (.load (fun _ => none) (.goto fun _ => 1)))
     (.load (fun _ => none) .halt))
def machine : FinTM2 where
 K := Fin 2
 k₀ := 0
 k₁ := 0
 Γ _ := Bool
 Λ := Fin 2
 main := 0
 σ := Option Bool
 initialState := none
 m := program

def cfg (l : Option (Fin 2)) (C T : List Bool) : RC := ⟨l,none,stk C T⟩
def run (t : Nat) (c : RC) : Option RC :=
 (fun s : Option RC => s.bind (TM2.step program))^[t] (some c)
lemma run_one (c d : RC) (h : TM2.step program c = some d) : run 1 c = some d := by
 simpa only [run,Function.iterate_one,Option.bind_some] using h
lemma run_comp {s t : Nat} {a b c : RC}
 (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]
lemma carry_true (C T : List Bool) :
 TM2.step program (cfg (some 0) (true::C) T) = some (cfg (some 0) C (false::T)) := by
 simp [TM2.step,program,cfg,TM2.stepAux]
lemma carry_false (C T : List Bool) :
 TM2.step program (cfg (some 0) (false::C) T) = some (cfg (some 1) (true::C) T) := by
 simp [TM2.step,program,cfg,TM2.stepAux]
lemma carry_empty (T : List Bool) :
 TM2.step program (cfg (some 0) [] T) = some (cfg (some 1) [true] T) := by
 simp [TM2.step,program,cfg,TM2.stepAux]
lemma restore_cons (C T : List Bool) (b : Bool) :
 TM2.step program (cfg (some 1) C (b::T)) = some (cfg (some 1) (b::C) T) := by
 simp [TM2.step,program,cfg,TM2.stepAux]
lemma restore_empty (C : List Bool) :
 TM2.step program (cfg (some 1) C []) = some (cfg none C []) := by
 simp [TM2.step,program,cfg,TM2.stepAux]
lemma restore_run (C T : List Bool) :
 run (T.length+1) (cfg (some 1) C T) = some (cfg none (T.reverse++C) []) := by
 induction T generalizing C with
 | nil => simpa using run_one _ _ (restore_empty C)
 | cons b T ih =>
   have hh := run_comp (run_one _ _ (restore_cons C T b)) (ih (b::C))
   simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

theorem carry_run (C T : List Bool) :
 ∃ t ≤ 2*C.length+T.length+2,
 run t (cfg (some 0) C T) = some (cfg none (T.reverse++growInc C) []) := by
 induction C generalizing T with
 | nil =>
   refine ⟨1+(T.length+1),by simp; omega,?_⟩
   simpa [growInc] using run_comp (run_one _ _ (carry_empty T)) (restore_run [true] T)
 | cons b C ih =>
   cases b with
   | false =>
     refine ⟨1+(T.length+1),by simp; omega,?_⟩
     simpa [growInc] using run_comp (run_one _ _ (carry_false C T)) (restore_run (true::C) T)
   | true =>
     obtain ⟨t,ht,hr⟩ := ih (false::T)
     refine ⟨1+t,by simp_all; omega,?_⟩
     have hh := run_comp (run_one _ _ (carry_true C T)) hr
     simpa [growInc,List.reverse_cons,List.append_assoc] using hh

theorem increment_run (C : List Bool) :
 ∃ t ≤ 2*C.length+2, run t (cfg (some 0) C []) = some (cfg none (growInc C) []) := by
 obtain ⟨t,ht,hh⟩ := carry_run C []
 exact ⟨t,by simpa using ht,by simpa using hh⟩
theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance
end PEqualNP.Outside.L_lib_895_aux.Carry

namespace PEqualNP.Outside.L_lib_895_aux.EmitWord
open Turing
inductive Stack where | source | temp | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.source,.temp,.output] (by intro k; cases k <;> simp)
inductive Label where | duplicate | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.duplicate,.restore] (by intro l; cases l <;> simp)
abbrev State := Option Bool
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def stk (w t r : List Bool) : Stack → List Bool
  | .source => w | .temp => t | .output => r
def cfg (l : Option Label) (s : State) (w t r : List Bool) : Cfg := ⟨l,s,stk w t r⟩
lemma setSource (w w' t r : List Bool) : Function.update (stk w t r) .source w' = stk w' t r := by
  funext k; cases k <;> simp [stk]
lemma setTemp (w t t' r : List Bool) : Function.update (stk w t r) .temp t' = stk w t' r := by
  funext k; cases k <;> simp [stk]
lemma setOutput (w t r r' : List Bool) : Function.update (stk w t r) .output r' = stk w t r' := by
  funext k; cases k <;> simp [stk]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .duplicate => .pop .source (fun _ o => o)
      (.branch Option.isSome
        (.push .temp (fun s => s.getD false)
          (.push .output (fun s => s.getD false)
            (.load (fun _ => none) (.goto fun _ => .duplicate))))
        (.load (fun _ => none) (.goto fun _ => .restore)))
  | .restore => .pop .temp (fun _ o => o)
      (.branch Option.isSome
        (.push .source (fun s => s.getD false)
          (.load (fun _ => none) (.goto fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .duplicate
  σ := State
  initialState := none
  m := program

def startCfg (w r : List Bool) : Cfg := cfg (some .duplicate) none w [] r
def endCfg (w r : List Bool) : Cfg := cfg none none w [] (w.reverse++r)

lemma duplicate_cons (s : State) (b : Bool) (w t r : List Bool) :
    TM2.step program (cfg (some .duplicate) s (b::w) t r) =
      some (cfg (some .duplicate) none w (b::t) (b::r)) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma duplicate_nil (s : State) (t r : List Bool) :
    TM2.step program (cfg (some .duplicate) s [] t r) =
      some (cfg (some .restore) none [] t r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma restore_cons (s : State) (b : Bool) (w t r : List Bool) :
    TM2.step program (cfg (some .restore) s w (b::t) r) =
      some (cfg (some .restore) none (b::w) t r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]
lemma restore_nil (s : State) (w r : List Bool) :
    TM2.step program (cfg (some .restore) s w [] r) = some (cfg none none w [] r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setTemp,setOutput]

lemma pass_duplicate (w : List Bool) : ∀ (t r : List Bool) (s : State),
    (flip bind (TM2.step program))^[w.length+1] (some (cfg (some .duplicate) s w t r)) =
      some (cfg (some .restore) none [] (w.reverse++t) (w.reverse++r)) := by
  induction w with
  | nil => intro t r s; exact duplicate_nil s t r
  | cons b w ih =>
    intro t r s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .duplicate) s (b::w) t r)) =
        some (cfg (some .duplicate) none w (b::t) (b::r)) := duplicate_cons s b w t r
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

lemma pass_restore (t : List Bool) : ∀ (w r : List Bool) (s : State),
    (flip bind (TM2.step program))^[t.length+1] (some (cfg (some .restore) s w t r)) =
      some (cfg none none (t.reverse++w) [] r) := by
  induction t with
  | nil => intro w r s; exact restore_nil s w r
  | cons b t ih =>
    intro w r s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some .restore) s w (b::t) r)) =
        some (cfg (some .restore) none (b::w) t r) := restore_cons s b w t r
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

theorem emit_run (w r : List Bool) :
    (flip bind (TM2.step program))^[2*w.length+2] (some (startCfg w r)) = some (endCfg w r) := by
  have hA := pass_duplicate w [] r none
  simp only [List.append_nil] at hA
  have hB := pass_restore w.reverse [] (w.reverse++r) none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hB
  change (flip bind (TM2.step program))^[2*w.length+2]
    (some (cfg (some .duplicate) none w [] r)) = some (cfg none none w [] (w.reverse++r))
  rw [show 2*w.length+2=(w.length+1)+(w.length+1) by omega,
    Function.iterate_add_apply,hA,hB]

def emit_evals (w r : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (startCfg w r) (some (endCfg w r))
      (2*w.length+2) where
  steps := 2*w.length+2
  evals_in_steps := emit_run w r
  steps_le_m := le_rfl

lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by intro j; change Finite Bool; infer_instance
lemma finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma finite_state : Finite machine.σ := by change Finite State; infer_instance
lemma final_stacks (w r : List Bool) :
    (endCfg w r).stk .source = w ∧ (endCfg w r).stk .temp = [] ∧
      (endCfg w r).stk .output = w.reverse++r := ⟨rfl,rfl,rfl⟩
lemma final_control (w r : List Bool) : (endCfg w r).l = none ∧ (endCfg w r).var = none := ⟨rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.EmitWord

namespace PEqualNP.Outside.L_lib_895_aux.ReverseMove
open Turing
inductive Stack where | source | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.source,.output] (by intro k; cases k <;> simp)
abbrev Label := Unit
abbrev State := Option Bool
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def stk (r o : List Bool) : Stack → List Bool | .source => r | .output => o
def cfg (l : Option Label) (s : State) (r o : List Bool) : Cfg := ⟨l,s,stk r o⟩
lemma setSource (r r' o : List Bool) : Function.update (stk r o) .source r' = stk r' o := by
  funext k; cases k <;> simp [stk]
lemma setOutput (r o o' : List Bool) : Function.update (stk r o) .output o' = stk r o' := by
  funext k; cases k <;> simp [stk]

def program (_ : Label) : TM2.Stmt (fun _ : Stack => Bool) Label State :=
  .pop .source (fun _ o => o)
    (.branch Option.isSome
      (.push .output (fun s => s.getD false)
        (.load (fun _ => none) (.goto fun _ => ())))
      (.load (fun _ => none) .halt))
def machine : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := ()
  σ := State
  initialState := none
  m := program

def startCfg (r o : List Bool) : Cfg := cfg (some ()) none r o
def endCfg (r o : List Bool) : Cfg := cfg none none [] (r.reverse++o)
lemma step_cons (s : State) (b : Bool) (r o : List Bool) :
    TM2.step program (cfg (some ()) s (b::r) o) = some (cfg (some ()) none r (b::o)) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setOutput]
lemma step_nil (s : State) (o : List Bool) :
    TM2.step program (cfg (some ()) s [] o) = some (cfg none none [] o) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,setSource,setOutput]

lemma pass (r : List Bool) : ∀ (o : List Bool) (s : State),
    (flip bind (TM2.step program))^[r.length+1] (some (cfg (some ()) s r o)) =
      some (cfg none none [] (r.reverse++o)) := by
  induction r with
  | nil => intro o s; exact step_nil s o
  | cons b r ih =>
    intro o s
    rw [List.length_cons,Function.iterate_succ_apply]
    have e : flip bind (TM2.step program) (some (cfg (some ()) s (b::r) o)) =
        some (cfg (some ()) none r (b::o)) := step_cons s b r o
    rw [e,ih]
    simp [List.reverse_cons,List.append_assoc]

theorem move_run (r o : List Bool) :
    (flip bind (TM2.step program))^[r.length+1] (some (startCfg r o)) = some (endCfg r o) := pass r o none

def move_evals (r o : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (startCfg r o) (some (endCfg r o)) (r.length+1) where
  steps := r.length+1
  evals_in_steps := move_run r o
  steps_le_m := le_rfl

theorem finish_run (r : List Bool) :
    (flip bind (TM2.step program))^[r.length+1] (some (startCfg r [])) =
      some (cfg none none [] r.reverse) := by simpa [endCfg] using move_run r []
lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by intro j; change Finite Bool; infer_instance
lemma finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma finite_state : Finite machine.σ := by change Finite State; infer_instance
lemma final_stacks (r o : List Bool) :
    (endCfg r o).stk .source = [] ∧ (endCfg r o).stk .output = r.reverse++o := ⟨rfl,rfl⟩
lemma final_control (r o : List Bool) : (endCfg r o).l = none ∧ (endCfg r o).var = none := ⟨rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.ReverseMove

namespace PEqualNP.Outside.L_lib_895_aux.TemplateMachine
open Turing
abbrev Instruction := Bool × Fin 8
abbrev Template := List Instruction
inductive Stack where | A | B | temp | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.A,.B,.temp,.output] (by intro k; cases k <;> simp)
inductive Label where | dupA | restA | dupB | restB | phase | advance deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.dupA,.restA,.dupB,.restB,.phase,.advance]
  (by intro k; cases k <;> simp)
inductive ExtraLabel where | dupOther | restOther | phase | advance deriving DecidableEq
instance : Fintype ExtraLabel := Fintype.ofList [.dupOther,.restOther,.phase,.advance]
  (by intro k; cases k <;> simp)

def ksA : Stack ≃ EmitWord.Stack ⊕ Unit where
  toFun | .A => .inl .source | .B => .inr () | .temp => .inl .temp | .output => .inl .output
  invFun | .inl .source => .A | .inl .temp => .temp | .inl .output => .output | .inr _ => .B
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with j|j; cases j <;> rfl; cases j; rfl

def ksB : Stack ≃ EmitWord.Stack ⊕ Unit where
  toFun | .B => .inl .source | .A => .inr () | .temp => .inl .temp | .output => .inl .output
  invFun | .inl .source => .B | .inl .temp => .temp | .inl .output => .output | .inr _ => .A
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with j|j; cases j <;> rfl; cases j; rfl

def lsA : Label ≃ EmitWord.Label ⊕ ExtraLabel where
  toFun | .dupA => .inl .duplicate | .restA => .inl .restore
        | .dupB => .inr .dupOther | .restB => .inr .restOther
        | .phase => .inr .phase | .advance => .inr .advance
  invFun | .inl .duplicate => .dupA | .inl .restore => .restA
         | .inr .dupOther => .dupB | .inr .restOther => .restB
         | .inr .phase => .phase | .inr .advance => .advance
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with j|j <;> cases j <;> rfl

def lsB : Label ≃ EmitWord.Label ⊕ ExtraLabel where
  toFun | .dupB => .inl .duplicate | .restB => .inl .restore
        | .dupA => .inr .dupOther | .restA => .inr .restOther
        | .phase => .inr .phase | .advance => .inr .advance
  invFun | .inl .duplicate => .dupB | .inl .restore => .restB
         | .inr .dupOther => .dupA | .inr .restOther => .restA
         | .inr .phase => .phase | .inr .advance => .advance
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with j|j <;> cases j <;> rfl

abbrev Cursor (t : Template) := Fin (t.length+1)
abbrev State (t : Template) := Option Bool × Cursor t
abbrev Cfg (t : Template) := TM2.Cfg (fun _ : Stack => Bool) Label (State t)
def zero (t : Template) : Cursor t := ⟨0,by omega⟩
def next {t : Template} (i : Cursor t) : Cursor t := ⟨(i.val+1) % (t.length+1),Nat.mod_lt _ (by omega)⟩
def instr (t : Template) (i : Cursor t) : Instruction := (t[i.val]?).getD (false,0)
def bit (c : Fin 8) (j : Nat) : Bool := c.val.testBit j
def bits3 (c : Fin 8) : List Bool := [bit c 0,bit c 1,bit c 2]
def sourceWord (b : Bool) (a bword : List Bool) := if b then bword else a
def stream (t : Template) (a b : List Bool) : List Bool :=
  t.flatMap (fun q => bits3 q.2 ++ sourceWord q.1 a b)
def cost (t : Template) (a b : List Bool) : Nat :=
  (t.map (fun q => 2*(sourceWord q.1 a b).length+4)).sum

def stk (a b tmp out : List Bool) : Stack → List Bool
  | .A => a | .B => b | .temp => tmp | .output => out
def cfg {t : Template} (l : Option Label) (s : State t) (a b tmp out : List Bool) : Cfg t :=
  ⟨l,s,stk a b tmp out⟩

def program (t : Template) : Label → TM2.Stmt (fun _ : Stack => Bool) Label (State t)
  | .dupA => BoolCall.trStmt ksA lsA (Equiv.refl _) .advance (EmitWord.program .duplicate)
  | .restA => BoolCall.trStmt ksA lsA (Equiv.refl _) .advance (EmitWord.program .restore)
  | .dupB => BoolCall.trStmt ksB lsB (Equiv.refl _) .advance (EmitWord.program .duplicate)
  | .restB => BoolCall.trStmt ksB lsB (Equiv.refl _) .advance (EmitWord.program .restore)
  | .phase => .branch (fun s => decide (s.2.val < t.length))
      (.push .output (fun s => bit (instr t s.2).2 0)
        (.push .output (fun s => bit (instr t s.2).2 1)
          (.push .output (fun s => bit (instr t s.2).2 2)
            (.branch (fun s => (instr t s.2).1)
              (.goto fun _ => .dupB) (.goto fun _ => .dupA)))))
      (.load (fun _ => (none,zero t)) .halt)
  | .advance => .load (fun s => (none,next s.2)) (.goto fun _ => .phase)

def machine (t : Template) : FinTM2 where
  K := Stack
  k₀ := .A
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .phase
  σ := State t
  initialState := (none,zero t)
  m := program t

lemma liftA_start (t : Template) (i : Cursor t) (a b r : List Bool) :
    BoolCall.liftCfg ksA lsA (Equiv.refl _) .advance i (fun _ => b) (EmitWord.startCfg a r) =
      cfg (.some .dupA) (none,i) a b [] r := by
  dsimp [BoolCall.liftCfg,cfg,EmitWord.startCfg,EmitWord.endCfg,EmitWord.cfg]
  congr 1
  funext k; cases k <;> rfl
lemma liftA_end (t : Template) (i : Cursor t) (a b r : List Bool) :
    BoolCall.liftCfg ksA lsA (Equiv.refl _) .advance i (fun _ => b) (EmitWord.endCfg a r) =
      cfg (.some .advance) (none,i) a b [] (a.reverse++r) := by
  dsimp [BoolCall.liftCfg,cfg,EmitWord.startCfg,EmitWord.endCfg,EmitWord.cfg]
  congr 1
  funext k; cases k <;> rfl
lemma liftB_start (t : Template) (i : Cursor t) (a b r : List Bool) :
    BoolCall.liftCfg ksB lsB (Equiv.refl _) .advance i (fun _ => a) (EmitWord.startCfg b r) =
      cfg (.some .dupB) (none,i) a b [] r := by
  dsimp [BoolCall.liftCfg,cfg,EmitWord.startCfg,EmitWord.endCfg,EmitWord.cfg]
  congr 1
  funext k; cases k <;> rfl
lemma liftB_end (t : Template) (i : Cursor t) (a b r : List Bool) :
    BoolCall.liftCfg ksB lsB (Equiv.refl _) .advance i (fun _ => a) (EmitWord.endCfg b r) =
      cfg (.some .advance) (none,i) a b [] (b.reverse++r) := by
  dsimp [BoolCall.liftCfg,cfg,EmitWord.startCfg,EmitWord.endCfg,EmitWord.cfg]
  congr 1
  funext k; cases k <;> rfl

lemma callA (t : Template) (i : Cursor t) (a b r : List Bool) :
    (flip bind (TM2.step (program t)))^[2*a.length+2]
      (some (cfg (some .dupA) (none,i) a b [] r)) =
        some (cfg (some .advance) (none,i) a b [] (a.reverse++r)) := by
  have h := BoolCall.run_lift ksA lsA (Equiv.refl _) .advance i (fun _ => b)
    EmitWord.program (program t) (by intro l; cases l <;> rfl) _ _ _ (EmitWord.emit_run a r)
  rw [liftA_start,liftA_end] at h
  exact h
lemma callB (t : Template) (i : Cursor t) (a b r : List Bool) :
    (flip bind (TM2.step (program t)))^[2*b.length+2]
      (some (cfg (some .dupB) (none,i) a b [] r)) =
        some (cfg (some .advance) (none,i) a b [] (b.reverse++r)) := by
  have h := BoolCall.run_lift ksB lsB (Equiv.refl _) .advance i (fun _ => a)
    EmitWord.program (program t) (by intro l; cases l <;> rfl) _ _ _ (EmitWord.emit_run b r)
  rw [liftB_start,liftB_end] at h
  exact h

end PEqualNP.Outside.L_lib_895_aux.TemplateMachine

namespace PEqualNP.Outside.L_lib_895_aux.TemplateMachine
open Turing
lemma setOutput (a b tmp r r' : List Bool) :
    Function.update (stk a b tmp r) .output r' = stk a b tmp r' := by
  funext k; cases k <;> simp [stk]

lemma phase_step (t : Template) (i : Cursor t) (q : Instruction)
    (hi : i.val<t.length) (hq : instr t i=q) (a b r : List Bool) :
    TM2.step (program t) (cfg (some .phase) (none,i) a b [] r) =
      some (cfg (some (if q.1 then .dupB else .dupA)) (none,i)
        a b [] ((bits3 q.2).reverse++r)) := by
  rcases q with ⟨src,tag⟩
  cases src <;> simp [TM2.step,program,TM2.stepAux,cfg,stk,hi,hq,bits3,setOutput]

lemma advance_step (t : Template) (i : Cursor t) (a b r : List Bool) :
    TM2.step (program t) (cfg (some .advance) (none,i) a b [] r) =
      some (cfg (some .phase) (none,next i) a b [] r) := by
  simp [TM2.step,program,TM2.stepAux,cfg]

lemma phase_end (t : Template) (i : Cursor t) (hi : i.val=t.length) (a b r : List Bool) :
    TM2.step (program t) (cfg (some .phase) (none,i) a b [] r) =
      some (cfg none (none,zero t) a b [] r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,hi]

lemma endpoint_run (t : Template) (i : Cursor t) (q : Instruction)
    (hi : i.val<t.length) (hq : instr t i=q) (a b r : List Bool) :
    (flip bind (TM2.step (program t)))^[2*(sourceWord q.1 a b).length+4]
      (some (cfg (some .phase) (none,i) a b [] r)) =
      some (cfg (some .phase) (none,next i) a b []
        ((bits3 q.2++sourceWord q.1 a b).reverse++r)) := by
  have hp : (flip bind (TM2.step (program t)))^[1]
      (some (cfg (some .phase) (none,i) a b [] r)) =
      some (cfg (some (if q.1 then .dupB else .dupA)) (none,i)
        a b [] ((bits3 q.2).reverse++r)) := phase_step t i q hi hq a b r
  rw [show 2*(sourceWord q.1 a b).length+4 = 1+((2*(sourceWord q.1 a b).length+2)+1) by omega,
    Function.iterate_add_apply,Function.iterate_add_apply,hp]
  rcases q with ⟨src,tag⟩
  cases src
  · simp only [Bool.false_eq_true, ↓reduceIte,sourceWord] at *
    rw [callA]
    simpa [flip,Option.bind,List.reverse_append,List.append_assoc] using advance_step t i a b (a.reverse++(bits3 tag).reverse++r)
  · simp only [↓reduceIte,sourceWord] at *
    rw [callB]
    simpa [flip,Option.bind,List.reverse_append,List.append_assoc] using advance_step t i a b (b.reverse++(bits3 tag).reverse++r)

lemma instr_at_prefix (t pre : Template) (q : Instruction) (tail : Template)
    (ht : t=pre++q::tail) (i : Cursor t) (hi : i.val=pre.length) : instr t i=q := by
  simp [instr,ht,hi,List.getElem?_append_right]

theorem suffix_run (t suffix : Template) :
    ∀ (pre : Template) (ht : t=pre++suffix) (i : Cursor t) (hi : i.val=pre.length)
      (a b r : List Bool),
    (flip bind (TM2.step (program t)))^[cost suffix a b+1]
      (some (cfg (some .phase) (none,i) a b [] r)) =
      some (cfg none (none,zero t) a b [] ((stream suffix a b).reverse++r)) := by
  induction suffix with
  | nil =>
    intro pre ht i hi a b r
    have he : i.val=t.length := by simpa [ht] using hi
    simpa [flip,Option.bind,cost,stream] using phase_end t i he a b r
  | cons q tail ih =>
    intro pre ht i hi a b r
    have hil : i.val<t.length := by simp [ht,hi]
    have hq := instr_at_prefix t pre q tail ht i hi
    have hp := endpoint_run t i q hil hq a b r
    have ht' : t=(pre++[q])++tail := by simpa [List.append_assoc] using ht
    have hn : (next i).val=(pre++[q]).length := by
      have hm : i.val+1<t.length+1 := by omega
      change (i.val+1) % (t.length+1)=(pre++[q]).length
      rw [Nat.mod_eq_of_lt hm]
      simp [hi]
    have hh := ih (pre++[q]) ht' (next i) hn a b ((bits3 q.2++sourceWord q.1 a b).reverse++r)
    have hc : cost (q::tail) a b+1=(cost tail a b+1)+(2*(sourceWord q.1 a b).length+4) := by
      simp [cost]; omega
    rw [hc,Function.iterate_add_apply,hp]
    simpa [stream,List.reverse_append,List.append_assoc] using hh

def startCfg (t : Template) (a b r : List Bool) : Cfg t :=
  cfg (some .phase) (none,zero t) a b [] r
def endCfg (t : Template) (a b r : List Bool) : Cfg t :=
  cfg none (none,zero t) a b [] ((stream t a b).reverse++r)

theorem template_run (t : Template) (a b r : List Bool) :
    (flip bind (TM2.step (program t)))^[cost t a b+1]
      (some (startCfg t a b r)) = some (endCfg t a b r) :=
  suffix_run t t [] (by simp) (zero t) rfl a b r

def template_evals (t : Template) (a b r : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program t)) (startCfg t a b r)
      (some (endCfg t a b r)) (cost t a b+1) where
  steps := cost t a b+1
  evals_in_steps := template_run t a b r
  steps_le_m := le_rfl

lemma finite_alphabets (t : Template) : ∀ j, Finite ((machine t).Γ j) := by
  intro j; change Finite Bool; infer_instance
lemma finite_labels (t : Template) : Finite (machine t).Λ := by change Finite Label; infer_instance
lemma finite_state (t : Template) : Finite (machine t).σ := by change Finite (State t); infer_instance
lemma final_stacks (t : Template) (a b r : List Bool) :
    (endCfg t a b r).stk .A=a ∧ (endCfg t a b r).stk .B=b ∧
    (endCfg t a b r).stk .temp=[] ∧ (endCfg t a b r).stk .output=(stream t a b).reverse++r :=
  ⟨rfl,rfl,rfl,rfl⟩
lemma final_control (t : Template) (a b r : List Bool) :
    (endCfg t a b r).l=none ∧ (endCfg t a b r).var=(none,zero t) := ⟨rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.TemplateMachine

namespace PEqualNP.Outside.L_lib_895_aux.BlockMachine
open Turing
inductive Stack where | A | B | N | temp | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.A,.B,.N,.temp,.output] (by intro k; cases k <;> simp)
inductive Label where | loop | afterClear | afterCopy | afterZero | afterCarryB | afterTemplate | clear | copyDup | copyRest | copyBack | zeroDup | zeroRest | carryA0 | carryA1 | carryB0 | carryB1 | tplDupA | tplRestA | tplDupB | tplRestB | tplPhase | tplAdvance deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.loop,.afterClear,.afterCopy,.afterZero,.afterCarryB,.afterTemplate,.clear,.copyDup,.copyRest,.copyBack,.zeroDup,.zeroRest,.carryA0,.carryA1,.carryB0,.carryB1,.tplDupA,.tplRestA,.tplDupB,.tplRestB,.tplPhase,.tplAdvance] (by intro l; cases l <;> simp)

def encksClear : Unit → Stack
  | _ => .B
def decksClear : Stack → Option (Unit)
  | .B => some () | _ => none
def ksClear : Stack ≃ Unit ⊕ {j // decksClear j=none} :=
  CallLayout.optionSplit encksClear decksClear
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [encksClear,decksClear])

def enclsClear : Unit → Label
  | _ => .clear
def declsClear : Label → Option (Unit)
  | .clear => some () | _ => none
def lsClear : Label ≃ Unit ⊕ {j // declsClear j=none} :=
  CallLayout.optionSplit enclsClear declsClear
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [enclsClear,declsClear])

def encksCopy : Copy.Stack → Stack
  | .A => .A | .B => .B | .C => .temp
def decksCopy : Stack → Option (Copy.Stack)
  | .A => some .A | .B => some .B | .temp => some .C | _ => none
def ksCopy : Stack ≃ Copy.Stack ⊕ {j // decksCopy j=none} :=
  CallLayout.optionSplit encksCopy decksCopy
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [encksCopy,decksCopy])

def enclsCopy : Copy.Label → Label
  | .duplicate => .copyDup | .restore => .copyRest | .copyBack => .copyBack
def declsCopy : Label → Option (Copy.Label)
  | .copyDup => some .duplicate | .copyRest => some .restore | .copyBack => some .copyBack | _ => none
def lsCopy : Label ≃ Copy.Label ⊕ {j // declsCopy j=none} :=
  CallLayout.optionSplit enclsCopy declsCopy
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [enclsCopy,declsCopy])

def encksZero : ZeroCopy.Stack → Stack
  | .source => .A | .temp => .temp | .output => .B
def decksZero : Stack → Option (ZeroCopy.Stack)
  | .A => some .source | .temp => some .temp | .B => some .output | _ => none
def ksZero : Stack ≃ ZeroCopy.Stack ⊕ {j // decksZero j=none} :=
  CallLayout.optionSplit encksZero decksZero
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [encksZero,decksZero])

def enclsZero : ZeroCopy.Label → Label
  | .duplicate => .zeroDup | .restore => .zeroRest
def declsZero : Label → Option (ZeroCopy.Label)
  | .zeroDup => some .duplicate | .zeroRest => some .restore | _ => none
def lsZero : Label ≃ ZeroCopy.Label ⊕ {j // declsZero j=none} :=
  CallLayout.optionSplit enclsZero declsZero
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [enclsZero,declsZero])

def encksCarryA : Fin 2 → Stack
  | 0 => .A | _ => .temp
def decksCarryA : Stack → Option (Fin 2)
  | .A => some 0 | .temp => some 1 | _ => none
def ksCarryA : Stack ≃ Fin 2 ⊕ {j // decksCarryA j=none} :=
  CallLayout.optionSplit encksCarryA decksCarryA
    (by intro k; fin_cases k <;> rfl)
    (by intro j k h; cases j <;> fin_cases k <;> simp_all [encksCarryA,decksCarryA])

def enclsCarryA : Fin 2 → Label
  | 0 => .carryA0 | _ => .carryA1
def declsCarryA : Label → Option (Fin 2)
  | .carryA0 => some 0 | .carryA1 => some 1 | _ => none
def lsCarryA : Label ≃ Fin 2 ⊕ {j // declsCarryA j=none} :=
  CallLayout.optionSplit enclsCarryA declsCarryA
    (by intro k; fin_cases k <;> rfl)
    (by intro j k h; cases j <;> fin_cases k <;> simp_all [enclsCarryA,declsCarryA])

def encksCarryB : Fin 2 → Stack
  | 0 => .B | _ => .temp
def decksCarryB : Stack → Option (Fin 2)
  | .B => some 0 | .temp => some 1 | _ => none
def ksCarryB : Stack ≃ Fin 2 ⊕ {j // decksCarryB j=none} :=
  CallLayout.optionSplit encksCarryB decksCarryB
    (by intro k; fin_cases k <;> rfl)
    (by intro j k h; cases j <;> fin_cases k <;> simp_all [encksCarryB,decksCarryB])

def enclsCarryB : Fin 2 → Label
  | 0 => .carryB0 | _ => .carryB1
def declsCarryB : Label → Option (Fin 2)
  | .carryB0 => some 0 | .carryB1 => some 1 | _ => none
def lsCarryB : Label ≃ Fin 2 ⊕ {j // declsCarryB j=none} :=
  CallLayout.optionSplit enclsCarryB declsCarryB
    (by intro k; fin_cases k <;> rfl)
    (by intro j k h; cases j <;> fin_cases k <;> simp_all [enclsCarryB,declsCarryB])

def encksTpl : TemplateMachine.Stack → Stack
  | .A => .A | .B => .B | .temp => .temp | .output => .output
def decksTpl : Stack → Option (TemplateMachine.Stack)
  | .A => some .A | .B => some .B | .temp => some .temp | .output => some .output | _ => none
def ksTpl : Stack ≃ TemplateMachine.Stack ⊕ {j // decksTpl j=none} :=
  CallLayout.optionSplit encksTpl decksTpl
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [encksTpl,decksTpl])

def enclsTpl : TemplateMachine.Label → Label
  | .dupA => .tplDupA | .restA => .tplRestA | .dupB => .tplDupB | .restB => .tplRestB | .phase => .tplPhase | .advance => .tplAdvance
def declsTpl : Label → Option (TemplateMachine.Label)
  | .tplDupA => some .dupA | .tplRestA => some .restA | .tplDupB => some .dupB | .tplRestB => some .restB | .tplPhase => some .phase | .tplAdvance => some .advance | _ => none
def lsTpl : Label ≃ TemplateMachine.Label ⊕ {j // declsTpl j=none} :=
  CallLayout.optionSplit enclsTpl declsTpl
    (by intro k; cases k <;> rfl)
    (by intro j k h; cases j <;> cases k <;> simp_all [enclsTpl,declsTpl])

abbrev Reg (t : TemplateMachine.Template) := Bool × (Option Bool × (TemplateMachine.Cursor t × Bool))
abbrev Cfg (t : TemplateMachine.Template) := TM2.Cfg (fun _ : Stack => Bool) Label (Reg t)
def clean (t : TemplateMachine.Template) : Reg t := (false,(none,(TemplateMachine.zero t,false)))
def optState (t : TemplateMachine.Template) : Reg t ≃ Option Bool × (Bool × (TemplateMachine.Cursor t × Bool)) where
  toFun r := (r.2.1,(r.1,r.2.2))
  invFun r := (r.2.1,(r.1,r.2.2))
  left_inv r := rfl
  right_inv r := rfl
def tplState (t : TemplateMachine.Template) : Reg t ≃ (Option Bool × TemplateMachine.Cursor t) × (Bool × Bool) where
  toFun r := ((r.2.1,r.2.2.1),(r.1,r.2.2.2))
  invFun r := (r.2.1,(r.1.1,(r.1.2,r.2.2)))
  left_inv r := rfl
  right_inv r := rfl

def stk (a b n tmp r : List Bool) : Stack → List Bool
  | .A => a | .B => b | .N => n | .temp => tmp | .output => r
def cfg {t : TemplateMachine.Template} (l : Option Label) (s : Reg t) (a b n tmp r : List Bool) : Cfg t :=
  ⟨l,s,stk a b n tmp r⟩

def retClear : {l // declsClear l=none} := ⟨.afterClear,rfl⟩
def retCopy : {l // declsCopy l=none} := ⟨.afterCopy,rfl⟩
def retZero : {l // declsZero l=none} := ⟨.afterZero,rfl⟩
def retCarryB : {l // declsCarryB l=none} := ⟨.afterCarryB,rfl⟩
def retCarryA : {l // declsCarryA l=none} := ⟨.loop,rfl⟩
def retTpl : {l // declsTpl l=none} := ⟨.afterTemplate,rfl⟩

def program (t : TemplateMachine.Template) : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Reg t)
  | .loop => .pop .N (fun r o => (r.1,(o,r.2.2)))
      (.branch (fun r => r.2.1.isSome)
        (.peek .N (fun _ o => (false,(none,(TemplateMachine.zero t,!o.isSome))))
          (.goto fun _ => .clear))
        (.load (fun _ => clean t) .halt))
  | .afterClear => .branch (fun r => r.2.2.2)
      (.goto fun _ => .zeroDup) (.goto fun _ => .copyDup)
  | .afterCopy => .goto fun _ => .carryB0
  | .afterZero => .goto fun _ => .tplPhase
  | .afterCarryB => .goto fun _ => .tplPhase
  | .afterTemplate => .goto fun _ => .carryA0
  | .clear => BoolCall.trStmt ksClear lsClear (Equiv.refl _) retClear (Clear.prog ())
  | .copyDup => BoolCall.trStmt ksCopy lsCopy (optState t) retCopy (Copy.program .duplicate)
  | .copyRest => BoolCall.trStmt ksCopy lsCopy (optState t) retCopy (Copy.program .restore)
  | .copyBack => BoolCall.trStmt ksCopy lsCopy (optState t) retCopy (Copy.program .copyBack)
  | .zeroDup => BoolCall.trStmt ksZero lsZero (optState t) retZero (ZeroCopy.program .duplicate)
  | .zeroRest => BoolCall.trStmt ksZero lsZero (optState t) retZero (ZeroCopy.program .restore)
  | .carryA0 => BoolCall.trStmt ksCarryA lsCarryA (optState t) retCarryA (Carry.program 0)
  | .carryA1 => BoolCall.trStmt ksCarryA lsCarryA (optState t) retCarryA (Carry.program 1)
  | .carryB0 => BoolCall.trStmt ksCarryB lsCarryB (optState t) retCarryB (Carry.program 0)
  | .carryB1 => BoolCall.trStmt ksCarryB lsCarryB (optState t) retCarryB (Carry.program 1)
  | .tplDupA => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .dupA)
  | .tplRestA => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .restA)
  | .tplDupB => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .dupB)
  | .tplRestB => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .restB)
  | .tplPhase => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .phase)
  | .tplAdvance => BoolCall.trStmt ksTpl lsTpl (tplState t) retTpl (TemplateMachine.program t .advance)

def machine (t : TemplateMachine.Template) : FinTM2 where
  K := Stack
  k₀ := .A
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .loop
  σ := Reg t
  initialState := clean t
  m := program t

lemma finite_alphabets (t : TemplateMachine.Template) : ∀ j, Finite ((machine t).Γ j) := by
  intro j; change Finite Bool; infer_instance
end PEqualNP.Outside.L_lib_895_aux.BlockMachine

namespace PEqualNP.Outside.L_lib_895_aux.BlockMachine
open Turing
abbrev Tpl := TemplateMachine.Template
def regs (t : Tpl) (last : Bool) : Reg t := (false,(none,(TemplateMachine.zero t,last)))

lemma callClear (t : Tpl) (last : Bool) (a b n r : List Bool) :
    (flip bind (TM2.step (program t)))^[b.length+1]
      (some (cfg (some .clear) (regs t last) a b n [] r)) =
        some (cfg (some .afterClear) (regs t last) a [] n [] r) := by
  let extra := fun j : {j // decksClear j=none} => stk a b n [] r j.val
  have hs : BoolCall.liftCfg ksClear lsClear (Equiv.refl _) retClear (none,(TemplateMachine.zero t,last)) extra (Clear.cfg (some ()) b) =
      cfg (some .clear) (regs t last) a b n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Clear.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksClear lsClear (Equiv.refl _) retClear (none,(TemplateMachine.zero t,last)) extra (Clear.cfg none []) =
      cfg (some .afterClear) (regs t last) a [] n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Clear.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksClear lsClear (Equiv.refl _) retClear (none,(TemplateMachine.zero t,last)) extra
    (Clear.prog) (program t) (by intro l; cases l; rfl) _ _ _ (Clear.clear_run b)
  rw [hs,he] at hh
  exact hh

lemma callCopy (t : Tpl) (last : Bool) (a b n r : List Bool) :
    (flip bind (TM2.step (program t)))^[3*a.length+3]
      (some (cfg (some .copyDup) (regs t last) a [] n [] r)) =
        some (cfg (some .afterCopy) (regs t last) a a n [] r) := by
  let extra := fun j : {j // decksCopy j=none} => stk a [] n [] r j.val
  have hs : BoolCall.liftCfg ksCopy lsCopy (optState t) retCopy (false,(TemplateMachine.zero t,last)) extra (Copy.startCfg a) =
      cfg (some .copyDup) (regs t last) a [] n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Copy.startCfg,Copy.endCfg,Copy.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksCopy lsCopy (optState t) retCopy (false,(TemplateMachine.zero t,last)) extra (Copy.endCfg a) =
      cfg (some .afterCopy) (regs t last) a a n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Copy.startCfg,Copy.endCfg,Copy.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksCopy lsCopy (optState t) retCopy (false,(TemplateMachine.zero t,last)) extra
    (Copy.program) (program t) (by intro l; cases l <;> rfl) _ _ _ (Copy.copy_run a)
  rw [hs,he] at hh
  exact hh

lemma callZero (t : Tpl) (last : Bool) (a b n r : List Bool) :
    (flip bind (TM2.step (program t)))^[2*a.length+2]
      (some (cfg (some .zeroDup) (regs t last) a [] n [] r)) =
        some (cfg (some .afterZero) (regs t last) a (List.replicate a.length false) n [] r) := by
  let extra := fun j : {j // decksZero j=none} => stk a [] n [] r j.val
  have hs : BoolCall.liftCfg ksZero lsZero (optState t) retZero (false,(TemplateMachine.zero t,last)) extra (ZeroCopy.startCfg a []) =
      cfg (some .zeroDup) (regs t last) a [] n [] r := by
    dsimp [BoolCall.liftCfg,cfg,ZeroCopy.startCfg,ZeroCopy.endCfg,ZeroCopy.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksZero lsZero (optState t) retZero (false,(TemplateMachine.zero t,last)) extra (ZeroCopy.endCfg a []) =
      cfg (some .afterZero) (regs t last) a (List.replicate a.length false) n [] r := by
    dsimp [BoolCall.liftCfg,cfg,ZeroCopy.startCfg,ZeroCopy.endCfg,ZeroCopy.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksZero lsZero (optState t) retZero (false,(TemplateMachine.zero t,last)) extra
    (ZeroCopy.program) (program t) (by intro l; cases l <;> rfl) _ _ _ (ZeroCopy.emit_run a [])
  rw [hs,he] at hh
  exact hh

lemma callTpl (t : Tpl) (last : Bool) (a b n r : List Bool) :
    (flip bind (TM2.step (program t)))^[TemplateMachine.cost t a b+1]
      (some (cfg (some .tplPhase) (regs t last) a b n [] r)) =
        some (cfg (some .afterTemplate) (regs t last) a b n [] ((TemplateMachine.stream t a b).reverse++r)) := by
  let extra := fun j : {j // decksTpl j=none} => stk a b n [] r j.val
  have hs : BoolCall.liftCfg ksTpl lsTpl (tplState t) retTpl (false,last) extra (TemplateMachine.startCfg t a b r) =
      cfg (some .tplPhase) (regs t last) a b n [] r := by
    dsimp [BoolCall.liftCfg,cfg,TemplateMachine.startCfg,TemplateMachine.endCfg,TemplateMachine.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksTpl lsTpl (tplState t) retTpl (false,last) extra (TemplateMachine.endCfg t a b r) =
      cfg (some .afterTemplate) (regs t last) a b n [] ((TemplateMachine.stream t a b).reverse++r) := by
    dsimp [BoolCall.liftCfg,cfg,TemplateMachine.startCfg,TemplateMachine.endCfg,TemplateMachine.cfg,optState,tplState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksTpl lsTpl (tplState t) retTpl (false,last) extra
    (TemplateMachine.program t) (program t) (by intro l; cases l <;> rfl) _ _ _ (TemplateMachine.template_run t a b r)
  rw [hs,he] at hh
  exact hh

lemma callCarryA (t : Tpl) (last : Bool) (a b n r : List Bool) :
    ∃ u ≤ 2*a.length+2, (flip bind (TM2.step (program t)))^[u]
      (some (cfg (some .carryA0) (regs t last) a b n [] r)) =
        some (cfg (some .loop) (regs t last) (growInc a) b n [] r) := by
  obtain ⟨u,hu,hr⟩ := Carry.increment_run a
  refine ⟨u,hu,?_⟩
  let extra := fun j : {j // decksCarryA j=none} => stk a b n [] r j.val
  have hs : BoolCall.liftCfg ksCarryA lsCarryA (optState t) retCarryA (false,(TemplateMachine.zero t,last)) extra (Carry.cfg (some 0) a []) =
      cfg (some .carryA0) (regs t last) a b n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Carry.cfg,optState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksCarryA lsCarryA (optState t) retCarryA (false,(TemplateMachine.zero t,last)) extra (Carry.cfg none (growInc a) []) =
      cfg (some .loop) (regs t last) (growInc a) b n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Carry.cfg,optState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksCarryA lsCarryA (optState t) retCarryA (false,(TemplateMachine.zero t,last)) extra
    Carry.program (program t) (by intro l; fin_cases l <;> rfl) u _ _ hr
  rw [hs,he] at hh
  exact hh

lemma callCarryB (t : Tpl) (last : Bool) (a b n r : List Bool) :
    ∃ u ≤ 2*b.length+2, (flip bind (TM2.step (program t)))^[u]
      (some (cfg (some .carryB0) (regs t last) a b n [] r)) =
        some (cfg (some .afterCarryB) (regs t last) a (growInc b) n [] r) := by
  obtain ⟨u,hu,hr⟩ := Carry.increment_run b
  refine ⟨u,hu,?_⟩
  let extra := fun j : {j // decksCarryB j=none} => stk a b n [] r j.val
  have hs : BoolCall.liftCfg ksCarryB lsCarryB (optState t) retCarryB (false,(TemplateMachine.zero t,last)) extra (Carry.cfg (some 0) b []) =
      cfg (some .carryB0) (regs t last) a b n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Carry.cfg,optState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have he : BoolCall.liftCfg ksCarryB lsCarryB (optState t) retCarryB (false,(TemplateMachine.zero t,last)) extra (Carry.cfg none (growInc b) []) =
      cfg (some .afterCarryB) (regs t last) a (growInc b) n [] r := by
    dsimp [BoolCall.liftCfg,cfg,Carry.cfg,optState,regs]
    congr 1
    funext k; cases k <;> first | rfl | exact List.append_nil _
  have hh := BoolCall.run_lift ksCarryB lsCarryB (optState t) retCarryB (false,(TemplateMachine.zero t,last)) extra
    Carry.program (program t) (by intro l; fin_cases l <;> rfl) u _ _ hr
  rw [hs,he] at hh
  exact hh

end PEqualNP.Outside.L_lib_895_aux.BlockMachine

namespace PEqualNP.Outside.L_lib_895_aux.BlockMachine
open Turing
abbrev Run (t : Tpl) (u : Nat) (c d : Cfg t) : Prop :=
  (flip bind (TM2.step (program t)))^[u] (some c)=some d
lemma run_one (t : Tpl) (c d : Cfg t) (h : TM2.step (program t) c=some d) : Run t 1 c d := h
lemma run_comp (t : Tpl) {u v : Nat} {a b c : Cfg t}
    (h : Run t u a b) (h' : Run t v b c) : Run t (u+v) a c := by
  unfold Run at *
  rw [Nat.add_comm u v,Function.iterate_add_apply,h,h']
lemma setN (a b n n' tmp r : List Bool) :
    Function.update (stk a b n tmp r) .N n'=stk a b n' tmp r := by
  funext k; cases k <;> simp [stk]
lemma loop_cons (t : Tpl) (s : Reg t) (x : Bool) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .loop) s a b (x::n) [] r)=
      some (cfg (some .clear) (regs t n.isEmpty) a b n [] r) := by
  cases n <;> simp [TM2.step,program,TM2.stepAux,cfg,stk,regs,setN]
lemma loop_nil (t : Tpl) (s : Reg t) (a b r : List Bool) :
    TM2.step (program t) (cfg (some .loop) s a b [] [] r)=
      some (cfg none (clean t) a b [] [] r) := by
  simp [TM2.step,program,TM2.stepAux,cfg,stk,regs,setN]
lemma branch_zero (t : Tpl) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterClear) (regs t true) a b n [] r)=
      some (cfg (some .zeroDup) (regs t true) a b n [] r) := rfl
lemma branch_copy (t : Tpl) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterClear) (regs t false) a b n [] r)=
      some (cfg (some .copyDup) (regs t false) a b n [] r) := rfl
lemma goto_carryB (t : Tpl) (last : Bool) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterCopy) (regs t last) a b n [] r)=
      some (cfg (some .carryB0) (regs t last) a b n [] r) := rfl
lemma goto_template_zero (t : Tpl) (last : Bool) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterZero) (regs t last) a b n [] r)=
      some (cfg (some .tplPhase) (regs t last) a b n [] r) := rfl
lemma goto_template_carry (t : Tpl) (last : Bool) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterCarryB) (regs t last) a b n [] r)=
      some (cfg (some .tplPhase) (regs t last) a b n [] r) := rfl
lemma goto_carryA (t : Tpl) (last : Bool) (a b n r : List Bool) :
    TM2.step (program t) (cfg (some .afterTemplate) (regs t last) a b n [] r)=
      some (cfg (some .carryA0) (regs t last) a b n [] r) := rfl

theorem iteration_nonlast (t : Tpl) (s : Reg t) (x : Bool) (a b n r : List Bool) (hn : n≠[]) :
    ∃ u ≤ b.length+7*a.length+TemplateMachine.cost t a (growInc a)+14,
      Run t u (cfg (some .loop) s a b (x::n) [] r)
        (cfg (some .loop) (regs t false) (growInc a) (growInc a) n []
          ((TemplateMachine.stream t a (growInc a)).reverse++r)) := by
  have hn' : n.isEmpty=false := by cases n <;> simp_all
  have h0 := run_one t _ _ (loop_cons t s x a b n r)
  rw [hn'] at h0
  have h1 := run_comp t h0 (callClear t false a b n r)
  have h2 := run_comp t h1 (run_one t _ _ (branch_copy t a [] n r))
  have h3 := run_comp t h2 (callCopy t false a [] n r)
  have h4 := run_comp t h3 (run_one t _ _ (goto_carryB t false a a n r))
  obtain ⟨uB,huB,hB⟩ := callCarryB t false a a n r
  have h5 := run_comp t h4 hB
  have h6 := run_comp t h5 (run_one t _ _ (goto_template_carry t false a (growInc a) n r))
  have h7 := run_comp t h6 (callTpl t false a (growInc a) n r)
  have h8 := run_comp t h7 (run_one t _ _ (goto_carryA t false a (growInc a) n
    ((TemplateMachine.stream t a (growInc a)).reverse++r)))
  obtain ⟨uA,huA,hA⟩ := callCarryA t false a (growInc a) n
    ((TemplateMachine.stream t a (growInc a)).reverse++r)
  have whole := run_comp t h8 hA
  exact ⟨_,by omega,whole⟩

theorem iteration_last (t : Tpl) (s : Reg t) (x : Bool) (a b r : List Bool) :
    ∃ u ≤ b.length+4*a.length+TemplateMachine.cost t a (List.replicate a.length false)+10,
      Run t u (cfg (some .loop) s a b [x] [] r)
        (cfg (some .loop) (regs t true) (growInc a) (List.replicate a.length false) [] []
          ((TemplateMachine.stream t a (List.replicate a.length false)).reverse++r)) := by
  have h0 := run_one t _ _ (loop_cons t s x a b [] r)
  have h1 := run_comp t h0 (callClear t true a b [] r)
  have h2 := run_comp t h1 (run_one t _ _ (branch_zero t a [] [] r))
  have h3 := run_comp t h2 (callZero t true a [] [] r)
  have h4 := run_comp t h3 (run_one t _ _ (goto_template_zero t true a (List.replicate a.length false) [] r))
  have h5 := run_comp t h4 (callTpl t true a (List.replicate a.length false) [] r)
  have h6 := run_comp t h5 (run_one t _ _ (goto_carryA t true a (List.replicate a.length false) []
    ((TemplateMachine.stream t a (List.replicate a.length false)).reverse++r)))
  obtain ⟨uA,huA,hA⟩ := callCarryA t true a (List.replicate a.length false) []
    ((TemplateMachine.stream t a (List.replicate a.length false)).reverse++r)
  have whole := run_comp t h6 hA
  exact ⟨_,by omega,whole⟩
end PEqualNP.Outside.L_lib_895_aux.BlockMachine

namespace PEqualNP.Outside.L_lib_895_aux

lemma log2_eight_mul_add_one (n : Nat) (hn : 2≤n) :
    (8*n+1).log2 = n.log2+3 := by
  have h0 : n≠0 := by omega
  have hlo := Nat.log2_self_le h0
  have hhi : n < 2^(n.log2+1) := Nat.lt_log2_self
  apply (Nat.log2_eq_iff (show 8*n+1≠0 by omega)).mpr
  constructor
  · rw [pow_add]
    norm_num
    omega
  · rw [show n.log2+3+1=(n.log2+1)+3 by omega,pow_add]
    norm_num
    omega

theorem output_width_exact (n : Nat) (hn : 2≤n) : width (8*n+1) = width n+3 := by
  unfold width
  rw [log2_eight_mul_add_one n hn]

theorem endpoint_bits (n i tag : Nat) (hn : 2≤n) (ht : tag<8) :
    bits (width (8*n+1)) (8*i+tag) = bits 3 tag ++ bits (width n) i := by
  rw [output_width_exact n hn]
  exact bits_shift_tag (width n) i tag ht

lemma flag_even_endpoint_bits (n i c : Nat) (hn : 2≤n) (hc : c<3) :
    bits (width (8*n+1)) (8*i+2+2*c) = bits 3 (2+2*c) ++ bits (width n) i := by
  rw [show 8*i+2+2*c=8*i+(2+2*c) by omega]
  exact endpoint_bits n i (2+2*c) hn (by omega)

lemma flag_odd_endpoint_bits (n i c : Nat) (hn : 2≤n) (hc : c<3) :
    bits (width (8*n+1)) (8*i+3+2*c) = bits 3 (3+2*c) ++ bits (width n) i := by
  rw [show 8*i+3+2*c=8*i+(3+2*c) by omega]
  exact endpoint_bits n i (3+2*c) hn (by omega)

lemma anchor_endpoint_bits (n i b : Nat) (hn : 2≤n) (hb : b<2) :
    bits (width (8*n+1)) (8*i+b) = bits 3 b ++ bits (width n) i :=
  endpoint_bits n i b hn (by omega)

lemma successor_endpoint_bits (n i j : Nat) (hn : 2≤n) (hj : j<4) :
    bits (width (8*n+1)) (8*((i+1) % n)+j) =
      bits 3 j ++ bits (width n) ((i+1) % n) :=
  endpoint_bits n ((i+1) % n) j hn (by omega)

lemma flag_words (n i c : Nat) (hn : 2≤n) (hc : c<3) :
    (PEqualNP.Outside.L_lib_895_aux.Comb.flag i c).flatMap (bits (width (8*n+1))) =
      bits 3 (2+2*c) ++ bits (width n) i ++ bits 3 (3+2*c) ++ bits (width n) i := by
  simp only [PEqualNP.Outside.L_lib_895_aux.Comb.flag,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [flag_even_endpoint_bits n i c hn hc,flag_odd_endpoint_bits n i c hn hc]
  simp only [List.append_assoc]

lemma input_width_bound (n : Nat) (B : List Ban) : width n ≤ (enc n B).length+1 := by
  have hw := Nat.log2_le_self n
  have hs := inputEncoding_size n B
  rw [←enc_eq_inputEncoding n B] at hs
  unfold width
  omega

lemma primitive_work_quadratic (L n w out : Nat) (hn : n≤L) (hw : w≤L+1)
    (ho : out≤1000*(L+1)^2) :
    L*w+n*w+out+L+n+1 ≤ 1005*(L+1)^2 := by
  have h1 := Nat.mul_le_mul_left L hw
  have h2 := Nat.mul_le_mul hn hw
  nlinarith

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux.TemplateSpec
open PEqualNP.Outside.L_lib_895_aux

abbrev Instruction := Bool × Fin 8

def stream (template : List Instruction) (a b : List Bool) : List Bool :=
  template.flatMap (fun e => bits 3 e.2.val ++ if e.1 then b else a)

def blockTemplate : List Instruction := [(false,0), (false,2), (false,4), (false,6), (false,0), (false,2), (false,3), (true,0), (false,0), (false,2), (false,3), (true,1), (false,0), (false,2), (false,3), (true,2), (false,0), (false,2), (false,3), (true,3), (false,1), (false,2), (false,3), (true,0), (false,1), (false,2), (false,3), (true,1), (false,1), (false,2), (false,3), (true,2), (false,1), (false,2), (false,3), (true,3), (false,0), (false,4), (false,5), (true,0), (false,0), (false,4), (false,5), (true,1), (false,0), (false,4), (false,5), (true,2), (false,0), (false,4), (false,5), (true,3), (false,1), (false,4), (false,5), (true,0), (false,1), (false,4), (false,5), (true,1), (false,1), (false,4), (false,5), (true,2), (false,1), (false,4), (false,5), (true,3), (false,0), (false,6), (false,7), (true,0), (false,0), (false,6), (false,7), (true,1), (false,0), (false,6), (false,7), (true,2), (false,0), (false,6), (false,7), (true,3), (false,1), (false,6), (false,7), (true,0), (false,1), (false,6), (false,7), (true,1), (false,1), (false,6), (false,7), (true,2), (false,1), (false,6), (false,7), (true,3)]

lemma blockTemplate_length : blockTemplate.length = 100 := by decide

set_option maxHeartbeats 1000000 in
lemma block_stream (n i : Nat) (hn : 2 ≤ n) :
    (PEqualNP.Outside.L_lib_895_aux.Comb.block n i).flatMap
      (fun row => row.flatMap (bits (width (8*n+1)))) =
    stream blockTemplate (bits (width n) i) (bits (width n) ((i+1) % n)) := by
  have he (v t : Nat) (ht : t < 8) :
      bits (width (8*n+1)) (8*v+t) = bits 3 t ++ bits (width n) v :=
    endpoint_bits n v t hn ht
  have hz (v : Nat) :
      bits (width (8*n+1)) (8*v) = bits 3 0 ++ bits (width n) v := by
    simpa using he v 0 (by decide)
  simp [PEqualNP.Outside.L_lib_895_aux.Comb.block,PEqualNP.Outside.L_lib_895_aux.Comb.flag,
    blockTemplate,stream,List.range_succ,he,hz,List.append_assoc,Nat.add_assoc]

def banTemplate (c d : Fin 3) : List Instruction :=
  [(false,⟨2+2*c.val,by omega⟩),(false,⟨3+2*c.val,by omega⟩),
   (true,⟨2+2*d.val,by omega⟩),(true,⟨3+2*d.val,by omega⟩)]

lemma banTemplate_length (c d : Fin 3) : (banTemplate c d).length = 4 := rfl

lemma ban_stream (n i j : Nat) (c d : Fin 3) (hn : 2 ≤ n) :
    (PEqualNP.Outside.L_lib_895_aux.Comb.flag i c.val ++
      PEqualNP.Outside.L_lib_895_aux.Comb.flag j d.val).flatMap (bits (width (8*n+1))) =
    stream (banTemplate c d) (bits (width n) i) (bits (width n) j) := by
  rw [List.flatMap_append,flag_words n i c.val hn c.isLt,flag_words n j d.val hn d.isLt]
  simp [banTemplate,stream,List.append_assoc]

end PEqualNP.Outside.L_lib_895_aux.TemplateSpec

namespace PEqualNP.Outside.L_lib_895_aux.TemplateReady
open PEqualNP.Outside.L_lib_895_aux

lemma stream_eq (t : List (Bool × Fin 8)) (a b : List Bool) :
    TemplateMachine.stream t a b = TemplateSpec.stream t a b := rfl

lemma cost_equal_width (t : List (Bool × Fin 8)) (a b : List Bool) (w : Nat)
    (ha : a.length=w) (hb : b.length=w) :
    TemplateMachine.cost t a b = t.length*(2*w+4) := by
  induction t with
  | nil => simp [TemplateMachine.cost]
  | cons q t ih =>
    rcases q with ⟨s,c⟩
    cases s <;> simp_all [TemplateMachine.cost,TemplateMachine.sourceWord,Nat.add_mul,Nat.add_comm]

def block_evals (n i : Nat) (R : List Bool) (hn : 2 ≤ n) :
    StateTransition.EvalsToInTime (Turing.TM2.step (TemplateMachine.program TemplateSpec.blockTemplate))
      (TemplateMachine.startCfg TemplateSpec.blockTemplate (bits (width n) i) (bits (width n) ((i+1) % n)) R)
      (some (TemplateMachine.cfg none (none,TemplateMachine.zero TemplateSpec.blockTemplate)
        (bits (width n) i) (bits (width n) ((i+1) % n)) []
        (((PEqualNP.Outside.L_lib_895_aux.Comb.block n i).flatMap
          (fun row => row.flatMap (bits (width (8*n+1))))).reverse++R)))
      (100*(2*width n+4)+1) := by
  have h := TemplateMachine.template_evals TemplateSpec.blockTemplate
    (bits (width n) i) (bits (width n) ((i+1) % n)) R
  have hc := cost_equal_width TemplateSpec.blockTemplate
    (bits (width n) i) (bits (width n) ((i+1) % n)) (width n) (bits_length _ _) (bits_length _ _)
  rw [TemplateSpec.blockTemplate_length] at hc
  rw [hc] at h
  unfold TemplateMachine.endCfg at h
  rw [stream_eq,←TemplateSpec.block_stream n i hn] at h
  exact h

def ban_evals (n i j : Nat) (c d : Fin 3) (R : List Bool) (hn : 2 ≤ n) :
    StateTransition.EvalsToInTime (Turing.TM2.step (TemplateMachine.program (TemplateSpec.banTemplate c d)))
      (TemplateMachine.startCfg (TemplateSpec.banTemplate c d) (bits (width n) i) (bits (width n) j) R)
      (some (TemplateMachine.cfg none (none,TemplateMachine.zero (TemplateSpec.banTemplate c d))
        (bits (width n) i) (bits (width n) j) []
        (((PEqualNP.Outside.L_lib_895_aux.Comb.flag i c.val ++ PEqualNP.Outside.L_lib_895_aux.Comb.flag j d.val).flatMap
          (bits (width (8*n+1)))).reverse++R)))
      (4*(2*width n+4)+1) := by
  have h := TemplateMachine.template_evals (TemplateSpec.banTemplate c d)
    (bits (width n) i) (bits (width n) j) R
  have hc := cost_equal_width (TemplateSpec.banTemplate c d)
    (bits (width n) i) (bits (width n) j) (width n) (bits_length _ _) (bits_length _ _)
  rw [TemplateSpec.banTemplate_length] at hc
  rw [hc] at h
  unfold TemplateMachine.endCfg at h
  rw [stream_eq,←TemplateSpec.ban_stream n i j c d hn] at h
  exact h

end PEqualNP.Outside.L_lib_895_aux.TemplateReady

namespace PEqualNP.Outside.L_lib_895_aux

lemma growInc_bits_fixed (w i : Nat) (hi : i+1 < 2^w) :
    growInc (bits w i) = bits w (i+1) := by
  have hval : wordValue (bits w i) = i := wordValue_bits w i (by omega)
  have hlen := growInc_length (bits w i)
  rw [bits_length] at hlen
  have hnot : ¬ w < (growInc (bits w i)).length := by
    intro hlt
    have he := growInc_expands (bits w i) (by simpa only [bits_length] using hlt)
    rw [hval,bits_length] at he
    omega
  have heq : (growInc (bits w i)).length = w := by omega
  have hr := bits_wordValue (growInc (bits w i))
  rw [heq,growInc_value,hval] at hr
  exact hr.symm

lemma growInc_bits_index (n i : Nat) (hi : i<n) :
    growInc (bits (width n) i) = bits (width n) (i+1) := by
  apply growInc_bits_fixed
  have hn : n < 2^(width n) := Nat.lt_log2_self
  omega

lemma bits_zero (w : Nat) : bits w 0 = List.replicate w false := by
  simp [bits]

end PEqualNP.Outside.L_lib_895_aux

namespace PEqualNP.Outside.L_lib_895_aux.BlockMachine
open Turing

def blockBits (n i : Nat) : List Bool :=
  (PEqualNP.Outside.L_lib_895_aux.Comb.block n i).flatMap (fun row => row.flatMap (bits (width (8*n+1))))
def blocksFrom (n : Nat) : Nat → Nat → List Bool
  | _,0 => []
  | i,k+1 => blockBits n i ++ blocksFrom n (i+1) k

theorem blocks_suffix (n : Nat) (hn : 2≤n) (k : Nat) :
    ∀ (i : Nat) (hik : i+k=n) (hk : 0<k) (s : Reg TemplateSpec.blockTemplate)
      (b r : List Bool) (hb : b.length≤width n),
    ∃ u ≤ k*(220*width n+500)+1,
      Run TemplateSpec.blockTemplate u
        (cfg (some .loop) s (bits (width n) i) b (List.replicate k true) [] r)
        (cfg none (clean TemplateSpec.blockTemplate) (bits (width n) n)
          (List.replicate (width n) false) [] [] ((blocksFrom n i k).reverse++r)) := by
  induction k with
  | zero => intro i hik hk; omega
  | succ k ih =>
    intro i hik hk s b r hb
    have hi : i<n := by omega
    have hg := growInc_bits_index n i hi
    cases k with
    | zero =>
      have hin : i+1=n := by omega
      obtain ⟨u,hu,hr⟩ := iteration_last TemplateSpec.blockTemplate s true (bits (width n) i) b r
      simp only [bits_length] at hu hr
      rw [hg,hin] at hr
      have hs : TemplateMachine.stream TemplateSpec.blockTemplate (bits (width n) i)
          (List.replicate (width n) false)=blockBits n i := by
        have hh := TemplateSpec.block_stream n i hn
        simpa [blockBits,TemplateReady.stream_eq,hin,bits_zero] using hh.symm
      rw [hs] at hr
      have hc := TemplateReady.cost_equal_width TemplateSpec.blockTemplate (bits (width n) i)
        (List.replicate (width n) false) (width n) (bits_length _ _) (by simp)
      rw [TemplateSpec.blockTemplate_length] at hc
      rw [hc] at hu
      have whole := run_comp TemplateSpec.blockTemplate hr
        (run_one _ _ _ (loop_nil _ _ _ _ _))
      refine ⟨u+1,by nlinarith,?_⟩
      simpa [blocksFrom] using whole
    | succ k =>
      have hin : i+1<n := by omega
      obtain ⟨u,hu,hr⟩ := iteration_nonlast TemplateSpec.blockTemplate s true (bits (width n) i) b
        (List.replicate (k+1) true) r (by simp)
      rw [hg] at hu hr
      simp only [bits_length] at hu
      have hs : TemplateMachine.stream TemplateSpec.blockTemplate (bits (width n) i)
          (bits (width n) (i+1))=blockBits n i := by
        have hh := TemplateSpec.block_stream n i hn
        simpa [blockBits,TemplateReady.stream_eq,Nat.mod_eq_of_lt hin] using hh.symm
      rw [hs] at hr
      have hc := TemplateReady.cost_equal_width TemplateSpec.blockTemplate (bits (width n) i)
        (bits (width n) (i+1)) (width n) (bits_length _ _) (bits_length _ _)
      rw [TemplateSpec.blockTemplate_length] at hc
      rw [hc] at hu
      obtain ⟨v,hv,hvRun⟩ := ih (i+1) (by omega) (by omega)
        (regs TemplateSpec.blockTemplate false) (bits (width n) (i+1)) ((blockBits n i).reverse++r)
        (by simp [bits_length])
      have whole := run_comp TemplateSpec.blockTemplate hr hvRun
      refine ⟨u+v,by nlinarith,?_⟩
      simpa [blocksFrom,List.reverse_append,List.append_assoc,List.replicate_succ] using whole

def startCfg (n : Nat) (r : List Bool) : Cfg TemplateSpec.blockTemplate :=
  cfg (some .loop) (clean TemplateSpec.blockTemplate) (bits (width n) 0) [] (List.replicate n true) [] r
def endCfg (n : Nat) (r : List Bool) : Cfg TemplateSpec.blockTemplate :=
  cfg none (clean TemplateSpec.blockTemplate) (bits (width n) n)
    (List.replicate (width n) false) [] [] ((blocksFrom n 0 n).reverse++r)

set_option maxRecDepth 4096 in
theorem blocks_run (n : Nat) (r : List Bool) (hn : 2≤n) :
    ∃ u ≤ n*(220*width n+500)+10,
      Run TemplateSpec.blockTemplate u (startCfg n r) (endCfg n r) := by
  obtain ⟨u,hu,hr⟩ := blocks_suffix n hn n 0 (by simp) (by omega)
    (clean TemplateSpec.blockTemplate) [] r (by simp)
  exact ⟨u,by omega,hr⟩

noncomputable def blocks_evals (n : Nat) (r : List Bool) (hn : 2≤n) :
    StateTransition.EvalsToInTime (TM2.step (program TemplateSpec.blockTemplate))
      (startCfg n r) (some (endCfg n r)) (n*(220*width n+500)+10) where
  steps := Classical.choose (blocks_run n r hn)
  evals_in_steps := (Classical.choose_spec (blocks_run n r hn)).2
  steps_le_m := (Classical.choose_spec (blocks_run n r hn)).1
end PEqualNP.Outside.L_lib_895_aux.BlockMachine

namespace PEqualNP.Outside.L_lib_895_aux.BlockMachine
open Turing
lemma blocksFrom_range (n i k : Nat) :
    blocksFrom n i k = (List.range' i k).flatMap (blockBits n) := by
  induction k generalizing i with
  | zero => simp [blocksFrom]
  | succ k ih => simp [blocksFrom,List.range'_succ,ih]

def postedBlocks (n : Nat) : List Bool :=
  (PEqualNP.Outside.L_lib_895_aux.Comb.emit n []).flatMap
    (fun row => row.flatMap (bits (width (8*n+1))))

lemma blocksFrom_eq_posted (n : Nat) : blocksFrom n 0 n = postedBlocks n := by
  have hf (xs : List Nat) :
      (xs.flatMap (PEqualNP.Outside.L_lib_895_aux.Comb.block n)).flatMap
        (fun row => row.flatMap (bits (width (8*n+1)))) = xs.flatMap (blockBits n) := by
    induction xs with
    | nil => rfl
    | cons i xs ih => simp [blockBits,List.flatMap_append,ih]
  rw [blocksFrom_range,←List.range_eq_range']
  simpa [postedBlocks,PEqualNP.Outside.L_lib_895_aux.Comb.emit] using (hf (List.range n)).symm

set_option maxRecDepth 4096 in
noncomputable def posted_blocks_evals (n : Nat) (r : List Bool) (hn : 2≤n) :
    StateTransition.EvalsToInTime (TM2.step (program TemplateSpec.blockTemplate))
      (startCfg n r)
      (some (cfg none (clean TemplateSpec.blockTemplate) (bits (width n) n)
        (List.replicate (width n) false) [] [] ((postedBlocks n).reverse++r)))
      (n*(220*width n+500)+10) := by
  have h := blocks_evals n r hn
  unfold endCfg at h
  rw [blocksFrom_eq_posted] at h
  exact h

lemma finite_labels : Finite (machine TemplateSpec.blockTemplate).Λ := by
  change Finite Label; infer_instance
lemma finite_state : Finite (machine TemplateSpec.blockTemplate).σ := by
  change Finite (Reg TemplateSpec.blockTemplate); infer_instance
end PEqualNP.Outside.L_lib_895_aux.BlockMachine

namespace PEqualNP.Outside.L_lib_895_aux.Front
open Turing
abbrev Stack := Prefix.Stack
abbrev BT := TemplateSpec.blockTemplate
abbrev Reg := Prefix.State × BlockMachine.Reg BT
inductive Label where
  | prefixPhase (l : Prefix.Label) | block (l : BlockMachine.Label) | clear
  | afterPrefix | afterBlock | finish
  deriving DecidableEq
def labelEquiv : Label ≃ Prefix.Label ⊕ BlockMachine.Label ⊕ Fin 4 where
  toFun | .prefixPhase l => .inl l | .block l => .inr (.inl l)
        | .clear => .inr (.inr 0) | .afterPrefix => .inr (.inr 1)
        | .afterBlock => .inr (.inr 2) | .finish => .inr (.inr 3)
  invFun | .inl l => .prefixPhase l | .inr (.inl l) => .block l
         | .inr (.inr 0) => .clear | .inr (.inr 1) => .afterPrefix
         | .inr (.inr 2) => .afterBlock | .inr (.inr _) => .finish
  left_inv l := by cases l <;> rfl
  right_inv l := by rcases l with l|l|l; rfl; rfl; fin_cases l <;> rfl
instance : Fintype Label := Fintype.ofEquiv (Prefix.Label ⊕ BlockMachine.Label ⊕ Fin 4) labelEquiv.symm
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label Reg

def ksPrefix := CallLayout.optionSplit (id : Prefix.Stack → Stack) (fun j => some j)
  (by intro k; rfl) (by intro j k h; exact (Option.some.inj h).symm)
def decPrefixL : Label → Option Prefix.Label | .prefixPhase l => some l | _ => none
def lsPrefix := CallLayout.optionSplit Label.prefixPhase decPrefixL
  (by intro l; rfl) (by intro j k h; cases j <;> simp_all [decPrefixL])
def retPrefix : {l // decPrefixL l=none} := ⟨.afterPrefix,rfl⟩

def encBlockK : BlockMachine.Stack → Stack
  | .A => .a | .B => .b | .N => .unary | .temp => .tmp | .output => .output
def decBlockK : Stack → Option BlockMachine.Stack
  | .a => some .A | .b => some .B | .unary => some .N
  | .tmp => some .temp | .output => some .output | _ => none
def ksBlock := CallLayout.optionSplit encBlockK decBlockK
  (by intro k; cases k <;> rfl)
  (by intro j k h; cases j <;> cases k <;> simp_all [encBlockK,decBlockK])
def decBlockL : Label → Option BlockMachine.Label | .block l => some l | _ => none
def lsBlock := CallLayout.optionSplit Label.block decBlockL
  (by intro l; rfl) (by intro j k h; cases j <;> simp_all [decBlockL])
def retBlock : {l // decBlockL l=none} := ⟨.afterBlock,rfl⟩

def encClearK (_ : Unit) : Stack := .b
def decClearK : Stack → Option Unit | .b => some () | _ => none
def ksClear := CallLayout.optionSplit encClearK decClearK
  (by intro k; cases k; rfl)
  (by intro j k h; cases j <;> cases k <;> simp_all [encClearK,decClearK])
def encClearL (_ : Unit) : Label := .clear
def decClearL : Label → Option Unit | .clear => some () | _ => none
def lsClear := CallLayout.optionSplit encClearL decClearL
  (by intro k; cases k; rfl)
  (by intro j k h; cases j <;> cases k <;> simp_all [encClearL,decClearL])
def retClear : {l // decClearL l=none} := ⟨.finish,rfl⟩
def clearState : Reg ≃ Bool × (Option Bool × BlockMachine.Reg BT) where
  toFun r := (r.1.2,(r.1.1,r.2))
  invFun r := ((r.2.1,r.1),r.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def clean (valid : Bool) : Reg := ((none,valid),BlockMachine.clean BT)
def cfg (l : Option Label) (s : Reg) (I A B N H O T : List Bool) : Cfg :=
  ⟨l,s,Prefix.stk I A B N H O T⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Reg
  | .prefixPhase l => BoolCall.trStmt ksPrefix lsPrefix (Equiv.refl _) retPrefix (Prefix.program l)
  | .block l => BoolCall.trStmt ksBlock lsBlock (Equiv.prodComm _ _) retBlock (BlockMachine.program BT l)
  | .clear => BoolCall.trStmt ksClear lsClear clearState retClear (Clear.prog ())
  | .afterPrefix => .branch (fun s => s.1.2)
      (.goto fun _ => .block .loop) (.load (fun _ => clean false) .halt)
  | .afterBlock => .load (fun _ => clean false) (.goto fun _ => .clear)
  | .finish => .load (fun _ => clean true) .halt

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .prefixPhase (.hdr 0)
  σ := Reg
  initialState := clean false
  m := program
lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by intro j; change Finite Bool; infer_instance
end PEqualNP.Outside.L_lib_895_aux.Front

namespace PEqualNP.Outside.L_lib_895_aux.Front
open Turing
lemma call_prefix (n : Nat) (I : List Bool) (hn : 2≤n) :
    ∃ u ≤ 30*((header n++I).length+1)^2,
    (flip bind (TM2.step program))^[u]
      (some (cfg (some (.prefixPhase (.hdr 0))) (clean false) (header n++I) [] [] [] [] [] [])) =
      some (cfg (some .afterPrefix) (clean true) I (bits (width n) 0) []
        (List.replicate n true) [] (header (8*n+1)).reverse []) := by
  obtain ⟨u,hu,hr⟩ := Prefix.valid_prefix n I hn
  refine ⟨u,hu,?_⟩
  have hs : BoolCall.liftCfg ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
      (fun _ => []) (Prefix.cfg (some (.hdr 0)) (none,false) (header n++I) [] [] [] [] [] []) =
      cfg (some (.prefixPhase (.hdr 0))) (clean false) (header n++I) [] [] [] [] [] [] := by
    dsimp [BoolCall.liftCfg,cfg,Prefix.cfg,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have he : BoolCall.liftCfg ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
      (fun _ => []) (Prefix.cfg none (none,true) I (bits (width n) 0) []
        (List.replicate n true) [] (header (8*n+1)).reverse []) =
      cfg (some .afterPrefix) (clean true) I (bits (width n) 0) []
        (List.replicate n true) [] (header (8*n+1)).reverse [] := by
    dsimp [BoolCall.liftCfg,cfg,Prefix.cfg,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have hh := BoolCall.run_lift ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
    (fun _ => []) Prefix.program program (by intro l; rfl) u _ _ hr
  rw [hs,he] at hh
  exact hh

lemma call_blocks (n : Nat) (I R : List Bool) (hn : 2≤n) :
    ∃ u ≤ n*(220*width n+500)+10,
    (flip bind (TM2.step program))^[u]
      (some (cfg (some (.block .loop)) (clean true) I (bits (width n) 0) []
        (List.replicate n true) [] R [])) =
      some (cfg (some .afterBlock) (clean true) I (bits (width n) n)
        (List.replicate (width n) false) [] [] ((BlockMachine.postedBlocks n).reverse++R) []) := by
  obtain ⟨u,hu,hr⟩ := BlockMachine.blocks_run n R hn
  refine ⟨u,hu,?_⟩
  let extra := fun j : {j // decBlockK j=none} => Prefix.stk I (bits (width n) 0) []
    (List.replicate n true) [] R [] j.val
  have hs : BoolCall.liftCfg ksBlock lsBlock (Equiv.prodComm _ _) retBlock (none,true)
      extra (BlockMachine.startCfg n R) =
      cfg (some (.block .loop)) (clean true) I (bits (width n) 0) []
        (List.replicate n true) [] R [] := by
    dsimp [BoolCall.liftCfg,cfg,BlockMachine.startCfg,BlockMachine.cfg,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have he : BoolCall.liftCfg ksBlock lsBlock (Equiv.prodComm _ _) retBlock (none,true)
      extra (BlockMachine.endCfg n R) =
      cfg (some .afterBlock) (clean true) I (bits (width n) n)
        (List.replicate (width n) false) [] [] ((BlockMachine.blocksFrom n 0 n).reverse++R) [] := by
    dsimp [BoolCall.liftCfg,cfg,BlockMachine.endCfg,BlockMachine.cfg,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have hh := BoolCall.run_lift ksBlock lsBlock (Equiv.prodComm _ _) retBlock (none,true)
    extra (BlockMachine.program BT) program (by intro l; rfl) u _ _ hr
  rw [hs,he,BlockMachine.blocksFrom_eq_posted] at hh
  exact hh

lemma clear_b (I A B R : List Bool) :
    (flip bind (TM2.step program))^[B.length+1]
      (some (cfg (some .clear) (clean false) I A B [] [] R [])) =
      some (cfg (some .finish) (clean false) I A [] [] [] R []) := by
  let extra := fun j : {j // decClearK j=none} => Prefix.stk I A B [] [] R [] j.val
  have hs : BoolCall.liftCfg ksClear lsClear clearState retClear (none,BlockMachine.clean BT)
      extra (Clear.cfg (some ()) B) = cfg (some .clear) (clean false) I A B [] [] R [] := by
    dsimp [BoolCall.liftCfg,cfg,Clear.cfg,clearState,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have he : BoolCall.liftCfg ksClear lsClear clearState retClear (none,BlockMachine.clean BT)
      extra (Clear.cfg none []) = cfg (some .finish) (clean false) I A [] [] [] R [] := by
    dsimp [BoolCall.liftCfg,cfg,Clear.cfg,clearState,clean]
    congr 1 <;> (funext k; cases k <;> rfl)
  have hh := BoolCall.run_lift ksClear lsClear clearState retClear (none,BlockMachine.clean BT)
    extra Clear.prog program (by intro l; cases l; rfl) _ _ _ (Clear.clear_run B)
  rw [hs,he] at hh
  exact hh
end PEqualNP.Outside.L_lib_895_aux.Front

namespace PEqualNP.Outside.L_lib_895_aux.Front
open Turing
abbrev Run (u : Nat) (c d : Cfg) : Prop := (flip bind (TM2.step program))^[u] (some c)=some d
lemma run_one (c d : Cfg) (h : TM2.step program c=some d) : Run 1 c d := h
lemma run_comp {u v : Nat} {a b c : Cfg} (h : Run u a b) (h' : Run v b c) : Run (u+v) a c := by
  unfold Run at *
  rw [Nat.add_comm u v,Function.iterate_add_apply,h,h']
lemma after_prefix (I A B N H O T : List Bool) :
    TM2.step program (cfg (some .afterPrefix) (clean true) I A B N H O T)=
      some (cfg (some (.block .loop)) (clean true) I A B N H O T) := rfl
lemma after_blocks (I A B N H O T : List Bool) :
    TM2.step program (cfg (some .afterBlock) (clean true) I A B N H O T)=
      some (cfg (some .clear) (clean false) I A B N H O T) := rfl
lemma finish_step (I A B N H O T : List Bool) :
    TM2.step program (cfg (some .finish) (clean false) I A B N H O T)=
      some (cfg none (clean true) I A B N H O T) := rfl
lemma output_pack (n : Nat) :
    (BlockMachine.postedBlocks n).reverse++(header (8*n+1)).reverse =
      (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse := by
  simp only [PEqualNP.Outside.L_lib_895_aux.Comb.pack,List.reverse_append]
  rfl

def startCfg (n : Nat) (I : List Bool) : Cfg :=
  cfg (some (.prefixPhase (.hdr 0))) (clean false) (header n++I) [] [] [] [] [] []
def endCfg (n : Nat) (I : List Bool) : Cfg :=
  cfg none (clean true) I (bits (width n) n) [] [] []
    (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse []

set_option maxRecDepth 4096 in
theorem valid_run (n : Nat) (I : List Bool) (hn : 2≤n) :
    ∃ u ≤ 1000*((header n++I).length+1)^2, Run u (startCfg n I) (endCfg n I) := by
  obtain ⟨u,hu,hr⟩ := call_prefix n I hn
  have h0 := run_comp hr (run_one _ _ (after_prefix I (bits (width n) 0) []
    (List.replicate n true) [] (header (8*n+1)).reverse []))
  obtain ⟨v,hv,hvRun⟩ := call_blocks n I (header (8*n+1)).reverse hn
  have h1 := run_comp h0 hvRun
  have h2 := run_comp h1 (run_one _ _ (after_blocks I (bits (width n) n)
    (List.replicate (width n) false) [] []
    ((BlockMachine.postedBlocks n).reverse++(header (8*n+1)).reverse) []))
  have h3 := run_comp h2 (clear_b I (bits (width n) n) (List.replicate (width n) false)
    ((BlockMachine.postedBlocks n).reverse++(header (8*n+1)).reverse))
  have whole := run_comp h3 (run_one _ _ (finish_step I (bits (width n) n) [] [] []
    ((BlockMachine.postedBlocks n).reverse++(header (8*n+1)).reverse) []))
  simp only [List.length_replicate] at whole
  rw [output_pack] at whole
  refine ⟨_,?_,whole⟩
  have hw : width n≤n+1 := by unfold width; have := Nat.log2_le_self n; omega
  have hL : n≤(header n++I).length := by simp [header]
  have hprod := Nat.mul_le_mul_left n hw
  have hnn := Nat.mul_le_mul hL hL
  nlinarith

set_option maxRecDepth 4096 in
noncomputable def valid_evals (n : Nat) (I : List Bool) (hn : 2≤n) :
    StateTransition.EvalsToInTime (TM2.step program) (startCfg n I) (some (endCfg n I))
      (1000*((header n++I).length+1)^2) where
  steps := Classical.choose (valid_run n I hn)
  evals_in_steps := (Classical.choose_spec (valid_run n I hn)).2
  steps_le_m := (Classical.choose_spec (valid_run n I hn)).1
lemma finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma finite_state : Finite machine.σ := by change Finite Reg; infer_instance
end PEqualNP.Outside.L_lib_895_aux.Front

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing
lemma bad_lift (k : Stack) (l : Option Unit) (S : Stack → List Bool) (w : List Bool) :
 BoolCall.liftCfg (badKS k) (badLS k) (Equiv.prodComm (Option Bool) Bool) (badRet k) none
   (fun e => S e.val) (Clear.cfg l w) =
 (⟨some (l.elim (badNext k) (fun _ => .badClear k)),(none,false),Function.update S k w⟩ : Cfg) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j
   cases k <;> cases j <;> rfl

lemma call_bad (k : Stack) (S : Stack → List Bool) :
 run ((S k).length+1) (⟨some (.badClear k),(none,false),S⟩ : Cfg) =
 some (⟨some (badNext k),(none,false),Function.update S k []⟩ : Cfg) := by
 have h := BoolCall.run_lift (badKS k) (badLS k) (Equiv.prodComm (Option Bool) Bool) (badRet k) none
   (fun e => S e.val) Clear.prog program (by intro l; cases l; rfl)
   _ _ _ (Clear.clear_run (S k))
 rw [bad_lift,bad_lift,Function.update_eq_self] at h
 exact h

lemma stk_set_input (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .input X = stk X A B N H O T := by
 funext j; cases j <;> rfl
lemma clear_input (I A B N H O T : List Bool) :
 run (I.length+1) (cfg (some (.badClear .input)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .input)) (none,false) [] A B N H O T) := by
 have h := call_bad .input (stk I A B N H O T)
 rw [stk_set_input] at h
 exact h

lemma stk_set_a (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .a X = stk I X B N H O T := by
 funext j; cases j <;> rfl
lemma clear_a (I A B N H O T : List Bool) :
 run (A.length+1) (cfg (some (.badClear .a)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .a)) (none,false) I [] B N H O T) := by
 have h := call_bad .a (stk I A B N H O T)
 rw [stk_set_a] at h
 exact h

lemma stk_set_b (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .b X = stk I A X N H O T := by
 funext j; cases j <;> rfl
lemma clear_b (I A B N H O T : List Bool) :
 run (B.length+1) (cfg (some (.badClear .b)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .b)) (none,false) I A [] N H O T) := by
 have h := call_bad .b (stk I A B N H O T)
 rw [stk_set_b] at h
 exact h

lemma stk_set_unary (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .unary X = stk I A B X H O T := by
 funext j; cases j <;> rfl
lemma clear_unary (I A B N H O T : List Bool) :
 run (N.length+1) (cfg (some (.badClear .unary)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .unary)) (none,false) I A B [] H O T) := by
 have h := call_bad .unary (stk I A B N H O T)
 rw [stk_set_unary] at h
 exact h

lemma stk_set_headerCopy (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .headerCopy X = stk I A B N X O T := by
 funext j; cases j <;> rfl
lemma clear_headerCopy (I A B N H O T : List Bool) :
 run (H.length+1) (cfg (some (.badClear .headerCopy)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .headerCopy)) (none,false) I A B N [] O T) := by
 have h := call_bad .headerCopy (stk I A B N H O T)
 rw [stk_set_headerCopy] at h
 exact h

lemma stk_set_output (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .output X = stk I A B N H X T := by
 funext j; cases j <;> rfl
lemma clear_output (I A B N H O T : List Bool) :
 run (O.length+1) (cfg (some (.badClear .output)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .output)) (none,false) I A B N H [] T) := by
 have h := call_bad .output (stk I A B N H O T)
 rw [stk_set_output] at h
 exact h

lemma stk_set_tmp (I A B N H O T X : List Bool) :
 Function.update (stk I A B N H O T) .tmp X = stk I A B N H O X := by
 funext j; cases j <;> rfl
lemma clear_tmp (I A B N H O T : List Bool) :
 run (T.length+1) (cfg (some (.badClear .tmp)) (none,false) I A B N H O T) =
 some (cfg (some (badNext .tmp)) (none,false) I A B N H O []) := by
 have h := call_bad .tmp (stk I A B N H O T)
 rw [stk_set_tmp] at h
 exact h

lemma start_reject (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .reject) (none,false) I A B N H O T) =
 some (cfg (some (.badClear .input)) (none,false) I A B N H O T) := rfl
lemma end_reject :
 TM2.step program (cfg (some .badDone) (none,false) [] [] [] [] [] [] []) =
 some (cfg none (none,false) [] [] [] [] [] [] []) := rfl

theorem reject_cleanup (I A B N H O T : List Bool) :
 run (I.length+A.length+B.length+N.length+H.length+O.length+T.length+9)
   (cfg (some .reject) (none,false) I A B N H O T) =
 some (cfg none (none,false) [] [] [] [] [] [] []) := by
 have h := run_one _ _ (start_reject I A B N H O T)
 have h := run_comp h (clear_input I A B N H O T)
 have h := run_comp h (clear_a [] A B N H O T)
 have h := run_comp h (clear_b [] [] B N H O T)
 have h := run_comp h (clear_unary [] [] [] N H O T)
 have h := run_comp h (clear_headerCopy [] [] [] [] H O T)
 have h := run_comp h (clear_output [] [] [] [] [] O T)
 have h := run_comp h (clear_tmp [] [] [] [] [] [] T)
 have h := run_comp h (run_one _ _ end_reject)
 have he : 1+(I.length+1)+(A.length+1)+(B.length+1)+(N.length+1)+(H.length+1)+(O.length+1)+(T.length+1)+1 =
 I.length+A.length+B.length+N.length+H.length+O.length+T.length+9 := by omega
 rw [he] at h
 exact h
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Prefix
open Turing
lemma call_header_any (n : Nat) (I : List Bool) :
 ∃ t ≤ 5*(n+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (header n++I) [] [] [] [] [] []) =
 some (cfg (some .afterHeader) (some false,false) I [] (growInc^[n] []) (List.replicate n true) [] [] []) := by
 obtain ⟨t,ht,hr⟩ := Header.header_run n I [] []
 have h := BoolCall.run_lift hdrKS hdrLS (Equiv.refl State) hdrRet false
   (fun e => stk [] [] [] [] [] [] [] e.val) Header.program program (by intro l; rfl)
   t _ _ hr
 rw [hdr_lift,hdr_lift] at h
 rw [Header.increment_eq_growInc,List.append_nil] at h
 refine ⟨t,by simp only [List.length_nil] at ht; nlinarith,?_⟩
 simp only [header,List.append_assoc,List.singleton_append]
 exact h

lemma call_unterminated (n : Nat) :
 ∃ t ≤ 5*(n+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (List.replicate n true) [] [] [] [] [] []) =
 some (cfg (some .afterHeader) (none,false) [] [] (growInc^[n] []) (List.replicate n true) [] [] []) := by
 obtain ⟨t,ht,hr⟩ := Header.canonical_unterminated_run n
 have h := BoolCall.run_lift hdrKS hdrLS (Equiv.refl State) hdrRet false
   (fun e => stk [] [] [] [] [] [] [] e.val) Header.program program (by intro l; rfl)
   t _ _ hr
 rw [hdr_lift,hdr_lift] at h
 exact ⟨t,ht,h⟩
lemma missing_delimiter_step (A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterHeader) (none,false) [] A B N H O T) =
 some (cfg (some .reject) (none,false) [] A B N H O T) := rfl
lemma failed_min_step (I A B N H O T : List Bool) :
 TM2.step program (cfg (some .afterMin) (none,false) I A B N H O T) =
 some (cfg (some .reject) (none,false) I A B N H O T) := rfl

lemma grow_length_bound (n : Nat) : (growInc^[n] []).length ≤ n := by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [Function.iterate_succ_apply']
   have h := growInc_length (growInc^[n] [])
   omega

theorem reject_unterminated (n : Nat) :
 ∃ t ≤ 30*((List.replicate n true).length+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (List.replicate n true) [] [] [] [] [] []) =
 some (cfg none (none,false) [] [] [] [] [] [] []) := by
 obtain ⟨t,ht,hr⟩ := call_unterminated n
 let B := growInc^[n] []
 let N := List.replicate n true
 have h := run_comp hr (run_one _ _ (missing_delimiter_step [] B N [] [] []))
 have h := run_comp h (reject_cleanup [] [] B N [] [] [])
 refine ⟨t+1+([].length+[].length+B.length+N.length+[].length+[].length+[].length+9),?_,h⟩
 have hl := grow_length_bound n
 dsimp only [B,N] at *
 simp only [List.length_nil,List.length_replicate]
 nlinarith

theorem reject_small_header (n : Nat) (I : List Bool) (hn : n < 2) :
 ∃ t ≤ 30*((header n++I).length+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) (header n++I) [] [] [] [] [] []) =
 some (cfg none (none,false) [] [] [] [] [] [] []) := by
 obtain ⟨t,ht,hr⟩ := call_header_any n I
 let B := growInc^[n] []
 let N := List.replicate n true
 have hacc : decide (2≤B.length) = false := by
   have hlen := grow_length_bound n
   have : ¬ 2≤B.length := by dsimp [B]; omega
   simp [this]
 have h := run_comp hr (run_one _ _ (after_header I [] B N [] [] []))
 have hm := call_min I [] B N [] [] []
 rw [hacc] at hm
 have h := run_comp h hm
 have h := run_comp h (run_one _ _ (failed_min_step I [] B N [] [] []))
 have h := run_comp h (reject_cleanup I [] B N [] [] [])
 refine ⟨t+1+1+1+(I.length+[].length+B.length+N.length+[].length+[].length+[].length+9),?_,h⟩
 have hl := grow_length_bound n
 have hL : (header n++I).length = n+1+I.length := by simp [header,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
 dsimp only [B,N] at *
 simp only [List.length_nil,List.length_replicate,hL]
 nlinarith
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Prefix

def HeaderLegal (x : List Bool) : Prop := ∃ n I, 2 ≤ n ∧ x = header n++I

theorem invalid_prefix (x : List Bool) (hbad : ¬ HeaderLegal x) :
 ∃ t ≤ 30*(x.length+1)^2,
 run t (cfg (some (.hdr 0)) (none,false) x [] [] [] [] [] []) =
 some (cfg none (none,false) [] [] [] [] [] [] []) := by
 rcases Header.input_decomposition x with ⟨n,hx⟩ | ⟨n,I,hx⟩
 · subst x
   exact reject_unterminated n
 · have he : x = header n++I := by simpa [header,List.append_assoc] using hx
   have hn : n < 2 := by
     by_contra h
     exact hbad ⟨n,I,by omega,he⟩
   rw [he]
   exact reject_small_header n I hn

theorem prefix_total (x : List Bool) :
 ∃ t ≤ 30*(x.length+1)^2,
 (∃ n I, 2 ≤ n ∧ x = header n++I ∧
   run t (cfg (some (.hdr 0)) (none,false) x [] [] [] [] [] []) =
   some (cfg none (none,true) I (bits (width n) 0) [] (List.replicate n true) [] (header (8*n+1)).reverse [])) ∨
 (¬ HeaderLegal x ∧ run t (cfg (some (.hdr 0)) (none,false) x [] [] [] [] [] []) =
   some (cfg none (none,false) [] [] [] [] [] [] [])) := by
 classical
 by_cases hx : HeaderLegal x
 · obtain ⟨n,I,hn,he⟩ := hx
   subst x
   obtain ⟨t,ht,hh⟩ := valid_prefix n I hn
   exact ⟨t,ht,Or.inl ⟨n,I,hn,rfl,hh⟩⟩
 · obtain ⟨t,ht,hh⟩ := invalid_prefix x hx
   exact ⟨t,ht,Or.inr ⟨hx,hh⟩⟩
end PEqualNP.Outside.L_lib_895_aux.Prefix

namespace PEqualNP.Outside.L_lib_895_aux.Parser

def parseHeaderAux (acc : Nat) : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::xs => some (acc,xs)
  | true::xs => parseHeaderAux (acc+1) xs
def parseHeader (xs : List Bool) : Option (Nat × List Bool) := parseHeaderAux 0 xs

lemma headerAux_sound (acc : Nat) (xs : List Bool) (n : Nat) (rest : List Bool)
    (h : parseHeaderAux acc xs = some (n,rest)) :
    acc ≤ n ∧ List.replicate acc true ++ xs = header n ++ rest := by
  induction xs generalizing acc with
  | nil => simp [parseHeaderAux] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only[parseHeaderAux,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨le_rfl,by simp [header,List.append_assoc]⟩
    | true =>
      have hh := ih (acc+1) h
      refine ⟨by omega,?_⟩
      simpa [List.replicate_add,List.append_assoc] using hh.2

lemma header_sound (xs : List Bool) (n : Nat) (rest : List Bool)
    (h : parseHeader xs = some (n,rest)) : xs = header n ++ rest := by
  simpa using (headerAux_sound 0 xs n rest h).2

lemma headerAux_complete (acc n : Nat) (rest : List Bool) :
    parseHeaderAux acc (header n ++ rest) = some (acc+n,rest) := by
  induction n generalizing acc with
  | zero => simp [header,parseHeaderAux]
  | succ n ih =>
    have hh : header (n+1) ++ rest = true::(header n ++ rest) := by
      simp [header,List.replicate_succ]
    rw [hh,parseHeaderAux,ih (acc+1)]
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
lemma header_complete (n : Nat) (rest : List Bool) :
    parseHeader (header n ++ rest) = some (n,rest) := by
  simpa [parseHeader] using headerAux_complete 0 n rest

def readWord (w : Nat) (xs : List Bool) : Option (Nat × List Bool) :=
  if w ≤ xs.length then some (wordValue (xs.take w),xs.drop w) else none

lemma readWord_sound (w : Nat) (xs : List Bool) (v : Nat) (rest : List Bool)
    (h : readWord w xs = some (v,rest)) :
    xs = bits w v ++ rest ∧ v < 2^w := by
  by_cases hlen : w ≤ xs.length
  · simp only[readWord,if_pos hlen,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    have ht : (xs.take w).length = w := by simp only[List.length_take,Nat.min_eq_left hlen]
    have hb : bits w (wordValue (xs.take w)) = xs.take w := by
      simpa only[ht] using bits_wordValue (xs.take w)
    refine ⟨?_,?_⟩
    · rw [hb]
      exact (List.take_append_drop w xs).symm
    · simpa only[ht] using wordValue_lt (xs.take w)
  · simp [readWord,hlen] at h

lemma readWord_complete (w v : Nat) (rest : List Bool) (hv : v<2^w) :
    readWord w (bits w v ++ rest) = some (v,rest) := by
  have hlen : w ≤ (bits w v ++ rest).length := by simp only[List.length_append,bits_length]; omega
  have ht : (bits w v ++ rest).take w = bits w v := List.take_left' (bits_length w v)
  have hd : (bits w v ++ rest).drop w = rest := List.drop_left' (bits_length w v)
  simp only[readWord,if_pos hlen,ht,hd,wordValue_bits w v hv]

end PEqualNP.Outside.L_lib_895_aux.Parser

namespace PEqualNP.Outside.L_lib_895_aux.Front
open Turing

def initialCfg (x : List Bool) : Cfg := cfg (some (.prefixPhase (.hdr 0))) (clean false) x [] [] [] [] [] []
def rejectCfg : Cfg := cfg none (clean false) [] [] [] [] [] [] []

lemma call_prefix_invalid (x : List Bool) (hx : ¬ Prefix.HeaderLegal x) :
    ∃ u ≤ 30*(x.length+1)^2,
      Run u (initialCfg x) (cfg (some .afterPrefix) (clean false) [] [] [] [] [] [] []) := by
  obtain ⟨u,hu,hr⟩ := Prefix.invalid_prefix x hx
  refine ⟨u,hu,?_⟩
  have hs : BoolCall.liftCfg ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
      (fun _ => []) (Prefix.cfg (some (.hdr 0)) (none,false) x [] [] [] [] [] []) = initialCfg x := by
    rfl
  have he : BoolCall.liftCfg ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
      (fun _ => []) (Prefix.cfg none (none,false) [] [] [] [] [] [] []) =
      cfg (some .afterPrefix) (clean false) [] [] [] [] [] [] [] := by rfl
  have hh := BoolCall.run_lift ksPrefix lsPrefix (Equiv.refl _) retPrefix (BlockMachine.clean BT)
    (fun _ => []) Prefix.program program (by intro l; rfl) u _ _ hr
  rw [hs,he] at hh
  exact hh

lemma reject_step : TM2.step program (cfg (some .afterPrefix) (clean false) [] [] [] [] [] [] []) =
    some rejectCfg := rfl

theorem invalid_run (x : List Bool) (hx : ¬ Prefix.HeaderLegal x) :
    ∃ u ≤ 1000*(x.length+1)^2, Run u (initialCfg x) rejectCfg := by
  obtain ⟨u,hu,hr⟩ := call_prefix_invalid x hx
  have whole := run_comp hr (run_one _ _ reject_step)
  exact ⟨u+1,by nlinarith [Nat.zero_le x.length],whole⟩

lemma header_legal_iff_parser (x : List Bool) :
    Prefix.HeaderLegal x ↔ ∃ n I, 2≤n ∧ Parser.parseHeader x=some (n,I) := by
  constructor
  · rintro ⟨n,I,hn,rfl⟩
    exact ⟨n,I,hn,Parser.header_complete n I⟩
  · rintro ⟨n,I,hn,hp⟩
    exact ⟨n,I,hn,Parser.header_sound x n I hp⟩

def outcome (x : List Bool) : Cfg :=
  match Parser.parseHeader x with
  | some (n,I) => if 2≤n then endCfg n I else rejectCfg
  | none => rejectCfg
lemma outcome_header (n : Nat) (I : List Bool) (hn : 2≤n) :
    outcome (header n++I)=endCfg n I := by simp [outcome,Parser.header_complete,hn]
lemma outcome_invalid (x : List Bool) (hx : ¬ Prefix.HeaderLegal x) : outcome x=rejectCfg := by
  cases hp : Parser.parseHeader x with
  | none => simp [outcome,hp]
  | some d =>
    rcases d with ⟨n,I⟩
    have hn : ¬ 2≤n := by
      intro hn
      exact hx ((header_legal_iff_parser x).mpr ⟨n,I,hn,hp⟩)
    simp [outcome,hp,hn]

set_option maxRecDepth 4096 in
theorem total_run (x : List Bool) :
    ∃ u ≤ 1000*(x.length+1)^2, Run u (initialCfg x) (outcome x) := by
  classical
  by_cases hx : Prefix.HeaderLegal x
  · obtain ⟨n,I,hn,he⟩ := hx
    subst x
    rw [outcome_header n I hn]
    exact valid_run n I hn
  · rw [outcome_invalid x hx]
    exact invalid_run x hx

set_option maxRecDepth 4096 in
noncomputable def total_evals (x : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg x) (some (outcome x))
      (1000*(x.length+1)^2) where
  steps := Classical.choose (total_run x)
  evals_in_steps := (Classical.choose_spec (total_run x)).2
  steps_le_m := (Classical.choose_spec (total_run x)).1

lemma outcome_flag (x : List Bool) :
    (outcome x).var.1.2=true ↔ ∃ n I, 2≤n ∧ Parser.parseHeader x=some (n,I) := by
  cases hp : Parser.parseHeader x with
  | none => simp [outcome,hp,rejectCfg,cfg,clean]
  | some d =>
    rcases d with ⟨n,I⟩
    by_cases hn : 2≤n <;> simp [outcome,hp,hn,endCfg,rejectCfg,cfg,clean]

lemma invalid_clears_all (x : List Bool) (hx : ¬ Prefix.HeaderLegal x) :
    (outcome x).l=none ∧ (outcome x).var=clean false ∧ ∀ k, (outcome x).stk k=[] := by
  rw [outcome_invalid x hx]
  refine ⟨rfl,rfl,?_⟩
  intro k; cases k <;> rfl
end PEqualNP.Outside.L_lib_895_aux.Front

namespace PEqualNP.Outside.L_lib_895_aux.ReadWord
open Turing
abbrev RC := TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 3) (Option Bool × Bool)
def stk (I W WT FT F : List Bool) : Fin 5 → List Bool := ![I,W,WT,FT,F]
@[simp] lemma stk_get0 (I W WT FT F : List Bool) : stk I W WT FT F 0 = I := rfl
@[simp] lemma stk_set0 (I W WT FT F X : List Bool) :
  Function.update (stk I W WT FT F) 0 X = stk X W WT FT F := by
  funext k; fin_cases k <;> rfl
@[simp] lemma stk_get1 (I W WT FT F : List Bool) : stk I W WT FT F 1 = W := rfl
@[simp] lemma stk_set1 (I W WT FT F X : List Bool) :
  Function.update (stk I W WT FT F) 1 X = stk I X WT FT F := by
  funext k; fin_cases k <;> rfl
@[simp] lemma stk_get2 (I W WT FT F : List Bool) : stk I W WT FT F 2 = WT := rfl
@[simp] lemma stk_set2 (I W WT FT F X : List Bool) :
  Function.update (stk I W WT FT F) 2 X = stk I W X FT F := by
  funext k; fin_cases k <;> rfl
@[simp] lemma stk_get3 (I W WT FT F : List Bool) : stk I W WT FT F 3 = FT := rfl
@[simp] lemma stk_set3 (I W WT FT F X : List Bool) :
  Function.update (stk I W WT FT F) 3 X = stk I W WT X F := by
  funext k; fin_cases k <;> rfl
@[simp] lemma stk_get4 (I W WT FT F : List Bool) : stk I W WT FT F 4 = F := rfl
@[simp] lemma stk_set4 (I W WT FT F X : List Bool) :
  Function.update (stk I W WT FT F) 4 X = stk I W WT FT X := by
  funext k; fin_cases k <;> rfl

def program : Fin 3 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 3) (Option Bool × Bool)
 | 0 => .pop 1 (fun s x => (x,s.2)) (.branch (fun s => s.1.isSome)
     (.push 2 (fun s => s.1.getD false)
       (.pop 0 (fun s x => (x,s.2)) (.branch (fun s => s.1.isSome)
         (.push 3 (fun s => s.1.getD false) (.load (fun s => (none,s.2)) (.goto fun _ => 0)))
         (.load (fun _ => (none,false)) (.goto fun _ => 1)))))
     (.load (fun s => (none,s.2)) (.goto fun _ => 1)))
 | 1 => .pop 2 (fun s x => (x,s.2)) (.branch (fun s => s.1.isSome)
     (.push 1 (fun s => s.1.getD false) (.load (fun s => (none,s.2)) (.goto fun _ => 1)))
     (.load (fun s => (none,s.2)) (.goto fun _ => 2)))
 | _ => .pop 3 (fun s x => (x,s.2)) (.branch (fun s => s.1.isSome)
     (.push 4 (fun s => s.1.getD false) (.load (fun s => (none,s.2)) (.goto fun _ => 2)))
     (.load (fun s => (none,s.2)) .halt))

def machine : FinTM2 where
 K := Fin 5
 k₀ := 0
 k₁ := 4
 Γ _ := Bool
 Λ := Fin 3
 main := 0
 σ := Option Bool × Bool
 initialState := (none,true)
 m := program

def cfg (l : Option (Fin 3)) (v : Bool) (I W WT FT F : List Bool) : RC :=
 ⟨l,(none,v),stk I W WT FT F⟩
def run (t : Nat) (c : RC) : Option RC :=
 (fun s : Option RC => s.bind (TM2.step program))^[t] (some c)
lemma run_one (c d : RC) (h : TM2.step program c = some d) : run 1 c = some d := by
 simpa only [run,Function.iterate_one,Option.bind_some] using h
lemma run_comp {s t : Nat} {a b c : RC}
 (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]

lemma read_cons (I W WT FT F : List Bool) (v : Bool) (a b : Bool) :
 TM2.step program (cfg (some 0) v (a::I) (b::W) WT FT F) = some (cfg (some 0) v I W (b::WT) (a::FT) F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma read_nil (I W WT FT F : List Bool) (v : Bool)  :
 TM2.step program (cfg (some 0) v I [] WT FT F) = some (cfg (some 1) v I [] WT FT F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma read_fail (I W WT FT F : List Bool) (v : Bool) (b : Bool) :
 TM2.step program (cfg (some 0) v [] (b::W) WT FT F) = some (cfg (some 1) false [] W (b::WT) FT F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma restoreW_cons (I W WT FT F : List Bool) (v : Bool) (b : Bool) :
 TM2.step program (cfg (some 1) v I W (b::WT) FT F) = some (cfg (some 1) v I (b::W) WT FT F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma restoreW_nil (I W WT FT F : List Bool) (v : Bool)  :
 TM2.step program (cfg (some 1) v I W [] FT F) = some (cfg (some 2) v I W [] FT F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma restoreF_cons (I W WT FT F : List Bool) (v : Bool) (b : Bool) :
 TM2.step program (cfg (some 2) v I W WT (b::FT) F) = some (cfg (some 2) v I W WT FT (b::F)) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma restoreF_nil (I W WT FT F : List Bool) (v : Bool)  :
 TM2.step program (cfg (some 2) v I W WT [] F) = some (cfg none v I W WT [] F) := by
 simp [TM2.step,program,cfg,TM2.stepAux]

lemma restoreF_run (I W WT FT F : List Bool) (v : Bool) :
 run (FT.length+1) (cfg (some 2) v I W WT FT F) =
 some (cfg none v I W WT [] (FT.reverse++F)) := by
 induction FT generalizing F with
 | nil => simpa using run_one _ _ (restoreF_nil I W WT [] F v)
 | cons b FT ih =>
   have h := run_comp (run_one _ _ (restoreF_cons I W WT FT F v b)) (ih (b::F))
   simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

lemma restoreW_run (I W WT FT F : List Bool) (v : Bool) :
 run (WT.length+1) (cfg (some 1) v I W WT FT F) =
 some (cfg (some 2) v I (WT.reverse++W) [] FT F) := by
 induction WT generalizing W with
 | nil => simpa using run_one _ _ (restoreW_nil I W [] FT F v)
 | cons b WT ih =>
   have h := run_comp (run_one _ _ (restoreW_cons I W WT FT F v b)) (ih (b::W))
   simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

lemma read_run (A W : List Bool) (hlen : A.length = W.length)
 (I WT FT F : List Bool) (v : Bool) :
 run (W.length+1) (cfg (some 0) v (A++I) W WT FT F) =
 some (cfg (some 1) v I [] (W.reverse++WT) (A.reverse++FT) F) := by
 induction W generalizing A WT FT with
 | nil =>
   have : A = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
   subst A
   simpa using run_one _ _ (read_nil I [] WT FT F v)
 | cons b W ih =>
   cases A with
   | nil => simp at hlen
   | cons a A =>
     have hl : A.length = W.length := by simpa using hlen
     have h := run_comp (run_one _ _ (read_cons (A++I) W WT FT F v a b)) (ih A hl (b::WT) (a::FT))
     simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem read_success (I W : List Bool) (hlen : W.length ≤ I.length) :
 run (3*W.length+3) (cfg (some 0) true I W [] [] []) =
 some (cfg none true (I.drop W.length) W [] [] (I.take W.length)) := by
 have hl : (I.take W.length).length = W.length := List.length_take_of_le hlen
 have h1 := read_run (I.take W.length) W hl (I.drop W.length) [] [] [] true
 have h2 := restoreW_run (I.drop W.length) [] W.reverse (I.take W.length).reverse [] true
 have h3 := restoreF_run (I.drop W.length) W [] (I.take W.length).reverse [] true
 simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3
 have h := run_comp (run_comp h1 h2) h3
 simpa only [List.take_append_drop,hl,show W.length+1+(W.length+1)+(W.length+1)=3*W.length+3 by omega] using h

end PEqualNP.Outside.L_lib_895_aux.ReadWord

namespace PEqualNP.Outside.L_lib_895_aux.ReadWord

lemma read_short (I W : List Bool) (hlen : I.length < W.length)
 (WT FT F : List Bool) (v : Bool) :
 run (I.length+1) (cfg (some 0) v I W WT FT F) =
 some (cfg (some 1) false [] (W.drop (I.length+1))
   ((W.take (I.length+1)).reverse++WT) (I.reverse++FT) F) := by
 induction I generalizing W WT FT with
 | nil =>
   cases W with
   | nil => simp at hlen
   | cons b W => simpa using run_one _ _ (read_fail [] W WT FT F v b)
 | cons a I ih =>
   cases W with
   | nil => simp at hlen
   | cons b W =>
     have hl : I.length < W.length := by simpa using hlen
     have h := run_comp (run_one _ _ (read_cons I W WT FT F v a b))
       (ih W hl (b::WT) (a::FT))
     simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem read_failure (I W : List Bool) (hlen : I.length < W.length) :
 run (3*I.length+4) (cfg (some 0) true I W [] [] []) =
 some (cfg none false [] W [] [] I) := by
 have htake : (W.take (I.length+1)).length = I.length+1 :=
   List.length_take_of_le (by omega)
 have h1 := read_short I W hlen [] [] [] true
 have h2 := restoreW_run [] (W.drop (I.length+1)) (W.take (I.length+1)).reverse I.reverse [] false
 have h3 := restoreF_run [] W [] I.reverse [] false
 simp only [List.append_nil,List.reverse_reverse,List.length_reverse,List.take_append_drop,htake] at h1 h2 h3
 have h := run_comp (run_comp h1 h2) h3
 simpa only [show I.length+1+(I.length+1+1)+(I.length+1)=3*I.length+4 by omega] using h

theorem read_contract (I W : List Bool) :
 ∃ t ≤ 3*W.length+3,
   run t (cfg (some 0) true I W [] [] []) =
   some (cfg none (decide (W.length ≤ I.length)) (I.drop W.length) W [] [] (I.take W.length)) := by
 by_cases h : W.length ≤ I.length
 · exact ⟨3*W.length+3,le_rfl,by simpa [h] using read_success I W h⟩
 · have hl : I.length < W.length := by omega
   refine ⟨3*I.length+4,by omega,?_⟩
   simpa [h,List.drop_eq_nil_of_le (by omega : I.length ≤ W.length),List.take_of_length_le (by omega : I.length ≤ W.length)] using read_failure I W hl

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance

end PEqualNP.Outside.L_lib_895_aux.ReadWord

namespace PEqualNP.Outside.L_lib_895_aux.RecordMachine
open Turing
abbrev S := Option Bool × Bool
abbrev Cfg := TM2.Cfg (fun _ : Fin 9 => Bool) (Fin 19) S

def kp (i : Fin 4) : Equiv.Perm (Fin 9) :=
  (Equiv.swap 1 (if i.val  %  2 = 1 then 8 else 1)).trans
    (Equiv.swap 4 ⟨4+i.val,by omega⟩)
def ks (i : Fin 4) : Fin 9 ≃ Fin 5 ⊕ Fin 4 :=
  (kp i).trans ((finSumFinEquiv (m:=5) (n:=4)).symm)
def lp (i : Fin 4) : Equiv.Perm (Fin 19) :=
  ((Equiv.swap 0 ⟨3*i.val,by omega⟩).trans
   (Equiv.swap 1 ⟨3*i.val+1,by omega⟩)).trans
   (Equiv.swap 2 ⟨3*i.val+2,by omega⟩)
def ls (i : Fin 4) : Fin 19 ≃ Fin 3 ⊕ Fin 16 :=
  (lp i).trans (finSumFinEquiv (m:=3) (n:=16)).symm
def ss : S ≃ S × Unit := ⟨fun s => (s,()),fun s => s.1,by intro s;rfl,by intro s;cases s; rfl⟩
def ret (i : Fin 4) : Fin 16 := ⟨10+i.val,by omega⟩
def callLabel (i : Fin 4) (j : Fin 3) : Fin 19 := ⟨3*i.val+j.val,by omega⟩
def after (i : Fin 4) : Fin 19 := ⟨13+i.val,by omega⟩
lemma label_component (i : Fin 4) (j : Fin 3) :
 (ls i).symm (.inl j) = callLabel i j := by fin_cases i <;> fin_cases j <;> decide
lemma label_return (i : Fin 4) : (ls i).symm (.inr (ret i)) = after i := by
 fin_cases i <;> decide

def program (l : Fin 19) : TM2.Stmt (fun _ : Fin 9 => Bool) (Fin 19) S :=
 if h : l.val < 12 then
   let i : Fin 4 := ⟨l.val/3,by omega⟩
   let j : Fin 3 := ⟨l.val % 3,Nat.mod_lt _ (by omega)⟩
   BoolCall.trStmt (ks i) (ls i) ss (ret i) (ReadWord.program j)
 else if l=12 then
   .push 8 (fun _ => false) (.push 8 (fun _ => false)
     (.load (fun _ => (none,true)) (.goto fun _ => 0)))
 else if l=17 then .pop 8 (fun s _ => s) (.pop 8 (fun _ _ => (none,false)) .halt)
 else if l=18 then .pop 8 (fun s _ => s) (.pop 8 (fun _ _ => (none,true)) .halt)
 else .branch (fun s => s.2)
   (.load (fun _ => (none,true)) (.goto fun _ =>
      if l=13 then 3 else if l=14 then 6 else if l=15 then 9 else 18))
   (.goto fun _ => 17)
lemma program_component (i : Fin 4) (j : Fin 3) :
 program ((ls i).symm (.inl j)) =
 BoolCall.trStmt (ks i) (ls i) ss (ret i) (ReadWord.program j) := by
 rw [label_component]
 fin_cases i <;> fin_cases j <;> rfl

def machine : FinTM2 where
 K := Fin 9
 k₀ := 0
 k₁ := 4
 Γ _ := Bool
 Λ := Fin 19
 main := 12
 σ := S
 initialState := (none,true)
 m := program

def run (t : Nat) (c : Cfg) : Option Cfg :=
 (flip bind (TM2.step program))^[t] (some c)
lemma run_one (c d : Cfg) (h : TM2.step program c=some d) : run 1 c=some d := h
lemma run_comp {s t : Nat} {a b c : Cfg}
 (h1 : run s a=some b) (h2 : run t b=some c) : run (s+t) a=some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]

def tapes (I W WT FT FI FC FJ FD CM : List Bool) : Fin 9 → List Bool :=
 ![I,W,WT,FT,FI,FC,FJ,FD,CM]
def cfg (l : Option (Fin 19)) (v : Bool) (st : Fin 9 → List Bool) : Cfg :=
 ⟨l,(none,v),st⟩
def marker (i : Fin 4) : Fin 9 := if i.val % 2=1 then 8 else 1
def field (i : Fin 4) : Fin 9 := ⟨4+i.val,by omega⟩
lemma stack_map (i : Fin 4) :
 (ks i).symm (.inl 0)=0 ∧ (ks i).symm (.inl 1)=marker i ∧
 (ks i).symm (.inl 2)=2 ∧ (ks i).symm (.inl 3)=3 ∧
 (ks i).symm (.inl 4)=field i := by fin_cases i <;> decide

def updated (i : Fin 4) (st : Fin 9 → List Bool) : Fin 9 → List Bool :=
 Function.update (Function.update st 0 ((st 0).drop (st (marker i)).length))
   (field i) ((st 0).take (st (marker i)).length)
lemma lift_start (i : Fin 4) (st : Fin 9 → List Bool)
 (h2 : st 2=[]) (h3 : st 3=[]) (hf : st (field i)=[]) :
 BoolCall.liftCfg (ks i) (ls i) ss (ret i) ()
   (fun e => st ((ks i).symm (.inr e)))
   (ReadWord.cfg (some 0) true (st 0) (st (marker i)) [] [] []) =
 cfg (some (callLabel i 0)) true st := by
 change (⟨some ((ls i).symm (.inl 0)),(none,true),_⟩ : Cfg) = ⟨some (callLabel i 0),(none,true),st⟩
 congr 1
 have hp : ReadWord.stk (st 0) (st (marker i)) [] [] [] =
       (fun k => st ((ks i).symm (.inl k))) := by
      funext k
      obtain ⟨h0,h1,h2',h3',h4⟩ := stack_map i
      fin_cases k <;> simp [ReadWord.stk,h0,h1,h2',h3',h4,h2,h3,hf]
 change BoolCall.liftStacks (ks i) (ReadWord.stk (st 0) (st (marker i)) [] [] []) (fun e => st ((ks i).symm (.inr e))) = st
 rw [hp]
 exact BoolCall.liftStacks_reconstruct (ks i) st
lemma lift_end (i : Fin 4) (st : Fin 9 → List Bool) (v : Bool)
 (h2 : st 2=[]) (h3 : st 3=[]) (hf : st (field i)=[]) :
 BoolCall.liftCfg (ks i) (ls i) ss (ret i) ()
   (fun e => st ((ks i).symm (.inr e)))
   (ReadWord.cfg none v ((st 0).drop (st (marker i)).length)
     (st (marker i)) [] [] ((st 0).take (st (marker i)).length)) =
 cfg (some (after i)) v (updated i st) := by
 change (⟨some ((ls i).symm (.inr (ret i))),(none,v),_⟩ : Cfg) = ⟨some (after i),(none,v),updated i st⟩
 congr 1
 · exact congrArg some (label_return i)
 · funext k
   fin_cases i <;> fin_cases k <;>
     simp [BoolCall.liftCfg,BoolCall.liftStacks,ks,kp,finSumFinEquiv,
       Equiv.swap_apply_def,Fin.addCases,Fin.natAdd,Fin.castAdd,ReadWord.cfg,ReadWord.stk,cfg,updated,field,marker] at * <;>
     assumption

theorem call_contract (i : Fin 4) (st : Fin 9 → List Bool)
 (h2 : st 2=[]) (h3 : st 3=[]) (hf : st (field i)=[]) :
 ∃ t ≤ 3*(st (marker i)).length+3,
 run t (cfg (some (callLabel i 0)) true st) =
 some (cfg (some (after i))
   (decide ((st (marker i)).length ≤ (st 0).length)) (updated i st)) := by
 obtain ⟨t,ht,hr⟩ := ReadWord.read_contract (st 0) (st (marker i))
 have h := BoolCall.run_lift (ks i) (ls i) ss (ret i) ()
   (fun e => st ((ks i).symm (.inr e))) ReadWord.program program
   (program_component i) t _ _ hr
 rw [lift_start i st h2 h3 hf,lift_end i st _ h2 h3 hf] at h
 exact ⟨t,ht,h⟩
end PEqualNP.Outside.L_lib_895_aux.RecordMachine

namespace PEqualNP.Outside.L_lib_895_aux.RecordMachine
open Turing

def initial (I W : List Bool) : Cfg := cfg (some 12) true (tapes I W [] [] [] [] [] [] [])
def stage0 (I W : List Bool) := tapes I W [] [] [] [] [] [] [false,false]
def stage1 (I W : List Bool) := updated 0 (stage0 I W)
def stage2 (I W : List Bool) := updated 1 (stage1 I W)
def stage3 (I W : List Bool) := updated 2 (stage2 I W)
def stage4 (I W : List Bool) := updated 3 (stage3 I W)
def clean (st : Fin 9 → List Bool) := Function.update st 8 []

lemma entry_step (I W : List Bool) : TM2.step program (initial I W) =
 some (cfg (some 0) true (stage0 I W)) := by
 simp [TM2.step,initial,cfg,program,TM2.stepAux]
 congr 1
 funext k
 fin_cases k <;> rfl

lemma check_step (i : Fin 4) (v : Bool) (st : Fin 9 → List Bool) :
 TM2.step program (cfg (some (after i)) v st) =
 some (cfg (some (if v then if i.val<3 then ⟨3*(i.val+1),by omega⟩ else 18 else 17)) v st) := by
 fin_cases i <;> cases v <;> rfl
lemma exit_step (v : Bool) (st : Fin 9 → List Bool) (hc : st 8=[false,false]) :
 TM2.step program (cfg (some (if v then 18 else 17)) v st) =
 some (cfg none v (clean st)) := by
 cases v <;>
 simp [TM2.step,program,cfg,TM2.stepAux,hc,clean,Function.update_idem]

lemma stage_conditions (I W : List Bool) :
 (stage0 I W) 2=[] ∧ (stage0 I W) 3=[] ∧ (stage0 I W) (field 0)=[] ∧
 (stage1 I W) 2=[] ∧ (stage1 I W) 3=[] ∧ (stage1 I W) (field 1)=[] ∧
 (stage2 I W) 2=[] ∧ (stage2 I W) 3=[] ∧ (stage2 I W) (field 2)=[] ∧
 (stage3 I W) 2=[] ∧ (stage3 I W) 3=[] ∧ (stage3 I W) (field 3)=[] := by
 simp [stage0,stage1,stage2,stage3,updated,tapes,field]
lemma stage_markers (I W : List Bool) :
 (stage0 I W) (marker 0)=W ∧ (stage1 I W) (marker 1)=[false,false] ∧
 (stage2 I W) (marker 2)=W ∧ (stage3 I W) (marker 3)=[false,false] := by
 simp [stage0,stage1,stage2,stage3,updated,tapes,field,marker]
lemma stage_inputs (I W : List Bool) :
 (stage0 I W) 0=I ∧ (stage1 I W) 0=I.drop W.length ∧
 (stage2 I W) 0=I.drop (W.length+2) ∧
 (stage3 I W) 0=I.drop (2*W.length+2) ∧
 (stage4 I W) 0=I.drop (2*W.length+4) := by
 simp [stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.drop_drop]
 congr 2 <;> omega
lemma all_CM (I W : List Bool) :
 stage1 I W 8=[false,false] ∧stage2 I W 8=[false,false] ∧
 stage3 I W 8=[false,false] ∧stage4 I W 8=[false,false] := by
 simp [stage0,stage1,stage2,stage3,stage4,updated,tapes,field]

end PEqualNP.Outside.L_lib_895_aux.RecordMachine

namespace PEqualNP.Outside.L_lib_895_aux.RecordMachine
open Turing

def Finished (I W : List Bool) (v : Bool) (st : Fin 9 → List Bool) : Prop :=
 v=decide (2*W.length+4≤I.length) ∧ st 1=W ∧ st 2=[] ∧ st 3=[] ∧ st 8=[] ∧
 (v=true → st=clean (stage4 I W)) ∧ (v=false → st 0=[])

theorem record_contract (I W : List Bool) :
 ∃ t ≤ 6*W.length+30, ∃ v st,
 run t (initial I W)=some (cfg none v st) ∧ Finished I W v st := by
 obtain ⟨c02,c03,c0f,c12,c13,c1f,c22,c23,c2f,c32,c33,c3f⟩ := stage_conditions I W
 obtain ⟨sm0,sm1,sm2,sm3⟩ := stage_markers I W
 obtain ⟨si0,si1,si2,si3,si4⟩ := stage_inputs I W
 obtain ⟨cm1,cm2,cm3,cm4⟩ := all_CM I W
 have he := run_one _ _ (entry_step I W)
 obtain ⟨t0,ht0,hr0⟩ := call_contract 0 (stage0 I W) c02 c03 c0f
 have hb0 : t0 ≤ 3*(W.length)+3 := by simpa only [sm0,List.length_cons,List.length_nil] using ht0
 have h0 : run t0 (cfg (some 0) true (stage0 I W)) =
   some (cfg (some 13) (decide (W.length≤I.length)) (stage1 I W)) := by
   simp only [sm0,si0,List.length_cons,List.length_nil] at hr0
   simpa [callLabel,after,stage1] using hr0
 obtain ⟨t1,ht1,hr1⟩ := call_contract 1 (stage1 I W) c12 c13 c1f
 have hb1 : t1 ≤ 3*(2)+3 := by simpa only [sm1,List.length_cons,List.length_nil] using ht1
 have h1 : run t1 (cfg (some 3) true (stage1 I W)) =
   some (cfg (some 14) (decide (2≤(I.drop W.length).length)) (stage2 I W)) := by
   simp only [sm1,si1,List.length_cons,List.length_nil] at hr1
   simpa [callLabel,after,stage2] using hr1
 obtain ⟨t2,ht2,hr2⟩ := call_contract 2 (stage2 I W) c22 c23 c2f
 have hb2 : t2 ≤ 3*(W.length)+3 := by simpa only [sm2,List.length_cons,List.length_nil] using ht2
 have h2 : run t2 (cfg (some 6) true (stage2 I W)) =
   some (cfg (some 15) (decide (W.length≤(I.drop (W.length+2)).length)) (stage3 I W)) := by
   simp only [sm2,si2,List.length_cons,List.length_nil] at hr2
   simpa [callLabel,after,stage3] using hr2
 obtain ⟨t3,ht3,hr3⟩ := call_contract 3 (stage3 I W) c32 c33 c3f
 have hb3 : t3 ≤ 3*(2)+3 := by simpa only [sm3,List.length_cons,List.length_nil] using ht3
 have h3 : run t3 (cfg (some 9) true (stage3 I W)) =
   some (cfg (some 16) (decide (2≤(I.drop (2*W.length+2)).length)) (stage4 I W)) := by
   simp only [sm3,si3,List.length_cons,List.length_nil] at hr3
   simpa [callLabel,after,stage4] using hr3
 by_cases hl0 : W.length≤I.length
 · have hs0 := h0
   simp only [hl0,decide_true] at hs0
   have hc0 := run_one _ _ (check_step 0 true (stage1 I W))
   change run 1 (cfg (some 13) true (stage1 I W)) = some (cfg (some 3) true (stage1 I W)) at hc0
   by_cases hl1 : 2≤(I.drop W.length).length
   · have hs1 := h1
     simp only [hl1,decide_true] at hs1
     have hc1 := run_one _ _ (check_step 1 true (stage2 I W))
     change run 1 (cfg (some 14) true (stage2 I W)) = some (cfg (some 6) true (stage2 I W)) at hc1
     by_cases hl2 : W.length≤(I.drop (W.length+2)).length
     · have hs2 := h2
       simp only [hl2,decide_true] at hs2
       have hc2 := run_one _ _ (check_step 2 true (stage3 I W))
       change run 1 (cfg (some 15) true (stage3 I W)) = some (cfg (some 9) true (stage3 I W)) at hc2
       by_cases hl3 : 2≤(I.drop (2*W.length+2)).length
       · have hs3 := h3
         simp only [hl3,decide_true] at hs3
         have hc3 := run_one _ _ (check_step 3 true (stage4 I W))
         change run 1 (cfg (some 16) true (stage4 I W)) = some (cfg (some 18) true (stage4 I W)) at hc3
         have hx := run_one _ _ (exit_step true (stage4 I W) cm4)
         have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hs2) hc2) hs3) hc3) hx
         refine ⟨_,by omega,true,clean (stage4 I W),hrun,?_⟩
         have hlen : 2*W.length+4≤I.length := by simp only [List.length_drop] at hl0 hl1 hl2 hl3; omega
         simp [Finished,hlen,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker] <;> omega
       · have hf3 := h3
         simp only [hl3,decide_false] at hf3
         have hc3 := run_one _ _ (check_step 3 false (stage4 I W))
         change run 1 (cfg (some 16) false (stage4 I W)) = some (cfg (some 17) false (stage4 I W)) at hc3
         have hx := run_one _ _ (exit_step false (stage4 I W) cm4)
         have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hs2) hc2) hf3) hc3) hx
         refine ⟨_,by omega,false,clean (stage4 I W),hrun,?_⟩
         have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl3; omega
         have hi : stage4 I W 0=[] := by
           rw [si4]
           apply List.drop_eq_nil_of_le
           simp only [List.length_drop] at hl3
           omega
         refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
         all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
     · have hf2 := h2
       simp only [hl2,decide_false] at hf2
       have hc2 := run_one _ _ (check_step 2 false (stage3 I W))
       change run 1 (cfg (some 15) false (stage3 I W)) = some (cfg (some 17) false (stage3 I W)) at hc2
       have hx := run_one _ _ (exit_step false (stage3 I W) cm3)
       have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hf2) hc2) hx
       refine ⟨_,by omega,false,clean (stage3 I W),hrun,?_⟩
       have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl2; omega
       have hi : stage3 I W 0=[] := by
         rw [si3]
         apply List.drop_eq_nil_of_le
         simp only [List.length_drop] at hl2
         omega
       refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
       all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
   · have hf1 := h1
     simp only [hl1,decide_false] at hf1
     have hc1 := run_one _ _ (check_step 1 false (stage2 I W))
     change run 1 (cfg (some 14) false (stage2 I W)) = some (cfg (some 17) false (stage2 I W)) at hc1
     have hx := run_one _ _ (exit_step false (stage2 I W) cm2)
     have hrun := run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hf1) hc1) hx
     refine ⟨_,by omega,false,clean (stage2 I W),hrun,?_⟩
     have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl1; omega
     have hi : stage2 I W 0=[] := by
       rw [si2]
       apply List.drop_eq_nil_of_le
       simp only [List.length_drop] at hl1
       omega
     refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
     all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
 · have hf0 := h0
   simp only [hl0,decide_false] at hf0
   have hc0 := run_one _ _ (check_step 0 false (stage1 I W))
   change run 1 (cfg (some 13) false (stage1 I W)) = some (cfg (some 17) false (stage1 I W)) at hc0
   have hx := run_one _ _ (exit_step false (stage1 I W) cm1)
   have hrun := run_comp (run_comp (run_comp he hf0) hc0) hx
   refine ⟨_,by omega,false,clean (stage1 I W),hrun,?_⟩
   have hlen : ¬2*W.length+4≤I.length := by omega
   have hi : stage1 I W 0=[] := by
     rw [si1]
     apply List.drop_eq_nil_of_le
     skip
     omega
   refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
   all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]

end PEqualNP.Outside.L_lib_895_aux.RecordMachine

namespace PEqualNP.Outside.L_lib_895_aux.RecordMachine
open Turing

def resultStacks (I W : List Bool) : Fin 9 → List Bool :=
 tapes (I.drop (2*W.length+4)) W [] []
   (I.take W.length) ((I.drop W.length).take 2)
   ((I.drop (W.length+2)).take W.length)
   ((I.drop (2*W.length+2)).take 2) []
lemma stage4_slices (I W : List Bool) : clean (stage4 I W)=resultStacks I W := by
 funext k
 fin_cases k <;>
 simp [resultStacks,clean,stage0,stage1,stage2,stage3,stage4,
   updated,tapes,field,marker,List.drop_drop,two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem record_success (I W : List Bool) (ha : 2*W.length+4≤I.length) :
 ∃ t ≤ 6*W.length+30,
 run t (initial I W)=some (cfg none true (resultStacks I W)) := by
 obtain ⟨t,ht,v,st,hr,hv,hW,h2,h3,h8,hs,hf⟩ := record_contract I W
 have he : v=true := by simpa [ha] using hv
 have heq := hs he
 rw [he,heq,stage4_slices] at hr
 exact ⟨t,ht,hr⟩

theorem machine_step_eq : machine.step=TM2.step program := rfl

theorem record_total_evals (I W : List Bool) :
 ∃ v st, Nonempty (StateTransition.EvalsToInTime machine.step
   (initial I W) (some (cfg none v st)) (6*W.length+30)) ∧ Finished I W v st := by
 obtain ⟨t,ht,v,st,hr,hf⟩ := record_contract I W
 refine ⟨v,st,?_,hf⟩
 rw [machine_step_eq]
 exact ⟨{steps := t, evals_in_steps := hr, steps_le_m := ht}⟩

theorem record_success_evals (I W : List Bool) (ha : 2*W.length+4≤I.length) :
 Nonempty (StateTransition.EvalsToInTime machine.step (initial I W)
   (some (cfg none true (resultStacks I W))) (6*W.length+30)) := by
 obtain ⟨t,ht,hr⟩ := record_success I W ha
 rw [machine_step_eq]
 exact ⟨{steps := t, evals_in_steps := hr, steps_le_m := ht}⟩

theorem record_failure_evals (I W : List Bool) (ha : I.length<2*W.length+4) :
 ∃ st, Nonempty (StateTransition.EvalsToInTime machine.step (initial I W)
   (some (cfg none false st)) (6*W.length+30)) ∧
 st 0=[] ∧ st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] := by
 obtain ⟨v,st,hr,hv,hW,h2,h3,h8,hs,hf⟩ := record_total_evals I W
 have hnot : ¬2*W.length+4≤I.length := by omega
 have he : v=false := by simpa [hnot] using hv
 rw [he] at hr
 exact ⟨st,hr,hf he,hW,h2,h3,h8⟩

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance
theorem state_count : Fintype.card S=6 := by decide
theorem label_count : Fintype.card (Fin 19)=19 := by decide
theorem stack_count : Fintype.card (Fin 9)=9 := by decide
end PEqualNP.Outside.L_lib_895_aux.RecordMachine

namespace PEqualNP.Outside.L_lib_895_aux.Compare
open Turing StateTransition

def value : List Bool → Nat
  | [] => 0
  | b::xs => (if b then 1 else 0)+2*value xs

def nextFlag (q a b : Bool) : Bool := bif a == b then q else b

def scan (q : Bool) : List Bool → List Bool → Bool
  | [], _ => q
  | a::xs, [] => scan (nextFlag q a false) xs []
  | a::xs,b::ys => scan (nextFlag q a b) xs ys

inductive K : Type
  | a | b | out
  deriving DecidableEq
instance : Fintype K := Fintype.ofList [.a,.b,.out] (fun k => by cases k <;> simp)
abbrev S := Option Bool × Bool
abbrev Γ (_ : K) := Bool
abbrev Cfg := TM2.Cfg Γ Unit S

def prog (_ : Unit) : TM2.Stmt Γ Unit S :=
  .pop .a (fun s a => (a,s.2))
    (.branch (fun s => s.1.isSome)
      (.pop .b (fun s b => (none,nextFlag s.2 (s.1.getD false) (b.getD false)))
        (.goto fun _ => ()))
      (.push .out (fun s => s.2)
        (.load (fun _ => (none,false)) .halt)))

abbrev machine : FinTM2 where
  K := K
  k₀ := .a
  k₁ := .out
  Γ := Γ
  Λ := Unit
  main := ()
  σ := S
  initialState := (none,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

def cmpSt (a b out : List Bool) : ∀ k, List (Γ k)
  | .a => a
  | .b => b
  | .out => out
lemma stacks_set_a (a a' b out : List Bool) :
    Function.update (cmpSt a b out) .a a' = cmpSt a' b out := by
  funext k; cases k <;> simp [cmpSt]
lemma stacks_set_b (a b b' out : List Bool) :
    Function.update (cmpSt a b out) .b b' = cmpSt a b' out := by
  funext k; cases k <;> simp [cmpSt]
lemma stacks_set_out (a b out out' : List Bool) :
    Function.update (cmpSt a b out) .out out' = cmpSt a b out' := by
  funext k; cases k <;> simp [cmpSt]

def running (q : Bool) (a b out : List Bool) : Cfg :=
  ⟨some (), (none,q), cmpSt a b out⟩
def finished (q : Bool) (out : List Bool) : Cfg :=
  ⟨none,(none,false),cmpSt [] [] (q::out)⟩

lemma step_cons (q a b : Bool) (xs ys out : List Bool) :
    (TM2.step prog) (running q (a::xs) (b::ys) out) =
      some (running (nextFlag q a b) xs ys out) := by
  simp [FinTM2.step,machine,TM2.step,prog,TM2.stepAux,running,cmpSt,
    stacks_set_a,stacks_set_b]
lemma step_nil (q : Bool) (out : List Bool) :
    (TM2.step prog) (running q [] [] out) = some (finished q out) := by
  simp [FinTM2.step,machine,TM2.step,prog,TM2.stepAux,running,finished,cmpSt,
    stacks_set_a,stacks_set_out]

lemma loop_run (a b : List Bool) (hlen : a.length=b.length) (q : Bool) (out : List Bool) :
    (flip bind (TM2.step prog))^[a.length+1] (some (running q a b out)) =
      some (finished (scan q a b) out) := by
  induction a generalizing b q with
  | nil =>
    cases b with
    | nil => exact step_nil q out
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length=ys.length := Nat.succ.inj hlen
      rw [List.length_cons,Function.iterate_succ_apply]
      have e : flip bind (TM2.step prog) (some (running q (x::xs) (y::ys) out)) =
          some (running (nextFlag q x y) xs ys out) := step_cons q x y xs ys out
      rw [e,ih ys ht (nextFlag q x y)]
      rfl

lemma scan_value (a b : List Bool) (hlen : a.length=b.length) (q : Bool) :
    scan q a b = decide (2*value a < 2*value b + (if q then 1 else 0)) := by
  induction a generalizing b q with
  | nil =>
    cases b with
    | nil => cases q <;> rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length=ys.length := Nat.succ.inj hlen
      rw [scan,ih ys ht]
      cases x <;> cases y <;> cases q
      all_goals
        apply Bool.decide_congr
        simp [nextFlag,value] <;> omega

lemma scan_false_value (a b : List Bool) (hlen : a.length=b.length) :
    scan false a b = decide (value a < value b) := by
  rw [scan_value a b hlen false]
  apply Bool.decide_congr
  simp <;> omega

def start (a b : List Bool) : Cfg := running false a b []
def finish (q : Bool) : Cfg := finished q []

theorem compare_run (a b : List Bool) (hlen : a.length=b.length) :
    (flip bind (TM2.step prog))^[a.length+1] (some (start a b)) =
      some (finish (decide (value a < value b))) := by
  simpa only[start,finish,scan_false_value a b hlen] using loop_run a b hlen false []

def compare_evals (a b : List Bool) (hlen : a.length=b.length) :
    EvalsToInTime (TM2.step prog) (start a b)
      (some (finish (decide (value a < value b)))) (a.length+1) where
  steps := a.length+1
  evals_in_steps := compare_run a b hlen
  steps_le_m := le_rfl

lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by
  intro j
  change Finite Bool
  infer_instance
lemma finite_state : Finite S := by infer_instance
lemma scratch_clean (q : Bool) :
    (finish q).stk K.a = [] ∧ (finish q).stk K.b = [] ∧ (finish q).stk K.out = [q] ∧
      (finish q).var = (none,false) := by
  exact ⟨rfl,rfl,rfl,rfl⟩
end PEqualNP.Outside.L_lib_895_aux.Compare

namespace PEqualNP.Outside.L_lib_895_aux.Compare
open Turing StateTransition

def halted (q : Bool) (b out : List Bool) : Cfg :=
  ⟨none,(none,false),cmpSt [] b (q::out)⟩
lemma step_empty (q : Bool) (b out : List Bool) :
    TM2.step prog (running q [] b out) = some (halted q b out) := by
  simp [TM2.step,prog,TM2.stepAux,running,halted,cmpSt,stacks_set_a,stacks_set_out]
lemma step_right_nil (q a : Bool) (xs out : List Bool) :
    TM2.step prog (running q (a::xs) [] out) =
      some (running (nextFlag q a false) xs [] out) := by
  simp [TM2.step,prog,TM2.stepAux,running,cmpSt,stacks_set_a,stacks_set_b]

theorem loop_run_any (a b : List Bool) (q : Bool) (out : List Bool) :
    (flip bind (TM2.step prog))^[a.length+1] (some (running q a b out)) =
      some (halted (scan q a b) (b.drop a.length) out) := by
  induction a generalizing b q with
  | nil => exact step_empty q b out
  | cons x xs ih =>
    cases b with
    | nil =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have e : flip bind (TM2.step prog) (some (running q (x::xs) [] out)) =
          some (running (nextFlag q x false) xs [] out) := step_right_nil q x xs out
      rw [e,ih [] (nextFlag q x false)]
      simp only[scan,List.drop_nil]
    | cons y ys =>
      rw [List.length_cons,Function.iterate_succ_apply]
      have e : flip bind (TM2.step prog) (some (running q (x::xs) (y::ys) out)) =
          some (running (nextFlag q x y) xs ys out) := step_cons q x y xs ys out
      rw [e,ih ys (nextFlag q x y)]
      simp only[scan,List.drop_succ_cons]

def total_evals (a b : List Bool) :
    EvalsToInTime (TM2.step prog) (start a b)
      (some (halted (scan false a b) (b.drop a.length) [])) (a.length+1) where
  steps := a.length+1
  evals_in_steps := loop_run_any a b false []
  steps_le_m := le_rfl

lemma machine_step_eq : machine.step = TM2.step prog := rfl

def compare_machine_evals (a b : List Bool) (hlen : a.length=b.length) :
    EvalsToInTime machine.step (start a b)
      (some (finish (decide (value a < value b)))) (a.length+1) := by
  change EvalsToInTime (TM2.step prog) (start a b)
    (some (finish (decide (value a < value b)))) (a.length+1)
  exact compare_evals a b hlen

lemma finite_state_size : Fintype.card S = 6 := by decide
lemma finite_stack_count : Fintype.card K = 3 := by decide
end PEqualNP.Outside.L_lib_895_aux.Compare

namespace PEqualNP.Outside.L_lib_895_aux.Compare
open Turing StateTransition
lemma value_wordValue (xs : List Bool) : value xs = wordValue xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only[value,wordValue,ih]

def compare_wordValue_evals (a b : List Bool) (hlen : a.length=b.length) :
    EvalsToInTime machine.step (start a b)
      (some (finish (decide (wordValue a < wordValue b)))) (a.length+1) := by
  simpa only[value_wordValue] using compare_machine_evals a b hlen

def compare_bits_evals (w a b : Nat) (ha : a<2^w) (hb : b<2^w) :
    EvalsToInTime machine.step (start (bits w a) (bits w b))
      (some (finish (decide (a<b)))) (w+1) := by
  have h := compare_wordValue_evals (bits w a) (bits w b) (by simp only[bits_length])
  simpa only[wordValue_bits w a ha,wordValue_bits w b hb,bits_length] using h
end PEqualNP.Outside.L_lib_895_aux.Compare

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
abbrev S := (Option Bool × Bool) × (Fin 4 × Fin 4)
abbrev H := Fin 19 ⊕ (Fin 4 × Copy.Label) ⊕ Fin 2 ⊕ Fin 10
abbrev Cfg := TM2.Cfg (fun _ : Fin 9 => Bool) H S
def rd (j : Fin 19) : H := .inl j
def cp (i : Fin 4) (j : Copy.Label) : H := .inr (.inl (i,j))
def cm (i : Fin 2) : H := .inr (.inr (.inl i))
def ph (i : Fin 10) : H := .inr (.inr (.inr i))
def dr : H → Option (Fin 19) | .inl j => some j | _ => none
def dc (i : Fin 4) : H → Option Copy.Label
 | .inr (.inl (k,j)) => if k=i then some j else none
 | _ => none
def dm (i : Fin 2) : H → Option Unit
 | .inr (.inr (.inl k)) => if k=i then some () else none
 | _ => none

def rls := CallLayout.optionSplit rd dr (by intro j;rfl) (by intro j k h;cases j <;> simp_all [dr,rd])
def cls (i : Fin 4) := CallLayout.optionSplit (cp i) (dc i)
 (by intro j;simp [dc,cp]) (by
  intro j k h
  rcases j with j | (⟨a,b⟩ | (j | j)) <;> simp_all [dc,cp])
def mls (i : Fin 2) := CallLayout.optionSplit (fun _ : Unit => cm i) (dm i)
 (by intro j;cases j;simp [dm,cm]) (by
  intro j k h
  rcases j with j | (⟨a,b⟩ | (j | j)) <;> simp_all [dm,cm])
def rks := CallLayout.optionSplit (id : Fin 9 → Fin 9) some
 (by intro k;rfl) (by intro j k h;simpa using (Option.some.inj h).symm)
def src (i : Fin 4) : Fin 9 := if i=0 then 4 else if i=3 then 1 else 6
def dst (i : Fin 4) : Fin 9 := if i.val % 2=0 then 2 else 3
def tmp (i : Fin 4) : Fin 9 := if i.val % 2=0 then 3 else 8
def ec (i : Fin 4) : Copy.Stack → Fin 9 | .A => src i | .B => dst i | .C => tmp i
def dk (i : Fin 4) (j : Fin 9) : Option Copy.Stack :=
 if j=src i then some .A else if j=dst i then some .B else if j=tmp i then some .C else none
def cks (i : Fin 4) := CallLayout.optionSplit (ec i) (dk i)
 (by intro k;fin_cases i <;> cases k <;> decide)
 (by intro j k h;fin_cases i <;> fin_cases j <;> cases k <;> revert h <;> decide)
def em : Compare.K → Fin 9 | .a => 2 | .b => 3 | .out => 8
def dmk (j : Fin 9) : Option Compare.K :=
 if j=2 then some .a else if j=3 then some .b else if j=8 then some .out else none
def mks := CallLayout.optionSplit em dmk
 (by intro k;cases k <;> decide)
 (by intro j k h;fin_cases j <;> cases k <;> revert h <;> decide)
def rss : S ≃ (Option Bool × Bool) × (Fin 4 × Fin 4) := Equiv.refl _
def css : S ≃ Option Bool × (Bool × (Fin 4 × Fin 4)) :=
 ⟨fun s => (s.1.1,(s.1.2,s.2)),fun s => ((s.1,s.2.1),s.2.2),by rintro ⟨⟨o,b⟩,cd⟩;rfl,by rintro ⟨o,b,cd⟩;rfl⟩
def rret : {j : H // dr j=none} := ⟨ph 0,rfl⟩
def cret (i : Fin 4) : {j : H // dc i j=none} :=
 ⟨ph (if i=0 then 3 else if i=1 then 4 else if i=2 then 6 else 7),rfl⟩
def mret (i : Fin 2) : {j : H // dm i j=none} := ⟨ph (if i=0 then 5 else 8),rfl⟩
def color (lo hi : Bool) : Fin 4 :=
 ⟨(if lo then 1 else 0)+2*(if hi then 1 else 0),by cases lo <;> cases hi <;> decide⟩
def setC (s : S) (hi : Option Bool) : S :=
 ((none,s.1.2),(color (s.1.1.getD false) (hi.getD false),s.2.2))
def setD (s : S) (hi : Option Bool) : S :=
 ((none,s.1.2),(s.2.1,color (s.1.1.getD false) (hi.getD false)))
def phaseProgram : Fin 10 → TM2.Stmt (fun _ : Fin 9 => Bool) H S
 | 0 => .branch (fun s => s.1.2) (.goto fun _ => ph 1) (.goto fun _ => ph 9)
 | 1 => .pop 5 (fun s o => ((o,s.1.2),s.2))
    (.pop 5 setC (.branch (fun s => decide (s.2.1.val<3))
      (.goto fun _ => ph 2) (.goto fun _ => ph 9)))
 | 2 => .pop 7 (fun s o => ((o,s.1.2),s.2))
    (.pop 7 setD (.branch (fun s => decide (s.2.2.val<3))
      (.goto fun _ => cp 0 .duplicate) (.goto fun _ => ph 9)))
 | 3 => .goto fun _ => cp 1 .duplicate
 | 4 => .load (fun s => ((none,false),s.2)) (.goto fun _ => cm 0)
 | 5 => .pop 8 (fun s o => ((o,s.1.2),s.2))
    (.branch (fun s => s.1.1.getD false)
      (.load (fun s => ((none,false),s.2)) (.goto fun _ => cp 2 .duplicate))
      (.goto fun _ => ph 9))
 | 6 => .goto fun _ => cp 3 .duplicate
 | 7 => .load (fun s => ((none,false),s.2)) (.goto fun _ => cm 1)
 | 8 => .pop 8 (fun s o => ((o,s.1.2),s.2))
    (.branch (fun s => s.1.1.getD false)
      (.load (fun s => ((none,true),s.2)) .halt) (.goto fun _ => ph 9))
 | _ => .load (fun s => ((none,false),s.2)) .halt

def program : H → TM2.Stmt (fun _ : Fin 9 => Bool) H S
 | .inl j => BoolCall.trStmt rks rls rss rret (RecordMachine.program j)
 | .inr (.inl (i,j)) => BoolCall.trStmt (cks i) (cls i) css (cret i) (Copy.program j)
 | .inr (.inr (.inl i)) => BoolCall.trStmt mks (mls i) rss (mret i) (Compare.prog ())
 | .inr (.inr (.inr i)) => phaseProgram i

def machine : FinTM2 where
 K := Fin 9
 k₀ := 0
 k₁ := 4
 Γ _ := Bool
 Λ := H
 main := rd 12
 σ := S
 initialState := ((none,true),(0,0))
 m := program

def cfg (l : Option H) (v : Bool) (c d : Fin 4) (st : Fin 9 → List Bool) : Cfg :=
 ⟨l,((none,v),(c,d)),st⟩
def run (t : Nat) (a : Cfg) := (flip bind (TM2.step program))^[t] (some a)
lemma run_one (a b : Cfg) (h : TM2.step program a=some b) : run 1 a=some b := h
lemma run_comp {s t : Nat} {a b c : Cfg}
 (h1 : run s a=some b) (h2 : run t b=some c) : run (s+t) a=some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]
lemma rbody (j : Fin 19) : program (rls.symm (.inl j))=BoolCall.trStmt rks rls rss rret (RecordMachine.program j) := rfl
lemma cbody (i : Fin 4) (j : Copy.Label) : program ((cls i).symm (.inl j))=BoolCall.trStmt (cks i) (cls i) css (cret i) (Copy.program j) := rfl
lemma mbody (i : Fin 2) (j : Unit) : program ((mls i).symm (.inl j))=BoolCall.trStmt mks (mls i) rss (mret i) (Compare.prog j) := by cases j;rfl
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def copyAfter (i : Fin 4) : Fin 10 := if i=0 then 3 else if i=1 then 4 else if i=2 then 6 else 7
def cmpAfter (i : Fin 2) : Fin 10 := if i=0 then 5 else 8

theorem reader_call (I W : List Bool) (c d : Fin 4) (ha : 2*W.length+4≤I.length) :
 ∃ t ≤ 6*W.length+30,
 run t (cfg (some (rd 12)) true c d (RecordMachine.tapes I W [] [] [] [] [] [] [])) =
 some (cfg (some (ph 0)) true c d (RecordMachine.resultStacks I W)) := by
 obtain ⟨t,ht,hr⟩ := RecordMachine.record_success I W ha
 have h := BoolCall.run_lift rks rls rss rret (c,d)
   (fun _ => []) RecordMachine.program program rbody t _ _ hr
 refine ⟨t,ht,?_⟩
 exact h

lemma copy_lift_start (i : Fin 4) (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4)
 (hd : st (dst i)=[]) (ht : st (tmp i)=[]) :
 BoolCall.liftCfg (cks i) (cls i) css (cret i) (b,(c,d))
   (fun e => st e.val) (Copy.startCfg (st (src i))) =
 cfg (some (cp i .duplicate)) b c d st := by
 change (⟨some (cp i .duplicate),((none,b),(c,d)),_⟩ : Cfg) =
   ⟨some (cp i .duplicate),((none,b),(c,d)),st⟩
 congr 1
 funext j
 change Sum.elim (Copy.copySt (st (src i)) [] []) (fun e => st e.val) (CallLayout.forward (dk i) j) = st j
 fin_cases i <;> fin_cases j <;>
 simp [BoolCall.liftStacks,cks,CallLayout.optionSplit,Equiv.coe_fn_mk,CallLayout.forward,
   dk,ec,src,dst,tmp,Copy.startCfg,Copy.cfg,Copy.copySt] at * <;> assumption

lemma copy_lift_end (i : Fin 4) (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4)
 (hd : st (dst i)=[]) (ht : st (tmp i)=[]) :
 BoolCall.liftCfg (cks i) (cls i) css (cret i) (b,(c,d))
   (fun e => st e.val) (Copy.endCfg (st (src i))) =
 cfg (some (ph (copyAfter i))) b c d (Function.update st (dst i) (st (src i))) := by
 change (⟨some (ph (copyAfter i)),((none,b),(c,d)),_⟩ : Cfg) =
   ⟨some (ph (copyAfter i)),((none,b),(c,d)),_⟩
 congr 1
 funext j
 change Sum.elim (Copy.copySt (st (src i)) (st (src i)) []) (fun e => st e.val) (CallLayout.forward (dk i) j) = (Function.update st (dst i) (st (src i))) j
 fin_cases i <;> fin_cases j <;>
 simp [BoolCall.liftStacks,cks,CallLayout.optionSplit,Equiv.coe_fn_mk,CallLayout.forward,
   dk,ec,src,dst,tmp,Copy.endCfg,Copy.cfg,Copy.copySt] at * <;> assumption

theorem copy_call (i : Fin 4) (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4)
 (hd : st (dst i)=[]) (ht : st (tmp i)=[]) :
 run (3*(st (src i)).length+3) (cfg (some (cp i .duplicate)) b c d st) =
 some (cfg (some (ph (copyAfter i))) b c d (Function.update st (dst i) (st (src i)))) := by
 have hr := Copy.copy_run (st (src i))
 have h := BoolCall.run_lift (cks i) (cls i) css (cret i) (b,(c,d))
   (fun e => st e.val) Copy.program program (cbody i) _ _ _ hr
 rw [copy_lift_start i st b c d hd ht,copy_lift_end i st b c d hd ht] at h
 exact h

def compared (st : Fin 9 → List Bool) :=
 Function.update (Function.update (Function.update st 2 []) 3 []) 8
   [decide (Compare.value (st 2)<Compare.value (st 3))]
lemma cmp_lift_start (i : Fin 2) (st : Fin 9 → List Bool) (c d : Fin 4) (he : st 8=[]) :
 BoolCall.liftCfg mks (mls i) rss (mret i) (c,d)
   (fun e => st e.val) (Compare.start (st 2) (st 3)) =
 cfg (some (cm i)) false c d st := by
 change (⟨some (cm i),((none,false),(c,d)),_⟩ : Cfg) =
   ⟨some (cm i),((none,false),(c,d)),st⟩
 congr 1
 funext j
 change Sum.elim (Compare.cmpSt (st 2) (st 3) []) (fun e => st e.val) (CallLayout.forward dmk j) = st j
 fin_cases j <;>
 simp [BoolCall.liftStacks,mks,CallLayout.optionSplit,Equiv.coe_fn_mk,CallLayout.forward,
   dmk,em,Compare.start,Compare.running,Compare.cmpSt,he]
lemma cmp_lift_end (i : Fin 2) (st : Fin 9 → List Bool) (c d : Fin 4) (he : st 8=[]) :
 BoolCall.liftCfg mks (mls i) rss (mret i) (c,d)
   (fun e => st e.val) (Compare.finish (decide (Compare.value (st 2)<Compare.value (st 3)))) =
 cfg (some (ph (cmpAfter i))) false c d (compared st) := by
 change (⟨some (ph (cmpAfter i)),((none,false),(c,d)),_⟩ : Cfg) =
   ⟨some (ph (cmpAfter i)),((none,false),(c,d)),_⟩
 congr 1
 funext j
 change Sum.elim (Compare.cmpSt [] [] [decide (Compare.value (st 2)<Compare.value (st 3))]) (fun e => st e.val) (CallLayout.forward dmk j) = compared st j
 fin_cases j <;>
 simp [BoolCall.liftStacks,mks,CallLayout.optionSplit,Equiv.coe_fn_mk,CallLayout.forward,
   dmk,em,Compare.finish,Compare.finished,Compare.cmpSt,compared]

theorem compare_call (i : Fin 2) (st : Fin 9 → List Bool) (c d : Fin 4)
 (hlen : (st 2).length=(st 3).length) (he : st 8=[]) :
 run ((st 2).length+1) (cfg (some (cm i)) false c d st) =
 some (cfg (some (ph (cmpAfter i))) false c d (compared st)) := by
 have h := BoolCall.run_lift mks (mls i) rss (mret i) (c,d)
   (fun e => st e.val) Compare.prog program (mbody i) _ _ _ (Compare.compare_run (st 2) (st 3) hlen)
 rw [cmp_lift_start i st c d he,cmp_lift_end i st c d he] at h
 exact h
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
def packet (A C B D R : List Bool) := A++(C++(B++(D++R)))
lemma packet_slices (A C B D R W : List Bool)
 (hA : A.length=W.length) (hB : B.length=W.length) (hC : C.length=2) (hD : D.length=2) :
 RecordMachine.resultStacks (packet A C B D R) W = RecordMachine.tapes R W [] [] A C B D [] := by
 have r0 : (packet A C B D R).drop W.length=C++(B++(D++R)) := List.drop_left' hA
 have r1 : (packet A C B D R).drop (W.length+2)=B++(D++R) := by
  rw [←List.drop_drop,r0]
  exact List.drop_left' hC
 have r2 : (packet A C B D R).drop (2*W.length+2)=D++R := by
  have he : 2*W.length+2=(W.length+2)+W.length := by omega
  rw [he,←List.drop_drop,r1]
  exact List.drop_left' hB
 have r3 : (packet A C B D R).drop (2*W.length+4)=R := by
  have he : 2*W.length+4=(2*W.length+2)+2 := by omega
  rw [he,←List.drop_drop,r2]
  exact List.drop_left' hD
 have t0 : (packet A C B D R).take W.length=A := List.take_left' hA
 have t1 : ((packet A C B D R).drop W.length).take 2=C := by rw [r0];exact List.take_left' hC
 have t2 : ((packet A C B D R).drop (W.length+2)).take W.length=B := by rw [r1];exact List.take_left' hB
 have t3 : ((packet A C B D R).drop (2*W.length+2)).take 2=D := by rw [r2];exact List.take_left' hD
 simp only [RecordMachine.resultStacks,r3,t0,t1,t2,t3]

theorem reader_packet (A B R W : List Bool) (c d : Fin 3)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 ∃ t ≤ 6*W.length+30,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg (some (ph 0)) true 0 0
   (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 d.val) [])) := by
 have hC : (bits 2 c.val).length=2 := bits_length _ _
 have hD : (bits 2 d.val).length=2 := bits_length _ _
 have ha : 2*W.length+4≤(packet A (bits 2 c.val) B (bits 2 d.val) R).length := by
  simp only [packet,List.length_append,hA,hB,hC,hD]
  omega
 obtain ⟨t,ht,hr⟩ := reader_call (packet A (bits 2 c.val) B (bits 2 d.val) R) W 0 0 ha
 rw [packet_slices A _ B _ R W hA hB hC hD] at hr
 exact ⟨t,ht,hr⟩
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
lemma b11 : Nat.testBit 1 1=false := by decide
lemma b20 : Nat.testBit 2 0=false := by decide
lemma b21 : Nat.testBit 2 1=true := by decide
abbrev asColor (c : Fin 3) : Fin 4 := ⟨c.val,by omega⟩
lemma colorC_step (c : Fin 3) (d : Fin 4)
 (I W WT FT FI FJ FD CM : List Bool) :
 TM2.step program (cfg (some (ph 1)) true 0 d
   (RecordMachine.tapes I W WT FT FI (bits 2 c.val) FJ FD CM)) =
 some (cfg (some (ph 2)) true (asColor c) d
   (RecordMachine.tapes I W WT FT FI [] FJ FD CM)) := by
 fin_cases c <;>
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,setC,color,
   bits,List.range_succ,RecordMachine.tapes,asColor,b11,b20,b21]
 all_goals congr 1
 all_goals funext k
 all_goals fin_cases k <;> rfl
lemma colorD_step (c : Fin 4) (d : Fin 3)
 (I W WT FT FI FJ CM : List Bool) :
 TM2.step program (cfg (some (ph 2)) true c 0
   (RecordMachine.tapes I W WT FT FI [] FJ (bits 2 d.val) CM)) =
 some (cfg (some (cp 0 .duplicate)) true c (asColor d)
   (RecordMachine.tapes I W WT FT FI [] FJ [] CM)) := by
 fin_cases d <;>
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,setD,color,
   bits,List.range_succ,RecordMachine.tapes,asColor,b11,b20,b21]
 all_goals congr 1
 all_goals funext k
 all_goals fin_cases k <;> rfl
lemma read_checked (st : Fin 9 → List Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 0)) true c d st)=
 some (cfg (some (ph 1)) true c d st) := rfl
lemma afterCopy0 (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 3)) b c d st)=
 some (cfg (some (cp 1 .duplicate)) b c d st) := rfl
lemma afterCopy1 (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 4)) b c d st)=
 some (cfg (some (cm 0)) false c d st) := rfl
lemma afterCopy2 (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 6)) b c d st)=
 some (cfg (some (cp 3 .duplicate)) b c d st) := rfl
lemma afterCopy3 (st : Fin 9 → List Bool) (b : Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 7)) b c d st)=
 some (cfg (some (cm 1)) false c d st) := rfl
lemma compare0_checked (st : Fin 9 → List Bool) (c d : Fin 4) (he : st 8=[true]) :
 TM2.step program (cfg (some (ph 5)) false c d st)=
 some (cfg (some (cp 2 .duplicate)) false c d (Function.update st 8 [])) := by
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,he]
lemma compare1_checked (st : Fin 9 → List Bool) (c d : Fin 4) (he : st 8=[true]) :
 TM2.step program (cfg (some (ph 8)) false c d st)=
 some (cfg none true c d (Function.update st 8 [])) := by
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,he]
lemma reject_step (st : Fin 9 → List Bool) (s : S) :
 TM2.step program (⟨some (ph 9),s,st⟩ : Cfg)=
 some (cfg none false s.2.1 s.2.2 st) := rfl
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
@[simp] lemma get0 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 0=I := rfl
@[simp] lemma get1 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 1=W := rfl
@[simp] lemma get2 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 2=WT := rfl
@[simp] lemma get3 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 3=FT := rfl
@[simp] lemma get4 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 4=FI := rfl
@[simp] lemma get5 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 5=FC := rfl
@[simp] lemma get6 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 6=FJ := rfl
@[simp] lemma get7 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 7=FD := rfl
@[simp] lemma get8 (I W WT FT FI FC FJ FD CM : List Bool) : RecordMachine.tapes I W WT FT FI FC FJ FD CM 8=CM := rfl
@[simp] lemma set2 (I W WT FT FI FC FJ FD CM : List Bool) (X : List Bool) : Function.update (RecordMachine.tapes I W WT FT FI FC FJ FD CM) 2 X=RecordMachine.tapes I W X FT FI FC FJ FD CM := by funext j;fin_cases j <;> rfl
@[simp] lemma set3 (I W WT FT FI FC FJ FD CM : List Bool) (X : List Bool) : Function.update (RecordMachine.tapes I W WT FT FI FC FJ FD CM) 3 X=RecordMachine.tapes I W WT X FI FC FJ FD CM := by funext j;fin_cases j <;> rfl
@[simp] lemma set8 (I W WT FT FI FC FJ FD CM : List Bool) (X : List Bool) : Function.update (RecordMachine.tapes I W WT FT FI FC FJ FD CM) 8 X=RecordMachine.tapes I W WT FT FI FC FJ FD X := by funext j;fin_cases j <;> rfl
@[simp] lemma compared_tapes (I W A B FI FC FJ FD : List Bool) :
 compared (RecordMachine.tapes I W A B FI FC FJ FD [])=
 RecordMachine.tapes I W [] [] FI FC FJ FD [decide (Compare.value A<Compare.value B)] := by simp [compared];rfl
theorem legal_record_run (A B R W : List Bool) (c d : Fin 3)
 (hA : A.length=W.length) (hB : B.length=W.length)
 (hij : Compare.value A<Compare.value B) (hjn : Compare.value B<Compare.value W) :
 ∃ t ≤ 30*W.length+100,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg none true (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) := by
 obtain ⟨t,ht,hr⟩ := reader_packet A B R W c d hA hB
 have hread := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 d.val) []) 0 0)
 have hC := run_one _ _ (colorC_step c 0 R W [] [] A B (bits 2 d.val) [])
 have hD := run_one _ _ (colorD_step (asColor c) d R W [] [] A B [])
 have hc0 : run (3*A.length+3) (cfg (some (cp 0 .duplicate)) true (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) =
   some (cfg (some (ph 3)) true (asColor c) (asColor d) (RecordMachine.tapes R W A [] A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 0 (RecordMachine.tapes R W [] [] A [] B [] []) true (asColor c) (asColor d) (by rfl) (by rfl)
 have hc1 : run (3*B.length+3) (cfg (some (cp 1 .duplicate)) true (asColor c) (asColor d) (RecordMachine.tapes R W A [] A [] B [] [])) =
   some (cfg (some (ph 4)) true (asColor c) (asColor d) (RecordMachine.tapes R W A B A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 1 (RecordMachine.tapes R W A [] A [] B [] []) true (asColor c) (asColor d) (by rfl) (by rfl)
 have hc2 : run (3*B.length+3) (cfg (some (cp 2 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) =
   some (cfg (some (ph 6)) false (asColor c) (asColor d) (RecordMachine.tapes R W B [] A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 2 (RecordMachine.tapes R W [] [] A [] B [] []) false (asColor c) (asColor d) (by rfl) (by rfl)
 have hc3 : run (3*W.length+3) (cfg (some (cp 3 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W B [] A [] B [] [])) =
   some (cfg (some (ph 7)) false (asColor c) (asColor d) (RecordMachine.tapes R W B W A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 3 (RecordMachine.tapes R W B [] A [] B [] []) false (asColor c) (asColor d) (by rfl) (by rfl)
 have hp3 := run_one _ _ (afterCopy0 (RecordMachine.tapes R W A [] A [] B [] []) true (asColor c) (asColor d))
 have hp4 := run_one _ _ (afterCopy1 (RecordMachine.tapes R W A B A [] B [] []) true (asColor c) (asColor d))
 have hp6 := run_one _ _ (afterCopy2 (RecordMachine.tapes R W B [] A [] B [] []) false (asColor c) (asColor d))
 have hp7 := run_one _ _ (afterCopy3 (RecordMachine.tapes R W B W A [] B [] []) false (asColor c) (asColor d))
 have hm0 : run (A.length+1) (cfg (some (cm 0)) false (asColor c) (asColor d) (RecordMachine.tapes R W A B A [] B [] [])) =
   some (cfg (some (ph 5)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) := by
   simpa [cmpAfter,hij] using compare_call 0 (RecordMachine.tapes R W A B A [] B [] []) (asColor c) (asColor d) (by simp [hA,hB]) (by rfl)
 have hm1 : run (B.length+1) (cfg (some (cm 1)) false (asColor c) (asColor d) (RecordMachine.tapes R W B W A [] B [] [])) =
   some (cfg (some (ph 8)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) := by
   simpa [cmpAfter,hjn] using compare_call 1 (RecordMachine.tapes R W B W A [] B [] []) (asColor c) (asColor d) (by simp [hB]) (by rfl)
 have hp5 : run 1 (cfg (some (ph 5)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) =
   some (cfg (some (cp 2 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) := by
   simpa using run_one _ _ (compare0_checked (RecordMachine.tapes R W [] [] A [] B [] [true]) (asColor c) (asColor d) (by rfl))
 have hp8 : run 1 (cfg (some (ph 8)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) =
   some (cfg none true (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) := by
   simpa using run_one _ _ (compare1_checked (RecordMachine.tapes R W [] [] A [] B [] [true]) (asColor c) (asColor d) (by rfl))
 have hrun := (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp hr hread) hC) hD) hc0) hp3) hc1) hp4) hm0) hp5) hc2) hp6) hc3) hp7) hm1) hp8)
 refine ⟨_,?_,hrun⟩
 omega
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def initial (I W : List Bool) : Cfg :=
 cfg (some (rd 12)) true 0 0 (RecordMachine.tapes I W [] [] [] [] [] [] [])
def legalEnd (n : Nat) (e : Ban) (hl : legalRecord n e) (R : List Bool) : Cfg :=
 cfg none true ⟨e.1.2,by have := hl.2.2.1;omega⟩ ⟨e.2.2,by have := hl.2.2.2;omega⟩
   (RecordMachine.tapes R (bits (width n) n) [] []
     (bits (width n) e.1.1) [] (bits (width n) e.2.1) [] [])

theorem legal_encoded_run (n : Nat) (e : Ban) (hl : legalRecord n e) (R : List Bool) :
 ∃ t ≤ 30*width n+100,
 run t (initial (recordBits n e++R) (bits (width n) n))=some (legalEnd n e hl R) := by
 rcases e with ⟨⟨i,c⟩,⟨j,d⟩⟩
 obtain ⟨hij,hjn,hc,hd⟩ := hl
 have hn : n<2^(width n) := Nat.lt_log2_self
 have hi : i<2^(width n) := lt_trans (lt_trans hij hjn) hn
 have hj : j<2^(width n) := lt_trans hjn hn
 have hvalI : Compare.value (bits (width n) i)=i := by rw [Compare.value_wordValue,wordValue_bits _ _ hi]
 have hvalJ : Compare.value (bits (width n) j)=j := by rw [Compare.value_wordValue,wordValue_bits _ _ hj]
 have hvalN : Compare.value (bits (width n) n)=n := by rw [Compare.value_wordValue,wordValue_bits _ _ hn]
 have hr := legal_record_run (bits (width n) i) (bits (width n) j) R (bits (width n) n)
   ⟨c,hc⟩ ⟨d,hd⟩ (by simp only [bits_length]) (by simp only [bits_length])
   (by simpa only [hvalI,hvalJ] using hij) (by simpa only [hvalJ,hvalN] using hjn)
 simpa [initial,legalEnd,asColor,packet,recordBits,List.append_assoc,bits_length] using hr

theorem machine_step_eq : machine.step=TM2.step program := rfl

theorem legal_encoded_evals (n : Nat) (e : Ban) (hl : legalRecord n e) (R : List Bool) :
 Nonempty (StateTransition.EvalsToInTime machine.step
   (initial (recordBits n e++R) (bits (width n) n))
   (some (legalEnd n e hl R)) (30*width n+100)) := by
 obtain ⟨t,ht,hr⟩ := legal_encoded_run n e hl R
 rw [machine_step_eq]
 exact ⟨{steps:=t,evals_in_steps:=hr,steps_le_m:=ht}⟩

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k
 change Finite Bool
 infer_instance
theorem finite_labels : Finite machine.Λ := by change Finite H;infer_instance
theorem finite_state : Finite machine.σ := by change Finite S;infer_instance
theorem state_count : Fintype.card S=96 := by decide
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.BanMachine
open Turing
abbrev Color := Fin 3 × Fin 3
abbrev Stack := TemplateMachine.Stack
abbrev Label := (Color × TemplateMachine.Label) ⊕ Unit
abbrev State := Option Bool × Fin 5
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label State

def ks : Stack ≃ Stack ⊕ Empty where
  toFun := Sum.inl
  invFun x := x.elim id Empty.elim
  left_inv _ := rfl
  right_inv x := by cases x with | inl x => rfl | inr x => cases x

def ss : State ≃ State × Unit where
  toFun s := (s,())
  invFun := Prod.fst
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨s,u⟩; cases u; rfl

def encode (c : Color) (l : TemplateMachine.Label) : Label := .inl (c,l)
def decode (c : Color) : Label → Option TemplateMachine.Label
  | .inl (d,l) => if d=c then some l else none
  | .inr _ => none

lemma decode_encode (c : Color) (l : TemplateMachine.Label) : decode c (encode c l) = some l := by
  simp [decode,encode]
lemma encode_decode (c : Color) (j : Label) (l : TemplateMachine.Label)
    (h : decode c j = some l) : encode c l = j := by
  cases j with
  | inr u => simp [decode] at h
  | inl p =>
    rcases p with ⟨d,l'⟩
    by_cases hd : d=c
    · subst d
      simp [decode] at h
      subst l'
      rfl
    · simp [decode,hd] at h

def ls (c : Color) : Label ≃ TemplateMachine.Label ⊕ {j : Label // decode c j = none} :=
  CallLayout.optionSplit (encode c) (decode c) (decode_encode c) (encode_decode c)

def ret (c : Color) : {j : Label // decode c j = none} := ⟨.inr (),rfl⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .inl (c,l) => BoolCall.trStmt ks (ls c) ss (ret c)
      (TemplateMachine.program (TemplateSpec.banTemplate c.1 c.2) l)
  | .inr _ => .halt

def machine : FinTM2 where
  K := Stack
  k₀ := .A
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .inl ((0,0),.phase)
  σ := State
  initialState := (none,0)
  m := program

def cfg (l : Option Label) (a b r : List Bool) : Cfg :=
  ⟨l,(none,0),TemplateMachine.stk a b [] r⟩

def start (c : Color) (a b r : List Bool) : Cfg := cfg (some (.inl (c,.phase))) a b r
def stop (a b r : List Bool) : Cfg := cfg (some (.inr ())) a b r
def finish (a b r : List Bool) : Cfg := cfg none a b r

lemma program_match (c : Color) (l : TemplateMachine.Label) :
    program ((ls c).symm (.inl l)) = BoolCall.trStmt ks (ls c) ss (ret c)
      (TemplateMachine.program (TemplateSpec.banTemplate c.1 c.2) l) := by
  rfl

lemma lift_start (c : Color) (a b r : List Bool) :
    BoolCall.liftCfg ks (ls c) ss (ret c) () Empty.elim
      (TemplateMachine.startCfg (TemplateSpec.banTemplate c.1 c.2) a b r) = start c a b r := by
  rfl

lemma lift_end (c : Color) (a b r : List Bool) :
    BoolCall.liftCfg ks (ls c) ss (ret c) () Empty.elim
      (TemplateMachine.endCfg (TemplateSpec.banTemplate c.1 c.2) a b r) =
      stop a b ((TemplateMachine.stream (TemplateSpec.banTemplate c.1 c.2) a b).reverse++r) := by
  rfl

lemma stop_step (a b r : List Bool) : TM2.step program (stop a b r) = some (finish a b r) := rfl

theorem ban_run (c : Color) (a b r : List Bool) :
    (flip bind (TM2.step program))^[TemplateMachine.cost (TemplateSpec.banTemplate c.1 c.2) a b+2]
      (some (start c a b r)) =
      some (finish a b ((TemplateMachine.stream (TemplateSpec.banTemplate c.1 c.2) a b).reverse++r)) := by
  have h := BoolCall.run_lift ks (ls c) ss (ret c) () Empty.elim
    (TemplateMachine.program (TemplateSpec.banTemplate c.1 c.2)) program (program_match c)
    _ _ _ (TemplateMachine.template_run (TemplateSpec.banTemplate c.1 c.2) a b r)
  rw [lift_start,lift_end] at h
  rw [show TemplateMachine.cost (TemplateSpec.banTemplate c.1 c.2) a b+2 =
    1+(TemplateMachine.cost (TemplateSpec.banTemplate c.1 c.2) a b+1) by omega,
    Function.iterate_add_apply,h]
  exact stop_step _ _ _

lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by
  intro j
  change Finite Bool
  infer_instance

theorem ban_bits_run (n i j : Nat) (c d : Fin 3) (R : List Bool) (hn : 2 ≤ n) :
    (flip bind (TM2.step program))^[4*(2*width n+4)+2]
      (some (start (c,d) (bits (width n) i) (bits (width n) j) R)) =
      some (finish (bits (width n) i) (bits (width n) j)
        (((PEqualNP.Outside.L_lib_895_aux.Comb.flag i c.val ++ PEqualNP.Outside.L_lib_895_aux.Comb.flag j d.val).flatMap
          (bits (width (8*n+1)))).reverse++R)) := by
  have h := ban_run (c,d) (bits (width n) i) (bits (width n) j) R
  have hc := TemplateReady.cost_equal_width (TemplateSpec.banTemplate c d)
    (bits (width n) i) (bits (width n) j) (width n) (bits_length _ _) (bits_length _ _)
  rw [TemplateSpec.banTemplate_length] at hc
  rw [hc,TemplateReady.stream_eq,←TemplateSpec.ban_stream n i j c d hn] at h
  exact h

def ban_bits_evals (n i j : Nat) (c d : Fin 3) (R : List Bool) (hn : 2 ≤ n) :
    StateTransition.EvalsToInTime (TM2.step program)
      (start (c,d) (bits (width n) i) (bits (width n) j) R)
      (some (finish (bits (width n) i) (bits (width n) j)
        (((PEqualNP.Outside.L_lib_895_aux.Comb.flag i c.val ++ PEqualNP.Outside.L_lib_895_aux.Comb.flag j d.val).flatMap
          (bits (width (8*n+1)))).reverse++R))) (4*(2*width n+4)+2) where
  steps := 4*(2*width n+4)+2
  evals_in_steps := ban_bits_run n i j c d R hn
  steps_le_m := le_rfl

end PEqualNP.Outside.L_lib_895_aux.BanMachine

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine
open Turing
abbrev S := RecordValid.S × Fin 5
abbrev H := RecordValid.H ⊕ BanMachine.Label ⊕ Fin 2 ⊕ Fin 6
abbrev Cfg := TM2.Cfg (fun _ : Fin 10 => Bool) H S

def rv (j : RecordValid.H) : H := .inl j
def bn (j : BanMachine.Label) : H := .inr (.inl j)
def cl (i : Fin 2) : H := .inr (.inr (.inl i))
def ph (i : Fin 6) : H := .inr (.inr (.inr i))

def dr : H → Option RecordValid.H | .inl j => some j | _ => none
def db : H → Option BanMachine.Label | .inr (.inl j) => some j | _ => none
def dc (i : Fin 2) : H → Option Unit
  | .inr (.inr (.inl j)) => if j=i then some () else none
  | _ => none

def rls := CallLayout.optionSplit rv dr (by intro j;rfl)
  (by intro j k h; rcases j with j | (j | (j | j)) <;> simp_all [dr,rv])
def bls := CallLayout.optionSplit bn db (by intro j;rfl)
  (by intro j k h; rcases j with j | (j | (j | j)) <;> simp_all [db,bn])
def cls (i : Fin 2) := CallLayout.optionSplit (fun _ : Unit => cl i) (dc i)
  (by intro j;cases j;simp [dc,cl])
  (by intro j k h;rcases j with j | (j | (j | j)) <;> simp_all [dc,cl])

def er (k : Fin 9) : Fin 10 := k.castSucc
def dkr (j : Fin 10) : Option (Fin 9) := if h : j.val<9 then some ⟨j.val,h⟩ else none
def rks := CallLayout.optionSplit er dkr
  (by intro k;fin_cases k <;> decide)
  (by intro j k h;fin_cases j <;> fin_cases k <;> revert h <;> decide)

def eb : BanMachine.Stack → Fin 10
  | .A => 4 | .B => 6 | .temp => 2 | .output => 9
def dkb (j : Fin 10) : Option BanMachine.Stack :=
  if j=4 then some .A else if j=6 then some .B else if j=2 then some .temp
  else if j=9 then some .output else none
def bks := CallLayout.optionSplit eb dkb
  (by intro k;cases k <;> decide)
  (by intro j k h;fin_cases j <;> cases k <;> revert h <;> decide)

def field (i : Fin 2) : Fin 10 := if i=0 then 4 else 6
def dkc (i : Fin 2) (j : Fin 10) : Option Unit := if j=field i then some () else none
def cks (i : Fin 2) := CallLayout.optionSplit (fun _ : Unit => field i) (dkc i)
  (by intro k;cases k;simp [dkc])
  (by intro j k h;cases k;simp only [dkc] at h;split at h <;> simp_all)

def rss : S ≃ RecordValid.S × Fin 5 := Equiv.refl _
def bss : S ≃ BanMachine.State × (Bool × (Fin 4 × Fin 4)) where
  toFun s := ((s.1.1.1,s.2),(s.1.1.2,s.1.2))
  invFun s := (((s.1.1,s.2.1),s.2.2),s.1.2)
  left_inv s := by rcases s with ⟨⟨⟨o,b⟩,cd⟩,cur⟩;rfl
  right_inv s := by rcases s with ⟨⟨o,cur⟩,b,cd⟩;rfl
def css : S ≃ Bool × (Option Bool × ((Fin 4 × Fin 4) × Fin 5)) where
  toFun s := (s.1.1.2,(s.1.1.1,(s.1.2,s.2)))
  invFun s := (((s.2.1,s.1),s.2.2.1),s.2.2.2)
  left_inv s := by rcases s with ⟨⟨⟨o,b⟩,cd⟩,cur⟩;rfl
  right_inv s := by rcases s with ⟨b,o,cd,cur⟩;rfl

def rret : {j : H // dr j=none} := ⟨ph 1,rfl⟩
def bret : {j : H // db j=none} := ⟨ph 2,rfl⟩
def cret (i : Fin 2) : {j : H // dc i j=none} := ⟨ph (if i=0 then 3 else 4),rfl⟩

def initialState : S := (((none,true),(0,0)),0)
def failureState : S := (((none,false),(0,0)),0)
def color3 (c : Fin 4) : Fin 3 := ⟨c.val % 3,Nat.mod_lt _ (by decide)⟩

def phaseProgram : Fin 6 → TM2.Stmt (fun _ : Fin 10 => Bool) H S
  | 0 => .peek 0 (fun s o => (((o,s.1.1.2),s.1.2),s.2))
      (.branch (fun s => s.1.1.1.isSome)
        (.load (fun _ => initialState) (.goto fun _ => rv (RecordValid.rd 12)))
        (.load (fun _ => initialState) .halt))
  | 1 => .branch (fun s => s.1.1.2)
      (.goto fun s => bn (BanMachine.encode (color3 s.1.2.1,color3 s.1.2.2) .phase))
      (.goto fun _ => ph 5)
  | 2 => .load (fun s => (((none,false),s.1.2),s.2)) (.goto fun _ => cl 0)
  | 3 => .goto fun _ => cl 1
  | 4 => .load (fun _ => initialState) (.goto fun _ => ph 0)
  | _ => .load (fun _ => failureState) .halt

def program : H → TM2.Stmt (fun _ : Fin 10 => Bool) H S
  | .inl j => BoolCall.trStmt rks rls rss rret (RecordValid.program j)
  | .inr (.inl j) => BoolCall.trStmt bks bls bss bret (BanMachine.program j)
  | .inr (.inr (.inl i)) => BoolCall.trStmt (cks i) (cls i) css (cret i) (Clear.prog (α:=Bool) ())
  | .inr (.inr (.inr i)) => phaseProgram i

def machine : FinTM2 where
  K := Fin 10
  k₀ := 0
  k₁ := 9
  Γ _ := Bool
  Λ := H
  main := ph 0
  σ := S
  initialState := initialState
  m := program

def cfg (l : Option H) (s : S) (st : Fin 10 → List Bool) : Cfg := ⟨l,s,st⟩
def run (t : Nat) (c : Cfg) := (flip bind (TM2.step program))^[t] (some c)
lemma run_comp {s t : Nat} {a b c : Cfg} (h1 : run s a=some b) (h2 : run t b=some c) :
    run (s+t) a=some c := by
  unfold run at *
  rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]
lemma rbody (j : RecordValid.H) : program (rls.symm (.inl j)) =
    BoolCall.trStmt rks rls rss rret (RecordValid.program j) := rfl
lemma bbody (j : BanMachine.Label) : program (bls.symm (.inl j)) =
    BoolCall.trStmt bks bls bss bret (BanMachine.program j) := rfl
lemma cbody (i : Fin 2) (j : Unit) : program ((cls i).symm (.inl j)) =
    BoolCall.trStmt (cks i) (cls i) css (cret i) (Clear.prog (α:=Bool) j) := by cases j;rfl

lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by
  intro j
  change Finite Bool
  infer_instance

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.ClearAll
open Turing

abbrev Cfg (N : Nat) := TM2.Cfg (fun _ : Fin N => Bool) (Fin (N+1)) Bool

def cfg {N : Nat} (l : Option (Fin (N+1))) (S : Fin N → List Bool) : Cfg N := ⟨l,false,S⟩

def program (N : Nat) (q : Fin (N+1)) : TM2.Stmt (fun _ : Fin N => Bool) (Fin (N+1)) Bool :=
  if h : q.val < N then
    .pop ⟨q.val,h⟩ (fun _ o => o.isSome)
      (.branch id
        (.load (fun _ => false) (.goto fun _ => q))
        (.load (fun _ => false) (.goto fun _ => ⟨q.val+1,by omega⟩)))
  else .halt

def next {N : Nat} (k : Fin N) : Fin (N+1) := ⟨k.val+1,by omega⟩

lemma pop_cons {N : Nat} (k : Fin N) (S : Fin N → List Bool) (b : Bool) (xs : List Bool)
    (h : S k = b::xs) :
    TM2.step (program N) (cfg (some k.castSucc) S) =
      some (cfg (some k.castSucc) (Function.update S k xs)) := by
  simp [TM2.step,TM2.stepAux,program,cfg,k.isLt,h]

lemma pop_nil {N : Nat} (k : Fin N) (S : Fin N → List Bool) (h : S k = []) :
    TM2.step (program N) (cfg (some k.castSucc) S) =
      some (cfg (some (next k)) (Function.update S k [])) := by
  simp [TM2.step,TM2.stepAux,program,cfg,k.isLt,h,next]

lemma final_step {N : Nat} (S : Fin N → List Bool) :
    TM2.step (program N) (cfg (some (Fin.last N)) S) = some (cfg none S) := by
  simp [TM2.step,TM2.stepAux,program,cfg]

def run {N : Nat} (t : Nat) (c : Cfg N) : Option (Cfg N) :=
  (fun s : Option (Cfg N) => s.bind (TM2.step (program N)))^[t] (some c)

lemma run_comp {N s t : Nat} {a b c : Cfg N}
    (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
  unfold run at *
  rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]

lemma clear_one {N : Nat} (k : Fin N) (xs : List Bool) :
    ∀ S : Fin N → List Bool, S k = xs →
      run (xs.length+1) (cfg (some k.castSucc) S) =
        some (cfg (some (next k)) (Function.update S k [])) := by
  induction xs with
  | nil =>
    intro S hS
    simpa only [run,List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some] using pop_nil k S hS
  | cons b xs ih =>
    intro S hS
    have hpop := pop_cons k S b xs hS
    have hr := ih (Function.update S k xs) (by simp)
    unfold run
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [Option.bind_some,hpop]
    simpa only [run,Function.update_idem] using hr

def before {N : Nat} (i : Nat) (S : Fin N → List Bool) : Fin N → List Bool :=
  fun k => if k.val < i then [] else S k

lemma before_current {N : Nat} (i : Nat) (hi : i<N) (S : Fin N → List Bool) :
    before i S ⟨i,hi⟩ = S ⟨i,hi⟩ := by simp [before]

lemma before_update {N : Nat} (i : Nat) (hi : i<N) (S : Fin N → List Bool) :
    Function.update (before i S) ⟨i,hi⟩ [] = before (i+1) S := by
  funext k
  by_cases hk : k = ⟨i,hi⟩
  · subst k
    simp [before]
  · rw [Function.update_of_ne hk]
    have hv : k.val ≠ i := fun h => hk (Fin.ext h)
    have he : k.val < i ↔ k.val < i+1 := by omega
    simp only [before,he]

lemma before_zero {N : Nat} (S : Fin N → List Bool) : before 0 S = S := by
  funext k
  simp [before]

lemma before_all {N : Nat} (S : Fin N → List Bool) : before N S = fun _ => [] := by
  funext k
  simp [before,k.isLt]

def cost {N : Nat} (S : Fin N → List Bool) (i : Nat) : Nat → Nat
  | 0 => 1
  | m+1 => if h : i<N then (S ⟨i,h⟩).length+1+cost S (i+1) m else 1

theorem suffix_run {N : Nat} (S : Fin N → List Bool) (m : Nat) :
    ∀ (i : Nat) (hi : i+m=N),
      run (cost S i m) (cfg (some ⟨i,by omega⟩) (before i S)) =
        some (cfg none (fun _ => [])) := by
  induction m with
  | zero =>
    intro i hi
    have he : i=N := by omega
    subst i
    simp only [cost,before_all]
    exact final_step _
  | succ m ih =>
    intro i hi
    have hil : i<N := by omega
    have hnext : i+1+m=N := by omega
    have hc := clear_one (⟨i,hil⟩ : Fin N) (S ⟨i,hil⟩) (before i S) (before_current i hil S)
    rw [before_update i hil S] at hc
    have hr := ih (i+1) hnext
    have hh := run_comp hc hr
    simp only [cost,dif_pos hil,next]
    exact hh

lemma cost_bound {N : Nat} (S : Fin N → List Bool) (L : Nat) (hL : ∀ k, (S k).length≤L)
    (i m : Nat) : cost S i m ≤ m*(L+1)+1 := by
  induction m generalizing i with
  | zero => simp [cost]
  | succ m ih =>
    simp only [cost]
    split
    · have hh := ih (i+1)
      have hs := hL ⟨i,by assumption⟩
      nlinarith
    · omega

theorem clear_all_run {N : Nat} (S : Fin N → List Bool) :
    run (cost S 0 N) (cfg (some 0) S) = some (cfg none (fun _ => [])) := by
  have h := suffix_run S N 0 (by omega)
  rw [before_zero] at h
  exact h

def machine (N : Nat) (k₀ k₁ : Fin N) : FinTM2 where
  K := Fin N
  k₀ := k₀
  k₁ := k₁
  Γ _ := Bool
  Λ := Fin (N+1)
  main := 0
  σ := Bool
  initialState := false
  m := program N

lemma finite_alphabets (N : Nat) (k₀ k₁ : Fin N) : ∀ j, Finite ((machine N k₀ k₁).Γ j) := by
  intro j
  change Finite Bool
  infer_instance

end PEqualNP.Outside.L_lib_895_aux.ClearAll

namespace PEqualNP.Outside.L_lib_895_aux.Finisher
open Turing
inductive Label where
 | success | abort | rev (l : Unit) | good (l : Fin 11) | bad (l : Fin 12) | done
 deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.success,.abort,.rev (),.good 0,.good 1,.good 2,.good 3,.good 4,.good 5,.good 6,.good 7,.good 8,.good 9,.good 10,.bad 0,.bad 1,.bad 2,.bad 3,.bad 4,.bad 5,.bad 6,.bad 7,.bad 8,.bad 9,.bad 10,.bad 11,.done] (by
 intro l; cases l with
 | good k => fin_cases k <;> simp
 | bad k => fin_cases k <;> simp
 | rev k => cases k; simp
 | _ => simp)
abbrev State := Option Bool × Bool
abbrev Cfg := TM2.Cfg (fun _ : Fin 11 => Bool) Label State
def cfg (l : Option Label) (S : Fin 11 → List Bool) : Cfg := ⟨l,(none,false),S⟩
def join (Q : Fin 10 → List Bool) (R : List Bool) : Fin 11 → List Bool :=
 fun j => if h : j.val<10 then Q ⟨j.val,h⟩ else R

def revK : ReverseMove.Stack → Fin 11 | .source => 9 | .output => 10
def revKD (j : Fin 11) : Option ReverseMove.Stack :=
 if j=9 then some .source else if j=10 then some .output else none
def revKS := CallLayout.optionSplit revK revKD
 (by intro k; cases k <;> rfl)
 (by intro j k h; fin_cases j <;> cases k <;> simp_all [revKD,revK])
def goodKS : Fin 11 ≃ Fin 10 ⊕ Fin 1 := (finSumFinEquiv (m := 10) (n := 1)).symm
def badKS := CallLayout.optionSplit (fun k : Fin 11 => k) some
 (by intro k; rfl) (by intro j k h; exact (Option.some.inj h).symm)

def revLD : Label → Option (Unit) | .rev k => some k | _ => none
def revLS := CallLayout.optionSplit Label.rev revLD
 (by intro k; rfl) (by intro j k h; cases j <;> simp_all [revLD])
def revRet : {j : Label // revLD j=none} := ⟨.good 0,rfl⟩

def goodLD : Label → Option (Fin 11) | .good k => some k | _ => none
def goodLS := CallLayout.optionSplit Label.good goodLD
 (by intro k; rfl) (by intro j k h; cases j <;> simp_all [goodLD])
def goodRet : {j : Label // goodLD j=none} := ⟨.done,rfl⟩

def badLD : Label → Option (Fin 12) | .bad k => some k | _ => none
def badLS := CallLayout.optionSplit Label.bad badLD
 (by intro k; rfl) (by intro j k h; cases j <;> simp_all [badLD])
def badRet : {j : Label // badLD j=none} := ⟨.done,rfl⟩

def program : Label → TM2.Stmt (fun _ : Fin 11 => Bool) Label State
 | .success => .load (fun _ => (none,false)) (.goto fun _ => .rev ())
 | .abort => .load (fun _ => (none,false)) (.goto fun _ => .bad 0)
 | .rev l => BoolCall.trStmt revKS revLS (Equiv.refl State) revRet (ReverseMove.program l)
 | .good l => BoolCall.trStmt goodKS goodLS (Equiv.prodComm (Option Bool) Bool) goodRet (ClearAll.program 10 l)
 | .bad l => BoolCall.trStmt badKS badLS (Equiv.prodComm (Option Bool) Bool) badRet (ClearAll.program 11 l)
 | .done => .load (fun _ => (none,false)) .halt

def machine : FinTM2 where
 K := Fin 11
 k₀ := 0
 k₁ := 10
 Γ _ := Bool
 Λ := Label
 main := .success
 σ := State
 initialState := (none,false)
 m := program

def run (t : Nat) (c : Cfg) : Option Cfg :=
 (fun s : Option Cfg => s.bind (TM2.step program))^[t] (some c)
lemma run_one (c d : Cfg) (h : TM2.step program c = some d) : run 1 c = some d := by
 simpa only [run,Function.iterate_one,Option.bind_some] using h
lemma run_comp {s t : Nat} {a b c : Cfg}
 (h1 : run s a = some b) (h2 : run t b = some c) : run (s+t) a = some c := by
 unfold run at *
 rw [Nat.add_comm s t,Function.iterate_add_apply,h1,h2]
lemma cfg_ext (c d : Cfg) (hl : c.l=d.l) (hv : c.var=d.var) (hs : c.stk=d.stk) : c=d := by
 cases c; cases d; cases hl; cases hv; cases hs; rfl

theorem finite_alphabets : ∀ k : machine.K, Finite (machine.Γ k) := by
 intro k; change Finite Bool; infer_instance
end PEqualNP.Outside.L_lib_895_aux.Finisher

namespace PEqualNP.Outside.L_lib_895_aux.Finisher
open Turing

def revStack (S : Fin 11 → List Bool) (r o : List Bool) : Fin 11 → List Bool :=
 fun j => if j=9 then r else if j=10 then o else S j
lemma rev_lift (l : Option Unit) (S : Fin 11 → List Bool) (r o : List Bool) :
 BoolCall.liftCfg revKS revLS (Equiv.refl State) revRet false
   (fun e => S e.val) (ReverseMove.cfg l none r o) =
 cfg (some (l.elim (.good 0) Label.rev)) (revStack S r o) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl
lemma rev_join_start (Q : Fin 10 → List Bool) :
 revStack (join Q []) (Q 9) [] = join Q [] := by
 funext j; fin_cases j <;> rfl
lemma rev_join_end (Q : Fin 10 → List Bool) (R : List Bool) :
 revStack (join Q []) [] R = join (Function.update Q 9 []) R := by
 funext j; fin_cases j <;> rfl
lemma good_lift (l : Option (Fin 11)) (Q : Fin 10 → List Bool) (R : List Bool) :
 BoolCall.liftCfg goodKS goodLS (Equiv.prodComm (Option Bool) Bool) goodRet none
   (fun _ => R) (ClearAll.cfg l Q) =
 cfg (some (l.elim .done Label.good)) (join Q R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl
lemma bad_lift (l : Option (Fin 12)) (S : Fin 11 → List Bool) :
 BoolCall.liftCfg badKS badLS (Equiv.prodComm (Option Bool) Bool) badRet none
   (fun _ => []) (ClearAll.cfg l S) =
 cfg (some (l.elim .done Label.bad)) S := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; rfl

lemma call_reverse (Q : Fin 10 → List Bool) :
 run ((Q 9).length+1) (cfg (some (.rev ())) (join Q [])) =
 some (cfg (some (.good 0)) (join (Function.update Q 9 []) (Q 9).reverse)) := by
 have h := BoolCall.run_lift revKS revLS (Equiv.refl State) revRet false
   (fun e => join Q [] e.val) ReverseMove.program program (by intro l; rfl)
   _ _ _ (ReverseMove.finish_run (Q 9))
 unfold ReverseMove.startCfg at h
 rw [rev_lift,rev_lift,rev_join_start,rev_join_end] at h
 exact h
lemma call_good (Q : Fin 10 → List Bool) (R : List Bool) :
 run (ClearAll.cost Q 0 10) (cfg (some (.good 0)) (join Q R)) =
 some (cfg (some .done) (join (fun _ => []) R)) := by
 have h := BoolCall.run_lift goodKS goodLS (Equiv.prodComm (Option Bool) Bool) goodRet none
   (fun _ => R) (ClearAll.program 10) program (by intro l; rfl)
   _ _ _ (ClearAll.clear_all_run Q)
 rw [good_lift,good_lift] at h
 exact h
lemma call_bad (S : Fin 11 → List Bool) :
 run (ClearAll.cost S 0 11) (cfg (some (.bad 0)) S) =
 some (cfg (some .done) (fun _ => [])) := by
 have h := BoolCall.run_lift badKS badLS (Equiv.prodComm (Option Bool) Bool) badRet none
   (fun _ => []) (ClearAll.program 11) program (by intro l; rfl)
   _ _ _ (ClearAll.clear_all_run S)
 rw [bad_lift,bad_lift] at h
 exact h
lemma enter_success (S : Fin 11 → List Bool) :
 TM2.step program (cfg (some .success) S) = some (cfg (some (.rev ())) S) := rfl
lemma enter_abort (S : Fin 11 → List Bool) :
 TM2.step program (cfg (some .abort) S) = some (cfg (some (.bad 0)) S) := rfl
lemma finish (S : Fin 11 → List Bool) :
 TM2.step program (cfg (some .done) S) = some (cfg none S) := rfl

theorem success_run (Q : Fin 10 → List Bool) :
 run (1+((Q 9).length+1)+ClearAll.cost (Function.update Q 9 []) 0 10+1)
   (cfg (some .success) (join Q [])) =
 some (cfg none (join (fun _ => []) (Q 9).reverse)) := by
 exact run_comp (run_comp (run_comp (run_one _ _ (enter_success _)) (call_reverse Q))
   (call_good (Function.update Q 9 []) (Q 9).reverse)) (run_one _ _ (finish _))

theorem abort_run (S : Fin 11 → List Bool) :
 run (1+ClearAll.cost S 0 11+1) (cfg (some .abort) S) =
 some (cfg none (fun _ => [])) := by
 exact run_comp (run_comp (run_one _ _ (enter_abort S)) (call_bad S)) (run_one _ _ (finish _))

theorem success_bound (Q : Fin 10 → List Bool) (L : Nat)
 (hL : ∀ k, k≠9 → (Q k).length≤L) :
 1+((Q 9).length+1)+ClearAll.cost (Function.update Q 9 []) 0 10+1 ≤
 (Q 9).length+1+10*(L+1)+3 := by
 have hq : ∀ k, ((Function.update Q 9 []) k).length≤L := by
   intro k
   by_cases hk : k=9
   · subst k; simp
   · rw [Function.update_of_ne hk]; exact hL k hk
 have h := ClearAll.cost_bound (Function.update Q 9 []) L hq 0 10
 omega

theorem abort_bound (S : Fin 11 → List Bool) (L : Nat) (hL : ∀ k, (S k).length≤L) :
 1+ClearAll.cost S 0 11+1 ≤ 11*(L+1)+3 := by
 have h := ClearAll.cost_bound S L hL 0 11
 omega

end PEqualNP.Outside.L_lib_895_aux.Finisher

namespace PEqualNP.Outside.L_lib_895_aux.Finisher
open Turing

def success_evals (Q : Fin 10 → List Bool) (L : Nat)
 (hL : ∀ k, k≠9 → (Q k).length≤L) :
 StateTransition.EvalsToInTime (TM2.step program) (cfg (some .success) (join Q []))
   (some (cfg none (join (fun _ => []) (Q 9).reverse)))
   ((Q 9).length+1+10*(L+1)+3) where
 steps := 1+((Q 9).length+1)+ClearAll.cost (Function.update Q 9 []) 0 10+1
 evals_in_steps := success_run Q
 steps_le_m := success_bound Q L hL

def abort_evals (S : Fin 11 → List Bool) (L : Nat) (hL : ∀ k, (S k).length≤L) :
 StateTransition.EvalsToInTime (TM2.step program) (cfg (some .abort) S)
   (some (cfg none (fun _ => []))) (11*(L+1)+3) where
 steps := 1+ClearAll.cost S 0 11+1
 evals_in_steps := abort_run S
 steps_le_m := abort_bound S L hL

lemma final_output (R : List Bool) : join (fun _ => []) R 10 = R := rfl
lemma final_other (R : List Bool) (k : Fin 11) (hk : k≠10) :
 join (fun _ => []) R k = [] := by
 fin_cases k <;> simp_all [join]
lemma split_stacks (S : Fin 11 → List Bool) :
 join (fun k : Fin 10 => S k.castSucc) (S 10) = S := by
 funext j; fin_cases j <;> rfl
end PEqualNP.Outside.L_lib_895_aux.Finisher

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing
abbrev Stack := Fin 11
abbrev Reg := Front.Reg × (TailMachine.S × Finisher.State)
inductive Label where
  | front (l : Front.Label) | tail (l : TailMachine.H) | finish (l : Finisher.Label)
  | afterFront | afterTail | afterFinish
  deriving DecidableEq
def labelEquiv : Label ≃ Front.Label ⊕ TailMachine.H ⊕ Finisher.Label ⊕ Fin 3 where
  toFun | .front l => .inl l | .tail l => .inr (.inl l)
        | .finish l => .inr (.inr (.inl l))
        | .afterFront => .inr (.inr (.inr 0))
        | .afterTail => .inr (.inr (.inr 1))
        | .afterFinish => .inr (.inr (.inr 2))
  invFun | .inl l => .front l | .inr (.inl l) => .tail l
         | .inr (.inr (.inl l)) => .finish l
         | .inr (.inr (.inr 0)) => .afterFront
         | .inr (.inr (.inr 1)) => .afterTail
         | .inr (.inr (.inr _)) => .afterFinish
  left_inv l := by cases l <;> rfl
  right_inv l := by rcases l with l|l|l|l; rfl; rfl; rfl; fin_cases l <;> rfl
instance : Fintype Label := Fintype.ofEquiv (Front.Label ⊕ TailMachine.H ⊕ Finisher.Label ⊕ Fin 3) labelEquiv.symm
abbrev Cfg := TM2.Cfg (fun _ : Stack => Bool) Label Reg

def encFrontK : Front.Stack → Stack
  | .input => 0 | .a => 1 | .b => 4 | .unary => 6 | .headerCopy => 5 | .output => 9 | .tmp => 2
def decFrontK (j : Stack) : Option Front.Stack :=
  if j=0 then some .input else if j=1 then some .a else if j=4 then some .b
  else if j=6 then some .unary else if j=5 then some .headerCopy
  else if j=9 then some .output else if j=2 then some .tmp else none
def ksFront := CallLayout.optionSplit encFrontK decFrontK
  (by intro k; cases k <;> decide)
  (by intro j k h; fin_cases j <;> cases k <;> revert h <;> decide)
def encTailK (k : Fin 10) : Stack := k.castSucc
def decTailK (j : Stack) : Option (Fin 10) := if h : j.val<10 then some ⟨j.val,h⟩ else none
def ksTail := CallLayout.optionSplit encTailK decTailK
  (by intro k; fin_cases k <;> decide)
  (by intro j k h; fin_cases j <;> fin_cases k <;> revert h <;> decide)
def ksFinish := CallLayout.optionSplit (id : Fin 11 → Stack) (fun j => some j)
  (by intro k; rfl) (by intro j k h; exact (Option.some.inj h).symm)

def decFrontL : Label → Option Front.Label | .front l => some l | _ => none
def decTailL : Label → Option TailMachine.H | .tail l => some l | _ => none
def decFinishL : Label → Option Finisher.Label | .finish l => some l | _ => none
def lsFront := CallLayout.optionSplit Label.front decFrontL
  (by intro k; rfl) (by intro j k h; cases j <;> simp_all [decFrontL])
def lsTail := CallLayout.optionSplit Label.tail decTailL
  (by intro k; rfl) (by intro j k h; cases j <;> simp_all [decTailL])
def lsFinish := CallLayout.optionSplit Label.finish decFinishL
  (by intro k; rfl) (by intro j k h; cases j <;> simp_all [decFinishL])
def retFront : {j // decFrontL j=none} := ⟨.afterFront,rfl⟩
def retTail : {j // decTailL j=none} := ⟨.afterTail,rfl⟩
def retFinish : {j // decFinishL j=none} := ⟨.afterFinish,rfl⟩

def ssTail : Reg ≃ TailMachine.S × (Front.Reg × Finisher.State) where
  toFun s := (s.2.1,(s.1,s.2.2))
  invFun s := (s.2.1,(s.1,s.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
def ssFinish : Reg ≃ Finisher.State × (Front.Reg × TailMachine.S) where
  toFun s := (s.2.2,(s.1,s.2.1))
  invFun s := (s.2.1,(s.2.2,s.1))
  left_inv _ := rfl
  right_inv _ := rfl

def initialState : Reg := (Front.clean false,(TailMachine.initialState,(none,false)))
def cfg (l : Option Label) (s : Reg) (st : Stack → List Bool) : Cfg := ⟨l,s,st⟩
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Reg
  | .front l => BoolCall.trStmt ksFront lsFront (Equiv.refl _) retFront (Front.program l)
  | .tail l => BoolCall.trStmt ksTail lsTail ssTail retTail (TailMachine.program l)
  | .finish l => BoolCall.trStmt ksFinish lsFinish ssFinish retFinish (Finisher.program l)
  | .afterFront => .branch (fun s => s.1.1.2)
      (.goto fun _ => .tail (TailMachine.ph 0)) (.goto fun _ => .finish .abort)
  | .afterTail => .branch (fun s => s.2.1.1.1.2)
      (.goto fun _ => .finish .success) (.goto fun _ => .finish .abort)
  | .afterFinish => .load (fun _ => initialState) .halt

def machine : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 10
  Γ _ := Bool
  Λ := Label
  main := .front (.prefixPhase (.hdr 0))
  σ := Reg
  initialState := initialState
  m := program
lemma finite_alphabets : ∀ j, Finite (machine.Γ j) := by intro j; change Finite Bool; infer_instance
lemma finite_labels : Finite machine.Λ := by change Finite Label; infer_instance
lemma finite_state : Finite machine.σ := by change Finite Reg; infer_instance
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing
abbrev Run (u : Nat) (c d : Cfg) : Prop := (flip bind (TM2.step program))^[u] (some c)=some d

def frontCfg (tailState : TailMachine.S) (finishState : Finisher.State)
    (extra : {j // decFrontK j=none} → List Bool) (c : Front.Cfg) : Cfg :=
  BoolCall.liftCfg ksFront lsFront (Equiv.refl _) retFront (tailState,finishState) extra c
def tailCfg (frontState : Front.Reg) (finishState : Finisher.State)
    (extra : {j // decTailK j=none} → List Bool) (c : TailMachine.Cfg) : Cfg :=
  BoolCall.liftCfg ksTail lsTail ssTail retTail (frontState,finishState) extra c
def finishCfg (frontState : Front.Reg) (tailState : TailMachine.S) (c : Finisher.Cfg) : Cfg :=
  BoolCall.liftCfg ksFinish lsFinish ssFinish retFinish (frontState,tailState) (fun _ => []) c

theorem call_front (tailState : TailMachine.S) (finishState : Finisher.State)
    (extra : {j // decFrontK j=none} → List Bool) (u : Nat) (c d : Front.Cfg)
    (h : (flip bind (TM2.step Front.program))^[u] (some c)=some d) :
    Run u (frontCfg tailState finishState extra c) (frontCfg tailState finishState extra d) :=
  BoolCall.run_lift ksFront lsFront (Equiv.refl _) retFront (tailState,finishState) extra
    Front.program program (by intro l; rfl) u c d h

theorem call_tail (frontState : Front.Reg) (finishState : Finisher.State)
    (extra : {j // decTailK j=none} → List Bool) (u : Nat) (c d : TailMachine.Cfg)
    (h : (flip bind (TM2.step TailMachine.program))^[u] (some c)=some d) :
    Run u (tailCfg frontState finishState extra c) (tailCfg frontState finishState extra d) :=
  BoolCall.run_lift ksTail lsTail ssTail retTail (frontState,finishState) extra
    TailMachine.program program (by intro l; rfl) u c d h

theorem call_finish (frontState : Front.Reg) (tailState : TailMachine.S)
    (u : Nat) (c d : Finisher.Cfg)
    (h : (flip bind (TM2.step Finisher.program))^[u] (some c)=some d) :
    Run u (finishCfg frontState tailState c) (finishCfg frontState tailState d) :=
  BoolCall.run_lift ksFinish lsFinish ssFinish retFinish (frontState,tailState) (fun _ => [])
    Finisher.program program (by intro l; rfl) u c d h

def front_evals (tailState : TailMachine.S) (finishState : Finisher.State)
    (extra : {j // decFrontK j=none} → List Bool) (c d : Front.Cfg) (bound : Nat)
    (h : StateTransition.EvalsToInTime (TM2.step Front.program) c (some d) bound) :
    StateTransition.EvalsToInTime (TM2.step program)
      (frontCfg tailState finishState extra c) (some (frontCfg tailState finishState extra d)) bound :=
  BoolCall.evals_lift ksFront lsFront (Equiv.refl _) retFront (tailState,finishState) extra
    Front.program program (by intro l; rfl) c d bound h

def tail_evals (frontState : Front.Reg) (finishState : Finisher.State)
    (extra : {j // decTailK j=none} → List Bool) (c d : TailMachine.Cfg) (bound : Nat)
    (h : StateTransition.EvalsToInTime (TM2.step TailMachine.program) c (some d) bound) :
    StateTransition.EvalsToInTime (TM2.step program)
      (tailCfg frontState finishState extra c) (some (tailCfg frontState finishState extra d)) bound :=
  BoolCall.evals_lift ksTail lsTail ssTail retTail (frontState,finishState) extra
    TailMachine.program program (by intro l; rfl) c d bound h

def finish_evals (frontState : Front.Reg) (tailState : TailMachine.S)
    (c d : Finisher.Cfg) (bound : Nat)
    (h : StateTransition.EvalsToInTime (TM2.step Finisher.program) c (some d) bound) :
    StateTransition.EvalsToInTime (TM2.step program)
      (finishCfg frontState tailState c) (some (finishCfg frontState tailState d)) bound :=
  BoolCall.evals_lift ksFinish lsFinish ssFinish retFinish (frontState,tailState) (fun _ => [])
    Finisher.program program (by intro l; rfl) c d bound h

lemma front_var (tailState : TailMachine.S) (finishState : Finisher.State)
    (extra : {j // decFrontK j=none} → List Bool) (c : Front.Cfg) :
    (frontCfg tailState finishState extra c).var=(c.var,(tailState,finishState)) := rfl
lemma tail_var (frontState : Front.Reg) (finishState : Finisher.State)
    (extra : {j // decTailK j=none} → List Bool) (c : TailMachine.Cfg) :
    (tailCfg frontState finishState extra c).var=(frontState,(c.var,finishState)) := rfl
lemma finish_var (frontState : Front.Reg) (tailState : TailMachine.S) (c : Finisher.Cfg) :
    (finishCfg frontState tailState c).var=(frontState,(tailState,c.var)) := rfl

lemma after_front_step (s : Reg) (st : Stack → List Bool) :
    TM2.step program (cfg (some .afterFront) s st)=
      some (cfg (some (if s.1.1.2 then .tail (TailMachine.ph 0) else .finish .abort)) s st) := by
  cases h : s.1.1.2 <;> simp [TM2.step,program,TM2.stepAux,cfg,h]
lemma after_tail_step (s : Reg) (st : Stack → List Bool) :
    TM2.step program (cfg (some .afterTail) s st)=
      some (cfg (some (if s.2.1.1.1.2 then .finish .success else .finish .abort)) s st) := by
  cases h : s.2.1.1.1.2 <;> simp [TM2.step,program,TM2.stepAux,cfg,h]
lemma after_finish_step (s : Reg) (st : Stack → List Bool) :
    TM2.step program (cfg (some .afterFinish) s st)=some (cfg none initialState st) := rfl

end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

def initialStacks (x : List Bool) : Stack → List Bool := Function.update (fun _ => []) 0 x
def outputStacks (y : List Bool) : Stack → List Bool := Function.update (fun _ => []) 10 y
def initialCfg (x : List Bool) : Cfg := cfg (some (.front (.prefixPhase (.hdr 0)))) initialState (initialStacks x)

lemma front_initial (x : List Bool) :
    frontCfg TailMachine.initialState (none,false) (fun _ => []) (Front.initialCfg x)=initialCfg x := by
  dsimp [frontCfg,BoolCall.liftCfg,Front.initialCfg,Front.cfg,cfg,initialCfg,initialState]
  congr 1
  funext (k : Fin 11); fin_cases k <;> rfl

lemma initList_eq (x : List Bool) : initList machine x=initialCfg x := by
  change (⟨_,_,_⟩ : Cfg)=_
  congr 1
  funext (k : Fin 11); fin_cases k <;> rfl
lemma haltList_eq (y : List Bool) : haltList machine y=cfg none initialState (outputStacks y) := by
  change (⟨_,_,_⟩ : Cfg)=_
  congr 1
  funext (k : Fin 11); fin_cases k <;> rfl

noncomputable def global_front_evals (x : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (frontCfg TailMachine.initialState (none,false) (fun _ => []) (Front.outcome x)))
      (1000*(x.length+1)^2) := by
  have h := front_evals TailMachine.initialState (none,false) (fun _ => [])
    _ _ _ (Front.total_evals x)
  rw [front_initial] at h
  exact h

lemma finish_return (frontState : Front.Reg) (tailState : TailMachine.S) (st : Stack → List Bool) :
    TM2.step program (finishCfg frontState tailState (Finisher.cfg none st))=
      some (cfg none initialState st) := rfl

private def extend_step {α : Type} (f : α → Option α) (a b c : α) (B : Nat)
    (h : StateTransition.EvalsToInTime f a (some b) B) (hs : f b=some c) :
    StateTransition.EvalsToInTime f a (some c) (B+1) where
  steps := h.steps+1
  evals_in_steps := by
    rw [Nat.add_comm h.steps 1,Function.iterate_add_apply,h.evals_in_steps]
    exact hs
  steps_le_m := by have := h.steps_le_m; omega

lemma final_join (y : List Bool) : Finisher.join (fun _ => []) y=outputStacks y := by
  funext (k : Fin 11); fin_cases k <;> rfl
lemma final_empty : (fun _ : Stack => ([] : List Bool))=outputStacks [] := by
  funext (k : Fin 11); fin_cases k <;> rfl

def global_success_evals (frontState : Front.Reg) (tailState : TailMachine.S)
    (Q : Fin 10 → List Bool) (L : Nat) (hL : ∀ k,k≠9 → (Q k).length≤L) :
    StateTransition.EvalsToInTime (TM2.step program)
      (finishCfg frontState tailState (Finisher.cfg (some .success) (Finisher.join Q [])))
      (some (haltList machine (Q 9).reverse))
      ((Q 9).length+1+10*(L+1)+3+1) := by
  have h := finish_evals frontState tailState _ _ _ (Finisher.success_evals Q L hL)
  have hh := extend_step (TM2.step program) _ _ _ _ h
    (finish_return frontState tailState (Finisher.join (fun _ => []) (Q 9).reverse))
  rw [final_join,←haltList_eq] at hh
  exact hh

def global_abort_evals (frontState : Front.Reg) (tailState : TailMachine.S)
    (st : Stack → List Bool) (L : Nat) (hL : ∀ k,(st k).length≤L) :
    StateTransition.EvalsToInTime (TM2.step program)
      (finishCfg frontState tailState (Finisher.cfg (some .abort) st))
      (some (haltList machine [])) (11*(L+1)+3+1) := by
  have h := finish_evals frontState tailState _ _ _ (Finisher.abort_evals st L hL)
  have hh := extend_step (TM2.step program) _ _ _ _ h
    (finish_return frontState tailState (fun _ => []))
  rw [final_empty,←haltList_eq] at hh
  exact hh
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine
open Turing

def stk (I W A B R : List Bool) : Fin 10 → List Bool := ![I,W,[],[],A,[],B,[],[],R]
def cs (v : Bool) (c d : Fin 4) : S := (((none,v),(c,d)),0)
lemma cfg_ext (a b : Cfg) (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
 cases a; cases b; cases hl; cases hv; cases hs; rfl
lemma run_one (a b : Cfg) (h : TM2.step program a=some b) : run 1 a=some b := h

lemma r_lift (l : Option RecordValid.H) (v : Bool) (c d : Fin 4) (I W A B R : List Bool) :
 BoolCall.liftCfg rks rls rss rret 0 (fun _ => R)
   (RecordValid.cfg l v c d (RecordMachine.tapes I W [] [] A [] B [] [])) =
 cfg (some (l.elim (ph 1) rv)) (cs v c d) (stk I W A B R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl

lemma b_lift (l : Option BanMachine.Label) (v : Bool) (c d : Fin 4) (I W A B R : List Bool) :
 BoolCall.liftCfg bks bls bss bret (v,(c,d)) (fun e => stk I W [] [] [] e.val)
   (BanMachine.cfg l A B R) =
 cfg (some (l.elim (ph 2) bn)) (cs v c d) (stk I W A B R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl

lemma ci_lift (l : Option Unit) (c d : Fin 4) (I W A B R : List Bool) :
 BoolCall.liftCfg (cks 0) (cls 0) css (cret 0) (none,((c,d),0))
   (fun e => stk I W [] B R e.val) (Clear.cfg l A) =
 cfg (some (l.elim (ph 3) (fun _ => cl 0))) (cs false c d) (stk I W A B R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl
lemma cj_lift (l : Option Unit) (c d : Fin 4) (I W A B R : List Bool) :
 BoolCall.liftCfg (cks 1) (cls 1) css (cret 1) (none,((c,d),0))
   (fun e => stk I W A [] R e.val) (Clear.cfg l B) =
 cfg (some (l.elim (ph 4) (fun _ => cl 1))) (cs false c d) (stk I W A B R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl

lemma call_validation (n : Nat) (e : Ban) (hl : legalRecord n e) (I R : List Bool) :
 ∃ t ≤ 30*width n+100,
 run t (cfg (some (rv (RecordValid.rd 12))) initialState
   (stk (recordBits n e++I) (bits (width n) n) [] [] R)) =
 some (cfg (some (ph 1))
   (cs true ⟨e.1.2,by have := hl.2.2.1;omega⟩ ⟨e.2.2,by have := hl.2.2.2;omega⟩)
   (stk I (bits (width n) n) (bits (width n) e.1.1) (bits (width n) e.2.1) R)) := by
 obtain ⟨t,ht,hr⟩ := RecordValid.legal_encoded_run n e hl I
 have h := BoolCall.run_lift rks rls rss rret 0 (fun _ => R)
   RecordValid.program program rbody _ _ _ hr
 unfold RecordValid.initial RecordValid.legalEnd at h
 rw [r_lift,r_lift] at h
 exact ⟨t,ht,h⟩

lemma color3_val (c : Fin 4) (hc : c.val<3) : (color3 c).val = c.val := by
 exact Nat.mod_eq_of_lt hc

lemma call_ban (n i j : Nat) (c d : Fin 4) (hc : c.val<3) (hd : d.val<3)
 (I R : List Bool) (hn : 2≤n) :
 run (4*(2*width n+4)+2)
   (cfg (some (bn (BanMachine.encode (color3 c,color3 d) .phase))) (cs true c d)
     (stk I (bits (width n) n) (bits (width n) i) (bits (width n) j) R)) =
 some (cfg (some (ph 2)) (cs true c d)
   (stk I (bits (width n) n) (bits (width n) i) (bits (width n) j)
     (((PEqualNP.Outside.L_lib_895_aux.Comb.flag i c.val ++ PEqualNP.Outside.L_lib_895_aux.Comb.flag j d.val).flatMap
       (bits (width (8*n+1)))).reverse++R))) := by
 have hr := BanMachine.ban_bits_run n i j (color3 c) (color3 d) R hn
 rw [color3_val c hc,color3_val d hd] at hr
 have h := BoolCall.run_lift bks bls bss bret (true,(c,d))
   (fun e => stk I (bits (width n) n) [] [] [] e.val)
   BanMachine.program program bbody _ _ _ hr
 unfold BanMachine.start BanMachine.finish at h
 rw [b_lift,b_lift] at h
 exact h

lemma call_clearI (c d : Fin 4) (I W A B R : List Bool) :
 run (A.length+1) (cfg (some (cl 0)) (cs false c d) (stk I W A B R)) =
 some (cfg (some (ph 3)) (cs false c d) (stk I W [] B R)) := by
 have h := BoolCall.run_lift (cks 0) (cls 0) css (cret 0) (none,((c,d),0))
   (fun e => stk I W [] B R e.val) Clear.prog program (cbody 0) _ _ _ (Clear.clear_run A)
 rw [ci_lift,ci_lift] at h
 exact h
lemma call_clearJ (c d : Fin 4) (I W A B R : List Bool) :
 run (B.length+1) (cfg (some (cl 1)) (cs false c d) (stk I W A B R)) =
 some (cfg (some (ph 4)) (cs false c d) (stk I W A [] R)) := by
 have h := BoolCall.run_lift (cks 1) (cls 1) css (cret 1) (none,((c,d),0))
   (fun e => stk I W A [] R e.val) Clear.prog program (cbody 1) _ _ _ (Clear.clear_run B)
 rw [cj_lift,cj_lift] at h
 exact h

lemma loop_step (b : Bool) (I W R : List Bool) :
 TM2.step program (cfg (some (ph 0)) initialState (stk (b::I) W [] [] R)) =
 some (cfg (some (rv (RecordValid.rd 12))) initialState (stk (b::I) W [] [] R)) := rfl
lemma emit_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 1)) (cs true c d) st) =
 some (cfg (some (bn (BanMachine.encode (color3 c,color3 d) .phase))) (cs true c d) st) := rfl
lemma clearI_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 2)) (cs true c d) st) =
 some (cfg (some (cl 0)) (cs false c d) st) := rfl
lemma clearJ_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 3)) (cs false c d) st) =
 some (cfg (some (cl 1)) (cs false c d) st) := rfl
lemma return_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 4)) (cs false c d) st) =
 some (cfg (some (ph 0)) initialState st) := rfl

def banWord (n : Nat) (e : Ban) : List Bool :=
 (PEqualNP.Outside.L_lib_895_aux.Comb.flag e.1.1 e.1.2 ++ PEqualNP.Outside.L_lib_895_aux.Comb.flag e.2.1 e.2.2).flatMap
   (bits (width (8*n+1)))

theorem iteration_legal (n : Nat) (e : Ban) (hn : 2≤n) (hl : legalRecord n e) (I R : List Bool) :
 ∃ t ≤ 50*width n+200,
 run t (cfg (some (ph 0)) initialState (stk (recordBits n e++I) (bits (width n) n) [] [] R)) =
 some (cfg (some (ph 0)) initialState (stk I (bits (width n) n) [] [] ((banWord n e).reverse++R))) := by
 let c : Fin 4 := ⟨e.1.2,by have := hl.2.2.1;omega⟩
 let d : Fin 4 := ⟨e.2.2,by have := hl.2.2.2;omega⟩
 let A := bits (width n) e.1.1
 let B := bits (width n) e.2.1
 let W := bits (width n) n
 let O := (banWord n e).reverse++R
 have h0 : run 1 (cfg (some (ph 0)) initialState (stk (recordBits n e++I) W [] [] R)) =
   some (cfg (some (rv (RecordValid.rd 12))) initialState (stk (recordBits n e++I) W [] [] R)) := by
   cases hw : recordBits n e++I with
   | nil =>
     have he := congrArg List.length hw
     simp only [List.length_append,recordBits_length,List.length_nil] at he
     omega
   | cons b J => exact run_one _ _ (loop_step b J W R)
 obtain ⟨t,ht,hr⟩ := call_validation n e hl I R
 have h := run_comp h0 hr
 have h := run_comp h (run_one _ _ (emit_step c d (stk I W A B R)))
 have hb := call_ban n e.1.1 e.2.1 c d hl.2.2.1 hl.2.2.2 I R hn
 have h := run_comp h hb
 have h := run_comp h (run_one _ _ (clearI_step c d (stk I W A B O)))
 have h := run_comp h (call_clearI c d I W A B O)
 have h := run_comp h (run_one _ _ (clearJ_step c d (stk I W [] B O)))
 have h := run_comp h (call_clearJ c d I W [] B O)
 have h := run_comp h (run_one _ _ (return_step c d (stk I W [] [] O)))
 refine ⟨1+t+1+(4*(2*width n+4)+2)+1+(A.length+1)+1+(B.length+1)+1,?_,h⟩
 have hA : A.length = width n := bits_length _ _
 have hB : B.length = width n := bits_length _ _
 rw [hA,hB]
 omega

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing
lemma cfg_ext (c d : Cfg) (hl : c.l=d.l) (hv : c.var=d.var) (hs : c.stk=d.stk) : c=d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl

def join_evals {α : Type} (f : α → Option α) (a b c : α) (B C : Nat)
    (h : StateTransition.EvalsToInTime f a (some b) B)
    (h' : StateTransition.EvalsToInTime f b (some c) C) :
    StateTransition.EvalsToInTime f a (some c) (B+C) where
  steps := h.steps+h'.steps
  evals_in_steps := by
    rw [Nat.add_comm h.steps h'.steps,Function.iterate_add_apply,h.evals_in_steps,h'.evals_in_steps]
  steps_le_m := by have := h.steps_le_m; have := h'.steps_le_m; omega

def step_evals {α : Type} (f : α → Option α) (a b : α) (h : f a=some b) :
    StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

def blockBuilder (n : Nat) : List Bool :=
  (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse

def tailInitial (n : Nat) (I : List Bool) : TailMachine.Cfg :=
  TailMachine.cfg (some (TailMachine.ph 0)) TailMachine.initialState
    (TailMachine.stk I (bits (width n) n) [] [] (blockBuilder n))

lemma front_to_tail (n : Nat) (I : List Bool) :
    TM2.step program (frontCfg TailMachine.initialState (none,false) (fun _ => []) (Front.endCfg n I)) =
      some (tailCfg (Front.clean true) (none,false) (fun _ => []) (tailInitial n I)) := by
  dsimp [frontCfg,tailCfg,BoolCall.liftCfg,Front.endCfg,Front.cfg,Front.clean,
    tailInitial,TailMachine.cfg,blockBuilder,TM2.step,program,TM2.stepAux,lsFront,lsTail,retFront,retTail,CallLayout.optionSplit,ssTail]
  simp only [Bool.cond_true,Bool.cond_false]
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext (k : Fin 11); fin_cases k <;> rfl

lemma front_to_abort :
    TM2.step program (frontCfg TailMachine.initialState (none,false) (fun _ => []) Front.rejectCfg) =
      some (finishCfg (Front.clean false) TailMachine.initialState
        (Finisher.cfg (some .abort) (fun _ => []))) := by
  dsimp [frontCfg,finishCfg,BoolCall.liftCfg,Front.rejectCfg,Front.cfg,Front.clean,
    Finisher.cfg,TM2.step,program,TM2.stepAux,ssFinish,lsFront,lsFinish,retFront,retFinish,CallLayout.optionSplit]
  simp only [Bool.cond_true,Bool.cond_false]
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext (k : Fin 11); fin_cases k <;> rfl

noncomputable def global_invalid_evals (x : List Bool) (hx : ¬ Prefix.HeaderLegal x) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (haltList machine [])) (1000*(x.length+1)^2+1+(11*(0+1)+3+1)) := by
  have hf := global_front_evals x
  rw [Front.outcome_invalid x hx] at hf
  have hs := step_evals (TM2.step program) _ _ front_to_abort
  have hb := global_abort_evals (Front.clean false) TailMachine.initialState (fun _ => []) 0 (by simp)
  exact join_evals (TM2.step program) _ _ _ _ _
    (join_evals (TM2.step program) _ _ _ _ _ hf hs) hb

noncomputable def global_tail_entry_evals (n : Nat) (I : List Bool) (hn : 2≤n) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg (header n++I))
      (some (tailCfg (Front.clean true) (none,false) (fun _ => []) (tailInitial n I)))
      (1000*((header n++I).length+1)^2+1) := by
  have hf := global_front_evals (header n++I)
  rw [Front.outcome_header n I hn] at hf
  exact join_evals (TM2.step program) _ _ _ _ _ hf
    (step_evals (TM2.step program) _ _ (front_to_tail n I))
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine

def recordPayload (n : Nat) (B : List Ban) := B.flatMap (recordBits n)
def banEncoding (n : Nat) (e : Ban) :=
  (PEqualNP.Outside.L_lib_895_aux.Comb.flag e.1.1 e.1.2 ++
    PEqualNP.Outside.L_lib_895_aux.Comb.flag e.2.1 e.2.2).flatMap (bits (width (8*n+1)))
def banPayload (n : Nat) (B : List Ban) := B.flatMap (banEncoding n)

lemma recordPayload_length (n : Nat) (B : List Ban) :
    (recordPayload n B).length = B.length*(2*width n+4) := by
  apply PEqualNP.Outside.L_lib_895_aux.Comb.flatMap_length_constant
  intro e he
  exact recordBits_length n e

lemma recordPayload_nil (n : Nat) : recordPayload n [] = [] := rfl
lemma recordPayload_cons (n : Nat) (e : Ban) (B : List Ban) :
    recordPayload n (e::B) = recordBits n e ++ recordPayload n B := rfl
lemma banPayload_nil (n : Nat) : banPayload n [] = [] := rfl
lemma banPayload_cons (n : Nat) (e : Ban) (B : List Ban) :
    banPayload n (e::B) = banEncoding n e ++ banPayload n B := rfl

lemma packed_emit_split (n : Nat) (B : List Ban) :
    PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) =
      PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n []) ++ banPayload n B := by
  simp [PEqualNP.Outside.L_lib_895_aux.Comb.pack,PEqualNP.Outside.L_lib_895_aux.Comb.emit,
    banPayload,banEncoding,List.flatMap_append,List.flatMap_map,List.append_assoc,
    bits,width,PEqualNP.Outside.L_lib_895_aux.Comb.bits,PEqualNP.Outside.L_lib_895_aux.Comb.width]
  apply congrArg (fun f : Ban → List Bool => B.flatMap f)
  funext e
  unfold banEncoding
  rw [List.flatMap_append]
  rfl

lemma packed_emit_reverse (n : Nat) (B : List Ban) :
    (banPayload n B).reverse ++
      (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse =
      (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B)).reverse := by
  have h := congrArg List.reverse (packed_emit_split n B)
  rw [List.reverse_append] at h
  exact h.symm

lemma records_time_quadratic (L w b : Nat) (hw : w≤L+1) (hb : b≤L) :
    b*(50*w+200)+1 ≤ 300*(L+1)^2 := by
  have hm := Nat.mul_le_mul hb (show 50*w+200≤50*(L+1)+200 by omega)
  nlinarith

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine

lemma loop_empty (W R : List Bool) :
    Turing.TM2.step program (cfg (some (ph 0)) initialState (stk [] W [] [] R)) =
      some (cfg none initialState (stk [] W [] [] R)) := rfl

theorem legal_payload_run (n : Nat) (B : List Ban) (hn : 2≤n)
    (hB : ∀ e∈B,legalRecord n e) (R : List Bool) :
    ∃ t ≤ B.length*(50*width n+200)+1,
      run t (cfg (some (ph 0)) initialState (stk (recordPayload n B) (bits (width n) n) [] [] R)) =
        some (cfg none initialState (stk [] (bits (width n) n) [] [] ((banPayload n B).reverse++R))) := by
  induction B generalizing R with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa only [recordPayload_nil,banPayload_nil,List.reverse_nil,List.nil_append] using
      run_one _ _ (loop_empty (bits (width n) n) R)
  | cons e B ih =>
    have he := hB e List.mem_cons_self
    have ht : ∀ a∈B,legalRecord n a := fun a ha => hB a (List.mem_cons_of_mem e ha)
    obtain ⟨u,hu,hru⟩ := iteration_legal n e hn he (recordPayload n B) R
    obtain ⟨v,hv,hrv⟩ := ih ht ((banWord n e).reverse++R)
    refine ⟨u+v,by simp only [List.length_cons];nlinarith,?_⟩
    have h := run_comp hru hrv
    simpa only [recordPayload_cons,banPayload_cons,List.reverse_append,List.append_assoc,
      banWord,banEncoding] using h

theorem legal_full_builder_run (n : Nat) (B : List Ban) (hl : legal n B) :
    ∃ t ≤ B.length*(50*width n+200)+1,
      run t (cfg (some (ph 0)) initialState
        (stk (recordPayload n B) (bits (width n) n) [] []
          (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse)) =
        some (cfg none initialState (stk [] (bits (width n) n) [] []
          (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B)).reverse)) := by
  obtain ⟨t,ht,hr⟩ := legal_payload_run n B hl.1 hl.2
    (PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n [])).reverse
  refine ⟨t,ht,?_⟩
  rw [packed_emit_reverse] at hr
  exact hr

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

def encodedOutput (n : Nat) (B : List Ban) : List Bool :=
  PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B)

lemma tail_to_success (Q : Fin 10 → List Bool) :
    TM2.step program (tailCfg (Front.clean true) (none,false) (fun _ => [])
      (TailMachine.cfg none TailMachine.initialState Q)) =
      some (finishCfg (Front.clean true) TailMachine.initialState
        (Finisher.cfg (some .success) (Finisher.join Q []))) := by
  dsimp [tailCfg,finishCfg,BoolCall.liftCfg,TailMachine.cfg,Finisher.cfg,
    TM2.step,program,TM2.stepAux,lsTail,lsFinish,retTail,retFinish,CallLayout.optionSplit,
    ssTail,ssFinish,TailMachine.initialState]
  simp only [Bool.cond_true]
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext (k : Fin 11); fin_cases k <;> rfl

set_option maxRecDepth 4096 in
theorem valid_global_run (n : Nat) (B : List Ban) (hl : legal n B) :
    ∃ u ≤ 1000000*((enc n B).length+1)^2,
      Run u (initialCfg (enc n B)) (haltList machine (encodedOutput n B)) := by
  obtain ⟨u,hu,hr⟩ := TailMachine.legal_full_builder_run n B hl
  let Q := TailMachine.stk [] (bits (width n) n) [] [] (encodedOutput n B).reverse
  let good := TailMachine.cfg none TailMachine.initialState Q
  have ht : StateTransition.EvalsToInTime (TM2.step TailMachine.program)
      (tailInitial n (TailMachine.recordPayload n B)) (some good)
      (B.length*(50*width n+200)+1) :=
    { steps := u, evals_in_steps := hr, steps_le_m := hu }
  have he := global_tail_entry_evals n (TailMachine.recordPayload n B) hl.1
  have hg := tail_evals (Front.clean true) (none,false) (fun _ => []) _ _ _ ht
  have h0 := join_evals (TM2.step program) _ _ _ _ _ he hg
  have hs := step_evals (TM2.step program) _ _ (tail_to_success Q)
  have h1 := join_evals (TM2.step program) _ _ _ _ _ h0 hs
  have hsize : n+B.length+1≤(enc n B).length := by
    rw [enc_eq_inputEncoding]
    exact inputEncoding_size n B
  have hw : width n≤(enc n B).length+1 := by
    unfold width
    have := Nat.log2_le_self n
    omega
  have hb : B.length≤(enc n B).length := by omega
  have hwork : ∀ k : Fin 10,k≠9 → (Q k).length≤(enc n B).length+1 := by
    intro k hk
    fin_cases k <;> simp_all [Q,TailMachine.stk,bits_length]
  have hf := global_success_evals (Front.clean true) TailMachine.initialState Q ((enc n B).length+1) hwork
  have hout : (Q 9).reverse=encodedOutput n B := by simp [Q,TailMachine.stk]
  rw [hout] at hf
  have whole := join_evals (TM2.step program) _ _ _ _ _ h1 hf
  refine ⟨whole.steps,?_,whole.evals_in_steps⟩
  have htime := TailMachine.records_time_quadratic (enc n B).length (width n) B.length hw hb
  have houtput : (encodedOutput n B).length≤1000*((enc n B).length+1)^2 := by
    rw [show encodedOutput n B=totalOutput (enc n B) by exact (totalOutput_on_legal n B hl).symm]
    exact totalOutput_length (enc n B)
  have hq : (Q 9).length=(encodedOutput n B).length := by simp [Q,TailMachine.stk]
  have hin : (header n++TailMachine.recordPayload n B).length=(enc n B).length := rfl
  have hsteps := whole.steps_le_m
  simp only [hq,hin] at hsteps
  nlinarith

set_option maxRecDepth 4096 in
noncomputable def valid_global_evals (n : Nat) (B : List Ban) (hl : legal n B) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg (enc n B))
      (some (haltList machine (encodedOutput n B))) (1000000*((enc n B).length+1)^2) where
  steps := Classical.choose (valid_global_run n B hl)
  evals_in_steps := (Classical.choose_spec (valid_global_run n B hl)).2
  steps_le_m := (Classical.choose_spec (valid_global_run n B hl)).1

end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

noncomputable def computer_of_runs (f : List Bool → List Bool)
    (h : ∀ x, StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (haltList machine (f x))) (1000000*(x.length+1)^2)) :
    TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time z := 1000000*(z+1)^2
  outputsFun x :=
    { steps := (h x).steps
      evals_in_steps := by
        have hm (l : List Bool) : List.map (Equiv.refl Bool).invFun l=l := by simp
        exact (congrArg (fun l : List Bool =>
          (flip bind (TM2.step program))^[(h x).steps] (some (initList machine l))) (hm x)).trans
          ((congrArg (fun c : Cfg => (flip bind (TM2.step program))^[(h x).steps] (some c))
            (initList_eq x)).trans
            ((h x).evals_in_steps.trans
              (congrArg (fun l : List Bool => some (haltList machine l)) (hm (f x)).symm)))
      steps_le_m := (h x).steps_le_m }

theorem machine_exists_of_total_runs
    (h : ∀ x, StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (haltList machine (totalOutput x))) (1000000*(x.length+1)^2)) :
    ∃ C : Nat, ∃ M : TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput,
      (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z≤C*(z+1)^2 := by
  refine ⟨1000000,computer_of_runs totalOutput h,?_,?_⟩
  · exact finite_alphabets
  · intro z; exact le_rfl
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.Parser

def recordOK (n : Nat) (e : Ban) : Bool :=
  decide (e.1.1<e.2.1 ∧ e.2.1<n ∧ e.1.2<3 ∧ e.2.2<3)
lemma recordOK_spec (n : Nat) (e : Ban) : recordOK n e = true ↔ legalRecord n e := by
  simp [recordOK,legalRecord]

def readRecord (n : Nat) (xs : List Bool) : Option (Ban × List Bool) :=
  Option.bind (readWord (width n) xs) (fun p0 =>
  Option.bind (readWord 2 p0.2) (fun p1 =>
  Option.bind (readWord (width n) p1.2) (fun p2 =>
  Option.bind (readWord 2 p2.2) (fun p3 =>
    let e := ((p0.1,p1.1),(p2.1,p3.1))
    bif recordOK n e then some (e,p3.2) else none))))

lemma readRecord_sound (n : Nat) (xs : List Bool) (e : Ban) (rest : List Bool)
    (h : readRecord n xs = some (e,rest)) :
    legalRecord n e ∧ xs = recordBits n e ++ rest := by
  cases h0 : readWord (width n) xs with
  | none => simp [readRecord,h0] at h
  | some p0 =>
    rcases p0 with ⟨i,x1⟩
    cases h1 : readWord 2 x1 with
    | none => simp [readRecord,h0,h1] at h
    | some p1 =>
      rcases p1 with ⟨c,x2⟩
      cases h2 : readWord (width n) x2 with
      | none => simp [readRecord,h0,h1,h2] at h
      | some p2 =>
        rcases p2 with ⟨j,x3⟩
        cases h3 : readWord 2 x3 with
        | none => simp [readRecord,h0,h1,h2,h3] at h
        | some p3 =>
          rcases p3 with ⟨d,x4⟩
          cases hg : recordOK n ((i,c),(j,d)) with
          | false => simp [readRecord,h0,h1,h2,h3,hg] at h
          | true =>
            have he : some (((i,c),(j,d)),x4) = some (e,rest) := by
              simpa only[readRecord,h0,h1,h2,h3,Option.bind_some,hg,Bool.cond_true] using h
            have hep := Option.some.inj he
            have he0 := congrArg Prod.fst hep
            have he1 := congrArg Prod.snd hep
            dsimp at he0 he1
            subst e
            subst rest
            obtain ⟨hs0,_⟩ := readWord_sound (width n) xs i x1 h0
            obtain ⟨hs1,_⟩ := readWord_sound 2 x1 c x2 h1
            obtain ⟨hs2,_⟩ := readWord_sound (width n) x2 j x3 h2
            obtain ⟨hs3,_⟩ := readWord_sound 2 x3 d x4 h3
            refine ⟨(recordOK_spec n _).mp hg,?_⟩
            rw [hs0,hs1,hs2,hs3]
            simp only[recordBits,List.append_assoc]

lemma readRecord_complete (n : Nat) (e : Ban) (rest : List Bool) (hl : legalRecord n e) :
    readRecord n (recordBits n e ++ rest) = some (e,rest) := by
  have hn : n<2^(width n) := Nat.lt_log2_self
  have hi : e.1.1<2^(width n) := lt_trans (lt_trans hl.1 hl.2.1) hn
  have hj : e.2.1<2^(width n) := lt_trans hl.2.1 hn
  have hc : e.1.2<2^2 := by have := hl.2.2.1; norm_num; omega
  have hd : e.2.2<2^2 := by have := hl.2.2.2; norm_num; omega
  have h0 := readWord_complete (width n) e.1.1
    (bits 2 e.1.2 ++ bits (width n) e.2.1 ++ bits 2 e.2.2 ++ rest) hi
  have h1 := readWord_complete 2 e.1.2
    (bits (width n) e.2.1 ++ bits 2 e.2.2 ++ rest) hc
  have h2 := readWord_complete (width n) e.2.1 (bits 2 e.2.2 ++ rest) hj
  have h3 := readWord_complete 2 e.2.2 rest hd
  simp only[List.append_assoc] at h0 h1 h2 h3
  have hg := (recordOK_spec n e).mpr hl
  simp [readRecord,recordBits,List.append_assoc,h0,h1,h2,h3,hg]

lemma readRecord_length (n : Nat) (xs : List Bool) (e : Ban) (rest : List Bool)
    (h : readRecord n xs = some (e,rest)) : xs.length = 2*width n+4+rest.length := by
  have hh := congrArg List.length (readRecord_sound n xs e rest h).2
  simpa only[List.length_append,recordBits_length] using hh
end PEqualNP.Outside.L_lib_895_aux.Parser

namespace PEqualNP.Outside.L_lib_895_aux.Parser

def parseRecords (n : Nat) : Nat → List Bool → Option (List Ban)
  | 0, [] => some []
  | 0, _::_ => none
  | f+1, [] => some []
  | f+1, x::xs => Option.bind (readRecord n (x::xs)) (fun p =>
      Option.map (fun B => p.1::B) (parseRecords n f p.2))

lemma parseRecords_step (n f : Nat) (xs : List Bool) (hne : xs≠[]) :
    parseRecords n (f+1) xs = Option.bind (readRecord n xs) (fun p =>
      Option.map (fun B => p.1::B) (parseRecords n f p.2)) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs => rfl

lemma parseRecords_sound (n fuel : Nat) (xs : List Bool) (B : List Ban)
    (h : parseRecords n fuel xs = some B) :
    (∀ e∈B,legalRecord n e) ∧ xs = B.flatMap (recordBits n) := by
  induction fuel generalizing xs B with
  | zero =>
    cases xs with
    | nil =>
      simp only[parseRecords,Option.some.injEq] at h
      subst B
      exact ⟨by simp,rfl⟩
    | cons x xs => simp [parseRecords] at h
  | succ fuel ih =>
    cases xs with
    | nil =>
      simp only[parseRecords,Option.some.injEq] at h
      subst B
      exact ⟨by simp,rfl⟩
    | cons x xs =>
      cases hr : readRecord n (x::xs) with
      | none => simp [parseRecords,hr] at h
      | some p =>
        rcases p with ⟨e,rest⟩
        cases ht : parseRecords n fuel rest with
        | none => simp [parseRecords,hr,ht] at h
        | some es =>
          have he : some (e::es) = some B := by
            simpa only[parseRecords,hr,Option.bind_some,ht,Option.map_some] using h
          have heB := Option.some.inj he
          subst B
          obtain ⟨hlegal,hprefix⟩ := readRecord_sound n (x::xs) e rest hr
          obtain ⟨hrest,hpayload⟩ := ih rest es ht
          refine ⟨?_,?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hlegal
            · exact hrest a ha
          · rw [hprefix,hpayload]
            rfl

lemma payload_length_bound (n : Nat) (B : List Ban) :
    B.length ≤ (B.flatMap (recordBits n)).length := by
  induction B with
  | nil => simp
  | cons e B ih =>
    simp only[List.length_cons,List.flatMap_cons,List.length_append,recordBits_length]
    omega

lemma parseRecords_complete (n : Nat) (B : List Ban) :
    (∀ e∈B,legalRecord n e) → ∀ fuel, B.length≤fuel →
      parseRecords n fuel (B.flatMap (recordBits n)) = some B := by
  induction B with
  | nil => intro hl fuel hf; cases fuel <;> rfl
  | cons e B ih =>
    intro hl fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have ht : B.length≤fuel := by simpa only[List.length_cons,Nat.succ_le_succ_iff] using hf
      have hr := ih (fun a ha => hl a (List.mem_cons_of_mem e ha)) fuel ht
      have hne : recordBits n e ++ B.flatMap (recordBits n) ≠ [] := by
        intro he
        have hh := congrArg List.length he
        simp only[List.length_append,recordBits_length,List.length_nil] at hh
        omega
      rw [List.flatMap_cons,parseRecords_step n fuel _ hne,
        readRecord_complete n e _ (hl e List.mem_cons_self),Option.bind_some,hr]
      rfl

end PEqualNP.Outside.L_lib_895_aux.Parser

namespace PEqualNP.Outside.L_lib_895_aux.Parser

def parse (xs : List Bool) : Option (Nat × List Ban) :=
  Option.bind (parseHeader xs) (fun p =>
    if 2≤p.1 then Option.map (fun B => (p.1,B)) (parseRecords p.1 p.2.length p.2)
    else none)

lemma parse_sound (xs : List Bool) (n : Nat) (B : List Ban)
    (h : parse xs = some (n,B)) : legal n B ∧ enc n B = xs := by
  cases hh : parseHeader xs with
  | none => simp [parse,hh] at h
  | some p =>
    rcases p with ⟨m,rest⟩
    by_cases hm : 2≤m
    · cases hr : parseRecords m rest.length rest with
      | none => simp [parse,hh,hm,hr] at h
      | some es =>
        have he : some (m,es) = some (n,B) := by
          simpa only[parse,hh,Option.bind_some,if_pos hm,hr,Option.map_some] using h
        have hep := Option.some.inj he
        have hn := congrArg Prod.fst hep
        have hB := congrArg Prod.snd hep
        dsimp at hn hB
        subst n
        subst B
        obtain ⟨hl,hpayload⟩ := parseRecords_sound m rest.length rest es hr
        refine ⟨⟨hm,hl⟩,?_⟩
        have hx := header_sound xs m rest hh
        rw [hpayload] at hx
        exact hx.symm
    · simp [parse,hh,hm] at h

lemma parse_complete (n : Nat) (B : List Ban) (hl : legal n B) :
    parse (enc n B) = some (n,B) := by
  have hh := header_complete n (B.flatMap (recordBits n))
  have hr := parseRecords_complete n B hl.2 _ (payload_length_bound n B)
  simp only[parse,enc,hh,Option.bind_some,if_pos hl.1,hr,Option.map_some]

lemma parse_success_iff (xs : List Bool) (n : Nat) (B : List Ban) :
    parse xs = some (n,B) ↔ legal n B ∧ enc n B = xs := by
  constructor
  · exact parse_sound xs n B
  · rintro ⟨hl,he⟩
    rw [←he]
    exact parse_complete n B hl

lemma parse_none_iff (xs : List Bool) : parse xs = none ↔
    ¬∃ n B, legal n B ∧ enc n B = xs := by
  constructor
  · intro hp ⟨n,B,hl,he⟩
    have hh := parse_complete n B hl
    rw [he,hp] at hh
    cases hh
  · intro hbad
    cases hp : parse xs with
    | none => rfl
    | some p =>
      rcases p with ⟨n,B⟩
      exact False.elim (hbad ⟨n,B,parse_sound xs n B hp⟩)

def output (xs : List Bool) : List Bool :=
  match parse xs with
  | none => []
  | some p => outputData p

lemma output_eq_totalOutput (xs : List Bool) : output xs = totalOutput xs := by
  cases hp : parse xs with
  | none =>
    have hbad := (parse_none_iff xs).mp hp
    rw [totalOutput_malformed xs hbad]
    simp only[output,hp]
  | some p =>
    rcases p with ⟨n,B⟩
    obtain ⟨hl,he⟩ := parse_sound xs n B hp
    have hh := totalOutput_on_legal n B hl
    rw [he] at hh
    simp only[output,hp]
    exact hh.symm

lemma output_on_legal (n : Nat) (B : List Ban) (hl : legal n B) :
    output (enc n B) = PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1)
      (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B) := by
  rw [output_eq_totalOutput,totalOutput_on_legal n B hl]
lemma output_malformed (xs : List Bool) (hbad : ¬∃ n B, legal n B ∧ enc n B=xs) :
    output xs = [] := by
  simp only[output,(parse_none_iff xs).mpr hbad]
lemma output_length (xs : List Bool) : (output xs).length ≤ 1000*(xs.length+1)^2 := by
  rw [output_eq_totalOutput]
  exact totalOutput_length xs

end PEqualNP.Outside.L_lib_895_aux.Parser

namespace PEqualNP.Outside.L_lib_895_aux.CodecBridge

def payload (n : Nat) (B : List Ban) : List Bool := B.flatMap (recordBits n)
def packed (n : Nat) (B : List Ban) : List Bool :=
 PEqualNP.Outside.L_lib_895_aux.Comb.pack (8*n+1) (PEqualNP.Outside.L_lib_895_aux.Comb.emit n B)

lemma header_length_eq (x : List Bool) (n : Nat) (I : List Bool)
 (hh : Parser.parseHeader x=some (n,I)) : x.length=n+1+I.length := by
 have he := Parser.header_sound x n I hh
 rw [he]
 simp [header]
 omega

lemma output_of_header_payload (x : List Bool) (n : Nat) (I : List Bool) (B : List Ban)
 (hh : Parser.parseHeader x=some (n,I)) (hn : 2≤n)
 (hl : ∀e∈B,legalRecord n e) (he : I=payload n B) : Parser.output x=packed n B := by
 have hx : x=enc n B := by
  rw [Parser.header_sound x n I hh,he]
  rfl
 rw [hx]
 exact Parser.output_on_legal n B ⟨hn,hl⟩

lemma records_none_of_no_payload (n : Nat) (I : List Bool)
 (hbad : ¬∃B,(∀e∈B,legalRecord n e) ∧I=payload n B) :
 Parser.parseRecords n I.length I=none := by
 cases hp : Parser.parseRecords n I.length I with
 | none => rfl
 | some B =>
   obtain ⟨hl,he⟩ := Parser.parseRecords_sound n I.length I B hp
   exact False.elim (hbad ⟨B,hl,he⟩)

lemma records_some_of_payload (n : Nat) (I : List Bool) (B : List Ban)
 (hl : ∀e∈B,legalRecord n e) (he : I=payload n B) :
 Parser.parseRecords n I.length I=some B := by
 rw [he]
 exact Parser.parseRecords_complete n B hl _ (Parser.payload_length_bound n B)

lemma output_of_header_no_payload (x : List Bool) (n : Nat) (I : List Bool)
 (hh : Parser.parseHeader x=some (n,I)) (hn : 2≤n)
 (hbad : ¬∃B,(∀e∈B,legalRecord n e) ∧I=payload n B) : Parser.output x=[] := by
 have hr := records_none_of_no_payload n I hbad
 simp only [Parser.output,Parser.parse,hh,Option.bind_some,if_pos hn,hr,Option.map_none]

lemma output_of_header_none (x : List Bool) (hh : Parser.parseHeader x=none) :
 Parser.output x=[] := by
 simp only [Parser.output,Parser.parse,hh,Option.bind_none]
lemma output_of_header_small (x : List Bool) (n : Nat) (I : List Bool)
 (hh : Parser.parseHeader x=some (n,I)) (hn : n<2) : Parser.output x=[] := by
 have hh' : ¬2≤n := by omega
 simp only [Parser.output,Parser.parse,hh,Option.bind_some,if_neg hh']

lemma width_le_budget (n L : Nat) (hbudget : n+1≤L) : width n≤L+1 := by
 unfold width
 have hh := Nat.log2_le_self n
 omega

lemma prefix_input_budget (x : List Bool) (n : Nat) (I : List Bool) (B : List Ban)
 (hh : Parser.parseHeader x=some (n,I)) (hb : (payload n B).length≤I.length) :
 n+1+(payload n B).length≤x.length := by
 rw [header_length_eq x n I hh]
 omega

lemma accepted_prefix_output_bound (n : Nat) (B : List Ban) (L : Nat)
 (hn : 2≤n) (hl : ∀e∈B,legalRecord n e)
 (hbudget : n+1+(payload n B).length≤L) :
 (packed n B).length≤1000*(L+1)^2 := by
 have hlegal : PEqualNP.Outside.L_lib_895_aux.Comb.legal n B := ⟨hn,hl⟩
 have hout := exact_output_quadratic n B hlegal
 have hin : (inputEncoding n B).length≤L := by
  change (enc n B).length≤L
  simpa only [enc,List.length_append,header,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,Nat.add_zero,payload] using hbudget
 change (packed n B).length≤1000*((inputEncoding n B).length+1)^2 at hout
 nlinarith

lemma accepted_prefix_resources (n : Nat) (B : List Ban) (L : Nat)
 (hn : 2≤n) (hl : ∀e∈B,legalRecord n e)
 (hbudget : n+1+(payload n B).length≤L) :
 (packed n B).length≤1000*(L+1)^2 ∧width n≤L+1 ∧n+B.length+1≤L := by
 have hb : B.length≤(payload n B).length := Parser.payload_length_bound n B
 exact ⟨accepted_prefix_output_bound n B L hn hl hbudget,
   width_le_budget n L (by omega),by omega⟩
end PEqualNP.Outside.L_lib_895_aux.CodecBridge

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

def RecordRejection : Prop := ∀ (n : Nat) (I : List Bool), 2≤n →
    (¬∃ B : List Ban, (∀ e∈B,legalRecord n e) ∧ I=TailMachine.recordPayload n B) →
    ∃ u ≤ 1000000*((header n++I).length+1)^2,
      Run u (initialCfg (header n++I)) (haltList machine [])

set_option maxRecDepth 4096 in
theorem total_runs_of_record_rejection (hReject : RecordRejection) (x : List Bool) :
    ∃ u ≤ 1000000*(x.length+1)^2,
      Run u (initialCfg x) (haltList machine (totalOutput x)) := by
  classical
  by_cases hx : Prefix.HeaderLegal x
  · obtain ⟨n,I,hn,he⟩ := hx
    subst x
    by_cases hI : ∃ B : List Ban, (∀ e∈B,legalRecord n e) ∧ I=TailMachine.recordPayload n B
    · obtain ⟨B,hB,he⟩ := hI
      have he' : header n++I=enc n B := by rw [he]; rfl
      rw [he',totalOutput_on_legal n B ⟨hn,hB⟩]
      exact valid_global_run n B ⟨hn,hB⟩
    · have hout : totalOutput (header n++I)=[] := by
        rw [←Parser.output_eq_totalOutput]
        exact CodecBridge.output_of_header_no_payload _ n I (Parser.header_complete n I) hn hI
      rw [hout]
      exact hReject n I hn hI
  · have hbad : ¬∃ n B,legal n B ∧enc n B=x := by
      rintro ⟨n,B,hl,he⟩
      exact hx ⟨n,TailMachine.recordPayload n B,hl.1,he.symm⟩
    rw [totalOutput_malformed x hbad]
    have hg := global_invalid_evals x hx
    refine ⟨hg.steps,?_,hg.evals_in_steps⟩
    have hs := hg.steps_le_m
    have hsq : 1≤(x.length+1)^2 := by
      simpa [pow_two] using Nat.mul_le_mul (show 1≤x.length+1 by omega) (show 1≤x.length+1 by omega)
    nlinarith

noncomputable def all_evals_of_record_rejection (hReject : RecordRejection) (x : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (haltList machine (totalOutput x))) (1000000*(x.length+1)^2) where
  steps := Classical.choose (total_runs_of_record_rejection hReject x)
  evals_in_steps := (Classical.choose_spec (total_runs_of_record_rejection hReject x)).2
  steps_le_m := (Classical.choose_spec (total_runs_of_record_rejection hReject x)).1

theorem machine_exists_of_record_rejection (hReject : RecordRejection) :
    ∃ C : Nat, ∃ M : TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput,
      (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z≤C*(z+1)^2 :=
  machine_exists_of_total_runs (all_evals_of_record_rejection hReject)
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
theorem reader_packet4 (A B R W : List Bool) (c d : Fin 4)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 ∃ t ≤ 6*W.length+30,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg (some (ph 0)) true 0 0
   (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 d.val) [])) := by
 have hC : (bits 2 c.val).length=2 := bits_length _ _
 have hD : (bits 2 d.val).length=2 := bits_length _ _
 have ha : 2*W.length+4≤(packet A (bits 2 c.val) B (bits 2 d.val) R).length := by
  simp only [packet,List.length_append,hA,hB,hC,hD]
  omega
 obtain ⟨t,ht,hr⟩ := reader_call (packet A (bits 2 c.val) B (bits 2 d.val) R) W 0 0 ha
 rw [packet_slices A _ B _ R W hA hB hC hD] at hr
 exact ⟨t,ht,hr⟩

lemma colorC_bad (d : Fin 4) (I W FI FJ FD : List Bool) :
 TM2.step program (cfg (some (ph 1)) true 0 d
   (RecordMachine.tapes I W [] [] FI (bits 2 3) FJ FD [])) =
 some (cfg (some (ph 9)) true 3 d
   (RecordMachine.tapes I W [] [] FI [] FJ FD [])) := by
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,setC,color,
   bits,List.range_succ,RecordMachine.tapes,show Nat.testBit 3 1=true by decide]
 funext k
 fin_cases k <;> rfl
lemma colorD_bad (c : Fin 4) (I W FI FJ : List Bool) :
 TM2.step program (cfg (some (ph 2)) true c 0
   (RecordMachine.tapes I W [] [] FI [] FJ (bits 2 3) [])) =
 some (cfg (some (ph 9)) true c 3
   (RecordMachine.tapes I W [] [] FI [] FJ [] [])) := by
 simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,setD,color,
   bits,List.range_succ,RecordMachine.tapes,show Nat.testBit 3 1=true by decide]
 funext k
 fin_cases k <;> rfl
lemma compare_bad (i : Fin 2) (st : Fin 9 → List Bool) (c d : Fin 4) (he : st 8=[false]) :
 TM2.step program (cfg (some (ph (cmpAfter i))) false c d st)=
 some (⟨some (ph 9),((some false,false),(c,d)),Function.update st 8 []⟩ : Cfg) := by
 fin_cases i <;> simp [TM2.step,program,phaseProgram,ph,cfg,TM2.stepAux,cmpAfter,he]
lemma read_bad (st : Fin 9 → List Bool) (c d : Fin 4) :
 TM2.step program (cfg (some (ph 0)) false c d st)=
 some (cfg (some (ph 9)) false c d st) := rfl
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
theorem index_packet_contract (A B R W : List Bool) (c d : Fin 3)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 ∃ t ≤ 30*W.length+100, ∃ v,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg none v (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) ∧
 v=decide (Compare.value A<Compare.value B ∧ Compare.value B<Compare.value W) := by
 obtain ⟨t,ht,hr⟩ := reader_packet A B R W c d hA hB
 have hread := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 d.val) []) 0 0)
 have hC := run_one _ _ (colorC_step c 0 R W [] [] A B (bits 2 d.val) [])
 have hD := run_one _ _ (colorD_step (asColor c) d R W [] [] A B [])
 have hc0 : run (3*A.length+3) (cfg (some (cp 0 .duplicate)) true (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) =
   some (cfg (some (ph 3)) true (asColor c) (asColor d) (RecordMachine.tapes R W A [] A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 0 (RecordMachine.tapes R W [] [] A [] B [] []) true (asColor c) (asColor d) (by rfl) (by rfl)
 have hc1 : run (3*B.length+3) (cfg (some (cp 1 .duplicate)) true (asColor c) (asColor d) (RecordMachine.tapes R W A [] A [] B [] [])) =
   some (cfg (some (ph 4)) true (asColor c) (asColor d) (RecordMachine.tapes R W A B A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 1 (RecordMachine.tapes R W A [] A [] B [] []) true (asColor c) (asColor d) (by rfl) (by rfl)
 have hc2 : run (3*B.length+3) (cfg (some (cp 2 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) =
   some (cfg (some (ph 6)) false (asColor c) (asColor d) (RecordMachine.tapes R W B [] A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 2 (RecordMachine.tapes R W [] [] A [] B [] []) false (asColor c) (asColor d) (by rfl) (by rfl)
 have hc3 : run (3*W.length+3) (cfg (some (cp 3 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W B [] A [] B [] [])) =
   some (cfg (some (ph 7)) false (asColor c) (asColor d) (RecordMachine.tapes R W B W A [] B [] [])) := by
   simpa [src,dst,tmp,copyAfter] using copy_call 3 (RecordMachine.tapes R W B [] A [] B [] []) false (asColor c) (asColor d) (by rfl) (by rfl)
 have hp3 := run_one _ _ (afterCopy0 (RecordMachine.tapes R W A [] A [] B [] []) true (asColor c) (asColor d))
 have hp4 := run_one _ _ (afterCopy1 (RecordMachine.tapes R W A B A [] B [] []) true (asColor c) (asColor d))
 have hp6 := run_one _ _ (afterCopy2 (RecordMachine.tapes R W B [] A [] B [] []) false (asColor c) (asColor d))
 have hp7 := run_one _ _ (afterCopy3 (RecordMachine.tapes R W B W A [] B [] []) false (asColor c) (asColor d))
 have hm0 : run (A.length+1) (cfg (some (cm 0)) false (asColor c) (asColor d) (RecordMachine.tapes R W A B A [] B [] [])) =
   some (cfg (some (ph 5)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [decide (Compare.value A<Compare.value B)])) := by
   simpa [cmpAfter] using compare_call 0 (RecordMachine.tapes R W A B A [] B [] []) (asColor c) (asColor d) (by simp [hA,hB]) (by rfl)
 have hm1 : run (B.length+1) (cfg (some (cm 1)) false (asColor c) (asColor d) (RecordMachine.tapes R W B W A [] B [] [])) =
   some (cfg (some (ph 8)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [decide (Compare.value B<Compare.value W)])) := by
   simpa [cmpAfter] using compare_call 1 (RecordMachine.tapes R W B W A [] B [] []) (asColor c) (asColor d) (by simp [hB]) (by rfl)
 by_cases hij : Compare.value A<Compare.value B
 · have hm := hm0
   simp only [hij,decide_true] at hm
   have hp5 : run 1 (cfg (some (ph 5)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) =
     some (cfg (some (cp 2 .duplicate)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) := by
     simpa using run_one _ _ (compare0_checked (RecordMachine.tapes R W [] [] A [] B [] [true]) (asColor c) (asColor d) (by rfl))
   by_cases hjn : Compare.value B<Compare.value W
   · have hn := hm1
     simp only [hjn,decide_true] at hn
     have hp8 : run 1 (cfg (some (ph 8)) false (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [true])) =
       some (cfg none true (asColor c) (asColor d) (RecordMachine.tapes R W [] [] A [] B [] [])) := by
       simpa using run_one _ _ (compare1_checked (RecordMachine.tapes R W [] [] A [] B [] [true]) (asColor c) (asColor d) (by rfl))
     have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp hr hread) hC) hD) hc0) hp3) hc1) hp4) hm) hp5) hc2) hp6) hc3) hp7) hn) hp8
     exact ⟨_,by omega,true,hrun,by simp [hij,hjn]⟩
   · have hn := hm1
     simp only [hjn,decide_false] at hn
     have hb := run_one _ _ (compare_bad 1 (RecordMachine.tapes R W [] [] A [] B [] [false]) (asColor c) (asColor d) (by rfl))
     have hx := run_one _ _ (reject_step (Function.update (RecordMachine.tapes R W [] [] A [] B [] [false]) 8 []) ((some false,false),(asColor c,asColor d)))
     have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp hr hread) hC) hD) hc0) hp3) hc1) hp4) hm) hp5) hc2) hp6) hc3) hp7) hn) hb) hx
     refine ⟨t+1+1+1+(3*A.length+3)+1+(3*B.length+3)+1+(A.length+1)+1+(3*B.length+3)+1+(3*W.length+3)+1+(B.length+1)+1+1,by omega,false,?_,by simp [hjn]⟩
     simpa [cmpAfter] using hrun
 · have hn := hm0
   simp only [hij,decide_false] at hn
   have hb := run_one _ _ (compare_bad 0 (RecordMachine.tapes R W [] [] A [] B [] [false]) (asColor c) (asColor d) (by rfl))
   have hx := run_one _ _ (reject_step (Function.update (RecordMachine.tapes R W [] [] A [] B [] [false]) 8 []) ((some false,false),(asColor c,asColor d)))
   have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp hr hread) hC) hD) hc0) hp3) hc1) hp4) hn) hb) hx
   refine ⟨t+1+1+1+(3*A.length+3)+1+(3*B.length+3)+1+(A.length+1)+1+1,by omega,false,?_,by simp [hij]⟩
   simpa [cmpAfter] using hrun
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def packetGood (A B W : List Bool) (c d : Fin 4) : Prop :=
 c.val<3 ∧ d.val<3 ∧ Compare.value A<Compare.value B ∧ Compare.value B<Compare.value W

instance (A B W : List Bool) (c d : Fin 4) : Decidable (packetGood A B W c d) := by unfold packetGood;infer_instance

def packetFinish (A B R W : List Bool) (c d : Fin 4) (v : Bool) (st : Fin 9 → List Bool) : Prop :=
 v=decide (packetGood A B W c d) ∧ st 0=R ∧st 1=W ∧st 2=[] ∧st 3=[] ∧st 4=A ∧st 6=B ∧st 8=[]

theorem packet_contract (A B R W : List Bool) (c d : Fin 4)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 ∃ t ≤ 30*W.length+100, ∃ v c' d' st,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg none v c' d' st) ∧ packetFinish A B R W c d v st := by
 by_cases hc : c.val<3
 · by_cases hd : d.val<3
   · obtain ⟨t,ht,v,hr,hv⟩ := index_packet_contract A B R W ⟨c.val,hc⟩ ⟨d.val,hd⟩ hA hB
     refine ⟨t,ht,v,asColor ⟨c.val,hc⟩,asColor ⟨d.val,hd⟩,RecordMachine.tapes R W [] [] A [] B [] [],hr,?_⟩
     simp only [packetFinish,packetGood,hc,hd,true_and]
     exact ⟨hv,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
   · have ed : d=3 := Fin.ext (by omega)
     subst d
     obtain ⟨t,ht,hr⟩ := reader_packet4 A B R W c 3 hA hB
     have hp := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 3) []) 0 0)
     have hC := run_one _ _ (colorC_step ⟨c.val,hc⟩ 0 R W [] [] A B (bits 2 3) [])
     have hD := run_one _ _ (colorD_bad (asColor ⟨c.val,hc⟩) R W A B)
     have hx := run_one _ _ (reject_step (RecordMachine.tapes R W [] [] A [] B [] []) ((none,true),(asColor ⟨c.val,hc⟩,3)))
     have hrun := run_comp (run_comp (run_comp (run_comp hr hp) hC) hD) hx
     refine ⟨_,by omega,false,asColor ⟨c.val,hc⟩,3,RecordMachine.tapes R W [] [] A [] B [] [],hrun,?_⟩
     simp [packetFinish,packetGood]
 · have ec : c=3 := Fin.ext (by omega)
   subst c
   obtain ⟨t,ht,hr⟩ := reader_packet4 A B R W 3 d hA hB
   have hp := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 3) B (bits 2 d.val) []) 0 0)
   have hC := run_one _ _ (colorC_bad 0 R W A B (bits 2 d.val))
   have hx := run_one _ _ (reject_step (RecordMachine.tapes R W [] [] A [] B (bits 2 d.val) []) ((none,true),(3,0)))
   have hrun := run_comp (run_comp (run_comp hr hp) hC) hx
   refine ⟨_,by omega,false,3,0,RecordMachine.tapes R W [] [] A [] B (bits 2 d.val) [],hrun,?_⟩
   simp [packetFinish,packetGood]
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def fa (I : List Bool) (w : Nat) := I.take w
def fc (I : List Bool) (w : Nat) := (I.drop w).take 2
def fb (I : List Bool) (w : Nat) := (I.drop (w+2)).take w
def fd (I : List Bool) (w : Nat) := (I.drop (2*w+2)).take 2
def fr (I : List Bool) (w : Nat) := I.drop (2*w+4)
lemma input_split (I : List Bool) (w : Nat) :
 I=packet (fa I w) (fc I w) (fb I w) (fd I w) (fr I w) := by
 have eR : I.drop (2*w+4)=(I.drop (2*w+2)).drop 2 := by rw [List.drop_drop]
 have eB : I.drop (2*w+2)=(I.drop (w+2)).drop w := by rw [List.drop_drop];congr 1 <;> omega
 have eC : I.drop (w+2)=(I.drop w).drop 2 := by rw [List.drop_drop]
 unfold packet fa fc fb fd fr
 rw [eR,List.take_append_drop,eB,List.take_append_drop,eC,List.take_append_drop,List.take_append_drop]
lemma full_lengths (I : List Bool) (w : Nat) (h : 2*w+4≤I.length) :
 (fa I w).length=w ∧(fc I w).length=2 ∧(fb I w).length=w ∧(fd I w).length=2 := by
 simp [fa,fc,fb,fd,List.length_take,List.length_drop]
 omega

def validationGood (I W : List Bool) : Prop :=
 2*W.length+4≤I.length ∧ wordValue (fc I W.length)<3 ∧ wordValue (fd I W.length)<3 ∧
 Compare.value (fa I W.length)<Compare.value (fb I W.length) ∧
 Compare.value (fb I W.length)<Compare.value W
instance (I W : List Bool) : Decidable (validationGood I W) := by unfold validationGood;infer_instance

theorem reader_failure_call (I W : List Bool) (ha : I.length<2*W.length+4) :
 ∃ t ≤ 6*W.length+30, ∃ st,
 run t (initial I W)=some (cfg (some (ph 0)) false 0 0 st) ∧
 st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] := by
 obtain ⟨t,ht,v,st,hr,hv,hW,h2,h3,h8,hs,hf⟩ := RecordMachine.record_contract I W
 have hn : ¬2*W.length+4≤I.length := by omega
 have he : v=false := by simpa [hn] using hv
 rw [he] at hr
 have h := BoolCall.run_lift rks rls rss rret (0,0) (fun _ => [])
   RecordMachine.program program rbody t _ _ hr
 exact ⟨t,ht,st,h,hW,h2,h3,h8⟩

theorem validation_total (I W : List Bool) :
 ∃ t ≤ 30*W.length+100, ∃ v c d st,
 run t (initial I W)=some (cfg none v c d st) ∧
 v=decide (validationGood I W) ∧st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] ∧
 (v=true → st 0=fr I W.length ∧st 4=fa I W.length ∧st 6=fb I W.length) := by
 by_cases ha : 2*W.length+4≤I.length
 · obtain ⟨hA,hC,hB,hD⟩ := full_lengths I W.length ha
   let c : Fin 4 := ⟨wordValue (fc I W.length),by
     have hh := wordValue_lt (fc I W.length)
     simpa [hC] using hh⟩
   let d : Fin 4 := ⟨wordValue (fd I W.length),by
     have hh := wordValue_lt (fd I W.length)
     simpa [hD] using hh⟩
   have ec : bits 2 c.val=fc I W.length := by
     simpa only [c,hC] using bits_wordValue (fc I W.length)
   have ed : bits 2 d.val=fd I W.length := by
     simpa only [d,hD] using bits_wordValue (fd I W.length)
   obtain ⟨t,ht,v,c',d',st,hr,hv,hR,hW,h2,h3,hFI,hFJ,h8⟩ :=
     packet_contract (fa I W.length) (fb I W.length) (fr I W.length) W c d hA hB
   have ei : packet (fa I W.length) (bits 2 c.val) (fb I W.length) (bits 2 d.val) (fr I W.length)=I := by
     rw [ec,ed,←input_split]
   change run t (initial (packet _ _ _ _ _) W)=_ at hr
   rw [ei] at hr
   refine ⟨t,ht,v,c',d',st,hr,?_,hW,h2,h3,h8,?_⟩
   · simpa [validationGood,ha,packetGood,c,d] using hv
   · intro _
     exact ⟨hR,hFI,hFJ⟩
 · have hs : I.length<2*W.length+4 := by omega
   obtain ⟨t,ht,st,hr,hW,h2,h3,h8⟩ := reader_failure_call I W hs
   have hp := run_one _ _ (read_bad st 0 0)
   have hx := run_one _ _ (reject_step st ((none,false),(0,0)))
   have hrun := run_comp (run_comp hr hp) hx
   refine ⟨_,by omega,false,0,0,st,hrun,?_,hW,h2,h3,h8,by simp⟩
   simp [validationGood,ha]
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordMachine
def FieldsBound (w : Nat) (st : Fin 9 → List Bool) : Prop :=
 (st 4).length≤w ∧(st 5).length≤2 ∧(st 6).length≤w ∧(st 7).length≤2
theorem record_contract_bounded (I W : List Bool) :
 ∃ t ≤ 6*W.length+30, ∃ v st,
 run t (initial I W)=some (cfg none v st) ∧ Finished I W v st ∧ FieldsBound W.length st := by
 obtain ⟨c02,c03,c0f,c12,c13,c1f,c22,c23,c2f,c32,c33,c3f⟩ := stage_conditions I W
 obtain ⟨sm0,sm1,sm2,sm3⟩ := stage_markers I W
 obtain ⟨si0,si1,si2,si3,si4⟩ := stage_inputs I W
 obtain ⟨cm1,cm2,cm3,cm4⟩ := all_CM I W
 have he := run_one _ _ (entry_step I W)
 obtain ⟨t0,ht0,hr0⟩ := call_contract 0 (stage0 I W) c02 c03 c0f
 have hb0 : t0 ≤ 3*(W.length)+3 := by simpa only [sm0,List.length_cons,List.length_nil] using ht0
 have h0 : run t0 (cfg (some 0) true (stage0 I W)) =
   some (cfg (some 13) (decide (W.length≤I.length)) (stage1 I W)) := by
   simp only [sm0,si0,List.length_cons,List.length_nil] at hr0
   simpa [callLabel,after,stage1] using hr0
 obtain ⟨t1,ht1,hr1⟩ := call_contract 1 (stage1 I W) c12 c13 c1f
 have hb1 : t1 ≤ 3*(2)+3 := by simpa only [sm1,List.length_cons,List.length_nil] using ht1
 have h1 : run t1 (cfg (some 3) true (stage1 I W)) =
   some (cfg (some 14) (decide (2≤(I.drop W.length).length)) (stage2 I W)) := by
   simp only [sm1,si1,List.length_cons,List.length_nil] at hr1
   simpa [callLabel,after,stage2] using hr1
 obtain ⟨t2,ht2,hr2⟩ := call_contract 2 (stage2 I W) c22 c23 c2f
 have hb2 : t2 ≤ 3*(W.length)+3 := by simpa only [sm2,List.length_cons,List.length_nil] using ht2
 have h2 : run t2 (cfg (some 6) true (stage2 I W)) =
   some (cfg (some 15) (decide (W.length≤(I.drop (W.length+2)).length)) (stage3 I W)) := by
   simp only [sm2,si2,List.length_cons,List.length_nil] at hr2
   simpa [callLabel,after,stage3] using hr2
 obtain ⟨t3,ht3,hr3⟩ := call_contract 3 (stage3 I W) c32 c33 c3f
 have hb3 : t3 ≤ 3*(2)+3 := by simpa only [sm3,List.length_cons,List.length_nil] using ht3
 have h3 : run t3 (cfg (some 9) true (stage3 I W)) =
   some (cfg (some 16) (decide (2≤(I.drop (2*W.length+2)).length)) (stage4 I W)) := by
   simp only [sm3,si3,List.length_cons,List.length_nil] at hr3
   simpa [callLabel,after,stage4] using hr3
 by_cases hl0 : W.length≤I.length
 · have hs0 := h0
   simp only [hl0,decide_true] at hs0
   have hc0 := run_one _ _ (check_step 0 true (stage1 I W))
   change run 1 (cfg (some 13) true (stage1 I W)) = some (cfg (some 3) true (stage1 I W)) at hc0
   by_cases hl1 : 2≤(I.drop W.length).length
   · have hs1 := h1
     simp only [hl1,decide_true] at hs1
     have hc1 := run_one _ _ (check_step 1 true (stage2 I W))
     change run 1 (cfg (some 14) true (stage2 I W)) = some (cfg (some 6) true (stage2 I W)) at hc1
     by_cases hl2 : W.length≤(I.drop (W.length+2)).length
     · have hs2 := h2
       simp only [hl2,decide_true] at hs2
       have hc2 := run_one _ _ (check_step 2 true (stage3 I W))
       change run 1 (cfg (some 15) true (stage3 I W)) = some (cfg (some 9) true (stage3 I W)) at hc2
       by_cases hl3 : 2≤(I.drop (2*W.length+2)).length
       · have hs3 := h3
         simp only [hl3,decide_true] at hs3
         have hc3 := run_one _ _ (check_step 3 true (stage4 I W))
         change run 1 (cfg (some 16) true (stage4 I W)) = some (cfg (some 18) true (stage4 I W)) at hc3
         have hx := run_one _ _ (exit_step true (stage4 I W) cm4)
         have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hs2) hc2) hs3) hc3) hx
         refine ⟨_,by omega,true,clean (stage4 I W),hrun,?_,?_⟩
         ·
           have hlen : 2*W.length+4≤I.length := by simp only [List.length_drop] at hl0 hl1 hl2 hl3; omega
           simp [Finished,hlen,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker] <;> omega
         · simp [FieldsBound,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.length_take]
       · have hf3 := h3
         simp only [hl3,decide_false] at hf3
         have hc3 := run_one _ _ (check_step 3 false (stage4 I W))
         change run 1 (cfg (some 16) false (stage4 I W)) = some (cfg (some 17) false (stage4 I W)) at hc3
         have hx := run_one _ _ (exit_step false (stage4 I W) cm4)
         have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hs2) hc2) hf3) hc3) hx
         refine ⟨_,by omega,false,clean (stage4 I W),hrun,?_,?_⟩
         ·
           have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl3; omega
           have hi : stage4 I W 0=[] := by
             rw [si4]
             apply List.drop_eq_nil_of_le
             simp only [List.length_drop] at hl3
             omega
           refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
           all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
         · simp [FieldsBound,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.length_take]
     · have hf2 := h2
       simp only [hl2,decide_false] at hf2
       have hc2 := run_one _ _ (check_step 2 false (stage3 I W))
       change run 1 (cfg (some 15) false (stage3 I W)) = some (cfg (some 17) false (stage3 I W)) at hc2
       have hx := run_one _ _ (exit_step false (stage3 I W) cm3)
       have hrun := run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hs1) hc1) hf2) hc2) hx
       refine ⟨_,by omega,false,clean (stage3 I W),hrun,?_,?_⟩
       ·
         have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl2; omega
         have hi : stage3 I W 0=[] := by
           rw [si3]
           apply List.drop_eq_nil_of_le
           simp only [List.length_drop] at hl2
           omega
         refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
         all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
       · simp [FieldsBound,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.length_take]
   · have hf1 := h1
     simp only [hl1,decide_false] at hf1
     have hc1 := run_one _ _ (check_step 1 false (stage2 I W))
     change run 1 (cfg (some 14) false (stage2 I W)) = some (cfg (some 17) false (stage2 I W)) at hc1
     have hx := run_one _ _ (exit_step false (stage2 I W) cm2)
     have hrun := run_comp (run_comp (run_comp (run_comp (run_comp he hs0) hc0) hf1) hc1) hx
     refine ⟨_,by omega,false,clean (stage2 I W),hrun,?_,?_⟩
     ·
       have hlen : ¬2*W.length+4≤I.length := by simp only [List.length_drop] at hl1; omega
       have hi : stage2 I W 0=[] := by
         rw [si2]
         apply List.drop_eq_nil_of_le
         simp only [List.length_drop] at hl1
         omega
       refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
       all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
     · simp [FieldsBound,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.length_take]
 · have hf0 := h0
   simp only [hl0,decide_false] at hf0
   have hc0 := run_one _ _ (check_step 0 false (stage1 I W))
   change run 1 (cfg (some 13) false (stage1 I W)) = some (cfg (some 17) false (stage1 I W)) at hc0
   have hx := run_one _ _ (exit_step false (stage1 I W) cm1)
   have hrun := run_comp (run_comp (run_comp he hf0) hc0) hx
   refine ⟨_,by omega,false,clean (stage1 I W),hrun,?_,?_⟩
   ·
     have hlen : ¬2*W.length+4≤I.length := by omega
     have hi : stage1 I W 0=[] := by
       rw [si1]
       apply List.drop_eq_nil_of_le
       skip
       omega
     refine ⟨by simp [hlen], ?_, ?_, ?_, by simp [clean], by simp, ?_⟩
     all_goals first | simpa [clean] using hi | simp [clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker]
   · simp [FieldsBound,clean,stage0,stage1,stage2,stage3,stage4,updated,tapes,field,marker,List.length_take]
end PEqualNP.Outside.L_lib_895_aux.RecordMachine

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
theorem packet_contract_bounded (A B R W : List Bool) (c d : Fin 4)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 ∃ t ≤ 30*W.length+100, ∃ v c' d' st,
 run t (cfg (some (rd 12)) true 0 0
   (RecordMachine.tapes (packet A (bits 2 c.val) B (bits 2 d.val) R) W [] [] [] [] [] [] [])) =
 some (cfg none v c' d' st) ∧ packetFinish A B R W c d v st ∧RecordMachine.FieldsBound W.length st := by
 by_cases hc : c.val<3
 · by_cases hd : d.val<3
   · obtain ⟨t,ht,v,hr,hv⟩ := index_packet_contract A B R W ⟨c.val,hc⟩ ⟨d.val,hd⟩ hA hB
     refine ⟨t,ht,v,asColor ⟨c.val,hc⟩,asColor ⟨d.val,hd⟩,RecordMachine.tapes R W [] [] A [] B [] [],hr,?_,?_⟩
     ·
       simp only [packetFinish,packetGood,hc,hd,true_and]
       exact ⟨hv,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
     · simp [RecordMachine.FieldsBound,hA,hB,bits_length]
   · have ed : d=3 := Fin.ext (by omega)
     subst d
     obtain ⟨t,ht,hr⟩ := reader_packet4 A B R W c 3 hA hB
     have hp := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 c.val) B (bits 2 3) []) 0 0)
     have hC := run_one _ _ (colorC_step ⟨c.val,hc⟩ 0 R W [] [] A B (bits 2 3) [])
     have hD := run_one _ _ (colorD_bad (asColor ⟨c.val,hc⟩) R W A B)
     have hx := run_one _ _ (reject_step (RecordMachine.tapes R W [] [] A [] B [] []) ((none,true),(asColor ⟨c.val,hc⟩,3)))
     have hrun := run_comp (run_comp (run_comp (run_comp hr hp) hC) hD) hx
     refine ⟨_,by omega,false,asColor ⟨c.val,hc⟩,3,RecordMachine.tapes R W [] [] A [] B [] [],hrun,?_,?_⟩
     ·
       simp [packetFinish,packetGood]
     · simp [RecordMachine.FieldsBound,hA,hB,bits_length]
 · have ec : c=3 := Fin.ext (by omega)
   subst c
   obtain ⟨t,ht,hr⟩ := reader_packet4 A B R W 3 d hA hB
   have hp := run_one _ _ (read_checked (RecordMachine.tapes R W [] [] A (bits 2 3) B (bits 2 d.val) []) 0 0)
   have hC := run_one _ _ (colorC_bad 0 R W A B (bits 2 d.val))
   have hx := run_one _ _ (reject_step (RecordMachine.tapes R W [] [] A [] B (bits 2 d.val) []) ((none,true),(3,0)))
   have hrun := run_comp (run_comp (run_comp hr hp) hC) hx
   refine ⟨_,by omega,false,3,0,RecordMachine.tapes R W [] [] A [] B (bits 2 d.val) [],hrun,?_,?_⟩
   ·
     simp [packetFinish,packetGood]
   · simp [RecordMachine.FieldsBound,hA,hB,bits_length]
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing
theorem reader_failure_call_bounded (I W : List Bool) (ha : I.length<2*W.length+4) :
 ∃ t ≤ 6*W.length+30, ∃ st,
 run t (initial I W)=some (cfg (some (ph 0)) false 0 0 st) ∧
 st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] ∧RecordMachine.FieldsBound W.length st := by
 obtain ⟨t,ht,v,st,hr,⟨hv,hW,h2,h3,h8,hs,hf⟩,hbound⟩ := RecordMachine.record_contract_bounded I W
 have hn : ¬2*W.length+4≤I.length := by omega
 have he : v=false := by simpa [hn] using hv
 rw [he] at hr
 have h := BoolCall.run_lift rks rls rss rret (0,0) (fun _ => [])
   RecordMachine.program program rbody t _ _ hr
 exact ⟨t,ht,st,h,hW,h2,h3,h8,hbound⟩

theorem validation_total_bounded (I W : List Bool) :
 ∃ t ≤ 30*W.length+100, ∃ v c d st,
 run t (initial I W)=some (cfg none v c d st) ∧
 v=decide (validationGood I W) ∧st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] ∧RecordMachine.FieldsBound W.length st ∧
 (v=true → st 0=fr I W.length ∧st 4=fa I W.length ∧st 6=fb I W.length) := by
 by_cases ha : 2*W.length+4≤I.length
 · obtain ⟨hA,hC,hB,hD⟩ := full_lengths I W.length ha
   let c : Fin 4 := ⟨wordValue (fc I W.length),by
     have hh := wordValue_lt (fc I W.length)
     simpa [hC] using hh⟩
   let d : Fin 4 := ⟨wordValue (fd I W.length),by
     have hh := wordValue_lt (fd I W.length)
     simpa [hD] using hh⟩
   have ec : bits 2 c.val=fc I W.length := by
     simpa only [c,hC] using bits_wordValue (fc I W.length)
   have ed : bits 2 d.val=fd I W.length := by
     simpa only [d,hD] using bits_wordValue (fd I W.length)
   obtain ⟨t,ht,v,c',d',st,hr,⟨hv,hR,hW,h2,h3,hFI,hFJ,h8⟩,hbound⟩ :=
     packet_contract_bounded (fa I W.length) (fb I W.length) (fr I W.length) W c d hA hB
   have ei : packet (fa I W.length) (bits 2 c.val) (fb I W.length) (bits 2 d.val) (fr I W.length)=I := by
     rw [ec,ed,←input_split]
   change run t (initial (packet _ _ _ _ _) W)=_ at hr
   rw [ei] at hr
   refine ⟨t,ht,v,c',d',st,hr,?_,hW,h2,h3,h8,hbound,?_⟩
   · simpa [validationGood,ha,packetGood,c,d] using hv
   · intro _
     exact ⟨hR,hFI,hFJ⟩
 · have hs : I.length<2*W.length+4 := by omega
   obtain ⟨t,ht,st,hr,hW,h2,h3,h8,hbound⟩ := reader_failure_call_bounded I W hs
   have hp := run_one _ _ (read_bad st 0 0)
   have hx := run_one _ _ (reject_step st ((none,false),(0,0)))
   have hrun := run_comp (run_comp hr hp) hx
   refine ⟨_,by omega,false,0,0,st,hrun,?_,hW,h2,h3,h8,hbound,by simp⟩
   simp [validationGood,ha]
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def decodedRecord (I : List Bool) (w : Nat) : Ban :=
 ((wordValue (fa I w),wordValue (fc I w)),(wordValue (fb I w),wordValue (fd I w)))
lemma encoded_good_decoded (n : Nat) (I : List Bool) :
 validationGood I (bits (width n) n) ↔
 2*width n+4≤I.length ∧legalRecord n (decodedRecord I (width n)) := by
 have hn : n<2^(width n) := Nat.lt_log2_self
 simp only [validationGood,bits_length,Compare.value_wordValue,wordValue_bits _ _ hn,
   legalRecord,decodedRecord]
 aesop

lemma packet_good_iff (A B R W : List Bool) (c d : Fin 4)
 (hA : A.length=W.length) (hB : B.length=W.length) :
 validationGood (packet A (bits 2 c.val) B (bits 2 d.val) R) W ↔packetGood A B W c d := by
 have hc : (bits 2 c.val).length=2 := bits_length _ _
 have hd : (bits 2 d.val).length=2 := bits_length _ _
 have hh := packet_slices A (bits 2 c.val) B (bits 2 d.val) R W hA hB hc hd
 have sa := congrArg (fun st => st 4) hh
 have sc := congrArg (fun st => st 5) hh
 have sb := congrArg (fun st => st 6) hh
 have sd := congrArg (fun st => st 7) hh
 simp only [RecordMachine.resultStacks,get4,get5,get6,get7] at sa sc sb sd
 have ha : 2*W.length+4≤(packet A (bits 2 c.val) B (bits 2 d.val) R).length := by
  simp only [packet,List.length_append,hA,hB,hc,hd]
  omega
 have vc : wordValue (bits 2 c.val)=c.val := wordValue_bits _ _ (by have := c.isLt;omega)
 have vd : wordValue (bits 2 d.val)=d.val := wordValue_bits _ _ (by have := d.isLt;omega)
 simp only [validationGood,ha,true_and,fa,fb,fc,fd,sa,sb,sc,sd,vc,vd,packetGood]

theorem validationGood_iff_prefix (n : Nat) (I : List Bool) :
 validationGood I (bits (width n) n) ↔
 ∃ e R, legalRecord n e ∧recordBits n e++R=I := by
 constructor
 · intro hg
   obtain ⟨ha,hl⟩ := (encoded_good_decoded n I).mp hg
   obtain ⟨hA,hC,hB,hD⟩ := full_lengths I (width n) ha
   refine ⟨decodedRecord I (width n),fr I (width n),hl,?_⟩
   have a := bits_wordValue (fa I (width n))
   have c := bits_wordValue (fc I (width n))
   have b := bits_wordValue (fb I (width n))
   have d := bits_wordValue (fd I (width n))
   rw [hA] at a
   rw [hC] at c
   rw [hB] at b
   rw [hD] at d
   simp only [recordBits,decodedRecord,a,b,c,d]
   simpa [packet,List.append_assoc] using (input_split I (width n)).symm
 · rintro ⟨⟨⟨i,c⟩,⟨j,d⟩⟩,R,hl,he⟩
   dsimp only [legalRecord] at hl
   obtain ⟨hij,hjn,hc,hd⟩ := hl
   have hn : n<2^(width n) := Nat.lt_log2_self
   have hi : i<2^(width n) := lt_trans (lt_trans hij hjn) hn
   have hj : j<2^(width n) := lt_trans hjn hn
   have ei : recordBits n ((i,c),(j,d))++R=
     packet (bits (width n) i) (bits 2 c) (bits (width n) j) (bits 2 d) R := by
     simp only [recordBits,packet,List.append_assoc]
   rw [←he,ei]
   apply (packet_good_iff (bits (width n) i) (bits (width n) j) R (bits (width n) n)
     ⟨c,by omega⟩ ⟨d,by omega⟩ (by simp only [bits_length]) (by simp only [bits_length])).mpr
   simp only [packetGood,Compare.value_wordValue,wordValue_bits _ _ hi,
     wordValue_bits _ _ hj,wordValue_bits _ _ hn]
   exact ⟨hc,hd,hij,hjn⟩
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def Result (n : Nat) (I : List Bool) (v : Bool) (st : Fin 9 → List Bool) : Prop :=
 (v=true ↔∃e R,legalRecord n e ∧recordBits n e++R=I) ∧
 st 1=bits (width n) n ∧st 2=[] ∧st 3=[] ∧st 8=[] ∧
 RecordMachine.FieldsBound (width n) st ∧
 (v=true → st 0=fr I (width n) ∧st 4=fa I (width n) ∧st 6=fb I (width n))

theorem validation_n_total (n : Nat) (I : List Bool) :
 ∃ t ≤ 30*width n+100, ∃ v c d st,
 run t (initial I (bits (width n) n))=some (cfg none v c d st) ∧Result n I v st := by
 obtain ⟨t,ht,v,c,d,st,hr,hv,hW,h2,h3,h8,hbound,hs⟩ := validation_total_bounded I (bits (width n) n)
 refine ⟨t,by simpa only [bits_length] using ht,v,c,d,st,hr,?_,hW,h2,h3,h8,?_,?_⟩
 · simpa only [hv,decide_eq_true_eq] using validationGood_iff_prefix n I
 · simpa only [bits_length] using hbound
 · simpa only [bits_length] using hs

theorem validation_n_evals (n : Nat) (I : List Bool) :
 ∃ v c d st, Nonempty (StateTransition.EvalsToInTime machine.step
   (initial I (bits (width n) n)) (some (cfg none v c d st)) (30*width n+100)) ∧Result n I v st := by
 obtain ⟨t,ht,v,c,d,st,hr,hs⟩ := validation_n_total n I
 refine ⟨v,c,d,st,?_,hs⟩
 rw [machine_step_eq]
 exact ⟨{steps:=t,evals_in_steps:=hr,steps_le_m:=ht}⟩

theorem failure_field_length (n : Nat) (I : List Bool) (v : Bool) (st : Fin 9 → List Bool)
 (h : Result n I v st) : ∀ k : Fin 9, 4≤k.val → k.val≤7 →
 (st k).length≤max (width n) 2 := by
 obtain ⟨_,_,_,_,_,hbound,_⟩ := h
 obtain ⟨h4,h5,h6,h7⟩ := hbound
 intro k hlo hhi
 fin_cases k <;> simp_all only [Fin.val_zero,Fin.val_one,Fin.reduceFinMk] <;> omega
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.RecordValid
open Turing

def noPush0 : TM2.Stmt (fun _ : Fin 9 => Bool) H S → Bool
 | .push k _ q => decide (k≠0) &&noPush0 q
 | .peek _ _ q | .pop _ _ q | .load _ q => noPush0 q
 | .branch _ q r => noPush0 q &&noPush0 r
 | .goto _ | .halt => true

lemma noPush0_stepAux (q : TM2.Stmt (fun _ : Fin 9 => Bool) H S) (hq : noPush0 q=true)
 (s : S) (st : Fin 9 → List Bool) :
 ((TM2.stepAux q s st).stk 0).length≤(st 0).length := by
 induction q generalizing s st with
 | push k f q ih =>
   have hp : k≠0 ∧noPush0 q=true := by simpa only [noPush0,Bool.and_eq_true,decide_eq_true_eq] using hq
   have hk := hp.1
   have hh := ih hp.2 s (Function.update st k (f s::st k))
   simpa [TM2.stepAux,Function.update_of_ne (Ne.symm hk)] using hh
 | peek k f q ih => exact ih hq (f s (st k).head?) st
 | pop k f q ih =>
   have hh := ih hq (f s (st k).head?) (Function.update st k (st k).tail)
   change ((TM2.stepAux q (f s (st k).head?) (Function.update st k (st k).tail)).stk 0).length≤_
   by_cases hk : k=0
   · subst k
     simp only [Function.update_self] at hh
     exact hh.trans (by cases st 0 <;> simp)
   · simpa [Function.update_of_ne (Ne.symm hk)] using hh
 | load f q ih => exact ih hq (f s) st
 | branch f q r iq ir =>
   have hp : noPush0 q=true ∧noPush0 r=true := by simpa only [noPush0,Bool.and_eq_true] using hq
   obtain ⟨hq,hr⟩ := hp
   cases he : f s
   · simpa [TM2.stepAux,he] using ir hr s st
   · simpa [TM2.stepAux,he] using iq hq s st
 | goto f => exact le_rfl
 | halt => exact le_rfl

theorem program_noPush0 : ∀ l : H,noPush0 (program l)=true := by decide

lemma step_input_length (a b : Cfg) (h : TM2.step program a=some b) :
 (b.stk 0).length≤(a.stk 0).length := by
 rcases a with ⟨l,s,st⟩
 cases l with
 | none => simp [TM2.step] at h
 | some l =>
   have he : TM2.stepAux (program l) s st=b := Option.some.inj h
   rw [←he]
   exact noPush0_stepAux (program l) (program_noPush0 l) s st

lemma iterate_none (t : Nat) : (flip bind (TM2.step program))^[t] none=none := by
 induction t with
 | zero => rfl
 | succ t ih => rw [Function.iterate_succ_apply];exact ih

theorem run_input_length {t : Nat} {a b : Cfg} (h : run t a=some b) :
 (b.stk 0).length≤(a.stk 0).length := by
 induction t generalizing a with
 | zero => have he : a=b := Option.some.inj h;rw [he]
 | succ t ih =>
   unfold run at h
   rw [Function.iterate_succ_apply] at h
   cases hs : TM2.step program a with
   | none =>
     have he : flip bind (TM2.step program) (some a)=none := hs
     rw [he,iterate_none] at h
     cases h
   | some a' =>
     have he : flip bind (TM2.step program) (some a)=some a' := hs
     rw [he] at h
     exact (ih h).trans (step_input_length a a' hs)

theorem validation_n_total_resources (n : Nat) (I : List Bool) :
 ∃ t ≤ 30*width n+100, ∃ v c d st,
 run t (initial I (bits (width n) n))=some (cfg none v c d st) ∧
 Result n I v st ∧(st 0).length≤I.length := by
 obtain ⟨t,ht,v,c,d,st,hr,hs⟩ := validation_n_total n I
 refine ⟨t,ht,v,c,d,st,hr,hs,?_⟩
 exact run_input_length hr
end PEqualNP.Outside.L_lib_895_aux.RecordValid

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine
open Turing

def extend (st : Fin 9 → List Bool) (R : List Bool) : Fin 10 → List Bool :=
 fun j => if h : j.val<9 then st ⟨j.val,h⟩ else R
lemma r_lift_full (l : Option RecordValid.H) (v : Bool) (c d : Fin 4)
 (st : Fin 9 → List Bool) (R : List Bool) :
 BoolCall.liftCfg rks rls rss rret 0 (fun _ => R) (RecordValid.cfg l v c d st) =
 cfg (some (l.elim (ph 1) rv)) (cs v c d) (extend st R) := by
 apply cfg_ext
 · cases l <;> rfl
 · rfl
 · funext j; fin_cases j <;> rfl

lemma enter_nonempty (I W R : List Bool) (hne : I≠[]) :
 run 1 (cfg (some (ph 0)) initialState (stk I W [] [] R)) =
 some (cfg (some (rv (RecordValid.rd 12))) initialState (stk I W [] [] R)) := by
 cases I with
 | nil => exact False.elim (hne rfl)
 | cons b I => exact run_one _ _ (loop_step b I W R)
lemma bad_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 1)) (cs false c d) st) =
 some (cfg (some (ph 5)) (cs false c d) st) := rfl
lemma failure_step (c d : Fin 4) (st : Fin 10 → List Bool) :
 TM2.step program (cfg (some (ph 5)) (cs false c d) st) =
 some (cfg none failureState st) := rfl

theorem lift_bad_validation (I W R : List Bool) (hne : I≠[]) (t : Nat) (c d : Fin 4)
 (st : Fin 9 → List Bool)
 (hr : RecordValid.run t (RecordValid.initial I W)=some (RecordValid.cfg none false c d st)) :
 run (t+3) (cfg (some (ph 0)) initialState (stk I W [] [] R)) =
 some (cfg none failureState (extend st R)) := by
 have h := BoolCall.run_lift rks rls rss rret 0 (fun _ => R)
   RecordValid.program program rbody t _ _ hr
 unfold RecordValid.initial at h
 rw [r_lift,r_lift_full] at h
 have h := run_comp (enter_nonempty I W R hne) h
 have h := run_comp h (run_one _ _ (bad_step c d (extend st R)))
 have h := run_comp h (run_one _ _ (failure_step c d (extend st R)))
 rw [show 1+t+1+1=t+3 by omega] at h
 exact h

def BadCore (w : Nat) (W R : List Bool) (st : Fin 10 → List Bool) : Prop :=
 st 1=W ∧st 2=[] ∧st 3=[] ∧st 8=[] ∧
 (st 4).length≤w ∧(st 5).length≤2 ∧(st 6).length≤w ∧(st 7).length≤2 ∧st 9=R

lemma extend_bad_core (w : Nat) (W R : List Bool) (st : Fin 9 → List Bool)
 (hW : st 1=W) (h2 : st 2=[]) (h3 : st 3=[]) (h8 : st 8=[])
 (hf : RecordMachine.FieldsBound w st) : BadCore w W R (extend st R) := by
 exact ⟨hW,h2,h3,h8,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,rfl⟩

theorem bad_iteration_fields (n : Nat) (I R : List Bool) (hne : I≠[])
 (hbad : ¬∃ e J, legalRecord n e ∧recordBits n e++J=I) :
 ∃ t ≤ 50*width n+200, ∃ st,
 run t (cfg (some (ph 0)) initialState (stk I (bits (width n) n) [] [] R)) =
   some (cfg none failureState st) ∧BadCore (width n) (bits (width n) n) R st := by
 obtain ⟨t,ht,v,c,d,st,hr,hv,hW,h2,h3,h8,hf,hs⟩ :=
   RecordValid.validation_total_bounded I (bits (width n) n)
 have hng : ¬RecordValid.validationGood I (bits (width n) n) := by
   intro hg
   exact hbad ((RecordValid.validationGood_iff_prefix n I).mp hg)
 have he : v=false := by rw [hv]; simp [hng]
 rw [he] at hr
 have h := lift_bad_validation I (bits (width n) n) R hne t c d st hr
 refine ⟨t+3,?_,extend st R,h,?_⟩
 · rw [bits_length] at ht
   omega
 · apply extend_bad_core _ _ _ _ hW h2 h3 h8
   rw [bits_length] at hf
   exact hf

theorem bad_iteration_root (n : Nat) (I R : List Bool) (_hn : 2≤n) (hne : I≠[])
 (hbad : ¬∃ e J, legalRecord n e ∧recordBits n e++J=I) :
 ∃ t ≤ 50*width n+200, ∃ st,
 run t (cfg (some (ph 0)) initialState (stk I (bits (width n) n) [] [] R)) =
   some (cfg none failureState st) ∧BadCore (width n) (bits (width n) n) R st ∧(st 0).length≤I.length := by
 obtain ⟨t,ht,v,c,d,st,hr,hv,hW,h2,h3,h8,hf,hs⟩ :=
   RecordValid.validation_total_bounded I (bits (width n) n)
 have hng : ¬RecordValid.validationGood I (bits (width n) n) := by
   intro hg
   exact hbad ((RecordValid.validationGood_iff_prefix n I).mp hg)
 have he : v=false := by rw [hv]; simp [hng]
 rw [he] at hr
 have hI := RecordValid.run_input_length hr
 have h := lift_bad_validation I (bits (width n) n) R hne t c d st hr
 refine ⟨t+3,?_,extend st R,h,?_,?_⟩
 · rw [bits_length] at ht
   omega
 · apply extend_bad_core _ _ _ _ hW h2 h3 h8
   rw [bits_length] at hf
   exact hf
 · exact hI

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine

def TapeBounds (n : Nat) (I R : List Bool) (st : Fin 10 → List Bool) : Prop :=
 (∀ k : Fin 9, (st k.castSucc).length≤I.length+width n+2) ∧
 (st 9).length≤R.length+I.length*(4*width n+12)

theorem banWord_length (n : Nat) (e : Ban) (hn : 2≤n) :
 (banWord n e).length=4*width n+12 := by
 change (bits (width (8*n+1)) (8*e.1.1+2+2*e.1.2) ++
   (bits (width (8*n+1)) (8*e.1.1+3+2*e.1.2) ++
   (bits (width (8*n+1)) (8*e.2.1+2+2*e.2.2) ++
   (bits (width (8*n+1)) (8*e.2.1+3+2*e.2.2) ++ [])))).length = _
 simp only [List.length_append,List.length_nil,bits_length]
 rw [output_width_exact n hn]
 omega

theorem empty_bounds (n : Nat) (R : List Bool) :
 TapeBounds n [] R (stk [] (bits (width n) n) [] [] R) := by
 constructor
 · intro k
   fin_cases k <;> simp [stk,bits_length]
 · simp [stk]

theorem bad_bounds (n : Nat) (I R : List Bool) (st : Fin 10 → List Bool)
 (hc : BadCore (width n) (bits (width n) n) R st) (hi : (st 0).length≤I.length) :
 TapeBounds n I R st := by
 obtain ⟨h1,h2,h3,h8,h4,h5,h6,h7,h9⟩ := hc
 have hw : (st 1).length=width n := by rw [h1,bits_length]
 have h2l : (st 2).length=0 := congrArg List.length h2
 have h3l : (st 3).length=0 := congrArg List.length h3
 have h8l : (st 8).length=0 := congrArg List.length h8
 constructor
 · intro k
   fin_cases k
   · change (st 0).length≤I.length+width n+2
     omega
   · change (st 1).length≤I.length+width n+2
     omega
   · change (st 2).length≤I.length+width n+2
     omega
   · change (st 3).length≤I.length+width n+2
     omega
   · change (st 4).length≤I.length+width n+2
     omega
   · change (st 5).length≤I.length+width n+2
     omega
   · change (st 6).length≤I.length+width n+2
     omega
   · change (st 7).length≤I.length+width n+2
     omega
   · change (st 8).length≤I.length+width n+2
     omega
 · rw [h9]
   omega

theorem head_bounds (n : Nat) (e : Ban) (J R : List Bool) (st : Fin 10 → List Bool) (hn : 2≤n)
 (hc : TapeBounds n J ((banWord n e).reverse++R) st) :
 TapeBounds n (recordBits n e++J) R st := by
 obtain ⟨hs,ho⟩ := hc
 constructor
 · intro k
   have hk := hs k
   simp only [List.length_append]
   omega
 · simp only [List.length_append,List.length_reverse] at ho ⊢
   rw [banWord_length n e hn] at ho
   have hp : 1≤(recordBits n e).length := by rw [recordBits_length]; omega
   have hm := Nat.mul_le_mul_right (4*width n+12) hp
   nlinarith
end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.GlobalBadBounds

lemma quadratic_pos (L : Nat) : 1≤(L+1)^2 := Nat.one_le_pow 2 (L+1) (by omega)

lemma first_nine_budget (L w i : Nat) (hi : i≤L) (hw : w≤L+1) :
 i+w+2≤1024*(L+1)^2 := by nlinarith

lemma output_growth_budget (L w i : Nat) (hi : i≤L) (hw : w≤L+1) :
 i*(4*w+12)≤24*(L+1)^2 := by
 have hm := Nat.mul_le_mul hi (show 4*w+12≤4*(L+1)+12 by omega)
 nlinarith

theorem all_tape_bounds (n : Nat) (I R : List Bool) (st : Fin 10 → List Bool) (L : Nat)
 (h : TailMachine.TapeBounds n I R st) (hi : I.length≤L) (hw : width n≤L+1)
 (hr : R.length≤1000*(L+1)^2) :
 ∀ k : Fin 10,(st k).length≤1024*(L+1)^2 := by
 obtain ⟨hs,ho⟩ := h
 intro k
 by_cases hk : k.val<9
 · let j : Fin 9 := ⟨k.val,hk⟩
   have he : j.castSucc=k := Fin.ext rfl
   have hh := hs j
   rw [he] at hh
   exact hh.trans (first_nine_budget L (width n) I.length hi hw)
 · have he : k=9 := Fin.ext (by omega)
   subst k
   have hm := output_growth_budget L (width n) I.length hi hw
   omega

theorem tail_time_bound (i w L : Nat) (hi : i≤L) (hw : w≤L+1) :
 (i+1)*(50*w+200)+1≤300*(L+1)^2 := by
 have hm := Nat.mul_le_mul (show i+1≤L+1 by omega)
   (show 50*w+200≤50*(L+1)+200 by omega)
 nlinarith

theorem tail_time_from_resources (n : Nat) (I : List Bool) (L : Nat)
 (hi : I.length≤L) (hw : width n≤L+1) :
 (I.length+1)*(50*width n+200)+1≤300*(L+1)^2 :=
 tail_time_bound I.length (width n) L hi hw

theorem global_bad_budget (L : Nat) :
 1000*(L+1)^2+300*(L+1)^2+(11*(1024*(L+1)^2+1)+4)+3≤
 1000000*(L+1)^2 := by
 have hp := quadratic_pos L
 nlinarith

theorem combined_time (front tail abort L : Nat)
 (hf : front≤1000*(L+1)^2) (ht : tail≤300*(L+1)^2)
 (ha : abort≤11*(1024*(L+1)^2+1)+4) :
 front+tail+abort+3≤1000000*(L+1)^2 := by
 have hb := global_bad_budget L
 omega

theorem bad_branch_resources (n : Nat) (I R : List Bool) (st : Fin 10 → List Bool) (L : Nat)
 (h : TailMachine.TapeBounds n I R st) (hi : I.length≤L) (hw : width n≤L+1)
 (hr : R.length≤1000*(L+1)^2) :
 (∀ k : Fin 10,(st k).length≤1024*(L+1)^2) ∧
 (I.length+1)*(50*width n+200)+1≤300*(L+1)^2 ∧
 1000*(L+1)^2+300*(L+1)^2+(11*(1024*(L+1)^2+1)+4)+3≤1000000*(L+1)^2 :=
 ⟨all_tape_bounds n I R st L h hi hw hr,tail_time_from_resources n I L hi hw,global_bad_budget L⟩
end PEqualNP.Outside.L_lib_895_aux.GlobalBadBounds

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine

def HasPayload (n : Nat) (I : List Bool) : Prop :=
  ∃ B : List Ban, (∀ e∈B,legalRecord n e) ∧ I=recordPayload n B

lemma hasPayload_nil (n : Nat) : HasPayload n [] :=
  ⟨[],by simp,rfl⟩

lemma hasPayload_head (n : Nat) (e : Ban) (I : List Bool) (hl : legalRecord n e) :
    HasPayload n (recordBits n e++I) ↔ HasPayload n I := by
  constructor
  · rintro ⟨B,hB,hEq⟩
    cases B with
    | nil =>
      have hh := congrArg List.length hEq
      simp only [List.length_append,recordBits_length,recordPayload_nil,List.length_nil] at hh
      omega
    | cons e' B =>
      have hEq' : recordBits n e++I = recordBits n e'++recordPayload n B := by
        simpa only [recordPayload_cons] using hEq
      have hr := Parser.readRecord_complete n e I hl
      have hr' := Parser.readRecord_complete n e' (recordPayload n B) (hB e' List.mem_cons_self)
      rw [hEq'] at hr
      have hp := Option.some.inj (hr.symm.trans hr')
      refine ⟨B,fun a ha => hB a (List.mem_cons_of_mem e' ha),?_⟩
      exact congrArg Prod.snd hp
  · rintro ⟨B,hB,hI⟩
    refine ⟨e::B,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hl
      · exact hB a ha
    · rw [recordPayload_cons,hI]

lemma legal_record_nonempty (n : Nat) (e : Ban) (I : List Bool) : recordBits n e++I ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [List.length_append,recordBits_length,List.length_nil] at hh
  omega

lemma hasPayload_nonempty_head (n : Nat) (I : List Bool) (hne : I≠[]) (h : HasPayload n I) :
    ∃ e J, legalRecord n e ∧recordBits n e++J=I := by
  obtain ⟨B,hB,hI⟩ := h
  cases B with
  | nil => exact False.elim (hne hI)
  | cons e B =>
    exact ⟨e,recordPayload n B,hB e List.mem_cons_self,hI.symm⟩

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.TailMachine

def Result (n : Nat) (I R : List Bool) (c : Cfg) : Prop :=
  c.l=none ∧TapeBounds n I R c.stk ∧
    ((∃ B : List Ban, (∀ e∈B,legalRecord n e) ∧ I=recordPayload n B ∧
      c=cfg none initialState (stk [] (bits (width n) n) [] [] ((banPayload n B).reverse++R))) ∨
      (c.var=failureState ∧¬HasPayload n I))

theorem total_run (n : Nat) (I R : List Bool) (hn : 2≤n) :
    ∃ t ≤ (I.length+1)*(50*width n+200)+1, ∃ c,
      run t (cfg (some (ph 0)) initialState (stk I (bits (width n) n) [] [] R)) = some c ∧
      Result n I R c := by
  induction hlen : I.length using Nat.strong_induction_on generalizing I R with
  | ind l ih =>
    by_cases hnil : I=[]
    · subst I
      refine ⟨1,by simp, cfg none initialState (stk [] (bits (width n) n) [] [] R),?_,?_⟩
      · exact run_one _ _ (loop_empty (bits (width n) n) R)
      · exact ⟨rfl,empty_bounds n R,Or.inl ⟨[],by simp,rfl,rfl⟩⟩
    · by_cases hhead : ∃ e J, legalRecord n e ∧recordBits n e++J=I
      · obtain ⟨e,J,he,hEq⟩ := hhead
        have hlt : J.length<l := by
          have hh := congrArg List.length hEq
          simp only [List.length_append,recordBits_length] at hh
          omega
        obtain ⟨u,hu,hru⟩ := iteration_legal n e hn he J R
        rw [hEq] at hru
        obtain ⟨v,hv,c,hrv,hc⟩ := ih J.length hlt J ((banWord n e).reverse++R) rfl
        have hmul := Nat.mul_le_mul_right (50*width n+200)
          (show J.length+2≤I.length+1 by omega)
        refine ⟨u+v,by nlinarith,c,run_comp hru hrv,?_⟩
        refine ⟨hc.1,?_,?_⟩
        · have hb := head_bounds n e J R c.stk hn hc.2.1
          rw [hEq] at hb
          exact hb
        · rcases hc.2.2 with hg | hb
          · obtain ⟨B,hB,hJ,hfinal⟩ := hg
            refine Or.inl ⟨e::B,?_,?_,?_⟩
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact he
              · exact hB a ha
            · rw [←hEq,recordPayload_cons,hJ]
            · rw [hfinal]
              simp only [banPayload_cons,List.reverse_append,List.append_assoc,banWord,banEncoding]
          · refine Or.inr ⟨hb.1,?_⟩
            intro hgood
            apply hb.2
            apply (hasPayload_head n e J he).mp
            rw [hEq]
            exact hgood
      · obtain ⟨t,ht,st,hr,hcore,hinput⟩ := bad_iteration_root n I R hn hnil hhead
        have hm := Nat.mul_le_mul_right (50*width n+200) (show 1≤I.length+1 by omega)
        refine ⟨t,by nlinarith,cfg none failureState st,hr,?_⟩
        refine ⟨rfl,bad_bounds n I R st hcore hinput,Or.inr ⟨rfl,?_⟩⟩
        exact fun hg => hhead (hasPayload_nonempty_head n I hnil hg)

lemma result_success {n : Nat} {I R : List Bool} {c : Cfg} (h : Result n I R c)
    (hv : c.var.1.1.2=true) :
    ∃ B : List Ban, (∀ e∈B,legalRecord n e) ∧ I=recordPayload n B ∧
      c=cfg none initialState (stk [] (bits (width n) n) [] [] ((banPayload n B).reverse++R)) := by
  rcases h.2.2 with hg | hb
  · exact hg
  · rw [hb.1] at hv
    cases hv

lemma result_failure {n : Nat} {I R : List Bool} {c : Cfg} (h : Result n I R c)
    (hv : c.var.1.1.2=false) : ¬HasPayload n I := by
  rcases h.2.2 with hg | hb
  · obtain ⟨B,hB,hI,hc⟩ := hg
    rw [hc] at hv
    cases hv
  · exact hb.2

end PEqualNP.Outside.L_lib_895_aux.TailMachine

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

lemma tail_to_abort (Q : Fin 10 → List Bool) :
    TM2.step program (tailCfg (Front.clean true) (none,false) (fun _ => [])
      (TailMachine.cfg none TailMachine.failureState Q)) =
      some (finishCfg (Front.clean true) TailMachine.failureState
        (Finisher.cfg (some .abort) (Finisher.join Q []))) := by
  dsimp [tailCfg,finishCfg,BoolCall.liftCfg,TailMachine.cfg,Finisher.cfg,
    TM2.step,program,TM2.stepAux,lsTail,lsFinish,retTail,retFinish,CallLayout.optionSplit,
    ssTail,ssFinish,TailMachine.failureState]
  simp only [Bool.cond_false]
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext (k : Fin 11); fin_cases k <;> rfl

set_option maxRecDepth 4096 in
theorem record_rejection : RecordRejection := by
  intro n I hn hbad
  let L := (header n++I).length
  obtain ⟨u,hu,c,hr,hc⟩ := TailMachine.total_run n I (blockBuilder n) hn
  have hfail : c.var=TailMachine.failureState := by
    rcases hc.2.2 with hg | hb
    · obtain ⟨B,hB,hI,hfinal⟩ := hg
      exact False.elim (hbad ⟨B,hB,hI⟩)
    · exact hb.1
  have hec : c=TailMachine.cfg none TailMachine.failureState c.stk :=
    TailMachine.cfg_ext _ _ hc.1 hfail rfl
  have hr' := hr.trans (congrArg some hec)
  have ht : StateTransition.EvalsToInTime (TM2.step TailMachine.program) (tailInitial n I)
      (some (TailMachine.cfg none TailMachine.failureState c.stk))
      ((I.length+1)*(50*width n+200)+1) :=
    { steps := u, evals_in_steps := hr', steps_le_m := hu }
  have hf := global_tail_entry_evals n I hn
  have htg := tail_evals (Front.clean true) (none,false) (fun _ => []) _ _ _ ht
  have h0 := join_evals (TM2.step program) _ _ _ _ _ hf htg
  have hs := step_evals (TM2.step program) _ _ (tail_to_abort c.stk)
  have h1 := join_evals (TM2.step program) _ _ _ _ _ h0 hs
  have hnL : n+1≤L := by dsimp [L]; simp [header]
  have hiL : I.length≤L := by dsimp [L]; simp [header] <;> omega
  have hwL := CodecBridge.width_le_budget n L hnL
  have hR : (blockBuilder n).length≤1000*(L+1)^2 := by
    have hh := CodecBridge.accepted_prefix_output_bound n [] L hn (by simp) (by simpa [CodecBridge.payload] using hnL)
    simpa [blockBuilder,CodecBridge.packed] using hh
  have hten := GlobalBadBounds.all_tape_bounds n I (blockBuilder n) c.stk L hc.2.1 hiL hwL hR
  have hall : ∀ k : Fin 11,(Finisher.join c.stk [] k).length≤1024*(L+1)^2 := by
    intro k
    by_cases hk : k.val<10
    · simpa only [Finisher.join,dif_pos hk] using hten ⟨k.val,hk⟩
    · simp [Finisher.join,hk]
  have ha := global_abort_evals (Front.clean true) TailMachine.failureState
    (Finisher.join c.stk []) (1024*(L+1)^2) hall
  have whole := join_evals (TM2.step program) _ _ _ _ _ h1 ha
  refine ⟨whole.steps,?_,whole.evals_in_steps⟩
  have hsteps := whole.steps_le_m
  have htime := GlobalBadBounds.tail_time_from_resources n I L hiL hwL
  have hbound := GlobalBadBounds.global_bad_budget L
  nlinarith
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

namespace PEqualNP.Outside.L_lib_895_aux.GlobalShell
open Turing

theorem all_inputs_run (x : List Bool) :
    ∃ u ≤ 1000000*(x.length+1)^2,
      Run u (initialCfg x) (haltList machine (totalOutput x)) :=
  total_runs_of_record_rejection record_rejection x

noncomputable def total_evals (x : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program) (initialCfg x)
      (some (haltList machine (totalOutput x))) (1000000*(x.length+1)^2) :=
  all_evals_of_record_rejection record_rejection x

noncomputable def totalComputer :
    TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput :=
  computer_of_runs totalOutput total_evals

lemma totalComputer_finite_alphabets : ∀ j, Finite (totalComputer.tm.Γ j) := finite_alphabets
lemma totalComputer_time (z : Nat) : totalComputer.time z=1000000*(z+1)^2 := rfl

theorem machine_exists :
    ∃ C : Nat, ∃ M : TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) totalOutput,
      (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z≤C*(z+1)^2 :=
  machine_exists_of_record_rejection record_rejection
end PEqualNP.Outside.L_lib_895_aux.GlobalShell

theorem PEqualNP.Outside.L_lib_895 :
let bits := fun (w v : Nat) => (List.range w).map (fun j => v.testBit j)
let header := fun n : Nat => List.replicate n true ++ [false]
let width := fun n : Nat => n.log2+1
let Ban := (Nat × Nat) × (Nat × Nat)
let legal := fun (n : Nat) (B : List Ban) => 2 ≤ n ∧ ∀ e ∈ B,
  e.1.1 < e.2.1 ∧ e.2.1 < n ∧ e.1.2 < 3 ∧ e.2.2 < 3
let enc := fun (n : Nat) (B : List Ban) =>
  header n ++ B.flatMap (fun e => bits (width n) e.1.1 ++ bits 2 e.1.2 ++
    bits (width n) e.2.1 ++ bits 2 e.2.2)
let valid := fun (n : Nat) (B : List Ban) (a : Fin n → Fin 3) =>
  let v := List.ofFn (fun j => (a j).val)
  ∀ e ∈ B, v.getD e.1.1 3 ≠ e.1.2 ∨ v.getD e.2.1 3 ≠ e.2.2
let pack := fun (k : Nat) (rows : List (List Nat)) =>
  header k ++ rows.flatMap (fun row => row.flatMap (bits (width k)))
let well := fun (k : Nat) (rows : List (List Nat)) => ∀ row ∈ rows,
  row.length = 4 ∧ row.Nodup ∧ ∀ v ∈ row, v < k
let wins := fun (k : Nat) (rows : List (List Nat)) (P : Equiv.Perm (Fin k)) =>
  Function.Involutive P ∧ ∀ row ∈ rows, ∃ u : Fin k, u.val ∈ row ∧
    (P u).val ∈ row ∧ P u ≠ u
let emit := fun (n : Nat) (B : List Ban) =>
  let flag := fun (i c : Nat) => [8*i+2+2*c,8*i+3+2*c]
  let block := fun (i : Nat) =>
    [[8*i,8*i+2,8*i+4,8*i+6]] ++ (List.range 3).flatMap (fun c =>
      (List.range 2).flatMap (fun b => (List.range 4).map (fun j =>
        [8*i+b] ++ flag i c ++ [8*((i+1)%n)+j])))
  (List.range n).flatMap block ++ B.map (fun e => flag e.1.1 e.1.2 ++ flag e.2.1 e.2.2)
∃ (f : List Bool → List Bool) (C : Nat),
  (∃ M : Turing.TM2ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) f,
    (∀ j, Finite (M.tm.Γ j)) ∧ ∀ z, M.time z ≤ C*(z+1)^2) ∧
  (∀ x : List Bool, (¬ ∃ n B, legal n B ∧ enc n B = x) → f x = []) ∧
  ∀ n B, legal n B →
    let k := 8*n+1
    let rows := emit n B
    f (enc n B) = pack k rows ∧ well k rows ∧ rows.length = 25*n+B.length ∧
      (pack k rows).length = k+1+4*(25*n+B.length)*width k ∧
      Nonempty ({a : Fin n → Fin 3 // valid n B a} ≃
        {P : Equiv.Perm (Fin k) // wins k rows P}) := by
  exact PEqualNP.Outside.L_lib_895_aux.target_of_quadratic_machine
    PEqualNP.Outside.L_lib_895_aux.GlobalShell.machine_exists
