import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_537

def rot (s word : Nat) : Nat := ((word <<< (s % 17)) ||| (word >>> (17 - s % 17))) % 2 ^ 17

def step (word : Nat) : Nat :=
  (List.range 17).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))).toNat <<< b)) 0

def fstep (w : Nat) : Nat :=
  (w &&& (2 ^ 17 - 1)) ^^^ (((2 ^ 17 - 1) ^^^
    ((((w &&& (2 ^ 17 - 1)) >>> 1) ||| ((w &&& (2 ^ 17 - 1)) <<< 16)) &&& (2 ^ 17 - 1))) &&&
    ((((w &&& (2 ^ 17 - 1)) >>> 2) ||| ((w &&& (2 ^ 17 - 1)) <<< 15)) &&& (2 ^ 17 - 1)))

def outputW (st : Nat → Nat) (w : Nat) : Nat :=
  ((List.range 4).foldl (fun x t =>
    st (x ^^^ rot 1 x ^^^ rot (17 - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (17 + (t + 1)) % 2 ^ 17)) (rot 1 w)) >>> 8

def passW (st : Nat → Nat) (key name : Nat) : Nat :=
  (List.range 4).foldl (fun state j =>
    st (state ^^^ rot 2 state ^^^ rot (17 - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (17 + (4 + (j + 1))) % 2 ^ 17))
    (rot 3 key ^^^ name)

theorem fold_bit (g : Nat → Bool) (i : Nat) : ∀ n,
    ((List.range n).foldl (fun acc b => acc ||| (g b).toNat <<< b) 0).testBit i =
      (decide (i < n) && g i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih]
    by_cases hin : i = n
    · subst hin
      cases g i <;> simp [Nat.testBit_shiftLeft]
    · cases hg : g n
      · simp only [Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_testBit, Bool.or_false]
        by_cases h : i < n
        · simp [h, show i < n + 1 by omega]
        · simp [h, show ¬ i < n + 1 by omega]
      · rw [Bool.toNat_true, Nat.one_shiftLeft, Nat.testBit_two_pow]
        have hni : ¬ n = i := fun e => hin e.symm
        by_cases h : i < n
        · simp [h, hni, show i < n + 1 by omega]
        · simp [h, hni, show ¬ i < n + 1 by omega]

theorem step_bit (w i : Nat) : (step w).testBit i = (decide (i < 17) && xor (w.testBit i)
    (!(w.testBit ((i + 1) % 17)) && w.testBit ((i + 2) % 17))) :=
  fold_bit (fun b => xor (w.testBit b)
    (!(w.testBit ((b + 1) % 17)) && w.testBit ((b + 2) % 17))) i 17

theorem step_eq (w : Nat) : step w = fstep w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [step_bit]
  have hm : ∀ j, Nat.testBit 131071 j = decide (j < 17) := fun j => by
    simpa using Nat.testBit_two_pow_sub_one 17 j
  unfold fstep
  by_cases hi : i < 17
  · interval_cases i <;> simp [-Nat.testBit_zero, hm, Nat.testBit_xor, Nat.testBit_and,
      Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  · simp [hi, hm, Nat.testBit_xor, Nat.testBit_and]

def negs : List Nat := [1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29]

def tab : List (Nat × Nat × Nat) := [(1241, 9, 21523), (1659, 6, 102457), (2313, 14, 123427), (3011, 6, 14000), (3241, 2, 28962), (3395, 1, 40064), (4906, 1, 82872), (5098, 6, 26512), (8753, 10, 36330), (9546, 6, 121161), (9795, 3, 89265), (11251, 2, 15634), (11386, 29, 37674), (11632, 1, 85721), (12371, 7, 103792), (13203, 2, 113384), (13489, 12, 40849), (15560, 22, 100912), (16411, 2, 16411), (19528, 26, 8587), (19883, 9, 99394), (23130, 2, 26370), (24384, 1, 31001), (26907, 22, 92761), (27952, 2, 113384), (28923, 1, 82787), (32834, 3, 48555), (33816, 10, 88096), (34530, 2, 40264), (35672, 6, 30264), (38410, 1, 129513), (38817, 18, 43240), (40265, 15, 8762), (40931, 9, 59290), (41354, 3, 47866), (41665, 10, 4523), (42641, 26, 8587), (44251, 1, 130656), (44872, 2, 38593), (47066, 3, 7123), (47312, 6, 95720), (48585, 10, 118136), (48744, 14, 62755), (50091, 6, 50417), (50138, 2, 80280), (52274, 12, 62194), (57898, 1, 58928), (59025, 2, 28962), (59880, 1, 77025), (60275, 2, 40099), (62113, 1, 72242), (62403, 3, 125402), (64171, 7, 9306), (64584, 1, 129552), (65104, 10, 75761), (66136, 2, 96288), (66954, 1, 20819), (66993, 3, 45162), (67123, 2, 86515), (68680, 2, 89122), (69009, 6, 38296), (69704, 1, 30472), (70443, 7, 96137), (71177, 2, 88987), (72314, 14, 62755), (73579, 1, 77339), (74250, 15, 87761), (74505, 2, 97730), (74985, 10, 11410), (75107, 1, 2857), (75169, 1, 106514), (76896, 14, 122659), (77130, 2, 41256), (79491, 1, 101320), (80835, 3, 28491), (80946, 3, 27785), (81451, 15, 5305), (81779, 10, 59339), (84179, 1, 81456), (84194, 3, 13115), (84721, 1, 55672), (85643, 3, 116633), (85754, 3, 12569), (86545, 6, 5635), (87240, 1, 37121), (87563, 2, 129938), (89443, 22, 53994), (90488, 6, 90488), (91938, 11, 45825), (92706, 1, 69066), (93657, 1, 130128), (94873, 9, 86650), (95128, 2, 86515), (96241, 7, 33032), (96753, 1, 121569), (96760, 2, 75097), (99770, 1, 110128), (100216, 14, 82315), (101203, 2, 22283), (102067, 3, 54818), (103224, 12, 130760), (103499, 6, 128713), (104265, 11, 53562), (104497, 7, 19073), (104714, 6, 106018), (106697, 6, 116626), (108089, 6, 39992), (110082, 2, 115010), (110130, 22, 86426), (110738, 14, 122659), (111915, 2, 15384), (113010, 6, 102457), (113321, 3, 7680), (113833, 6, 75768), (114056, 1, 16683), (115323, 2, 19881), (115936, 7, 45072), (115970, 3, 101001), (119210, 6, 127794), (119322, 3, 62793), (120345, 2, 38593), (124624, 2, 79107), (124944, 1, 23209), (126874, 7, 45072), (127040, 7, 120019), (129762, 3, 64866)]

def chk0 (w : Nat) : Bool := !(passW fstep w 0 < 2 ^ 8) || w.testBit 2 || tab.any (fun t => t.1 == w)

def chkZ (w : Nat) : Bool := !(outputW fstep w == 0) ||
  (negs.all (fun c => !(passW fstep w c < 2 ^ 8)) && (!(w.testBit 2) || !(passW fstep w 0 < 2 ^ 8)))

theorem cover (p : Nat → Bool) (h : ∀ b < 8, ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    p ((hi + 16 * b) * 1024 + lo) = true) : ∀ w < 2 ^ 17, p w = true := by
  intro w hw
  have hw' : w < 131072 := by simpa using hw
  have := h (w / 16384) (by omega) (w / 1024 % 16) (List.mem_range.2 (by omega)) (w % 1024)
    (List.mem_range.2 (by omega))
  have e : (w / 1024 % 16 + 16 * (w / 16384)) * 1024 + w % 1024 = w := by omega
  rwa [e] at this

set_option maxHeartbeats 0 in
theorem c0_0 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 0) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_1 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 1) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_2 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 2) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_3 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 3) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_4 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 4) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_5 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 5) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_6 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 6) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c0_7 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chk0 ((hi + 16 * 7) * 1024 + lo) = true := by
  decide +kernel

theorem c0_all : ∀ w < 2 ^ 17, chk0 w = true := by
  apply cover
  intro b hb
  interval_cases b
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7

set_option maxHeartbeats 0 in
theorem cz_0 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 0) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_1 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 1) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_2 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 2) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_3 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 3) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_4 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 4) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_5 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 5) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_6 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 6) * 1024 + lo) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cz_7 : ∀ hi ∈ List.range 16, ∀ lo ∈ List.range 1024,
    chkZ ((hi + 16 * 7) * 1024 + lo) = true := by
  decide +kernel

theorem cz_all : ∀ w < 2 ^ 17, chkZ w = true := by
  apply cover
  intro b hb
  interval_cases b
  · exact cz_0
  · exact cz_1
  · exact cz_2
  · exact cz_3
  · exact cz_4
  · exact cz_5
  · exact cz_6
  · exact cz_7

set_option maxHeartbeats 0 in
theorem tab_ok : ∀ t ∈ tab, t.2.1 ∈ negs ∧ t.2.2 < 2 ^ 17 ∧ t.2.2.testBit 2 = false ∧
    outputW fstep (t.2.2 ^^^ 12) = outputW fstep (t.1 ^^^ 12) ∧ passW fstep t.2.2 t.2.1 < 2 ^ 8 := by
  decide +kernel

theorem wit : outputW fstep 11632 = 0 ∧ passW fstep 11632 0 < 2 ^ 8 := by
  decide +kernel

theorem negs_sub : ∀ c ∈ negs, c < 2 ^ 17 ∧
    c ∈ ([0, 1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29] : List Nat) := by
  decide

end PEqualNP.Outside.L_lib_537

open PEqualNP.Outside.L_lib_537 in
theorem PEqualNP.Outside.L_lib_537 :
let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
let columnPass := fun (key name : Nat) =>
  ((List.range 4).foldl (fun state j =>
    step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (k + (4 + (j + 1))) % 2 ^ k))
    (rot 3 key ^^^ name)) < 2 ^ 8
let keys := List.range (2 ^ k)
∀ lookup : Nat → Bool, ∃ column : Fin (2 ^ k),
  column.val ∈ ([0, 1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29] : List Nat) ∧
  ¬ ((∃ w ∈ keys, output w = 0 ∧ columnPass w column.val) ↔
    (∃ candidate ∈ keys,
      (if candidate.testBit 2 then output candidate = 0
       else lookup (output (candidate ^^^ 12)) = true) ∧ columnPass candidate column.val)) := by
  show ∀ lookup : Nat → Bool, ∃ column : Fin (2 ^ 17),
    column.val ∈ ([0, 1, 2, 3, 6, 7, 9, 10, 11, 12, 14, 15, 18, 22, 26, 29] : List Nat) ∧
    ¬ ((∃ w ∈ List.range (2 ^ 17), outputW step w = 0 ∧ passW step w column.val < 2 ^ 8) ↔
      (∃ candidate ∈ List.range (2 ^ 17),
        (if candidate.testBit 2 then outputW step candidate = 0
         else lookup (outputW step (candidate ^^^ 12)) = true) ∧
          passW step candidate column.val < 2 ^ 8))
  rw [show step = fstep from funext step_eq]
  intro lookup
  have hZ : ∀ w < 2 ^ 17, outputW fstep w = 0 →
      (∀ c ∈ negs, ¬ passW fstep w c < 2 ^ 8) ∧
        (w.testBit 2 = true → ¬ passW fstep w 0 < 2 ^ 8) := by
    intro w hw h0
    have := cz_all w hw
    simp only [chkZ, h0, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
    refine ⟨this.1, fun hb => ?_⟩
    rcases this.2 with h | h
    · simp [hb] at h
    · exact h
  by_cases h : ∃ cand ∈ List.range (2 ^ 17), cand.testBit 2 = false ∧
      passW fstep cand 0 < 2 ^ 8 ∧ lookup (outputW fstep (cand ^^^ 12)) = true
  · obtain ⟨cand, hc, hb, hp, hl⟩ := h
    have h0 := c0_all cand (List.mem_range.1 hc)
    simp only [chk0, hb, Bool.or_false, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h0
    rcases h0 with h0 | h0
    · exact absurd hp h0
    obtain ⟨t, ht, hte⟩ := List.any_eq_true.1 h0
    have hte' : t.1 = cand := by simpa using hte
    obtain ⟨hneg, hlt, hb', ho, hp'⟩ := tab_ok t ht
    obtain ⟨hcl, hcm⟩ := negs_sub _ hneg
    refine ⟨⟨t.2.1, hcl⟩, hcm, fun hiff => ?_⟩
    obtain ⟨w, hw, ho0, hpw⟩ := hiff.2 ⟨t.2.2, List.mem_range.2 hlt, by
      rw [if_neg (by simp [hb']), ho, hte']
      exact hl, hp'⟩
    exact (hZ w (List.mem_range.1 hw) ho0).1 _ hneg hpw
  · refine ⟨⟨0, by norm_num⟩, by simp, fun hiff => ?_⟩
    obtain ⟨cand, hc, hif, hp⟩ := hiff.1 ⟨11632, List.mem_range.2 (by norm_num), wit.1, wit.2⟩
    split_ifs at hif with hb
    · exact (hZ cand (List.mem_range.1 hc) hif).2 hb hp
    · exact h ⟨cand, hc, by simpa using hb, hp, hif⟩
