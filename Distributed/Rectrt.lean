import Distributed.Basic

/-- Rectangle root. Gives the side-length of the shorter side of the largest rectangle with area `n`. `d` is the side-length difference.

## Examples
- `rectrt 1 12 = 3`, because `3 * (3 + 1) ≤ 12`
- `rectrt 1 19 = 3`, because `3 * (3 + 1) ≤ 19`
- `rectrt 1 20 = 4`, because `4 * (4 + 1) ≤ 20`
- `rectrt 2 23 = 3`, because `3 * (3 + 2) = 15 ≤ 23`
- `rectrt 2 24 = 3`, because `4 * (4 + 2) = 24 ≤ 24`
- `rectrt 3 9 = 1`, because `1 * (1 + 3) = 3 ≤ 9`
- `rectrt 3 10 = 2`, because `2 * (2 + 3) = 10 ≤ 10`
- `rectrt 3 18 = 3`, because `3 * (3 + 3) = 18 ≤ 18`
-/
def rectrt (d : ℕ) (n : ℕ) : ℕ :=
  if d = 0 then n.sqrt else -- Really just provides the case `rectrt 0 1 = 1`
  if n ≤ d then 0 else
  iter n (n / 2)
where
  @[semireducible] iter (n guess : Nat) : Nat :=
    let next := (guess * guess + n) / (2 * guess + d)
    if _h : next < guess then
      iter n next
    else
      guess
  termination_by guess

/-- Like rectrt, but instead of the shorter side, gives the vertical side. -/
def rectrt_h (w h : ℕ) (n : ℕ) :=
  if w > h then
    let d := w - h
    rectrt d n
  else
    let d := h - w
    rectrt d n + d

def rectrt_w (w h : ℕ) (n : ℕ) :=
  if w > h then
    let d := w - h
    rectrt d n + d
  else
    let d := h - w
    rectrt d n

variable (w h n : ℕ)

abbrev IsRectrt (w h n rw rh: ℕ) := rh * rw ≤ n ∧ n < (rh + 1) * (rw + 1) ∧ (rh : ℤ) - rw = h - w

-- Creates a list n, [(rw, rh)] where rw, rh are the valid rw and rh searched using IsRectrt
#eval let w := 1; let h := 2; (List.range 21).map fun n => (n, List.filter ((IsRectrt w h n).uncurry) (range2 10 10).flatten)
#eval let w := 1; let h := 2; (List.range 21).map fun n => (n, [(rectrt_w w h n, rectrt_h w h n)])

-- Check for equality
#eval let w := 1; let h := 2; let n := 21; ((List.range n).map fun n => (n, List.filter ((IsRectrt w h n).uncurry) (range2 10 10).flatten)) == (List.range n).map fun n => (n, [(rectrt_w w h n, rectrt_h w h n)])

-- I'm not going to prove this as Mathlib doesn't prove that IsSqrt is unique
-- theorem IsRectrt.unique : ∀ rw rh rw' rh', IsRectrt w h n rw rh ∧ IsRectrt w h n rw' rh' → rw = rw' ∧ rh = rh' := by
--   intros
--   expose_names
--   unfold IsRectrt at h_1
--   rcases h_1 with ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
--   sorry

@[grind] lemma rectrt_h_eq_w : rectrt_h w h n = rectrt_w h w n := by
  simp [rectrt_h, rectrt_w]
  grind

@[grind] lemma rectrt.iter_le (hh : h < w) (guess : ℕ) : iter (w - h) n guess * (iter (w - h) n guess + (w - h)) ≤ n := by
  unfold iter
  let next := (guess * guess + n) / (2 * guess + (w - h))
  if h_next : next < guess then
    simpa only [next, dif_pos h_next] using iter_le hh next
  else
    extract_lets
    split_ifs
    unfold next at h_next
    simp at h_next
    rw [Nat.le_div_iff_mul_le] at h_next
    · grind
    · grind


private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

#eval let w := 6; let h := 2; let n := 40; let guess := 4; let next := (guess * guess + n) / (2 * guess + (w - h))
  -- rectrt n, next, something > n
  (rectrt (w - h) n, next, (next + 1) * (next + 1 + (w - h)))


-- @[grind] lemma rectrt.lt_iter_succ (hh : h < w) (guess : ℕ) (hn : n < (guess + 1) * (guess + (w - h) + 1)) : n < (iter (w - h) n guess + 1) * (iter (w - h) n guess + (w - h) + 1) := by
--   unfold iter
--   let next := (guess * guess + n) / (2 * guess + (w - h))
--   dsimp
--   split_ifs with h_next
--   · suffices n < (next + 1) * (next + (w - h) + 1) by
--       simpa only [dif_pos h_next] using lt_iter_succ hh next this

--     refine Nat.lt_of_mul_lt_mul_left ?_ (a := (2 * guess + (w - h))^2)
--     rw [pow_two]
--     have : (2 * guess + (w - h)) * (next + 1) = ?_
--     · rw [← Nat.add_div_right]

--   · exact hn

    -- This is a decent try
    -- suffices n + (next + 1 + (w - h)) * (w - h) < (next + 1 + (w - h)) ^ 2 by
    --   rw [pow_two] at this
    --   grind

    -- refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    -- apply Nat.lt_of_le_of_lt AM_GM

    -- rw [show (4 : ℕ) = 2 * 2 from rfl, pow_two]
    -- rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    -- apply Nat.mul_self_lt_mul_self

    -- dsimp [next]
    -- -- rw [← Nat.add_div_right _ ?_]
    -- rw [add_assoc _ 1]
    -- rw [← Nat.add_mul_div_right _ (1 + (w - h)) ?_]
    -- generalize w - h = d at *
    -- sorry

/-- Arithmetic helper: if `t ≤ g` and `d : ℕ`, then
`t * (2*g + d) - g*g ≤ t * (t + d)`.
This is the key inequality `t(2g+d) - g² ≤ t(t+d)` which is
an immediate consequence of writing `g = t + k` and expanding,
so the left becomes `t(t+d) - k² ≤ t(t+d)`.
-/
lemma sub_bound (t g d : ℕ) (htg : t ≤ g) :
  t * (2 * g + d) - g * g ≤ t * (t + d) := by
  -- Write `g = t + k` with `k ≥ 0` and expand.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le htg
  subst g
  -- Show: `t*(2*(t+k) + d) - (t+k)^2 ≤ t*(t+d)`
  -- Move the `-(t+k)^2` to RHS using `Nat.sub_le_iff_le_add`.
  refine (Nat.sub_le_iff_le_add).mpr ?_
  -- It suffices to prove `t*(2*(t+k)+d) ≤ (t+k)^2 + t*(t+d)`.
  -- Expand both sides and compare termwise.
  calc
    t * (2 * (t + k) + d)
        = t * (2 * t) + t * (2 * k) + t * d := by
              grind
    _ ≤ (t * t + t * t) + (t * k + t * k) + t * d := by
              grind
    _ ≤ (t * t + t * k + k * t + k * k) + (t * t + t * d) := by
              -- `t*k + t*k ≤ t*k + k*t + k*k` and `t*t ≤ t*t`
              have : t * k + t * k ≤ t * k + k * t + k * k := by
                nlinarith
              -- rearrange and bound componentwise
              nlinarith -- if `nlinarith` unavailable, proceed with monotone additions
    _ = (t + k) * (t + k) + t * (t + d) := by grind
  nlinarith

@[grind] lemma rectrt.lt_iter_succ
  (hh : h < w)
  (guess : ℕ)
  (hn : n < (guess + 1) * (guess + (w - h) + 1)) : n < (iter (w - h) n guess + 1) * (iter (w - h) n guess + (w - h) + 1) := by
  set d := w - h with hd
  have hd_pos : 0 < d := Nat.sub_pos_of_lt hh
  unfold iter
  extract_lets next
  split_ifs with h_next
  · have hb_pos : 0 < 2 * guess + d := by grind
    -- Division decomposition: `g^2 + n = next * b + r` with `r < b`
    have hmodlt : (guess * guess + n) % (2 * guess + d) < (2 * guess + d) :=
      Nat.mod_lt _ hb_pos
    have hdiv : guess * guess + n = next * (2 * guess + d) + (guess * guess + n) % (2 * guess + d) := by exact Eq.symm (Nat.div_add_mod' _ _)
    -- hence `g^2 + n < (next + 1) * (2g + d)`
    have hmul : guess * guess + n < (next + 1) * (2 * guess + d) := by
      calc
        guess * guess + n = next * (2 * guess + d) + (guess * guess + n) % (2 * guess + d) := hdiv
        _ < next * (2 * guess + d) + (2 * guess + d) := Nat.add_lt_add_left hmodlt _
        _ = (next + 1) * (2 * guess + d) := by grind
    -- subtract `g^2` on both sides (allowed since `g^2 ≤ g^2 + n`)
    have hsub : n < (next + 1) * (2 * guess + d) - guess * guess := by
      have : guess * guess ≤ guess * guess + n := Nat.le_add_right _ _
      exact Nat.lt_sub_iff_add_lt'.mpr hmul
    -- bound the RHS by `(next + 1) * (next + 1 + d)` using `next + 1 ≤ guess`.
    have ht_le_g : next + 1 ≤ guess := Nat.succ_le_of_lt h_next
    have hbound : (next + 1) * (2 * guess + d) - guess * guess ≤ (next + 1) * (next + 1 + d) := by
      simpa [Nat.add_comm] using sub_bound (next + 1) guess d ht_le_g
    suffices n < (next + 1) * (next + 1 + d) by
      simpa [dif_pos h_next] using rectrt.lt_iter_succ hh next (by grind)
    have hfinal : n < (next + 1) * (next + 1 + d) := lt_of_lt_of_le hsub hbound
    exact hfinal
  · grind

@[grind] theorem rectrt_isRectrt : IsRectrt w h n (rectrt_w w h n) (rectrt_h w h n) := by
  dsimp only [IsRectrt]
  rw [← rectrt_h_eq_w]
  refine ⟨?_, ?_, ?_⟩
  · by_cases wh : w = h
    · simp [wh, rectrt_h, rectrt]
      exact Nat.sqrt_le n
    · have : h < w ∨ w < h
      · grind

      rcases this with wh2 | wh2
      · have : ¬ w < h
        · grind
        simp [rectrt_h, wh2, this]
        simp [rectrt, show ¬ w - h = 0 by grind]
        grind
      ·
        have : ¬ h < w
        · grind
        simp [rectrt_h, wh2, this]
        simp [rectrt, show ¬ h - w = 0 by grind]
        split_ifs with hn
        · apply Nat.zero_le
        grind
  · by_cases wh : w = h
    · simp [wh, rectrt_h, rectrt]
      exact Nat.lt_succ_sqrt n
    · have : h < w ∨ w < h
      · grind

      rcases this with wh2 | wh2
      · have : ¬ w < h
        · grind
        simp [rectrt_h, wh2, this]
        simp [rectrt, show ¬ w - h = 0 by grind]
        split_ifs
        · grind
        · have := rectrt.lt_iter_succ w h n wh2 (n/2) ?_
          · grind
          · have : 0 < n
            · linarith
            simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
            rw [Nat.lt_add_one_iff]
            rw [add_comm, add_comm _ (n/2), ← add_assoc, ← add_assoc, ← add_assoc, ← mul_two, add_assoc, add_assoc, add_comm]
            refine le_trans (Nat.le_of_eq (Nat.div_add_mod' n 2).symm) ?_
            rw [Nat.add_comm, Nat.add_le_add_iff_right]
            suffices n % 2 ≤ w - h by
              ring_nf
              exact Nat.le_add_left_of_le this
            grind
      · -- TODO get rid of repetition
        have : ¬ h < w
        · grind
        simp [rectrt_h, wh2, this]
        simp [rectrt, show ¬ h - w = 0 by grind]
        split_ifs
        · grind
        · have := rectrt.lt_iter_succ h w n wh2 (n/2) ?_
          · grind
          · have : 0 < n
            · linarith
            simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
            rw [Nat.lt_add_one_iff]
            rw [add_comm, add_comm _ (n/2), ← add_assoc, ← add_assoc, ← add_assoc, ← mul_two, add_assoc, add_assoc, add_comm]
            refine le_trans (Nat.le_of_eq (Nat.div_add_mod' n 2).symm) ?_
            rw [Nat.add_comm, Nat.add_le_add_iff_right]
            suffices n % 2 ≤ h - w by
              ring_nf
              exact Nat.le_add_left_of_le this
            grind
  · simp [rectrt_h]
    grind

lemma rectrt.iter_pos {n d g : ℕ} (hd : d ≠ 0) (hn : d < n) (hg : 0 < g) :
    0 < iter d n g := by
  unfold iter
  set m : ℕ := (g * g + n) / (2 * g + d) with hm
  by_cases hlt : m < g
  · simp [dif_pos hlt]
    -- show `m > 0` so we can call recursively on `m`.
    have dpos : 0 < d := Nat.pos_of_ne_zero hd
    -- `d ≤ 2*g + d`, hence `0 < 2*g + d`.
    have d_le : d ≤ 2 * g + d := by grind
    have denom_pos : 0 < 2 * g + d := lt_of_lt_of_le dpos d_le
    -- show numerator ≥ denominator
    have hadd : d + 1 ≤ n := Nat.succ_le_of_lt hn

    have diff_eq : g * g + n - (2 * g + d) = (g - 1) * (g - 1) + (n - (d + 1))
    · by_cases g = 1
      · simp_all
        grind
      · have : g > 1
        · grind
        calc
        g * g + n - (2 * g + d)
          = (g * g + n - 2 * g) - d := by grind
        _ = (g * g - 2 * g) + (n - d) := by rw [Nat.sub_add_comm]; grind; exact Nat.mul_le_mul_right g this
        _ = (g - 1) * (g - 1) - 1 + (n - d) := by rw [tsub_mul, mul_tsub]; simp [Nat.sub_sub]; grind
        _ = (g - 1) * (g - 1) + (n - (d + 1)) := by rw [← Nat.sub_add_comm]; grind; simp [show 1 ≤ g - 1 by grind]

    have left_nonneg : 0 ≤ (g - 1) * (g - 1) := by apply Nat.zero_le
    have right_nonneg : 0 ≤ n - (d + 1) := (Nat.le_sub_iff_add_le' hn).mpr hn
    have diff_nonneg : 0 ≤ g * g + n - (2 * g + d) := by
      grind
    have denom_le_num : 2 * g + d ≤ g * g + n := by
      nlinarith
    have m_pos : 0 < m := by
      simpa [hm] using Nat.div_pos denom_le_num denom_pos
    exact rectrt.iter_pos hd hn m_pos
  · simp [dif_neg hlt]
    exact hg


-- lemma lt_succ_rectrt (d n : ℕ) : n < (rectrt d n).succ * (rectrt d n + d).succ := (rectrt.spec d n).right

/- Given n such that rectrt 1 n = 3, then n ≤ 4 * 3 + 3 + 4 = 19 -/
-- #eval rectrt 1 11 -- 2
-- #eval rectrt 1 12 -- 3
-- #eval rectrt 1 19 -- 3
-- #eval rectrt 1 20 -- 4

-- lemma rectrt_le_add (d n : ℕ) : let s := rectrt d n
--     n ≤ s * (s + d) + (s + d) + s := by
--   extract_lets s
--   rw [← Nat.succ_mul]
--   apply Nat.le_of_lt_succ
--   exact (lt_succ_rectrt d n)




lemma lt_succ_rectrt : n < (rectrt_h w h n).succ * (rectrt_w w h n).succ := (rectrt_isRectrt w h n).right.left

lemma rectrt_le_add : n ≤ rectrt_h w h n * rectrt_w w h n + rectrt_w w h n + rectrt_h w h n := by
  rw [← Nat.succ_mul]
  apply Nat.le_of_lt_succ
  exact (lt_succ_rectrt w h n)

lemma rectrt_diff : (rectrt_w w h n : ℤ) - rectrt_h w h n = w - h := by
  unfold rectrt_h rectrt_w
  grind

@[grind] lemma rectrt_h_zero : h ≤ rectrt_h 0 h n := by
  simp [rectrt_h]

@[grind] lemma rectrt_w_zero : w ≤ rectrt_w w 0 n := by
  rw [← rectrt_h_eq_w]
  exact rectrt_h_zero w n

lemma rectrt_pos_iff {d : ℕ} : d < n ↔ 0 < rectrt d n := by
  simp [rectrt]
  split_ifs with hd hn
  · simp_all
    exact Iff.symm Nat.sqrt_pos
  · grind
  · simp_all
    have : 0 < n / 2
    · grind
    apply rectrt.iter_pos hd hn this

@[grind] lemma rectrt_w_zero_pos : h < n ↔ 0 < rectrt_w 0 h n := by
  simp [rectrt_w]
  exact rectrt_pos_iff n

lemma rectrt_h_zero_pos : w < n ↔ 0 < rectrt_h w 0 n := by
  grind

@[grind] lemma rectrt_h_pos (hn : w < h + n) : 0 < rectrt_h w h n := by
  by_cases hh : h = 0
  · grind
  · by_cases hw : w = 0
    · grind
    · simp [← Nat.pos_iff_ne_zero] at *
      have ⟨spec1, spec2, spec3⟩ := rectrt_isRectrt w h n
      grind

lemma rectrt_w_pos (hn : h < w + n) : 0 < rectrt_w w h n := by
  rw [← rectrt_h_eq_w]
  grind

-- Too hard for now
-- lemma rectrt_h_pos_iff : w < h + n ↔ 0 < rectrt_h w h n := by

lemma rectrt_h_div (hn : w < h + n) : rectrt_w w h n ≤ n / rectrt_h w h n := by
  rw [Nat.le_div_iff_mul_le]
  · grind
  · grind

lemma rectrt_h_mul_rectrt_w_lt_succ : rectrt_h w h n * rectrt_w w h n < n.succ := by
  grind

lemma rectrt_w_div (hn : h < w + n) : rectrt_h w h n ≤ n / rectrt_w w h n := by
  rw [rectrt_h_eq_w]
  nth_rw 2 [← rectrt_h_eq_w]
  exact rectrt_h_div h w n hn

#eval let w := 2; let h := 3; (List.range 20).map fun n => (decide $ rectrt_h w h n ≤ h, decide $ rectrt_w w h n ≤ w)

lemma rectrt_le_iff : rectrt_h w h n ≤ h ↔ rectrt_w w h n ≤ w := by
  have ⟨spec1, spec2, spec3⟩ := rectrt_isRectrt w h n
  grind

lemma rectrt_ge_iff : h ≤ rectrt_h w h n ↔ w ≤ rectrt_w w h n := by
  have ⟨spec1, spec2, spec3⟩ := rectrt_isRectrt w h n
  grind

/-

w=3 h=2
   0   1   2   9  16  25
   3   4   5  10  17  26
   6   7   8  11  18  27
  12  13  14  15  19  28
  20  21  22  23  24  29
  30  31  32  33  34  35

When s = 2, w * h = 6 ≤ n

-/

lemma rectrt_h_ge_of_mul (hn : h * w ≤ n) : h ≤ rectrt_h w h n := by
  by_cases hh : h = 0
  · simp_all
  · by_cases hw : w = 0
    · simp [hw, rectrt_h]
    ·
      simp [← Nat.pos_iff_ne_zero] at *
      have ⟨spec1, spec2, spec3⟩ := rectrt_isRectrt w h n
      by_contra!
      have hh2 : rectrt_h w h n ≤ h - 1
      · grind
      have hw2 : rectrt_w w h n ≤ w - 1
      · grind
      have hhw : rectrt_h w h n * rectrt_w w h n ≤ (h - 1) * (w - 1)
      · exact Nat.mul_le_mul hh2 hw2

      simp [tsub_mul, mul_tsub] at hhw
      have : w ≤ h * w ∧ h ≤ h * w
      · constructor
        · exact Nat.le_mul_of_pos_left w hh
        · exact Nat.le_mul_of_pos_right h hw
      have : h - 1 ≤ (h - 1) * w
      · by_cases h - 1 = 0
        · grind
        · apply Nat.le_mul_of_pos_right _ hw
      rw [le_tsub_iff_left, le_tsub_iff_left (Nat.le_mul_of_pos_left w hh)] at hhw
      · grind
      · rw [tsub_mul] at this
        simp_all

-- Sorry-free until this point



-- Too hard
lemma rectrt_h_mul : rectrt_h w h (h * w) = h := by
  by_cases hh : h = 0
  · simp_all [rectrt_h]
    by_cases hw : w = 0
    · simp_all [rectrt]
    · simp [← Nat.pos_iff_ne_zero] at hw
      simp [hw, rectrt]
  · by_cases hw : w = 0
    · simp [hw, rectrt_h, rectrt]
    · simp [← Nat.pos_iff_ne_zero] at *
      have ⟨spec1, spec2, spec3⟩ := rectrt_isRectrt w h (h * w)
      sorry

lemma rectrt_h_mono : Monotone (rectrt_h w h) := sorry
