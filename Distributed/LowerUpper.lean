import Distributed.RectPairing

variable (w h n : ℕ)

abbrev InLower := h * w ≤ n ∧
  n - rectrt_h w h n * rectrt_w w h n < rectrt_w w h n

abbrev InUpper := h * w ≤ n ∧
  ¬ n - rectrt_h w h n * rectrt_w w h n < rectrt_w w h n

@[simp] lemma InLower.unpair_def (hn : InLower w h n) : unpair w h n = (n - rectrt_h w h n * rectrt_w w h n, rectrt_h w h n) := by
  simp_all [unpair]

@[simp] lemma InUpper.unpair_def (hn : InUpper w h n) : unpair w h n = (rectrt_w w h n, n - rectrt_h w h n * rectrt_w w h n - rectrt_w w h n) := by
  simp_all [unpair]

lemma InLower.unpair_y_ge (hn : InLower w h n) : h ≤ (unpair w h n).2 := by
  simp [InLower.unpair_def _ _ _ hn]
  obtain ⟨hn1, hn2⟩ := hn
  by_cases hh : h = 0
  · simp_all
  · by_cases hw : w = 0
    · simp [hw, rectrt_h]
    · apply rectrt_h_ge_of_mul
      exact hn1

lemma outside_rect (hn : h * w ≤ n) : InLower w h n ∨ InUpper w h n := by
  tauto




def main' : IO Unit := do
  let w := 3
  let h := 2
  IO.println f!"Output of `pair w h x y` where x→ y↓"
  for l in ((pair w h).uncurry <$> .) <$> (range2 6 6) do
    for n in l do
      let t := Bool.toNat $ decide $ InUpper w h n
      let b := Bool.toNat $ decide $ InLower w h n
      let s := toString (t + 2 * b)
      -- let s := toString n
      let pad := String.replicate (4 - s.length) ' '
      IO.print f!"{pad}{s}"
    IO.println ""

  IO.println ""

  let mut y := 0
  for l in ((unpair w h ∘ (pair w h).uncurry) <$> .) <$> (range2 10 10) do
    let mut x := 0
    for p in l do
      let s := toString p
      -- if x < w ∧ y < h then IO.print "*   "
      -- else IO.print f!"{p.1}   "
      let pad := String.replicate (8 - s.length) ' '
      if x < w ∧ y < h then IO.print "  (*, *)"
      else IO.print f!"{pad}{s}"
      x := x + 1
    y := y + 1
    IO.println ""

#eval main'
