import Distributed.Rectrt

/-- Pair function with linear rectangle.

For example, given `w = 3, h = 4`, it produces:

   0   1   2  15  24  35  48  63  80  99 120 143 168 195 224
   3   4   5  16  25  36  49  64  81 100 121 144 169 196 225
   6   7   8  17  26  37  50  65  82 101 122 145 170 197 226
   9  10  11  18  27  38  51  66  83 102 123 146 171 198 227
  12  13  14  19  28  39  52  67  84 103 124 147 172 199 228
  20  21  22  23  29  40  53  68  85 104 125 148 173 200 229
  30  31  32  33  34  41  54  69  86 105 126 149 174 201 230
  42  43  44  45  46  47  55  70  87 106 127 150 175 202 231
  56  57  58  59  60  61  62  71  88 107 128 151 176 203 232
  72  73  74  75  76  77  78  79  89 108 129 152 177 204 233
  90  91  92  93  94  95  96  97  98 109 130 153 178 205 234
 110 111 112 113 114 115 116 117 118 119 131 154 179 206 235
 132 133 134 135 136 137 138 139 140 141 142 155 180 207 236
 156 157 158 159 160 161 162 163 164 165 166 167 181 208 237
 182 183 184 185 186 187 188 189 190 191 192 193 194 209 238

Which contains a 3 wide 4 tall rectangle at the origin with linearly increasing values. After the rectangle, the algorithm continues as follows:

   *   *   *  15 |
   *   *   *  16 |
   *   *   *  17 |
   *   *   *  18 |
  12  13  14  19 ↓
  ---------→
-/
def pair (w h : ℕ) (x y : ℕ) : ℕ := if y < h ∧ x < w then
    y * w + x
  else if y - h < x + 1 - w then
    x * (x - w + h + 1) + y
  else
    y * (y - h + w) + x

#eval pair 3 4 5 0


/-- Inverse of `pair` -/
def unpair (w h n : ℕ) : ℕ × ℕ :=
  if n < h * w then
    (n % w, n / w)
  else

  let root_h := rectrt_h w h n
  let root_w := rectrt_w w h n

  let i := n - root_h * root_w -- how much n is over the previous rectangle
  if i < root_w
  then
    -- Lower triangle
    (i, root_h)
  else
    -- Upper triangle
    (root_w, i - root_w)

-- Old bad implementation
/-
  if w > h then
    let d := w - h
    let s := rectrt d n -- short side
    let l := s + d -- long side
    let i := n - s * l -- how much n is over the previous rectangle
    if i < l
    then
      -- Lower triangle
      (i, s)
    else
      -- Upper triangle
      (l, i - l)
  else
    let d := h - w
    let s := rectrt d n
    let l := s + d
    let i := n - s * l
    if i < s
    then
      -- Lower triangle
      (i, l)
    else
      -- Upper triangle
      (s, i - s)
-/

theorem pair_unpair.in_rect {w h n : ℕ} (hn : n < h * w) : pair w h (n % w) (n / w) = n := by
  dsimp [pair]
  have h1 : n / w < h
  · by_cases w = 0
    · simp_all
    · rw [Nat.div_lt_iff_lt_mul]
      · assumption
      · grind
  have h2 : n % w < w
  · by_cases w = 0
    · simp_all
    · apply Nat.mod_lt
      grind
  simp [h1, h2]
  exact Nat.div_add_mod' _ _

theorem pair_unpair.in_rect' {w h n : ℕ} (hn : n < h * w) : pair w h (unpair w h n).1 (unpair w h n).2 = n := by
  dsimp only [unpair]
  simp [hn]
  exact in_rect hn

theorem pair_unpair {w h n : ℕ} : pair w h (unpair w h n).1 (unpair w h n).2 = n := by
  nth_rw 1 [unpair]
  split_ifs with hn
  · simp [unpair, hn]
    exact pair_unpair.in_rect hn
  · sorry

theorem unpair_pair (w h : ℕ) : unpair w h ∘ (pair w h).uncurry = id := by
  unfold unpair pair
  sorry

#eval let w := 10; let h := 5; unpair w h (pair w h 6 4)

-- Check that unpair is inverse of pair
#eval let w := 2; let h := 3; List.all (((fun p => p == (unpair w h ∘ (pair w h).uncurry) p) <$> .) <$> (range2 10 20)) (List.all . id)
#eval let w := 3; let h := 2; List.all (((fun p => p == (unpair w h ∘ (pair w h).uncurry) p) <$> .) <$> (range2 10 20)) (List.all . id)

def main : IO Unit := do
  let w := 3
  let h := 2
  IO.println f!"Output of `unpair w h ∘ pair w h` where x→ y↓ (should be id)"
  for l in ((unpair w h ∘ (pair w h).uncurry) <$> .) <$> (range2 10 20) do
    for p in l do
      let s := toString p
      let pad := String.replicate (8 - s.length) ' '
      IO.print f!"{s}{pad}"
    IO.println ""

#eval main
