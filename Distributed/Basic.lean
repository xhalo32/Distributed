import Mathlib.Tactic

def range2 (n m : ℕ) := (fun y => (., y) <$> List.range n) <$> List.range m
