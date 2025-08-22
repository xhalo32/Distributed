import Mathlib.Tactic

variable (d : ℕ) (f : ℤ → ℤ)

abbrev Lipschitz := ∀ n, |f n - f (n + 1)| ≤ d

theorem Lipschitz.neg (h : Lipschitz d f) : Lipschitz d (-f) := by
  dsimp [Lipschitz] at *
  refine forall_imp (fun n => ?_) h
  rw [abs_sub_comm]
  grind

theorem Lipschitz.const (h : Lipschitz 0 f) : ∀ n m, f n = f m := by
  intro n m
  simp [Lipschitz] at h
  wlog h_ord : n ≤ m
  · symm
    apply this f m n
    · grind
    · grind

  let d := m - n
  have : m = n + d
  · grind
  clear_value d
  simp only [this] at *
  lift d to ℕ using show 0 ≤ d by grind
  clear h_ord

  induction' d with d ih generalizing n
  · simp
  · grind

theorem discrete_bolzano {d : ℕ} (hf : Lipschitz d f) (h_pos : ∃ n, f n > 0) (h_neg : ∃ n, f n < 0) : ∃ n, |f n| ≤ d := by
  have d_pos : 0 < d
  · by_contra!
    simp_all
    have := hf.const
    grind

  obtain ⟨n_pos, h_pos⟩ := h_pos
  obtain ⟨n_neg, h_neg⟩ := h_neg

  wlog n_ord : n_pos < n_neg
  · simp_rw [← fun n => abs_neg (f n)]
    apply this _ hf.neg d_pos
    · simp
      exact h_neg
    · simp
      exact h_pos
    grind

  by_contra! h

  have hfn_pos : f n_pos ≥ d
  · specialize h n_pos
    rw [abs_of_nonneg h_pos.le] at h
    linarith

  have hfn_neg : f n_neg ≤ -d
  · specialize h n_neg
    rw [abs_of_nonpos h_neg.le] at h
    linarith

  let nd := n_neg - n_pos
  -- Next we set n_neg = n_pos + nd
  have : n_neg = n_pos + nd
  · grind
  clear_value nd
  simp only [this] at *
  lift nd to ℕ using show 0 ≤ nd by grind
  clear n_ord n_neg -- remove unnecessary objects

  induction' nd with nd ih generalizing n_pos
  · grind
  · simp_all
    by_cases hf_pos_nd : f (n_pos + nd) < 0
    · specialize ih n_pos
      simp_all
      have := h (n_pos + nd)
      rw [lt_abs] at this
      grind
    ·
      simp at hf_pos_nd
      by_cases f (n_pos + nd) = 0
      · specialize h (n_pos + nd)
        rw [lt_abs] at h
        grind
      ·
        have := hf (n_pos + nd)
        simp [abs_le] at this
        apply lt_of_le_of_ne at hf_pos_nd
        specialize hf_pos_nd (by grind)
        apply And.right at this
        rw [Int.add_assoc] at this
        grw [hfn_neg] at this
        simp at this
        linarith
