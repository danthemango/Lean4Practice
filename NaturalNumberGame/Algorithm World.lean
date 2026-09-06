abbrev succ := Nat.succ
abbrev ℕ := Nat
abbrev MyNat := Nat
abbrev MyNat.succ := Nat.succ

theorem zero_ne_succ (a : ℕ) : 0 ≠ MyNat.succ a := by
  sorry

theorem pred_succ (n : ℕ) : (MyNat.succ n).pred = n := by
  sorry

example (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry
