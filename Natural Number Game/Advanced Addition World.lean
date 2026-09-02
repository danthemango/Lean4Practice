theorem zero_add (x : Nat) : x + 0 = x := by
  omega

theorem add_right_cancel (a b n : Nat) : a + n = b + n → a = b := by
  omega

theorem add_left_cancel (a b n : Nat) : n + a = n + b → a = b := by
  omega

theorem add_left_eq_self (x y : Nat) : x + y = y → x = 0 := by
  rw [← zero_add y]
  exact add_right_cancel x 0 y

theorem add_right_eq_self (x y : Nat) : x + y = x → y = 0 := by
  rw [add_comm x y]
  exact add_left_eq_self y x
