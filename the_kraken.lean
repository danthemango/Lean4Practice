import Lean4PracticeWithMathlib.Basic

theorem or_inl {P Q} (p : P) : P ∨ Q := by
  left
  assumption

theorem or_inr {P Q} (p : P) : Q ∨ P := by
  right
  assumption

example (O S : Prop)(s : S) : S ∨ O := by
  have h4 : S ∨ O := or_inl s
  exact h4

-- simpler
example (O S : Prop)(s : S) : S ∨ O := by
  exact or_inl s

example (K S : Prop)(s : S) : K ∨ S := by
  exact or_inr s

theorem or_elim {P Q R} (h : P ∨ Q) (_ : P → R) (_ : Q → R)
  : Q ∨ P
  := by
  cases h
  right
  assumption
  left
  assumption

example (B C I : Prop)(h1 : C → B)(h2 : I → B)(h3 : C ∨ I) : B := by
  -- exact or_elim h3 h1 h2
  sorry
