import Lean4PracticeWithMathlib.Basic

theorem or_inl {P Q} (p : P) : P ∨ Q := by
  left
  assumption

theorem or_inr {P Q} (p : P) : Q ∨ P := by
  right
  assumption

-- the kraken
example (O S : Prop)(s : S) : S ∨ O := by
  have h4 : S ∨ O := or_inl s
  exact h4

example (O S : Prop)(s : S) : K ∨ S := by
  sorry
