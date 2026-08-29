import Lean4PracticeWithMathlib.Basic

example (P Q: Prop)(h'₁: P)(h : P → Q) : Q := by
    apply h h'₁

example (P: Prop) : P → P := by
  intro h
  assumption

example (P Q: Prop) : P ∧ Q → Q ∧ P := by
    intro h
    constructor
    cases h
    assumption
    cases h
    assumption

example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  intro h3
  have a : A := h1 h3
  have s : S := h2 a
  assumption

example (P Q T U: Prop) (h1 : P → Q) (h3 : Q → T) (h5 : T → U) : P → U := by
  intro h
  apply h5 (h3 (h1 h))

example (P Q R: Prop) (h : P ∧ Q → R) : P → Q → R := by
  intro p
  intro q
  have pandq : P ∧ Q := and_intro p q
  exact h pandq

-- try it without cases, exact, or have
example (P Q R: Prop) (h : P ∧ Q → R) : P → Q → R := by
  sorry
