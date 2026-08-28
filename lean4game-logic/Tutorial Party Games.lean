import Lean4PracticeWithMathlib.Basic

theorem iff_intro {P Q} (mp : P → Q) (mpr : Q → P) : P ↔ Q := by
  constructor
  assumption
  assumption

theorem iff_mp {P Q} (h : P ↔ Q) (a : P) : Q := by
  exact h.mp a

theorem iff_mpr {P Q} (h : P ↔ Q) (a : Q) : P := by
  exact h.mpr a

example (P Q R : Prop) (h1 : P ↔ R)(h2 : P → Q) : R → Q := by
  have h3 : R → P := h1.mpr
  exact λ hr => h2 (h3 hr)

-- skipped problem

#check and_assoc
example {P Q R} : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  exact and_assoc

#check or_assoc
example {P Q R} : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  exact or_assoc

example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rw [or_assoc]
  rw [and_assoc]
  exact h

-- boss
example (P Q R : Prop): (P ∧ Q ↔ R ∧ Q) ↔ Q → (P ↔ R) := by
  have h1 : P ∧ Q → P := λ pandq => pandq.left
  have h2 : R ∧ Q → R := λ randq => randq.left
  have h3 : (P ∧ Q → R ∧ Q) → Q → P → R := λ andimp => λ hq => λ hp => (andimp (and_intro hp hq)).left
  have h4 : (R ∧ Q → P ∧ Q) → Q → R → P := λ andimp => λ hq => λ hr => (andimp (and_intro hr hq)).left
  -- have h5 : (P ∧ Q → R ∧ Q) ∧ (R ∧ Q → P ∧ Q) → (P ∧ Q ↔ R ∧ Q) := λ hand => iff_intro hand.left hand.right
  have h6 : (P → R) ∧ (R → P) → (P ↔ R) := λ hand => iff_intro hand.left hand.right
  have h7 : (P ∧ Q ↔ R ∧ Q) → Q → P ↔ R := by sorry
  have h10 : Q → (P ↔ R) → (P ∧ Q ↔ R ∧ Q) := by sorry
  have h8 : (P ∧ Q ↔ R ∧ Q) ↔ Q → R → P := by sorry
  -- have h9 : (P ∧ Q ↔ R ∧ Q) → Q → (P ↔ R) := λ iffpqr => iffpqr
  sorry
