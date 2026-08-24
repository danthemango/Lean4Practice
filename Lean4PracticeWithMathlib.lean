import Lean4PracticeWithMathlib.Basic

-- ImpIntro game

example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
    constructor
    exact h.left.right
    constructor
    exact h.right.right.left.left
    exact h.left.left

-- everything implies itself
example (C: Prop) : C → C := by
    have h : C → C := fun c : C => c
    exact h

example (C: Prop) : C → C := by exact λ(c : C) => c

-- exact may fill in the type for us
example (C: Prop) : C → C := by exact λc => c

example (I S: Prop) : I ∧ S → S ∧ I := by
    intro h
    constructor
    exact h.right
    exact h.left

-- proved by creating a function that takes in a value of type I ∧ S
-- then gives S ∧ I
example (I S: Prop) : I ∧ S → S ∧ I := by
    exact λ h : I ∧ S => ⟨ h.right, h.left ⟩

-- and again where type is just assumed
example (I S: Prop) : I ∧ S → S ∧ I := by
    exact λ h => ⟨ h.right, h.left ⟩

example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
    intro h3
    have h4 : A := h1 h3
    exact h2 h4

-- construct the function, and nest h1 and h2 as function executions
example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
    have h3 : C → S := λ h : C => h2 (h1 h)
    exact h3

-- and again a bit simpler
example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
    exact λ h => h2 (h1 h)

example (P Q T U: Prop) (p : P) (h1 : P → Q) (h3 : Q → T) (h5 : T → U) : U := by
    have h6 : P → U := λ h : P => h5 (h3 (h1 h))
    exact h6 p

-- and again with infix operator
-- example (P Q T U: Prop) (p : P) (h1 : P → Q) (h3 : Q → T) (h5 : T → U) : U := by
--     exact (h₁ ≫ h₃ ≫ h₅) p

example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
    exact λ hl1 => λ hl2 => h (and_intro hl1 hl2)

example (C D S: Prop) (h : C → D → S) : C ∧ D → S := by
    exact λ hl1 => (h hl1.left) hl1.right

example (C D S : Prop) (h : (S → C) ∧ (S → D)) : S → C ∧ D := by
    exact λ hl1 => and_intro (h.left hl1) (h.right hl1)

-- note: using placeholder _ to ignore unneeded evidence
example (R S : Prop) : R → (S → R) ∧ (¬S → R) := by
    have h1 : R → (S → R) := λ hl1 => λ _ => hl1
    have h2 : R → (¬ S → R) := λ hl1 => λ _ => hl1
    exact λ hlg1 => and_intro (h1 hlg1) (h2 hlg1)
