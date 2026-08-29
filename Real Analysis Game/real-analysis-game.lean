import Lean4PracticeWithMathlib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF

-- There exists a real number that makes this binomial expansion work.
example (x y : ℝ) : ∃ (c : ℝ), (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4 := by
  use 6
  ring_nf

-- the intro tactic:
-- For all positive real numbers, this algebraic identity holds.
example : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  intro x hx
  rfl

-- the specialize tactic
-- If a function of x always equals x², then it equals t² when evaluated at t.
example (t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f (x) = x ^ 2) : f (t) = t^2 := by
  specialize hf t
  specialize hf t_pos
  apply hf

-- the choose tactic
-- If there exists a point where f equals 2, then there exists a point where f² equals 4.
example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  choose d h2 using h
  use d
  rewrite [h2]
  ring_nf

-- boss level
example (f : ℝ → ℝ)
  (h_existential : ∃ (a : ℝ), f (a) = 3)
  (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9)
  : ∃ (b : ℝ), ∀ y > 0, f (y + 1)^2 = (f (y) + (f b)^2)^2
  := by
  choose d hfd using h_existential
  use d
  intro e e_pos
  specialize h_universal e
  specialize h_universal e_pos
  rewrite [h_universal]
  rewrite [hfd]
  ring_nf

-- Pset 1
---------

-- Given that f (u) = 2 * u + 1 for all u, prove that there exists some a such that f (3) = a.
example (f : ℝ → ℝ) (h : ∀ u, f (u) = 2 * u + 1) : ∃ a, f (3) = a := by
  use 7
  specialize h 3
  ring_nf at h
  apply h


-- Show that there exists a constant c so that, for any real numbers x and y
-- with x ^ 2 + y ^ 2 = 2 and x * y = 1, we have (x + y) ^ 2 = c.
example : ∃ c, ∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y = 1 → (x + y) ^ 2 = c := by
  have huv : ∀ (u v : ℝ), (u + v) ^ 2 = u ^ 2 + v ^ 2 + u * v * 2 := by
    intro u v
    ring_nf
  use 4
  intro x y h2 h3
  rewrite [huv]
  rewrite [h2]
  rewrite [h3]
  ring_nf

example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (1) = 8 := by
  specialize h1 0
  rewrite [h2] at h1
  have h5 : g (0+1) = g 1 := by ring_nf
  rewrite [h5] at h1
  rewrite [h1]
  ring_nf

example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (2) = 11 := by
  have h3 : g (0 + 1) = g 0 + 3 := by
    apply h1 0
  have h4 : g 1 = g (0 + 1) := by ring_nf
  rewrite [← h4] at h3
  have h5 : g (1 + 1) = g 1 + 3 := by apply h1 1
  have h6 : g (1 + 1) = g 2 := by ring_nf
  rewrite [← h6]
  rewrite [h5]
  rewrite [h3]
  rewrite [h2]
  ring_nf

example (p : ℝ → ℝ) (x : ℝ) (h1 : ∀ t, p (t) = t ^ 2 + 2 * t) (h2 : p (x) = 15)
  : ∃ b, x ^ 2 + 2 * x = b := by
  use 15
  specialize h1 x
  rewrite [← h1]
  rewrite [← h2]
  rfl
