import Mathlib

open Set Real

def hello := "world"
example (x : Nat) : x ^ 2 + 6 * x + 9 = (x + 3) ^ 2 := by ring


example : 1 + 1 = 2 := by simp?

-- 10
example (x y : ℚ) (h1 : x = y - 4) (h2 : 7 * x - 2 * y = 17) : x = 5 ∧ y = 9 := by
  have : 7 * (y - 4) - 2 * y = 17 := by linarith
  have : 7 * y - 28 - 2 * y = 17 := by linarith
  have : 5 * y = 45 := by linarith
  have r1 : y = 9 := by linarith
  have r2 : x = 5 := by linarith
  exact ⟨r2, r1⟩

example : InjOn log { x | x > 0} := by
  intro x xpos y ypos
  intro e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : range exp = {y | y > 0} := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

def iden (x : Bool) := x


lemma range_iden_univ : range iden = univ := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro
    use iden x
    rfl

example : preimage iden (range iden) = univ := by 
  rw [range_iden_univ]
  ext
  rfl


def f (x : ℝ) := x^2 + 2

noncomputable def g (x : ℝ ) := sqrt (x - 2)

example (x : ℝ) (h1: x ≥ 2) : (f ∘ g) x = (g ∘ f) x := by
  let y := x - 2

  have x_gt_zero : 0 ≤ x := by linarith
  have h2 : y ≥ 0 :=
    calc y = x - 2 := rfl
      _ ≥ 2 - 2 := by linarith
      _ = 0 := by linarith
  have y_gt_zero : 0 ≤ y := by linarith

  have y_sqr : (sqrt y) ^ 2 + 2 = y + 2 := by
    q

  have h3 : (f ∘ g) x =(sqrt y) ^ 2 + 2 :=
    calc (f ∘ g) x = f (g x) := by rfl
      _ = (g x) ^ 2 + 2 := by rfl
      _ = (sqrt (x - 2)) ^ 2 + 2 := by rfl
      _ = (sqrt y) ^ 2 + 2 := by rfl
  have h5 : (f ∘ g) x = y + 2 :=
      _ = y + 2 := by exact (sq_sqrt y_gt_zero)
  have h4 : (g ∘ f) x = y + 2 :=
    calc (g ∘ f) x = g (f x) := by rfl
      _ = sqrt (x^2 + 2 - 2) := by rfl
      _ = sqrt (x^2) := by ring_nf
      _ = sqrt (x * x) := by ring_nf
      _ = x := by exact (sqrt_mul_self x_gt_zero)
      _ = y + 2 := by ring
  sorry
