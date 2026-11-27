module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact real radicals for the native sharp quaternionic triple

These are scalar identities for the explicit source witness, not a substitute
for constructing and checking its actual quaternionic orthonormal bases.
-/

noncomputable section

namespace QuaternionicMUB.AttainmentScalars

def r : ℝ := Real.sqrt (Real.sqrt 3)
def B : ℝ := Real.sqrt 2 / 2
def delta : ℝ := (Real.sqrt 3 - 1) * B
def A : ℝ := (r + delta) / 2
def C : ℝ := (r - delta) / 2

lemma sqrt_three_square : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

lemma r_square : r ^ 2 = Real.sqrt 3 := by
  exact Real.sq_sqrt (Real.sqrt_nonneg _)

lemma B_square : B ^ 2 = (1 / 2 : ℝ) := by
  have h : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold B
  nlinarith

lemma delta_square : delta ^ 2 = 2 - Real.sqrt 3 := by
  rw [delta, mul_pow, B_square]
  nlinarith [sqrt_three_square]

lemma A_add_C : A + C = r := by unfold A C; ring
lemma A_sub_C : A - C = delta := by unfold A C; ring

lemma A_square_add_C_square : A ^ 2 + C ^ 2 = 1 := by
  unfold A C
  nlinarith [r_square, delta_square]

lemma A_mul_C : A * C = (Real.sqrt 3 - 1) / 2 := by
  unfold A C
  nlinarith [r_square, delta_square]

lemma B_mul_difference : B * (A - C) = (Real.sqrt 3 - 1) / 2 := by
  rw [A_sub_C]
  calc
    B * delta = (Real.sqrt 3 - 1) * B ^ 2 := by unfold delta; ring
    _ = (Real.sqrt 3 - 1) / 2 := by rw [B_square]; ring

lemma correlation_scalar : A * B - A * C - B * C = 0 := by
  have h := B_mul_difference
  rw [← A_mul_C] at h
  nlinarith

lemma skew_square : (A ^ 2 - C ^ 2) ^ 2 = 2 * Real.sqrt 3 - 3 := by
  calc
    (A ^ 2 - C ^ 2) ^ 2 = (A ^ 2 + C ^ 2) ^ 2 - 4 * (A * C) ^ 2 := by ring
    _ = 2 * Real.sqrt 3 - 3 := by
      rw [A_square_add_C_square, A_mul_C]
      nlinarith [sqrt_three_square]

end QuaternionicMUB.AttainmentScalars
