module

public import ThirteenPlanes.Quaternionic.JointEigenbasis
public import ThirteenPlanes.Quaternionic.FrameGeometry
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The native traceless quaternionic quartic identity

Diagonalize the actual Hermitian matrix using the unrestricted proved spectral
return, preserve real traces under its two-sided quaternion unitary, and use
the elementary identity for three real eigenvalues summing to zero.
No Albert embedding or supplied quartic certificate is assumed.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

def unitaryConjugate (U : QBasis) (A : QMat) : QMat :=
  U.matᴴ * A * U.mat

lemma unitaryConjugate_mul (U : QBasis) (A B : QMat) :
    unitaryConjugate U (A * B) = unitaryConjugate U A * unitaryConjugate U B := by
  simp only [unitaryConjugate, mul_assoc]
  rw [← mul_assoc U.mat U.matᴴ (B * U.mat), U.mul_adjoint, one_mul]

lemma unitaryConjugate_one (U : QBasis) : unitaryConjugate U 1 = 1 := by
  simp only [unitaryConjugate, mul_one, U.adjoint_mul]

lemma unitaryConjugate_pow (U : QBasis) (A : QMat) (n : ℕ) :
    unitaryConjugate U (A ^ n) = unitaryConjugate U A ^ n := by
  induction n with
  | zero => simp only [pow_zero, unitaryConjugate_one]
  | succ n ih => rw [pow_succ, unitaryConjugate_mul, ih, pow_succ]

lemma rtrace_unitaryConjugate (U : QBasis) (A : QMat) :
    rtrace (unitaryConjugate U A) = rtrace A := by
  rw [unitaryConjugate, rtrace_mul_rotate, mul_assoc, U.mul_adjoint, mul_one]

lemma rtrace_realDiagonal_pow (a : Outcome → ℝ) (n : ℕ) :
    rtrace (realDiagonal a ^ n) = ∑ i, a i ^ n := by
  simp [rtrace, realDiagonal, Matrix.diagonal_pow, ← Quaternion.coe_pow]

lemma rtrace_pow_eq_diagonal (U : QBasis) (A : QMat) (a : Outcome → ℝ)
    (hdiag : unitaryConjugate U A = realDiagonal a) (n : ℕ) :
    rtrace (A ^ n) = ∑ i, a i ^ n := by
  calc
    rtrace (A ^ n) = rtrace (unitaryConjugate U (A ^ n)) :=
      (rtrace_unitaryConjugate U (A ^ n)).symm
    _ = rtrace (realDiagonal a ^ n) := by rw [unitaryConjugate_pow, hdiag]
    _ = ∑ i, a i ^ n := rtrace_realDiagonal_pow a n

lemma real_triple_quartic (a : Outcome → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i, a i ^ 4) = (1 / 2 : ℝ) * (∑ i, a i ^ 2) ^ 2 := by
  rw [Fin.sum_univ_three] at ha
  have h2 : a 2 = - a 0 - a 1 := by linarith
  simp only [Fin.sum_univ_three, h2]
  ring

/-- Every actual traceless quaternionic Hermitian three-by-three matrix
satisfies the universal rank-three quartic trace identity. -/
theorem traceless_quartic (X : QMat) (hX : X.IsHermitian) (ht : rtrace X = 0) :
    rtrace (X ^ 4) = (1 / 2 : ℝ) * (rtrace (X ^ 2)) ^ 2 := by
  obtain ⟨U, a, b, hdiag, _⟩ :=
    commuting_hermitian_simultaneous_diagonalization X 0 hX
      Matrix.isHermitian_zero (Commute.zero_right X)
  have hdiag' : unitaryConjugate U X = realDiagonal a := hdiag
  have ha : ∑ i, a i = 0 := by
    have h := rtrace_pow_eq_diagonal U X a hdiag' 1
    simpa only [pow_one, ht] using h.symm
  rw [rtrace_pow_eq_diagonal U X a hdiag' 4,
    rtrace_pow_eq_diagonal U X a hdiag' 2]
  exact real_triple_quartic a ha


lemma rtrace_rotate4 (A B C D : QMat) :
    rtrace (A * (B * (C * D))) = rtrace (B * (C * (D * A))) := by
  rw [rtrace_mul_comm A (B * (C * D))]
  simp only [mul_assoc]

lemma rtrace_xyyx (X Y : QMat) :
    rtrace (X * (Y * (Y * X))) = rtrace (X * (X * (Y * Y))) := by
  rw [rtrace_rotate4 X Y Y X, ← mul_assoc Y Y (X * X),
    rtrace_mul_comm (Y * Y) (X * X), mul_assoc]

lemma rtrace_yxxy (X Y : QMat) :
    rtrace (Y * (X * (X * Y))) = rtrace (X * (X * (Y * Y))) :=
  rtrace_rotate4 Y X X Y

lemma rtrace_yyxx (X Y : QMat) :
    rtrace (Y * (Y * (X * X))) = rtrace (X * (X * (Y * Y))) := by
  rw [← mul_assoc Y Y (X * X), rtrace_mul_comm (Y * Y) (X * X), mul_assoc]

lemma rtrace_yxyx (X Y : QMat) :
    rtrace (Y * (X * (Y * X))) = rtrace (X * (Y * (X * Y))) :=
  rtrace_rotate4 Y X Y X

lemma rtrace_fourth_add_sub (X Y : QMat) :
    rtrace ((X + Y) ^ 4) + rtrace ((X - Y) ^ 4) -
      2 * rtrace (X ^ 4) - 2 * rtrace (Y ^ 4) =
        8 * rtrace (X ^ 2 * Y ^ 2) + 4 * rtrace (X * Y * X * Y) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_add, add_mul, mul_sub, sub_mul,
    mul_assoc, rtrace_add, rtrace_sub, rtrace_xyyx, rtrace_yxxy,
    rtrace_yyxx, rtrace_yxyx]
  ring

lemma traceForm_jordan_square (X Y : QMat) :
    2 * traceForm (jordan X Y) (jordan X Y) =
      rtrace (X ^ 2 * Y ^ 2) + rtrace (X * Y * X * Y) := by
  simp only [jordan, traceForm_eq_rtrace_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, add_mul, mul_add, rtrace_smul, rtrace_add, pow_two, mul_assoc,
    rtrace_xyyx, rtrace_yxxy, rtrace_yyxx, rtrace_yxyx]
  ring

lemma rtrace_square_add (X Y : QMat) :
    rtrace ((X + Y) ^ 2) = rtrace (X ^ 2) + 2 * rtrace (X * Y) + rtrace (Y ^ 2) := by
  simp only [pow_two, add_mul, mul_add, rtrace_add, rtrace_mul_comm Y X]
  ring

lemma rtrace_square_sub (X Y : QMat) :
    rtrace ((X - Y) ^ 2) = rtrace (X ^ 2) - 2 * rtrace (X * Y) + rtrace (Y ^ 2) := by
  simp only [pow_two, sub_mul, mul_sub, rtrace_sub, rtrace_mul_comm Y X]
  ring

/-- Polarization is on arbitrary actual trace-zero Hermitian matrices, with no
orthogonality or normalization assumption hidden in the statement. -/
theorem traceless_quartic_polarized (X Y : QMat)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (htX : rtrace X = 0) (htY : rtrace Y = 0) :
    rtrace (X ^ 2 * Y ^ 2) + 2 * traceForm (jordan X Y) (jordan X Y) =
      (1 / 2 : ℝ) * traceForm X X * traceForm Y Y + (traceForm X Y) ^ 2 := by
  have hp := traceless_quartic (X + Y) (hX.add hY)
    (by rw [rtrace_add, htX, htY]; ring)
  have hm := traceless_quartic (X - Y) (hX.sub hY)
    (by change rtraceLinear (X - Y) = 0; rw [map_sub]; change rtrace X - rtrace Y = 0; rw [htX, htY]; ring)
  have hx := traceless_quartic X hX htX
  have hy := traceless_quartic Y hY htY
  have hmix := rtrace_fourth_add_sub X Y
  rw [hp, hm, hx, hy, rtrace_square_add, rtrace_square_sub] at hmix
  have hj := traceForm_jordan_square X Y
  simp only [traceForm_eq_rtrace_mul, ← pow_two] at *
  nlinarith

/-- The literal quaternionic matrix commutator has its actual Frobenius square. -/
theorem commutator_frobeniusSq (X Y : QMat)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobeniusSq (X * Y - Y * X) =
      4 * (rtrace (X ^ 2 * Y ^ 2) - traceForm (jordan X Y) (jordan X Y)) := by
  have hj := traceForm_jordan_square X Y
  rw [← rtrace_adjoint_mul_self]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX.eq, hY.eq,
    sub_mul, mul_sub, rtrace_sub, pow_two, mul_assoc,
    rtrace_xyyx, rtrace_yxxy, rtrace_yyxx, rtrace_yxyx] at *
  linarith

end QuaternionicMUB
