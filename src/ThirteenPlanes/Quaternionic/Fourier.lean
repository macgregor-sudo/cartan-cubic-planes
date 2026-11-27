module

public import ThirteenPlanes.Quaternionic.Algebra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Literal quaternionic Fourier basis in dimension three

The entries are actual quaternions. The positive scale sqrt(3)/3 is equal to
1/sqrt(3). Conjugating the explicit cubic root of unity gives its square, so
the displayed symmetric matrix is the ordinary normalized Fourier matrix.
The unitary and unbiasedness claims below concern the native QBasis carrier.
-/

noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

/-- The specified complex cube root inside the literal quaternion algebra. -/
def omega : Q := ⟨-1/2, Real.sqrt 3/2, 0, 0⟩

def fourierScale : ℝ := Real.sqrt 3/3

lemma fourierScale_eq_inv_sqrt : fourierScale = 1/Real.sqrt 3 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  dsimp [fourierScale]
  field_simp
  nlinarith

lemma omega_square : omega*omega=star omega := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  ext <;> norm_num [omega, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul] <;> nlinarith

lemma omega_normSq : Quaternion.normSq omega=1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  norm_num [omega, Quaternion.normSq_def'] <;> nlinarith

lemma omega_sum : 1+omega+star omega=0 := by
  ext <;> norm_num [omega]

lemma omega_cube : omega*omega*omega=1 := by
  rw [omega_square, Quaternion.star_mul_self, omega_normSq] <;> rfl

/-- Fourier matrix written with its two distinct nonreal phases. -/
def fourierMatrix : QMat :=
  fourierScale • !![1,1,1; 1,omega,star omega; 1,star omega,omega]

lemma fourierMatrix_adjoint_mul : fourierMatrixᴴ * fourierMatrix=1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 3)^4=9 := by
    calc
      (Real.sqrt 3)^4 = ((Real.sqrt 3)^2)^2 := by ring
      _ = 9 := by rw [hs]; norm_num
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    ext <;>
    norm_num [fourierMatrix, fourierScale, omega, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [hs, hs4]

lemma fourierMatrix_mul_adjoint : fourierMatrix * fourierMatrixᴴ=1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 3)^4=9 := by
    calc
      (Real.sqrt 3)^4 = ((Real.sqrt 3)^2)^2 := by ring
      _ = 9 := by rw [hs]; norm_num
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    ext <;>
    norm_num [fourierMatrix, fourierScale, omega, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [hs, hs4]

/-- An actual ordered quaternionic orthonormal basis. -/
def fourierBasis : QBasis where
  mat := fourierMatrix
  adjoint_mul := fourierMatrix_adjoint_mul
  mul_adjoint := fourierMatrix_mul_adjoint

lemma fourierMatrix_entry_normSq (i j : Outcome) :
    Quaternion.normSq (fourierMatrix i j)=(1/3:ℝ) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 3)^4=9 := by
    calc
      (Real.sqrt 3)^4 = ((Real.sqrt 3)^2)^2 := by ring
      _ = 9 := by rw [hs]; norm_num
  fin_cases i <;> fin_cases j <;>
    norm_num [fourierMatrix, fourierScale, omega, Quaternion.normSq_def'] <;>
    ring_nf <;> norm_num [hs, hs4]

lemma coordinate_column_inner (V : QBasis) (a b : Outcome) :
    qInner (QBasis.coordinate.column a) (V.column b) = V.mat a b := by
  simp [qInner, QBasis.column, QBasis.coordinate, Matrix.one_apply, apply_ite]

/-- A native two-basis witness, used before constructing any attaining triple. -/
theorem coordinate_fourier_mutuallyUnbiased : QBasis.coordinate.MutuallyUnbiased fourierBasis := by
  intro a b
  rw [coordinate_column_inner]
  exact fourierMatrix_entry_normSq a b

end QuaternionicMUB
