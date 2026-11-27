module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RealDerivations

open Polynomial
open scoped Matrix

noncomputable section

/-- The commutator in the trace-zero coordinates consisting of the first two diagonal
entries and the three upper-triangular entries in positions 12, 13, 23. -/
def commutatorMatrix (a b c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, -2*a, -2*b, 0;
     0, 0, 2*a, 0, -2*c;
     a, -a, 0, -c, -b;
     2*b, b, c, 0, -a;
     c, 2*c, b, a, 0]

private def gramMatrix (a b c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![2*a^2 + 4*b^2, -2*a^2 + 2*b^2, 2*b*c, -2*a*c, -4*a*b;
     -2*a^2 + 2*c^2, 2*a^2 + 4*c^2, 2*b*c, 4*a*c, 2*a*b;
     3*b*c, 3*b*c, 4*a^2+b^2+c^2, 3*a*b, -3*a*c;
     0, 3*a*c, 3*a*b, a^2+4*b^2+c^2, 3*b*c;
     -3*a*b, 0, -3*a*c, 3*b*c, a^2+b^2+4*c^2]

private theorem gramMatrix_eq (a b c : ℝ) :
    -(commutatorMatrix a b c * commutatorMatrix a b c) = gramMatrix a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutatorMatrix, gramMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 800000 in
/-- In the unnormalized coordinate basis the Gram matrix is the negative square of the
trace-skew commutator matrix. Its characteristic roots are the squared singular values. -/
theorem commutatorGram_charpoly (a b c : ℝ) :
    let A := commutatorMatrix a b c
    let q := a ^ 2 + b ^ 2 + c ^ 2
    (-(A * A)).charpoly = X * (X - C q) ^ 2 * (X - C (4 * q)) ^ 2 := by
  dsimp only
  rw [gramMatrix_eq]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.sub_apply]
  norm_num [gramMatrix, Fin.succAbove, Fin.castSucc, Fin.succ, Fin.castLT, Fin.lt_def]
  ring

end
end ThirteenPlanes.RealDerivations
