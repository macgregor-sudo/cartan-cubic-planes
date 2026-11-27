module

public import ThirteenPlanes.Quaternionic.PhaseTransforms
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Exact real trace formulas for the literal centered cubic tensor. -/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma rtrace_three_reverse (A B C : QMat) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    rtrace (B*A*C) = rtrace (A*B*C) := by
  calc
    rtrace (B*A*C) = rtrace ((B*A*C)ᴴ) := (rtrace_conjTranspose _).symm
    _ = rtrace (C*A*B) := by
      simp only [Matrix.conjTranspose_mul, hA.eq, hB.eq, hC.eq, mul_assoc]
    _ = rtrace (A*B*C) := rtrace_mul_rotate C A B

lemma traceForm_jordan_hermitian (A B C : QMat) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) :
    traceForm (jordan A B) C = rtrace (A*B*C) := by
  rw [traceForm_eq_rtrace_mul, jordan, smul_mul_assoc, add_mul,
    rtrace_smul, rtrace_add, rtrace_three_reverse A B C hA hB hC]
  ring

lemma rtrace_coordinate_mul (A : QMat) (a : Outcome) :
    rtrace (QBasis.coordinate.point a * A) = (A a a).re := by
  fin_cases a <;>
    simp [QBasis.point, QBasis.column, QBasis.coordinate, projector, rtrace,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- No unbiasedness assumption is used: this is the actual cubic entry for
arbitrary quaternion columns in the last two slots. -/
lemma coordinate_tensor_projectors (g h : Outcome → QVec) (a b c : Outcome) :
    centeredTensor QBasis.coordinate.point (fun j => projector (g j))
      (fun j => projector (h j)) a b c =
      (g b a * qInner (g b) (h c) * star (h c a)).re - 1/9 := by
  rw [centeredTensor, traceForm_jordan_hermitian _ _ _
    (QBasis.point_isHermitian _ _) (projector_isHermitian _) (projector_isHermitian _),
    mul_assoc, rtrace_coordinate_mul, projector_mul_apply]

end QuaternionicMUB
