module

public import ThirteenPlanes.Quaternionic.Algebra
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.InnerProductSpace.Symmetric

@[expose] public section

/-!
# Faithful real action of native quaternion matrices

The algebraic column action is wrapped from Mathlib's ordinary matrix-vector
bilinear map. The real Hilbert carrier uses the existing Euclidean quaternion
inner product. No real diagonalizer is presumed to be quaternion linear.
The following declarations establish these native bridges.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

/-- Literal quaternion matrix multiplication on columns, linear over the reals. -/
def matrixAction (A : QMat) : QVec →ₗ[ℝ] QVec := Matrix.mulVecBilin ℝ ℝ A

@[simp] lemma matrixAction_apply (A : QMat) (v : QVec) : matrixAction A v = A *ᵥ v := rfl

lemma matrixAction_injective : Function.Injective matrixAction := by
  intro A B h
  apply Matrix.ext
  intro i j
  have h' := congrArg
    (fun T : QVec →ₗ[ℝ] QVec => T (Pi.single j 1) i) h
  change (A *ᵥ Pi.single j 1) i = (B *ᵥ Pi.single j 1) i at h'
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h'

lemma matrixAction_one : matrixAction 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact Matrix.one_mulVec v

lemma matrixAction_mul (A B : QMat) :
    matrixAction (A * B) = (matrixAction A).comp (matrixAction B) := by
  apply LinearMap.ext
  intro v
  exact (Matrix.mulVec_mulVec v A B).symm

/-- Right quaternion multiplication is respected without commuting quaternion
factors. This is the extra symmetry a general real operator need not have. -/
lemma matrixAction_right_mul (A : QMat) (v : QVec) (q : Q) :
    matrixAction A (fun i => v i * q) = fun i => matrixAction A v i * q := by
  funext i
  change (∑ j, A i j * (v j * q)) = (∑ j, A i j * v j) * q
  simp only [Finset.sum_mul, mul_assoc]

/-- The full quaternion-valued adjoint identity, prior to taking real parts. -/
lemma qInner_matrixAction_adjoint (A : QMat) (u v : QVec) :
    qInner (matrixAction A u) v = qInner u (matrixAction Aᴴ v) := by
  simp only [matrixAction_apply, qInner, Matrix.mulVec, dotProduct,
    star_sum, star_mul, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_assoc _ _ _

/-- The genuine real Euclidean space of three quaternion columns. -/
abbrev QHilbert := PiLp 2 (fun _ : Outcome => Q)

/-- Only the normed carrier changes; the entries and real vector operations do not. -/
def columnEquiv : QHilbert ≃ₗ[ℝ] QVec := WithLp.linearEquiv 2 ℝ QVec

/-- The faithful real operator used by the existing real spectral theory. -/
def realAction (A : QMat) : QHilbert →ₗ[ℝ] QHilbert :=
  columnEquiv.symm.toLinearMap.comp ((matrixAction A).comp columnEquiv.toLinearMap)

@[simp] lemma realAction_apply (A : QMat) (v : QHilbert) :
    columnEquiv (realAction A v) = matrixAction A (columnEquiv v) := by
  simp [realAction]

lemma realAction_injective : Function.Injective realAction := by
  intro A B h
  apply matrixAction_injective
  apply LinearMap.ext
  intro v
  have h' := congrArg
    (fun T : QHilbert →ₗ[ℝ] QHilbert => columnEquiv (T (columnEquiv.symm v))) h
  simpa only [realAction_apply, LinearEquiv.apply_symm_apply] using h'

lemma realAction_one : realAction 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply columnEquiv.injective
  simpa only [realAction_apply, LinearMap.id_apply] using
    congrArg (fun T : QVec →ₗ[ℝ] QVec => T (columnEquiv v)) matrixAction_one

lemma realAction_mul (A B : QMat) :
    realAction (A * B) = (realAction A).comp (realAction B) := by
  apply LinearMap.ext
  intro v
  apply columnEquiv.injective
  change columnEquiv (realAction (A * B) v) =
    columnEquiv (realAction A (realAction B v))
  rw [realAction_apply, realAction_apply, realAction_apply]
  exact congrArg (fun T : QVec →ₗ[ℝ] QVec => T (columnEquiv v)) (matrixAction_mul A B)

lemma quaternion_inner_eq_qInner_re (p q : Q) : inner ℝ p q = (star p * q).re := by
  simp only [Quaternion.inner_def, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

lemma hilbert_inner_eq_qInner_re (u v : QHilbert) :
    inner ℝ u v = (qInner (columnEquiv u) (columnEquiv v)).re := by
  change (∑ i, inner ℝ (u i) (v i)) = (∑ i, star (u i) * v i).re
  rw [quaternion_re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact quaternion_inner_eq_qInner_re _ _

/-- Taking the real part of the exact quaternion adjoint identity gives the
correct real adjoint, with the source right-module convention retained. -/
lemma realAction_adjoint_identity (A : QMat) (u v : QHilbert) :
    inner ℝ (realAction A u) v = inner ℝ u (realAction Aᴴ v) := by
  rw [hilbert_inner_eq_qInner_re, hilbert_inner_eq_qInner_re,
    realAction_apply, realAction_apply, qInner_matrixAction_adjoint]

lemma realAction_isSymmetric {A : QMat} (hA : A.IsHermitian) :
    (realAction A).IsSymmetric := by
  intro u v
  simpa only [hA.eq] using realAction_adjoint_identity A u v

lemma realAction_commute {A B : QMat} (hAB : Commute A B) :
    Commute (realAction A) (realAction B) := by
  change (realAction A).comp (realAction B) = (realAction B).comp (realAction A)
  rw [← realAction_mul, ← realAction_mul, hAB.eq]

/-- Literal independent right multiplication in each column entry. -/
def rightMultiply (q : Q) (v : QHilbert) : QHilbert :=
  WithLp.toLp 2 (fun i => v i * q)

lemma realAction_rightMultiply (A : QMat) (v : QHilbert) (q : Q) :
    realAction A (rightMultiply q v) = rightMultiply q (realAction A v) := by
  apply columnEquiv.injective
  change matrixAction A (fun i => v i * q) = fun i => matrixAction A (columnEquiv v) i * q
  exact matrixAction_right_mul A (columnEquiv v) q

/-- A real subspace is stable under the actual right quaternion scalar action. -/
def RightStable (S : Submodule ℝ QHilbert) : Prop :=
  ∀ v ∈ S, ∀ q : Q, rightMultiply q v ∈ S

end QuaternionicMUB
