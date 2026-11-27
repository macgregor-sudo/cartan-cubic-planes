module

public import ThirteenPlanes.Cartan.QuaternionJordan
public import ThirteenPlanes.Quaternionic.ImaginaryConjugation
public import Mathlib.Data.Matrix.Basis

@[expose] public section

set_option backward.privateInPublic true

/-! Faithfulness of the skew-Hermitian quaternionic matrix action. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix BigOperators

noncomputable section

private theorem conjTranspose_singleQuat (i j : Outcome) (q : Q) :
    (Matrix.single i j q : QMat)ᴴ = Matrix.single j i (star q) := by
  apply Matrix.ext
  intro a b
  change star (Matrix.single i j q b a) = Matrix.single j i (star q) a b
  simp only [Matrix.single, Matrix.of_apply, apply_ite, star_zero, and_comm]
  split_ifs <;> rfl

private theorem diagonalTest_selfAdjoint (i : Outcome) :
    (Matrix.single i i (1 : Q)).IsHermitian := by
  change (Matrix.single i i (1 : Q) : QMat)ᴴ = _
  rw [conjTranspose_singleQuat, star_one]

private theorem edgeTest_selfAdjoint (i j : Outcome) (q : Q) :
    (Matrix.single i j q + Matrix.single j i (star q)).IsHermitian := by
  change (Matrix.single i j q + Matrix.single j i (star q) : QMat)ᴴ = _
  rw [Matrix.conjTranspose_add, conjTranspose_singleQuat, conjTranspose_singleQuat,
    star_star, add_comm]

private theorem commute_of_commutator_zero (A : quaternionSkewMatrices)
    (hz : quaternionCommutatorLinear A = 0) (X : QMat) (hX : X.IsHermitian) :
    A.val * X = X * A.val := by
  have h : quaternionCommutator A (fullOfMatrix X hX) = 0 := by
    exact LinearMap.congr_fun (congrArg Subtype.val hz) _
  have hmat := congrArg fullMat h
  rw [quaternionCommutator_matrix, fullMat_ofMatrix, map_zero] at hmat
  exact sub_eq_zero.mp hmat

/-- The compact quaternionic matrix algebra acts faithfully on actual unital Hermitian matrices. -/
theorem quaternionCommutatorLinear_injective : Function.Injective quaternionCommutatorLinear := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro A hA
  have hz : quaternionCommutatorLinear A = 0 := hA
  have offdiag (i j : Outcome) (hij : i ≠ j) : A.val i j = 0 := by
    have hh := congrArg (fun X : QMat => X i j)
      (commute_of_commutator_zero A hz _ (diagonalTest_selfAdjoint j))
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij, mul_one] at hh
    exact hh
  have edge (i j : Outcome) (hij : i ≠ j) (q : Q) : A.val i i * q = q * A.val j j := by
    have hh := congrArg (fun X : QMat => X i j)
      (commute_of_commutator_zero A hz _ (edgeTest_selfAdjoint i j q))
    simp only [mul_add, add_mul, Matrix.add_apply] at hh
    rw [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ hij.symm,
      Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij, add_zero,
      add_zero] at hh
    exact hh
  have pure (i : Outcome) : (A.val i i).re = 0 := by
    have hh := congrArg (fun X : QMat => (X i i).re) A.property
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Quaternion.re_star, Quaternion.re_neg] at hh
    linarith
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change A.val i j = 0
  by_cases hij : i = j
  · subst j
    let j := i + 1
    have hij : i ≠ j := by
      change i ≠ i + 1
      fin_cases i <;> decide
    have hsame : A.val i i = A.val j j := by simpa only [mul_one, one_mul] using edge i j hij 1
    have hi : A.val i i * qi = qi * A.val i i := by simpa only [← hsame] using edge i j hij qi
    have hj : A.val i i * qj = qj * A.val i i := by
      simpa only [← hsame] using edge i j hij qj
    have hiJ := congrArg (fun q : Q => q.imK) hi
    have hiK := congrArg (fun q : Q => q.imJ) hi
    have hjI := congrArg (fun q : Q => q.imK) hj
    simp [qi] at hiJ
    simp [qi] at hiK
    simp [qj] at hjI
    apply Quaternion.ext <;> simp only [Quaternion.re_zero, Quaternion.imI_zero,
      Quaternion.imJ_zero, Quaternion.imK_zero]
    · exact pure i
    · linarith
    · linarith
    · linarith
  · exact offdiag i j hij

/-- The literal commutator representation identifies the two compact operator carriers. -/
def quaternionCommutatorEquiv : quaternionSkewMatrices ≃ₗ[ℝ] quaternionOperatorAlgebra :=
  LinearEquiv.ofInjective quaternionCommutatorLinear quaternionCommutatorLinear_injective

private def quaternionSkewBracket (A B : quaternionSkewMatrices) : quaternionSkewMatrices :=
  ⟨A.val * B.val - B.val * A.val, by
    change (A.val * B.val - B.val * A.val)ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      A.property, B.property, neg_mul_neg, neg_mul_neg, neg_sub]⟩

theorem quaternionCommutator_bracket (A B : quaternionSkewMatrices) :
    quaternionCommutator (quaternionSkewBracket A B) =
      operatorBracket (quaternionCommutator A) (quaternionCommutator B) := by
  apply LinearMap.ext
  intro x
  apply fullMat_injective
  change fullMat (quaternionCommutator (quaternionSkewBracket A B) x) =
    fullMat (quaternionCommutator A (quaternionCommutator B x) -
      quaternionCommutator B (quaternionCommutator A x))
  simp only [map_sub, quaternionCommutator_matrix, quaternionSkewBracket]
  noncomm_ring

/-- Commutativity is exactly preserved by the faithful native representation. -/
theorem quaternionCommutator_commute_iff (A B : quaternionSkewMatrices) :
    Commute (quaternionCommutator A) (quaternionCommutator B) ↔ Commute A.val B.val := by
  constructor
  · intro h
    have hz : quaternionCommutator (quaternionSkewBracket A B) = 0 :=
      (quaternionCommutator_bracket A B).trans (sub_eq_zero.mpr h.eq)
    have hzero : quaternionCommutatorLinear (quaternionSkewBracket A B) = 0 :=
      Subtype.ext hz
    exact sub_eq_zero.mp ((congrArg Subtype.val
      (quaternionCommutatorLinear_injective (hzero.trans quaternionCommutatorLinear.map_zero.symm))) :
      A.val * B.val - B.val * A.val = 0)
  · intro h
    have hzero : quaternionSkewBracket A B = 0 := Subtype.ext (sub_eq_zero.mpr h.eq)
    have hq : quaternionCommutator (0 : quaternionSkewMatrices) = 0 :=
      congrArg Subtype.val quaternionCommutatorLinear.map_zero
    have hp := quaternionCommutator_bracket A B
    rw [hzero, hq] at hp
    exact sub_eq_zero.mp hp.symm

end

end ThirteenPlanes.Cartan
