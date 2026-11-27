module

public import ThirteenPlanes.Cartan.QuaternionFaithful
public import ThirteenPlanes.Cartan.Conjugation
public import ThirteenPlanes.Cartan.Restriction
public import Mathlib.Algebra.Lie.Matrix

@[expose] public section

/-! The compact symplectic Lie algebra on skew-Hermitian quaternionic matrices. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix RealInnerProductSpace

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Compact sp(3), with the literal matrix commutator. -/
abbrev compactSp3 : LieSubalgebra ℝ QMat :=
  { quaternionSkewMatrices with
    lie_mem' := by
      intro A B hA hB
      change (A * B - B * A)ᴴ = -(A * B - B * A)
      change Aᴴ = -A at hA
      change Bᴴ = -B at hB
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB,
        neg_mul_neg, neg_mul_neg, neg_sub] }

@[simp] theorem mem_compactSp3 (A : QMat) : A ∈ compactSp3 ↔ Aᴴ = -A := Iff.rfl

/-- The quaternionic matrices and their faithful commutator representation. -/
abbrev compactSp3Operators : compactSp3 ≃ₗ[ℝ] quaternionOperatorAlgebra :=
  quaternionCommutatorEquiv

/-- Conjugation through an actual two-sided quaternionic unitary basis. -/
def compactSp3Conjugate (U : QBasis) : compactSp3 ≃ₗ⁅ℝ⁆ compactSp3 :=
  { ((quaternionicPullback U).submoduleMap quaternionSkewMatrices).trans
    (LinearEquiv.ofEq _ quaternionSkewMatrices (by
      ext A
      rw [Submodule.mem_map_equiv]
      change (U.mat * A * U.matᴴ)ᴴ = -(U.mat * A * U.matᴴ) ↔ Aᴴ = -A
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        ← mul_assoc]
      change (quaternionicPullback U).symm Aᴴ = -(quaternionicPullback U).symm A ↔ Aᴴ = -A
      rw [← map_neg]
      exact (quaternionicPullback U).symm.injective.eq_iff)) with
  map_lie' := by
    intro A B
    apply Subtype.ext
    change unitaryConjugate U (A.val * B.val - B.val * A.val) =
      unitaryConjugate U A.val * unitaryConjugate U B.val -
        unitaryConjugate U B.val * unitaryConjugate U A.val
    rw [show unitaryConjugate U (A.val * B.val - B.val * A.val) =
      unitaryConjugate U (A.val * B.val) - unitaryConjugate U (B.val * A.val)
      from map_sub (quaternionicPullback U) _ _, unitaryConjugate_mul, unitaryConjugate_mul] }

@[simp] theorem compactSp3Conjugate_val (U : QBasis) (A : compactSp3) :
    (compactSp3Conjugate U A).val = U.matᴴ * A.val * U.mat := rfl

end
end ThirteenPlanes.Cartan
