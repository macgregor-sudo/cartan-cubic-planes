module

public import ThirteenPlanes.SignedFields
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace ThirteenPlanes

noncomputable section

/-- Real fields with the kinetic metric of the signed model. -/
def SignedField := ↥signedFields

instance : AddCommGroup SignedField := inferInstanceAs (AddCommGroup ↥signedFields)
instance : Module ℝ SignedField := inferInstanceAs (Module ℝ ↥signedFields)
instance : FiniteDimensional ℝ SignedField := inferInstanceAs (FiniteDimensional ℝ ↥signedFields)

def signedCoordinates : SignedField →ₗ[ℝ] (NonzeroCharge → ℂ) := signedFields.subtype

/-- Both members of an opposite pair occur, each with weight three. -/
def signedFieldEmbedding : SignedField →ₗ[ℝ] EuclideanSpace ℂ NonzeroCharge :=
  Real.sqrt 3 • ((WithLp.linearEquiv 2 ℝ (NonzeroCharge → ℂ)).symm.toLinearMap.comp signedCoordinates)

theorem signedFieldEmbedding_injective : Function.Injective signedFieldEmbedding := by
  intro a b h
  have hr : Real.sqrt 3 ≠ 0 := by positivity
  have he := (smul_right_injective _ hr) h
  exact (signedFields.subtype_injective ((WithLp.linearEquiv 2 ℝ (NonzeroCharge → ℂ)).symm.injective he))

instance : NormedAddCommGroup SignedField :=
  NormedAddCommGroup.induced _ _ signedFieldEmbedding signedFieldEmbedding_injective

instance : InnerProductSpace ℝ SignedField := InnerProductSpace.induced signedFieldEmbedding

theorem signedField_norm_sq (x : SignedField) :
    ‖x‖ ^ 2 = 3 * ∑ i, ‖signedCoordinates x i‖ ^ 2 := by
  change ‖signedFieldEmbedding x‖ ^ 2 = _
  change ‖Real.sqrt 3 • (WithLp.toLp 2 (signedCoordinates x) : EuclideanSpace ℂ NonzeroCharge)‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by norm_num), EuclideanSpace.norm_sq_eq]

end
end ThirteenPlanes
