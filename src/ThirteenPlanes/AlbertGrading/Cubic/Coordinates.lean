module

public import ThirteenPlanes.AlbertGrading.Cubic.Expansion

@[expose] public section

/-! Coordinates and basis elements on the nonzero grades.

`gradeUnit` and `gradeCoord` extend `u_{g_p}` and `ζ_p` to all 26 nonzero grades by
`u_{-g_p} = ū_{g_p}` and `ζ_{-g_p} = ζ̄_p`. -/

namespace ThirteenPlanes.AlbertGrading.Cubic

open Grading Grading.JC

noncomputable section

variable (sgn : SignedPlaneIndex → Bool)

theorem gradeUnit_signedGrade (u : SignedPlaneIndex → JC) (p : SignedPlaneIndex) (s : Bool) :
    gradeUnit sgn u (signedGrade p s) = if s = sgn p then u p else conj (u p) := by
  unfold gradeUnit
  rw [show (signedPlaneGradeEquiv.symm (signedGrade p s)).2 = s from sgnOf_signedGrade p s,
    pointOfNZ_signedGrade]

theorem gradeCoord_signedGrade (ζ : SignedPlaneIndex → ℂ) (p : SignedPlaneIndex) (s : Bool) :
    gradeCoord sgn ζ (signedGrade p s) = if s = sgn p then ζ p else star (ζ p) := by
  unfold gradeCoord
  rw [show (signedPlaneGradeEquiv.symm (signedGrade p s)).2 = s from sgnOf_signedGrade p s,
    pointOfNZ_signedGrade]

/-- Sums over nonzero grades are sums over points and signs. -/
theorem sum_nonzero {M : Type*} [AddCommMonoid M] (f : NonzeroCharge → M) :
    ∑ k, f k = ∑ p, (f (signedGrade p false) + f (signedGrade p true)) := by
  rw [← signedPlaneGradeEquiv.sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool, add_comm]; rfl

theorem gradeUnit_opp (u : SignedPlaneIndex → JC) (k : NonzeroCharge) :
    gradeUnit sgn u (oppositeCharge k) = conj (gradeUnit sgn u k) := by
  rw [← grade_point_sign k, ← signedGrade_not, gradeUnit_signedGrade, gradeUnit_signedGrade]
  cases sgnOf k <;> cases sgn (pointOfNZ k) <;> simp

theorem gradeCoord_opp (ζ : SignedPlaneIndex → ℂ) (k : NonzeroCharge) :
    gradeCoord sgn ζ (oppositeCharge k) = star (gradeCoord sgn ζ k) := by
  rw [← grade_point_sign k, ← signedGrade_not, gradeCoord_signedGrade, gradeCoord_signedGrade]
  cases sgnOf k <;> cases sgn (pointOfNZ k) <;> simp

/-- `Σ_g Re ζ_g³ = 2 Σ_p Re ζ_p³`. -/
theorem sum_gradeCoord_cube (ζ : SignedPlaneIndex → ℂ) :
    ∑ k, (gradeCoord sgn ζ k ^ 3).re = 2 * ∑ p, (ζ p ^ 3).re := by
  rw [sum_nonzero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hs : ((starRingEnd ℂ) (ζ p) ^ 3).re = (ζ p ^ 3).re := by rw [← map_pow]; rfl
  rw [gradeCoord_signedGrade, gradeCoord_signedGrade]
  cases sgn p <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, Complex.star_def, hs] <;> ring

/-- `Σ_p (ζ_p u_p + ζ̄_p ū_p) = Σ_g ζ_g u_g`. -/
theorem sum_field (u : SignedPlaneIndex → JC) (ζ : SignedPlaneIndex → ℂ) :
    ∑ p, (ζ p • u p + star (ζ p) • conj (u p)) =
      ∑ k, gradeCoord sgn ζ k • gradeUnit sgn u k := by
  rw [sum_nonzero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [gradeCoord_signedGrade, gradeCoord_signedGrade, gradeUnit_signedGrade, gradeUnit_signedGrade]
  cases sgn p <;> simp [add_comm]

end

end ThirteenPlanes.AlbertGrading.Cubic
