module

public import ThirteenPlanes.Quaternionic.TripleLowerBound
public import ThirteenPlanes.Quaternionic.AttainmentScalars
public import ThirteenPlanes.Quaternionic.FourierCoordinateDefs
public import ThirteenPlanes.Quaternionic.ImaginaryConjugation

@[expose] public section

/-! The explicit witness for equality in the quaternionic lower bound.

The phase quaternions use the same native imaginary coordinates as the Fourier basis.
They have unit norms and satisfy both complex autocorrelation identities. -/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

/-- The complex image of the same actual quaternion Fourier cube root. -/
def attainmentOmega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

def attainmentPhases : Outcome → Q :=
  ![(AttainmentScalars.A : Q) + AttainmentScalars.C • qj,
    omega ^ 2 * (AttainmentScalars.B • (1 - qj)),
    -(omega * ((AttainmentScalars.C : Q) + AttainmentScalars.A • qj))]

lemma attainment_star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp

lemma attainmentOmega_square : attainmentOmega ^ 2 = star attainmentOmega := by
  apply Complex.ext <;>
    simp [attainmentOmega, pow_two, Complex.mul_re, Complex.mul_im, Complex.star_def]
  all_goals nlinarith [AttainmentScalars.sqrt_three_square]

lemma attainmentOmega_normSq : Complex.normSq attainmentOmega = 1 := by
  simp [attainmentOmega, Complex.normSq_apply]
  nlinarith [AttainmentScalars.sqrt_three_square]

lemma quaternion_real_add_qj_normSq (a c : ℝ) :
    Quaternion.normSq ((a : Q) + c • qj) = a ^ 2 + c ^ 2 := by
  simp [qj, Quaternion.normSq_def']

lemma attainmentPhases_unit (i : Outcome) : Quaternion.normSq (attainmentPhases i) = 1 := by
  fin_cases i
  · change Quaternion.normSq
      ((AttainmentScalars.A : Q) + AttainmentScalars.C • qj) = 1
    rw [quaternion_real_add_qj_normSq, AttainmentScalars.A_square_add_C_square]
  · change Quaternion.normSq
      (omega ^ 2 * (AttainmentScalars.B • (1 - qj))) = 1
    simp only [map_mul, map_pow, omega_normSq, one_pow, one_mul,
      Quaternion.normSq_smul, AttainmentScalars.B_square]
    norm_num [qj, Quaternion.normSq_def']
  · change Quaternion.normSq
      (-(omega * ((AttainmentScalars.C : Q) + AttainmentScalars.A • qj))) = 1
    rw [Quaternion.normSq_neg, map_mul, omega_normSq, one_mul,
      quaternion_real_add_qj_normSq]
    nlinarith [AttainmentScalars.A_square_add_C_square]

lemma attainment_phaseA_zero : phaseA attainmentPhases 0 = (AttainmentScalars.A : ℂ) := by
  apply Complex.ext <;> simp [phaseA, attainmentPhases, qj]

lemma attainment_phaseB_zero : phaseB attainmentPhases 0 = (AttainmentScalars.C : ℂ) := by
  apply Complex.ext <;> simp [phaseB, attainmentPhases, qj]

lemma attainment_phaseA_one :
    phaseA attainmentPhases 1 = star attainmentOmega * (AttainmentScalars.B : ℂ) := by
  have hω : omega ^ 2 = star omega := by simpa only [pow_two] using omega_square
  change (⟨(omega ^ 2 * (AttainmentScalars.B • (1 - qj))).re,
    (omega ^ 2 * (AttainmentScalars.B • (1 - qj))).imI⟩ : ℂ) = _
  rw [hω]
  apply Complex.ext <;>
    simp [phaseA, attainmentPhases, hω, omega, qj, attainmentOmega,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals ring

lemma attainment_phaseB_one :
    phaseB attainmentPhases 1 = -(star attainmentOmega * (AttainmentScalars.B : ℂ)) := by
  have hω : omega ^ 2 = star omega := by simpa only [pow_two] using omega_square
  change (⟨(omega ^ 2 * (AttainmentScalars.B • (1 - qj))).imJ,
    (omega ^ 2 * (AttainmentScalars.B • (1 - qj))).imK⟩ : ℂ) = _
  rw [hω]
  apply Complex.ext <;>
    simp [phaseB, attainmentPhases, hω, omega, qj, attainmentOmega,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals ring

lemma attainment_phaseA_two :
    phaseA attainmentPhases 2 = -(attainmentOmega * (AttainmentScalars.C : ℂ)) := by
  apply Complex.ext <;>
    simp [phaseA, attainmentPhases, omega, qj, attainmentOmega,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals ring

lemma attainment_phaseB_two :
    phaseB attainmentPhases 2 = -(attainmentOmega * (AttainmentScalars.A : ℂ)) := by
  apply Complex.ext <;>
    simp [phaseB, attainmentPhases, omega, qj, attainmentOmega,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals ring

lemma attainment_correlations_A :
    Heron.correlation (phaseA attainmentPhases) = 0 := by
  have hs : ((AttainmentScalars.A * AttainmentScalars.B -
      AttainmentScalars.A * AttainmentScalars.C -
      AttainmentScalars.B * AttainmentScalars.C : ℝ) : ℂ) = 0 := by
    rw [AttainmentScalars.correlation_scalar]
    rfl
  calc
    Heron.correlation (phaseA attainmentPhases) =
        star attainmentOmega * ((AttainmentScalars.A * AttainmentScalars.B -
          AttainmentScalars.A * AttainmentScalars.C -
          AttainmentScalars.B * AttainmentScalars.C : ℝ) : ℂ) := by
      simp only [Heron.correlation, attainment_phaseA_zero, attainment_phaseA_one,
        attainment_phaseA_two, star_neg, star_mul, star_star, attainment_star_real,
        star_add, star_sub, Complex.ofReal_sub, Complex.ofReal_mul]
      ring_nf
      rw [attainmentOmega_square]
      ring
    _ = 0 := by rw [hs, mul_zero]

lemma attainment_correlations_B :
    Heron.correlation (phaseB attainmentPhases) = 0 := by
  have hs : ((AttainmentScalars.A * AttainmentScalars.B -
      AttainmentScalars.A * AttainmentScalars.C -
      AttainmentScalars.B * AttainmentScalars.C : ℝ) : ℂ) = 0 := by
    rw [AttainmentScalars.correlation_scalar]
    rfl
  calc
    Heron.correlation (phaseB attainmentPhases) =
        star attainmentOmega * ((AttainmentScalars.A * AttainmentScalars.B -
          AttainmentScalars.A * AttainmentScalars.C -
          AttainmentScalars.B * AttainmentScalars.C : ℝ) : ℂ) := by
      simp only [Heron.correlation, attainment_phaseB_zero, attainment_phaseB_one,
        attainment_phaseB_two, star_neg, star_mul, star_star, attainment_star_real,
        star_add, star_sub, Complex.ofReal_sub, Complex.ofReal_mul]
      ring_nf
      rw [attainmentOmega_square]
      ring
    _ = 0 := by rw [hs, mul_zero]


lemma attainment_z_zero :
    Complex.normSq (phaseA attainmentPhases 0) -
      Complex.normSq (phaseB attainmentPhases 0) =
        AttainmentScalars.A ^ 2 - AttainmentScalars.C ^ 2 := by
  rw [attainment_phaseA_zero, attainment_phaseB_zero]
  simp only [Complex.normSq_ofReal]
  ring

lemma attainment_z_one :
    Complex.normSq (phaseA attainmentPhases 1) -
      Complex.normSq (phaseB attainmentPhases 1) = 0 := by
  rw [attainment_phaseA_one, attainment_phaseB_one, Complex.normSq_neg]
  ring

lemma attainment_z_two :
    Complex.normSq (phaseA attainmentPhases 2) -
      Complex.normSq (phaseB attainmentPhases 2) =
        AttainmentScalars.C ^ 2 - AttainmentScalars.A ^ 2 := by
  rw [attainment_phaseA_two, attainment_phaseB_two]
  simp only [Complex.normSq_neg, map_mul, attainmentOmega_normSq, one_mul,
    Complex.normSq_ofReal]
  ring


/-- The actual source witness as a literal ordered quaternionic basis. -/
def attainingBasis : QBasis :=
  phasedFourierBasis attainmentPhases attainmentPhases_unit

lemma coordinate_attaining_mutuallyUnbiased :
    QBasis.coordinate.MutuallyUnbiased attainingBasis := by
  intro a b
  rw [coordinate_column_inner]
  change Quaternion.normSq
    ((phasedFourierBasis attainmentPhases attainmentPhases_unit).column b a) = (1 / 3 : ℝ)
  rw [phasedFourierBasis_column]
  change Quaternion.normSq (attainmentPhases a * fourierMatrix a b) = (1 / 3 : ℝ)
  rw [map_mul, attainmentPhases_unit, one_mul, fourierMatrix_entry_normSq]

lemma fourier_attaining_mutuallyUnbiased :
    fourierBasis.MutuallyUnbiased attainingBasis :=
  fourier_unbiased_of_correlations attainmentPhases attainmentPhases_unit
    attainment_correlations_A attainment_correlations_B

lemma attaining_basisS :
    basisS QBasis.coordinate fourierBasis attainingBasis = 1 - 1 / Real.sqrt 3 := by
  change basisS QBasis.coordinate fourierBasis
    (phasedFourierBasis attainmentPhases attainmentPhases_unit) = _
  rw [basisS_phased_formula attainmentPhases attainmentPhases_unit
    attainment_correlations_A attainment_correlations_B]
  simp only [phaseZ, attainment_z_zero, attainment_z_one, attainment_z_two,
    mul_zero, zero_mul, add_zero]
  have hi : (1 : ℝ) / Real.sqrt 3 = Real.sqrt 3 / 3 := fourierScale_eq_inv_sqrt.symm
  rw [hi]
  nlinarith [AttainmentScalars.skew_square]

lemma attaining_basisW :
    basisW QBasis.coordinate fourierBasis attainingBasis = (3 - Real.sqrt 3) / 18 := by
  have h := attaining_basisS
  change 6 * basisW QBasis.coordinate fourierBasis attainingBasis =
    1 - 1 / Real.sqrt 3 at h
  have hi : (1 : ℝ) / Real.sqrt 3 = Real.sqrt 3 / 3 := fourierScale_eq_inv_sqrt.symm
  rw [hi] at h
  linarith

/-- An actual unrestricted quaternionic MUB triple attains both native source
bounds. The quantified objects are the original QBasis, not phase certificates. -/
theorem triple_bound_attained :
    ∃ U V W : QBasis,
      U.MutuallyUnbiased V ∧ U.MutuallyUnbiased W ∧ V.MutuallyUnbiased W ∧
      basisS U V W = 1 - 1 / Real.sqrt 3 ∧
      basisW U V W = (3 - Real.sqrt 3) / 18 := by
  exact ⟨QBasis.coordinate, fourierBasis, attainingBasis,
    coordinate_fourier_mutuallyUnbiased, coordinate_attaining_mutuallyUnbiased,
    fourier_attaining_mutuallyUnbiased, attaining_basisS, attaining_basisW⟩

end QuaternionicMUB
