module

public import ThirteenPlanes.Quaternionic.FourierScale

@[expose] public section

/-!
# Small spectral expansion of the native Fourier overlap

The complex three-point transform is expanded before taking any quaternionic
norm. This keeps the native coordinate bridge linear and its two spectral norm
identities quadratic in six real variables each.
-/
noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

/-- The unnormalized complex Fourier transform in the fixed source convention. -/
def dft3 (a : Outcome → ℂ) (k : Outcome) : ℂ :=
  ![a 0 + a 1 + a 2,
    a 0 + a 1 * complexPhase 1 + a 2 * complexPhase 2,
    a 0 + a 1 * complexPhase 2 + a 2 * complexPhase 1] k

/-- The exact norm expansion uses the source's cyclic correlation orientation. -/
lemma dft3_normSq (a : Outcome → ℂ) (k : Outcome) :
    Complex.normSq (dft3 a k) =
      (∑ i, Complex.normSq (a i)) +
        2 * (Heron.correlation a * complexPhase k).re := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases k <;>
    simp [dft3, complexPhase, Heron.correlation, Fin.sum_univ_succ,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    ring_nf <;> norm_num [hs] <;> ring

/-- In p=a+bj, the two native overlap components have characters c-b and -c-b.
No norms are expanded in this bridge; all four coordinate equations are linear. -/
lemma unscaled_fourier_overlap_components (p : Outcome → Q) (b c : Outcome) :
    qInner (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c) =
      (⟨(dft3 (phaseA p) (fourierDifference b c)).re,
        (dft3 (phaseA p) (fourierDifference b c)).im,
        (dft3 (phaseB p) (fourierNegativeSum b c)).re,
        (dft3 (phaseB p) (fourierNegativeSum b c)).im⟩ : Q) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases b <;> fin_cases c <;>
    ext <;>
    simp [qInner, unscaledFourierColumn, unscaledPhasedFourierColumn,
      fourierPhaseMatrix, omega, dft3, phaseA, phaseB, complexPhase,
      fourierDifference, fourierNegativeSum, Fin.sum_univ_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [hs] <;> ring

lemma unscaled_fourier_overlap_norm (p : Outcome → Q) (b c : Outcome) :
    Quaternion.normSq
      (qInner (unscaledFourierColumn b) (unscaledPhasedFourierColumn p c)) =
      Complex.normSq (dft3 (phaseA p) (fourierDifference b c)) +
        Complex.normSq (dft3 (phaseB p) (fourierNegativeSum b c)) := by
  rw [unscaled_fourier_overlap_components]
  simp only [Quaternion.normSq_def', Complex.normSq_apply]
  ring

/-- All nine literal native overlap entries, with the common scale restored.
No unit-phase hypothesis is needed for this polynomial identity. -/
theorem fourier_overlap_entry (p : Outcome → Q) (b c : Outcome) :
    Quaternion.normSq (qInner (fourierBasis.column b) (phasedFourierColumn p c)) =
      ((∑ i, Quaternion.normSq (p i)) +
        2 * mixedFourierRe (Heron.correlation (phaseA p))
          (Heron.correlation (phaseB p)) b c) / 9 := by
  rw [fourier_overlap_norm_scale, unscaled_fourier_overlap_norm,
    dft3_normSq, dft3_normSq]
  have hsum : (∑ i, Complex.normSq (phaseA p i)) +
      (∑ i, Complex.normSq (phaseB p i)) = ∑ i, Quaternion.normSq (p i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact phase_normSq_split p i
  simp only [mixedFourierRe, Complex.add_re]
  rw [show (∑ i, Complex.normSq (phaseA p i)) +
      2 * (Heron.correlation (phaseA p) * complexPhase (fourierDifference b c)).re +
      ((∑ i, Complex.normSq (phaseB p i)) +
      2 * (Heron.correlation (phaseB p) * complexPhase (fourierNegativeSum b c)).re) =
      ((∑ i, Complex.normSq (phaseA p i)) + (∑ i, Complex.normSq (phaseB p i))) +
      2 * ((Heron.correlation (phaseA p) * complexPhase (fourierDifference b c)).re +
        (Heron.correlation (phaseB p) * complexPhase (fourierNegativeSum b c)).re) by ring,
    hsum]

end QuaternionicMUB
