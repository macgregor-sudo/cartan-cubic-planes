/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.JordanFrames.AlbertNormal
public import ThirteenPlanes.AlbertGrading.Recognition.Main

@[expose] public section

set_option backward.privateInPublic true

/-! The checked native pair normalization supplies the hypothesis of the sparsest-system theorem. -/

namespace ThirteenPlanes.AlbertGrading

open JordanFrames

noncomputable section

private def phaseEntry (u : Glennie.Octonion) : Glennie.Octonion :=
  (-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u

private theorem phaseEntry_conj (u : Glennie.Octonion)
    (hu : Glennie.octRe u = 0) : Glennie.octConj (phaseEntry u) = phaseEntry (-u) := by
  have hc : Glennie.octConj u = -u := AlbertSequential.octonionConj_eq_neg_of_real_zero hu
  simp only [phaseEntry, Glennie.octConj_add, Glennie.octConj_smul, Glennie.octConj_scalar, hc]

private theorem scalar_eq_smul_one (r : ℝ) :
    Glennie.octScalar r = r • Glennie.octScalar 1 :=
  AlbertSequential.octonionScalar_eq_smul r

private theorem scaled_omega_zero (u : Glennie.Octonion) :
    (1 / 3 : ℝ) • omegaU u 0 = (1 / 3 : ℝ) • Glennie.octScalar 1 := by
  simp only [omegaU, chargePhase_zero, Complex.one_re, Complex.one_im, zero_smul, add_zero]
  rfl

private theorem scaled_omega_one (u : Glennie.Octonion) :
    (1 / 3 : ℝ) • omegaU u 1 = phaseEntry u := by
  rw [omegaU, cp1, chargeRoot_re, chargeRoot_im]
  change (1 / 3 : ℝ) • (Glennie.octScalar (-1 / 2) + (Real.sqrt 3 / 2) • u) = _
  rw [scalar_eq_smul_one]
  unfold phaseEntry
  module

private theorem scaled_omega_neg_one (u : Glennie.Octonion) :
    (1 / 3 : ℝ) • omegaU u (-1) = phaseEntry (-u) := by
  rw [omegaU, chargePhase_neg, cp1]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, chargeRoot_re, chargeRoot_im]
  change (1 / 3 : ℝ) • (Glennie.octScalar (-1 / 2) + -(Real.sqrt 3 / 2) • u) = _
  rw [scalar_eq_smul_one]
  unfold phaseEntry
  module

/-- The literal upper entries of the two Fourier frames agree with identical outcome labels. -/
theorem nativeFourierFrame_eq_fourierFrameU (u : Glennie.Octonion)
    (hu : Glennie.octRe u = 0) (k : Fin 3) :
    nativeFourierFrame u k = fourierFrameU u k := by
  have hneg : Glennie.octRe (-u) = 0 := by
    change -Glennie.octRe u = 0
    rw [hu, neg_zero]
  fin_cases k
  · change nativeFourierZero = fourierFrameU u 0
    apply Glennie.Albert.ext <;> simp only [nativeFourierZero, fourierFrameU, zero_mul, scaled_omega_zero]
  · change nativeFourierPhase (-u) =
      ⟨1 / 3, 1 / 3, 1 / 3, (1 / 3 : ℝ) • omegaU u (-1),
        (1 / 3 : ℝ) • omegaU u 1, (1 / 3 : ℝ) • omegaU u (-1)⟩
    rw [scaled_omega_neg_one, scaled_omega_one]
    change (⟨1 / 3, 1 / 3, 1 / 3, phaseEntry (-u), Glennie.octConj (phaseEntry (-u)),
      phaseEntry (-u)⟩ : Glennie.Albert) = _
    rw [phaseEntry_conj (-u) hneg, neg_neg]
  · change nativeFourierPhase u =
      ⟨1 / 3, 1 / 3, 1 / 3, (1 / 3 : ℝ) • omegaU u 1,
        (1 / 3 : ℝ) • omegaU u (-1), (1 / 3 : ℝ) • omegaU u 1⟩
    rw [scaled_omega_neg_one, scaled_omega_one]
    change (⟨1 / 3, 1 / 3, 1 / 3, phaseEntry u, Glennie.octConj (phaseEntry u),
      phaseEntry u⟩ : Glennie.Albert) = _
    rw [phaseEntry_conj u hu]

/-- Section 3 pair normalization on the exact diagonal and Fourier frame predicates of Section 5. -/
theorem nativeNormalFormOctonion : FrameProperties.NormalFormOctonion := by
  intro F G hF hG unbiased
  obtain ⟨φ, u, hu, hn, hP, hQ⟩ := native_normalize_unbiased_pair F G hF hG unbiased
  refine ⟨φ, u, hu, hn, congrArg Set.range (funext hP), congrArg Set.range (funext ?_)⟩
  intro k
  exact (hQ k).trans (nativeFourierFrame_eq_fourierFrameU u hu k)

/-- Sharp existence and orbit uniqueness of the thirteen-plane systems with 52 positive shares. -/
theorem nativeSparsest : Statements.Sparsest :=
  sparsest nativeNormalFormOctonion

end
end ThirteenPlanes.AlbertGrading
