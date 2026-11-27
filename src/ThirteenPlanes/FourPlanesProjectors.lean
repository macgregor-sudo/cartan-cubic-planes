/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritMutuallyUnbiasedBases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Ordered projector trace for the marked share in the plane-share energy formula (c).
The Fourier bases and projections are from the Apache-2.0 package
`albert-sequential-measurements` v2.0.0, commit 10e5ca8ce341a1cb3a812569d3081005a40007c8,
`src/QutritFourierBases.lean` and `src/QutritMutuallyUnbiasedBases.lean`. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open AlbertSequential

theorem qutritRoot_eq :
    qutritRoot = (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2 := by
  apply Complex.ext <;> norm_num [qutritRoot, Complex.div_re, Complex.div_im]

private theorem star_qutritRoot_sq : star qutritRoot * star qutritRoot = qutritRoot := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext <;>
    norm_num [qutritRoot, Complex.star_def, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem markedBasisVector_first :
    qutritBasisVector 0 0 = ![(1 : ℂ), 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem markedBasisVector_second :
    qutritBasisVector 1 0 = fun i => (Real.sqrt (1 / 3) : ℂ) * ![(1 : ℂ), 1, 1] i := by
  change qutritFourierVector (qutritCharacter 0) 0 = _
  funext i
  fin_cases i <;> simp [qutritFourierVector, qutritRawFourierVector, qutritCharacter]

theorem markedBasisVector_third :
    qutritBasisVector 3 1 = fun i => (Real.sqrt (1 / 3) : ℂ) * ![(1 : ℂ), 1, qutritRoot] i := by
  have hunit : star qutritRoot * qutritRoot = 1 := qutritCharacter_unit 1
  change qutritFourierVector (qutritCharacter 2) 1 = _
  funext i
  fin_cases i <;> simp [qutritFourierVector, qutritRawFourierVector, qutritCharacter]
  · exact hunit
  · exact star_qutritRoot_sq

private theorem rankOneProjection_trace_pair (v w : Fin 3 → ℂ) :
    Matrix.trace (qutritRankOneProjection v * qutritRankOneProjection w) =
      qutritInner v w * qutritInner w v := by
  simp only [Matrix.trace, Matrix.diag_apply, qutritRankOneProjection_mul_apply]
  change _ = qutritInner v w * ∑ i, star (w i) * v i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem qutritProjection_pairTrace (k l : Fin 4) (b c : Fin 3) :
    Matrix.trace (qutritMUBProjection k b * qutritMUBProjection l c) =
      if k = l then (if b = c then 1 else 0) else (1 / 3 : ℂ) := by
  rw [qutritMUBProjection, qutritMUBProjection, rankOneProjection_trace_pair,
    ← qutritInner_star (qutritBasisVector k b) (qutritBasisVector l c)]
  by_cases hkl : k = l
  · subst l
    rw [qutritBasisVector_orthonormal]
    by_cases hbc : b = c <;> simp [hbc]
  · rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      qutritBasisVector_unbiased k l hkl b c]
    norm_num [hkl]

private theorem rankOneProjection_trace_triple (v w u : Fin 3 → ℂ) :
    Matrix.trace (qutritRankOneProjection v * qutritRankOneProjection w *
      qutritRankOneProjection u) = qutritInner v w * qutritInner w u * qutritInner u v := by
  have hentry (i j : Fin 3) :
      (qutritRankOneProjection v * qutritRankOneProjection w * qutritRankOneProjection u) i j =
        v i * qutritInner v w * qutritInner w u * star (u j) := by
    change ∑ x, (qutritRankOneProjection v * qutritRankOneProjection w) i x *
      (u x * star (u j)) = _
    simp only [qutritRankOneProjection_mul_apply]
    change _ = v i * qutritInner v w * (∑ k, star (w k) * u k) * star (u j)
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [Matrix.trace, Matrix.diag_apply, hentry]
  change _ = qutritInner v w * qutritInner w u * ∑ i, star (u i) * v i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem markedBasis_inner_second_third :
    qutritInner (qutritBasisVector 1 0) (qutritBasisVector 3 1) =
      (2 + qutritRoot) / 3 := by
  rw [markedBasisVector_second, markedBasisVector_third, qutritInner_scale,
    qutritNormalization_square, qutritInner, Fin.sum_univ_three]
  simp
  ring

/-- The complex trace in the order of the paper's three rays. -/
theorem markedProjection_orderedTrace :
    Matrix.trace (qutritMUBProjection 0 0 * qutritMUBProjection 1 0 *
      qutritMUBProjection 3 1) = (2 + qutritRoot) / 9 := by
  have hv (k : Fin 4) (b : Fin 3) (h : k ≠ 0) :
      qutritBasisVector k b 0 = (Real.sqrt (1 / 3) : ℂ) := by
    revert h
    refine Fin.cases (fun h => (h rfl).elim) (fun a _ => ?_) k
    change qutritFourierVector (qutritCharacter a) b 0 = _
    simp [qutritFourierVector, qutritRawFourierVector]
  rw [qutritMUBProjection, qutritMUBProjection, qutritMUBProjection,
    rankOneProjection_trace_triple, markedBasis_inner_second_third]
  change qutritInner (qutritStandardVector 0) (qutritBasisVector 1 0) * _ *
    qutritInner (qutritBasisVector 3 1) (qutritStandardVector 0) = _
  rw [qutritStandardVector_inner_left,
    ← qutritInner_star (qutritStandardVector 0) (qutritBasisVector 3 1),
    qutritStandardVector_inner_left, hv 1 0 (by decide), hv 3 1 (by decide),
    Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (1 / 3) : ℝ) : ℂ) * (Real.sqrt (1 / 3) : ℂ) *
        ((2 + qutritRoot) / 3) := by ring
    _ = _ := by rw [qutritNormalization_square]; ring

theorem markedProjection_orderedTrace_re :
    (Matrix.trace (qutritMUBProjection 0 0 * qutritMUBProjection 1 0 *
      qutritMUBProjection 3 1)).re = 1 / 6 := by
  rw [markedProjection_orderedTrace]
  norm_num [qutritRoot, Complex.div_re]

end ThirteenPlanes
