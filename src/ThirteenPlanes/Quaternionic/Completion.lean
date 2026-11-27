module

public import ThirteenPlanes.Quaternionic.FrameDictionary
public import ThirteenPlanes.Quaternionic.Quartic

@[expose] public section

/-!
# Native spectral step in one-missing-frame completion

This module starts with the exact pair criterion supplied by the two-dimensional
complement: norm-one orthogonal traceless Hermitian X,Y with X²+Y²=(2/3)I.
It proves the literal matrix commutator vanishes, rather than assuming a common
quaternion eigenbasis. SixCompletion proves the six-frame geometric construction.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

/-- The square-sum complement criterion forces actual quaternion matrices to
commute. Constants are obtained from the universal quartic and its polarization. -/
lemma square_sum_pair_commutes (X Y : QMat)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (htX : rtrace X = 0) (htY : rtrace Y = 0)
    (hxx : traceForm X X = 1) (hyy : traceForm Y Y = 1)
    (hxy : traceForm X Y = 0)
    (hsq : X ^ 2 + Y ^ 2 = (2 / 3 : ℝ) • (1 : QMat)) : Commute X Y := by
  have hx2 : rtrace (X ^ 2) = 1 := by
    simpa only [pow_two, traceForm_eq_rtrace_mul] using hxx
  have hx4 : rtrace (X ^ 4) = 1 / 2 := by
    rw [traceless_quartic X hX htX, hx2]
    norm_num
  have hpow : X ^ 2 * X ^ 2 = X ^ 4 := by
    rw [← pow_add]
  have hc : rtrace (X ^ 2 * Y ^ 2) = 1 / 6 := by
    have h := congrArg (fun A : QMat => rtrace (X ^ 2 * A)) hsq
    simp only [mul_add, rtrace_add, mul_smul_comm, mul_one, rtrace_smul,
      hpow, hx4, hx2] at h
    linarith
  have hp := traceless_quartic_polarized X Y hX hY htX htY
  have hj : traceForm (jordan X Y) (jordan X Y) = 1 / 6 := by
    rw [hc, hxx, hyy, hxy] at hp
    linarith
  have hf : frobeniusSq (X * Y - Y * X) = 0 := by
    rw [commutator_frobeniusSq X Y hX hY, hc, hj]
    norm_num
  change X * Y = Y * X
  exact sub_eq_zero.mp ((frobeniusSq_eq_zero_iff _).mp hf)

lemma square_sum_pair_diagonalizes (X Y : QMat)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (htX : rtrace X = 0) (htY : rtrace Y = 0)
    (hxx : traceForm X X = 1) (hyy : traceForm Y Y = 1)
    (hxy : traceForm X Y = 0)
    (hsq : X ^ 2 + Y ^ 2 = (2 / 3 : ℝ) • (1 : QMat)) :
    ∃ U : QBasis, ∃ a b : Outcome → ℝ,
      U.matᴴ * X * U.mat = realDiagonal a ∧ U.matᴴ * Y * U.mat = realDiagonal b :=
  commuting_hermitian_simultaneous_diagonalization X Y hX hY
    (square_sum_pair_commutes X Y hX hY htX htY hxx hyy hxy hsq)

end QuaternionicMUB
