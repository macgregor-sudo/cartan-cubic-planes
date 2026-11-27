module

public import ThirteenPlanes.Quaternionic.Transforms
public import ThirteenPlanes.Quaternionic.HadamardPhase

@[expose] public section

/-!
# Native order-three Hadamard matrices after dephasing

Unitarity and a constant first row and column determine the remaining four
entries from one quaternion. Equal entry norms supply precisely the two
unit-norm equations used by HadamardPhase.
-/

noncomputable section
open scoped BigOperators Matrix
namespace QuaternionicMUB

lemma fourierScale_ne_zero : fourierScale ≠ 0 := by
  dsimp [fourierScale]
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (by norm_num)

lemma sqrt_three_mul_fourierScale : Real.sqrt 3 * fourierScale = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [fourierScale]
  nlinarith

lemma dephased_row_sum (K : QBasis)
    (hr : ∀ j, K.mat 0 j = fourierScale • (1:Q))
    (i : Outcome) (hi : i ≠ 0) : ∑ j, K.mat i j = 0 := by
  have h := congrArg (fun A : QMat => A i 0) K.mul_adjoint
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hr,
    star_smul, star_trivial, star_one, mul_smul_comm, mul_one,
    ← Finset.smul_sum, Matrix.one_apply, if_neg hi] at h
  exact (smul_eq_zero.mp h).resolve_left fourierScale_ne_zero

lemma dephased_column_sum (K : QBasis)
    (hc : ∀ i, K.mat i 0 = fourierScale • (1:Q))
    (j : Outcome) (hj : j ≠ 0) : ∑ i, K.mat i j = 0 := by
  have h := congrArg (fun A : QMat => A 0 j) K.adjoint_mul
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hc,
    star_smul, star_trivial, star_one, smul_mul_assoc, one_mul,
    ← Finset.smul_sum, Matrix.one_apply, if_neg (Ne.symm hj)] at h
  exact (smul_eq_zero.mp h).resolve_left fourierScale_ne_zero

/-- The whole literal matrix has the one-phase block form. No entry permutation
or residual diagonalizer is part of the hypotheses. -/
theorem dephased_hadamard_shape (K : QBasis)
    (hr : ∀ j, K.mat 0 j = fourierScale • (1:Q))
    (hc : ∀ i, K.mat i 0 = fourierScale • (1:Q))
    (hn : ∀ i j, Quaternion.normSq (K.mat i j) = (1/3:ℝ)) :
    ∃ a : Q, Quaternion.normSq a = 1 ∧ Quaternion.normSq (-1-a) = 1 ∧
      K.mat = fourierScale • !![1,1,1; 1,a,-1-a; 1,-1-a,a] := by
  let t : Q := fourierScale • (1:Q)
  have h1 := dephased_row_sum K hr 1 (by decide)
  have h2 := dephased_row_sum K hr 2 (by decide)
  have hv := dephased_column_sum K hc 1 (by decide)
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.zero_eta,
    Fin.isValue, Fin.sum_univ_zero, add_zero] at h1 h2 hv
  have h12 : K.mat 1 2 = -(t + K.mat 1 1) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [t, ← add_assoc, hc] using h1
  have h21 : K.mat 2 1 = -(t + K.mat 1 1) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [t, ← add_assoc, hr] using hv
  have h22 : K.mat 2 2 = K.mat 1 1 := by
    have hz : K.mat 2 2 = -(t + K.mat 2 1) := by
      apply eq_neg_of_add_eq_zero_right
      simpa [t, ← add_assoc, hc] using h2
    rw [hz, h21]
    abel
  let a : Q := Real.sqrt 3 • K.mat 1 1
  have hsa : fourierScale • a = K.mat 1 1 := by
    dsimp [a]
    rw [smul_smul, mul_comm fourierScale, sqrt_three_mul_fourierScale, one_smul]
  have hsc : Real.sqrt 3 • K.mat 1 2 = -1-a := by
    rw [h12, smul_neg, smul_add]
    change -(Real.sqrt 3 • (fourierScale • (1:Q)) + a) = _
    rw [smul_smul, sqrt_three_mul_fourierScale, one_smul]
    abel
  have hsn : ∀ i j, Quaternion.normSq (Real.sqrt 3 • K.mat i j) = 1 := by
    intro i j
    rw [Quaternion.normSq_smul, Real.sq_sqrt (by norm_num), hn]
    norm_num
  refine ⟨a, hsn 1 1, ?_, ?_⟩
  · rw [← hsc]
    exact hsn 1 2
  · have hsminus : fourierScale • (-1-a) = -(t+K.mat 1 1) := by
      rw [show (-1-a:Q) = -(1+a) by abel, smul_neg, smul_add, hsa]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, hr, hc, hsa, hsminus, h12, h21, h22, t]

end QuaternionicMUB
