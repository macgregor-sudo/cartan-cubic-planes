module

public import ThirteenPlanes.Cartan.ComplexUnitary
public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

set_option backward.privateInPublic true

/-! The scalar commutant in the actual complex traceless representation. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators Matrix RealInnerProductSpace
open RoundCubics

noncomputable section

private abbrev V := complexJordan.traceFree

private def tracelessDiagonal (d : Fin 3 → ℝ) (hs : ∑ i, d i = 0) : V :=
  ⟨ofFullMatrix (Matrix.diagonal (fun i => (d i : ℂ))) (by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]), by
    change complexJordan.trace _ = 0
    rw [complexJordan_trace]
    change (Matrix.trace (Matrix.diagonal fun i => (d i : ℂ))).re = 0
    rw [Matrix.trace_diagonal]
    simpa only [Complex.re_sum, Complex.ofReal_re] using hs⟩

@[simp] private theorem tracelessDiagonal_matrix (d : Fin 3 → ℝ) (hs : ∑ i, d i = 0) :
    fullMatrix (tracelessDiagonal d hs).val = Matrix.diagonal (fun i => (d i : ℂ)) :=
  fullMatrix_ofFullMatrix _ _

private def signUnitary (i : Fin 3) : ComplexUnitary3 := by
  let d (j : Fin 3) : ℂ := if i = j then -1 else 1
  refine ⟨Matrix.diagonal d, Matrix.diagonal_mem_unitary.mpr ?_⟩
  constructor <;> funext j <;> by_cases h : i = j <;> simp [d, h, Pi.star_def]

private theorem signUnitary_action_apply (i a b : Fin 3) (X : ComplexMatrix3) :
    complexMatrixAd (signUnitary i) X a b =
      (if i = a then -1 else 1) * X a b * (if i = b then -1 else 1) := by
  rw [complexMatrixAd_apply]
  let d (j : Fin 3) : ℂ := if i = j then -1 else 1
  change ((Matrix.diagonal d * X * (Matrix.diagonal d)ᴴ : ComplexMatrix3) a b) = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = b <;> simp [d, h]

private def permutationUnitary (σ : Equiv.Perm (Fin 3)) : ComplexUnitary3 := by
  refine ⟨σ.permMatrix ℂ, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, Matrix.permMatrix_one]

private theorem permutationUnitary_action_diag (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → ℂ) :
    complexMatrixAd (permutationUnitary σ) (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d (σ i)) := by
  rw [complexMatrixAd_apply]
  change (σ.permMatrix ℂ) * Matrix.diagonal d * (σ.permMatrix ℂ)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  exact Matrix.submatrix_diagonal_equiv d σ

private def d01 : Fin 3 → ℝ := ![1, -1, 0]
private def d02 : Fin 3 → ℝ := ![1, 0, -1]
private def D01 : V := tracelessDiagonal d01 (by norm_num [d01, Fin.sum_univ_three])
private def D02 : V := tracelessDiagonal d02 (by norm_num [d02, Fin.sum_univ_three])

private theorem unitary_action_neg_D01 :
    (complexUnitaryAction (permutationUnitary (Equiv.swap (0 : Fin 3) 1))).traceAction complexJordan D01 = -D01 := by
  apply Subtype.ext
  apply fullMatrix_injective
  change complexMatrixAd (permutationUnitary (Equiv.swap (0 : Fin 3) 1)) (fullMatrix D01.val) =
    -fullMatrix D01.val
  rw [show fullMatrix D01.val = Matrix.diagonal (fun i => (d01 i : ℂ)) from tracelessDiagonal_matrix _ _,
    permutationUnitary_action_diag, Matrix.diagonal_neg]
  congr 1
  funext i
  fin_cases i <;> norm_num [d01, Equiv.swap_apply_def]

private theorem unitary_action_D01_to_D02 :
    (complexUnitaryAction (permutationUnitary (Equiv.swap (1 : Fin 3) 2))).traceAction complexJordan D01 = D02 := by
  apply Subtype.ext
  apply fullMatrix_injective
  change complexMatrixAd (permutationUnitary (Equiv.swap (1 : Fin 3) 2)) (fullMatrix D01.val) = fullMatrix D02.val
  rw [show fullMatrix D01.val = Matrix.diagonal (fun i => (d01 i : ℂ)) from tracelessDiagonal_matrix _ _,
    show fullMatrix D02.val = Matrix.diagonal (fun i => (d02 i : ℂ)) from tracelessDiagonal_matrix _ _,
    permutationUnitary_action_diag]
  congr 1
  funext i
  fin_cases i <;> norm_num [d01, d02, Equiv.swap_apply_def]

private theorem matrix_diagonal_of_offdiag_zero (X : ComplexMatrix3) (h : ∀ i j, i ≠ j → X i j = 0) :
    X = Matrix.diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

private theorem commuting_preserves_diag (S : Module.End ℝ V)
    (hS : ∀ U : ComplexUnitary3, ∀ x, S ((complexUnitaryAction U).traceAction complexJordan x) =
      (complexUnitaryAction U).traceAction complexJordan (S x))
    (x : V) (hx : ∀ i j, i ≠ j → fullMatrix x.val i j = 0) :
    ∀ i j, i ≠ j → fullMatrix (S x).val i j = 0 := by
  have hf (i : Fin 3) : (complexUnitaryAction (signUnitary i)).traceAction complexJordan x = x := by
    apply Subtype.ext
    apply fullMatrix_injective
    rw [complexUnitaryAction_trace_matrix]
    ext a b
    rw [signUnitary_action_apply]
    by_cases hab : a = b
    · subst b
      by_cases hai : i = a <;> simp [hai]
    · simp [hx a b hab]
  intro i j hij
  have h := hS (signUnitary i) x
  rw [hf] at h
  have he := congrArg (fun y : V => fullMatrix y.val i j) h
  change fullMatrix (S x).val i j = complexMatrixAd (signUnitary i) (fullMatrix (S x).val) i j at he
  rw [signUnitary_action_apply] at he
  simp [hij] at he
  linear_combination he / 2

private theorem complex_diag_spanned (x : V) (hx : ∀ i j, i ≠ j → fullMatrix x.val i j = 0) :
    x = (-(fullMatrix x.val 1 1).re) • D01 + (-(fullMatrix x.val 2 2).re) • D02 := by
  let X := fullMatrix x.val
  have hreal (i : Fin 3) : X i i = ((X i i).re : ℂ) := by
    have h := congrFun (congrFun (fullMatrix_hermitian x.val).eq i) i
    have hi : (X i i).im = 0 := by
      change star (X i i) = X i i at h
      have he := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at he
      linarith
    exact Complex.ext rfl (by simp [hi])
  have ht : Matrix.trace X = 0 := by
    rw [hermitian_trace_eq_real (fullMatrix_hermitian x.val)]
    have h := x.property
    change complexJordan.trace x.val = 0 at h
    rw [complexJordan_trace] at h
    change (↑(Matrix.trace (fullMatrix x.val)).re : ℂ) = 0
    simp [h]
  have hsum : (X 0 0).re + (X 1 1).re + (X 2 2).re = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Complex.add_re] using congrArg Complex.re ht
  apply Subtype.ext
  apply fullMatrix_injective
  change X = fullMatrix ((-(X 1 1).re) • D01.val + (-(X 2 2).re) • D02.val)
  rw [map_add, map_smul, map_smul,
    show fullMatrix D01.val = Matrix.diagonal (fun i => (d01 i : ℂ)) from tracelessDiagonal_matrix _ _,
    show fullMatrix D02.val = Matrix.diagonal (fun i => (d02 i : ℂ)) from tracelessDiagonal_matrix _ _]
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext
    · fin_cases i <;> simp [d01, d02, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      linarith
    · have hi := congrArg Complex.im (hreal i)
      rw [Complex.ofReal_im] at hi
      simp [hi, d01, d02, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Complex.mul_im]
  · simp [X, hx i j hij, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij]

private theorem scalar_on_diagonal (S : Module.End ℝ V)
    (hS : ∀ U : ComplexUnitary3, ∀ x, S ((complexUnitaryAction U).traceAction complexJordan x) =
      (complexUnitaryAction U).traceAction complexJordan (S x)) :
    ∃ a : ℝ, ∀ x : V, (∀ i j, i ≠ j → fullMatrix x.val i j = 0) → S x = a • x := by
  have hx : ∀ i j, i ≠ j → fullMatrix D01.val i j = 0 := by
    intro i j hij
    rw [show fullMatrix D01.val = Matrix.diagonal (fun i => (d01 i : ℂ)) from tracelessDiagonal_matrix _ _,
      Matrix.diagonal_apply_ne _ hij]
  let X := fullMatrix (S D01).val
  have hX := matrix_diagonal_of_offdiag_zero X (commuting_preserves_diag S hS D01 hx)
  have hneg := hS (permutationUnitary (Equiv.swap (0 : Fin 3) 1)) D01
  rw [unitary_action_neg_D01, map_neg] at hneg
  have he := congrArg (fun y : V => fullMatrix y.val 2 2) hneg
  change -X 2 2 = complexMatrixAd (permutationUnitary (Equiv.swap (0 : Fin 3) 1)) X 2 2 at he
  conv_rhs at he => rw [hX, permutationUnitary_action_diag]
  have hz : X 2 2 = 0 := by
    simp [Equiv.swap_apply_def] at he
    linear_combination -he / 2
  let a := -(X 1 1).re
  have h01 : S D01 = a • D01 := by
    have h := complex_diag_spanned (S D01) (commuting_preserves_diag S hS D01 hx)
    change S D01 = a • D01 + (-(X 2 2).re) • D02 at h
    simpa [hz] using h
  have h02 : S D02 = a • D02 := by
    have h := hS (permutationUnitary (Equiv.swap (1 : Fin 3) 2)) D01
    rw [unitary_action_D01_to_D02, h01, map_smul, unitary_action_D01_to_D02] at h
    exact h
  refine ⟨a, fun x hx => ?_⟩
  rw [complex_diag_spanned x hx, map_add, map_smul, map_smul, h01, h02, smul_add,
    smul_comm _ a, smul_comm _ a]

/-- Every traceless complex Hermitian element is a unitary conjugate of a real diagonal one. -/
theorem complex_unitary_diagonal_orbit (x : V) :
    ∃ U : ComplexUnitary3, ∃ y : V, (∀ i j, i ≠ j → fullMatrix y.val i j = 0) ∧
      x = (complexUnitaryAction U).traceAction complexJordan y := by
  let X := fullMatrix x.val
  have hX : X.IsHermitian := fullMatrix_hermitian x.val
  let d := hX.eigenvalues
  let U := hX.eigenvectorUnitary
  have hspec : X = complexMatrixAd U (Matrix.diagonal (fun i => (d i : ℂ))) := hX.spectral_theorem
  have ht : Matrix.trace X = 0 := by
    rw [hermitian_trace_eq_real hX]
    have h := x.property
    change complexJordan.trace x.val = 0 at h
    rw [complexJordan_trace] at h
    change (↑(Matrix.trace (fullMatrix x.val)).re : ℂ) = 0
    simp [h]
  have hd : ∑ i, d i = 0 := by
    rw [hspec, complexMatrixAd_preserves_trace, Matrix.trace_diagonal] at ht
    simpa only [Complex.re_sum, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re ht
  refine ⟨U, tracelessDiagonal d hd, ?_, ?_⟩
  · intro i j hij
    simp [hij, Matrix.diagonal_apply_ne]
  · apply Subtype.ext
    apply fullMatrix_injective
    rw [complexUnitaryAction_trace_matrix, tracelessDiagonal_matrix]
    exact hspec

/-- The commutant of the actual special-unitary traceless action consists of real scalars. -/
theorem complex_scalar_commutant (S : Module.End ℝ complexJordan.traceFree)
    (hS : ∀ U : ComplexSpecialUnitary3, ∀ x,
      S ((complexSU3Action U).traceAction complexJordan x) =
        (complexSU3Action U).traceAction complexJordan (S x)) :
    ∃ a : ℝ, S = a • LinearMap.id := by
  have hU (U : ComplexUnitary3) (x : V) : S ((complexUnitaryAction U).traceAction complexJordan x) =
      (complexUnitaryAction U).traceAction complexJordan (S x) := by
    obtain ⟨W, hW⟩ := complexUnitary_exists_SU3_sameAction U
    have h (y : V) : (complexSU3Action W).traceAction complexJordan y =
        (complexUnitaryAction U).traceAction complexJordan y := Subtype.ext (hW y.val)
    rw [← h x, ← h (S x)]
    exact hS W x
  obtain ⟨a, ha⟩ := scalar_on_diagonal S hU
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  obtain ⟨U, y, hy, hxy⟩ := complex_unitary_diagonal_orbit x
  change S x = a • x
  rw [hxy, hU, ha y hy, map_smul]

end

end ThirteenPlanes.Cartan
