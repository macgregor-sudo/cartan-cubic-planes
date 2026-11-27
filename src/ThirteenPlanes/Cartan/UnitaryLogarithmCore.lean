module

public import ThirteenPlanes.Cartan.ComplexCasimir
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

set_option backward.privateInPublic true

/-! Corrected diagonal logarithms and unitary covariance of the matrix exponential. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators Matrix
open NormedSpace RoundCubics

noncomputable section

/-- A determinant-one unitary diagonal matrix has a traceless skew logarithm. -/
theorem diagonal_unitary_corrected_log (d : Fin 3 → ℂ)
    (hunitary : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hdet : ∏ i, d i = 1) :
    ∃ A : complexSkewTracelessMatrices, exp A.val = Matrix.diagonal d := by
  have hu := Matrix.diagonal_mem_unitary.mp hunitary
  have hun (i : Fin 3) : ‖d i‖ = 1 := CStarRing.norm_of_mem_unitary
    (show d i ∈ unitary ℂ from ⟨congrFun hu.1 i, congrFun hu.2 i⟩)
  have hn (i : Fin 3) : d i ≠ 0 := norm_ne_zero_iff.mp (by rw [hun]; norm_num)
  let l (i : Fin 3) := Complex.log (d i)
  have hl (i : Fin 3) : (l i).re = 0 := by rw [show (l i).re = Real.log ‖d i‖ from Complex.log_re _, hun, Real.log_one]
  have he (i : Fin 3) : Complex.exp (l i) = d i := Complex.exp_log (hn i)
  let s := ∑ i, l i
  have hs : Complex.exp s = 1 := by
    change Complex.exp (∑ i, l i) = 1
    rw [Complex.exp_sum]
    simp only [he, hdet]
  have hir : s.re = 0 := by simp [s, Complex.re_sum, hl]
  let a (i : Fin 3) := if i = 0 then l i - s else l i
  have har (i : Fin 3) : (a i).re = 0 := by by_cases hi : i = 0 <;> simp [a, hi, hl, hir]
  have ha : ∑ i, a i = 0 := by
    simp [a, s, Fin.sum_univ_three]
    ring
  have hae (i : Fin 3) : Complex.exp (a i) = d i := by
    by_cases hi : i = 0
    · simp [a, hi, Complex.exp_sub, he, hs]
    · simp [a, hi, he]
  let A : complexSkewTracelessMatrices := ⟨Matrix.diagonal a, by
    change (Matrix.diagonal a)ᴴ = -Matrix.diagonal a ∧ Matrix.trace (Matrix.diagonal a) = 0
    constructor
    · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
      congr 1
      funext i
      apply Complex.ext <;> simp [har i]
    · rw [Matrix.trace_diagonal, ha]⟩
  refine ⟨A, ?_⟩
  change exp (Matrix.diagonal a) = Matrix.diagonal d
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  exact hae i

/-- The finite matrix exponential commutes with unitary conjugation. -/
theorem complexMatrixAd_exp (U : ComplexUnitary3) (A : ComplexMatrix3) :
    exp (complexMatrixAd U A) = complexMatrixAd U (exp A) := by
  rw [complexMatrixAd_apply, complexMatrixAd_apply]
  exact Matrix.exp_units_conj (Unitary.toUnits U) A


private theorem centered_skew {A : ComplexMatrix3} (hA : Aᴴ = -A) :
    (traceFreePart A)ᴴ = -(traceFreePart A) := by
  have ht : star (Matrix.trace A) = -Matrix.trace A := by
    rw [← Matrix.trace_conjTranspose, hA, Matrix.trace_neg]
  unfold traceFreePart
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hA, star_div₀,
    ht, show star (3 : ℂ) = 3 by norm_num, neg_div, neg_smul, neg_sub]
  abel

private theorem centered_commute {A B : ComplexMatrix3} (h : Commute A B) :
    Commute (traceFreePart A) (traceFreePart B) := by
  have hA := h.sub_right ((Commute.one_right A).smul_right (Matrix.trace B / 3 : ℂ))
  exact hA.sub_left ((Commute.one_left (traceFreePart B)).smul_left (Matrix.trace A / 3 : ℂ))

private theorem complexMatrixAd_center (V : ComplexUnitary3) (A : ComplexMatrix3) :
    complexMatrixAd V (traceFreePart A) = traceFreePart (complexMatrixAd V A) := by
  rw [traceFreePart, traceFreePart, map_sub, map_smul, map_one, complexMatrixAd_preserves_trace]

section PairDiagonalization

variable (diagonalize : ∀ A : Fin 2 → complexSkewTracelessMatrices,
  (Pairwise fun i j => Commute (A i).val (A j).val) →
    ∃ V : ComplexSpecialUnitary3, ∀ i, ∃ a : Fin 3 → ℝ, (∑ k, a k = 0) ∧
      complexMatrixAd (⟨V.val, V.property.1⟩ : ComplexUnitary3) (A i).val =
        Matrix.diagonal (fun k => a k • Complex.I))

include diagonalize

private theorem specialUnitary_diagonalizes (U : ComplexSpecialUnitary3) :
    ∃ V : ComplexSpecialUnitary3, ∃ d : Fin 3 → ℂ,
      complexMatrixAd (⟨V.val, V.property.1⟩ : ComplexUnitary3) U.val = Matrix.diagonal d := by
  let M : ComplexMatrix3 := U.val
  let X := M - Mᴴ
  let Y := Complex.I • (M + Mᴴ)
  have hX : Xᴴ = -X := by
    simp only [X, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]
  have hY : Yᴴ = -Y := by
    simp only [Y, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I, neg_smul]
    rw [add_comm Mᴴ M]
  let A₀ : complexSkewTracelessMatrices := ⟨traceFreePart X, centered_skew hX, trace_traceFreePart _⟩
  let A₁ : complexSkewTracelessMatrices := ⟨traceFreePart Y, centered_skew hY, trace_traceFreePart _⟩
  have hcomm : Commute M Mᴴ := U.property.1.2.trans U.property.1.1.symm
  have hXY : Commute X Y := by
    have h := ((Commute.refl M).add_right hcomm).sub_left (hcomm.symm.add_right (Commute.refl Mᴴ))
    exact h.smul_right Complex.I
  let A : Fin 2 → complexSkewTracelessMatrices := ![A₀, A₁]
  have hA : Pairwise fun i j => Commute (A i).val (A j).val := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact centered_commute hXY
    · exact (centered_commute hXY).symm
    · exact (hij rfl).elim
  obtain ⟨V, hV⟩ := diagonalize A hA
  let W : ComplexUnitary3 := ⟨V.val, V.property.1⟩
  let B := complexMatrixAd W M
  let C := complexMatrixAd W Mᴴ
  have hz (i j : Fin 3) (hij : i ≠ j) : B i j = 0 := by
    obtain ⟨a, _, ha⟩ := hV 0
    obtain ⟨b, _, hb⟩ := hV 1
    change complexMatrixAd W (traceFreePart (M - Mᴴ)) = _ at ha
    change complexMatrixAd W (traceFreePart (Complex.I • (M + Mᴴ))) = _ at hb
    rw [complexMatrixAd_center, map_sub] at ha
    rw [complexMatrixAd_center, map_smul, map_add] at hb
    have ha' := congrArg (fun D : ComplexMatrix3 => D i j) ha
    have hb' := congrArg (fun D : ComplexMatrix3 => D i j) hb
    have hminus : B i j - C i j = 0 := by
      simpa [B, C, traceFreePart, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij] using ha'
    have hplus' : Complex.I * (B i j + C i j) = 0 := by
      simpa [B, C, traceFreePart, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, mul_add, hij] using hb'
    have hplus := (mul_eq_zero.mp hplus').resolve_left Complex.I_ne_zero
    linear_combination (hminus + hplus) / 2
  refine ⟨V, fun i => B i i, ?_⟩
  change B = Matrix.diagonal (fun i => B i i)
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij, hz i j hij]

/-- Every actual special unitary three-by-three matrix is the exponential of a traceless
skew-Hermitian matrix. Correcting one scalar logarithm by their sum keeps every exponential fixed. -/
theorem suThree_exists_traceless_skew_log_of_pair_diagonalization (U : ComplexSpecialUnitary3) :
    ∃ A : complexSkewTracelessMatrices, exp A.val = U.val := by
  obtain ⟨V, d, hV⟩ := specialUnitary_diagonalizes diagonalize U
  let W : ComplexUnitary3 := ⟨V.val, V.property.1⟩
  have hdU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [← hV, ← map_star, ← map_mul, U.property.1.2, map_one]
  have hdDet : ∏ i, d i = 1 := by
    rw [← Matrix.det_diagonal, ← hV, complexMatrixAd_apply, Matrix.det_mul, Matrix.det_mul]
    have hVdet : V.val.det = 1 := V.property.2
    have hVdet' : V.valᴴ.det = 1 := (star V).property.2
    rw [hVdet, hVdet', show U.val.det = 1 from U.property.2, mul_one, mul_one]
  obtain ⟨A, hA⟩ := diagonal_unitary_corrected_log d hdU hdDet
  refine ⟨complexConjugatedSkew (star W) A, ?_⟩
  change exp (complexMatrixAd (star W) A.val) = U.val
  rw [complexMatrixAd_exp, hA, ← hV, complexMatrixAd_inv]


end PairDiagonalization

end

end ThirteenPlanes.Cartan
