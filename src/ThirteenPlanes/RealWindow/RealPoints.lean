module

public import ThirteenPlanes.Peirce.SlotRealModel
public import ThirteenPlanes.FourPlanesProjectors
public import ThirteenPlanes.JordanFrames.ComplexDiagonalization

@[expose] public section

set_option backward.privateInPublic true

/-! A real Cartan frame and a real rank-one point unbiased to that frame. -/

open scoped Matrix RealInnerProductSpace ComplexOrder

namespace ThirteenPlanes.ClosedBlocks

open Peirce AlbertSequential

noncomputable section

private theorem realTrace_toMatrix (x : RealTracelessSymmetric3) :
    x.val.toMatrix = (realTraceMatrix x).map Complex.ofReal := by
  obtain ⟨⟨a,b,p,q,r⟩, rfl⟩ := realCartanEquiv.surjective x
  unfold realTraceMatrix
  apply Matrix.ext
  intro i j
  change complexCartanMatrix a b p q r i j = (((complexCartanMatrix a b p q r i j).re : ℝ) : ℂ)
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul]

private theorem realTrace_toMatrix_injective :
    Function.Injective (fun x : RealTracelessSymmetric3 => x.val.toMatrix) :=
  TracelessHermitian3.toMatrix_injective.comp Subtype.val_injective

private def realPartMatrix (A : ComplexMatrix3) : RealMatrix3 := A.map Complex.re

private theorem realTrace_exists_of_real {A : ComplexMatrix3} (hA : A.IsHermitian)
    (ht : Matrix.trace A = 0) (him : ∀ i j, (A i j).im = 0) :
    ∃ x : RealTracelessSymmetric3, x.val.toMatrix = A := by
  let B := realPartMatrix A
  have hs : Bᵀ = B := by
    apply Matrix.ext
    intro i j
    change (A j i).re = (A i j).re
    have hh := congrArg (fun X : ComplexMatrix3 => (X i j).re) hA.eq
    change (star (A j i)).re = (A i j).re at hh
    simpa only [Complex.star_def, Complex.conj_re] using hh
  have htr : Matrix.trace B = 0 := by
    change ∑ i, Complex.reAddGroupHom (A i i) = 0
    simpa only [Matrix.trace, Matrix.diag_apply, map_sum, map_zero] using congrArg Complex.reAddGroupHom ht
  obtain ⟨x, hx⟩ := (realTraceMatrix_range B).mpr ⟨hs, htr⟩
  refine ⟨x, ?_⟩
  rw [realTrace_toMatrix, hx]
  apply Matrix.ext
  intro i j
  exact Complex.ext rfl (him i j).symm

private def projectionScale : ℂ := (Real.sqrt 6 : ℂ) / 2

private theorem projectionScale_square : projectionScale * projectionScale = 3 / 2 := by
  have hs : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  dsimp [projectionScale]
  linear_combination hs / 4

private theorem projectionScale_star : star projectionScale = projectionScale := by
  simp [projectionScale]

private theorem matrix_one_im (i j : Fin 3) : ((1 : ComplexMatrix3) i j).im = 0 := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem center_unit_projection_exists {P : ComplexMatrix3} (herm : P.IsHermitian)
    (idempotent : P * P = P) (trace : Matrix.trace P = 1) (real : ∀ i j, (P i j).im = 0) :
    ∃ x : RealTracelessSymmetric3, IsUnitIdempotent realCartanCubic x ∧
      x.val.toMatrix = projectionScale • traceFreePart P := by
  let A := projectionScale • traceFreePart P
  have hah : A.IsHermitian := (traceFreePart_hermitian herm).smul projectionScale_star
  have hat : Matrix.trace A = 0 := by
    simp [A, Matrix.trace_smul, trace_traceFreePart]
  have hai (i j : Fin 3) : (A i j).im = 0 := by
    simp [A, traceFreePart, trace, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Complex.mul_im, Complex.sub_im, real, matrix_one_im, projectionScale]
  obtain ⟨x, hx⟩ := realTrace_exists_of_real hah hat hai
  have sqbase : (P - (1 / 3 : ℂ) • (1 : ComplexMatrix3)) * (P - (1 / 3 : ℂ) • (1 : ComplexMatrix3)) =
      (1 / 3 : ℂ) • P + (1 / 9 : ℂ) • (1 : ComplexMatrix3) := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, idempotent, smul_smul]
    module
  have hsq : A * A = (1 / 2 : ℂ) • P + (1 / 6 : ℂ) • (1 : ComplexMatrix3) := by
    dsimp only [A]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, projectionScale_square, traceFreePart, trace, sqbase]
    module
  have htr : Matrix.trace (A * A) = 1 := by
    rw [hsq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace, trace_one_matrix3]
    norm_num [smul_eq_mul]
  have hcx : complexCartanCubic.L x.val x.val = x.val := by
    apply TracelessHermitian3.toMatrix_injective
    rw [complexCartanCubic, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    change (Real.sqrt 6 : ℂ) • (TracelessHermitian3.jordan x.val x.val).toMatrix = _
    rw [TracelessHermitian3.toMatrix_jordan, symmetricMatrixProduct_self, hx, traceFreePart, htr,
      hsq, show A = projectionScale • (P - (1 / 3 : ℂ) • (1 : ComplexMatrix3)) by
        dsimp only [A]
        rw [traceFreePart, trace]]
    dsimp [projectionScale]
    module
  have hn : ‖x‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    change ‖x.val‖ ^ 2 = 1 ^ 2
    rw [← real_inner_self_eq_norm_sq, TracelessHermitian3.inner_eq_tracePairing, hx]
    change (Matrix.trace (A * A)).re = _
    rw [htr]
    norm_num
  refine ⟨x, ⟨hn, ?_⟩, hx⟩
  apply ext_inner_right ℝ
  intro y
  change (complexCartanCubic.pullback realTraceSubmodule.subtype).apply x x y = ⟪x.val, y.val⟫
  rw [SymmetricCubic.pullback_apply]
  change ⟪complexCartanCubic.L x.val x.val, y.val⟫ = _
  rw [hcx]

private theorem diag_real (i a b : Fin 3) : (qutritMUBProjection 0 i a b).im = 0 := by
  rw [JordanFrames.standardComplexPoint_diagonal]
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, Pi.single_apply]
    split <;> norm_num
  · simp [Matrix.diagonal_apply_ne _ hab]

private theorem flat_real (a b : Fin 3) : (qutritMUBProjection 1 0 a b).im = 0 := by
  change ((qutritBasisVector 1 0 a) * star (qutritBasisVector 1 0 b)).im = _
  rw [markedBasisVector_second]
  fin_cases a <;> fin_cases b <;> simp [Complex.mul_im]

private theorem normalizedProjection_inner {x y : RealTracelessSymmetric3} {P Q : ComplexMatrix3}
    (hP : Matrix.trace P = 1) (hQ : Matrix.trace Q = 1)
    (hx : x.val.toMatrix = projectionScale • traceFreePart P)
    (hy : y.val.toMatrix = projectionScale • traceFreePart Q)
    (hPQ : Matrix.trace (P * Q) = 1 / 3) : ⟪x, y⟫ = 0 := by
  change ⟪x.val, y.val⟫ = _
  rw [TracelessHermitian3.inner_eq_tracePairing, hx, hy]
  change (Matrix.trace ((projectionScale • traceFreePart P) * (projectionScale • traceFreePart Q))).re = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  have h : Matrix.trace (traceFreePart P * traceFreePart Q) = 0 := by
    simp only [traceFreePart, hP, hQ, sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, hPQ, trace_one_matrix3, smul_eq_mul]
    ring
  rw [h]
  simp

/-- The real symmetric Cartan carrier has its diagonal rank-one frame and the centered
all-ones projector, orthogonal to the three frame directions. -/
theorem realCartan_has_flat_frame :
    ∃ (a : Fin 3 → RealTracelessSymmetric3) (b : RealTracelessSymmetric3),
      (∀ i, IsUnitIdempotent realCartanCubic (a i)) ∧ ∑ i, a i = 0 ∧
        IsUnitIdempotent realCartanCubic b ∧ ∀ i, ⟪a i, b⟫ = 0 := by
  have h (i : Fin 3) := center_unit_projection_exists (qutritMUBProjection_positive 0 i).isHermitian
    (qutritMUBProjection_idempotent 0 i) (qutritMUBProjection_trace 0 i) (diag_real i)
  choose a ha using h
  obtain ⟨b, hb, hB⟩ := center_unit_projection_exists (qutritMUBProjection_positive 1 0).isHermitian
    (qutritMUBProjection_idempotent 1 0) (qutritMUBProjection_trace 1 0) flat_real
  refine ⟨a, b, fun i => (ha i).1, ?_, hb, fun i => ?_⟩
  · apply realTrace_toMatrix_injective
    change (TracelessHermitian3.toMatrix ((∑ i, a i : RealTracelessSymmetric3) : TracelessHermitian3)) = _
    simp only [Submodule.coe_sum, map_sum, (ha _).2]
    rw [← Finset.smul_sum, Fin.sum_univ_three, ← traceFreePart_add, ← traceFreePart_add,
      ← Fin.sum_univ_three, qutritMUBProjection_sum]
    simp [traceFreePart]
  · apply normalizedProjection_inner (qutritMUBProjection_trace 0 i) (qutritMUBProjection_trace 1 0)
      (ha i).2 hB
    rw [qutritProjection_pairTrace]
    norm_num

end

end ThirteenPlanes.ClosedBlocks
