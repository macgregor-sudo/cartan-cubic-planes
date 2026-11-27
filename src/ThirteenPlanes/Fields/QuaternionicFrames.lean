module

public import ThirteenPlanes.Peirce.FrameFormula
public import ThirteenPlanes.Quaternionic.NativeTraceModel

@[expose] public section

set_option backward.privateInPublic true

/-! The unit-idempotent formula on the quaternionic Hermitian carrier. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.Peirce

open QuaternionicMUB

noncomputable section

private theorem quaternion_full_product_matrix (x y : HermitianHilbert) :
    fullMat (quaternionFullCubic.L x y) = jordan (fullMat x) (fullMat y) :=
  fullMat_ofMatrix _ _

private theorem quaternion_innerUnit (x : HermitianHilbert) : ⟪fullUnit, x⟫ = rtrace (fullMat x) := by
  rw [hermitianHilbert_inner]
  change traceForm (fullMat fullUnit) (fullMat x) = _
  rw [fullMat_fullUnit, traceForm_eq_rtrace_mul, one_mul]

private theorem quaternion_inclusion_product (x y : TracelessHilbert) :
    quaternionFullCubic.L (traceInclusion x) (traceInclusion y) =
      traceInclusion (quaternionTraceCubic.L x y) + (⟪x,y⟫ / 3) • fullUnit := by
  apply fullMat_injective
  rw [quaternion_full_product_matrix, map_add, map_smul, fullMat_fullUnit, fullMat_traceInclusion,
    fullMat_traceInclusion, fullMat_traceInclusion, quaternionTraceCubic_L_matrix,
    tracelessHilbert_inner]
  change jordan (traceMat x) (traceMat y) = centerMatrix (jordan (traceMat x) (traceMat y)) +
    (rtrace (jordan (traceMat x) (traceMat y)) / 3) • (1 : QMat)
  rw [centerMatrix, sub_add_cancel]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Lemma 2b-frames, for the actual quaternionic Hermitian matrices. -/
theorem quaternionicFrame_of_three_unit_idempotents (h : SymmetricCubic V)
    (I : V →ₗᵢ[ℝ] TracelessHilbert)
    (product : ∀ x y, I (h.L x y) = Real.sqrt 6 • quaternionTraceCubic.L (I x) (I y))
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    ∃ F : Frame, ∀ i,
      F.point i = (1 / 3 : ℝ) • ((1 : QMat) + Real.sqrt 6 • traceMat (I (a i))) := by
  let J := traceInclusion.comp I
  have hrank : ⟪fullUnit, fullUnit⟫ = 3 := by rw [quaternion_innerUnit, fullMat_fullUnit, rtrace_one]
  have htrace (x : V) : ⟪fullUnit, J x⟫ = 0 := by
    rw [quaternion_innerUnit]
    exact traceMat_trace (I x)
  have hproduct (x y : V) : quaternionFullCubic.L (J x) (J y) =
      (Real.sqrt 6)⁻¹ • J (h.L x y) + (⟪x,y⟫ / 3) • fullUnit := by
    change quaternionFullCubic.L (traceInclusion (I x)) (traceInclusion (I y)) =
      (Real.sqrt 6)⁻¹ • traceInclusion (I (h.L x y)) + (⟪x,y⟫ / 3) • fullUnit
    rw [quaternion_inclusion_product, product, map_smul, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne', one_smul,
      LinearIsometry.inner_map_map (𝕜 := ℝ) I]
  let p (i : Fin 3) := framePoint J fullUnit (a i)
  have H := frame_of_three_unit_idempotents h quaternionFullCubic fullUnit J quaternionFullCubic_unit
    hrank htrace hproduct a ha hs
  refine ⟨⟨fun i => fullMat (p i), fun i => fullMat_hermitian (p i), ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    rw [← quaternion_innerUnit]
    exact H.trace_one i
  · intro i
    rw [← quaternion_full_product_matrix]
    exact congrArg fullMat (H.idempotent i)
  · intro i j hij
    rw [← quaternion_full_product_matrix, ← map_zero fullMat]
    exact congrArg fullMat (H.orthogonal i j hij)
  · rw [← map_sum, show (∑ i, p i) = fullUnit from H.sum_unit, fullMat_fullUnit]
  · intro i
    change fullMat ((1 / 3 : ℝ) • (fullUnit + Real.sqrt 6 • traceInclusion (I (a i)))) = _
    rw [map_smul, map_add, fullMat_fullUnit, map_smul, fullMat_traceInclusion]

/-- Orthogonal source vectors give quaternionic frame points with trace overlap one third. -/
theorem quaternionicFrame_formula_unbiased (I : V →ₗᵢ[ℝ] TracelessHilbert) {x y : V}
    (orth : ⟪x,y⟫ = 0) :
    traceForm ((1 / 3 : ℝ) • ((1 : QMat) + Real.sqrt 6 • traceMat (I x)))
      ((1 / 3 : ℝ) • ((1 : QMat) + Real.sqrt 6 • traceMat (I y))) = 1 / 3 := by
  let J := traceInclusion.comp I
  have hp (z : V) : fullMat (framePoint J fullUnit z) =
      (1 / 3 : ℝ) • ((1 : QMat) + Real.sqrt 6 • traceMat (I z)) := by
    change fullMat ((1 / 3 : ℝ) • (fullUnit + Real.sqrt 6 • traceInclusion (I z))) = _
    rw [map_smul, map_add, fullMat_fullUnit, map_smul, fullMat_traceInclusion]
  rw [← hp, ← hp]
  change traceForm _ _ = _
  have hrank : ⟪fullUnit, fullUnit⟫ = 3 := by rw [quaternion_innerUnit, fullMat_fullUnit, rtrace_one]
  have htrace (z : V) : ⟪fullUnit, J z⟫ = 0 := by
    rw [quaternion_innerUnit]
    exact traceMat_trace (I z)
  have hi := framePoint_inner_of_orthogonal J fullUnit hrank htrace orth
  rw [hermitianHilbert_inner] at hi
  exact hi

end

end ThirteenPlanes.Peirce
