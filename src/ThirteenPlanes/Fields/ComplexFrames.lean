module

public import ThirteenPlanes.Peirce.FrameFormula
public import ThirteenPlanes.Fields.PlaneIdempotents
public import ThirteenPlanes.Shares.ComplexTraceFrames

@[expose] public section

set_option backward.privateInPublic true

/-! The unit-idempotent formula on the complex Hermitian carrier. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

open Peirce

noncomputable section

private theorem complexUnit_trace (x : FullHermitian) :
    ⟪complexUnit, x⟫ = (Matrix.trace (fullMatrix x)).re := by
  rw [fullInner_eq_tracePairing]
  change (Matrix.trace (1 * fullMatrix x)).re = _
  rw [one_mul]

private theorem complexTraceInclusion_product (x y : TracelessHermitian3) :
    complexFullCubic.L (complexTraceInclusion x) (complexTraceInclusion y) =
      complexTraceInclusion (matrixEqualCubic.L x y) + (⟪x,y⟫ / 3) • complexUnit := by
  apply fullMatrix_injective
  rw [fullMatrix_complexFullCubic_product, map_add, map_smul]
  let X := TracelessHermitian3.toMatrix x
  let Y := TracelessHermitian3.toMatrix y
  change symmetricMatrixProduct X Y = TracelessHermitian3.toMatrix (TracelessHermitian3.jordan x y) +
    ((⟪x,y⟫ / 3 : ℝ) : ℂ) • (1 : ComplexMatrix3)
  rw [TracelessHermitian3.toMatrix_jordan, TracelessHermitian3.inner_eq_tracePairing,
    tracePairing_eq_re_trace_jordan, traceFreePart]
  push_cast
  rw [← hermitian_trace_eq_real (symmetricMatrixProduct_hermitian x.isHermitian y.isHermitian)]
  dsimp only [X, Y]
  abel

private theorem complexFrame_formula_point (X : TracelessHermitian3) :
    fullMatrix (framePoint complexTraceInclusion complexUnit X) =
      (1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix X) := by
  rw [framePoint, map_smul, map_add, map_smul]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Lemma 2b-frames, for the actual complex Hermitian matrices. -/
theorem complexFrame_of_three_unit_idempotents (h : SymmetricCubic V)
    (I : V →ₗᵢ[ℝ] TracelessHermitian3)
    (product : ∀ x y, I (h.L x y) = Real.sqrt 6 • matrixEqualCubic.L (I x) (I y))
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    ∃ F : ComplexTraceFrame3, ∀ i,
      F.point i = (1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (I (a i))) := by
  let J := complexTraceInclusion.comp I
  have hrank : ⟪complexUnit, complexUnit⟫ = 3 := by
    rw [complexUnit_trace]
    change (Matrix.trace (1 : ComplexMatrix3)).re = _
    norm_num [Matrix.trace_one]
  have htrace (x : V) : ⟪complexUnit, J x⟫ = 0 := by
    rw [complexUnit_trace]
    change (Matrix.trace (TracelessHermitian3.toMatrix (I x))).re = 0
    simp
  have hproduct (x y : V) : complexFullCubic.L (J x) (J y) =
      (Real.sqrt 6)⁻¹ • J (h.L x y) + (⟪x,y⟫ / 3) • complexUnit := by
    change complexFullCubic.L (complexTraceInclusion (I x)) (complexTraceInclusion (I y)) =
      (Real.sqrt 6)⁻¹ • complexTraceInclusion (I (h.L x y)) + (⟪x,y⟫ / 3) • complexUnit
    have hi : ⟪I x, I y⟫ = ⟪x,y⟫ := by
      have hh := norm_add_sq_real (I x) (I y)
      rw [← I.map_add, I.norm_map, I.norm_map, I.norm_map] at hh
      linarith only [hh, norm_add_sq_real x y]
    rw [complexTraceInclusion_product, product, map_smul, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne', one_smul, hi]
  let p (i : Fin 3) := framePoint J complexUnit (a i)
  have H := frame_of_three_unit_idempotents h complexFullCubic complexUnit J complexUnit_mul
    hrank htrace hproduct a ha hs
  let F : ComplexTraceFrame3 :=
    { point := fun i => fullMatrix (p i)
      hermitian := fun i => fullMatrix_hermitian (p i)
      trace_one := fun i => by
        rw [hermitian_trace_eq_real (fullMatrix_hermitian (p i)), ← complexUnit_trace, H.trace_one]
        norm_num
      jordan_point := fun i j => by
        rw [← fullMatrix_complexFullCubic_product]
        split_ifs with he
        · subst j
          rw [show complexFullCubic.L (p i) (p i) = p i from H.idempotent i]
        · rw [show complexFullCubic.L (p i) (p j) = 0 from H.orthogonal i j he, map_zero]
      sum_unit := by
        rw [← map_sum, show (∑ i, p i) = complexUnit from H.sum_unit]
        rfl }
  exact ⟨F, fun i => complexFrame_formula_point (I (a i))⟩

/-- Orthogonality of two source vectors gives trace overlap one third for their frame points. -/
theorem complexFrame_formula_unbiased (I : V →ₗᵢ[ℝ] TracelessHermitian3) {x y : V}
    (orth : ⟪x,y⟫ = 0) :
    tracePairing
      ((1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (I x)))
      ((1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (I y))) = 1 / 3 := by
  have hxy : ⟪I x, I y⟫ = 0 := by
    have hh := norm_add_sq_real (I x) (I y)
    rw [← I.map_add, I.norm_map, I.norm_map, I.norm_map] at hh
    linarith only [hh, norm_add_sq_real x y, orth]
  rw [TracelessHermitian3.inner_eq_tracePairing] at hxy
  unfold tracePairing at hxy ⊢
  norm_num [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_one, Complex.real_smul, Complex.mul_re, Complex.add_re, hxy]

/-- The exact traceless component of a complex point supplied by the frame formula. -/
theorem complexFrame_center_of_formula (F : ComplexTraceFrame3) (i : Fin 3) (x : TracelessHermitian3)
    (hp : F.point i = (1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix x)) :
    F.center i = (Real.sqrt 6 / 3 : ℝ) • x := by
  apply TracelessHermitian3.toMatrix_injective
  change traceFreePart (F.point i) = TracelessHermitian3.toMatrix ((Real.sqrt 6 / 3 : ℝ) • x)
  rw [traceFreePart, F.trace_one, hp, map_smul]
  change ((1 / 3 : ℝ) : ℂ) • (1 + (Real.sqrt 6 : ℂ) • TracelessHermitian3.toMatrix x) -
    (1 / 3 : ℂ) • (1 : ComplexMatrix3) = ((Real.sqrt 6 / 3 : ℝ) : ℂ) • TracelessHermitian3.toMatrix x
  push_cast
  module

/-- Every closed complex Hermitian two-plane is the centered span of an actual Jordan frame. -/
theorem complexClosedPlane_has_frame (S : Submodule ℝ TracelessHermitian3)
    (dim : Module.finrank ℝ S = 2) (closed : IsClosedPiece matrixEqualCubic S) :
    ∃ F : ComplexTraceFrame3, S = F.plane := by
  let h := Real.sqrt 6 • matrixEqualCubic
  have hc : IsClosedPiece h S := by
    change IsClosedPiece (Real.sqrt 6 • matrixEqualCubic) S
    exact (isClosedPiece_smul_iff (h := matrixEqualCubic)
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne' S).mpr closed
  have hr : IsRound h 1 := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [show h = Real.sqrt 6 • matrixEqualCubic from rfl, SymmetricCubic.squareMap_smul,
      norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
      matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
    ring
  obtain ⟨a, hS, ha, hs⟩ := closedPlane_three_unitIdempotents hr S dim hc
  obtain ⟨F, hF⟩ := complexFrame_of_three_unit_idempotents h (LinearIsometry.id) (fun _ _ => rfl) a ha hs
  have hle : F.plane ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [complexFrame_center_of_formula F i (a i) (hF i)]
    exact S.smul_mem _ (hS i)
  exact ⟨F, (Submodule.eq_of_le_of_finrank_eq hle (F.plane_dimension.trans dim.symm)).symm⟩

end

end ThirteenPlanes.RoundCubics
