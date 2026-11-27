module

public import ThirteenPlanes.Fields.ComplexFrames
public import ThirteenPlanes.Peirce.SlotRealModel

@[expose] public section

set_option backward.privateInPublic true

/-! Complex frame coordinates restricted to real symmetric matrices. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.Peirce

open RoundCubics

noncomputable section

/-- The isometric inclusion of the real symmetric trace carrier into the complex trace carrier. -/
abbrev realTraceIsometry : RealTracelessSymmetric3 →ₗᵢ[ℝ] TracelessHermitian3 :=
  realTraceSubmodule.subtypeₗᵢ

private theorem realTrace_entries (x : RealTracelessSymmetric3) (i j : Fin 3) :
    (TracelessHermitian3.toMatrix x.val i j).im = 0 := by
  obtain ⟨⟨a, b, p, q, r⟩, rfl⟩ := realCartanEquiv.surjective x
  change (complexCartanMatrix a b p q r i j).im = 0
  fin_cases i <;> fin_cases j <;>
    simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul]

private theorem realTraceSubmodule_mem_of_entries (x : TracelessHermitian3)
    (h : ∀ i j, (TracelessHermitian3.toMatrix x i j).im = 0) : x ∈ realTraceSubmodule := by
  let A : RealMatrix3 := (TracelessHermitian3.toMatrix x).map Complex.re
  have hsym : Aᵀ = A := by
    ext i j
    have he := congrFun (congrFun x.isHermitian.eq i) j
    simpa [A, Matrix.conjTranspose_apply, Complex.star_def] using congrArg Complex.re he
  have ht : Matrix.trace A = 0 := by
    change ∑ i, (TracelessHermitian3.toMatrix x i i).re = 0
    have he := congrArg Complex.re x.trace_eq_zero
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.zero_re] at he
    exact he
  obtain ⟨y, hy⟩ := (realTraceMatrix_range A).mpr ⟨hsym, ht⟩
  have hxy : realTraceIsometry y = x := by
    apply TracelessHermitian3.toMatrix_injective
    ext i j
    apply Complex.ext
    · exact congrFun (congrFun hy i) j
    · exact (realTrace_entries y i j).trans (h i j).symm
  rw [← hxy]
  exact y.property

private theorem realTrace_complex_product_mem (x y : RealTracelessSymmetric3) :
    matrixEqualCubic.L (realTraceIsometry x) (realTraceIsometry y) ∈ realTraceSubmodule := by
  apply realTraceSubmodule_mem_of_entries
  intro i j
  let X := TracelessHermitian3.toMatrix (realTraceIsometry x)
  let Y := TracelessHermitian3.toMatrix (realTraceIsometry y)
  let A := symmetricMatrixProduct X Y
  have hA : A.IsHermitian := symmetricMatrixProduct_hermitian (realTraceIsometry x).isHermitian
    (realTraceIsometry y).isHermitian
  have hre : Matrix.trace A = ((Matrix.trace A).re : ℂ) := hermitian_trace_eq_real hA
  have hentry : (A i j).im = 0 := by
    change (((1 / 2 : ℂ) • (X * Y + Y * X)) i j).im = 0
    norm_num [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, smul_eq_mul,
      Complex.mul_im, Complex.add_im, Complex.im_sum, X, Y, realTrace_entries, Complex.div_im]
  change (TracelessHermitian3.toMatrix (TracelessHermitian3.jordan
    (realTraceIsometry x) (realTraceIsometry y)) i j).im = 0
  rw [TracelessHermitian3.toMatrix_jordan]
  change ((traceFreePart A) i j).im = 0
  simp only [traceFreePart, Matrix.sub_apply, Complex.sub_im, Matrix.smul_apply, smul_eq_mul, hentry]
  rw [hre]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The actual centered Jordan product on the real carrier is the complex product restricted to it. -/
theorem realTraceIsometry_product (x y : RealTracelessSymmetric3) :
    realTraceIsometry (realCartanCubic.L x y) = Real.sqrt 6 •
      matrixEqualCubic.L (realTraceIsometry x) (realTraceIsometry y) := by
  let z : RealTracelessSymmetric3 := ⟨Real.sqrt 6 • matrixEqualCubic.L
    (realTraceIsometry x) (realTraceIsometry y), realTraceSubmodule.smul_mem _
    (realTrace_complex_product_mem x y)⟩
  suffices realCartanCubic.L x y = z from congrArg realTraceIsometry this
  apply ext_inner_right ℝ
  intro w
  change realCartanCubic.apply x y w = complexCartanCubic.apply (realTraceIsometry x)
    (realTraceIsometry y) (realTraceIsometry w)
  exact SymmetricCubic.pullback_apply _ _ _ _ _

private theorem real_framePoint_complex (x : RealTracelessSymmetric3) :
    ((1 / 3 : ℝ) • ((1 : RealMatrix3) + Real.sqrt 6 • realTraceMatrix x)).map Complex.ofReal =
      (1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (realTraceIsometry x)) := by
  ext i j
  apply Complex.ext
  · by_cases hij : i = j <;>
      simp [Matrix.smul_apply, Matrix.add_apply, hij, realTraceMatrix]
  · by_cases hij : i = j <;>
      simp [Matrix.smul_apply, Matrix.add_apply, hij, realTrace_entries]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Lemma 2b-frames, for real symmetric matrices, included into the complex model. -/
theorem realFrame_of_three_unit_idempotents (h : SymmetricCubic V)
    (I : V →ₗᵢ[ℝ] RealTracelessSymmetric3)
    (product : ∀ x y, I (h.L x y) = realCartanCubic.L (I x) (I y))
    (a : Fin 3 → V) (ha : ∀ i, IsUnitIdempotent h (a i)) (hs : ∑ i, a i = 0) :
    ∃ F : ComplexTraceFrame3, ∀ i,
      F.point i = ((1 / 3 : ℝ) • ((1 : RealMatrix3) + Real.sqrt 6 • realTraceMatrix (I (a i)))).map
        Complex.ofReal := by
  have hp (x y : V) : (realTraceIsometry.comp I) (h.L x y) = Real.sqrt 6 • matrixEqualCubic.L
      ((realTraceIsometry.comp I) x) ((realTraceIsometry.comp I) y) := by
    change realTraceIsometry (I (h.L x y)) = _
    rw [product, realTraceIsometry_product]
    rfl
  obtain ⟨F, hF⟩ := complexFrame_of_three_unit_idempotents h (realTraceIsometry.comp I) hp a ha hs
  refine ⟨F, fun i => ?_⟩
  rw [real_framePoint_complex]
  exact hF i

/-- For the actual real symmetric frame points the ordinary matrix trace overlap is one third. -/
theorem realFrame_formula_unbiased (I : V →ₗᵢ[ℝ] RealTracelessSymmetric3) {x y : V}
    (orth : ⟪x,y⟫ = 0) :
    Matrix.trace (((1 / 3 : ℝ) • ((1 : RealMatrix3) + Real.sqrt 6 • realTraceMatrix (I x))) *
      ((1 / 3 : ℝ) • ((1 : RealMatrix3) + Real.sqrt 6 • realTraceMatrix (I y)))) = 1 / 3 := by
  have h := complexFrame_formula_unbiased (realTraceIsometry.comp I) orth
  change tracePairing
    ((1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (realTraceIsometry (I x))))
    ((1 / 3 : ℝ) • ((1 : ComplexMatrix3) + Real.sqrt 6 • TracelessHermitian3.toMatrix (realTraceIsometry (I y))))
    = 1 / 3 at h
  rw [← real_framePoint_complex, ← real_framePoint_complex] at h
  simpa [tracePairing, Matrix.trace, Matrix.mul_apply] using h

/-- A real closed plane is the traceless span of frame points which are all real symmetric matrices. -/
theorem realClosedPlane_has_frame (S : Submodule ℝ RealTracelessSymmetric3)
    (dim : Module.finrank ℝ S = 2) (closed : IsClosedPiece realCartanCubic S) :
    ∃ F : ComplexTraceFrame3, S.map realTraceIsometry.toLinearMap = F.plane ∧
      ∀ a i j, (F.point a i j).im = 0 := by
  let T := S.map realTraceIsometry.toLinearMap
  have hTdim : Module.finrank ℝ T = 2 :=
    (Submodule.equivMapOfInjective realTraceIsometry.toLinearMap realTraceIsometry.injective S).finrank_eq.symm.trans dim
  have hT : IsClosedPiece matrixEqualCubic T := by
    apply (isClosedPiece_smul_iff (h := matrixEqualCubic)
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne' T).mp
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨realCartanCubic.L x y, closed hx hy, realTraceIsometry_product x y⟩
  obtain ⟨F, hF⟩ := complexClosedPlane_has_frame T hTdim hT
  refine ⟨F, hF, fun a i j => ?_⟩
  have hcenter : F.center a ∈ T := by
    rw [hF]
    exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨x, _, hx⟩ := hcenter
  have hi := realTrace_entries x i j
  rw [show x.val = F.center a from hx] at hi
  change ((traceFreePart (F.point a)) i j).im = 0 at hi
  rw [traceFreePart, F.trace_one] at hi
  by_cases hij : i = j <;> simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij] using hi

end

end ThirteenPlanes.Peirce
