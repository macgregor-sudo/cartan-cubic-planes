module

public import ThirteenPlanes.Cartan.OperatorFrames
public import ThirteenPlanes.Fields.ComplexFrames

@[expose] public section

set_option backward.privateInPublic true

/-! Jordan operators on the actual complex Hermitian matrices. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix BigOperators RealInnerProductSpace
open RoundCubics

noncomputable section

@[simp] theorem fullMatrix_complexUnit : fullMatrix complexUnit = 1 := rfl

private theorem complex_jordan_identity (A B : ComplexMatrix3) :
    symmetricMatrixProduct A (symmetricMatrixProduct (symmetricMatrixProduct A A) B) =
      symmetricMatrixProduct (symmetricMatrixProduct A A) (symmetricMatrixProduct A B) := by
  rw [symmetricMatrixProduct_self]
  simp only [symmetricMatrixProduct, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul, mul_assoc]
  abel

/-- The full complex Hermitian Hilbert space with its unital Jordan product. -/
def complexJordan : TraceJordanData FullHermitian where
  L := complexFullCubic.L
  unit := complexUnit
  unit_left := complexUnit_mul
  unit_trace := by
    rw [fullInner_eq_tracePairing, fullMatrix_complexUnit]
    norm_num [tracePairing, Matrix.trace_one]
  comm := complexFullCubic.L_comm
  assoc_inner x y z := (complexFullCubic.apply_swap₂₃ x y z).trans (real_inner_comm _ _)
  jordan x := by
    change complexFullCubic.L x * complexFullCubic.L (complexFullCubic.L x x) =
      complexFullCubic.L (complexFullCubic.L x x) * complexFullCubic.L x
    apply LinearMap.ext
    intro y
    apply fullMatrix_injective
    simp only [mul_apply_eq_comp, fullMatrix_complexFullCubic_product]
    exact complex_jordan_identity _ _

@[simp] theorem complexJordan_trace (x : FullHermitian) :
    complexJordan.trace x = (Matrix.trace (fullMatrix x)).re := by
  change ⟪complexUnit, x⟫ = _
  rw [fullInner_eq_tracePairing, fullMatrix_complexUnit]
  simp [tracePairing]

/-- The abstract trace kernel in the unital model equals the native traceless Hermitian carrier. -/
def complexTraceEquiv : complexJordan.traceFree ≃ₗᵢ[ℝ] TracelessHermitian3 where
  toFun x := ⟨x.val.val, fullMatrix_hermitian x.val, by
    change Matrix.trace (fullMatrix x.val) = 0
    have h := x.property
    change complexJordan.trace x.val = 0 at h
    rw [complexJordan_trace] at h
    rw [hermitian_trace_eq_real (fullMatrix_hermitian x.val), h, Complex.ofReal_zero]⟩
  invFun x := ⟨complexTraceInclusion x, by
    change complexJordan.trace (complexTraceInclusion x) = 0
    rw [complexJordan_trace]
    change (Matrix.trace (TracelessHermitian3.toMatrix x)).re = 0
    simp⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

@[simp] theorem complexTraceEquiv_matrix (x : complexJordan.traceFree) :
    TracelessHermitian3.toMatrix (complexTraceEquiv x) = fullMatrix x.val := rfl

private theorem complex_center_matrix (x : FullHermitian) :
    fullMatrix (complexJordan.center x).val = traceFreePart (fullMatrix x) := by
  change fullMatrix (x - (complexJordan.trace x / 3) • complexUnit) = _
  rw [map_sub, map_smul, fullMatrix_complexUnit, complexJordan_trace, traceFreePart]
  have hh := hermitian_trace_eq_real (fullMatrix_hermitian x)
  conv_rhs => rw [hh]
  change fullMatrix x - ((↑((Matrix.trace (fullMatrix x)).re / 3 : ℝ) : ℂ)) • (1 : ComplexMatrix3) = _
  push_cast
  rfl

@[simp] theorem complex_traceCubic_map_L (x y : complexJordan.traceFree) :
    complexTraceEquiv (complexJordan.traceCubic.L x y) =
      matrixEqualCubic.L (complexTraceEquiv x) (complexTraceEquiv y) := by
  apply TracelessHermitian3.toMatrix_injective
  rw [complexTraceEquiv_matrix, complexJordan.traceCubic_L, complex_center_matrix]
  change traceFreePart (fullMatrix (complexFullCubic.L x.val y.val)) =
    TracelessHermitian3.toMatrix (TracelessHermitian3.jordan (complexTraceEquiv x) (complexTraceEquiv y))
  rw [fullMatrix_complexFullCubic_product, TracelessHermitian3.toMatrix_jordan,
    complexTraceEquiv_matrix, complexTraceEquiv_matrix]

/-- Lift a native matrix frame to the unital trace-metric model. -/
def complexJordanFrame (F : ComplexTraceFrame3) : complexJordan.Frame where
  point a := ofFullMatrix (F.point a) (F.hermitian a)
  trace_one a := by rw [complexJordan_trace, fullMatrix_ofFullMatrix, F.trace_one]; norm_num
  mul_point a b := by
    apply fullMatrix_injective
    change fullMatrix (complexFullCubic.L _ _) = _
    rw [fullMatrix_complexFullCubic_product, fullMatrix_ofFullMatrix, fullMatrix_ofFullMatrix, F.jordan_point]
    split_ifs <;> simp
  sum_unit := by
    apply fullMatrix_injective
    change fullMatrix (∑ a, ofFullMatrix (F.point a) (F.hermitian a)) = fullMatrix complexUnit
    rw [map_sum, fullMatrix_complexUnit]
    simpa only [fullMatrix_ofFullMatrix] using F.sum_unit

/-- The lifted frame has the same centered span as the native frame. -/
theorem complexJordanFrame_plane (F : ComplexTraceFrame3) :
    ((complexJordanFrame F).plane complexJordan).map complexTraceEquiv.toLinearMap = F.plane := by
  rw [TraceJordanData.Frame.plane, Submodule.map_span, ← Set.range_comp]
  change Submodule.span ℝ (Set.range fun a =>
    complexTraceEquiv (complexJordan.center ((complexJordanFrame F).point a))) = _
  have h (a : Fin 3) : complexTraceEquiv (complexJordan.center ((complexJordanFrame F).point a)) = F.center a := by
    apply TracelessHermitian3.toMatrix_injective
    rw [complexTraceEquiv_matrix, complex_center_matrix]
    change traceFreePart (fullMatrix (ofFullMatrix (F.point a) (F.hermitian a))) = _
    rw [fullMatrix_ofFullMatrix]
    rfl
  simp_rw [h]
  rfl

/-- Every closed complex two-plane in the unital trace-metric model is the plane of a native frame. -/
theorem complex_closedPlane_has_frame (U : Submodule ℝ complexJordan.traceFree)
    (hd : Module.finrank ℝ U = 2) (hc : IsClosedPiece complexJordan.traceCubic U) :
    ∃ F : complexJordan.Frame, U = F.plane complexJordan := by
  let W := U.map complexTraceEquiv.toLinearMap
  have hdW : Module.finrank ℝ W = 2 :=
    (complexTraceEquiv.toLinearEquiv.submoduleMap U).finrank_eq.symm.trans hd
  have hcW : IsClosedPiece matrixEqualCubic W := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    change matrixEqualCubic.L (complexTraceEquiv x) (complexTraceEquiv y) ∈ W
    rw [← complex_traceCubic_map_L]
    exact Submodule.mem_map_of_mem (hc hx hy)
  obtain ⟨F, hF⟩ := complexClosedPlane_has_frame W hdW hcW
  refine ⟨complexJordanFrame F, ?_⟩
  apply Submodule.map_injective_of_injective complexTraceEquiv.injective
  rw [complexJordanFrame_plane]
  exact hF

/-- The actual matrix space of traceless skew-Hermitian three-by-three complex matrices. -/
def complexSkewTracelessMatrices : Submodule ℝ ComplexMatrix3 where
  carrier := {A | Aᴴ = -A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨hA, htA⟩ ⟨hB, htB⟩
    change (A + B)ᴴ = -(A + B) ∧ Matrix.trace (A + B) = 0
    simp [Matrix.conjTranspose_add, hA, hB, htA, htB, Matrix.trace_add, add_comm]
  smul_mem' := by
    rintro a A ⟨hA, htA⟩
    change (a • A)ᴴ = -(a • A) ∧ Matrix.trace (a • A) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, hA, smul_neg, Matrix.trace_smul, htA, smul_zero]
    exact ⟨rfl, rfl⟩

private theorem complex_bracket_hermitian (A : complexSkewTracelessMatrices)
    (x : FullHermitian) : (A.val * fullMatrix x - fullMatrix x * A.val).IsHermitian := by
  change (A.val * fullMatrix x - fullMatrix x * A.val)ᴴ = _
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    (fullMatrix_hermitian x).eq, A.property.1, mul_neg, neg_mul]
  abel

/-- The native matrix commutator action of a traceless skew-Hermitian matrix. -/
def complexCommutator (A : complexSkewTracelessMatrices) : Module.End ℝ FullHermitian where
  toFun x := ofFullMatrix _ (complex_bracket_hermitian A x)
  map_add' x y := by
    apply fullMatrix_injective
    simp only [map_add, fullMatrix_ofFullMatrix, mul_add, add_mul]
    abel
  map_smul' r x := by
    apply fullMatrix_injective
    simp only [map_smul, fullMatrix_ofFullMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply]

@[simp] theorem complexCommutator_matrix (A : complexSkewTracelessMatrices) (x : FullHermitian) :
    fullMatrix (complexCommutator A x) = A.val * fullMatrix x - fullMatrix x * A.val :=
  fullMatrix_ofFullMatrix _ _

private theorem complex_commutator_derivation (A : complexSkewTracelessMatrices) :
    complexJordan.IsDerivation (complexCommutator A) := by
  intro x y
  apply fullMatrix_injective
  change fullMatrix (complexCommutator A (complexFullCubic.L x y)) =
    fullMatrix (complexFullCubic.L (complexCommutator A x) y +
      complexFullCubic.L x (complexCommutator A y))
  simp only [map_add, complexCommutator_matrix, fullMatrix_complexFullCubic_product,
    symmetricMatrixProduct, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← smul_add]
  congr 1
  noncomm_ring

private theorem complex_commutator_skew (A : complexSkewTracelessMatrices) :
    IsSkew (V := FullHermitian) (complexCommutator A) := by
  intro x y
  rw [fullInner_eq_tracePairing, fullInner_eq_tracePairing]
  simp only [complexCommutator_matrix, tracePairing, sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
  have h := Matrix.trace_mul_comm A.val (fullMatrix x * fullMatrix y)
  rw [← mul_assoc] at h
  rw [← mul_assoc (fullMatrix x) A.val (fullMatrix y), ← mul_assoc (fullMatrix x) (fullMatrix y) A.val, h]
  ring

/-- Matrix commutators as represented skew Jordan derivations. -/
def complexCommutatorLinear : complexSkewTracelessMatrices →ₗ[ℝ] SkewOperator FullHermitian where
  toFun A := ⟨complexCommutator A, complex_commutator_skew A⟩
  map_add' A B := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply fullMatrix_injective
    change fullMatrix (complexCommutator (A + B) x) =
      fullMatrix (complexCommutator A x + complexCommutator B x)
    simp only [map_add, complexCommutator_matrix, Submodule.coe_add, add_mul, mul_add]
    abel
  map_smul' r A := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply fullMatrix_injective
    change fullMatrix (complexCommutator (r • A) x) = r • fullMatrix (complexCommutator A x)
    simp only [complexCommutator_matrix, Submodule.coe_smul, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- The image of the actual traceless skew-Hermitian matrices acting by commutation. -/
def complexOperatorAlgebra : Submodule ℝ (SkewOperator FullHermitian) :=
  LinearMap.range complexCommutatorLinear

theorem complexOperatorAlgebra_le : complexOperatorAlgebra ≤ complexJordan.skewDerivations := by
  rintro _ ⟨A, rfl⟩
  exact complex_commutator_derivation A

end

end ThirteenPlanes.Cartan
