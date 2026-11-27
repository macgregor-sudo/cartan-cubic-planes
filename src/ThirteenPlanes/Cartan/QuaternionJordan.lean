module

public import ThirteenPlanes.Cartan.OperatorFrames
public import ThirteenPlanes.Quaternionic.NativeTraceModel

@[expose] public section

set_option backward.privateInPublic true

/-! The skew-operator model on actual quaternionic Hermitian matrices. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix BigOperators RealInnerProductSpace
open QuaternionicMUB

noncomputable section

theorem quaternion_L_matrix (x y : HermitianHilbert) :
    fullMat (quaternionFullCubic.L x y) = jordan (fullMat x) (fullMat y) :=
  fullMat_ofMatrix _ _

private theorem quaternion_jordan_identity (A B : QMat) :
    jordan A (jordan (jordan A A) B) = jordan (jordan A A) (jordan A B) := by
  rw [jordan_self]
  simp only [jordan, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  simp only [mul_assoc]
  abel

/-- The native quaternionic Hermitian model with its real trace metric. -/
def quaternionJordan : TraceJordanData HermitianHilbert where
  L := quaternionFullCubic.L
  unit := fullUnit
  unit_left := quaternionFullCubic_unit
  unit_trace := by
    rw [hermitianHilbert_inner]
    change traceForm (fullMat fullUnit) (fullMat fullUnit) = 3
    rw [fullMat_fullUnit, traceForm_eq_rtrace_mul, one_mul, rtrace_one]
  comm := quaternionFullCubic.L_comm
  assoc_inner x y z := (quaternionFullCubic.apply_swap₂₃ x y z).trans (real_inner_comm _ _)
  jordan x := by
    change quaternionFullCubic.L x * quaternionFullCubic.L (quaternionFullCubic.L x x) =
      quaternionFullCubic.L (quaternionFullCubic.L x x) * quaternionFullCubic.L x
    apply LinearMap.ext
    intro y
    apply fullMat_injective
    simp only [mul_apply_eq_comp, quaternion_L_matrix]
    exact quaternion_jordan_identity _ _

@[simp] theorem quaternionJordan_trace (x : HermitianHilbert) :
    quaternionJordan.trace x = rtrace (fullMat x) := by
  change ⟪fullUnit, x⟫ = _
  rw [hermitianHilbert_inner]
  change traceForm (fullMat fullUnit) (fullMat x) = _
  rw [fullMat_fullUnit, traceForm_eq_rtrace_mul, one_mul]

/-- Identification with the native quaternionic traceless carrier from §4. -/
noncomputable def quaternionTraceEquiv : quaternionJordan.traceFree ≃ₗᵢ[ℝ] TracelessHilbert where
  toFun x := ⟨x.val.val, x.val.property, (quaternionJordan_trace x.val).symm.trans x.property⟩
  invFun x := ⟨traceInclusion x, (quaternionJordan_trace (traceInclusion x)).trans (traceMat_trace x)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

@[simp] theorem quaternionTraceEquiv_inclusion (x : quaternionJordan.traceFree) :
    traceInclusion (quaternionTraceEquiv x) = x.val := rfl

@[simp] theorem quaternionTraceEquiv_matrix (x : quaternionJordan.traceFree) :
    traceMat (quaternionTraceEquiv x) = fullMat x.val := rfl

theorem quaternionTraceFree_finrank : Module.finrank ℝ quaternionJordan.traceFree = 14 :=
  quaternionTraceEquiv.toLinearEquiv.finrank_eq.trans finrank_TracelessHilbert

/-- The ambient real space of quaternionic skew-Hermitian matrices. -/
def quaternionSkewMatrices : Submodule ℝ QMat where
  carrier := {A | Aᴴ = -A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B)ᴴ = -(A + B)
    rw [Matrix.conjTranspose_add, hA, hB, neg_add]
  smul_mem' := by
    intro a A hA
    change (a • A)ᴴ = -(a • A)
    rw [Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

private theorem quaternion_bracket_hermitian (A : quaternionSkewMatrices)
    (x : HermitianHilbert) : (A.val * fullMat x - fullMat x * A.val).IsHermitian := by
  change (A.val * fullMat x - fullMat x * A.val)ᴴ = _
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fullMat_hermitian x |>.eq, A.property, mul_neg, neg_mul]
  abel

/-- The actual commutator action of a skew-Hermitian quaternionic matrix on Hermitian matrices. -/
def quaternionCommutator (A : quaternionSkewMatrices) : Module.End ℝ HermitianHilbert where
  toFun x := fullOfMatrix _ (quaternion_bracket_hermitian A x)
  map_add' x y := by
    apply fullMat_injective
    simp only [map_add, fullMat_ofMatrix, mul_add, add_mul]
    abel
  map_smul' r x := by
    apply fullMat_injective
    simp only [map_smul, fullMat_ofMatrix, mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply]

@[simp] theorem quaternionCommutator_matrix (A : quaternionSkewMatrices) (x : HermitianHilbert) :
    fullMat (quaternionCommutator A x) = A.val * fullMat x - fullMat x * A.val :=
  fullMat_ofMatrix _ _

private theorem quaternion_commutator_derivation (A : quaternionSkewMatrices) :
    quaternionJordan.IsDerivation (quaternionCommutator A) := by
  intro x y
  apply fullMat_injective
  change fullMat (quaternionCommutator A (quaternionFullCubic.L x y)) =
    fullMat (quaternionFullCubic.L (quaternionCommutator A x) y +
      quaternionFullCubic.L x (quaternionCommutator A y))
  simp only [map_add, quaternionCommutator_matrix, quaternion_L_matrix,
    jordan, mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_add]
  congr 1
  noncomm_ring

private theorem quaternion_commutator_skew (A : quaternionSkewMatrices) :
    IsSkew (quaternionCommutator A) := by
  intro x y
  rw [hermitianHilbert_inner, hermitianHilbert_inner]
  change traceForm (fullMat (quaternionCommutator A x)) (fullMat y) =
    -traceForm (fullMat x) (fullMat (quaternionCommutator A y))
  simp only [quaternionCommutator_matrix, traceForm_eq_rtrace_mul, sub_mul, mul_sub, rtrace_sub]
  have h := rtrace_mul_comm A.val (fullMat x * fullMat y)
  rw [← mul_assoc] at h
  rw [← mul_assoc (fullMat x) A.val (fullMat y), ← mul_assoc (fullMat x) (fullMat y) A.val]
  linarith

/-- Matrix commutators as represented skew Jordan derivations. -/
def quaternionCommutatorLinear : quaternionSkewMatrices →ₗ[ℝ] SkewOperator HermitianHilbert where
  toFun A := ⟨quaternionCommutator A, quaternion_commutator_skew A⟩
  map_add' A B := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply fullMat_injective
    change fullMat (quaternionCommutator (A + B) x) =
      fullMat (quaternionCommutator A x + quaternionCommutator B x)
    simp only [map_add, quaternionCommutator_matrix, Submodule.coe_add, add_mul, mul_add]
    abel
  map_smul' r A := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply fullMat_injective
    change fullMat (quaternionCommutator (r • A) x) =
      fullMat (r • quaternionCommutator A x)
    simp only [map_smul, quaternionCommutator_matrix, Submodule.coe_smul,
      smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The literal space of quaternionic commutator operators, on the unital carrier. -/
def quaternionOperatorAlgebra : Submodule ℝ (SkewOperator HermitianHilbert) :=
  LinearMap.range quaternionCommutatorLinear

theorem quaternionOperatorAlgebra_le :
    quaternionOperatorAlgebra ≤ quaternionJordan.skewDerivations := by
  rintro _ ⟨A, rfl⟩
  exact quaternion_commutator_derivation A

end

end ThirteenPlanes.Cartan
