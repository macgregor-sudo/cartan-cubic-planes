module

public import ThirteenPlanes.Peirce.CartanTrilinear
public import ThirteenPlanes.Peirce.SlotNativeModel
public import ThirteenPlanes.Peirce.SlotQuaternionModel
public import ThirteenPlanes.Peirce.SlotRealModel

@[expose] public section

/-! Conditions N1–N3 on the actual models of Lemma 2b-model. -/

open scoped Quaternion InnerProductSpace RealInnerProductSpace
open scoped ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.Peirce

noncomputable section

/-- The printed slot product on associative coefficient algebras, in the upper-entry convention. -/
def conjugateSlotProduct (K : Type*) [Ring K] [Algebra ℝ K] [StarRing K] [StarModule ℝ K] :
    K →ₗ[ℝ] K →ₗ[ℝ] K :=
  LinearMap.mk₂ ℝ (fun p q => q * star p)
    (by intros; rw [star_add, mul_add])
    (by intros; rw [star_smul, star_trivial, mul_smul_comm])
    (by intros; rw [add_mul])
    (by intros; rw [smul_mul_assoc])

@[simp] theorem conjugateSlotProduct_apply (K : Type*) [Ring K] [Algebra ℝ K]
    [StarRing K] [StarModule ℝ K] (p q : K) : conjugateSlotProduct K p q = q * star p := rfl

/-- The actual octonionic slot product in the same upper-entry convention. -/
def nativeConjugateSlotProduct : AlbertSequential.Octonion →ₗ[ℝ] AlbertSequential.Octonion →ₗ[ℝ]
    AlbertSequential.Octonion := by
  open AlbertSequential in
  exact LinearMap.mk₂ ℝ (fun p q => octonionMul q (octonionConj p))
    (by intros; rw [octonionConj_add, octonionMul_add_right])
    (by intros; rw [octonionConj_smul, octonionMul_smul_right])
    (by intros; rw [octonionMul_add_left])
    (by intros; rw [octonionMul_smul_left])

@[simp] theorem nativeConjugateSlotProduct_apply (p q : AlbertSequential.Octonion) :
    nativeConjugateSlotProduct p q = AlbertSequential.octonionMul q (AlbertSequential.octonionConj p) := rfl

set_option maxHeartbeats 1000000 in
/-- Lemma 2b-model, for real symmetric matrices with their actual trace metric. -/
theorem realCartan_modelConditions :
    CartanCoordinateConditions realCartanCubic realCartanEquiv (conjugateSlotProduct ℝ) := by
  refine cartanCoordinateConditions_of_normalForm realCartanCubic realCartanEquiv
    (conjugateSlotProduct ℝ) realCartanField_norm_sq ?_
  intro α β p q r
  simpa only [conjugateSlotProduct_apply, star_trivial] using realCartanCubic_normalForm α β p q r

/-- Lemma 2b-model, for complex Hermitian matrices with their actual trace metric. -/
theorem complexCartan_modelConditions :
    CartanCoordinateConditions complexCartanCubic complexCartanEquiv (conjugateSlotProduct ℂ) := by
  exact cartanCoordinateConditions_of_normalForm _ _ _ complexCartanField_norm_sq complexCartanCubic_normalForm

/-- Lemma 2b-model, for quaternionic Hermitian matrices with their actual trace metric. -/
theorem quaternionCartan_modelConditions :
    CartanCoordinateConditions quaternionCartanCubic quaternionCartanEquiv (conjugateSlotProduct (Quaternion ℝ)) := by
  exact cartanCoordinateConditions_of_normalForm _ _ _ quaternionCartanField_norm_sq quaternionCartanCubic_normalForm

/-- Lemma 2b-model, for native Albert matrices with their actual trace metric. -/
theorem nativeCartan_modelConditions :
    CartanCoordinateConditions nativeCartanCubic nativeCartanEquiv nativeConjugateSlotProduct := by
  exact cartanCoordinateConditions_of_normalForm _ _ _ nativeCartanField_norm_sq nativeCartanCubic_normalForm

end

end ThirteenPlanes.Peirce
