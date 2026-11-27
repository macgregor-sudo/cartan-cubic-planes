module

public import ThirteenPlanes.SignedSkewStabilizerNative
public import AlbertDerivationDimension
public import CompanionIltyakovAction

@[expose] public section

set_option backward.privateInPublic true

open scoped RealInnerProductSpace

namespace ThirteenPlanes.SignedSkew

noncomputable section

def extendSignedEnd : (SignedField →ₗ[ℝ] SignedField) →ₗ[ℝ]
    (AlbertSequential.Albert →ₗ[ℝ] AlbertSequential.Albert) :=
  signedSplitSequentialEquiv.conj.toLinearMap.comp liftSignedEnd

@[simp] theorem extendSignedEnd_on_image (A : SignedField →ₗ[ℝ] SignedField) (x : SignedWithUnit) :
    extendSignedEnd A (signedSplitSequentialEquiv x) = signedSplitSequentialEquiv (liftSignedEnd A x) := by
  change signedSplitSequentialEquiv.conj (liftSignedEnd A) (signedSplitSequentialEquiv x) = _
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

theorem extendSignedEnd_derivation_iff (A : SignedField →ₗ[ℝ] SignedField) :
    extendSignedEnd A ∈ AlbertSequential.albertDerivations ↔ IsSkew A ∧ CenterDerivation signedEqualCubic A := by
  rw [← liftSignedEnd_derivation_iff signedEqualCubic]
  constructor
  · intro hd x y
    have ht := AlbertSequential.albertDerivation_mul ⟨extendSignedEnd A,hd⟩
      (signedSplitSequentialEquiv x) (signedSplitSequentialEquiv y)
    change extendSignedEnd A (AlbertSequential.jordanMul (signedSplitSequentialEquiv x) (signedSplitSequentialEquiv y)) = _ at ht
    apply signedSplitSequentialEquiv.injective
    simpa only [← signedSplitSequentialEquiv_product, extendSignedEnd_on_image, map_add] using ht
  · intro hd x y
    obtain ⟨x,rfl⟩ := signedSplitSequentialEquiv.surjective x
    obtain ⟨y,rfl⟩ := signedSplitSequentialEquiv.surjective y
    change extendSignedEnd A (AlbertSequential.jordanMul (signedSplitSequentialEquiv x) (signedSplitSequentialEquiv y)) = _
    simp only [← signedSplitSequentialEquiv_product, extendSignedEnd_on_image]
    rw [hd x y, map_add]

private theorem sequential_derivation_trace_zero (D : AlbertSequential.AlbertDerivation)
    (x : AlbertSequential.Albert) : AlbertSequential.albertTrace (D.val x) = 0 := by
  have hc : AlbertSequential.nativeJordanProductLinear (D.val x) =
      D.val * AlbertSequential.nativeJordanProductLinear x -
        AlbertSequential.nativeJordanProductLinear x * D.val := by
    ext y
    change AlbertSequential.jordanMul (D.val x) y =
      D.val (AlbertSequential.jordanMul x y) - AlbertSequential.jordanMul x (D.val y)
    rw [AlbertSequential.albertDerivation_mul, add_sub_cancel_right]
  have ht := AlbertSequential.CompanionIltyakov.native_leftTrace_eq_nine (D.val x)
  rw [hc, map_sub, LinearMap.trace_mul_comm ℝ D.val, sub_self] at ht
  linarith

private def pulledSequentialDerivation (D : AlbertSequential.AlbertDerivation) :
    SignedWithUnit →ₗ[ℝ] SignedWithUnit := signedSplitSequentialEquiv.symm.conj D.val

private theorem pulledSequentialDerivation_apply (D : AlbertSequential.AlbertDerivation) (x : SignedWithUnit) :
    signedSplitSequentialEquiv (pulledSequentialDerivation D x) = D.val (signedSplitSequentialEquiv x) := by
  simp [pulledSequentialDerivation]

theorem extendSignedEnd_surj (D : AlbertSequential.AlbertDerivation) :
    ∃ A : SignedField →ₗ[ℝ] SignedField, extendSignedEnd A = D.val := by
  let B := pulledSequentialDerivation D
  let A := ((LinearMap.fst ℝ SignedField ℝ).comp B).comp (LinearMap.inl ℝ SignedField ℝ)
  have hunit : B (0,1) = 0 := by
    apply signedSplitSequentialEquiv.injective
    change signedSplitSequentialEquiv (pulledSequentialDerivation D (0,1)) = _
    rw [pulledSequentialDerivation_apply, signedSplitSequentialEquiv_unit, AlbertSequential.albertDerivation_unit,
      map_zero]
  have htrace (x : SignedWithUnit) : (B x).2 = 0 := by
    have ht := sequential_derivation_trace_zero D (signedSplitSequentialEquiv x)
    rw [← pulledSequentialDerivation_apply, signedSplitSequentialEquiv_trace] at ht
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
  have hL : liftSignedEnd A = B := by
    apply LinearMap.ext
    intro x
    have hx : x = (x.1,0) + x.2 • ((0,1) : SignedWithUnit) := by
      apply Prod.ext <;> simp
    have hB : B x = B (x.1,0) := by
      conv_lhs => rw [hx]
      rw [map_add, map_smul, hunit, smul_zero, add_zero]
    rw [liftSignedEnd_apply, hB]
    exact Prod.ext rfl (htrace (x.1,0)).symm
  refine ⟨A, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := signedSplitSequentialEquiv.surjective y
  rw [extendSignedEnd_on_image, hL]
  exact pulledSequentialDerivation_apply D x

end

end ThirteenPlanes.SignedSkew
